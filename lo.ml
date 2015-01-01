type id = int
module ISet = Set.Make
  (struct
    type t = int
    let compare = compare
  end)

type unop = Not
type binop =
  | Add | Sub
  | Le | Ge | Lt | Gt | Eq | Ne

type phi = { pjmp: id; pvar: int }

type instr =
  | INop
  | ICon of int
  | IUop of unop * id
  | IBop of id * binop * id
  | IBrz of id * id * id
  | IJmp of id
  | IPhi of phi list

(* Phi nodes must be at the join of branches
   in the control flow graph, if n branches
   join, the phi node must have n elements in
   its list that indicate the value to merge
   from each of the branches.
   The id given in each of
*)

type prog = instr array


(* Here, we analyze a program backwards to
   compute the liveness of all variables.
   We assume that all phi nodes are placed
   correctly.
*)
let liveness p =
  (* The idea is now to reach a fixpoint
     by applying the same backward liveness
     propagation a sufficient number of
     times.
     The [changed] variable will tell us
     when we reached the fixpoint, it is
     reset to false at each iteration.
  *)
  let changed = ref true in
  let liveout = Array.make (Array.length p) ISet.empty in

  let setlive v l =
    (* Extend the liveness of v to l. *)
    if not (ISet.mem v liveout.(l)) then begin
      changed := true;
      liveout.(l) <- ISet.add v liveout.(l);
    end in

  let succs i =
    (* Retreive the successor nodes of i. *)
    if i = Array.length p -1 then [] else
    match p.(i) with
    | IBrz (_, i1, i2) -> [i1; i2]
    | IJmp i1 -> [i1]
    | _ -> [i+1] in

  let gen i = ISet.of_list
    (* Get the Gen set of i. *)
    begin match p.(i) with
    | IUop (_, i1) -> [i1]
    | IBop (i1, _, i2) -> [i1; i2]
    | IPhi l ->
      List.iter (fun {pjmp; pvar} ->
        setlive pvar pjmp
      ) l; []
    | _ -> []
    end in

  let livein i =
    (* Get the live In set of i. *)
    let s = liveout.(i) in
    let s = ISet.union s (gen i) in
    ISet.remove i s in

  (* The fixpoint computation. *)
  while !changed do
    changed := false;
    for i = Array.length p -1 downto 0 do
      (* Collect live Ins of all successor blocks. *)
      let live = List.fold_left (fun live i' ->
          ISet.union live (livein i')
        ) ISet.empty (succs i) in
      ISet.iter (fun i' ->
        setlive i' i
      ) live
    done
  done;
  liveout

type reginfo =
  { mutable rreg: int
  ; mutable rspill: int option
  ; mutable rhint: int
  }

let regalloc nr p l =
  let regs = Array.init (Array.length p)
    (fun _ ->
      { rreg = -1
      ; rspill = None
      ; rhint = -1
      }) in

  let ( |> ) a b = if a = -1 then b else a in

  (* Number of spilled registers. *)
  let spill = ref 0 in
  let rspill i =
    if regs.(i).rspill = None then begin
      regs.(i).rspill <- Some !spill;
      incr spill;
    end in

  (* Associative list binding irrefs to registers,
     it is ordered by freshness. *)
  let used = ref [] in
  let free = ref (
      let rec m i = if i = nr then []  else i :: m (i+1)
      in m 0
    ) in
  let alloc hint i =
    let r, fl =
      let l, fl = List.partition ((=) hint) !free in
      if l <> [] then (hint, fl) else
      match !free with
      | r :: fl -> (r, fl)
      | [] ->
        (* No more free registers, we need to spill. *)
        let rec g = function
          | [] -> assert false
          | [r,i'] -> rspill i'; (r, [])
          | x :: us ->
            let (r, us) = g us in
            (r, x :: us) in
        let r, us = g !used in
        used := us;
        r, [] in
    free := fl;
    used := (r, i) :: !used;
    r in

  for i = 0 to Array.length p -1 do

    (* Forget about all bindings that are not live
       at the end of the instruction. *)
    let used', free' = List.partition
      (fun (_, i') -> ISet.mem i' l.(i)) !used in
    used := used';
    free := List.map fst free' @ !free;

    (* Bind a register to the current instruction
       if its result is not discarded. *)
    if ISet.mem i l.(i) then begin
      match p.(i) with
      | ICon _ | IBrz _ | IJmp _ | INop -> ()
      | IPhi l ->
        (* Try to ensure that variables merged by a phi
           use the same register. *)
        let f r {pvar;_} = regs.(pvar).rreg |> r in
        let r = List.fold_left f (-1) l in
        let r =
          let h = regs.(i).rhint in
          if r = -1 then alloc h i else r in
        List.iter (fun {pvar;_} ->
          regs.(pvar).rhint <- r
        ) l;
        regs.(i).rreg <- r
      | IUop (_, i')
      | IBop (i', _, _) ->
        let h =
          regs.(i).rhint |>
          regs.(i').rreg |>
          regs.(i').rhint in
        regs.(i).rreg <- alloc h i
    end;

  done;
  (regs, !spill)










(* Testing. *)

let parse src =
  let blocks = Hashtbl.create 31 in
  let rec addlbl idx l =
    let l = String.trim l in
    try
      let il = String.index l ':' in
      let lbl = String.sub l 0 il in
      Hashtbl.add blocks lbl idx;
      let l =
        String.sub l (il+1)
          (String.length l -(il+1)) in
      addlbl idx l
    with Not_found -> l ^ " " in
  let src = List.mapi addlbl src in
  let p = Array.make (List.length src) INop in
  List.iteri (fun idx l ->
    let fail s =
      failwith
        (Printf.sprintf "line %d: %s" (idx+1) s) in
    let tok =
      let p = ref 0 in fun () ->
      try
        while l.[!p] = ' ' do incr p done;
        let p0 = !p in
        while l.[!p] <> ' ' do incr p done;
        String.sub l p0 (!p - p0)
      with _ -> fail "token expected" in
    let id () =
      let v = tok () in
      try Hashtbl.find blocks v
      with _ -> fail ("unknown variable " ^ v) in
    let instr =
      if l = " " then INop else
      let bop o =
        let i1 = id () in
        let i2 = id () in
        IBop (i1, o, i2) in
      match tok () with
      | "con" -> ICon (int_of_string (tok ()))
      | "not" -> IUop (Not, id ())
      | "add" -> bop Add
      | "sub" -> bop Sub
      | "cle" -> bop Le
      | "cge" -> bop Ge
      | "clt" -> bop Lt
      | "cgt" -> bop Gt
      | "ceq" -> bop Eq
      | "cne" -> bop Ne
      | "phi" ->
        let exp t =
          let t' = tok () in
          if t' <> t then
            fail ("unexpected " ^ t') in
        let rec f () =
          match tok () with
          | "[" ->
            let pjmp = id () in
            let pvar = id () in
            exp "]";
            {pjmp; pvar} :: f ()
          | "." -> []
          | t -> fail ("unexpected " ^ t) in
        IPhi (f ())
      | "brz" ->
        let v = id () in
        let bz = id () in
        let bn = id () in
        IBrz (v, bz, bn)
      | "jmp" -> IJmp (id ())
      | i -> fail ("invalid " ^ i) in
    p.(idx) <- instr
  ) src;
  p

let t_pow = parse
  [ "k0:  con 0"
  ; "ni:  con 1234"
  ; "k1:  con 1"
  ; "n0:  phi [ jmp n1 ] [ k1 ni ] ."
  ; "f1:  phi [ jmp f2 ] [ k1 k1 ] ."
  ; "n1:  sub n0 k1"
  ; "f2:  add f1 f1"
  ; "jmp: brz n1 end n0"
  ; "end:"
  ]

(*
  The following program has irreducible
  control-flow.  The control flow is
  pictured below.

  +--b1      <- defs r0, r1
  |  |
  b2 b3
  |  |
  \  b4<-+   <- uses r0
   \ |   |
  +--b5  |   <- uses r1
  |  |   |
  b7 b6--+

  A simple implementation (that works for
  non-irreducible control flows) proceeds
  backwards, it would successfully make r1
  live in b2 and b3 but r0 would fail to be
  live in b2. It would become live for the
  loop b4-b5-b6 when reaching the loop header
  b4, but the simple algorithm would not
  propagate back to b2.
*)

let t_irred = parse
  [ "k0:  con 0"
  ; "r0:  con 1"
  ; "r1:  con 2"
  ; "b1:  brz k0 b2 b3"
  ; "b2:  jmp b5"
  ; "b3:"
  ; "b4:  add r0 k0"
  ; "b50: add r1 k0"
  ; "b5:  brz k0 b6 b7"
  ; "b6:  jmp b4"
  ; "b7:"
  ]

let _ =
  let p = t_pow in
  let open Printf in

  printf "\n** Liveness analysis:\n";
  let l = liveness p in
  for i = 0 to Array.length p -1 do
    printf "%04d:" i;
    ISet.iter (printf " %04d") l.(i);
    printf "\n";
  done;

  printf "\n** Register allocation:\n";
  let regs = [| "rax"; "rbx"; "rcx" |] in
  let r, s = regalloc (Array.length regs) p l in
  if s <> 0 then printf "!! Needs spills !!\n";
  let bop_str = function
    | Add -> "add" | Sub -> "sub"
    | Le -> "cle" | Ge -> "cge" | Lt -> "clt" | Gt -> "cgt" | Eq -> "ceq" | Ne -> "cne" in
  for i = 0 to Array.length p -1 do
    let reg i =
      if r.(i).rreg = -1 then sprintf "%03d" i else regs.(r.(i).rreg) in
    if r.(i).rreg = -1
    then printf "%03d:  " i
    else printf "%s = " (reg i);
    begin match p.(i) with
    | ICon k -> printf "%d" k
    | INop -> ()
    | IUop (Not, i') -> printf "not %s" (reg i')
    | IBop (i1, o, i2) ->
      printf "%s %s %s" (bop_str o) (reg i1) (reg i2)
    | IBrz (i1, i2, i3) ->
      printf "brz %s %03d %03d" (reg i1) i2 i3
    | IJmp i' ->
      printf "jmp %s" (reg i')
    | IPhi l ->
      printf "phi ";
      List.iter (fun {pjmp; pvar} ->
        printf "[ %d %s ] " pjmp (reg pvar)
      ) l
    end;
    printf "\n"
  done
