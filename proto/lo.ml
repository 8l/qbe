module ISet = Set.Make
  (struct
    type t = int
    let compare = compare
  end)

type unop = Not
type binop =
  | Add | Sub
  | Le | Ge | Lt | Gt | Eq | Ne

type ('ref, 'loc) phi = { pjmp: 'loc; pvar: 'ref }

type ('ref, 'loc) ir =
  | INop
  | ICon of int
  | IUop of unop * 'ref
  | IBop of 'ref * binop * 'ref
  | IBrz of 'ref * 'loc * 'loc
  | IJmp of 'loc
  | IPhi of ('ref, 'loc) phi list

(* Phi nodes must be at the join of branches
   in the control flow graph, if n branches
   join, the phi node must have n elements in
   its list that indicate the value to merge
   from each of the branches.
   The id given in each of
*)


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


type loc =
  | L0          (* No location. *)
  | LCon of int (* Constant. *)
  | LReg of int (* Machine register. *)
  | LSpl of int (* Spill location. *)

type spill = { sreg: int; soff: int }

type regir =
  | RIR of int * (loc, int ref) ir
  | RMove of loc * loc

(* The reg IR adds spill saves and restores to standard
   IR instructions.  The register allocator below uses
   these new instructions when the physical machine lacks
   registers.
*)

let regalloc nr p l =
  (* The final reg IR is built here. *)
  let rir = ref [] in
  let emit r = rir := r :: !rir in
  let ipos = Array.init (Array.length p) ref in
  emit (RIR (-1, INop));

  (* Hints help the allocator to know what register
     to use.  They can be combined using the |>
     operator below. *)
  let hints = Array.make (Array.length p) (-1) in
  (* let ( |> ) a b = if a < 0 then b else a in *)

  (* Number of spill slots. *)
  let spill = ref 0 in

  (* Associative list binding live ir to locations,
     ordered by freshness. *)
  let locs = ref [] in
  let setloc i l = locs := (i, l) :: !locs in
  let setspill i =
    setloc i (LSpl !spill);
    incr spill; !spill - 1 in

  (* Get free registers. *)
  let free () =
    let rl = Array.to_list (Array.init nr (fun i -> i)) in
    List.filter (fun r ->
      not (List.mem (LReg r) (List.map snd !locs))
    ) rl in

  (* Allocate a register for an ir. *)
  let alloc hint i =
    let ret r = setloc i (LReg r); r in
    let free = free () in
    if List.mem hint free then ret hint
    else match free with  r::_ -> ret r
    | [] -> (* No more free registers, force spill. *)
      let regof = function LReg r -> r | _ -> -1 in
      let cmpf (a,_) (b,_) = compare a b in
      let l = List.map (fun (i,l) -> (i,regof l)) !locs in
      let l = List.filter (fun (_,r) -> r >= 0) l in
      let sir, sreg = List.hd (List.sort cmpf l) in (* Take the oldest. *)
      locs := snd (List.partition ((=) (sir, LReg sreg)) !locs);
      let soff =
        match try List.assoc sir !locs with _ -> L0 with
        | LSpl n -> n
        | _ -> setspill sir in
      emit (RMove (LReg sreg, LSpl soff));
      ret sreg in

  (* Find a register for a destination. *)
  let dst i =
    let li =
      try List.assoc i !locs with Not_found -> L0 in
    let r = match li with
      | LReg r -> r
      | _ -> alloc hints.(i) i in
    begin match li with
    | LSpl l -> emit (RMove (LSpl l, LReg r))
    | _ -> ()
    end;
    locs := snd (List.partition (fun (j,_) -> j=i) !locs);
    r in

  let phis = ref [] in

  (* Find a location for an operand. *)
  let loc i =
    try List.assoc i !locs with Not_found ->
    try List.assoc i !phis with Not_found ->
    match p.(i) with
    | ICon k -> setloc i (LCon k); LCon k
    | _ -> LReg (alloc hints.(i) i) in

  let loc2 i =
    try List.assoc i !locs with Not_found ->
    try List.assoc i !phis with Not_found ->
    match p.(i) with
    | ICon k -> setloc i (LCon k); LCon k
    | _ ->
      (* Here, we just want to avoid using the
         same register we used for the first
         operand. *)
      if free () = [] then LSpl (setspill i)
      else LReg (alloc hints.(i) i) in

  let philoc i =
    match p.(i) with
    | IPhi pl ->
      (try List.assoc i !phis with Not_found ->
      let l = loc2 i in
      phis := (i, l) :: !phis;
      begin match l with
      | LReg h -> List.iter (fun x -> hints.(x.pvar) <- h) pl;
      | _ -> ()
      end;
      l)
    | _ -> failwith "regalloc: invalid call to philoc" in
  let rec movs jmp i =
    if i >= Array.length p then () else
    match p.(i) with
    | IPhi l ->
      let l = List.filter (fun x -> x.pjmp = jmp) l in
      assert (List.length l = 1);
      let pl = philoc i in
      let v = (List.hd l).pvar in
      let vl = loc2 v in
      emit (RMove (pl, vl));
      movs jmp (i+1)
    | _ -> () in


  (* Going backwards. *)
  for i = Array.length p -1 downto 0 do

    (* Forget about all bindings not live
       at the end of the instruction. *)
    locs := List.filter
      (fun (i',_) -> ISet.mem i' l.(i)) !locs;

    begin match p.(i) with
    | IPhi _ -> ()
    | ICon _ | INop ->
      movs i (i+1)
    | IBrz (i', l1, l2) ->
      emit (RIR (-1, IJmp ipos.(l2)));
      movs i l2;
      let li' = loc i' in
      let p = List.length !rir in
      emit (RIR (-1, IBrz (li', ipos.(l1), ref p)));
      movs i l1
    | IJmp l ->
      emit (RIR (-1, IJmp ipos.(l)));
      movs i l;
    | IUop (op, i') ->
      let r = dst i in
      let li' = hints.(i') <- r; loc i' in
      emit (RIR (r, IUop (op, li')));
      movs i (i+1)
    | IBop (il, op, ir) ->
      let r = dst i in
      let lil = hints.(il) <- r; loc il in
      let lir = loc2 ir in
      emit (RIR (r, IBop (lil, op, lir)));
      movs i (i+1)
    end;

    (* Update position of the current instruction. *)
    ipos.(i) := List.length !rir;
  done;

  (Array.of_list !rir, !spill)


module type ARCH = sig
  type label type reg
  type brtype = Jump | NonZ of reg

  (* Labels for branching. *)
  val newlbl: unit -> label
  val setlbl: label -> unit

  (* Register creation. *)
  val regk: int -> reg
  val regn: int -> reg

  (* Register spilling and restoration. *)
  val spill: reg -> int -> unit
  val resto: int -> reg -> unit
  (* Boring instructions. *)
  val mov: reg -> reg -> unit
  val bop: binop -> reg -> reg -> reg -> unit
  val uop: unop -> reg -> reg -> unit
  val br: brtype -> label -> unit

  (* Initialization finalization. *)
  val reset: int -> unit
  val code: unit -> string
end



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

let t_sum =
  [ "k0:  con 0"
  ; "ni:  con 1234"
  ; "k1:  con 1"
  ; "n0:  phi [ jmp n1 ] [ k1 ni ] ."
  ; "f1:  phi [ jmp f2 ] [ k1 k1 ] ."
  ; "n1:  sub n0 k1"
  ; "f2:  add f1 n0"
  ; "jmp: brz n1 end n0"
  (* ; "jmp: jmp n0" *)
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

let t_irred =
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
  let src = t_sum in
  let p = parse src in
  let open Printf in

  printf "** Program:\n";
  List.iter (printf "%s\n") src;

  printf "\n** Liveness analysis:\n";
  let l = liveness p in
  for i = 0 to Array.length p -1 do
    printf "%04d:" i;
    ISet.iter (printf " %04d") l.(i);
    printf "\n";
  done;

  printf "\n** Register allocation:\n";
  let regs = [| "rax"; "rbx" |] in (* ; "rbx"; "rcx" |] in *)
  let loc = function
    | L0 -> assert false
    | LReg r -> regs.(r)
    | LCon k -> sprintf "$%d" k
    | LSpl n -> sprintf "%d(sp)" n in
  let r, _ = regalloc (Array.length regs) p l in
  let bop_str = function
    | Add -> "add" | Sub -> "sub"
    | Le -> "cle" | Ge -> "cge"
    | Lt -> "clt" | Gt -> "cgt"
    | Eq -> "ceq" | Ne -> "cne" in
  let lr = Array.length r in
  let inum l = lr - !l in
  for i = 0 to lr -1 do
    printf "%03d " i;
    begin match r.(i) with
    | RIR (r, IUop (Not, i')) ->
      printf "%s = not %s" regs.(r) (loc i')
    | RIR (r, IBop (i1, o, i2)) ->
      printf "%s = %s %s %s"
        regs.(r) (bop_str o) (loc i1) (loc i2)
    | RIR (_, IBrz (i', l1, l2)) ->
      printf "brz %s %03d %03d" (loc i')
        (inum l1) (inum l2)
    | RIR (_, IJmp l) ->
      printf "jmp %03d" (inum l)
    | RIR (_, IPhi l) ->
      printf "phi"
    | RMove (t, f) ->
      printf "%s = %s" (loc t) (loc f)
    | _ -> ()
    end;
    printf "\n"
  done
