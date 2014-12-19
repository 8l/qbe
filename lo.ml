type id = int
module ISet = Set.Make
  (struct
    type t = id
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




(*

  Non-reducible control flow graph, these
  cfgs are problematic when implementing
  the naive backwards liveness analysis.

  +--i
  |  |
  y  x--+
  |  |  |
  +--a  |
     |  |
     b--+
     |
     c

*)









(* Testing. *)

let parse src =
  let blocks = Hashtbl.create 31 in
  let src = List.mapi (fun idx l ->
      let l = String.trim l in
      try
        let il = String.index l ':' in
        let lbl = String.sub l 0 il in
        Hashtbl.add blocks lbl idx;
        String.sub l (il+1)
          (String.length l -(il+1)) ^ " "
      with Not_found -> l ^ " "
    ) src in
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

let t_fact = parse
  [ "start:"
  ; "  ni: con 1234"
  ; "  k1: con 1"
  ; "loop:"
  ; "  n0: phi [ back n1 ] [ k1 ni ] ."
  ; "  n1: sub n0 k1"
  ; "back: brz n1 pend loop"
  ; "pend:"
  ]

let _ =
  let open Printf in
  let s = liveness t_fact in
  for i = 0 to Array.length s-1 do
    printf "%04d:" i;
    ISet.iter (printf " %04d") s.(i);
    printf "\n";
  done
