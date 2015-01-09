type uop = Neg
type bop = Add | Sub | CLe | CEq

type bref = int (* Block references. *)
type 'op seqi = [ `Nop | `Uop of uop * 'op | `Bop of 'op * bop * 'op ]
type 'op jmpi = [ `Brz of 'op * bref * bref | `Jmp of bref ]

type ('ins, 'op) bb =
  { bb_phis: [ `Phi of 'op list ] array
  ; bb_inss: 'ins array
  ; bb_jmp: 'op jmpi
  }




(* ** Liveness analysis. ** *)
type iref = IRPhi of (bref * int) | IRIns of (bref * int)
type iprog = ((iref seqi, iref) bb) array

module IRSet = Set.Make(
  struct type t = iref let compare = compare end
)

let liveness (p: iprog) =
  let module H = Hashtbl in
  let changed = ref true in (* Witness for fixpoint. *)
  let lh = H.create 1001 in
  let liveout ir =
    try H.find lh ir with Not_found ->
    let e = IRSet.empty in H.add lh ir e; e in
  let setlive ir ir' = (* Mark ir live at ir'. *)
    let lir' = liveout ir' in
    if not (IRSet.mem ir lir') then begin
      changed := true;
      H.replace lh ir' (IRSet.add ir lir');
    end in
  let succs (b, i) = (* Successor nodes of an instruction. *)
    let bb = p.(b) in
    if i+1 = Array.length bb.bb_inss then
      if b+1 = Array.length p then [] else
      match bb.bb_jmp with
      | `Brz (_, b1, b2) -> [(b1, 0); (b2, 0)]
      | `Jmp b1 -> [(b1, 0)]
    else [(b, i+1)] in
  let gen (b, i) = IRSet.of_list
    begin match p.(b).bb_inss.(i) with
    | `Uop (_, i1) -> [i1]
    | `Bop (i1, _, i2) -> [i1; i2]
    | `Nop -> []
    end in
  let livein ir =
    let s = liveout ir in
    let s = IRSet.union s (gen ir) in
    IRSet.remove (IRIns ir) s in
  while !changed do
    changed := false;
    for b = Array.length p - 1 downto 0 do
      let bb = p.(b) in
      for i = Array.length bb.bb_inss - 1 downto 0 do
        let ir = (b, i) in
        let live = List.fold_left (fun live ir' ->
            IRSet.union live (livein ir')
          ) IRSet.empty (succs ir) in
        IRSet.iter (fun ir' -> setlive ir' ir) live
      done;
      Array.iter (fun (`Phi il) ->
        let blk ir = match ir with
          | IRPhi (b, _) | IRIns (b, _) -> b in
        List.iter (fun ir ->
          let br = blk ir in
          let bb = p.(br) in
          setlive ir (br, Array.length bb.bb_inss - 1)
        ) il
      ) bb.bb_phis;
    done
  done;
  lh (* Return the final hash table. *)

(* ** Register allocation. ** *)
type loc = LVoid | LReg of int | LSpill of int
