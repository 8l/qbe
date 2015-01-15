type uop = Neg
type bop = Add | Sub | CLe | CEq

type bref = int (* Block references. *)
type 'op seqi = [ `Nop | `Uop of uop * 'op | `Bop of 'op * bop * 'op ]
type 'op jmpi = [ `Brz of 'op * bref * bref | `Jmp of bref ]

type ('ins, 'phi, 'jmp) bb =
  { mutable bb_name: string
  ; mutable bb_phis: 'phi array
  ; mutable bb_inss: 'ins array
  ; mutable bb_jmp: 'jmp
  }


(* ** Liveness analysis. ** *)
type iref = IRPhi of (bref * int) | IRIns of (bref * int)
type iprog = (iref seqi, [`Phi of iref list], iref jmpi) bb array

module IRSet = Set.Make(
  struct type t = iref let compare = compare end
)

let liveout lh ir =
  try Hashtbl.find lh ir with Not_found ->
  let e = IRSet.empty in Hashtbl.add lh ir e; e
let livein lh p ir =
  let gen (b, i) = IRSet.of_list begin
    let {bb_inss; bb_jmp; _} = p.(b) in
      if i = Array.length bb_inss
      then match bb_jmp with
      | `Brz (i1, _, _) -> [i1]
      | `Jmp _ -> []
      else match bb_inss.(i) with
      | `Uop (_, i1) -> [i1]
      | `Bop (i1, _, i2) -> [i1; i2]
      | `Nop -> []
    end in
  let s = liveout lh ir in
  let s = IRSet.union s (gen ir) in
  IRSet.remove (IRIns ir) s

let liveness (p: iprog) =
  let module H = Hashtbl in
  let changed = ref true in (* Witness for fixpoint. *)
  let nbb = Array.length p in
  let lh = H.create 1001 in
  let setlive ir ir' = (* Mark ir live at ir'. *)
    let lir' = liveout lh ir' in
    if not (IRSet.mem ir lir') then begin
      changed := true;
      H.replace lh ir' (IRSet.add ir lir');
    end in
  let succs (b, i) = (* Successor nodes of an instruction. *)
    let bb = {bb_inss; bb_jmp; _} in
    if i = Array.length bb_inss then
      if b+1 = nbb then [] else
      match bb_jmp with
      | `Brz (_, b1, b2) -> [(b1, 0); (b2, 0)]
      | `Jmp b1 -> [(b1, 0)]
    else [(b, i+1)] in
  while !changed do
    changed := false;
    for b = nbb - 1 downto 0 do
      let bb = p.(b) in
      for i = Array.length bb.bb_inss downto 0 do
        let ir = (b, i) in
        let live = List.fold_left (fun live ir' ->
            IRSet.union live (livein lh p ir')
          ) IRSet.empty (succs ir) in
        IRSet.iter (fun ir' -> setlive ir' ir) live
      done;
      Array.iter (fun (`Phi il) ->
        let blk ir = match ir with
          | IRPhi (b, _) | IRIns (b, _) -> b in
        List.iter (fun ir ->
          let br = blk ir in
          let bb = p.(br) in
          setlive ir (br, Array.length bb.bb_inss)
        ) il
      ) bb.bb_phis;
    done
  done;
  lh (* Return the final hash table. *)


(* ** Register allocation. ** *)
type loc = LVoid | LReg of int | LSpill of int | LCon of int
type 'op rins = { ri_res: 'op; ri_ins: [ 'op seqi | `Mov of 'op ] }
type 'op rphi = { rp_res: 'op; rp_list: (bref * loc) list }
type rprog = (loc rins, loc rphi, loc jmpi) bb array


let regalloc nr (p: iprog) =
  let module H = Hashtbl in
  let lh = liveness p in
  let nbb = Array.length p in
  let bbmaps = Array.create nbb [] in
  let rp = Array.init nbb (fun i ->
      { bb_name = p.(i).bb_name
      ; bb_phis = [| |]
      ; bb_inss = [| |]
      ; bb_jmp = `Jmp -1
      }
    ) in
  let bb = ref [] in (* Basic block in construction. *)
  let emiti l i = bb := {ri_res=l; ri_ins=i} :: !bb in
  let m = H.create 101 in (* The map from iref to locations. *)
  for b = nbb - 1 downto 0 do
    (* At the end, spill everyting not in liveout of the predecessor block. *)
    rp.(b).bb_inss <- Array.of_list !bb;
    bb := [];
  done;
  rp


(* ** Phi resolution. ** *)
(* Machine program, ready for code generation. *)
type mprog = (loc rins, unit, loc jmpi) bb array
