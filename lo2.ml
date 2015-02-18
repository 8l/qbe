type uop = Neg
type bop = Add | Sub | CLe | CEq

type bref = int (* Block references. *)
type 'op seqi = [ `Con of int | `Uop of uop * 'op | `Bop of 'op * bop * 'op ]
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
      if i = -1 then [] else
      if i = Array.length bb_inss
      then match bb_jmp with
      | `Brz (i1, _, _) -> [i1]
      | `Jmp _ -> []
      else match bb_inss.(i) with
      | `Uop (_, i1) -> [i1]
      | `Bop (i1, _, i2) -> [i1; i2]
      | `Con _ -> []
    end in
  let kill ((b, i) as ir) =
    if i >= 0 then IRSet.singleton (IRIns ir) else
    fst (Array.fold_left
      (fun (k, i) _ -> (IRSet.add (IRPhi (b, i)) k, i+1))
      (IRSet.empty, 0) p.(b).bb_phis
    ) in
  let s = liveout lh ir in
  let s = IRSet.union s (gen ir) in
  IRSet.diff s (kill ir)

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
    let {bb_inss; bb_jmp; _} = p.(b) in
    if i = Array.length bb_inss then
      if b+1 = nbb then [] else
      match bb_jmp with
      | `Brz (_, b1, b2) -> [(b1, -1); (b2, -1)]
      | `Jmp b1 -> [(b1, -1)]
    else [(b, i+1)] in
  while !changed do
    changed := false;
    for b = nbb - 1 downto 0 do
      let bb = p.(b) in
      for i = Array.length bb.bb_inss downto -1 do
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
          setlive ir (br, Array.length p.(br).bb_inss)
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

let regalloc (p: iprog) =
  let module H = struct
    include Hashtbl
    let find h ir = try find h ir with Not_found -> LVoid
  end in

  let lh = liveness p in
  let nbb = Array.length p in
  let rp = Array.init nbb (fun i ->
      { bb_name = p.(i).bb_name
      ; bb_phis = [| |]
      ; bb_inss = [| |]
      ; bb_jmp = `Jmp (-1)
      }
    ) in
  let outmaps = Array.make nbb [] in
  let phimaps = Array.make nbb [| |] in
  let bb = ref [] in (* Basic block in construction. *)
  let emiti l i = bb := {ri_res=l; ri_ins=i} :: !bb in
  let act = H.create 101 in (* The active list. *)
  let free = ref [0;1;2] in (* Free registers. *)

  let nspill = ref 0 in
  let newspill () = incr nspill; !nspill - 1 in
  let getspill ir =
    match H.find act ir with
    | LSpill s -> s
    | _ -> -1 in

  let kill ir =
    match H.find act ir with
    | LReg r -> H.remove act ir; free := r :: !free
    | _ -> H.remove act ir in

  let loc ir =
    match H.find act ir with
    | LVoid ->
      let l =
        match !free with
        | r :: f -> free := f; LReg r
        | [] -> LSpill (newspill ())
      in
      H.add act ir l; l
    | l -> l in

  let rec getreg frz = (* Aggressively obtain one register. *)
    match !free with
    | r :: f when List.mem r frz -> (* Frozen, can't use it. *)
      free := f;
      let r' = getreg frz in
      free := r :: !free; r'
    | r :: f -> free := f; r
    | [] -> (* Spill needed! *)
      match
        H.fold (fun ir loc l -> (* Find candidates. *)
          match loc with
          | LReg r when not (List.mem r frz) ->
            (ir, r) :: l
          | _ -> l
        ) act [] (* |> sort by spill cost *)
      with [] -> failwith "god damn it, not enough registers"
      | (ir, r) :: _ ->
        H.remove act ir;
        let s = getspill ir in
        let s =
          if s >= 0 then s else
          let s' = newspill () in
          H.add act ir (LSpill s'); s' in
        emiti (LReg r) (`Mov (LSpill s));
        r in

  let regloc frz ir =
    match H.find act ir with
    | LReg r -> r
    | _ ->
      let r = getreg frz in
      H.add act ir (LReg r); r in

  for b = nbb - 1 downto 0 do
    let bi = p.(b).bb_inss in
    let bl = Array.length bi in

    (* Fill outmaps with the allocation state at
     * the end of the block (after the final branch).
     * Invariant 1: everything in registers is live.
     *)

    let lvout = liveout lh (b, bl) in
    outmaps.(b) <- begin
      IRSet.fold (fun ir m -> (ir, loc ir) :: m) lvout []
    end;

    let jmp =
      match p.(b).bb_jmp with
      | `Jmp br -> `Jmp br
      | `Brz (ir, br1, br2) ->
        `Brz (loc ir, br1, br2) in
    rp.(b).bb_jmp <- jmp;

    for i = bl - 1 downto 0 do
      let ir = IRIns (b, i) in
      begin match H.find act ir with
      | LVoid -> () (* Dead code. *)
      | lir ->
        let r, frz =
          match lir with
          | LSpill s ->
            let r = getreg [] in
            emiti (LSpill s) (`Mov (LReg r));
            if not (List.mem r !free) then
              free := r :: !free; (* Add it straight back to free, but freeze it. *)
            (r, [r])
          | LReg r -> (r, [])
          | _ -> assert false
          in
        kill ir;
        let s = getspill ir in
        begin match bi.(i) with
        | `Con k ->
          if s >= 0 then emiti (LSpill s) (`Mov (LReg r));
          emiti (LReg r) (`Mov (LCon k))
        | `Uop (op, ir') ->
          let r' = regloc frz ir' in
          if s >= 0 then emiti (LSpill s) (`Mov (LReg r));
          emiti (LReg r) (`Uop (op, LReg r'))
        | `Bop (ir1, op, ir2) ->
          let r1 = regloc frz ir1 in
          let frz = r1 :: frz in
          let r2 = regloc frz ir2 in
          if s >= 0 then emiti (LSpill s) (`Mov (LReg r));
          emiti (LReg r) (`Bop (LReg r1, op, LReg r2))
        end;
      end
    done;

    phimaps.(b) <- begin
      Array.init (Array.length p.(b).bb_phis) (fun p ->
        let pr = IRPhi (b, p) in
        let ploc = H.find act pr in
        kill pr; ploc
      )
    end;

    (* Kill everything not in liveout of the predecessor block. *)
    let lvout =
      if b = 0 then IRSet.empty else
      liveout lh (b-1, Array.length p.(b-1).bb_inss) in
    IRSet.iter kill lvout;

    rp.(b).bb_inss <- Array.of_list !bb;
    bb := [];
  done;

  (* Compute phis. *)
  for b = 0 to nbb - 1 do
    rp.(b).bb_phis <- begin
      Array.mapi (fun i (`Phi l) ->
        { rp_res = phimaps.(b).(i)
        ; rp_list = List.map (function
            | IRPhi (b, p) -> b, phimaps.(b).(i)
            | IRIns (b, _) as ir -> (b, List.assoc ir outmaps.(b))
          ) l
        }
      ) p.(b).bb_phis
    end
  done;

  rp

(* Facts
 * There are little lifetime holes in SSA (caused by block ordering)
 *)


(* Little test programs. *)
let pbasic: iprog =
  [| { bb_name = "start"
     ; bb_phis = [| |]
     ; bb_inss =
       [| `Con 2
        ; `Con 3
        ; `Bop (IRIns (0, 0), Add, IRIns (0, 1))
        ; `Bop (IRIns (0, 0), Add, IRIns (0, 2))
       |]
     ; bb_jmp = `Brz (IRIns (0, 3), -1, -1)
     }
  |]

let pcount: iprog =
  [| { bb_name = "init"
     ; bb_phis = [||]
     ; bb_inss = [| `Con 100; `Con 1 |]
     ; bb_jmp = `Jmp 1
     }
   ; { bb_name = "loop"
     ; bb_phis = [| `Phi [IRIns (0, 0); IRIns (1, 0)] |]
     ; bb_inss = [| `Bop (IRPhi (1, 0), Sub, IRIns (0, 1)) |]
     ; bb_jmp = `Brz (IRIns (1, 0), 2, 1)
     }
   ; { bb_name = "end"
     ; bb_phis = [||]
     ; bb_inss = [| `Con 42 |]
     ; bb_jmp = `Jmp (-1)
     }
  |]

let psum: iprog =
  [| { bb_name = "init"
     ; bb_phis = [||]
     ; bb_inss = [| `Con 100; `Con 1 |]
     ; bb_jmp = `Jmp 1
     }
   ; { bb_name = "loop"
     ; bb_phis =
       [| `Phi [IRIns (0, 0); IRIns (1, 0)]       (* n  = phi(100, n1) *)
        ; `Phi [IRIns (0, 1); IRIns (1, 1)]       (* s  = phi(1, s1) *)
       |]
     ; bb_inss =
       [| `Bop (IRPhi (1, 0), Sub, IRIns (0, 1))  (* n1 = n - 1 *)
        ; `Bop (IRPhi (1, 1), Add, IRPhi (1, 0))  (* s1 = s + n *)
       |]
     ; bb_jmp = `Brz (IRIns (1, 0), 2, 1)
     }
   ; { bb_name = "end"
     ; bb_phis = [||]
     ; bb_inss = [| `Con 42 |]
     ; bb_jmp = `Jmp (-1)
     }
  |]

(* ** Phi resolution. ** *)
(* Machine program, ready for code generation. *)
type mprog = (loc rins, unit, loc jmpi) bb array
