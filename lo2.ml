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
type loc = LVoid | LReg of int | LSpill of int
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
  let free = ref [0;1;2;3;4] in (* Free registers. *)

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
        | [] -> LSpill (newspill ())                        (* Here we can try to spill the longer range instead. *)
      in
      H.add act ir l; l
    | l -> l in

  for b = nbb - 1 downto 0 do
    let bi = p.(b).bb_inss in
    let bl = Array.length bi in

    (* Fill outmaps with the allocation state at
     * the end of the block (after the final branch).
     * Invariant 1: everything in registers is live.
     *)

    let lvout = liveout lh (b, bl) in
    IRSet.iter (fun ir -> ignore (loc ir)) lvout;
    outmaps.(b) <- begin
      H.fold (fun ir l m ->
        if IRSet.mem ir lvout
        then (ir, l) :: m
        else m
      ) act []
    end;

    let jmp =
      match p.(b).bb_jmp with
      | `Jmp br -> `Jmp br
      | `Brz (ir, br1, br2) ->
        `Brz (LReg (regloc ir), br1, br2) in
    rp.(b).bb_jmp <- jmp;

    for i = bl - 1 downto 0 do
      let ir = IRIns (b, i) in
      begin match H.find act ir with
      | LVoid -> () (* Dead code. *)
      | lir ->
        let r =
          match lir with
          | LSpill spl1 ->
            (* Restore in a register.
             *
             * In this situation, the register for the result
             * must not be killed because it lives until the
             * spill code executes.
             *
             * This is a bit silly because we will move it
             * into a spill location right after that, there
             * is no benefit from having it in register here.
             *)
            let r = getreg
          | LReg r -> kill ir; r (* In register, we can kill it now. *)
          | _ -> assert false
          in
        begin match bi.(i) with
        | `Con k ->
          emiti lir (`Mov (LCon k))
        | `Uop (op, ir') ->
          let r' = regloc ir' in
          emiti (LReg r) (`Uop (op, LReg r'))
        | `Bop (ir1, op, ir2) ->
          let r1 = regloc ir1 in
          let r2 = regloc ~block:r1 ir2 in
          emiti (LReg r) (`Bop (LReg r1, op, LReg r2))
        end;
        kill ir;
      end
    done;

    phimaps.(b) <- begin
      Array.init (Array.length p.(b).bb_phis) (fun p ->
        let pr = IRPhi (b, p) in
        let ploc = H.find act pr in
        kill pr; ploc
      )
    end;

    (* Spill everyting not in liveout of the predecessor block.
     * Remove them from the active list (ensures Invariant 1).
     *)

    let lvout =
      if b = 0 then IRSet.empty else
      liveout lh (b-1, Array.length p.(b-1).bb_inss) in
    let spl = H.fold (fun ir l s ->
        match l with
        | LReg r ->
          if IRSet.mem ir lvout then s else (ir, r) :: s
        | _ -> s
      ) act [] in
    List.iter (fun (ir, r) ->
      let spl = LSpill (newspill ()) in
      free := r :: !free;
      H.replace act ir spl;
      emiti (LReg r) (`Mov spl)
    ) spl;

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


(* ** NEW attempt at a more clever allocator. ** *)

let ircmp a b =
  let blk = function IRPhi (b,_) | IRIns (b,_) -> b in
  let cb = compare (blk a) (blk b) in
  if cb <> 0 then cb else
  match a, b with
  | IRPhi _, IRIns _ -> -1
  | IRIns _, IRPhi _ -> +1
  | IRPhi (_,x), IRPhi (_,y)
  | IRIns (_,x), IRIns (_,y) -> compare x y

(* An interval specifies a region of the program text (usually where
 * a variable is live. It has two bounds, lo is exclusive and hi is
 * inclusive.
 *)
type inter = { lo: iref; hi: iref }

(* The register type is used to store the usage of a given register
 * by the program.  The list of intervals it stores has to be non-
 * overlapping.
 * Invariant: Intervals are stored.
 *)
type reg = { mutable busy: (iref * inter) list }

let reg_dispo {busy} i =
  let rec f = function
    | (_, {lo; hi}) :: l ->
      if ircmp hi i.lo < 0 then f l else  (* [lo, hi] ... [i] *)
      if ircmp lo i.hi < 0 then true else (* [i] ... [lo, hi] *)
      false                               (* overlap *)
    | [] -> true in
  f busy

let reg_add r ir i =
  assert (reg_dispo r i);
  let c (_,a) (_,b) = ircmp a.lo b.lo in
  r.busy <- List.sort c ((ir, i) :: r.busy)

let mkinters (p: iprog) =
  let module H = Hashtbl in
  let lh = liveness p in
  let ih = H.create 1001 in
  let n = ref 0 in      (* Fairly hashish. *)
  let setlive ir loc =
    let rec f = function
      | [] -> [({lo=loc; hi=loc}, !n)]
      | ({lo;_}, n') :: [] when n'+1 = !n -> [({lo; hi=loc}, !n)]
      | x :: l' -> x :: f l' in
    H.replace ih ir
      (f (try H.find ih ir with Not_found -> [])) in
  for b = 0 to Array.length p - 1 do
    for i = -1 to Array.length p.(b).bb_inss do
      let loc = IRIns (b,i) in
      IRSet.iter (fun ir -> setlive ir loc)
        (liveout lh (b,i));
      incr n;
    done
  done;
  let hp = Heap.create (fun (_,a) (_,b) ->
      match a, b with
      | a::_, b::_ -> ircmp a.lo b.lo
      | _ -> assert false
    ) in
  H.iter (fun ir il ->
    Heap.add hp (ir, List.map fst il)
  ) ih;
  hp

let regalloc2 ?(nr=4) (p: iprog) =
  let nbb = Array.length p in

  let _regs = Array.init nr (fun _ -> {busy=[]}) in
  let _spillh = Heap.create (fun (_,a) (_,b) -> ircmp b a) in
  let act = Hashtbl.create 101 in (* Active list. *)
  let _loc_ ir =
    try Hashtbl.find act ir
    with Not_found -> LVoid in

  let rp = Array.init nbb (fun i ->
      { bb_name = p.(i).bb_name
      ; bb_phis = [| |]
      ; bb_inss = [| |]
      ; bb_jmp = `Jmp (-1)
      }
    ) in
  let bb = ref [] in (* Block in construction. *)
  let _emit l i = bb := {ri_res=l;ri_ins=i} :: !bb in

  for b = 0 to nbb do
    let bi = p.(b).bb_inss in
    let bl = Array.length bi in

    (* Entering a block.
     * Many phi intervals start at the same time.
     * We need to allocate them registers and store
     * the allocator state for the resolve phase.
     *)

    for i = 0 to bl - 1 do
      let _ir = IRIns (b,i) in

      (* For a regular instruction:
       *   1. Get locations of arguments.
       *      Make sure they are in registers.
       *   2. Free registers of dead variables.
       *   3. Allocate for the new interval.
       *   4. Emit the instruction.
       *)

      ()
    done;

    (* Leaving a block.
     * Rewrite the jump.
     * Store the allocator state for the resolve
     * phase.
     *)

    rp.(b).bb_inss <- Array.of_list (List.rev !bb);
  done;

  rp


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
