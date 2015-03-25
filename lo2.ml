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
let blk = function IRPhi (b, _) | IRIns (b, _) -> b
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

let regalloc (p: iprog): rprog =
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
  let inmaps  = Array.make nbb [] in
  let bb = ref [] in (* Basic block in construction. *)
  let emiti l i = bb := {ri_res=l; ri_ins=i} :: !bb in
  let act = H.create 101 in (* The active list. *)
  let free = ref [0;1;2;3] in (* Free registers. *)

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
          let frz = r :: r1 :: frz in
          let r2 = regloc frz ir2 in
          if s >= 0 then emiti (LSpill s) (`Mov (LReg r));
          emiti (LReg r) (`Bop (LReg r1, op, LReg r2))
        end;
      end
    done;

    let lvin = liveout lh (b, -1) in
    inmaps.(b) <- begin
      IRSet.fold (fun ir l ->
        let loc = H.find act ir in
        if blk ir = b then
          kill ir; (* Kill current block's phis *)
        (ir, loc) :: l
      ) lvin []
    end;

    rp.(b).bb_inss <- Array.of_list !bb;
    bb := [];
  done;

  (* Compute phis. *)
  for b = 0 to nbb - 1 do
    rp.(b).bb_phis <- Array.of_list begin
      IRSet.fold (fun ir l ->
        match ir with
        | IRPhi (b', pr) when b' = b ->
          let `Phi pl = p.(b).bb_phis.(pr) in
          let pl =
            let f ir =
              let b = blk ir in
              (b, List.assoc ir outmaps.(b)) in
            List.map f pl |>
            List.sort (fun (a,_) (b,_) -> compare a b) in
          { rp_res = List.assoc ir inmaps.(b)
          ; rp_list =  pl
          } :: l
        | _ -> assert (blk ir <> b);
          (* Forgive me, I sin!! *)
          let rl = ref [] in
          for b = 0 to nbb - 1 do
            let bl = Array.length p.(b).bb_inss in
            if IRSet.mem ir (liveout lh (b, bl)) then
              rl := (b, List.assoc ir outmaps.(b)) :: !rl
          done;
          { rp_res = List.assoc ir inmaps.(b)
          ; rp_list = List.rev !rl
          } :: l
      ) (liveout lh (b, -1)) []
    end
  done;

  rp


(* ** Phi resolution. ** *)
(* Machine program, ready for code generation. *)
type mprog = (loc rins, unit, loc jmpi) bb array

let movgen (p: rprog): mprog =

  let parmov b b' =
    let tmp = LReg (-1) in
    let src, dst =
      let phis = p.(b').bb_phis in
      Array.map (fun x -> List.assoc b x.rp_list) phis,
      Array.map (fun x -> x.rp_res) phis in
    let n = Array.length dst in
    let status = Array.make n `Mv in
    let ms = ref [] in
    let emov dst src =
      ms := {ri_res = dst; ri_ins = `Mov src} :: !ms in
    let rec mv i =
      if src.(i) <> dst.(i) then begin
        status.(i) <- `Mvg;
        for j = 0 to n - 1 do
          if src.(j) = dst.(i) then
            match status.(j) with
            | `Mv -> mv j
            | `Mvg -> emov tmp src.(j); src.(j) <- tmp
            | `Mvd -> ()
        done;
        emov dst.(i) src.(i);
        status.(i) <- `Mvd;
      end in
    for i = 0 to n - 1 do
      if status.(i) = `Mv then mv i
    done;
    List.rev !ms |> Array.of_list in

  let nbb = Array.length p in
  let bmap = Array.init nbb (fun i -> -i - 1) in
  let bn = ref 0 in
  let mp = ref [] in
  let addb b = mp := b :: !mp; incr bn; !bn - 1 in

  for b = 0 to nbb - 1 do
    let b' =
      { bb_name = p.(b).bb_name
      ; bb_phis = [| |]
      ; bb_inss = p.(b).bb_inss
      ; bb_jmp = `Jmp (-1)
      } in
    bmap.(b) <- addb b';
    let movbb suff jb =
      if jb = -1 then -1 else
      let c = parmov b jb in
      if c = [| |] then bmap.(jb) else
      addb
        { bb_name = p.(b).bb_name ^ suff
        ; bb_phis = [| |]
        ; bb_inss = c
        ; bb_jmp = `Jmp bmap.(jb)
        } in
    b'.bb_jmp <- begin
      match p.(b).bb_jmp with
      | `Jmp b1 -> `Jmp (movbb "_mov" b1)
      | `Brz (l, b1, b2) ->
        let b1', b2' =
          if b1 = b + 1 then
            let b2' = movbb "_mov2" b2 in
            let b1' = movbb "_mov1" b1 in
            (b1', b2')
          else
            let b1' = movbb "_mov1" b1 in
            let b2' = movbb "_mov2" b2 in
            (b1', b2') in
        `Brz (l, b1', b2')
    end;
  done;
  List.rev !mp
  |> Array.of_list
  |> Array.map (fun b ->
    let f n =
      if n >= -1 then n else bmap.(-n - 1) in
    { b with bb_jmp =
      match b.bb_jmp with
      | `Jmp b1 -> `Jmp (f b1)
      | `Brz (l, b1, b2) -> `Brz (l, f b1, f b2)
    }
  )

let codegen (p: mprog): string =
  let cl = ref [] in
  let outs s = cl := s :: !cl in
  let outb b = outs (String.make 1 (Char.chr b)) in

  let regmap = [| (* only caller-save regs, for now *)
      0;  (* rax *)
      1;  (* rcx *)
      2;  (* rdx *)
      6;  (* rsi *)
      7;  (* rdi *)
      8;  (* r8  *)
      9;  (* r9  *)
      10; (* r10 *)
      11; (* r11 *)
    |] in
  let regn = function
    | LReg r -> regmap.(r+1)
    | _ -> failwith "register expected in regn" in

  let rexp rg rm =
    let rex = 0x48 in
    let rg, rex = if rg > 7
      then rg-8, rex lor 4
      else rg, rex in
    let rm, rex = if rm > 7
      then rm-8, rex lor 1
      else rm, rex in
    (rex, rg, rm) in

  let modrm ?(md=3) r m =
    (md lsl 6) + (r lsl 3) + m in

  let arit op r r1 r2 =
    if r <> r1 && op <> 0xf7 then begin (* HACK *)
      let rex, r1, r = rexp r1 r in
      outb rex; outb 0x89; outb (modrm r1 r);  (* mov r1, r *)
    end;
    let rex, r2, r = rexp r2 r in
    outb rex; outb op; outb (modrm r2 r)       (* op r2, r *)
      in

  for b = 0 to Array.length p - 1 do
    let is = p.(b).bb_inss in
    for i = 0 to Array.length is - 1 do
      match is.(i) with
      | { ri_res = l; ri_ins = `Bop (l1, op, l2) } ->
        begin match op with
        | Add -> arit 0x01 (regn l) (regn l1) (regn l2)
        | Sub -> arit 0x29 (regn l) (regn l1) (regn l2)
        | CLe -> failwith "CLe not implemented"
        | CEq -> failwith "CEq not implemented"
        end
      | { ri_res = l; ri_ins = `Uop (Neg, l1) } ->
        arit 0xf7 (regn l) 3 (regn l1)
      | _ -> ()
    done
  done;

  outb 0xc3;                                     (* retq *)
  String.concat "" (List.rev !cl)


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

(* ------------------------------------------------------------------------ *)

let _ =
  let oc = open_out "comp.bin" in
  let s = pbasic |> regalloc |> movgen |> codegen in
  output_string oc s;
  close_out oc

(* ------------------------------------------------------------------------ *)

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

let pspill: iprog =
  [| { bb_name = "init"
     ; bb_phis = [||]
     ; bb_inss =
(* 00 *)    [| `Con 42
(* 01 *)     ; `Bop (IRIns (0, 0), Add, IRIns (0, 0))
(* 02 *)     ; `Bop (IRIns (0, 0), Add, IRIns (0, 1))
(* 03 *)     ; `Bop (IRIns (0, 0), Add, IRIns (0, 2))
(* 04 *)     ; `Bop (IRIns (0, 0), Add, IRIns (0, 3))
(* 05 *)     ; `Bop (IRIns (0, 0), Add, IRIns (0, 4))
(* 06 *)     ; `Bop (IRIns (0, 0), Add, IRIns (0, 5))
(* 07 *)     ; `Bop (IRIns (0, 6), Add, IRIns (0, 6))
(* 08 *)     ; `Bop (IRIns (0, 5), Add, IRIns (0, 7))
(* 09 *)     ; `Bop (IRIns (0, 4), Add, IRIns (0, 8))
(* 10 *)     ; `Bop (IRIns (0, 3), Add, IRIns (0, 9))
(* 11 *)     ; `Bop (IRIns (0, 2), Add, IRIns (0, 10))
(* 12 *)     ; `Bop (IRIns (0, 1), Add, IRIns (0, 11))
(* 13 *)     ; `Bop (IRIns (0, 0), Add, IRIns (0, 12))
           |]
     ; bb_jmp = `Brz (IRIns (0, 13), -1, -1)
     }
  |]
