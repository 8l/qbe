type id = int
type ty =
  | TInt of bool * int
  | TArr of int * ty
  | TPtr of ty
  | TVoid
type con = CInt of int
type cnd = Ge | Le | Gt | Lt | Ne | Eq
type ins =
  | IAlloc of ty
  | IMem of id
  | ISto of id * id
  | IAdd of id * id
  | ISub of id * id
  | ICon of ty * con
  | IBr  of id * cnd * id * id
  | IJmp of id
  | IPhi of ty * id * id

let isint = function TInt _ -> true | _ -> false
let isbranch = function IBr _ | IJmp _ -> true | _ -> false

exception Type of string
let tychk blk =
  let typs = Array.make (Array.length blk) TVoid in
  let blks = ref [] in
  let jmp src dst =
    let rec f = function
      | (blk, srcs) :: tl when blk = dst ->
        (blk, src :: srcs) :: tl
      | b :: tl when fst b < dst -> b :: f tl
      | l ->
        let srcs =
          if dst = 0 then [src] else
          if isbranch blk.(dst-1)
          then [src] else [dst-1; src] in
        (dst, srcs) :: l in
    blks := f !blks in
  let f i =                                           (* do easy type checks *)
    let chn n =
      if n >= i || n < 0 then
        raise (Type "broken data dependency") in
    function
    | IPhi (ty, _, _) ->
      if ty = TVoid then
        raise (Type "invalid void phi");
      typs.(i) <- ty
    | ICon (ty, _) -> typs.(i) <- ty
    | IAlloc ty ->
      if ty = TVoid then
        raise (Type "invalid void alloc");
      typs.(i) <- TPtr ty
    | IMem n ->
      chn n;
      (match typs.(n) with
      | TPtr ty -> typs.(i) <- ty
      | _ -> raise (Type "invalid dereference")
      )
    | ISto (a, b) ->
      chn a; chn b;
      if typs.(a) <> TPtr typs.(b) then
        raise (Type "invalid store")
    | IAdd (a, b) ->
      chn a; chn b;
      if not (isint typs.(b)) then
        raise (Type "second add operand not integral");
      (match typs.(a) with
      | (TPtr _) as t -> typs.(i) <- t
      | (TInt _) as t ->
        if t <> typs.(b) then
          raise (Type "invalid heterogeneous addition");
        typs.(i) <- t
      | _ -> raise (Type "invalid type for addition")
      )
    | ISub (a, b) ->
      chn a; chn b;
      (match typs.(a), typs.(b) with
      | (TPtr _ as ta), (TPtr _ as tb) ->
        if ta <> tb then
          raise (Type "substracted pointers have different types");
        typs.(i) <- TInt (true, 64)
      | (TInt _ as ta), (TInt _ as tb) ->
        if ta <> tb then
          raise (Type "invalid heterogeneous substraction");
        typs.(i) <- ta
      | _ -> raise (Type "invalid type for substraction")
      )
    | IBr (_, _, _, dst) -> jmp i dst; jmp i (i+1)
    | IJmp dst -> jmp i dst in
  Array.iteri f blk;
  let f = function                                (* check types at phi nodes *)
    | IPhi (_, a, b) ->
      if typs.(a) <> typs.(b) then
        raise (Type "ill-typed phi node")
    | _ -> () in
  Array.iter f blk;
  let bbase i =
    let rec f base = function
      | [] -> base
      | (b, _) :: _ when b > i -> base
      | (b, _) :: tl -> f b tl in
    f 0 !blks in
  let f i = function                               (* check validity of ssa *)
    | IPhi (_, a, b) ->
      let callers =
        List.map bbase (List.assoc (bbase i) !blks) in
      let ba = bbase a and bb = bbase b in
      if ba = bb
      || not (List.mem ba callers)
      || not (List.mem bb callers)
      then
        raise (Type "invalid phi node");
    | IAdd (a, b) | ISub (a, b) | ISto (a, b) | IBr (a, _, b, _) ->
      let bi = bbase i in
      if bbase a <> bi || bbase b <> bi then
        raise (Type "operands of non-phy not in current block")
    | IMem a ->
      if bbase a <> bbase i then
        raise (Type "operands of non-phy not in current block")
    | IJmp _ | ICon _ | IAlloc _ -> () in
  Array.iteri f blk

                                                          (* tests *)
let _ =
  let int = TInt (true, 32) in
  let p0 = [|
    (* 0 *) ICon (int, CInt 1);
    (* 1 *) ICon (int, CInt 42);
    (* 2 *) IPhi (int, 0, 2);
    (* 3 *) IAdd (1, 2);
    (* 4 *) IJmp 1
  |] in tychk p0
