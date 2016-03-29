(* abi fuzzer, generates two modules one calling
 * the other in two possibly different languages
 *)

type _ bty =
  | Char: int bty
  | Short: int bty
  | Int: int bty
  | Long: int bty
  | Float: float bty
  | Double: float bty

type _ sty =
  | Field: 'a bty * 'b sty -> ('a * 'b) sty
  | Empty: unit sty

type _ aty =
  | Base: 'a bty -> 'a aty
  | Struct: 'a sty -> 'a aty

type anyb = AB: _ bty -> anyb (* kinda boring... *)
type anys = AS: _ sty -> anys
type anya = AA: _ aty -> anya
type testb = TB: 'a bty * 'a -> testb
type testa = TA: 'a aty * 'a -> testa


let align a x =
  let m = x mod a in
  if m <> 0 then x + (a-m) else x

let btysize: type a. a bty -> int = function
  | Char -> 1
  | Short -> 2
  | Int -> 4
  | Long -> 8
  | Float -> 4
  | Double -> 8

let btyalign = btysize

let styempty: type a. a sty -> bool = function
  | Field _ -> false
  | Empty -> true

let stysize s =
  let rec f: type a. int -> a sty -> int =
    fun sz -> function
    | Field (b, s) ->
      let a = btyalign b in
      f (align a sz + btysize b) s
    | Empty -> sz in
  f 0 s

let rec styalign: type a. a sty -> int = function
  | Field (b, s) -> max (btyalign b) (styalign s)
  | Empty -> 1


(* Generate types and test vectors. *)
module Gen = struct
  module R = Random

  let init = function
    | None ->
      let f = open_in "/dev/urandom" in
      let seed =
        Char.code (input_char f) lsl 16 +
        Char.code (input_char f) lsl 8 +
        Char.code (input_char f) in
      close_in f;
      R.init seed;
      seed
    | Some seed ->
      R.init seed;
      seed

  let int sz =
    let bound = 1 lsl (8 * min sz 3 - 1) in
    let i = R.int bound in
    if R.bool () then - i else i

  let float () =
    let f = R.float 1000. in
    if R.bool () then -. f else f

  let testv: type a. a aty -> a =
    let tb: type a. a bty -> a = function (* eh, dry... *)
      | Float  -> float ()
      | Double -> float ()
      | Char   -> int (btysize Char)
      | Short  -> int (btysize Short)
      | Int    -> int (btysize Int)
      | Long   -> int (btysize Long) in
    let rec ts: type a. a sty -> a = function
      | Field (b, s) -> (tb b, ts s)
      | Empty -> () in
    function
    | Base b -> tb b
    | Struct s -> ts s

  let b () = (* uniform *)
    match R.int 6 with
    | 0 -> AB Char
    | 1 -> AB Short
    | 2 -> AB Int
    | 3 -> AB Long
    | 4 -> AB Float
    | _ -> AB Double

  let smax = 5      (* max elements in structs *)
  let structp = 0.3 (* odds of having a struct type *)
  let amax = 8      (* max function arguments *)

  let s () =
    let rec f n =
      if n = 0 then AS Empty else
      let AB bt = b () in
      let AS st = f (n-1) in
      AS (Field (bt, st)) in
    f (1 + R.int (smax-1))

  let a () =
    if R.float 1.0 > structp then
      let AB bt = b () in
      AA (Base bt)
    else
      let AB bt = b () in
      let AS st = s () in
      AA (Struct (Field (bt, st)))

  let test () =
    let AA ty = a () in
    let t = testv ty in
    TA (ty, t)

  let tests () =
    let rec f n =
      if n = 0 then [] else
      test () :: f (n-1) in
    f (R.int amax)

end


(* Code generation for C *)
module OutC = struct
  open Printf

  let ctypelong oc name =
    let cb: type a. a bty -> unit = function
      | Char   -> fprintf oc "char"
      | Short  -> fprintf oc "short"
      | Int    -> fprintf oc "int"
      | Long   -> fprintf oc "long"
      | Float  -> fprintf oc "float"
      | Double -> fprintf oc "double" in
    let rec cs: type a. int -> a sty -> unit =
      fun i -> function
      | Field (b, s) ->
        cb b;
        fprintf oc " f%d; " i;
        cs (i+1) s;
      | Empty -> () in
    function
    | Base b ->
      cb b;
    | Struct s ->
      fprintf oc "struct %s { " name;
      cs 1 s;
      fprintf oc "}";
      ()

  let ctype: type a. out_channel -> string -> a aty -> unit =
    fun oc name -> function
    | Struct _ -> fprintf oc "struct %s" name
    | t -> ctypelong oc "" t

  let base: type a. out_channel -> a bty * a -> unit =
    fun oc -> function
    | Char, i   -> fprintf oc "%d" i
    | Short, i  -> fprintf oc "%d" i
    | Int, i    -> fprintf oc "%d" i
    | Long, i   -> fprintf oc "%d" i
    | Float, f  -> fprintf oc "%ff" f
    | Double, f -> fprintf oc "%f" f

  let init oc name (TA (ty, t)) =
    let inits s =
      let rec f: type a. a sty * a -> unit = function
        | Field (b, s), (tb, ts) ->
          base oc (b, tb);
          fprintf oc ", ";
          f (s, ts)
        | Empty, () -> () in
      fprintf oc "{ ";
      f s;
      fprintf oc "}"; in
    ctype oc name ty;
    fprintf oc " %s = " name;
    begin match (ty, t) with
    | Base b, tb -> base oc (b, tb)
    | Struct s, ts -> inits (s, ts)
    end;
    fprintf oc ";\n";
    ()

  let extension = ".c"

  let comment oc s =
    fprintf oc "/* %s */\n" s

  let prelude oc = List.iter (fprintf oc "%s\n")
    [ "#include <stdio.h>"
    ; "#include <stdlib.h>"
    ; ""
    ; "static void fail(char *chk)"
    ; "{"
    ; "\tfprintf(stderr, \"fail: checking %s\\n\", chk);"
    ; "\tabort();"
    ; "}"
    ; ""
    ]

  let typedef oc name = function
    | TA (Struct ts, _) ->
      ctypelong oc name (Struct ts);
      fprintf oc ";\n";
    | _ -> ()

  let check oc name =
    let chkbase: type a. string -> a bty * a -> unit =
      fun name t ->
        fprintf oc "\tif (%s != " name;
        base oc t;
        fprintf oc ")\n\t\tfail(%S);\n" name; in
    function
    | TA (Base b, tb) -> chkbase name (b, tb)
    | TA (Struct s, ts) ->
      let rec f: type a. int -> a sty * a -> unit =
        fun i -> function
        | Field (b, s), (tb, ts) ->
          chkbase (Printf.sprintf "%s.f%d" name i) (b, tb);
          f (i+1) (s, ts);
        | Empty, () -> () in
      f 1 (s, ts)

  let argname i = "arg" ^ string_of_int (i+1)

  let proto oc (TA (tret, _)) args =
    ctype oc "ret" tret;
    fprintf oc " f(";
    let narg = List.length args in
    List.iteri (fun i (TA (targ, _)) ->
      ctype oc (argname i) targ;
      fprintf oc " %s" (argname i);
      if i <> narg-1 then
        fprintf oc ", ";
    ) args;
    fprintf oc ")";
    ()

  let caller oc ret args =
    let narg = List.length args in
    prelude oc;
    typedef oc "ret" ret;
    List.iteri (fun i arg ->
      typedef oc (argname i) arg;
    ) args;
    proto oc ret args;
    fprintf oc ";\n\nint main()\n{\n";
    List.iteri (fun i arg ->
      fprintf oc "\t";
      init oc (argname i) arg;
    ) args;
    fprintf oc "\t";
    let TA (tret, _) = ret in
    ctype oc "ret" tret;
    fprintf oc " ret;\n\n";
    fprintf oc "\tret = f(";
    List.iteri (fun i _ ->
      fprintf oc "%s" (argname i);
      if i <> narg-1 then
        fprintf oc ", ";
    ) args;
    fprintf oc ");\n";
    check oc "ret" ret;
    fprintf oc "\n\treturn 0;\n}\n";
    ()

  let callee oc ret args =
    prelude oc;
    typedef oc "ret" ret;
    List.iteri (fun i arg ->
      typedef oc (argname i) arg;
    ) args;
    fprintf oc "\n";
    proto oc ret args;
    fprintf oc "\n{\n\t";
    init oc "ret" ret;
    fprintf oc "\n";
    List.iteri (fun i arg ->
      check oc (argname i) arg;
    ) args;
    fprintf oc "\n\treturn ret;\n}\n";
    ()

end

(* Code generation for QBE *)
module OutIL = struct
  open Printf

  let comment oc s =
    fprintf oc "# %s\n" s

  let tmp, lbl =
    let next = ref 0 in
    (fun () -> incr next; "%t" ^ (string_of_int !next)),
    (fun () -> incr next; "@l" ^ (string_of_int !next))

  let bvalue: type a. a bty * a -> string = function
    | Char, i   -> sprintf "%d" i
    | Short, i  -> sprintf "%d" i
    | Int, i    -> sprintf "%d" i
    | Long, i   -> sprintf "%d" i
    | Float, f  -> sprintf "s_%f" f
    | Double, f -> sprintf "d_%f" f

  let btype: type a. a bty -> string = function
    | Char   -> "w"
    | Short  -> "w"
    | Int    -> "w"
    | Long   -> "l"
    | Float  -> "s"
    | Double -> "d"

  let extension = ".ssa"

  let argname i = "arg" ^ string_of_int (i+1)

  let siter oc base s g =
    let rec f: type a. int -> int -> a sty * a -> unit =
      fun id off -> function
      | Field (b, s), (tb, ts) ->
        let off = align (btyalign b) off in
        let addr = tmp () in
        fprintf oc "\t%s =l add %d, %s\n" addr off base;
        g id addr (TB (b, tb));
        f (id + 1) (off + btysize b) (s, ts);
     | Empty, () -> () in
   f 0 0 s

  let bmemtype b =
    if AB b = AB Char  then "b" else
    if AB b = AB Short then "h" else
    btype b

  let init oc = function
    | TA (Base b, tb) -> bvalue (b, tb)
    | TA (Struct s, ts) ->
      let base = tmp () in
      fprintf oc "\t%s =l alloc%d %d\n"
        base (styalign s) (stysize s);
      siter oc base (s, ts)
      begin fun _ addr (TB (b, tb)) ->
        fprintf oc "\tstore%s %s, %s\n"
          (bmemtype b) (bvalue (b, tb)) addr;
      end;
      base

  let check oc id name =
    let bcheck = fun id name (b, tb) ->
      let tcmp = tmp () in
      let nxtl = lbl () in
      fprintf oc "\t%s =w ceq%s %s, %s\n"
        tcmp (btype b) name (bvalue (b, tb));
      fprintf oc "\tstorew %d, %%failcode\n" id;
      fprintf oc "\tjnz %s, %s, @fail\n" tcmp nxtl;
      fprintf oc "%s\n" nxtl; in
    function
    | TA (Base Char, i) ->
      let tval = tmp () in
      fprintf oc "\t%s =w extsb %s\n" tval name;
      bcheck id tval (Int, i)
    | TA (Base Short, i) ->
      let tval = tmp () in
      fprintf oc "\t%s =w extsh %s\n" tval name;
      bcheck id tval (Int, i)
    | TA (Base b, tb) ->
      bcheck id name (b, tb)
    | TA (Struct s, ts) ->
      siter oc name (s, ts)
      begin fun id' addr (TB (b, tb)) ->
        let tval = tmp () in
        let lsuffix =
          if AB b = AB Char  then "sb" else
          if AB b = AB Short then "sh" else
          "" in
        fprintf oc "\t%s =%s load%s %s\n"
          tval (btype b) lsuffix addr;
        bcheck (100*id + id'+1) tval (b, tb);
      end;
      ()

  let ttype name = function
    | TA (Base b, _)   -> btype b
    | TA (Struct _, _) -> ":" ^ name

  let typedef oc name =
    let rec f: type a. a sty -> unit = function
      | Field (b, s) ->
        fprintf oc "%s" (bmemtype b);
        if not (styempty s) then
          fprintf oc ", ";
        f s;
      | Empty -> () in
    function
    | TA (Struct ts, _) ->
      fprintf oc "type :%s = { " name;
      f ts;
      fprintf oc " }\n";
    | _ -> ()

  let postlude oc = List.iter (fprintf oc "%s\n")
    [ "@fail"
    ;  "# failure code"
    ; "\t%fcode =w loadw %failcode"
    ; "\t%f0 =w call $printf(l $failstr, w %fcode)"
    ; "\t%f1 =w call $abort()"
    ; "\tret 0"
    ; "}"
    ; ""
    ; "data $failstr = { b \"fail on check %d\\n\", b 0 }"
    ]

  let caller oc ret args =
    let narg = List.length args in
    List.iteri (fun i arg ->
      typedef oc (argname i) arg;
    ) args;
    typedef oc "ret" ret;
    fprintf oc "\nexport function w $main() {\n";
    fprintf oc "@start\n";
    fprintf oc "\t%%failcode =l alloc4 4\n";
    let targs = List.mapi (fun i arg ->
      comment oc ("define argument " ^ (string_of_int (i+1)));
      (ttype (argname i) arg, init oc arg)
    ) args in
    comment oc "call test function";
    fprintf oc "\t%%ret =%s call $f(" (ttype "ret" ret);
    List.iteri (fun i (ty, tmp) ->
      fprintf oc "%s %s" ty tmp;
      if i <> narg-1 then
        fprintf oc ", ";
    ) targs;
    fprintf oc ")\n";
    comment oc "check the return value";
    check oc 0 "%ret" ret;
    fprintf oc "\tret 0\n";
    postlude oc;
    ()

  let callee oc ret args =
    let narg = List.length args in
    List.iteri (fun i arg ->
      typedef oc (argname i) arg;
    ) args;
    typedef oc "ret" ret;
    fprintf oc "\nexport function %s $f(" (ttype "ret" ret);
    List.iteri (fun i arg ->
      let a = argname i in
      fprintf oc "%s %%%s" (ttype a arg) a;
      if i <> narg-1 then
        fprintf oc ", ";
    ) args;
    fprintf oc ") {\n";
    fprintf oc "@start\n";
    fprintf oc "\t%%failcode =l alloc4 4\n";
    List.iteri (fun i arg ->
      comment oc ("checking argument " ^ (string_of_int (i+1)));
      check oc (i+1) ("%" ^ argname i) arg;
    ) args;
    comment oc "define the return value";
    let rettmp = init oc ret in
    fprintf oc "\tret %s\n" rettmp;
    postlude oc;
    ()

end


module type OUT = sig
  val extension: string
  val comment: out_channel -> string -> unit
  val caller: out_channel -> testa -> testa list -> unit
  val callee: out_channel -> testa -> testa list -> unit
end

let _ =
  let usage code =
    Printf.eprintf "usage: abi.ml [-s SEED] DIR {c,ssa} {c,ssa}\n";
    exit code in

  let outmod = function
    | "c"   -> (module OutC : OUT)
    | "ssa" -> (module OutIL: OUT)
    | _ -> usage 1 in

  let seed, dir, mcaller, mcallee =
    match Sys.argv with
    | [| _; "-s"; seed; dir; caller; callee |] ->
      let seed =
        try Some (int_of_string seed) with
        Failure _ -> usage 1 in
      seed, dir, outmod caller, outmod callee
    | [| _; dir; caller; callee |] ->
      None, dir, outmod caller, outmod callee
    | [| _; "-h" |] ->
      usage 0
    | _ ->
      usage 1 in

  let seed = Gen.init seed in
  let tret = Gen.test () in
  let targs = Gen.tests () in
  let module OCaller = (val mcaller : OUT) in
  let module OCallee = (val mcallee : OUT) in
  let ocaller = open_out (dir ^ "/caller" ^ OCaller.extension) in
  let ocallee = open_out (dir ^ "/callee" ^ OCallee.extension) in
  OCaller.comment ocaller (Printf.sprintf "seed %d" seed);
  OCallee.comment ocallee (Printf.sprintf "seed %d" seed);
  OCaller.caller ocaller tret targs;
  OCallee.callee ocallee tret targs;
  ()
