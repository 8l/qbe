(* fuzzer *)

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
type test = T: 'a aty * 'a -> test


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


(* Generate types and test vectors. *)
module Gen = struct
  module R = Random

  let init = function
    | None ->
      let f = open_in "/dev/urandom" in
      let seed =
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

  let smax = 4      (* max elements in structs *)
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
    T (ty, t)

  let tests () =
    let rec f n =
      if n = 0 then [] else
      test () :: f (n-1) in
    f (R.int amax)

end

module type OUT = sig
  val extension: string
  val comment: out_channel -> string -> unit
  val caller: out_channel -> test -> test list -> unit
  val callee: out_channel -> test -> test list -> unit
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

  let init oc name (T (ty, t)) =
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
    ; "static void"
    ; "fail(char *chk)"
    ; "{"
    ; "\tfprintf(stderr, \"fail: checking %s\\n\", chk);"
    ; "\tabort();"
    ; "}"
    ; ""
    ]

  let typedef oc name = function
    | T (Struct ts, _) ->
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
    | T (Base b, tb) -> chkbase name (b, tb)
    | T (Struct s, ts) ->
      let rec f: type a. int -> a sty * a -> unit =
        fun i -> function
        | Field (b, s), (tb, ts) ->
          chkbase (Printf.sprintf "%s.f%d" name i) (b, tb);
          f (i+1) (s, ts);
        | Empty, () -> () in
      f 1 (s, ts)

  let argname i = "arg" ^ string_of_int (i+1)

  let proto oc (T (tret, _)) args =
    ctype oc "ret" tret;
    fprintf oc " f(";
    let narg = List.length args in
    List.iteri (fun i (T (targ, _)) ->
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
    let T (tret, _) = ret in
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


let _ =
  let seed = Gen.init None in
  let tret = Gen.test () in
  let targs = Gen.tests () in
  let oc = stdout in
  OutC.comment oc (Printf.sprintf "seed %d" seed);
  (* OutC.caller oc tret targs; *)
  OutC.callee oc tret targs;
  ()
