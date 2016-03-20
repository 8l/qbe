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

  let test: type a. a aty -> a =
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

  let binn = 8   (* default parameters for binomial law of s *)
  and binp = 0.8

  let rec s ?(n=binn) ?(pp=binp) () = (* binomial law *)
    if n = 0 || R.float 1.0 > pp then AS Empty else
    let AB bt = b () in
    let AS st = s ~n:(n-1) () in
    AS (Field (bt, st))

  let a ?(n=binn) ?(pp=binp) ?(ps=0.8) () =
    if R.float 1.0 > ps then
      let AB bt = b () in
      AA (Base bt)
    else
      let AB bt = b () in
      let AS st = s ~n ~pp () in
      AA (Struct (Field (bt, st)))

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

  let ctype oc name =
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
      fprintf oc " %s" name;
    | Struct s ->
      fprintf oc "struct %s { " name;
      cs 1 s;
      fprintf oc "} %s" name;
      ()

  let init oc name (T (ty, t)) =
    let initb: type a. a bty * a -> unit = function
      | Char, i   -> fprintf oc "%d" i
      | Short, i  -> fprintf oc "%d" i
      | Int, i    -> fprintf oc "%d" i
      | Long, i   -> fprintf oc "%d" i
      | Float, f  -> fprintf oc "%ff" f
      | Double, f -> fprintf oc "%f" f in
    let inits s =
      let rec f: type a. a sty * a -> unit = function
        | Field (b, s), (tb, ts) ->
          initb (b, tb);
          fprintf oc ", ";
          f (s, ts)
        | Empty, () -> () in
      fprintf oc "{ ";
      f s;
      fprintf oc "}"; in
    ctype oc name ty;
    fprintf oc " = ";
    begin match (ty, t) with
    | Base b, tb -> initb (b, tb)
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
    ; "fail(int ret, int chk)"
    ; "{"
    ; "\tfprintf(stderr, \"fail: %s check number %d\\n\""
    ; "\t\tret ? \"return\" : \"argument\", chk);"
    ; "\tabort();"
    ; "}"
    ; ""
    ]

  let caller oc ret args =
    prelude oc;
    fprintf oc "int\nmain()\n{";
    fprintf oc "\t";
    init oc "ret" ret;
    fprintf oc "}\n";
    ()

end


let _ =
  let _seed = Gen.init None in
  let AA ty = Gen.a () in
  let t = Gen.test ty in
  OutC.caller stdout (T (ty, t)) []
