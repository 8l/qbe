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


let btysize: type a. a bty -> int = function
  | Char -> 1
  | Short -> 2
  | Int -> 4
  | Long -> 8
  | Float -> 4
  | Double -> 8

let btyalign = btysize


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

  let binn = 10   (* default parameters for binomial law of s *)
  and binp = 0.5

  let rec s ?(n=binn) ?(pp=binp) () = (* binomial law *)
    if n = 0 || R.float 1.0 > pp then AS Empty else
    let AB bt = b () in
    let AS st = s ~n:(n-1) () in
    AS (Field (bt, st))

  let a ?(n=binn) ?(pp=binp) ?(ps=0.2) () =
    if R.float 1.0 > ps then
      let AB bt = b () in
      AA (Base bt)
    else
      let AS st = s ~n ~pp () in
      AA (Struct st)

end


(* Code generation for C *)
module OutC = struct
  open Printf

end
