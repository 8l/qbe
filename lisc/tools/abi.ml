(* fuzzer *)

module R = Random

let maxargs = 10
let maxmems = 16

type _ basety =
  | Char: int basety
  | Short: int basety
  | Int: int basety
  | Long: int basety
  | Float: float basety
  | Double: float basety

type _ structy =
  | Field: 'a basety * 'b structy -> ('a * 'b) structy
  | Empty: unit structy

type _ abity =
  | Base: 'a basety -> 'a abity
  | Struct: 'a structy -> 'a abity

let _ =
  let f = open_in "/dev/urandom" in
  let s = Char.code (input_char f) in
  let s = Char.code (input_char f) + (s lsl 8) in
  R.init s;
  Printf.printf "Seed: %d\n" s;
  ()
