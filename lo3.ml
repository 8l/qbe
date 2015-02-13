(* Generic binary heaps. *)
module Heap: sig
  type 'a t
  val create: ('a -> 'a -> int) -> 'a t
  val add: 'a t -> 'a -> unit
  val pop: 'a t -> 'a option
  val top: 'a t -> 'a option
end = struct
  type 'a t =
    { mutable arr: 'a array
    ; mutable len: int
    ; cmp: 'a -> 'a -> int
    }

  let mkarray n = Array.make n (Obj.magic 0)
  let create cmp = {arr = mkarray 2; len = 0; cmp }
  let top {arr; len; _} =
    if len = 0 then None else Some arr.(1)
  let swap arr i j =
    let tmp = arr.(i) in
    arr.(i) <- arr.(j);
    arr.(j) <- tmp

  let rec bblup cmp arr i =
    let prnt = i/2 in
    if prnt = 0 then () else
    if cmp arr.(prnt) arr.(i) < 0 then () else
    (swap arr prnt i; bblup cmp arr prnt)
  let add ({arr; len; cmp} as hp) x =
    let arr =
      let alen = Array.length arr in
      if alen > len+1 then arr else
      let arr' = mkarray (alen * 2) in
      Array.blit arr 0 arr' 0 alen;
      hp.arr <- arr';
      arr' in
    hp.len <- len + 1;
    arr.(hp.len) <- x;
    bblup cmp arr hp.len

  let rec bbldn cmp arr i len =
    let ch0 = 2*i in
    let ch1 = ch0 + 1 in
    if ch0 > len then () else
    let mn =
      if ch1 > len then ch0 else
      if cmp arr.(ch0) arr.(ch1) < 0
      then ch0 else ch1 in
    if cmp arr.(i) arr.(mn) <= 0 then () else
    (swap arr i mn; bbldn cmp arr mn len)
  let pop ({arr; len; cmp} as hp) =
    if len = 0 then None else
    let t = top hp in
    arr.(1) <- arr.(len);
    hp.len <- len - 1;
    bbldn cmp arr 1 len;
    t
end

let rec popall h =
  match Heap.pop h with
  | None -> []
  | Some x -> x :: popall h

let _ =
  if true then
  let rnd () =
    (2047 land Random.bits ()) *
    ((Random.bits () land 2) - 1) in
  let rec f n = if n = 0 then [] else rnd () :: f (n-1) in
  for n = 1 to 150 do
    for i = 1 to 1_000 do
      let l = f n in
      (* List.iter (Printf.printf "%d, ") l; print_newline (); *)
      let h = Heap.create compare in
      List.iter (Heap.add h) l;
      let l' = popall h in
      assert (List.sort compare l = l');
    done;
    Printf.printf "... %d\n" n;
    flush stdout;
  done;
  print_string "OK!\n"
