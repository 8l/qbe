(* Generic binary heaps. *)
module Heap: sig
  type 'a t
  val create: ('a -> 'a -> int) -> 'a t
  val add: 'a t -> 'a -> unit
  val popd: 'a t -> unit
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
  let popd ({arr; len; cmp} as hp) =
    if len = 0 then () else
    arr.(1) <- arr.(len);
    hp.len <- len - 1;
    bbldn cmp arr 1 len
  let pop hp =
    let r = top hp in
    popd hp; r
end
