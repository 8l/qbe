let dent = 4

type doc = item list
and item =
  | Verb of string * string
  | Par of string
  | Ulist of doc list
  | Olist of doc list
  | Title of int * string

let (|>) x f = f x

module String = struct
  include String

  let suff s n =
    let l = String.length s in
    if n >= l then "" else
    String.sub s n (l-n)

  let haspref p s =
    let lp = String.length p in
    String.length s >= lp &&
    p = String.sub s 0 lp
end

let warn n e =
  Printf.eprintf "Warning line %d: %s.\n" n e

let getdent s =
  let rec f n =
    if n >= String.length s then 0 else
    if s.[n] = ' ' then f (n+1) else
    if s.[n] = '\t' then f (n+8) else
    n/dent in
  f 0

let dedent s i =
  let rec f i j =
    if i <= 0 then (-i, j) else
    if j >= String.length s then (0, j) else
    if s.[j] = ' ' then f (i-1) (j+1) else
    if s.[j] = '\t' then f (i-8) (j+1) else
    (0, j) in
  let (p, j) = f (i*dent) 0 in
  String.make p ' ' ^ String.suff s j

let rec getlines acc n =
  match try Some (read_line ()) with End_of_file -> None with
  | Some s ->
    getlines ((n, getdent s, s) :: acc) (n+1)
  | None -> List.rev acc

let endnum s =
  let rec f n =
    if n >= String.length s then 0 else
    let c = Char.code s.[n] in
    if c >= 48 && c <= 57 then f (n+1) else
    if s.[n] = ' ' then f (n+1) else
    if s.[n] = '.' then (n+1) else
    0 in
  f 0
let skipnum s = String.suff s (endnum s)
let skipbullet s = String.suff (dedent s 1000) 2

let gettitles lines =
  let titles = Hashtbl.create 100 in
  let insert lvl n t =
    let t = skipnum t in
    if Hashtbl.mem titles t then
      warn n "title has multiple definitions";
    Hashtbl.add titles t (lvl, n) in
  lines |> List.iter begin fun (n, lvl, t) ->
    if lvl <> 0 then () else
    if String.haspref "- " t then insert 0 n t else
    if String.haspref "~ " t then insert 1 n t else
    ()
  end;
  titles

let top lines =
  match !lines with
  | [] -> None
  | l :: _ -> Some l

let pop lines =
  match top lines with
  | None -> None
  | l -> lines := List.tl !lines; l

let push lines l =
  lines := l :: !lines

let isolist l = endnum l <> 0
let isulist l = String.haspref "* " (dedent l 1000)

let getverb lines idnt =
  let rec f ls =
    match top lines with
    | Some (n, i, l) when i >= idnt || l = "" ->
      pop lines |> ignore;
      f (dedent l idnt :: ls)
    | _ ->
      let ls =
        if List.hd ls = ""
          then List.tl ls
          else ls in
      List.rev ls |>
      String.concat "\n" in
  f []

let getpar lines idnt =
  let rec f ls =
    match top lines with
    | Some (n, i, l)
      when i = idnt
        && l <> ""
        && not (isolist l)
        && not (isulist l) ->
      pop lines |> ignore;
      f (l :: ls)
    | _ ->
      List.rev ls |>
      String.concat "\n" in
  f []

let mergedoc =
  let rec aggreg f = function
    | (i :: is) as is'->
      begin match f i with
      | Some l ->
        let l', is = aggreg f is in
        List.append l l', is
      | None -> [], is'
      end
    | is -> [], is in
  let ul = function Ulist l -> Some l | _ -> None in
  let ol = function Olist l -> Some l | _ -> None in
  let rec f d = match d with
    | Ulist _ :: _ ->
      let l, d = aggreg ul d in
      Ulist l :: f d
    | Olist _ :: _ ->
      let l, d = aggreg ol d in
      Olist l :: f d
    | i :: d -> i :: f d
    | [] -> [] in
  f

let rec getdoc lines si acc =
  match top lines with
  | Some (n, i, l) ->
    if i = si && isolist l then begin             (* Olist item *)
      pop lines |> ignore;
      push lines (n, i+1, skipnum l);
      let li = getdoc lines (si+1) [] in
      getdoc lines si (Olist [li] :: acc);
    end else
    if i = si && isulist l then begin             (* Ulist item *)
      pop lines |> ignore;
      push lines (n, i+1, skipbullet l);
      let li = getdoc lines (si+1) [] in
      getdoc lines si (Ulist [li] :: acc);
    end else
    if i > si then begin                          (* Verb item *)
      let ty =
        if l.[0] <> '[' then "" else begin
          pop lines |> ignore;
          l
        end in
      let verb = getverb lines i in
      getdoc lines si (Verb (ty, verb) :: acc);
    end else
    if si = 0 && String.haspref "~ " l
    || si = 0 && String.haspref "- " l then begin  (* Titles *)
      pop lines |> ignore;
      let lvl = if l.[0] = '-' then 0 else 1 in
      let tit = String.suff l 2 in
      getdoc lines si (Title (lvl, tit) :: acc);
    end else
    if String.haspref "---" l
    || String.haspref "~~~" l
    || l = "" then begin                          (* Decorations *)
      pop lines |> ignore;
      getdoc lines si acc;
    end else
    if i = si then begin                          (* Par item *)
      let par = getpar lines si in
      getdoc lines si (Par par :: acc);
    end else
      List.rev acc |> mergedoc
  | None -> List.rev acc |> mergedoc

let rec dochtml d =
  let open Printf in
  let rec prlist =
    List.iter begin fun d ->
      match d with
      | Par p :: d -> printf "<li>%s\n" p; dochtml d
      | d -> printf "<li>"; dochtml d;
    end in
  let itemhtml = function
    | Title (0, t) ->
      printf "<h3>%s</h3>\n" t;
    | Title (_, t) ->
      printf "<h4>%s</h4>\n" t;
    | Olist l ->
      printf "<ol>\n";
      prlist l;
      printf "</ol>\n";
    | Ulist l ->
      printf "<ul>\n";
      prlist l;
      printf "</ul>\n";
    | Verb (_, v) ->
      printf "<pre>\n%s\n</pre>\n" v;
    | Par p ->
      printf "<p>\n%s\n</p>\n" p; in
  List.iter itemhtml d

let _ =
  let lines = getlines [] 1 in
  let _ = gettitles lines in
  getdoc (ref lines) 0 [] |> dochtml
