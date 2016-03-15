let dent = 4

type doc = item list
and item =
  | Verb of string * string
  | Par of (string * bool)
  | Ulist of doc list
  | Olist of doc list
  | Title of int * string * string

let (|>) x f = f x

let isspace = String.contains " \n\t"

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

  let trim s =
    let l = String.length s in
    let i = ref 0 and j = ref (l-1) in
    while !i<l && isspace s.[!i]
      do incr i done;
    while !j>=0 && isspace s.[!j]
      do decr j done;
    if !j = -1 then s else sub s !i (!j- !i+1)
end

let idify s =
  let rec f i cs =
    if i >= String.length s then cs else
    match s.[i] with
    | ' ' -> f (i+1) ("-" :: cs)
    | c   -> f (i+1) (String.make 1 c :: cs) in
  f 0 [] |> List.rev |> String.concat ""

let warn = Printf.eprintf

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

let matchs skip fin s =
  let rec f n =
    if n >= String.length s then 0 else
    if s.[n] = fin then (n+1) else
    if String.contains skip s.[n] then f (n+1) else
    0 in
  f 0

let endnum = matchs " 0123456789" '.'
let endbul = matchs " " '*'
let skipnum s = String.suff s (endnum s)
let skipbul s = String.suff s (endbul s)

let gettitles lines =
  let titles = Hashtbl.create 100 in
  let insert lvl n t =
    let t = String.trim (skipnum (String.suff t 2)) in
    if Hashtbl.mem titles t then
      warn "line %d: title has multiple definitions\n" n;
    Hashtbl.add titles t (lvl, idify t) in
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
  lines := List.tl !lines
let push lines l =
  lines := l :: !lines

let isolist l = endnum l <> 0
let isulist l = endbul l <> 0

let getverb lines idnt =
  let rec skip = function
    | s :: l when String.trim s = "" -> skip l
    | l -> l in
  let rec f ls =
    match top lines with
    | Some (n, i, l)
      when i >= idnt
        || String.trim l = "" ->
      pop lines;
      f (dedent l idnt :: ls)
    | _ ->
      skip ls |> List.rev |>
      String.concat "\n" in
  f []

let getpar lines idnt =
  let empty = function
    | Some (_, _, l) -> String.trim l = ""
    | _ -> false in
  let rec f ls =
    match top lines with
    | Some (n, i, l)
      when i = idnt
        && l <> ""
        && not (isolist l)
        && not (isulist l) ->
      pop lines;
      f (l :: ls)
    | t ->
      String.concat "\n" (List.rev ls),
      empty t in
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
      pop lines;
      push lines (n, i+1, skipnum l);
      let li = getdoc lines (si+1) [] in
      getdoc lines si (Olist [li] :: acc);
    end else
    if i = si && isulist l then begin             (* Ulist item *)
      pop lines;
      push lines (n, i+1, skipbul l);
      let li = getdoc lines (si+1) [] in
      getdoc lines si (Ulist [li] :: acc);
    end else
    if i > si then begin                          (* Verb item *)
      let ty =
        let l = dedent l i in
        if l.[0] <> '`' then "" else begin
          pop lines;
          String.suff l 1
        end in
      let verb = getverb lines (si+1) in
      getdoc lines si (Verb (ty, verb) :: acc);
    end else
    if si = 0 && String.haspref "~ " l
    || si = 0 && String.haspref "- " l then begin (* Titles *)
      pop lines;
      let lvl = if l.[0] = '-' then 0 else 1 in
      let tit = String.suff l 2 in
      let id = idify (String.trim (skipnum tit)) in
      getdoc lines si (Title (lvl, id, tit) :: acc);
    end else
    if String.haspref "---" l
    || String.haspref "~~~" l
    || l = "" then begin                          (* Decorations *)
      pop lines;
      getdoc lines si acc;
    end else
    if i = si then begin                          (* Par item *)
      let par = getpar lines si in
      getdoc lines si (Par par :: acc);
    end else
      List.rev acc |> mergedoc
  | None -> List.rev acc |> mergedoc

type printer =
  { pchar: char -> unit
  ; plink: string -> unit
  ; pcode: string -> unit
  }

let print pp s =
  let l = String.length s in
  let rec getlink j spc =
    if j >= l || s.[j] = '>' then j+1, "" else
    if isspace s.[j] then
      getlink (j+1) true
    else
      let j', t = getlink (j+1) false in
      if spc then
        j', Printf.sprintf " %c%s" s.[j] t
      else
        j', Printf.sprintf  "%c%s" s.[j] t in
  let getlink j =
    let j', s = getlink j false in
    j', String.trim s in
  let rec getdlim j d =
    if j >= l || s.[j] = d then j+1, "" else
    let j', t = getdlim (j+1) d in
    j', Printf.sprintf "%c%s" s.[j] t in
  let rec f i =
    if i >= l then () else
    match s.[i] with
    | '<' when i < l-1 && s.[i+1] = '@' ->
      let i, t = getlink (i+2) in
      pp.plink t;
      f i
    | '`' ->
      let i, t = getdlim (i+1) '`' in
      pp.pcode t;
      f i
    | c ->
      pp.pchar c;
      f (i+1)
  in f 0

let rec dochtml titles d =
  let open Printf in
  let pchar = function
    | '<' -> printf "&lt;"
    | '>' -> printf "&gt;"
    | '&' -> printf "&amp;"
    | c   -> printf "%c" c in
  let escape = String.iter pchar in
  let plink l =
    try
      let (_, id) = Hashtbl.find titles l in
      printf "<a href=\"#%s\">%s</a>" id l
    with Not_found ->
      warn "warning: unresolved link '%s'\n" l;
      printf "<a href=\"#\">%s</a>" l in
  let pcode s =
    printf "<code>";
    escape s;
    printf "</code>"; in
  let pp = {pchar; plink; pcode} in
  let rec plist =
    List.iter begin fun d ->
      match d with
      | Par (p, nl) :: d when
        not nl || d = [] ->
        printf "<li>";
        print pp p;
        printf "\n";
        dochtml titles d;
      | d ->
        printf "<li>";
        dochtml titles d;
    end in
  let itemhtml = function
    | Title (0, id, t) ->
      printf "<h3><a id='%s'>" id;
      escape t;
      printf "</a></h3>\n";
    | Title (_, id, t) ->
      printf "<h4><a id='%s'>" id;
      escape t;
      printf "</a></h4>\n";
    | Olist l ->
      printf "<ol>\n";
      plist l;
      printf "</ol>\n";
    | Ulist l ->
      printf "<ul>\n";
      plist l;
      printf "</ul>\n";
    | Verb (cls, v) ->
      if cls <> ""
      then printf "<pre class=\"%s\">" cls
      else printf "<pre>\n";
      escape v;
      printf "\n</pre>\n";
    | Par (p, _) ->
      printf "<p>\n";
      print pp p;
      printf "\n</p>\n"; in
  List.iter itemhtml d

let _ =
  let lines = getlines [] 1 in
  let titles = gettitles lines in
  getdoc (ref lines) 0 [] |> dochtml titles
