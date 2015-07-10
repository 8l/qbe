(* This is a module to spit simple ELF
   object files that can afterwards be
   linked to build an application.
*)

let hash s =
  (* The ELF hash function. *)
  let open Int64 in (* I doubt this is necessary... *)
  let rec f p h =
    if p = String.length s then to_int h else
    let h = shift_left h 4 in
    let h = add h (of_int (int_of_char s.[p])) in
    let g = logand h (of_int 0xf0000000) in
    let h = logxor h (shift_right g 24) in
    f (p+1) (logand h (of_int 0x0fffffff)) in
  f 0 (of_int 0)

let le n x =
  (* Make a string of bytes in little endian convention. *)
  let b = Bytes.create n in
  let rec f i x =
    if i = n then () else
    let d = char_of_int (x land 0xff) in
    Bytes.set b i d;
    f (i+1) (x lsr 8) in
  f 0 x; Bytes.to_string b

let stt_NOTYPE = 0
let stt_OBJECT = 1
let stt_FUNC   = 2

let stb_LOCAL  = 0
let stb_GLOBAL = 16
let stb_WEAK   = 32

let sht_NULL     = le 4 0
let sht_PROGBITS = le 4 1
let sht_SYMTAB   = le 4 2
let sht_STRTAB   = le 4 3
let sht_RELA     = le 4 4
let sht_NOTE     = le 4 7
let sht_NOBITS   = le 4 8

let shf_WRITE     = 1
let shf_ALLOC     = 2
let shf_EXECINSTR = 4

let barebones_elf oc fn text =
  let header = String.concat ""
    [ "\x7fELF"                          (* e_ident, magic *)
    ; "\x02"                             (* e_ident, ELFCLASS64 *)
    ; "\x01"                             (* e_ident, ELFDATA2LSB *)
    ; "\x01"                             (* e_indent, EV_CURRENT *)
    ; "\x00"                             (* e_ident, ELFOSABI_SYSV *)
    ; "\x00"                             (* e_ident, ABI version *)
    ; "\x00\x00\x00\x00\x00\x00\x00"     (* e_ident, padding *)
    ; "\x01\x00"                         (* e_type, ET_REL *)
    ; "\x3e\x00"                         (* e_machine, EM_X86_64 *)
    ; "\x01\x00\x00\x00"                 (* e_version, EV_CURRENT *)
    ; "\x00\x00\x00\x00\x00\x00\x00\x00" (* e_entry, unused *)
    ; "\x00\x00\x00\x00\x00\x00\x00\x00" (* e_phoff, unused *)
    ; "\x40\x00\x00\x00\x00\x00\x00\x00" (* e_shoff, 64 *)
    ; "\x00\x00\x00\x00"                 (* e_flags, 0 *)
    ; "\x40\x00"                         (* e_hsize, 64 *)
    ; "\x00\x00"                         (* e_phentsize, 0 *)
    ; "\x00\x00"                         (* e_phnum, 0 *)
    ; "\x40\x00"                         (* e_shentsize, 64 *)
    ; "\x07\x00"                         (* e_shnum, 7 *)
    ; "\x06\x00"                         (* e_shstrndx, 6 *)
    ] in

  (* We will use the following section organization.
     1- .text   PROGBITS
     2- .data   PROGBITS
     3- .bss    NOBITS
     4- .rela   RELA
     5- .symtab SYMTAB
     6- .strtab STRTAB
  *)

  let adds s x = (String.length s, s ^ x ^ "\x00") in
  (* section names *)
  let textstr, strtab = adds "\x00" ".text" in
  let datastr, strtab = adds strtab ".data" in
  let bssstr , strtab = adds strtab ".bss"  in
  let relastr, strtab = adds strtab ".rela" in
  let symtstr, strtab = adds strtab ".symt" in
  let strtstr, strtab = adds strtab ".strt" in
  (* function names *)
  let fnstr, strtab = adds strtab fn in

  let symtab = String.concat ""
    [ le 0x18 0                      (* first symbol is reserved *)
    ; le 4 fnstr                     (* st_name *)
    ; le 1 (stt_FUNC lor stb_GLOBAL) (* st_info *)
    ; "\x00"                         (* st_other *)
    ; le 2 1                         (* st_shndx, .text *)
    ; le 8 0                         (* st_value, offset in .text section *)
    ; le 8 (String.length text)      (* st_size *)
    ] in

  let textoff = 64 + 7 * 64 in
  let txtlen, txtpad =
    let l = String.length text in
    let p = (l + 7) land 7 in
    (l, p) in
  let dataoff = textoff + txtlen + txtpad in
  let bssoff  = dataoff + 0 in
  let relaoff = bssoff + 0 in
  let symtoff = relaoff + 0 in
  let strtoff = symtoff + String.length symtab in

  let sh = String.concat ""
    [ le 64 0 (* first section header is reserved *)
    (* .text *)
    ; le 4 textstr                   (* sh_name *)
    ; sht_PROGBITS                   (* sh_type *)
    ; le 8 (shf_ALLOC lor shf_EXECINSTR) (* sh_flags *)
    ; le 8 0                         (* sh_addr *)
    ; le 8 textoff                   (* sh_offset *)
    ; le 8 txtlen                    (* sh_size *)
    ; le 4 0                         (* sh_link *)
    ; le 4 0                         (* sh_info *)
    ; le 8 1                         (* sh_addralign *)
    ; le 8 0                         (* sh_entsize *)
    (* .data *)
    ; le 4 datastr                   (* sh_name *)
    ; sht_PROGBITS                   (* sh_type *)
    ; le 8 (shf_ALLOC lor shf_WRITE) (* sh_flags *)
    ; le 8 0                         (* sh_addr *)
    ; le 8 dataoff                   (* sh_offset *)
    ; le 8 0                         (* sh_size *)
    ; le 4 0                         (* sh_link *)
    ; le 4 0                         (* sh_info *)
    ; le 8 1                         (* sh_addralign *)
    ; le 8 0                         (* sh_entsize *)
    (* .bss *)
    ; le 4 bssstr                    (* sh_name *)
    ; sht_NOBITS                     (* sh_type *)
    ; le 8 (shf_ALLOC lor shf_WRITE) (* sh_flags *)
    ; le 8 0                         (* sh_addr *)
    ; le 8 bssoff                    (* sh_offset *)
    ; le 8 0                         (* sh_size *)
    ; le 4 0                         (* sh_link *)
    ; le 4 0                         (* sh_info *)
    ; le 8 1                         (* sh_addralign *)
    ; le 8 0                         (* sh_entsize *)
    (* .rela *)
    ; le 4 relastr                   (* sh_name *)
    ; sht_RELA                       (* sh_type *)
    ; le 8 0                         (* sh_flags *)
    ; le 8 0                         (* sh_addr *)
    ; le 8 relaoff                   (* sh_offset *)
    ; le 8 0                         (* sh_size *)
    ; le 4 5                         (* sh_link, symtab index *)
    ; le 4 1                         (* sh_info, text section *)
    ; le 8 1                         (* sh_addralign *)
    ; le 8 0x18                      (* sh_entsize *)
    (* .symtab *)
    ; le 4 symtstr                   (* sh_name *)
    ; sht_SYMTAB                     (* sh_type *)
    ; le 8 0                         (* sh_flags *)
    ; le 8 0                         (* sh_addr *)
    ; le 8 symtoff                   (* sh_offset *)
    ; le 8 (String.length symtab)    (* sh_size *)
    ; le 4 6                         (* sh_link, strtab index *)
    ; le 4 1                         (* sh_info, first non-local symbol *)
    ; le 8 1                         (* sh_addralign *)
    ; le 8 0x18                      (* sh_entsize *)
    (* .strtab *)
    ; le 4 strtstr                   (* sh_name *)
    ; sht_STRTAB                     (* sh_type *)
    ; le 8 0                         (* sh_flags *)
    ; le 8 0                         (* sh_addr *)
    ; le 8 strtoff                   (* sh_offset *)
    ; le 8 (String.length strtab)    (* sh_size *)
    ; le 4 0                         (* sh_link *)
    ; le 4 0                         (* sh_info *)
    ; le 8 1                         (* sh_addralign *)
    ; le 8 0x18                      (* sh_entsize *)
    ] in

  List.iter (output_string oc)
    [ header
    ; sh
    ; text; String.make txtpad '\x90'
    ; symtab
    ; strtab
    ]


(*
let _ =
  let oc = open_out "test.o" in
  let text = String.concat ""
    [ "\xb8\x2a\x00\x00\x00" (* mov 42, %eax *)
    ; "\xc3"                 (* retq *)
    ] in
  barebones_elf oc "main" text
*)
