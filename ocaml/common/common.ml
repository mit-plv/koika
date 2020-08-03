(*! Shared utilities !*)
type size_t = int
type ptr_t = int

let poly_cmp = compare

module OrderedString = struct
  type t = string
  let compare = compare
end
module StringSet = Set.Make (OrderedString)
module StringMap = struct
  include Map.Make (OrderedString)
  let of_list s = of_seq (List.to_seq s)
end

module Perf = struct
  let debug_perf = false

  let with_timer ?(verbose=false) ?(elapsed=false) label f =
    let time = Unix.gettimeofday () in
    let elapsed = elapsed || debug_perf in
    let verbose = verbose || debug_perf in
    if verbose then Printf.eprintf ">> [%s]\n%!" label;
    let result = Sys.opaque_identity (f ()) in
    if verbose && elapsed then Printf.eprintf "<< [%s] %.3fs\n%!"
                                label (Unix.gettimeofday () -. time);
    result
end

module Pos = struct
  open Printf

  type pos = { line: int; col: int }
  type range = { rbeg: pos; rend: pos }

  type t =
    | Unknown
    | StrPos of string
    | Filename of string
    | Range of string * range

  let compare p1 p2 =
    match p1, p2 with
    | Unknown, Unknown -> 0
    | Unknown, _ -> -1 | _, Unknown -> 1
    | StrPos _, StrPos _ -> 0 (* Use reporting order *)
    | StrPos _, _ -> -1 | _, StrPos _ -> 1
    | Filename f1, Filename f2 -> compare f1 f2
    | Filename _, _ -> -1 | _, Filename _ -> 1
    | Range (f1, rng1), Range (f2, rng2) ->
       match compare f1 f2 with
       | 0 -> compare rng1 rng2
       | n -> n

  let range_to_string begpos endpos =
    if begpos = endpos then sprintf "%d" begpos
    else sprintf "%d-%d" begpos endpos

  (* Emacs expects columns to start at 1 in compilation output *)
  let to_string = function
    | Unknown -> "<position unknown>"
    | StrPos s -> s
    | Filename f ->
       sprintf "%s:0:1" f
    | Range (fname, { rbeg; rend }) ->
       let line = range_to_string rbeg.line rend.line in
       let col = range_to_string (rbeg.col + 1) (rend.col + 1) in
       sprintf "%s:%s:%s" fname line col
end

type bits_value = bool array

type typ =
  | Bits_t of size_t
  | Enum_t of enum_sig
  | Struct_t of struct_sig
  | Array_t of array_sig
and struct_sig =
  { struct_name: string;
    struct_fields: (string * typ) list }
and enum_sig =
  { enum_name: string;
    enum_bitsize: int;
    enum_members: (string * bits_value) list }
and array_sig =
  { array_type: typ;
    array_len: int }

let enum_find_field_opt sg v =
  match List.find_opt (fun (_nm, bs) -> bs = v) sg.enum_members with
  | Some (nm, _) -> Some nm
  | None -> None

let rec typ_sz = function
  | Bits_t sz -> sz
  | Enum_t sg -> enum_sz sg
  | Struct_t sg -> struct_sz sg
  | Array_t sg -> array_sz sg
and enum_sz { enum_bitsize; _ } =
  enum_bitsize
and struct_sz { struct_fields; _ } =
  List.fold_left (fun acc (_, ftau) -> acc + typ_sz ftau) 0 struct_fields
and array_sz { array_type; array_len } =
  typ_sz array_type * array_len

let kind_to_str ?(pre=false) = function
  | Bits_t _ -> "bits"
  | Enum_t _ -> (if pre then "an enum" else "enum")
  | Struct_t _ -> (if pre then "a struct" else "struct")
  | Array_t _ -> (if pre then "an array" else "array")

type value =
  | Bits of bits_value
  | Enum of enum_sig * bits_value
  | Struct of struct_sig * (value list)
  | Array of array_sig * (value array)

let typ_of_value = function
  | Bits bs -> Bits_t (Array.length bs)
  | Enum (sg, _) -> Enum_t sg
  | Struct (sg, _) -> Struct_t sg
  | Array (sg, _) -> Array_t sg

let rec typ_to_string (tau: typ) =
  match tau with
  | Bits_t sz -> Printf.sprintf "bits %d" sz
  | Enum_t sg -> enum_sig_to_string sg
  | Struct_t sg -> struct_sig_to_string sg
  | Array_t sg -> array_sig_to_string sg
and enum_sig_to_string sg =
  Printf.sprintf "enum %s" sg.enum_name
and struct_sig_field_to_string (nm, typ) =
  Printf.sprintf "%s: %s" nm (typ_to_string typ)
and struct_sig_to_string { struct_name; struct_fields } =
  let fields = List.map struct_sig_field_to_string struct_fields in
  Printf.sprintf "struct %s { %s }" struct_name (String.concat "; " fields)
and array_sig_to_string { array_type; array_len } =
  Printf.sprintf "array<%s, %d>" (typ_to_string array_type) array_len
and typ_name (tau: typ) =
  match tau with
  | Enum_t sg -> sg.enum_name
  | Struct_t sg -> sg.struct_name
  | Bits_t _ | Array_t _ -> typ_to_string tau

let rec value_to_string (v: value) =
  match v with
   | Bits bs -> bits_to_string bs
   | Enum (sg, bs) -> enum_to_string sg bs
   | Struct (sg, fields) -> struct_to_string sg fields
   | Array (sg, elems) -> array_to_string sg elems
and bits_to_string bs =
  Array.map (fun b -> if b then "1" else "0") bs
  |> Array.to_list |> String.concat ""
and enum_to_string sg bs =
  Printf.sprintf "%s::%s" sg.enum_name
    (match enum_find_field_opt sg bs with
     | Some s -> s
     | None -> Printf.sprintf "{%s}" (bits_to_string bs))
and struct_field_to_string (nm, typ) v =
  assert (typ = typ_of_value v);
  Printf.sprintf "%s = %s" nm (value_to_string v)
and struct_to_string { struct_name; struct_fields } fields =
  assert (List.length struct_fields = List.length fields);
  let fields = List.map2 struct_field_to_string struct_fields fields in
  Printf.sprintf "%s { %s }" struct_name (String.concat "; " fields)
and array_elem_to_string typ v =
  assert (typ = typ_of_value v);
  value_to_string v
and array_to_string { array_type; array_len } elems =
  assert (array_len = Array.length elems);
  let elems = Array.map (array_elem_to_string array_type) elems in
  Printf.sprintf "[| %s |]" (String.concat "; " (Array.to_list elems))

let rec compare_types tau1 tau2 =
  match tau1, tau2 with
  | Bits_t sz1, Bits_t sz2 -> compare sz1 sz2
  | Bits_t _, _ -> -1
  | _, Bits_t _ -> 1
  | Enum_t sg1, Enum_t sg2 -> compare sg1.enum_name sg2.enum_name
  | Enum_t _, _ -> -1
  | _, Enum_t _ -> 1
  | Struct_t sg1, Struct_t sg2 -> compare sg1.struct_name sg2.struct_name
  | Struct_t _, _ -> -1
  | _, Struct_t _ -> 1
  | Array_t sg1, Array_t sg2 ->
     let tau12 = compare_types sg1.array_type sg2.array_type in
     if tau12 <> 0 then tau12
     else compare sg1.array_len sg2.array_len

let sort_types types =
  List.sort compare_types types

module OrderedTypByName = struct
  type t = typ
  let compare = compare_types
end

module TypNameSet = Set.Make(OrderedTypByName)

let topo_sort_types types =
  let add (seen, ordered) = function
    | Bits_t _ | Array_t _ -> (seen, ordered) (* Bits and arrays are anonymous types *)
    | (Struct_t _ | Enum_t _) as tau -> (TypNameSet.add tau seen, tau :: ordered) in
  let rec loop ((seen, _) as acc) tau =
    if TypNameSet.mem tau seen then acc
    else let acc = match tau with
           | Struct_t sg -> List.fold_left (fun acc (_, tau) -> loop acc tau) acc sg.struct_fields
           | Array_t { array_type; _ } -> loop acc array_type
           | Bits_t _ | Enum_t _ -> acc in
         (* Add tau last because we're topo-sorting *)
         add acc tau in
  List.rev (snd (List.fold_left loop (TypNameSet.empty, []) types))

let partition_types types =
  List.fold_right (fun tau (enums, structs) ->
      match tau with
      | Bits_t _ | Array_t _ -> (enums, structs)
      | Enum_t sg -> (sg :: enums, structs)
      | Struct_t sg -> (enums, sg :: structs))
    types ([], [])

type ffi_signature = {
    ffi_name: string;
    ffi_argtype: typ;
    ffi_rettype: typ
  }

type reg_signature = {
    reg_name: string;
    reg_init: value;
  }

let reg_type r =
  typ_of_value r.reg_init

type rule_name_t = string
type fn_name_t = string
type var_t = string
type port_t = P0 | P1

type ('loc_t, 'content_t) locd = {
    lpos: 'loc_t;
    lcnt: 'content_t
  }

let locd_make lpos lcnt =
  { lpos; lcnt }

let locd_of_pair (pos, x) =
  locd_make pos x

type 'action internal_function = {
    int_name: string;
    int_argspec: (string * typ) list;
    int_retSig: typ;
    int_body: 'action
  }

let with_output_to_file fname (f: out_channel -> 'a -> unit) (data: 'a) =
  let out = open_out fname in
  try f out data; close_out_noerr out
  with e -> (close_out_noerr out; raise e)

let make_gensym gensym_prefix =
  let state = Hashtbl.create 8 in
  let reset () =
    Hashtbl.clear state in
  let next prefix =
    let counter =
      match Hashtbl.find_opt state prefix with
      | None -> 0
      | Some n -> n in
    if counter = max_int then failwith "gensym";
    Hashtbl.replace state prefix (succ counter);
    Printf.sprintf "%s%s%d" gensym_prefix prefix counter in
  (next, reset)

exception CompilationError of string

let rec replace_strings haystack = function
  | [] -> haystack
  | (needle, replacement) :: repls ->
     let re = Str.regexp (Str.quote needle) in
     let haystack = Str.global_replace re replacement haystack in
     replace_strings haystack repls

let special_re =
  Str.regexp ".*[][ \t\n!\"#^$&'()*,;<=>?\\`{|}~]"

let quote_arg arg =
  if Sys.os_type = "Unix" && not (Str.string_match special_re arg 0)
  then arg else Filename.quote arg

let command ?(verbose=false) ?(elapsed=false) exe args =
  (* FIXME use Unix.open_process_args instead of Filename.quote (OCaml 4.08) *)
  let qargs = List.map quote_arg (exe :: args) in
  let cmd = String.concat " " qargs in
  Perf.with_timer ~verbose ~elapsed (Printf.sprintf "command:%s" cmd) (fun () ->
      if Sys.command cmd <> 0 then raise (CompilationError cmd))

let (<<) f g x = f (g x)
