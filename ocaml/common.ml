type size_t = int
type ptr_t = int

module OrderedString = struct
  type t = string
  let compare = compare
end
module StringSet = Set.Make (OrderedString)
module StringMap = struct
  include Map.Make (OrderedString)
  let of_list s = of_seq (List.to_seq s)
end

type bits_value = bool array

type typ =
  | Bits_t of size_t
  | Enum_t of enum_sig
  | Struct_t of struct_sig
and struct_sig =
  { struct_name: string;
    struct_fields: (string * typ) list }
and enum_sig =
  { enum_name: string;
    enum_bitsize: int;
    enum_members: (string * bits_value) list }

let enum_find_field_opt sg v =
  match List.find_opt (fun (_nm, bs) -> bs = v) sg.enum_members with
  | Some (nm, _) -> Some nm
  | None -> None

let rec typ_sz = function
  | Bits_t sz -> sz
  | Enum_t sg -> enum_sz sg
  | Struct_t sg -> struct_sz sg
and enum_sz { enum_bitsize; _ } =
  enum_bitsize
and struct_sz { struct_fields; _ } =
  List.fold_left (fun acc (_, ftau) -> acc + typ_sz ftau) 0 struct_fields

let kind_to_str ?(pre=false) = function
  | Bits_t _ -> "bits"
  | Enum_t _ -> (if pre then "an enum" else "enum")
  | Struct_t _ -> (if pre then "a struct" else "struct")

type value =
  | Bits of bits_value
  | Enum of enum_sig * bits_value
  | Struct of struct_sig * (value list)

let typ_of_value = function
  | Bits bs -> Bits_t (Array.length bs)
  | Enum (sg, _) -> Enum_t sg
  | Struct (sg, _) -> Struct_t sg

let rec typ_to_string (tau: typ) =
  match tau with
  | Bits_t sz -> Printf.sprintf "bits %d" sz
  | Enum_t sg -> enum_sig_to_string sg
  | Struct_t sg -> struct_sig_to_string sg
and enum_sig_to_string sg =
  Printf.sprintf "enum %s" sg.enum_name
and struct_field_to_string (nm, typ) =
  Printf.sprintf "%s: %s" nm (typ_to_string typ)
and struct_sig_to_string { struct_name; struct_fields } =
  let fields = List.map struct_field_to_string struct_fields in
  Printf.sprintf "struct %s { %s }" struct_name (String.concat "; " fields)

let compare_types tau1 tau2 =
  match tau1, tau2 with
  | Bits_t sz1, Bits_t sz2 -> compare sz1 sz2
  | Bits_t _, _ -> -1
  | _, Bits_t _ -> 1
  | Enum_t sg1, Enum_t sg2 -> compare sg1.enum_name sg2.enum_name
  | Enum_t _, _ -> -1
  | _, Enum_t _ -> 1
  | Struct_t sg1, Struct_t sg2 -> compare sg1.struct_name sg2.struct_name

let sort_types types =
  List.sort compare_types types

module OrderedTypByName = struct
  type t = typ
  let compare = compare_types
end

module TypNameSet = Set.Make(OrderedTypByName)

let topo_sort_types types =
  let add (seen, ordered) = function
    | Bits_t _ -> (seen, ordered)
    | (Struct_t _ | Enum_t _) as tau -> (TypNameSet.add tau seen, tau :: ordered) in
  let rec loop ((seen, _) as acc) tau =
    if TypNameSet.mem tau seen then acc
    else let acc = match tau with
           | Struct_t sg -> List.fold_left (fun acc (_, tau) -> loop acc tau) acc sg.struct_fields
           | _ -> acc in
         add acc tau in
  List.rev (snd (List.fold_left loop (TypNameSet.empty, []) types))

let partition_types types =
  List.fold_right (fun tau (enums, structs) ->
      match tau with
      | Bits_t _ -> (enums, structs)
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
type port_t = int

type ('loc_t, 'content_t) locd = {
    lpos: 'loc_t;
    lcnt: 'content_t
  }

let locd_make lpos lcnt =
  { lpos; lcnt }

let locd_of_pair (pos, x) =
  locd_make pos x

type 'cst_t literal =
  | Var of var_t
  | Const of 'cst_t

type 'action internal_function = {
    int_name: string;
    int_argspec: (string * typ) list;
    int_rettype: typ;
    int_body: 'action
  }

type ('f, 'lit_t, 'reg_t, 'fn_t) action =
  | Error
  | Fail of typ
  (* | UVar | UConst: replaced by Lit *)
  | Assign of (('f, var_t) locd * ('f, 'lit_t, 'reg_t, 'fn_t) action_locd)
  (* | USeq: replaced by Progn *)
  (* | UBind: replaced by Let *)
  | If of ('f, 'lit_t, 'reg_t, 'fn_t) action_locd
          * ('f, 'lit_t, 'reg_t, 'fn_t) action_locd
          * ('f, 'lit_t, 'reg_t, 'fn_t) action_locd list
  | Read of port_t
            * ('f, 'reg_t) locd
  | Write of port_t
             * ('f, 'reg_t) locd
             * ('f, 'lit_t, 'reg_t, 'fn_t) action_locd
  (* | UUnop | UBinop | UExternalCall: replaced by UCall *)
  | InternalCall of
      { fn: ('f, 'lit_t, 'reg_t, 'fn_t) action_locd internal_function;
        args: ('f, 'lit_t, 'reg_t, 'fn_t) action_locd list }
  (* Sugar on Coq side *)
  | Skip
  | Progn of ('f, 'lit_t, 'reg_t, 'fn_t) action_locd list
  | StructInit of (struct_sig * (('f, string) locd * ('f, 'lit_t, 'reg_t, 'fn_t) action_locd) list)
  | Switch of { binder: var_t;
                operand: ('f, 'lit_t, 'reg_t, 'fn_t) action_locd;
                default: ('f, 'lit_t, 'reg_t, 'fn_t) action_locd;
                branches: (('f, 'lit_t, 'reg_t, 'fn_t) action_locd
                           * ('f, 'lit_t, 'reg_t, 'fn_t) action_locd) list } (* branches *)
  (* Not in Coq-side AST *)
  | Lit of 'lit_t
  | When of ('f, 'lit_t, 'reg_t, 'fn_t) action_locd
            * ('f, 'lit_t, 'reg_t, 'fn_t) action_locd list
  | Let of (('f, var_t) locd * ('f, 'lit_t, 'reg_t, 'fn_t) action_locd) list
           * ('f, 'lit_t, 'reg_t, 'fn_t) action_locd list
  | Call of { fn: ('f, 'fn_t) locd;
              args: ('f, 'lit_t, 'reg_t, 'fn_t) action_locd list }

and ('f, 'lit_t, 'reg_t, 'fn_t) action_locd =
  ('f, ('f, 'lit_t, 'reg_t, 'fn_t) action) locd

type 'f scheduler =
  | Done
  | Sequence of ('f, string) locd list
  | Try of ('f, string) locd * ('f, 'f scheduler) locd * ('f, 'f scheduler) locd

let with_output_to_file fname (f: out_channel -> unit) =
  let out = open_out fname in
  try f out; close_out_noerr out
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

let (<<) f g x = f (g x)
