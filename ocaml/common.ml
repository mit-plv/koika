type size_t = int
type ptr_t = int

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

let rec typ_sz = function
  | Bits_t sz -> sz
  | Enum_t sg -> enum_sz sg
  | Struct_t sg -> struct_sz sg
and enum_sz { enum_bitsize; _ } =
  enum_bitsize
and struct_sz { struct_fields; _ } =
  List.fold_left (fun acc (_, ftau) -> acc + typ_sz ftau) 0 struct_fields

let kind_to_str = function
  | Bits_t _ -> "bits"
  | Enum_t _ -> "enum"
  | Struct_t _ -> "struct"

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

type ('prim, 'custom) fun_id_t =
  | CustomFn of 'custom
  | PrimFn of 'prim

type 'name_t ffi_signature = {
    ffi_name: 'name_t;
    ffi_arg1type: typ;
    ffi_arg2type: typ;
    ffi_rettype: typ
  }

type reg_signature = {
    reg_name: string;
    reg_init: value;
  }

let reg_type r =
  typ_of_value r.reg_init

type name_t = string
type var_t = string
type port_t = int

type ('loc_t, 'content_t) locd = {
    lpos: 'loc_t;
    lcnt: 'content_t
  }

type ('f, 'cst_t, 'reg_t, 'fn_t) action =
  | Skip
  | Fail of size_t
  | Var of var_t
  | Num of int
  | Const of 'cst_t
  | Progn of ('f, ('f, 'cst_t, 'reg_t, 'fn_t) action) locd list
  | Let of (('f, var_t) locd * ('f, ('f, 'cst_t, 'reg_t, 'fn_t) action) locd) list
           * ('f, ('f, 'cst_t, 'reg_t, 'fn_t) action) locd list
  | If of ('f, ('f, 'cst_t, 'reg_t, 'fn_t) action) locd
          * ('f, ('f, 'cst_t, 'reg_t, 'fn_t) action) locd
          * ('f, ('f, 'cst_t, 'reg_t, 'fn_t) action) locd list
  | When of ('f, ('f, 'cst_t, 'reg_t, 'fn_t) action) locd
            * ('f, ('f, 'cst_t, 'reg_t, 'fn_t) action) locd list
  | Read of port_t
            * ('f, 'reg_t) locd
  | Write of port_t
             * ('f, 'reg_t) locd
             * ('f, ('f, 'cst_t, 'reg_t, 'fn_t) action) locd
  | Call of ('f, 'fn_t) locd
            * ('f, ('f, 'cst_t, 'reg_t, 'fn_t) action) locd list

type 'f scheduler =
  | Done
  | Sequence of ('f, string) locd list
  | Try of ('f, string) locd * ('f, 'f scheduler) locd * ('f, 'f scheduler) locd

type 'fn circuit = 'fn circuit' Hashcons.hash_consed
and 'fn circuit' =
  | CNot of 'fn circuit
  | CAnd of 'fn circuit * 'fn circuit
  | COr of 'fn circuit * 'fn circuit
  | CMux of size_t * 'fn circuit * 'fn circuit * 'fn circuit
  | CConst of bits_value
  | CExternal of 'fn ffi_signature * 'fn circuit * 'fn circuit
  | CReadRegister of reg_signature
  | CAnnot of size_t * string * 'fn circuit

type 'fn circuit_root = {
    root_reg: reg_signature;
    root_circuit: 'fn circuit;
  }

let subcircuits = function
  | CNot c -> [c]
  | CAnd (c1, c2) -> [c1; c2]
  | COr (c1, c2) -> [c1; c2]
  | CMux (_sz, s, c1, c2) -> [s; c1; c2]
  | CExternal (_fn, c1, c2) -> [c1; c2]
  | CReadRegister _r -> []
  | CAnnot (_sz, _annot, c) -> [c]
  | CConst _ -> []

let hashtbl_update tbl k v_dflt v_fn =
  Hashtbl.replace tbl k
    (v_fn (match Hashtbl.find_opt tbl k with
           | Some v -> v
           | None -> v_dflt))

let compute_parents (circuits: 'fn circuit list) =
  let tag_to_parents = Hashtbl.create 50 in
  List.iter (fun c ->
      List.iter (fun (child: _ circuit) ->
          hashtbl_update tag_to_parents child.tag []
            (fun children -> child :: children))
        (subcircuits c.Hashcons.node))
    circuits;
  tag_to_parents

let with_output_to_file fname (f: out_channel -> unit) =
  let out = open_out fname in
  try f out; close_out_noerr out
  with e -> (close_out_noerr out; raise e)

type 'f err_contents =
  { epos: 'f;
    ekind: [`ParseError | `NameError | `ResolutionError | `TypeError];
    emsg: string }
