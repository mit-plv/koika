type size_t = int
type ptr_t = int

type bits_value = {
    bs_size: size_t;
    bs_bits: bool list;
  }

type typ =
  | Bits_t of size_t
  | Struct_t of struct_sig
and struct_sig =
  { struct_name: string;
    struct_fields: (string * typ) list }

let rec typ_sz = function
  | Bits_t sz -> sz
  | Struct_t sg -> struct_sz sg
and struct_sz { struct_fields; _ } =
  List.fold_left (fun acc (_, ftau) -> acc + typ_sz ftau) 0 struct_fields

type value =
  | Bits of bits_value
  | Struct of string * (value list)

let rec typ_to_string (tau: typ) =
  match tau with
  | Bits_t n -> Printf.sprintf "bits %d" n
  | Struct_t sg -> struct_sig_to_string sg
and struct_field_to_string (nm, typ) =
  Printf.sprintf "%s: %s" nm (typ_to_string typ)
and struct_sig_to_string { struct_name; struct_fields } =
  let fields = List.map struct_field_to_string struct_fields in
  Printf.sprintf "struct %s { %s }" struct_name (String.concat "; " fields)

type ('prim, 'custom) fun_id_t =
  | CustomFn of 'custom
  | PrimFn of 'prim

type ('prim, 'custom) ffi_signature = {
    ffi_name: ('prim, 'custom) fun_id_t;
    ffi_arg1type: typ;
    ffi_arg2type: typ;
    ffi_rettype: typ
  }

type reg_signature = {
    reg_name: string;
    reg_type: typ;
    reg_init_val: value;
  }

type name_t = string
type var_t = string
type port_t = int

type ('loc_t, 'content_t) locd = {
    lpos: 'loc_t;
    lcnt: 'content_t
  }

type ('f, 'reg_t, 'fn_t) action =
  | Skip
  | Fail of size_t
  | Var of var_t
  | Num of int
  | Const of bool list
  | Progn of ('f, ('f, 'reg_t, 'fn_t) action) locd list
  | Let of (('f, var_t) locd * ('f, ('f, 'reg_t, 'fn_t) action) locd) list
           * ('f, ('f, 'reg_t, 'fn_t) action) locd list
  | If of ('f, ('f, 'reg_t, 'fn_t) action) locd
          * ('f, ('f, 'reg_t, 'fn_t) action) locd
          * ('f, ('f, 'reg_t, 'fn_t) action) locd list
  | When of ('f, ('f, 'reg_t, 'fn_t) action) locd
            * ('f, ('f, 'reg_t, 'fn_t) action) locd list
  | Read of port_t
            * ('f, 'reg_t) locd
  | Write of port_t
             * ('f, 'reg_t) locd
             * ('f, ('f, 'reg_t, 'fn_t) action) locd
  | Call of ('f, 'fn_t) locd
            * ('f, ('f, 'reg_t, 'fn_t) action) locd list

type 'f scheduler =
  | Done
  | Sequence of ('f, string) locd list
  | Try of ('f, string) locd * ('f, 'f scheduler) locd * ('f, 'f scheduler) locd

type ('p, 'k) circuit = ('p, 'k) circuit' Hashcons.hash_consed
and ('p, 'k) circuit' =
  | CNot of ('p, 'k) circuit
  | CAnd of ('p, 'k) circuit * ('p, 'k) circuit
  | COr of ('p, 'k) circuit * ('p, 'k) circuit
  | CMux of size_t * ('p, 'k) circuit * ('p, 'k) circuit * ('p, 'k) circuit
  | CConst of bits_value
  | CExternal of ('p, 'k) ffi_signature * ('p, 'k) circuit * ('p, 'k) circuit
  | CReadRegister of reg_signature
  | CAnnot of size_t * string * ('p, 'k) circuit

type ('p, 'k) circuit_root = {
    root_reg: reg_signature;
    root_circuit: ('p, 'k) circuit;
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

let compute_parents (circuits: ('p, 'k) circuit list) =
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
    ekind: [`ParseError | `NameError | `TypeError];
    emsg: string }
