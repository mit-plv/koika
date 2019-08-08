type size_t = int
type ptr_t = int

type bits_const = {
    bs_size: size_t;
    bs_bits: bool list;
  }

type 'prim fun_id_t =
  | CustomFn of string
  | PrimFn of 'prim

type 'prim ffi_signature = {
    ffi_name: 'prim fun_id_t;
    ffi_arg1size: size_t;
    ffi_arg2size: size_t;
    ffi_retsize: size_t
  }

type reg_signature = {
    reg_name: string;
    reg_size: size_t;
    reg_init_val: bits_const;
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
  | Fail
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

type 'p circuit = 'p circuit' Hashcons.hash_consed
and 'p circuit' =
  | CNot of 'p circuit
  | CAnd of 'p circuit * 'p circuit
  | COr of 'p circuit * 'p circuit
  | CMux of size_t * 'p circuit * 'p circuit * 'p circuit
  | CConst of bits_const
  | CExternal of 'p ffi_signature * 'p circuit * 'p circuit
  | CReadRegister of reg_signature
  | CAnnot of size_t * string * 'p circuit

type 'p circuit_root = {
    root_reg: reg_signature;
    root_circuit: 'p circuit;
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

let compute_parents (circuits: 'p circuit list) =
  let tag_to_parents = Hashtbl.create 50 in
  List.iter (fun c ->
      List.iter (fun (child: _ circuit) ->
          hashtbl_update tag_to_parents child.tag []
            (fun children -> child :: children))
        (subcircuits c.Hashcons.node))
    circuits;
  tag_to_parents

type 'f err_contents =
  { epos: 'f;
    ekind: [`ParseError | `NameError | `TypeError];
    emsg: string }
