(*! Generic RTL backend !*)
open Common
open Cuttlebone
open Cuttlebone.Util
open Cuttlebone.Graphs

open Printf

let debug = true
let add_debug_annotations = false
let omit_reset_line = false

type node_metadata =
  { shared: bool; circuit: circuit' }

type metadata_map = (int, node_metadata) Hashtbl.t

type expr =
  | EPtr of node
  | EName of string
  | EConst of Common.bits_value
  | EUnop of Extr.PrimTyped.fbits1 * node
  | EBinop of Extr.PrimTyped.fbits2 * node * node
  | EMux of node * node * node
  | EPure of ffi_signature * node
and node =
  { tag: int;
    size: int;
    expr: expr;
    annots: string list;
    mutable kind: node_kind }
and node_kind =
  | Unique
  | Shared
  | Printed of { name: string }

type node_map = (int, node) Hashtbl.t

let may_share = function
  | EUnop _ | EBinop _ | EMux _ -> true
  | _ -> false

let fn1_sz fn =
  let fsig = Cuttlebone.Extr.PrimSignatures.coq_Sigma1 (Bits1 fn) in
  typ_sz (Cuttlebone.Util.retSig fsig)

let fn2_sz fn =
  let fsig = Cuttlebone.Extr.PrimSignatures.coq_Sigma2 (Bits2 fn) in
  typ_sz (Cuttlebone.Util.retSig fsig)

let compute_circuit_metadata (metadata: metadata_map) (c: circuit) =
  let rec iter c =
    let open Hashcons in
    match Hashtbl.find_opt metadata c.tag with
    | Some _ ->
       Hashtbl.replace metadata c.tag { shared = true; circuit = c.node }
    | None ->
       iter' c.node;
       assert (not (Hashtbl.mem metadata c.tag)); (* No cycles *)
       Hashtbl.replace metadata c.tag { shared = false; circuit = c.node }
  and iter' (node: circuit') =
    match node with
    | CMux (_, s, c1, c2) -> iter s; iter c1; iter c2
    | CConst _ -> ()
    | CReadRegister _ -> ()
    | CUnop (_, c1) -> iter c1
    | CBinop (_, c1, c2) -> iter c1; iter c2
    | CExternal (_, c) -> iter c
    | CBundle (_, _) -> ()       (* FIXME *)
    | CBundleRef (_, _, _) -> () (* FIXME *)
    | CAnnot (_, _, c) -> iter c in
  ignore (iter c)

let node_of_circuit (metadata: metadata_map) (cache: node_map) (c: circuit) =
  let rec lift ({ tag; node = c'; _ }: circuit) =
    let open Hashcons in
    match Hashtbl.find_opt cache tag with
    | Some node -> node
    | None ->
       let size, annots, expr = lift' c' in
       let n = { tag; size; expr; annots; kind = Unique } in
       let shared = (Hashtbl.find metadata tag).shared in
       if shared && may_share expr then n.kind <- Shared;
       Hashtbl.replace cache n.tag n;
       n
  and lift' (c: circuit') =
    match c with
    | CMux (sz, s, c1, c2) -> sz, [], EMux (lift s, lift c1, lift c2)
    | CConst c -> Array.length c, [], EConst c
    | CReadRegister r -> typ_sz (reg_type r), [], EName (r.reg_name)
    | CUnop (f, c1) -> fn1_sz f, [], EUnop (f, lift c1)
    | CBinop (f, c1, c2) -> fn2_sz f, [], EBinop (f, lift c1, lift c2)
    | CExternal (f, c) -> typ_sz f.ffi_rettype, [], EPure (f, lift c)
    | CBundle (_, _) -> 0, [], EName "(FIXME bundle)"
    | CBundleRef (sz, _, _) -> sz, [], EName "(FIXME BundleRef)"
    | CAnnot (sz, annot, c) ->
       let ann = if annot = "" then [] else [annot] in
       match lift c with
       | { kind = Unique; annots; expr; _ } -> sz, ann @ annots, expr
       | n -> sz, ann, EPtr n in
  lift c

module Debug = struct
  let unop_to_str =
    let open Cuttlebone.Extr.PrimTyped in
    function
    | Not _ -> "not"
    | SExt (_, _) -> "sext"
    | ZExtL (_, _) -> "zextl"
    | ZExtR (_, _) -> "zextr"
    | Repeat (_, _) -> "repeat"
    | Slice (_, _, _) -> "slice"
    | Lowered _ -> "lowered"

  let binop_to_str =
    let open Cuttlebone.Extr.PrimTyped in
    function
    | And _ -> "and"
    | Or _ -> "or"
    | Xor _ -> "xor"
    | Lsl (_, _) -> "lsl"
    | Lsr (_, _) -> "lsr"
    | Asr (_, _) -> "asr"
    | Concat (_, _) -> "concat"
    | Sel _ -> "sel"
    | SliceSubst (_, _, _) -> "slicesubst"
    | IndexedSlice (_, _) -> "indexedslice"
    | Plus _ -> "plus"
    | Minus _ -> "minus"
    | EqBits (_, _) -> "eqbits"
    | Compare (_, _, _) -> "compare"

  let expr_to_str = function
    | EPtr n -> sprintf "EPtr %d" n.tag
    | EName n -> sprintf "EName \"%s\"" n
    | EConst cst -> sprintf "EConst %s" (string_of_bits cst)
    | EMux (s, c1, c2) -> sprintf "EMux (%d, %d, %d)" s.tag c1.tag c2.tag
    | EPure (_, c) -> sprintf "EPure (_, %d)" c.tag
    | EUnop (f, c) -> sprintf "EUnop (%s, %d)" (unop_to_str f) c.tag
    | EBinop (f, c1, c2) -> sprintf "EBinop (%s, %d, %d)" (binop_to_str f) c1.tag c2.tag

  let node_kind_to_str = function
    | Unique -> "Unique"
    | Shared -> "Shared"
    | Printed { name } -> sprintf "Printed { name = \"%s\" }" name

  let node_to_str { tag; expr; annots; kind; _ } =
    sprintf "{ tag=%d; kind=%s; expr=%s; annots=[%s] }"
      tag (node_kind_to_str kind) (expr_to_str expr) (String.concat "; " annots)

  let circuit_to_str =
    let open Cuttlebone.Graphs in
    function
    | CMux (_, s, c1, c2) -> sprintf "CMux (%d, %d, %d)" s.tag c1.tag c2.tag
    | CConst cst -> sprintf "CConst %s" (string_of_bits cst)
    | CReadRegister r -> sprintf "CReadRegister %s" r.reg_name
    | CUnop (f, c) -> sprintf "CUnop (%s, %d)" (unop_to_str f) c.tag
    | CBinop (f, c1, c2) -> sprintf "CBinop (%s, %d, %d)" (binop_to_str f) c1.tag c2.tag
    | CExternal (_, c) -> sprintf "CExternal (_, %d)" c.tag
    | CBundle (_, _) -> sprintf "CBundle"
    | CBundleRef (_, _, _) -> sprintf "CBundleRef"
    | CAnnot (_, a, c) -> sprintf "CAnnot \"%s\" %d" a c.tag

  let iter_ordered f tbl =
    List.iter (fun (k, v) -> f k v)
      (List.sort poly_cmp (List.of_seq (Hashtbl.to_seq tbl)))

  let print_node_cache cache =
    if debug then
      iter_ordered (fun tag node ->
          eprintf "%d → %s\n" tag (node_to_str node)) cache

  let print_metadata metadata =
    if debug then
      iter_ordered (fun tag { shared; circuit } ->
          eprintf "%d → { shared=%b; circuit=%s }\n"
            tag shared (circuit_to_str circuit))
        metadata

  let annotate s n =
    if add_debug_annotations then
      match n.annots with
      | [] -> s
      | ans -> sprintf "/*<%s>*/%s" (String.concat "; " ans) s
    else s
end

let compute_roots_metadata graph_roots =
  let metadata = Hashtbl.create 500 in
  List.iter (fun c -> compute_circuit_metadata metadata c.root_circuit) graph_roots;
  Debug.print_metadata metadata;
  metadata

let translate_roots metadata graph_roots =
  let cache = Hashtbl.create 500 in
  let translate_root { root_reg; root_circuit } =
    (root_reg.reg_name,
     Cuttlebone.Util.bits_of_value root_reg.reg_init,
     node_of_circuit metadata cache root_circuit) in
  let roots = List.map translate_root graph_roots in
  Debug.print_node_cache cache;
  roots

let gensym_next, gensym_reset =
  make_gensym "_"

let name_node (n: node) =
  let rec last = function
    | [] -> ""
    | [lst] -> lst
    | _ :: tl -> last tl in
  gensym_next (last n.annots)

let unlowered () =
  failwith "sext, zextl, zextr, etc. must be elaborated away by the compiler."

module type RTLBackend = sig
  val p_module : modname:string -> out_channel -> circuit_graph -> unit
end

module Verilog : RTLBackend = struct
  let p_decl out kind sz name expr =
    let range = if sz = 1 then "" else sprintf "[%d:0]" (pred sz) in
    fprintf out "\t%s%s %s = %s;\n" kind range name expr

  let precedence = function
    | EPtr _ | EName _ | EConst _ -> 0
    | EUnop (Slice _, _) | EBinop ((Sel _ | IndexedSlice _), _, _) -> -1
    | EUnop (Not _, _) -> -2
    | EBinop (Concat _, _, _) -> -3
    | EUnop (Repeat _, _) -> -4
    | EBinop ((Plus _ | Minus _), _, _) -> -5
    | EBinop ((Lsl _ | Lsr _ | Asr _), _, _) -> -6
    | EBinop (Compare (_, _, _), _, _) -> -7
    | EBinop (EqBits _, _, _) -> -8
    | EBinop (And _, _, _) -> -10 (* -9, but confusing *)
    | EBinop (Xor _, _, _) -> -10
    | EBinop (Or _, _, _) -> -10 (* -11, but confusing *)
    | EMux (_, _, _) -> -12
    | EPure (_, _) -> failwith "FIXME"
    | EBinop (SliceSubst _, _, _) -> -1 (* FIXME *)
    | EUnop ((SExt _ | ZExtL _ | ZExtR _ | Lowered _), _) -> unlowered ()

  let rec complex_op = function
    | { expr = (EPtr _ | EName _ | EConst _); _ } -> false
    | { expr = (EUnop (Slice _, _) | EBinop ((Sel _ | IndexedSlice _), _, _)); _ } -> false
    | { expr = (EUnop _ | EBinop _ | EMux _); _ } -> true
    | { expr = EPure _; _ } -> failwith "FIXME"

  let sp_cast signed p () x =
    sprintf (if signed then "$signed(%a)" else "$unsigned(%a)") p x

  let rec p_expr out (e: expr) =
    let lvl = precedence e in
    let sp_str () s = s in
    let p () n = snd (p_node out lvl n) in
    let pr () n = snd (p_node ~restricted_ctx:true out lvl n) in
    let p0 () n = snd (p_node out min_int n) in
    match e with
    | EPtr n -> lvl, p () n
    | EName name -> (lvl, name)
    | EConst cst -> (lvl, string_of_bits cst)
    | EUnop (f, c) ->
       (lvl,
        match f with
        | Not _ -> sprintf "~%a" p c
        | Repeat (_, times) -> sprintf "{%d{%a}}" times p0 c
        | Slice (_, offset, slice_sz) -> sprintf "%a[%d +: %d]" p c offset slice_sz
        | SExt _ | ZExtL _ | ZExtR _ | Lowered _ -> unlowered ())
    | EBinop (f, c1, c2) ->
       (lvl,
        match f with
        | Plus _ -> sprintf "%a + %a" p c1 p c2
        | Minus _ -> sprintf "%a - %a" p c1 p c2
        | Compare(s, CLt, _) -> sprintf "%a < %a" (sp_cast s p) c1 (sp_cast s p) c2
        | Compare(s, CGt, _) -> sprintf "%a > %a" (sp_cast s p) c1 (sp_cast s p) c2
        | Compare(s, CLe, _) -> sprintf "%a <= %a" (sp_cast s p) c1 (sp_cast s p) c2
        | Compare(s, CGe, _) -> sprintf "%a >= %a" (sp_cast s p) c1 (sp_cast s p) c2
        | Sel _ -> sprintf "%a[%a]" pr c1 p0 c2
        | IndexedSlice (_, slice_sz) -> sprintf "%a[%a +: %d]" pr c1 p0 c2 slice_sz
        | And 1 ->  sprintf "%a && %a" p c1 p c2
        | And _ ->  sprintf "%a & %a" p c1 p c2
        | Or 1 -> sprintf "%a || %a" p c1 p c2
        | Or _ -> sprintf "%a | %a" p c1 p c2
        | Xor _ -> sprintf "%a ^ %a" p c1 p c2
        | Lsl (_, _) -> sprintf "%a << %a" p c1 p c2
        | Lsr (_, _) -> sprintf "%a >> %a" p c1 p c2
        | Asr (_, _) ->
           (* Arithmetic shifts need an explicit cast:
                reg [2:0] a     =        $signed(3'b100) >>> 1;                     // 3'b110
                reg [2:0] mux_a = 1'b1 ? $signed(3'b100) >>> 1 : 3'b000;            // 3'b010
                reg [2:0] b     =        $unsigned($signed(3'b100) >>> 1);          // 3'b110
                reg [2:0] mux_b = 1'b1 ? $unsigned($signed(3'b100) >>> 1) : 3'b000; // 3'b110 *)
           sprintf "%a" (sp_cast false sp_str) (sprintf "%a >>> %a" (sp_cast true p) c1 p c2)
        | EqBits (_, true) -> sprintf "%a != %a" p c1 p c2
        | EqBits (_, false) -> sprintf "%a == %a" p c1 p c2
        | Concat (_, _) -> sprintf "{%a, %a}" p0 c1 p0 c2
        | SliceSubst _ -> unlowered ())
    | EMux (s, c1, c2) -> (lvl, sprintf "%a ? %a : %a" p s p c1 p c2)
    | EPure (f, c) -> (lvl, "FIXME: extcall")
  and p_unique_node out ctx_lvl n =
    let lvl, s = p_expr out n.expr in
    let s = Debug.annotate s n in
    if lvl <= ctx_lvl then (0, sprintf "(%s)" s) else (lvl, s)
  and p_shared_node out n =
    let name = name_node n in
    let _, s = p_unique_node out min_int n in
    p_decl out "wire" n.size name s;
    n.kind <- Printed { name };
    (0, name)
  and p_node ?(restricted_ctx=false) out ctx_lvl (n: node) =
    match n.kind with
    | Shared -> p_shared_node out n
    | Printed { name } -> (0, name)
    | Unique ->
       if restricted_ctx && complex_op n then p_shared_node out n
       else p_unique_node out ctx_lvl n

  let p_delayed out name expr =
    fprintf out "\t\t\t%s <= %s;\n" name expr

  let p_root_init out roots =
    List.iter (fun (name, init, _) -> p_delayed out name (string_of_bits init)) roots

  let p_root_net out roots =
    List.iter (fun (name, _, net) -> p_delayed out name net) roots

  let p_always_block out roots =
    fprintf out "	always @(posedge CLK) begin\n";
    if omit_reset_line then
      p_root_net out roots
    else begin
        fprintf out "		if (!RST_N) begin\n";
        p_root_init out roots;
        fprintf out "		end else begin\n";
        p_root_net out roots;
        fprintf out "		end\n";
      end;
    fprintf out "	end\n"

  let p_root_network out (name, init, node) =
    (name, init, snd (p_node out min_int node))

  let p_root_decl out (name, init, _) =
    p_decl out "reg" (Array.length init) name (string_of_bits init)

  let p_module ~modname out { graph_roots; _ } =
    let metadata = compute_roots_metadata graph_roots in
    let roots = translate_roots metadata graph_roots in
    fprintf out "// -*- mode: verilog -*-\n";
    fprintf out "module %s(input wire CLK, input wire RST_N);\n" modname;
    List.iter (p_root_decl out) roots;
    fprintf out "\n";
    let root_exprs = List.map (p_root_network out) roots in
    fprintf out "\n";
    p_always_block out root_exprs;
    fprintf out "endmodule\n"
end

let main target_dpath (modname: string) (c: circuit_graph) =
  with_output_to_file (Filename.concat target_dpath (modname ^ ".v"))
    (Verilog.p_module ~modname) c
