(*! Generic RTL backend !*)
open Common
open Cuttlebone
open Cuttlebone.Util
open Cuttlebone.Graphs

open Printf

let add_debug_annotations = false
let omit_reset_line = false

type status =
  | Unique
  | Shared of string option

(* FIXME: replace EName with EReadRegister *)

type expr =
  | EName of string
  | EConst of Common.bits_value
  | EUnop of Extr.PrimTyped.fbits1 * node
  | EBinop of Extr.PrimTyped.fbits2 * node * node
  | EMux of node * node * node
  | EPure of ffi_signature * node
  | EAnnot of string * node
and node =
  { size: int;
    expr: expr;
    mutable shared: status }

type node_map = (int, node) Hashtbl.t

let rec has_shared_annot = function
  | { expr = EAnnot _; shared = Shared _; _ } -> true
  | { expr = EAnnot (_, n); _ } -> has_shared_annot n
  | _ -> false

let may_share expr =
  let rec interesting = function
    | EUnop _ | EBinop _ | EMux _ -> true
    | EAnnot (_, n) -> interesting n.expr
    | _ -> false in
  let redundant_annot = function
    | EAnnot (_, n) -> has_shared_annot n
    | _ -> false in
  interesting expr && not (redundant_annot expr)

let fn1_sz fn =
  let fsig = Cuttlebone.Extr.PrimSignatures.coq_Sigma1 (Bits1 fn) in
  typ_sz (Cuttlebone.Util.retSig fsig)

let fn2_sz fn =
  let fsig = Cuttlebone.Extr.PrimSignatures.coq_Sigma2 (Bits2 fn) in
  typ_sz (Cuttlebone.Util.retSig fsig)

let build_verilog_expr (cache: node_map) (c: circuit) =
  let rec lift c =
    match Hashtbl.find_opt cache c.Hashcons.hkey with
    | Some node ->
       node.shared <- Shared None;
       node
    | None ->
       let size, expr = lift' c.node in
       assert (not (Hashtbl.mem cache c.hkey)); (* No cycles *)
       let node = { expr; size; shared = Unique } in
       Hashtbl.replace cache c.hkey node;
       node
  and lift' (node: circuit') =
    match node with
    | CMux (sz, s, c1, c2) -> sz, EMux (lift s, lift c1, lift c2)
    | CConst c -> Array.length c, EConst c
    | CReadRegister r -> typ_sz (reg_type r), EName (r.reg_name)
    | CUnop (f, c1) -> fn1_sz f, EUnop (f, lift c1)
    | CBinop (f, c1, c2) -> fn2_sz f, EBinop (f, lift c1, lift c2)
    | CExternal (f, c) -> typ_sz f.ffi_rettype, EPure (f, lift c)
    | CBundle (_, _) -> 0, EName "(FIXME bundle)"
    | CBundleRef (sz, _, _) -> sz, EName "(FIXME BundleRef)"
    | CAnnot (sz, annot, c) -> sz, EAnnot (annot, lift c) in
  lift c

let gensym_next, gensym_reset =
  make_gensym "_"

let hd = function
  | EName _ -> "name"
  | EConst _ -> "const"
  | EMux (_, _, _) -> "mux"
  | EPure (_, _) -> "pure"
  | EAnnot (s, _) -> sprintf "[%s]" s
  | EUnop (Not _, _) -> "not"
  | EUnop (SExt (_, _), _) -> "sext"
  | EUnop (ZExtL (_, _), _) -> "zextl"
  | EUnop (ZExtR (_, _), _) -> "zextr"
  | EUnop (Repeat (_, _), _) -> "repeat"
  | EUnop (Slice (_, _, _), _) -> "slice"
  | EUnop (Lowered _, _) -> "lowered"
  | EBinop (And _, _, _) -> "and"
  | EBinop (Or _, _, _) -> "or"
  | EBinop (Xor _, _, _) -> "xor"
  | EBinop (Lsl (_, _), _, _) -> "lsl"
  | EBinop (Lsr (_, _), _, _) -> "lsr"
  | EBinop (Asr (_, _), _, _) -> "asr"
  | EBinop (Concat (_, _), _, _) -> "concat"
  | EBinop (Sel _, _, _) -> "sel"
  | EBinop (SliceSubst (_, _, _), _, _) -> "slicesubst"
  | EBinop (IndexedSlice (_, _), _, _) -> "indexedslice"
  | EBinop (Plus _, _, _) -> "plus"
  | EBinop (Minus _, _, _) -> "minus"
  | EBinop (EqBits (_, _), _, _) -> "eqbits"
  | EBinop (Compare (_, _, _), _, _) -> "compare"

let name_expr (e: expr) =
  let rec name_expr = function
    | EAnnot (annot, c) -> annot :: name_node c
    | _ -> []
  and name_node n =
    if n.shared <> Unique then [] else name_expr n.expr in
  gensym_next (match name_expr e with [] -> "" | hd :: _ -> hd)

let p_decl out kind sz name expr =
  let range = if sz = 1 then "" else sprintf "[%d:0]" (pred sz) in
  fprintf out "\t%s%s %s = %s;\n" kind range name expr

let unlowered () =
  failwith "sext, zextl, zextr, etc. must be elaborated away by the compiler."

let precedence = function
  | EName _ | EConst _ -> 0
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
  | EAnnot _ -> -1

let rec complex_op = function
  | { shared = Shared _; _ } -> false
  | { expr = (EName _ | EConst _); _ } -> false
  | { expr = (EUnop (Slice _, _) | EBinop ((Sel _ | IndexedSlice _), _, _)); _ } -> false
  | { expr = (EUnop _ | EBinop _ | EMux _); _ } -> true
  | { expr = EPure _; _ } -> failwith "FIXME"
  | { expr = EAnnot (_, n); _ } -> complex_op n

let sp_cast signed p () x =
  sprintf (if signed then "$signed(%a)" else "$unsigned(%a)") p x

let annotate_debug s e =
  if add_debug_annotations then
    let hd = hd e in
    sprintf "/*<%s>*/%s/*</%s>*/" hd s hd
  else s

let rec p_expr' out ctx_lvl (e: expr) =
  let lvl = precedence e in
  let sp_str () s = s in
  let p () n = snd (p_node out lvl n) in
  let pr () n = snd (p_node ~restricted_ctx:true out lvl n) in
  let p0 () n = snd (p_node out min_int n) in
  match e with
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
      | SliceSubst (sz, offset, slice_sz) -> "FIXME: unlowered"
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
      | Concat (_, _) -> sprintf "{%a, %a}" p0 c1 p0 c2)
  | EMux (s, c1, c2) -> (lvl, sprintf "%a ? %a : %a" p s p c1 p c2)
  | EPure (f, c) -> (lvl, "FIXME: extcall")
  | EAnnot (_, c) -> p_node out ctx_lvl c
and p_expr out ctx_lvl e =
  let lvl, s = p_expr' out ctx_lvl e in
  let s = annotate_debug s e in
  if lvl <= ctx_lvl then (0, sprintf "(%s)" s) else (lvl, s)
and p_shared_node out n =
  let name = name_expr n.expr in
  let _, s = p_expr out min_int n.expr in
  p_decl out "wire" n.size name s;
  n.shared <- Shared (Some name);
  (0, name)
and p_node ?(restricted_ctx=false) out ctx_lvl (n: node) =
  if (n.shared = Unique && restricted_ctx && complex_op n) ||
       (n.shared = Shared None && may_share n.expr) then
     p_shared_node out n
  else match n.shared with
       | Shared (Some name) -> (0, name)
       | _ -> p_expr out ctx_lvl n.expr

let p_delayed out name expr =
  fprintf out "\t\t\t%s <= %s;\n" name expr

let sp_value v =
  string_of_bits (Cuttlebone.Util.bits_of_value v)

let p_root_init out roots =
  List.iter (fun (name, init, _) -> p_delayed out name (sp_value init)) roots

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

let p_root_network cache out (r: circuit_root) =
  (r.root_reg.reg_name,
   r.root_reg.reg_init,
   snd (p_node out min_int (Hashtbl.find cache r.root_circuit.hkey)))

let p_root_decl out { root_reg = r; _ } =
  p_decl out "reg" (typ_sz (reg_type r)) r.reg_name (sp_value r.reg_init)

let p_module modname out { graph_roots; _ } =
  let cache = Hashtbl.create 500 in
  let populate_cache c =
    ignore (build_verilog_expr cache c.root_circuit) in
  List.iter populate_cache graph_roots;
  fprintf out "// -*- mode: verilog -*-\n";
  fprintf out "module %s(input wire CLK, input wire RST_N);\n" modname;
  List.iter (p_root_decl out) graph_roots;
  fprintf out "\n";
  let root_exprs = List.map (p_root_network cache out) graph_roots in
  fprintf out "\n";
  p_always_block out root_exprs;
  fprintf out "endmodule\n"

let main target_dpath (modname: string) (c: circuit_graph) =
  with_output_to_file (Filename.concat target_dpath (modname ^ ".v"))
    (p_module modname) c
