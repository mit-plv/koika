(*! Frontend | Desugaring of untyped actions !*)
Require Import Koika.Common Koika.Environments Koika.Syntax Koika.TypedSyntax Koika.ErrorReporting Koika.SyntaxMacros.

Section Desugaring.
  (* The desugaring phase can produce larger terms than its inputs, and so
     cannot be intermingled with the typechecking phase without angering
     Coq's termination checker. *)

  Context {pos_t var_t fn_name_t reg_t ext_fn_t: Type}.

  Notation usugar := (usugar pos_t var_t fn_name_t).
  Notation uaction := (uaction pos_t var_t fn_name_t).

  Import PrimUntyped.

  Fixpoint desugar_action' {reg_t' ext_fn_t'} (pos: pos_t)
           (fR: reg_t' -> reg_t) (fSigma: ext_fn_t' -> ext_fn_t)
           (a: uaction reg_t' ext_fn_t') {struct a}
    : uaction reg_t ext_fn_t :=
    let d a := desugar_action' pos fR fSigma a in
    match a with
    | UError err => UError err
    | UFail tau => UFail tau
    | UVar var => UVar var
    | UConst cst => UConst cst
    | UAssign v ex => UAssign v (d ex)
    | USeq a1 a2 => USeq (d a1) (d a2)
    | UBind v ex body => UBind v (d ex) (d body)
    | UIf cond tbranch fbranch => UIf (d cond) (d tbranch) (d fbranch)
    | URead port idx => URead port (fR idx)
    | UWrite port idx value => UWrite port (fR idx) (d value)
    | UUnop fn arg => UUnop fn (d arg)
    | UBinop fn arg1 arg2 => UBinop fn (d arg1) (d arg2)
    | UExternalCall fn arg => UExternalCall (fSigma fn) (d arg)
    | UInternalCall fn args =>
      UInternalCall (map_intf_body d fn) (List.map d args)
    | UAPos p e => UAPos p (d e)
    | USugar s => desugar pos fR fSigma s
    end
  with desugar {reg_t' ext_fn_t'}
               (pos: pos_t)
               (fR: reg_t' -> reg_t) (fSigma: ext_fn_t' -> ext_fn_t)
               (s: usugar reg_t' ext_fn_t')
       : uaction reg_t ext_fn_t :=
         let d a := desugar_action' pos fR fSigma a in
         match s with
         | UErrorInAst =>
           UError {| emsg := ExplicitErrorInAst; epos := pos; esource := ErrSrc s |}
         | USkip =>
           SyntaxMacros.uskip
         | UConstBits bs =>
           UConst (tau := bits_t _) bs
         | UConstString s =>
           UConst (tau := array_t {| array_type := bits_t 8 |}) (array_of_bytes s)
         | UConstEnum sig name =>
           match vect_index name sig.(enum_members) with
           | Some idx => UConst (tau := enum_t sig) (vect_nth sig.(enum_bitpatterns) idx)
           | None => UError {| epos := pos; emsg := UnboundEnumMember name sig;
                              esource := ErrSrc s |}
           end
         | UProgn aa =>
           SyntaxMacros.uprogn (List.map d aa)
         | ULet bindings body =>
           List.fold_right (fun '(var, a) acc => UBind var (d a) acc) (d body) bindings
         | UWhen cond body =>
           UIf (d cond) (d body) (UFail (bits_t 0)) (* FIXME infer the type of the second branch? *)
         | UStructInit sig fields =>
           let fields := List.map (fun '(f, a) => (f, d a)) fields in
           SyntaxMacros.ustruct_init sig fields
         | UArrayInit tau elements =>
           let sig := {| array_type := tau; array_len := List.length elements |} in
           let usubst pos := UBinop (UArray2 (USubstElement pos)) in
           let empty := SyntaxMacros.uinit (array_t sig) in
           snd (List.fold_left (fun '(pos, acc) a => (S pos, (usubst pos) acc (d a))) elements (0, empty))
         | USwitch var default branches =>
           let branches := List.map (fun '(cond, body) => (d cond, d body)) branches in
           SyntaxMacros.uswitch (d var) (d default) branches
         | UCallModule fR' fSigma' fn args =>
           let df body := desugar_action' pos (fun r => fR (fR' r)) (fun fn => fSigma (fSigma' fn)) body in
           UInternalCall (map_intf_body df fn) (List.map d args)
         end.

  Definition desugar_action (pos: pos_t) (a: uaction reg_t ext_fn_t)
    : uaction reg_t ext_fn_t :=
    desugar_action' pos (fun r => r) (fun fn => fn) a.
End Desugaring.
