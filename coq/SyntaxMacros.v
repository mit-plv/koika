(*! Frontend | Macros used in untyped programs !*)
Require Import Koika.Common Koika.Types Koika.Syntax Koika.TypedSyntax Koika.TypedSyntax Koika.Primitives.
Import PrimUntyped.

Section SyntaxMacros.
  Context {pos_t var_t fn_name_t reg_t ext_fn_t: Type}.

  Notation uaction := (uaction pos_t var_t fn_name_t reg_t ext_fn_t).

  Definition bits_of_ascii c : bits 8 :=
    match c with
    | Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
      Ob~b7~b6~b5~b4~b3~b2~b1~b0
    end.

  Fixpoint array_of_bytes (s: string) : vect (bits 8) (String.length s) :=
    match s with
    | EmptyString => vect_nil
    | String c s => vect_cons (bits_of_ascii c) (array_of_bytes s)
    end.

  Fixpoint uprogn (aa: list uaction) :=
    match aa with
    | [] => UConst (tau := bits_t 0) Ob
    | [a] => a
    | a :: aa => USeq a (uprogn aa)
    end.

  Definition uskip : uaction :=
    UConst (tau := bits_t 0) Ob.

  Definition uinit (tau: type) : uaction :=
    let zeroes := UConst (tau := bits_t _) (Bits.zeroes (type_sz tau)) in
    UUnop (UConv (UUnpack tau)) zeroes.

  Definition ustruct_init (sig: struct_sig) (fields: list (string * uaction)) : uaction :=
    let empty := SyntaxMacros.uinit (struct_t sig) in
    let usubst f := UBinop (UStruct2 (USubstField f)) in
    List.fold_left (fun acc '(f, a) => (usubst f) acc a) fields empty.

  Fixpoint uswitch (var: uaction) (default: uaction)
           (branches: list (uaction * uaction)) : uaction :=
    match branches with
    | nil => default
    | (label, action) :: branches =>
      UIf (UBinop (UEq false) var label) action (uswitch var default branches)
    end.

  Fixpoint uswitch_nodefault (var: uaction)
           {nb} (branches: vect (uaction * uaction) (S nb)) : uaction :=
    let '(label, action) := vect_hd branches in
    match nb return vect _ (S nb) -> uaction with
    | 0 => fun _ => action
    | S nb => fun branches =>
               UIf (UBinop (UEq false) var label) action
                   (uswitch_nodefault var (vect_tl branches))
    end branches.

  Definition gen_branches label_sz bound (branch_bodies: index bound -> uaction)
    : vect (uaction * uaction) bound :=
    let label_of_index idx := UConst (tau := bits_t _) (Bits.of_index label_sz idx) in
    vect_map (fun idx => (label_of_index idx, branch_bodies idx))
             (all_indices bound).

  Fixpoint uswitch_stateful (var: uaction)
           {nb} (branches: vect (uaction * uaction) nb) : uaction :=
    match nb return vect _ nb -> uaction with
    | 0 => fun _ => uskip
    | S nb => fun branches =>
               let '(label, action) := vect_hd branches in
               USeq (UIf (UBinop (UEq false) var label)
                         action uskip)
                    (uswitch_stateful var (vect_tl branches))
    end branches.

  Fixpoint muxtree var_logsz bit_idx (var: var_t) {sz} (bodies: bits sz -> uaction) :=
    match sz return (bits sz -> uaction) -> uaction with
    | 0 =>
      fun bodies =>
        bodies Ob
    | S n =>
      fun bodies =>
      (* FIXME add a version of sel taking a compile-time constant? *)
      let bidx := UConst (tau := bits_t var_logsz) (Bits.of_nat var_logsz bit_idx) in
      UIf (UBinop (UBits2 USel) (UVar var) bidx)
          (muxtree var_logsz (S bit_idx) var (fun bs => bodies bs~1))
          (muxtree var_logsz (S bit_idx) var (fun bs => bodies bs~0))
    end bodies.

  Definition UCompleteMuxTree sz
             (var: var_t) (branch_bodies: bits sz -> uaction) :=
    muxtree (log2 sz) 0 var branch_bodies.

  Fixpoint ortree {sz} (bodies: bits sz -> uaction) :=
    match sz return (bits sz -> uaction) -> uaction with
    | 0 =>
      fun bodies =>
        bodies Ob
    | S n =>
      fun bodies =>
      (UBinop (UBits2 UOr)
              (ortree (fun bs => bodies bs~1))
              (ortree (fun bs => bodies bs~0)))
    end bodies.

  Definition UCompleteOrTree sz nbits
             (var: var_t) (branch_bodies: bits sz -> uaction) :=
    ortree
      (fun bs => UIf (UBinop (UEq false) (UConst (tau := bits_t sz) bs) (UVar var))
                  (branch_bodies bs)
                  (UConst (tau := bits_t nbits) Bits.zero)).

  Inductive switch_style :=
  | TreeSwitch
  | OrTreeSwitch (nbits: nat)
  | NestedSwitch
  | SequentialSwitchTt
  | SequentialSwitch (tau: type) (output_var: var_t).

  Definition UCompleteSwitch (style: switch_style) sz
             (var: var_t) (branch_bodies: index (pow2 sz) -> uaction) :=
    let branches bodies :=
        gen_branches sz (pow2 sz) bodies in
    match style with
    | TreeSwitch =>
      UCompleteMuxTree sz var (fun bs => branch_bodies (Bits.to_index_safe bs))
    | OrTreeSwitch nbits =>
      UCompleteOrTree sz nbits var (fun bs => branch_bodies (Bits.to_index_safe bs))
    | NestedSwitch =>
      uswitch_nodefault (UVar var) (branches branch_bodies)
    | SequentialSwitchTt =>
      uswitch_stateful (UVar var) (branches branch_bodies)
    | SequentialSwitch output_type output_var =>
      let branch_bodies idx := UAssign output_var (branch_bodies idx) in
      UBind output_var
            (uinit output_type)
            (USeq (uswitch_stateful (UVar var) (branches branch_bodies))
                  (UVar output_var))
    end.
End SyntaxMacros.

Module Display.
  Section Display.
    Notation var_t := string (only parsing).
    Notation fn_name_t := string (only parsing).
    Context {pos_t reg_t ext_fn_t: Type}.

    Notation uaction := (uaction pos_t var_t fn_name_t reg_t ext_fn_t).

    Inductive field : Type :=
    | Str (s: string)
    | Value (tau: type).

    Notation intfun := (InternalFunction var_t fn_name_t uaction).

    Definition empty_printer : InternalFunction var_t fn_name_t uaction :=
      {| int_name := "print";
         int_argspec := [];
         int_retSig := unit_t;
         int_body := USugar USkip |}.

    Definition display_utf8 s : uaction :=
      UUnop (UDisplay (UDisplayUtf8)) (USugar (UConstString s)).

    Definition nl_printer : InternalFunction var_t fn_name_t uaction :=
      {| int_name := "print_nl";
         int_argspec := [];
         int_retSig := unit_t;
         int_body := display_utf8 "\n" |}.

    Definition extend_printer f (offset: nat) (printer: intfun) : intfun :=
      let opts :=
          {| display_newline := false; display_strings := false; display_style := dFull |} in
      let display_value arg :=
          UUnop (UDisplay (UDisplayValue opts)) (UVar arg) in
      let '(Build_InternalFunction int_name int_argspec int_retSig int_body) :=
          printer in
      match f with
      | Str s =>
        {| int_name := int_name;
           int_argspec := int_argspec;
           int_retSig := int_retSig;
           int_body := (USeq (display_utf8 s) int_body) |}
      | Value tau =>
        let arg := String.append "arg" (show offset) in
        {| int_name := int_name;
           int_argspec := (arg, tau) :: int_argspec;
           int_retSig := unit_t;
           int_body := (USeq (display_value arg) int_body) |}
      end.

    Fixpoint make_printer (offset: nat) (fstring: list field) : intfun :=
      match fstring with
      | [] => empty_printer
      | f :: fstring => extend_printer f offset (make_printer (S offset) fstring)
      end.

    Definition Printer (fstring: list field) :=
      make_printer 0 fstring.

    Example example :=
      Eval compute in Printer [Str "x: "; Value (bits_t 16); Str "y: "; Value (bits_t 32)].
  End Display.
End Display.

Require Import Koika.LoweredSyntax.

Section LoweredSyntaxMacros.
  Context {pos_t var_t fn_name_t reg_t ext_fn_t: Type}.
  Context {CR: reg_t -> nat}
          {CSigma: ext_fn_t -> CExternalSignature}.

  Notation action := (action pos_t var_t CR CSigma).

  Fixpoint infix_action (infix: lsig) {sig sig': lsig} {tau} (a: action (sig ++ sig') tau)
    : action (sig ++ infix ++ sig') tau.
  Proof.
    remember (sig ++ sig'); destruct a; subst.
    - exact (Fail sz).
    - exact (Var k (minfix infix m)).
    - exact (Const cst).
    - exact (Assign k (minfix infix m) (infix_action infix _ _ _ a)).
    - exact (Seq (infix_action infix _ _ _ a1) (infix_action infix _ _ _ a2)).
    - exact (Bind k (infix_action infix _ _ _ a1) (infix_action infix (_ :: sig) sig' _ a2)).
    - exact (If (infix_action infix _ _ _ a1) (infix_action infix _ _ _ a2) (infix_action infix _ _ _ a3)).
    - exact (Read port idx).
    - exact (Write port idx (infix_action infix _ _ _ a)).
    - exact (Unop fn (infix_action infix _ _ _ a)).
    - exact (Binop fn (infix_action infix _ _ _ a1) (infix_action infix _ _ _ a2)).
    - exact (ExternalCall fn (infix_action infix _ _ _ a)).
    - exact (infix_action infix _ _ _ a).
  Defined.

  Definition prefix_action (prefix: lsig) {sig: lsig} {sz} (a: action sig sz)
    : action (prefix ++ sig) sz :=
    infix_action prefix (sig := []) a.

  Definition suffix_action (suffix: lsig) {sig: lsig} {sz} (a: action sig sz)
    : action (sig ++ suffix) sz.
  Proof. rewrite <- (capp_nil_r suffix); apply infix_action; rewrite (capp_nil_r sig); exact a. Defined.

  Definition lsig_of_tsig (sig: tsig var_t) : lsig :=
    List.map (fun k_tau => type_sz (snd k_tau)) sig.

  Fixpoint InternalCall'
           {sz: nat}
           {sig: lsig}
           {fn_sig: lsig}
           (args: context (fun sz => var_t * action sig sz)%type fn_sig)
           (fn_body: action (fn_sig ++ sig) sz)
    : action sig sz :=
    match args in context _ fn_sig
          return action (fn_sig ++ sig) sz ->
                 action sig sz with
    | CtxEmpty =>
      fun fn_body => fn_body
    | CtxCons sz (k, v) tl =>
      fun fn_body =>
        let fn_body := Bind k (prefix_action _ v) fn_body in
        InternalCall' tl fn_body
    end fn_body.

  Definition InternalCall
             {sz: nat}
             {sig: lsig}
             {fn_sig: lsig}
             (args: context (fun sz => var_t * action sig sz)%type fn_sig)
             (fn_body: action fn_sig sz)
    : action sig sz :=
    InternalCall' args (suffix_action sig fn_body).
End LoweredSyntaxMacros.
