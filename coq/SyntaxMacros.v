(*! Frontend | Macros used in untyped programs !*)
Require Import Koika.Common Koika.Syntax Koika.TypedSyntax Koika.Primitives.
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

  Fixpoint uswitch (var: uaction) (default: uaction)
           (branches: list (uaction * uaction)) : uaction :=
    match branches with
    | nil => default
    | (label, action) :: branches =>
      UIf (UBinop UEq var label) action (uswitch var default branches)
    end.

  Fixpoint uswitch_nodefault (var: uaction)
           {nb} (branches: vect (uaction * uaction) (S nb)) : uaction :=
    let '(label, action) := vect_hd branches in
    match nb return vect _ (S nb) -> uaction with
    | 0 => fun _ => action
    | S nb => fun branches =>
               UIf (UBinop UEq var label) action
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
               USeq (UIf (UBinop UEq var label)
                         action uskip)
                    (uswitch_stateful var (vect_tl branches))
    end branches.

  Fixpoint utree var_logsz bit_idx (var: var_t) {sz} (bodies: bits sz -> uaction) :=
    match sz return (bits sz -> uaction) -> uaction with
    | 0 =>
      fun bodies =>
        bodies Ob
    | S n =>
      fun bodies =>
      (* FIXME add a version of sel taking a compile-time constant? *)
      let bidx := UConst (tau := bits_t var_logsz) (Bits.of_nat var_logsz bit_idx) in
      UIf (UBinop (UBits2 USel) (UVar var) bidx)
          (utree var_logsz (S bit_idx) var (fun bs => bodies bs~1))
          (utree var_logsz (S bit_idx) var (fun bs => bodies bs~0))
    end bodies.

  Definition UCompleteTree sz
             (var: var_t) (branch_bodies: bits sz -> uaction) :=
    utree (log2 sz) 0 var branch_bodies.

  Inductive switch_style :=
  | TreeSwitch
  | NestedSwitch
  | SequentialSwitchTt
  | SequentialSwitch (tau: type) (output_var: var_t).

  Definition UCompleteSwitch (style: switch_style) sz
             (var: var_t) (branch_bodies: index (pow2 sz) -> uaction) :=
    let branches bodies :=
        gen_branches sz (pow2 sz) bodies in
    match style with
    | TreeSwitch =>
      UCompleteTree sz var (fun bs => branch_bodies (Bits.to_index_safe bs))
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

    Notation intfun := (InternalFunction fn_name_t var_t uaction).

    Definition empty_printer : InternalFunction fn_name_t var_t uaction :=
      {| int_name := "";
         int_argspec := [];
         int_retType := unit_t;
         int_body := USugar USkip |}.

    Definition display_utf8 s : uaction :=
      UUnop (UDisplay (UDisplayUtf8)) (USugar (UConstString s)).

    Definition nl_printer : InternalFunction fn_name_t var_t uaction :=
      {| int_name := "";
         int_argspec := [];
         int_retType := unit_t;
         int_body := display_utf8 "\n" |}.

    Fixpoint extend_printer f (offset: nat) (printer: intfun) : intfun :=
      let opts :=
          {| display_newline := false; display_strings := false; display_style := dFull |} in
      let display_value arg :=
          UUnop (UDisplay (UDisplayValue opts)) (UVar arg) in
      let '(Build_InternalFunction int_name int_argspec int_retType int_body) :=
          printer in
      match f with
      | Str s =>
        {| int_name := int_name;
           int_argspec := int_argspec;
           int_retType := int_retType;
           int_body := (USeq (display_utf8 s) int_body) |}
      | Value tau =>
        let arg := String.append "arg" (show offset) in
        {| int_name := int_name;
           int_argspec := (arg, tau) :: int_argspec;
           int_retType := unit_t;
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

Section TypedSyntaxMacros.
  Context {pos_t var_t reg_t ext_fn_t: Type}.
  Context {R: reg_t -> type}
          {Sigma: ext_fn_t -> ExternalSignature}.

  Notation action := (action pos_t var_t R Sigma).

  Fixpoint mshift {K} (prefix: list K) {sig: list K} {k} (m: member k sig)
    : member k (prefix ++ sig) :=
    match prefix return member k sig -> member k (prefix ++ sig) with
    | [] => fun m => m
    | k' :: prefix => fun m => MemberTl k k' (prefix ++ sig) (mshift prefix m)
    end m.

  Fixpoint mshift' {K} (infix: list K) {sig sig': list K} {k} (m: member k (sig ++ sig'))
    : member k (sig ++ infix ++ sig').
  Proof.
    destruct sig as [ | k' sig].
    - exact (mshift infix m).
    - destruct (mdestruct m) as [(-> & Heq) | (m' & Heq)]; cbn in *.
      + exact (MemberHd k' (sig ++ infix ++ sig')).
      + exact (MemberTl k k' (sig ++ infix ++ sig') (mshift' _ infix sig sig' k m')).
  Defined.

  Fixpoint infix_action (infix: tsig var_t) {sig sig': tsig var_t} {tau} (a: action (sig ++ sig') tau)
    : action (sig ++ infix ++ sig') tau.
  Proof.
    remember (sig ++ sig'); destruct a; subst.
    - exact (Fail tau).
    - exact (Var (mshift' infix m)).
    - exact (Const cst).
    - exact (Assign (mshift' infix m) (infix_action infix _ _ _ a)).
    - exact (Seq (infix_action infix _ _ _ a1) (infix_action infix _ _ _ a2)).
    - exact (Bind var (infix_action infix _ _ _ a1) (infix_action infix (_ :: sig) sig' _ a2)).
    - exact (If (infix_action infix _ _ _ a1) (infix_action infix _ _ _ a2) (infix_action infix _ _ _ a3)).
    - exact (Read port idx).
    - exact (Write port idx (infix_action infix _ _ _ a)).
    - exact (Unop fn (infix_action infix _ _ _ a)).
    - exact (Binop fn (infix_action infix _ _ _ a1) (infix_action infix _ _ _ a2)).
    - exact (ExternalCall fn (infix_action infix _ _ _ a)).
    - exact (infix_action infix _ _ _ a).
  Defined.

  Definition prefix_action (prefix: tsig var_t) {sig: tsig var_t} {tau} (a: action sig tau)
    : action (prefix ++ sig) tau :=
    infix_action prefix (sig := []) a.

  Fixpoint suffix_action_eqn {A} (l: list A) {struct l}:
    l ++ [] = l.
  Proof. destruct l; cbn; [ | f_equal ]; eauto. Defined.

  Definition suffix_action (suffix: tsig var_t) {sig: tsig var_t} {tau} (a: action sig tau)
    : action (sig ++ suffix) tau.
  Proof. rewrite <- (suffix_action_eqn suffix); apply infix_action; rewrite (suffix_action_eqn sig); exact a. Defined.

  Fixpoint InternalCall'
           {tau: type}
           (sig: tsig var_t)
           (fn_sig: tsig var_t)
           (fn_body: action (fn_sig ++ sig) tau)
           (args: context (fun '(_, tau) => action sig tau) fn_sig)
    : action sig tau :=
    match fn_sig return action (fn_sig ++ sig) tau ->
                        context (fun '(_, tau) => action sig tau) fn_sig ->
                        action sig tau with
    | [] =>
      fun fn_body _ =>
        fn_body
    | (k, tau) :: fn_sig =>
      fun fn_body args =>
        InternalCall' sig fn_sig
                      (Bind k (prefix_action fn_sig (chd args)) fn_body)
                      (ctl args)
    end fn_body args.

  Fixpoint InternalCall
             {tau: type}
             (sig: tsig var_t)
             (fn_sig: tsig var_t)
             (fn_body: action fn_sig tau)
             (args: context (fun '(_, tau) => action sig tau) fn_sig)
    : action sig tau :=
    InternalCall' sig fn_sig (suffix_action sig fn_body) args.
End TypedSyntaxMacros.
