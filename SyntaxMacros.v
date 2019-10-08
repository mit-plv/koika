Require Import Coq.Lists.List.
Require Import SGA.Syntax SGA.TypedSyntax SGA.Primitives SGA.Interop.
Import ListNotations.

Section SyntaxMacros.
  Context {pos_t method_name_t var_t reg_t: Type}.

  Definition bits_of_ascii c : bits 8 :=
    match c with
    | Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
      Ob~b7~b6~b5~b4~b3~b2~b1~b0
    end.

  Fixpoint bits_of_bytes s : bits (String.length s * 8) :=
    match s with
    | EmptyString => Ob
    | String c s =>
      Bits.app (bits_of_bytes s) (bits_of_ascii c) (* FIXME: reversed *)
    end.

  Section ConstBits.
    Context {fn_t: Type}.
    Notation uaction := (uaction pos_t method_name_t var_t reg_t fn_t).

    Definition UConstBits {sz} (bs: bits sz) : uaction :=
      UConst (tau := bits_t sz) bs.

    Definition USkip : uaction :=
      UConstBits Ob.
  End ConstBits.

  Section Interop.
    Context {custom_fn_t: Type}.
    Notation uaction := (uaction pos_t method_name_t var_t reg_t (interop_ufn_t custom_fn_t)).

    Definition if_eq a1 a2 (tbranch fbranch: uaction) :=
      UIf (UCall (UPrimFn (UConvFn UEq)) a1 a2)
          tbranch
          fbranch.

    Fixpoint USwitch
             (var: uaction)
             (default: uaction)
             (branches: list (uaction * uaction))
      : uaction :=
      match branches with
      | nil => default
      | (val, action) :: branches =>
        if_eq var val
              action (USwitch var default branches)
      end.

    Fixpoint gen_switch {tau}
             (var: var_t)
             {nb} (branches: vect (type_denote tau * uaction) (S nb)) : uaction :=
      let '(label, branch) := vect_hd branches in
      match nb return vect _ (S nb) -> uaction with
      | 0 => fun _ => branch
      | S nb => fun branches => if_eq (UVar var) (UConst label)
                                  branch (gen_switch var (vect_tl branches))
      end branches.

    Definition UCompleteSwitch
               sz bound
               (var: var_t)
               (branches: vect uaction (S bound)) :=
      gen_switch (tau := bits_t sz) var
                 (vect_map2 (fun n a => (Bits.of_nat sz (index_to_nat n), a))
                            (all_indices (S bound)) branches).

    Definition UStructInit
               (sig: struct_sig)
               (fields: list (string * uaction)) :=
      let uinit := UPrimFn (UConvFn (UInit (struct_t sig))) in
      let usubst f := UPrimFn (UStructFn (UDo SubstField f)) in
      List.fold_left (fun acc '(f, a) => UCall (usubst f) acc a)
                     fields (UCall uinit (UConstBits Ob) (UConstBits Ob)).
  End Interop.

  Record UInternalFunction {ufn_t} :=
    { int_sig: InternalSignature method_name_t var_t;
      int_body: Syntax.uaction pos_t method_name_t var_t reg_t ufn_t }.
End SyntaxMacros.

Arguments UInternalFunction pos_t {method_name_t} var_t reg_t ufn_t : assert.
Arguments Build_UInternalFunction {pos_t method_name_t var_t reg_t ufn_t} int_sig int_body : assert.

Module Display.
  Section Display.
    Context {pos_t method_name_t reg_t: Type}.

    Context {custom_fn_t: Type}.
    Notation uaction := (uaction pos_t method_name_t string reg_t (interop_ufn_t custom_fn_t)).

    Inductive field : Type :=
    | Str (s: string)
    | Value (tau: type).

    Open Scope string_scope.

    Notation intfun := (UInternalFunction pos_t string reg_t (interop_ufn_t custom_fn_t)).

    Definition empty_printer : intfun :=
      {| int_sig := {| int_name := ""; int_args := []; int_retType := unit_t |};
         int_body := USkip |}.

    Fixpoint extend_printer f offset (printer: intfun) : intfun :=
      let display_utf8 s := UCall (UPrimFn (UDisplayFn UDisplayUtf8)) (UConstString s) (UConstBits Ob) in
      let display_value arg := UCall (UPrimFn (UDisplayFn UDisplayValue)) (UVar arg) (UConstBits Ob) in
      let '(Build_UInternalFunction int_sig int_body) := printer in
      match f with
      | Str s =>
        {| int_sig := int_sig;
           int_body := (USeq (display_utf8 s) int_body) |}
      | Value tau =>
        let arg := "arg" ++ string_of_nat offset in
        {| int_sig := {| int_name := ""; int_args := (arg, tau) :: int_sig.(int_args); int_retType := unit_t |};
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
  Context {var_t reg_t fn_t: Type}.
  Context {R: reg_t -> type}
          {Sigma: fn_t -> ExternalSignature}.

  Notation action := (action var_t R Sigma).

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
    - exact (Call fn (infix_action infix _ _ _ a1) (infix_action infix _ _ _ a2)).
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
