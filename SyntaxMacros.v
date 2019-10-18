Require Import Coq.Lists.List.
Require Import SGA.Syntax SGA.TypedSyntax SGA.Primitives SGA.Interop.
Import ListNotations.

Import PrimUntyped.

Section SyntaxMacros.
  Context {pos_t var_t fn_name_t reg_t ext_fn_t: Type}.

  Notation uaction := (uaction pos_t var_t fn_name_t reg_t ext_fn_t).

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

  Fixpoint gen_switch {tau}
           (var: var_t)
           {nb} (branches: vect (type_denote tau * uaction) (S nb)) : uaction :=
    let '(label, branch) := vect_hd branches in
    match nb return vect _ (S nb) -> uaction with
    | 0 => fun _ => branch
    | S nb => fun branches =>
      UIf (UBinop UEq (UVar var) (UConst label))
          branch (gen_switch var (vect_tl branches))
    end branches.

  Definition UCompleteSwitch
             sz bound
             (var: var_t)
             (branches: vect uaction (S bound)) :=
    gen_switch (tau := bits_t sz) var
               (vect_map2 (fun n a => (Bits.of_nat sz (index_to_nat n), a))
                          (all_indices (S bound)) branches).
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

    Open Scope string_scope.

    Notation intfun := (InternalFunction fn_name_t var_t uaction).

    Definition empty_printer : InternalFunction fn_name_t var_t uaction :=
      {| int_name := "";
         int_argspec := [];
         int_retType := unit_t;
         int_body := USugar USkip |}.

    Fixpoint extend_printer f offset (printer: intfun) : intfun :=
      let display_utf8 s := UUnop (UDisplay UDisplayUtf8) (UConstString s) in
      let display_value arg := UUnop (UDisplay UDisplayValue) (UVar arg) in
      let '(Build_InternalFunction int_name int_argspec int_retType int_body) := printer in
      match f with
      | Str s =>
        {| int_name := int_name;
           int_argspec := int_argspec;
           int_retType := int_retType;
           int_body := (USeq (display_utf8 s) int_body) |}
      | Value tau =>
        let arg := "arg" ++ string_of_nat offset in
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
    - exact (Unop fn (infix_action infix _ _ _ a)).
    - exact (Binop fn (infix_action infix _ _ _ a1) (infix_action infix _ _ _ a2)).
    - exact (ExternalCall fn (infix_action infix _ _ _ a)).
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
