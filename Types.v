Require Export Coq.Strings.String.
Require Import Coq.Vectors.Vector.
Require Export SGA.Common SGA.Vect.

Record struct_sig' {A} :=
  { struct_name: string;
    struct_fields: list (string * A) }.
Arguments struct_sig' : clear implicits.

Inductive type : Type :=
| bits_t (sz: nat)
| struct_t (sig: struct_sig' type).

Notation struct_sig := (struct_sig' type).

Ltac simple_eq :=
  first [ left; solve[eauto] | right; inversion 1; subst; solve[congruence] ].

Instance EqDec_type : EqDec type.
Proof.
  econstructor.
  fix IHtau 1;
    destruct t1 as [ sz1 | fs1 ];
    destruct t2 as [ sz2 | fs2 ]; cbn;
      try simple_eq.
  - destruct (eq_dec sz1 sz2); subst;
      simple_eq.
  - destruct fs1 as [ nm1 f1 ];
      destruct fs2 as [ nm2 f2 ]; cbn.
    + destruct (eq_dec nm1 nm2); subst;
        try simple_eq.
      revert f1 f2;
        fix IHf 1;
        destruct f1 as [ | (n1 & tau1) f1 ], f2 as [ | (n2 & tau2) f2 ];
        try simple_eq.
      destruct (eq_dec n1 n2); subst;
        try simple_eq.
      destruct (IHtau tau1 tau2); subst;
        try simple_eq.
      destruct (IHf f1 f2) as [ Heq | Hneq ]; subst;
        try inversion Heq; try simple_eq.
Defined.

Fixpoint type_sz tau :=
  match tau with
  | bits_t sz => sz
  | struct_t fields => List.fold_right (fun '(_, tau') acc => type_sz tau' + acc) 0 fields.(struct_fields)
  end.

Coercion type_sz : type >-> nat.

Fixpoint type_denote tau : Type :=
  match tau with
  | bits_t sz => bits sz
  | struct_t fields =>
    List.fold_right (fun '(_, tau) acc => type_denote tau * acc)%type unit fields.(struct_fields)
  end.

Coercion type_denote : type >-> Sortclass.

Definition bits_of_value {tau: type} (x: type_denote tau) : bits (type_sz tau).
Proof.
  revert tau x.
  fix IHt 1; destruct tau as [sz | sig]; cbn.
  - intro x; exact x.
  - destruct sig; cbn.
    revert struct_fields0.
    fix IH 1. destruct struct_fields0 as [ | (nm & tau) struct_fields0 ]; cbn.
    + intro x; exact x.
    + intros (x & xs).
      apply Bits.app.
      apply (IHt tau x).
      apply (IH _ xs).
Defined.

Program Definition value_of_bits {tau: type} (bs: bits (type_sz tau)) : type_denote tau.
Proof.
  revert tau bs.
  fix IHt 1; destruct tau as [sz | sig]; cbn.
  - intro x; exact x.
  - destruct sig; cbn.
    revert struct_fields0.
    fix IH 1. destruct struct_fields0 as [ | (nm & tau) struct_fields0 ]; cbn.
    + intro x; exact x.
    + intros v.
      apply Bits.split in v.
      exact (IHt _ (fst v), IH _ (snd v)).
Defined.

Ltac fold_fixes :=
  repeat match goal with
         | [  |- context[?x] ] => is_fix x; set x
         end.

Definition bits_of_value_of_bits :
  forall tau (bs: bits (type_sz tau)),
    bits_of_value (value_of_bits bs) = bs.
Proof.
  fix IHt 1; destruct tau as [sz | sig]; cbn.
  - reflexivity.
  - destruct sig; cbn.
    revert struct_fields0.
    fix IH 1. destruct struct_fields0 as [ | (nm & tau) struct_fields0 ]; cbn.
    + reflexivity.
    + cbn.
      intros. rewrite IH, IHt.
      apply vect_app_split.
Qed.

Definition value_of_bits_of_value :
  forall tau (v: type_denote tau),
    (value_of_bits (bits_of_value v)) = v.
Proof.
  fix IHt 1; destruct tau as [sz | sig]; cbn.
  - reflexivity.
  - destruct sig; cbn.
    revert struct_fields0.
    fix IH 1. destruct struct_fields0 as [ | (nm & tau) struct_fields0 ]; cbn.
    + reflexivity.
    + cbn.
      intros.
      rewrite (surjective_pairing v).
      unfold Bits.split, Bits.app.
      rewrite vect_split_app.
      cbn.
      rewrite IH, IHt.
      reflexivity.
Qed.

Record ExternalSignature :=
  FunSig { arg1Type: type; arg2Type: type; retType: type }.

Notation "{{ a1 ~> a2 ~> ret }}" :=
  {| arg1Type := a1; arg2Type := a2; retType := ret |}
    (at level 200, no associativity).

Coercion ExternalSignature_denote fn :=
  fn.(arg1Type) -> fn.(arg2Type) -> fn.(retType).

Lemma ExternalSignature_injRet :
  forall (s1 s2 s1' s2': type) (retType retType': type),
    FunSig s1 s2 retType =
    FunSig s1' s2' retType' ->
    retType = retType'.
Proof. now inversion 1. Qed.

Inductive type_kind :=
  kind_bits | kind_struct (sig: struct_sig).

Inductive fn_tc_error' :=
| FnKindMismatch (expected: type_kind)
| FnUnboundField (f: string) (sig: struct_sig).

Inductive arg_id := Arg1 | Arg2.

Definition fn_tc_error : Type := arg_id * fn_tc_error'.

Definition assert_bits_t arg (tau: type) : result nat fn_tc_error :=
  match tau with
  | bits_t sz => Success sz
  | struct_t _ => Failure (arg, FnKindMismatch kind_bits)
  end.
