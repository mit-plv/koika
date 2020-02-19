(*! Utilities | Decidable equality typeclass !*)
Require Import Coq.Strings.String.
Require Import Coq.Vectors.Vector.

Class EqDec (T: Type) :=
  { eq_dec: forall t1 t2: T, { t1 = t2 } + { t1 <> t2 } }.

Definition beq_dec {A} {EQ: EqDec A} a1 a2 : bool :=
  if eq_dec a1 a2 then true else false.

Lemma beq_dec_iff {A} (EQ: EqDec A) a1 a2 :
  beq_dec a1 a2 = true <-> a1 = a2.
Proof.
  unfold beq_dec; destruct eq_dec; subst.
  - firstorder.
  - split; intro; (eauto || congruence).
Qed.

Hint Extern 1 (EqDec _) => econstructor; decide equality : typeclass_instances.
Hint Extern 1 ({ _ = _ } + { _ <> _ }) => apply eq_dec : typeclass_instances.

Instance EqDec_bool : EqDec bool := _.
Instance EqDec_ascii : EqDec Ascii.ascii := _.
Instance EqDec_string : EqDec string := _.
Instance EqDec_unit : EqDec unit := _.
Instance EqDec_nat : EqDec nat := {| eq_dec := PeanoNat.Nat.eq_dec |}.
Instance EqDec_pair A B `{EqDec A} `{EqDec B} : EqDec (A * B) := _.
Instance EqDec_option A `{EqDec A} : EqDec (option A) := _.
Instance EqDec_vector A (sz: nat) {EQ: EqDec A}: EqDec (Vector.t A sz).
Proof. econstructor; intros; eapply Vector.eq_dec; apply beq_dec_iff. Defined.
Instance EqDec_eq_true {A} (f: A -> bool) (a: A) : EqDec (f a = true).
Proof. constructor; left; apply Eqdep_dec.UIP_dec, eq_dec. Qed.

Lemma eq_rect_eqdec_irrel {A} {EQ: EqDec A} (x: A) (P: A -> Type):
  forall (px: P x) (y: A) (pr1 pr2: x = y),
    eq_rect x P px y pr1 =
    eq_rect x P px y pr2.
Proof.
  destruct pr1; cbn; intros.
  apply Eqdep_dec.eq_rect_eq_dec, eq_dec.
Qed.
