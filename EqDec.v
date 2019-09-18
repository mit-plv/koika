Require Import Coq.Strings.String.
Require Import Coq.Vectors.Vector.

Class EqDec (T: Type) :=
  { eq_dec: forall t1 t2: T, { t1 = t2 } + { t1 <> t2 } }.

Definition EqDec_beq {A} {EQ: EqDec A} a1 a2 : bool :=
  if eq_dec a1 a2 then true else false.

Lemma EqDec_beq_iff {A} (EQ: EqDec A) a1 a2 :
  EqDec_beq a1 a2 = true <-> a1 = a2.
Proof.
  unfold EqDec_beq; destruct eq_dec; subst.
  - firstorder.
  - split; intro; (eauto || congruence).
Qed.

Hint Extern 1 (EqDec _) => econstructor; decide equality : typeclass_instances.
Hint Extern 1 ({ _ = _ } + { _ <> _ }) => apply eq_dec : typeclass_instances.

Instance EqDec_bool : EqDec bool := _.
Instance EqDec_ascii : EqDec Ascii.ascii := _.
Instance EqDec_string : EqDec string := _.
Instance EqDec_unit : EqDec unit := _.
Instance EqDec_pair A B `{EqDec A} `{EqDec B} : EqDec (A * B) := _.
Instance EqDec_option A `{EqDec A} : EqDec (option A) := _.
Instance EqDec_vector A (sz: nat) {EQ: EqDec A}: EqDec (Vector.t A sz).
Proof. econstructor; intros; eapply Vector.eq_dec; apply EqDec_beq_iff. Defined.
