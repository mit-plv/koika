Require Import SGA.Vect.

Inductive type :=
| bits_t (n: nat).

Coercion Nat_of_type '(bits_t n) :=
  n.

Coercion Type_of_type (tau: type) :=
  bits tau.

Record ExternalSignature :=
  FunSig { arg1Type: type;
           arg2Type: type;
           retType: type }.

Notation "{{ a1 ~> a2 ~> ret }}" :=
  {| arg1Type := bits_t a1; arg2Type := bits_t a2; retType := bits_t ret |}
    (at level 200, no associativity).

Coercion Type_of_signature fn :=
  fn.(arg1Type) -> fn.(arg2Type) -> fn.(retType).

Lemma ExternalSignature_injRet :
  forall (s1 s2 s1' s2': type) (retType retType': type),
    FunSig s1 s2 retType =
    FunSig s1' s2' retType' ->
    retType = retType'.
Proof. now inversion 1. Qed.
