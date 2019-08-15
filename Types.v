Require Export SGA.Common SGA.Vect.
Require Export Coq.Strings.String.
Require Import Coq.Vectors.Vector.

Record struct_sig' {A} :=
  { sv_len: nat;
    sv_name: string;
    sv_data: Vector.t (string * A) sv_len }.
Arguments struct_sig' : clear implicits.

Inductive type : Type :=
| bits_t (sz: nat)
| struct_t (sig: struct_sig' type).

Notation struct_sig := (struct_sig' type).

Fixpoint type_sz tau :=
  match tau with
  | bits_t sz => sz
  | struct_t fields => Vector.fold_left (fun acc '(_, tau') => acc + type_sz tau') 0 fields.(sv_data)
  end.

Coercion type_sz : type >-> nat.

Fixpoint type_denote tau : Type :=
  match tau with
  | bits_t sz => bits sz
  | struct_t fields =>
    Vector.fold_left (fun acc '(_, tau) => type_denote tau * acc)%type unit fields.(sv_data)
  end.

Coercion type_denote : type >-> Sortclass.

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

Inductive type_kind := kind_bits | kind_struct {len: nat} (sig: struct_sig).

Inductive fn_tc_error :=
| kind_mismatch (expected: type_kind)
| unbound_field (f: string) (sig: struct_sig).

Definition assert_bits_t (tau: type) : result nat fn_tc_error :=
  match tau with
  | bits_t sz => Success sz
  | struct_t _ => Failure (kind_mismatch kind_bits)
  end.
