Require Export Coq.Strings.String.
Require Export SGA.Common SGA.Vect SGA.IndexUtils.
Require Import Coq.Lists.List.
Import ListNotations.

(** * Definitions **)

Record struct_sig' {A} :=
  { struct_name: string;
    struct_fields: list (string * A) }.
Arguments struct_sig' : clear implicits.

Record enum_sig :=
  { enum_name: string;
    enum_size: nat;
    enum_bitsize: nat;
    enum_members: vect string enum_size;
    enum_bitpatterns: vect (bits enum_bitsize) enum_size }.

Inductive type : Type :=
| bits_t (sz: nat)
| enum_t (sig: enum_sig)
| struct_t (sig: struct_sig' type).

Notation unit_t := (bits_t 0).
Notation struct_sig := (struct_sig' type).

Inductive type_kind :=
| kind_bits
| kind_enum (sig: option enum_sig)
| kind_struct (sig: option struct_sig).

Definition kind_of_type (tau: type) :=
  match tau with
  | bits_t sz => kind_bits
  | enum_t sig => kind_enum (Some sig)
  | struct_t sig => kind_struct (Some sig)
  end.

Definition struct_fields_sz' (type_sz: type -> nat) (fields: list (string * type)) :=
  list_sum (List.map (fun nm_tau => type_sz (snd nm_tau)) fields).

Fixpoint type_sz tau :=
  match tau with
  | bits_t sz => sz
  | enum_t sig => sig.(enum_bitsize)
  | struct_t sig => struct_fields_sz' type_sz sig.(struct_fields)
  end.

Notation struct_fields_sz := (struct_fields_sz' type_sz).

Definition struct_index (sig: struct_sig) :=
  Vect.index (List.length sig.(struct_fields)).

Definition struct_sz sig :=
  type_sz (struct_t sig).

Definition field_type (sig: struct_sig) idx :=
  snd (List_nth sig.(struct_fields) idx).

Definition field_sz (sig: struct_sig) idx :=
  type_sz (field_type sig idx).

Definition field_offset_left (sig: struct_sig) (idx: struct_index sig) :=
  let prev_fields := List.firstn (index_to_nat idx) sig.(struct_fields) in
  struct_fields_sz prev_fields.

Definition field_offset_right (sig: struct_sig) (idx: struct_index sig) :=
  let next_fields := List.skipn (S (index_to_nat idx)) sig.(struct_fields) in
  struct_fields_sz next_fields.

Notation struct_bits_t sig :=
  (bits_t (struct_sz sig)).

Notation field_bits_t sig idx :=
  (bits_t (field_sz sig idx)).

Inductive Port :=
  P0 | P1.

(** * Denotations *)

Definition struct_denote' (type_denote: type -> Type) (fields: list (string * type)) :=
  List.fold_right (fun '(_, tau) acc => type_denote tau * acc)%type unit fields.

Fixpoint type_denote tau : Type :=
  match tau with
  | bits_t sz => bits sz
  | enum_t sig => bits sig.(enum_bitsize)
  | struct_t sig => struct_denote' type_denote sig.(struct_fields)
  end.

Notation struct_denote := (struct_denote' type_denote).

(** * Bit representations **)

Fixpoint bits_of_value {tau: type} (x: type_denote tau) {struct tau} : bits (type_sz tau) :=
  let bits_of_struct_value :=
      (fix bits_of_struct_value
           {fields}
           (x: struct_denote fields)
       : bits (struct_fields_sz fields) :=
         match fields return struct_denote fields -> bits (struct_fields_sz fields) with
         | [] => fun _ => vect_nil
         | (nm, tau) :: fields => fun '(x, xs) => Bits.app (bits_of_value x) (bits_of_struct_value xs)
         end x) in
  match tau return type_denote tau -> bits (type_sz tau) with
  | bits_t sz => fun bs => bs
  | enum_t sig => fun bs => bs
  | struct_t sig => fun str => bits_of_struct_value str
  end x.

Fixpoint value_of_bits {tau: type} (bs: bits (type_sz tau)) {struct tau}: type_denote tau :=
  let value_of_struct_bits :=
      (fix value_of_struct_bits
           {fields: list (string * type)}
           (bs: bits (struct_fields_sz fields))
       : struct_denote fields :=
         match fields return bits (struct_fields_sz fields) -> struct_denote fields with
         | [] => fun bs => tt
         | (nm, tau) :: fields =>
           fun bs =>
             let splt := Bits.split bs in
             let hd := value_of_bits (snd splt) in
             let tl := value_of_struct_bits (fst splt) in
             (hd, tl)
         end bs) in
  match tau return bits (type_sz tau) -> type_denote tau with
  | bits_t sz => fun bs => bs
  | enum_t sig => fun bs => bs
  | struct_t sig => fun bs => value_of_struct_bits bs
  end bs.

Definition bits_of_value_of_bits :
  forall tau (bs: bits (type_sz tau)),
    bits_of_value (value_of_bits bs) = bs.
Proof.
  fix IHtau 1; destruct tau as [sz | sig | sig]; cbn.
  - reflexivity.
  - reflexivity.
  - destruct sig; cbn.
    revert struct_fields0.
    fix IHfields 1. destruct struct_fields0 as [ | (nm & tau) struct_fields0 ]; cbn.
    + destruct bs; reflexivity.
    + intros; rewrite IHtau, IHfields; apply vect_app_split.
Qed.

Definition value_of_bits_of_value :
  forall tau (v: type_denote tau),
    (value_of_bits (bits_of_value v)) = v.
Proof.
  fix IHt 1; destruct tau as [sz | sig | sig]; cbn.
  - reflexivity.
  - reflexivity.
  - destruct sig; cbn.
    revert struct_fields0.
    fix IH 1. destruct struct_fields0 as [ | (nm & tau) struct_fields0 ]; cbn.
    + destruct v; reflexivity.
    + cbn.
      intros.
      rewrite (surjective_pairing v).
      unfold Bits.split, Bits.app.
      rewrite vect_split_app.
      cbn.
      rewrite IH, IHt.
      reflexivity.
Qed.

Lemma bits_of_value_inj :
  forall {tau: type} (x y: type_denote tau),
    bits_of_value x = bits_of_value y ->
    x = y.
Proof.
  intros * H%(f_equal value_of_bits);
    rewrite !value_of_bits_of_value in H;
    auto.
Qed.

Lemma value_of_bits_inj :
  forall {tau: type} (bs0 bs1: bits (type_sz tau)),
    value_of_bits bs0 = value_of_bits bs1 ->
    bs0 = bs1.
Proof.
  intros * H%(f_equal bits_of_value);
    rewrite !bits_of_value_of_bits in H;
    auto.
Qed.

(** * Coercions **)

Coercion type_sz : type >-> nat.
Coercion type_denote : type >-> Sortclass.

(** * Anonymous function signatures **)

(* Example ufn := {{{ "A" | "x" :: unit_t ~> bits_t 5 | tt }}}. *)

Record CSig {n: nat} := { argSizes : vect nat n; retSize : nat }.
Arguments CSig : clear implicits.

Fixpoint CSig_denote' {n} (args: vect nat n) (ret: nat) :=
  match n return vect nat n -> Type with
  | 0 => fun _ => bits ret
  | S n => fun arg => bits (vect_hd arg) -> CSig_denote' (vect_tl arg) ret
  end args.

Definition CSig_denote {n} (sg: CSig n) :=
  CSig_denote' sg.(argSizes) sg.(retSize).

Coercion CSig_denote: CSig >-> Sortclass.

Notation arg1Size fsig := (vect_hd fsig.(argSizes)).
Notation arg2Size fsig := (vect_hd (vect_tl fsig.(argSizes))).

Module CSigNotations.
  Notation "{{  a1 ~> ret  }}" :=
    {| argSizes := vect_cons a1 vect_nil;
       retSize := ret |}.

  Notation "{{  a1 ~> a2 ~> ret  }}" :=
    {| argSizes := vect_cons a1 (vect_cons a2 vect_nil);
       retSize := ret |}.
End CSigNotations.

Record Sig {n: nat} := { argTypes : vect type n; retType : type }.
Arguments Sig : clear implicits.

Definition CSig_of_Sig {n} (sig: Sig n) : CSig n :=
  {| argSizes := vect_map type_sz sig.(argTypes);
     retSize := type_sz sig.(retType) |}.

Definition Sig_of_CSig {n} (sig: CSig n) : Sig n :=
  {| argTypes := vect_map bits_t sig.(argSizes);
     retType := bits_t sig.(retSize) |}.

Fixpoint Sig_denote' {n} (args: vect type n) (ret: type) :=
  match n return vect type n -> Type with
  | 0 => fun _ => ret
  | S n => fun arg => vect_hd arg -> Sig_denote' (vect_tl arg) ret
  end args.

Definition Sig_denote {n} (sg: Sig n) :=
  Sig_denote' sg.(argTypes) sg.(retType).

Coercion Sig_denote: Sig >-> Sortclass.

Notation arg1Type fsig := (vect_hd fsig.(argTypes)).
Notation arg2Type fsig := (vect_hd (vect_tl fsig.(argTypes))).

Module SigNotations.
  Notation "{{  a1 ~> ret  }}" :=
    {| argTypes := vect_cons a1 vect_nil;
       retType := ret |}.

  Notation "{{  a1 ~> a2 ~> ret  }}" :=
    {| argTypes := vect_cons a1 (vect_cons a2 vect_nil);
       retType := ret |}.
End SigNotations.

(** * External functions **)

Definition ExternalSignature := Sig 1.
Definition CExternalSignature := CSig 1.

(** * Internal functions **)

Definition tsig var_t := list (var_t * type).

Record InternalFunction {fn_name_t var_t action: Type} :=
  { int_name : fn_name_t;
    int_argspec : tsig var_t;
    int_retType : type;
    int_body : action }.
Arguments InternalFunction : clear implicits.
Arguments Build_InternalFunction {fn_name_t var_t action}
          int_name int_argspec int_retType int_body : assert.

Record arg_sig {var_t} :=
  { arg_name: var_t;
    arg_type: type }.

Definition prod_of_argsig {var_t} (a: @arg_sig var_t) :=
  (a.(arg_name), a.(arg_type)).

(** * Equalities **)

Ltac existT_dec :=
  repeat match goal with
         | [ H: existT _ _ ?x = existT _ _ ?y |- _ ] =>
           apply Eqdep_dec.inj_pair2_eq_dec in H; [ | apply eq_dec ]
         end.

Ltac simple_eq :=
  first [ left; solve[eauto] | right; inversion 1; existT_dec; subst; solve[congruence] ].

Instance EqDec_type : EqDec type.
Proof.
  econstructor.
  fix IHtau 1;
    destruct t1 as [ sz1 | en1 | fs1 ];
    destruct t2 as [ sz2 | en2 | fs2 ]; cbn;
      try simple_eq.
  - destruct (eq_dec sz1 sz2); subst;
      simple_eq.
  - destruct en1 as [en1 es1 ebsz1 em1 ebp1];
      destruct en2 as [en2 es2 ebsz2 em2 ebp2].
    destruct (eq_dec en1 en2); subst; try simple_eq.
    destruct (eq_dec es1 es2); subst; try simple_eq.
    destruct (eq_dec ebsz1 ebsz2); subst; try simple_eq.
    destruct (eq_dec em1 em2); subst; try simple_eq.
    destruct (eq_dec ebp1 ebp2); subst; try simple_eq.
  - destruct fs1 as [ nm1 f1 ];
      destruct fs2 as [ nm2 f2 ]; cbn.
    destruct (eq_dec nm1 nm2); subst; try simple_eq.
    destruct (eq_dec (EqDec := _) f1 f2); subst; try simple_eq.
Defined.

Instance EqDec_type_denote {tau: type} : EqDec (type_denote tau).
Proof.
  econstructor.
  revert tau; fix eq_dec_td 1;
    destruct tau as [ ? | ? | [? fields] ]; cbn.
  - apply eq_dec.
  - apply eq_dec.
  - revert fields; fix eq_dec_struct 1.
    destruct fields as [ | (nm, tau) fields ]; cbn.
    + apply eq_dec.
    + destruct t1 as [t1 tt1], t2 as [t2 tt2].
      destruct (eq_dec_td _ t1 t2); subst; try simple_eq.
      destruct (eq_dec_struct _ tt1 tt2); subst; try simple_eq.
Defined.
