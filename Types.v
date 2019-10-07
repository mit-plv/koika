Require Export Coq.Strings.String.
Require Export SGA.Common SGA.Vect SGA.IndexUtils.
Require Import Coq.Lists.List.
Import ListNotations.

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
    (* revert f1 f2; fix IHf 1; *)
    (*   destruct f1 as [ | (n1 & tau1) f1 ], f2 as [ | (n2 & tau2) f2 ]; try simple_eq. *)
    (* destruct (eq_dec n1 n2); subst; try simple_eq. *)
    (* destruct (IHtau tau1 tau2); subst; try simple_eq. *)
    (* destruct (IHf f1 f2) as [ Heq | Hneq ]; subst; try inversion Heq; *)
    (*   try simple_eq. *)
Defined.

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

Coercion type_sz : type >-> nat.

Definition struct_denote' (type_denote: type -> Type) (fields: list (string * type)) :=
  List.fold_right (fun '(_, tau) acc => type_denote tau * acc)%type unit fields.

Fixpoint type_denote tau : Type :=
  match tau with
  | bits_t sz => bits sz
  | enum_t sig => bits sig.(enum_bitsize)
  | struct_t sig => struct_denote' type_denote sig.(struct_fields)
  end.

Notation struct_denote := (struct_denote' type_denote).

Coercion type_denote : type >-> Sortclass.

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

Record ExternalSignature :=
  FunSig { arg1Type: type; arg2Type: type; retType: type }.

Notation "{{  a1 ~> a2 ~> ret  }}" :=
  {| arg1Type := a1; arg2Type := a2; retType := ret |}.

Coercion ExternalSignature_denote fn :=
  fn.(arg1Type) -> fn.(arg2Type) -> fn.(retType).

Lemma ExternalSignature_injRet :
  forall (s1 s2 s1' s2': type) (retType retType': type),
    FunSig s1 s2 retType =
    FunSig s1' s2' retType' ->
    retType = retType'.
Proof. now inversion 1. Qed.

Definition tsig var_t := list (var_t * type).

Record InternalSignature {name_t var_t: Type} :=
  { int_name : name_t;
    int_args : tsig var_t;
    int_retType : type }.
Arguments InternalSignature : clear implicits.

Record arg_sig {var_t} :=
  { arg_name: var_t;
    arg_type: type }.

Definition prod_of_argsig {var_t} (a: @arg_sig var_t) :=
  (a.(arg_name), a.(arg_type)).

Notation "x :: y" := {| arg_name := x%string; arg_type := y |} : intarg_scope.
Delimit Scope intarg_scope with intarg.

(* FIXME improve this notation *)
Notation "{{{  name | x ~> .. ~> z ~> ret  }}}" :=
  {| int_name := name%string;
     int_args := (cons (prod_of_argsig (x%intarg)) .. (cons (prod_of_argsig z%intarg) nil) ..);
     int_retType := ret |} (at level 60).

(* Check {{{ "A" | "x" :: unit_t ~> bits_t 5 }}}. *)

Inductive type_kind :=
  kind_bits | kind_enum (sig: option enum_sig) | kind_struct (sig: option struct_sig).

Inductive fn_tc_error' :=
| FnKindMismatch (expected: type_kind)
| FnUnboundField (f: string) (sig: struct_sig).

(* FIXME add ability to report error on meta arguments *)
(* FIXME and use this to fix the location of unbound field errors *)
Inductive fn_tc_error_loc := Arg1 | Arg2.

Definition fn_tc_error : Type := fn_tc_error_loc * fn_tc_error'.

Definition assert_bits_t arg (tau: type) : result nat fn_tc_error :=
  match tau with
  | bits_t sz => Success sz
  | enum_t _ | struct_t _ => Failure (arg, FnKindMismatch kind_bits)
  end.

Definition assert_struct_t arg (tau: type) : result struct_sig fn_tc_error :=
  match tau with
  | struct_t sg => Success sg
  | bits_t _ | enum_t _ => Failure (arg, FnKindMismatch (kind_struct None))
  end.
