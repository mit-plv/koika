(*! Language | Types used by Kôika programs !*)
Require Export Coq.Strings.String.
Require Export Koika.Common Koika.IndexUtils.

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

Record array_sig' {A} :=
  { array_type: A;
    array_len: nat }.
Arguments array_sig' : clear implicits.

Inductive type : Type :=
| bits_t (sz: nat)
| enum_t (sig: enum_sig)
| struct_t (sig: struct_sig' type)
| array_t (sig: array_sig' type).

Notation unit_t := (bits_t 0).
Notation struct_sig := (struct_sig' type).
Notation array_sig := (array_sig' type).

Inductive type_kind :=
| kind_bits
| kind_enum (sig: option enum_sig)
| kind_struct (sig: option struct_sig)
| kind_array (sig: option array_sig).

Definition kind_of_type (tau: type) :=
  match tau with
  | bits_t sz => kind_bits
  | enum_t sig => kind_enum (Some sig)
  | struct_t sig => kind_struct (Some sig)
  | array_t sig => kind_array (Some sig)
  end.

Definition struct_fields_sz' (type_sz: type -> nat) (fields: list (string * type)) :=
  list_sum (List.map (fun nm_tau => type_sz (snd nm_tau)) fields).

Fixpoint type_sz tau :=
  match tau with
  | bits_t sz => sz
  | enum_t sig => sig.(enum_bitsize)
  | struct_t sig => struct_fields_sz' type_sz sig.(struct_fields)
  | array_t sig => Bits.rmul sig.(array_len) (type_sz sig.(array_type))
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

Definition array_index (sig: array_sig) :=
  Vect.index sig.(array_len).

Definition array_sz sig :=
  type_sz (array_t sig).

Definition element_sz (sig: array_sig) :=
  type_sz sig.(array_type).

Definition element_offset_right (sig: array_sig) (idx: array_index sig) :=
  Bits.rmul (sig.(array_len) - S (Vect.index_to_nat idx)) (element_sz sig).

Notation struct_bits_t sig :=
  (bits_t (struct_sz sig)).

Notation field_bits_t sig idx :=
  (bits_t (field_sz sig idx)).

Inductive Port :=
  P0 | P1.

(** * Denotations *)

Definition struct_denote' (type_denote: type -> Type) (fields: list (string * type)) :=
  List.fold_right (fun k_tau acc => type_denote (snd k_tau) * acc)%type unit fields.

Fixpoint type_denote tau : Type :=
  match tau with
  | bits_t sz => bits sz
  | enum_t sig => bits sig.(enum_bitsize)
  | struct_t sig => struct_denote' type_denote sig.(struct_fields)
  | array_t sig => vect (type_denote sig.(array_type)) sig.(array_len)
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
  | bits_t _ => fun bs => bs
  | enum_t _ => fun bs => bs
  | struct_t _ => fun str => bits_of_struct_value str
  | array_t _ => fun v => Bits.appn (vect_map bits_of_value v)
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
  | bits_t _ => fun bs => bs
  | enum_t _ => fun bs => bs
  | struct_t _ => fun bs => value_of_struct_bits bs
  | array_t _ => fun bs => vect_map value_of_bits (Bits.splitn bs)
  end bs.

Example ex__bits_of_value :=
  Eval simpl in
    let t := struct_t
              {| struct_name := "xyz";
                 struct_fields :=
                   [("mm_typ", bits_t 2);
                    ("addr", bits_t 8);
                    ("data", array_t {| array_type := bits_t 2;
                                        array_len := 3 |})] |}%string in
    let mm_typ := Ob~0~1 in
    let mm_addr := Ob~1~1~1~1~0~0~0~0 in
    let mm_data := [Ob~1~0; Ob~0~0; Ob~1~1]%vect in
    bits_of_value ((mm_typ, (mm_addr, (mm_data, tt))): type_denote t).
(* [ex__bits_of_value = Ob~0~1~1~1~1~1~0~0~0~0~1~0~0~0~1~1 : bits 16] *)

Definition bits_of_value_of_bits :
  forall tau (bs: bits (type_sz tau)),
    bits_of_value (value_of_bits bs) = bs.
Proof.
  fix IHtau 1; destruct tau as [sz | sig | sig | sig]; cbn.
  - reflexivity.
  - reflexivity.
  - destruct sig; cbn.
    revert struct_fields0.
    fix IHfields 1. destruct struct_fields0 as [ | (nm & tau) struct_fields0 ]; cbn.
    + destruct bs; reflexivity.
    + intros; rewrite IHtau, IHfields; apply vect_app_split.
  - intros;
      erewrite vect_map_map, (vect_map_id _ (IHtau _)), Bits.appn_splitn;
      reflexivity.
Qed.

Definition value_of_bits_of_value :
  forall tau (v: type_denote tau),
    (value_of_bits (bits_of_value v)) = v.
Proof.
  fix IHt 1; destruct tau as [sz | sig | sig | sig]; cbn.
  - reflexivity.
  - reflexivity.
  - destruct sig; cbn.
    revert struct_fields0.
    fix IH 1. destruct struct_fields0 as [ | (nm & tau) struct_fields0 ]; cbn.
    + destruct v; reflexivity.
    + cbn.
      intros.
      rewrite (surjective_pairing v).
      unfold Bits.split.
      rewrite vect_split_app.
      cbn.
      rewrite IH, IHt.
      reflexivity.
  - intros;
      erewrite Bits.splitn_appn, vect_map_map, (vect_map_id _ (IHt _));
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

Coercion type_denote : type >-> Sortclass.

(** * Anonymous function signatures **)

Record _Sig {argKind: Type} {nArgs: nat} :=
  { argSigs : vect argKind nArgs; retSig : argKind }.
Arguments _Sig : clear implicits.

Fixpoint _Sig_denote {nArgs argKind} (type_of_argKind: argKind -> Type)
         (args: vect argKind nArgs) (ret: argKind) :=
  match nArgs return vect argKind nArgs -> Type with
  | 0 => fun _ => type_of_argKind ret
  | S n => fun arg => type_of_argKind (vect_hd arg) ->
                  _Sig_denote type_of_argKind (vect_tl arg) ret
  end args.

Notation Sig n := (_Sig type n).
Notation CSig n := (_Sig nat n).

Definition CSig_denote {n} (sg: CSig n) :=
  _Sig_denote (@Bits.bits) sg.(argSigs) sg.(retSig).

Definition Sig_denote {n} (sg: Sig n) :=
  _Sig_denote type_denote sg.(argSigs) sg.(retSig).

Definition CSig_of_Sig {n} (sig: Sig n) : CSig n :=
  {| argSigs := vect_map type_sz sig.(argSigs);
     retSig := type_sz sig.(retSig) |}.

Definition Sig_of_CSig {n} (sig: CSig n) : Sig n :=
  {| argSigs := vect_map bits_t sig.(argSigs);
     retSig := bits_t sig.(retSig) |}.

Notation arg1Sig := (fun fsig => (vect_hd fsig.(argSigs))).
Notation arg2Sig := (fun fsig => (vect_hd (vect_tl fsig.(argSigs)))).

Module SigNotations.
  Notation "{$  a1 ~> ret  $}" :=
    {| argSigs := vect_cons a1 vect_nil;
       retSig := ret |}.

  Notation "{$  a1 ~> a2 ~> ret  $}" :=
    {| argSigs := vect_cons a1 (vect_cons a2 vect_nil);
       retSig := ret |}.
End SigNotations.

(** * External functions **)

Definition ExternalSignature := Sig 1.
Definition CExternalSignature := CSig 1.

(** * Internal functions **)

Definition tsig var_t := list (var_t * type).
Definition lsig := list nat.

Record InternalFunction {var_t fn_name_t action: Type} :=
  { int_name : fn_name_t;
    int_argspec : tsig var_t;
    int_retSig : type;
    int_body : action }.
Arguments InternalFunction : clear implicits.
Arguments Build_InternalFunction {var_t fn_name_t action}
          int_name int_argspec int_retSig int_body : assert.

Definition map_intf_body {var_t fn_name_t action action': Type}
           (f: action -> action') (fn: InternalFunction var_t fn_name_t action) :=
  {| int_name := fn.(int_name);
     int_argspec := fn.(int_argspec);
     int_retSig := fn.(int_retSig);
     int_body := f fn.(int_body) |}.

Record arg_sig {var_t} :=
  { arg_name: var_t;
    arg_type: type }.
Arguments arg_sig : clear implicits.

Definition prod_of_argsig {var_t} (a: @arg_sig var_t) :=
  (a.(arg_name), a.(arg_type)).

(** * Debugging and disambiguation of type names **)

Fixpoint type_id (tau: type) : string :=
  match tau with
  | bits_t sz => "bits_" ++ show sz
  | enum_t sig => sig.(enum_name)
  | struct_t sig => sig.(struct_name)
  | array_t sig => "array_" ++ show sig.(array_len) ++ "_" ++ type_id sig.(array_type)
  end.

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
    destruct t1 as [ sz1 | en1 | fs1 | as1 ];
    destruct t2 as [ sz2 | en2 | fs2 | as2 ]; cbn;
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
  - destruct as1 as [ tau1 len1 ];
      destruct as2 as [ tau2 len2 ]; cbn.
    destruct (IHtau tau1 tau2); subst; try simple_eq.
    destruct (eq_dec len1 len2); subst; try simple_eq.
Defined.

Instance EqDec_type_denote {tau: type} : EqDec (type_denote tau).
Proof.
  econstructor.
  revert tau; fix eq_dec_td 1;
    destruct tau as [ ? | ? | [? fields] | ? ]; cbn.
  - apply eq_dec.
  - apply eq_dec.
  - revert fields; fix eq_dec_struct 1.
    destruct fields as [ | (nm, tau) fields ]; cbn.
    + apply eq_dec.
    + destruct t1 as [t1 tt1], t2 as [t2 tt2].
      destruct (eq_dec_td _ t1 t2); subst; try simple_eq.
      destruct (eq_dec_struct _ tt1 tt2); subst; try simple_eq.
  - pose {| eq_dec := eq_dec_td (sig.(array_type)) |}.
    apply eq_dec.
Defined.
