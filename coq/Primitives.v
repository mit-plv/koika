Require Export SGA.Common SGA.Environments SGA.IndexUtils SGA.Types SGA.ErrorReporting.

Inductive comparison :=
  cLt | cGt | cLe | cGe.

Module PrimUntyped.
  Inductive udisplay :=
  | UDisplayUtf8
  | UDisplayValue.

  Inductive uconv :=
  | UPack
  | UUnpack (tau: type)
  | UIgnore.

  Inductive ubits1 :=
  | UNot
  | UZExtL (width: nat)
  | UZExtR (width: nat)
  | UPart (offset: nat) (width: nat).

  Inductive ubits2 :=
  | UAnd
  | UOr
  | UXor
  | ULsl
  | ULsr
  | UConcat
  | USel
  | UPartSubst (offset: nat) (width: nat)
  | UIndexedPart (width: nat)
  | UPlus
  | UMinus
  | UCompare (signed: bool) (c: comparison).

  Inductive ustruct1 :=
  | UGetField (f: string)
  | UGetFieldBits (sig: struct_sig) (f: string).

  Inductive ustruct2 :=
  | USubstField (f: string)
  | USubstFieldBits (sig: struct_sig) (f: string).

  Inductive ufn1 :=
  | UDisplay (fn: udisplay)
  | UConv (fn: uconv)
  | UBits1 (fn: ubits1)
  | UStruct1 (fn: ustruct1).

  Inductive ufn2 :=
  | UEq
  | UBits2 (fn: ubits2)
  | UStruct2 (fn: ustruct2).
End PrimUntyped.

Module PrimTyped.
  Inductive fdisplay :=
  | DisplayUtf8 (len: nat)
  | DisplayValue (tau: type).

  Inductive fconv :=
    Pack | Unpack | Ignore.

  Inductive fbits1 :=
  | Not (sz: nat)
  | ZExtL (sz: nat) (width: nat)
  | ZExtR (sz: nat) (width: nat)
  | Part (sz: nat) (offset: nat) (width: nat).

  Inductive fbits2 :=
  | And (sz: nat)
  | Or (sz: nat)
  | Xor (sz: nat)
  | Lsl (bits_sz: nat) (shift_sz: nat)
  | Lsr (bits_sz: nat) (shift_sz: nat)
  | Concat (sz1 sz2 : nat)
  | Sel (sz: nat)
  | PartSubst (sz: nat) (offset: nat) (width: nat)
  | IndexedPart (sz: nat) (width: nat)
  | Plus (sz : nat)
  | Minus (sz : nat)
  | EqBits (sz: nat)
  | Compare (signed: bool) (c: comparison) (sz: nat).

  Inductive fstruct1 :=
  | GetField.

  Inductive fstruct2 :=
  | SubstField.

  Inductive fn1 :=
  | Display (fn: fdisplay)
  | Conv (tau: type) (fn: fconv)
  | Bits1 (fn: fbits1)
  | Struct1 (fn: fstruct1) (sig: struct_sig) (f: struct_index sig).

  Inductive fn2 :=
  | Eq (tau: type)
  | Bits2 (fn: fbits2)
  | Struct2 (fn: fstruct2) (sig: struct_sig) (f: struct_index sig).

  Definition GetFieldBits (sig: struct_sig) (idx: struct_index sig) : fbits1 :=
    Part (struct_sz sig) (field_offset_right sig idx) (field_sz sig idx).

  Definition SubstFieldBits (sig: struct_sig) (idx: struct_index sig) : fbits2 :=
    PartSubst (struct_sz sig) (field_offset_right sig idx) (field_sz sig idx).
End PrimTyped.

(* Like Nat.log2_iter, but switches to next power of two one number earlier
   (computes ceil(log2(n)) instead of floor(log2(n))). *)
Fixpoint log2_iter k_fuel p_logn q_n r_buffer :=
  match k_fuel with
    | O => p_logn
    | S k_fuel =>
      match r_buffer with
      | O => log2_iter k_fuel (S p_logn) (S q_n) (pred q_n)
      | S r_buffer => log2_iter k_fuel p_logn (S q_n) r_buffer
      end
  end.

Definition log2 n := log2_iter (pred n) 0 1 0.

Module PrimTypeInference.
  Import PrimUntyped PrimTyped.

  Definition find_field sig f : result _ fn_tc_error :=
    opt_result (List_assoc f sig.(struct_fields)) (Arg1, UnboundField f sig).

  Definition tc1 (fn: ufn1) (tau1: type): result fn1 fn_tc_error :=
    match fn with
    | UDisplay fn =>
      match fn with
      | UDisplayUtf8 =>
        let/res sz1 := assert_bits_t Arg1 tau1 in
        Success (Display (DisplayUtf8 sz1))
      | UDisplayValue =>
        Success (Display (DisplayValue tau1))
      end
    | UConv fn =>
      Success (match fn with
               | UPack => Conv tau1 Pack
               | UUnpack tau => Conv tau Unpack
               | UIgnore => Conv tau1 Ignore
               end)
    | UBits1 fn =>
      let/res sz1 := assert_bits_t Arg1 tau1 in
      Success (Bits1 match fn with
                     | UNot => Not sz1
                     | UZExtL width => ZExtL sz1 width
                     | UZExtR width => ZExtR sz1 width
                     | UPart offset width => Part sz1 offset width
                     end)
    | UStruct1 fn =>
      match fn with
      | UGetField f =>
        let/res sig := assert_struct_t Arg1 tau1 in
        let/res idx := find_field sig f in
        Success (Struct1 GetField sig idx)
      | UGetFieldBits sig f =>
        let/res idx := find_field sig f in
        Success (Bits1 (GetFieldBits sig idx))
      end
    end.

  Definition tc2 (fn: ufn2) (tau1: type) (tau2: type): result fn2 fn_tc_error :=
    match fn with
    | UEq => Success (Eq tau1)
    | UBits2 fn =>
      let/res sz1 := assert_bits_t Arg1 tau1 in
      let/res sz2 := assert_bits_t Arg2 tau2 in
      Success (Bits2 match fn with
                     | USel => Sel sz1
                     | UPartSubst offset width => PartSubst sz1 offset width
                     | UIndexedPart width => IndexedPart sz1 width
                     | UAnd => And sz1
                     | UOr => Or sz1
                     | UXor => Xor sz1
                     | ULsl => Lsl sz1 sz2
                     | ULsr => Lsr sz1 sz2
                     | UConcat => Concat sz1 sz2
                     | UPlus => Plus sz1
                     | UMinus => Minus sz1
                     | UCompare signed c => Compare signed c sz1
                     end)
    | UStruct2 fn =>
      match fn with
      | USubstField f =>
        let/res sig := assert_struct_t Arg1 tau1 in
        let/res idx := find_field sig f in
        Success (Struct2 SubstField sig idx)
      | USubstFieldBits sig f =>
        let/res idx := find_field sig f in
        Success (Bits2 (SubstFieldBits sig idx))
      end
    end.
End PrimTypeInference.

Module CircuitSignatures.
  Import PrimTyped.
  Import CSigNotations.

  Definition CSigma1 (fn: fbits1) : CSig 1 :=
    match fn with
    | Not sz => {$ sz ~> sz $}
    | ZExtL sz width => {$ sz ~> (Nat.max sz width) $}
    | ZExtR sz width => {$ sz ~> (Nat.max sz width) $}
    | Part sz offset width => {$ sz ~> width $}
    end.

  Definition CSigma2 (fn: PrimTyped.fbits2) : CSig 2 :=
    match fn with
    | Sel sz => {$ sz ~> (log2 sz) ~> 1 $}
    | PartSubst sz offset width => {$ sz ~> width ~> sz $}
    | IndexedPart sz width => {$ sz ~> (log2 sz) ~> width $}
    | And sz => {$ sz ~> sz ~> sz $}
    | Or sz => {$ sz ~> sz ~> sz $}
    | Xor sz => {$ sz ~> sz ~> sz $}
    | Lsl bits_sz shift_sz => {$ bits_sz ~> shift_sz ~> bits_sz $}
    | Lsr bits_sz shift_sz => {$ bits_sz ~> shift_sz ~> bits_sz $}
    | Concat sz1 sz2 => {$ sz1 ~> sz2 ~> (sz2 + sz1) $}
    | EqBits sz => {$ sz ~> sz ~> 1 $}
    | Plus sz => {$ sz ~> sz ~> sz $}
    | Minus sz => {$ sz ~> sz ~> sz $}
    | Compare _ _ sz => {$ sz ~> sz ~> 1 $}
    end.
End CircuitSignatures.

Module PrimSignatures.
  Import PrimUntyped PrimTyped CircuitSignatures.
  Import SigNotations.

  Definition Sigma1 (fn: fn1) : Sig 1 :=
    match fn with
    | Conv tau fn =>
      match fn with
      | Pack => {$ tau ~> bits_t (type_sz tau) $}
      | Unpack => {$ bits_t (type_sz tau) ~> tau $}
      | Ignore => {$ tau ~> unit_t $}
      end
    | Display fn =>
      {$ match fn with
         | DisplayUtf8 sz => bits_t sz
         | DisplayValue tau => tau
         end ~> unit_t $}
    | Bits1 fn => Sig_of_CSig (CSigma1 fn)
    | Struct1 GetField sig idx => {$ struct_t sig ~> field_type sig idx $}
    end.

  Definition Sigma2 (fn: fn2) : Sig 2 :=
    match fn with
    | Eq tau => {$ tau ~> tau ~> bits_t 1 $}
    | Struct2 SubstField sig idx => {$ struct_t sig ~> field_type sig idx ~> struct_t sig $}
    | Bits2 fn => Sig_of_CSig (CSigma2 fn)
    end.
End PrimSignatures.

Module BitFuns.
  Definition bitfun_of_predicate {sz} (p: bits sz -> bits sz -> bool) (bs1 bs2: bits sz) :=
    Ob~(p bs1 bs2).

  Definition sel {sz} (bs: bits sz) (idx: bits (log2 sz)) :=
    Ob~match Bits.to_index sz idx with
       | Some idx => Bits.nth bs idx
       | _ => false (* TODO: x *)
       end.

  Definition lsl {bits_sz shift_sz} (bs: bits bits_sz) (places: bits shift_sz) :=
    Bits.lsl (Bits.to_nat places) bs.

  Definition lsr {bits_sz shift_sz} (bs: bits bits_sz) (places: bits shift_sz) :=
    Bits.lsr (Bits.to_nat places) bs.

  Definition bits_eq {sz} (bs1 bs2: bits sz) :=
    if eq_dec bs1 bs2 then Ob~1 else Ob~0.

  Definition part {sz} (offset: nat) (width: nat) (bs: bits sz) :=
    vect_extend_end_firstn (vect_firstn width (vect_skipn offset bs)) false.

  Lemma part_subst_cast :
    forall sz width offset,
      Nat.min sz (Nat.min offset sz + (width + (sz - (offset + width)))) = sz.
  Proof.
    induction sz, width, offset; cbn; auto using Min.min_idempotent.
    - f_equal; apply (IHsz 0 offset).
    - f_equal; apply (IHsz width 0).
    - f_equal; apply (IHsz (S width) offset).
  Defined.

  Definition part_subst {sz}
             (offset: nat)
             (width: nat)
             (bs: bits sz)
             (v: bits width) : bits sz :=
    let head := vect_firstn offset bs in
    let tail := vect_skipn (offset + width) bs in
    ltac:(rewrite <- (part_subst_cast sz width offset);
            exact (vect_firstn sz (vect_app head (vect_app v tail)))).

  Fixpoint get_field fields
           (v: struct_denote fields)
           (idx: index (List.length fields))
           {struct fields}
    : type_denote (snd (List_nth fields idx)).
    destruct fields, idx, p; cbn.
    - apply (fst v).
    - apply (get_field fields (snd v) a).
  Defined.

  Fixpoint subst_field fields
           (v: struct_denote fields)
           (idx: index (List.length fields))
           (v': type_denote (snd (List_nth fields idx)))
           {struct fields}
    : (struct_denote fields).
    destruct fields, idx, p; cbn.
    - apply (v', snd v).
    - apply (fst v, subst_field fields (snd v) a v').
  Defined.
End BitFuns.

Module CircuitPrimSpecs.
  Import PrimTyped BitFuns.

  Definition sigma1 (fn: PrimTyped.fbits1) : CSig_denote (CircuitSignatures.CSigma1 fn) :=
    match fn with
    | Not _ => fun bs => Bits.neg bs
    | ZExtL sz width => fun bs => Bits.extend_end bs width false
    | ZExtR sz width => fun bs => Bits.extend_beginning bs width false
    | Part _ offset width => part offset width
    end.

  Definition sigma2 (fn: PrimTyped.fbits2) : CSig_denote (CircuitSignatures.CSigma2 fn) :=
    match fn with
    | Sel _ => sel
    | PartSubst _ offset width => part_subst offset width
    | IndexedPart _ width => fun bs offset => part (Bits.to_nat offset) width bs
    | And _ => Bits.map2 andb
    | Or _ => Bits.map2 orb
    | Xor _ => Bits.map2 xorb
    | Lsl _ _ => lsl
    | Lsr _ _ => lsr
    | Concat _ _ => Bits.app
    | Plus _ => Bits.plus
    | Minus _ => Bits.minus
    | EqBits _ => bits_eq
    | Compare true cLt _ => bitfun_of_predicate Bits.signed_lt
    | Compare true cGt _ => bitfun_of_predicate Bits.signed_gt
    | Compare true cLe _ => bitfun_of_predicate Bits.signed_le
    | Compare true cGe _ => bitfun_of_predicate Bits.signed_ge
    | Compare false cLt _ => bitfun_of_predicate Bits.unsigned_lt
    | Compare false cGt _ => bitfun_of_predicate Bits.unsigned_gt
    | Compare false cLe _ => bitfun_of_predicate Bits.unsigned_le
    | Compare false cGe _ => bitfun_of_predicate Bits.unsigned_ge
    end.
End CircuitPrimSpecs.

Module PrimSpecs.
  Import PrimTyped BitFuns.

  Definition sigma1 (fn: fn1) : Sig_denote (PrimSignatures.Sigma1 fn) :=
    match fn with
    | Display fn =>
      match fn with
      | DisplayUtf8 _ => fun _ => Ob
      | DisplayValue tau => fun _ => Ob
      end
    | Conv tau fn =>
      match fn with
      | Pack => fun v => bits_of_value v
      | Unpack => fun bs => value_of_bits bs
      | Ignore => fun _ => Ob
      end
    | Bits1 fn => CircuitPrimSpecs.sigma1 fn
    | Struct1 GetField sig idx => fun s => get_field sig.(struct_fields) s idx
    end.

  Definition sigma2 (fn: fn2) : Sig_denote (PrimSignatures.Sigma2 fn) :=
    match fn with
    | Eq tau => fun v1 v2 => if eq_dec v1 v2 then Ob~1 else Ob~0
    | Bits2 fn => CircuitPrimSpecs.sigma2 fn
    | Struct2 SubstField sig idx => fun s v => subst_field sig.(struct_fields) s idx v
    end.
End PrimSpecs.
