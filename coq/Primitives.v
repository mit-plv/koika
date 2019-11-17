Require Export Koika.Common Koika.Environments Koika.IndexUtils Koika.Types Koika.ErrorReporting.

Inductive bits_comparison :=
  cLt | cGt | cLe | cGe.

Inductive bits_display_style :=
  dBin | dDec | dHex | dFull.

Record display_options :=
  { display_strings : bool;
    display_newline : bool;
    display_style : bits_display_style }.

Module PrimUntyped.
  Inductive udisplay :=
  | UDisplayUtf8
  | UDisplayValue (opts: display_options).

  Inductive uconv :=
  | UPack
  | UUnpack (tau: type)
  | UIgnore.

  Inductive ubits1 :=
  | UNot
  | USExt (width: nat)
  | UZExtL (width: nat)
  | UZExtR (width: nat)
  | URepeat (times: nat)
  | USlice (offset: nat) (width: nat).

  Inductive ubits2 :=
  | UAnd
  | UOr
  | UXor
  | ULsl
  | ULsr
  | UAsr
  | UConcat
  | USel
  | USliceSubst (offset: nat) (width: nat)
  | UIndexedSlice (width: nat)
  | UPlus
  | UMinus
  | UCompare (signed: bool) (c: bits_comparison).

  Inductive ustruct1 :=
  | UGetField (f: string)
  | UGetFieldBits (sig: struct_sig) (f: string).

  Inductive ustruct2 :=
  | USubstField (f: string)
  | USubstFieldBits (sig: struct_sig) (f: string).

  Inductive uarray1 :=
  | UGetElement (pos: nat)
  | UGetElementBits (sig: array_sig) (pos: nat).

  Inductive uarray2 :=
  | USubstElement (pos: nat)
  | USubstElementBits (sig: array_sig) (pos: nat).

  Inductive ufn1 :=
  | UDisplay (fn: udisplay)
  | UConv (fn: uconv)
  | UBits1 (fn: ubits1)
  | UStruct1 (fn: ustruct1)
  | UArray1 (fn: uarray1).

  Inductive ufn2 :=
  | UEq
  | UBits2 (fn: ubits2)
  | UStruct2 (fn: ustruct2)
  | UArray2 (fn: uarray2).
End PrimUntyped.

Module PrimTyped.
  Inductive fdisplay :=
  | DisplayUtf8 (len: nat)
  | DisplayValue (tau: type) (opts: display_options).

  Inductive fconv :=
    Pack | Unpack | Ignore.

  Inductive fbits1 :=
  | Not (sz: nat)
  | SExt (sz: nat) (width: nat)
  | ZExtL (sz: nat) (width: nat)
  | ZExtR (sz: nat) (width: nat)
  | Repeat (sz: nat) (times: nat)
  | Slice (sz: nat) (offset: nat) (width: nat).

  Inductive fbits2 :=
  | And (sz: nat)
  | Or (sz: nat)
  | Xor (sz: nat)
  | Lsl (bits_sz: nat) (shift_sz: nat)
  | Lsr (bits_sz: nat) (shift_sz: nat)
  | Asr (bits_sz: nat) (shift_sz: nat)
  | Concat (sz1 sz2 : nat)
  | Sel (sz: nat)
  | SliceSubst (sz: nat) (offset: nat) (width: nat)
  | IndexedSlice (sz: nat) (width: nat)
  | Plus (sz : nat)
  | Minus (sz : nat)
  | EqBits (sz: nat)
  | Compare (signed: bool) (c: bits_comparison) (sz: nat).

  Inductive fstruct1 :=
  | GetField.

  Inductive fstruct2 :=
  | SubstField.

  Inductive farray1 :=
  | GetElement.

  Inductive farray2 :=
  | SubstElement.

  Inductive fn1 :=
  | Display (fn: fdisplay)
  | Conv (tau: type) (fn: fconv)
  | Bits1 (fn: fbits1)
  | Struct1 (fn: fstruct1) (sig: struct_sig) (f: struct_index sig)
  | Array1 (fn: farray1) (sig: array_sig) (idx: array_index sig).

  Inductive fn2 :=
  | Eq (tau: type)
  | Bits2 (fn: fbits2)
  | Struct2 (fn: fstruct2) (sig: struct_sig) (f: struct_index sig)
  | Array2 (fn: farray2) (sig: array_sig) (idx: array_index sig).

  Definition GetElementBits (sig: array_sig) (idx: array_index sig) : fbits1 :=
    Slice (array_sz sig) (element_offset_right sig idx) (element_sz sig).

  Definition SubstElementBits (sig: array_sig) (idx: array_index sig) : fbits2 :=
    SliceSubst (array_sz sig) (element_offset_right sig idx) (element_sz sig).

  Definition GetFieldBits (sig: struct_sig) (idx: struct_index sig) : fbits1 :=
    Slice (struct_sz sig) (field_offset_right sig idx) (field_sz sig idx).

  Definition SubstFieldBits (sig: struct_sig) (idx: struct_index sig) : fbits2 :=
    SliceSubst (struct_sz sig) (field_offset_right sig idx) (field_sz sig idx).
End PrimTyped.

Module PrimTypeInference.
  Import PrimUntyped PrimTyped.

  Definition find_field sig f : result _ fn_tc_error :=
    opt_result (List_assoc f sig.(struct_fields)) (Arg1, UnboundField f sig).

  Definition check_index sig pos : result (array_index sig) fn_tc_error :=
    opt_result (Vect.index_of_nat sig.(array_len) pos) (Arg1, OutOfBounds pos sig).

  Definition tc1 (fn: ufn1) (tau1: type): result fn1 fn_tc_error :=
    match fn with
    | UDisplay fn =>
      match fn with
      | UDisplayUtf8 =>
        let/res sig := assert_kind (kind_array None) Arg1 tau1 in
        Success (Display (DisplayUtf8 sig.(array_len)))
      | UDisplayValue opts =>
        Success (Display (DisplayValue tau1 opts))
      end
    | UConv fn =>
      Success (match fn with
               | UPack => Conv tau1 Pack
               | UUnpack tau => Conv tau Unpack
               | UIgnore => Conv tau1 Ignore
               end)
    | UBits1 fn =>
      let/res sz1 := assert_kind kind_bits Arg1 tau1 in
      Success (Bits1 match fn with
                     | UNot => Not sz1
                     | USExt width => SExt sz1 width
                     | UZExtL width => ZExtL sz1 width
                     | UZExtR width => ZExtR sz1 width
                     | URepeat times => Repeat sz1 times
                     | USlice offset width => Slice sz1 offset width
                     end)
    | UStruct1 fn =>
      match fn with
      | UGetField f =>
        let/res sig := assert_kind (kind_struct None) Arg1 tau1 in
        let/res idx := find_field sig f in
        Success (Struct1 GetField sig idx)
      | UGetFieldBits sig f =>
        let/res idx := find_field sig f in
        Success (Bits1 (GetFieldBits sig idx))
      end
    | UArray1 fn =>
      match fn with
      | UGetElement pos =>
        let/res sig := assert_kind (kind_array None) Arg1 tau1 in
        let/res idx := check_index sig pos in
        Success (Array1 GetElement sig idx)
      | UGetElementBits sig pos =>
        let/res idx := check_index sig pos in
        Success (Bits1 (GetElementBits sig idx))
      end
    end.

  Definition tc2 (fn: ufn2) (tau1: type) (tau2: type): result fn2 fn_tc_error :=
    match fn with
    | UEq => Success (Eq tau1)
    | UBits2 fn =>
      let/res sz1 := assert_kind kind_bits Arg1 tau1 in
      let/res sz2 := assert_kind kind_bits Arg2 tau2 in
      Success (Bits2 match fn with
                     | USel => Sel sz1
                     | USliceSubst offset width => SliceSubst sz1 offset width
                     | UIndexedSlice width => IndexedSlice sz1 width
                     | UAnd => And sz1
                     | UOr => Or sz1
                     | UXor => Xor sz1
                     | ULsl => Lsl sz1 sz2
                     | ULsr => Lsr sz1 sz2
                     | UAsr => Asr sz1 sz2
                     | UConcat => Concat sz1 sz2
                     | UPlus => Plus sz1
                     | UMinus => Minus sz1
                     | UCompare signed c => Compare signed c sz1
                     end)
    | UStruct2 fn =>
      match fn with
      | USubstField f =>
        let/res sig := assert_kind (kind_struct None) Arg1 tau1 in
        let/res idx := find_field sig f in
        Success (Struct2 SubstField sig idx)
      | USubstFieldBits sig f =>
        let/res idx := find_field sig f in
        Success (Bits2 (SubstFieldBits sig idx))
      end
    | UArray2 fn =>
      match fn with
      | USubstElement pos =>
        let/res sig := assert_kind (kind_array None) Arg1 tau1 in
        let/res idx := check_index sig pos in
        Success (Array2 SubstElement sig idx)
      | USubstElementBits sig pos =>
        let/res idx := check_index sig pos in
        Success (Bits2 (SubstElementBits sig idx))
      end
    end.
End PrimTypeInference.

Module CircuitSignatures.
  Import PrimTyped.
  Import CSigNotations.

  Definition CSigma1 (fn: fbits1) : CSig 1 :=
    match fn with
    | Not sz => {$ sz ~> sz $}
    | SExt sz width => {$ sz ~> (Nat.max sz width) $}
    | ZExtL sz width => {$ sz ~> (Nat.max sz width) $}
    | ZExtR sz width => {$ sz ~> (Nat.max sz width) $}
    | Repeat sz times => {$ sz ~> times * sz $}
    | Slice sz offset width => {$ sz ~> width $}
    end.

  Definition CSigma2 (fn: PrimTyped.fbits2) : CSig 2 :=
    match fn with
    | Sel sz => {$ sz ~> (log2 sz) ~> 1 $}
    | SliceSubst sz offset width => {$ sz ~> width ~> sz $}
    | IndexedSlice sz width => {$ sz ~> (log2 sz) ~> width $}
    | And sz => {$ sz ~> sz ~> sz $}
    | Or sz => {$ sz ~> sz ~> sz $}
    | Xor sz => {$ sz ~> sz ~> sz $}
    | Lsl bits_sz shift_sz => {$ bits_sz ~> shift_sz ~> bits_sz $}
    | Lsr bits_sz shift_sz => {$ bits_sz ~> shift_sz ~> bits_sz $}
    | Asr bits_sz shift_sz => {$ bits_sz ~> shift_sz ~> bits_sz $}
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
         | DisplayUtf8 len => array_t {| array_len := len; array_type := bits_t 8 |}
         | DisplayValue tau _ => tau
         end ~> unit_t $}
    | Bits1 fn => Sig_of_CSig (CSigma1 fn)
    | Struct1 GetField sig idx => {$ struct_t sig ~> field_type sig idx $}
    | Array1 GetElement sig idx => {$ array_t sig ~> sig.(array_type) $}
    end.

  Definition Sigma2 (fn: fn2) : Sig 2 :=
    match fn with
    | Eq tau => {$ tau ~> tau ~> bits_t 1 $}
    | Bits2 fn => Sig_of_CSig (CSigma2 fn)
    | Struct2 SubstField sig idx => {$ struct_t sig ~> field_type sig idx ~> struct_t sig $}
    | Array2 SubstElement sig idx => {$ array_t sig ~> sig.(array_type) ~> array_t sig $}
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

  Definition asr {bits_sz shift_sz} (bs: bits bits_sz) (places: bits shift_sz) :=
    Bits.asr (Bits.to_nat places) bs.

  Definition bits_eq {sz} (bs1 bs2: bits sz) :=
    if eq_dec bs1 bs2 then Ob~1 else Ob~0.

  Definition slice {sz} (offset: nat) (width: nat) (bs: bits sz) :=
    vect_extend_end_firstn (vect_firstn width (vect_skipn offset bs)) false.

  Lemma slice_subst_cast :
    forall sz width offset,
      Nat.min sz (Nat.min offset sz + (width + (sz - (offset + width)))) = sz.
  Proof.
    induction sz, width, offset; cbn; auto using Min.min_idempotent.
    - f_equal; apply (IHsz 0 offset).
    - f_equal; apply (IHsz width 0).
    - f_equal; apply (IHsz (S width) offset).
  Defined.

  Definition slice_subst {sz}
             (offset: nat)
             (width: nat)
             (bs: bits sz)
             (v: bits width) : bits sz :=
    let head := vect_firstn offset bs in
    let tail := vect_skipn (offset + width) bs in
    ltac:(rewrite <- (slice_subst_cast sz width offset);
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
    | SExt sz width => fun bs => Bits.extend_end bs width (Bits.msb bs)
    | ZExtL sz width => fun bs => Bits.extend_end bs width false
    | ZExtR sz width => fun bs => Bits.extend_beginning bs width false
    | Repeat sz times => fun bs => Bits.repeat times bs
    | Slice _ offset width => slice offset width
    end.

  Definition sigma2 (fn: PrimTyped.fbits2) : CSig_denote (CircuitSignatures.CSigma2 fn) :=
    match fn with
    | Sel _ => sel
    | SliceSubst _ offset width => slice_subst offset width
    | IndexedSlice _ width => fun bs offset => slice (Bits.to_nat offset) width bs
    | And _ => Bits.map2 andb
    | Or _ => Bits.map2 orb
    | Xor _ => Bits.map2 xorb
    | Lsl _ _ => lsl
    | Lsr _ _ => lsr
    | Asr _ _ => asr
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
      | DisplayValue tau _ => fun _ => Ob
      end
    | Conv tau fn =>
      match fn with
      | Pack => fun v => bits_of_value v
      | Unpack => fun bs => value_of_bits bs
      | Ignore => fun _ => Ob
      end
    | Bits1 fn => CircuitPrimSpecs.sigma1 fn
    | Struct1 GetField sig idx => fun s => get_field sig.(struct_fields) s idx
    | Array1 GetElement sig idx => fun a => vect_nth a idx
    end.

  Definition sigma2 (fn: fn2) : Sig_denote (PrimSignatures.Sigma2 fn) :=
    match fn with
    | Eq tau => fun v1 v2 => if eq_dec v1 v2 then Ob~1 else Ob~0
    | Bits2 fn => CircuitPrimSpecs.sigma2 fn
    | Struct2 SubstField sig idx => fun s v => subst_field sig.(struct_fields) s idx v
    | Array2 SubstElement sig idx => fun a e => vect_replace a idx e
    end.
End PrimSpecs.
