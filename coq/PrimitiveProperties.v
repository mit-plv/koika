(*! Equations showing how to implement functions on structures and arrays as bitfuns !*)
Require Import Koika.Primitives.
Import BitFuns.

Ltac min_t :=
  repeat match goal with
         | [ |- context[Min.min ?x ?y] ] =>
           first [rewrite (Min.min_l x y) by min_t | rewrite (Min.min_r x y) by min_t ]
         | _ => omega
         end.

Lemma slice_end :
  forall sz sz' (v : bits (sz + sz')),
    slice sz sz' v = vect_skipn_plus sz v.
Proof.
  intros.
  apply vect_to_list_inj.
  unfold slice, vect_skipn_plus, vect_extend_end_firstn, vect_extend_end.
  autorewrite with vect_to_list.
  min_t; rewrite Nat.sub_diag by omega; cbn.
  rewrite app_nil_r.
  rewrite firstn_skipn.
  rewrite firstn_all2 by (rewrite vect_to_list_length; reflexivity).
  reflexivity.
Qed.

Lemma slice_front :
  forall n sz (v: bits (n + sz)) offset width,
    offset + width <= n ->
    slice offset width v =
    slice offset width (vect_firstn_plus n v).
Proof.
  intros.
  apply vect_to_list_inj.
  unfold slice, vect_extend_end_firstn, vect_extend_end, vect_firstn_plus.
  autorewrite with vect_to_list.
  rewrite skipn_firstn, firstn_firstn.
  min_t; reflexivity.
Qed.

Lemma struct_slice_correct_le :
  forall fields idx,
    struct_fields_sz (skipn (S (index_to_nat idx)) fields) + type_sz (snd (List_nth fields idx)) <=
    struct_fields_sz fields.
Proof.
  intros.
  change (type_sz (snd (List_nth fields idx))) with (struct_fields_sz [List_nth fields idx]).
  rewrite plus_comm; setoid_rewrite <- list_sum_app; rewrite <- map_app; cbn [List.app].
  rewrite List_nth_skipn_cons_next.
  rewrite <- skipn_map.
  apply list_sum_skipn_le.
Qed.

Lemma array_slice_correct_le :
  forall n n' sz,
    n' < n ->
    Bits.rmul (n - S n') sz + sz <= Bits.rmul n sz.
Proof.
  intros.
  rewrite !Bits.rmul_correct.
  rewrite <- Nat.mul_succ_l.
  auto using Nat.mul_le_mono_r with arith.
Qed.

Lemma slice_subst_end :
  forall sz0 sz (bs0: bits (sz0 + sz)) (bs: bits sz),
    slice_subst sz0 sz bs0 bs = Bits.app bs (fst (Bits.split bs0)).
Proof.
  unfold Bits.split; intros; rewrite vect_split_firstn_skipn; cbn.
  apply vect_to_list_inj.
  unfold slice_subst, vect_skipn_plus, vect_firstn_plus, vect_extend_end_firstn, vect_extend_end.
  autorewrite with vect_to_list.
  rewrite !firstn_app.
  rewrite firstn_length_le by (rewrite vect_to_list_length; omega).
  rewrite !minus_plus, vect_to_list_length, Nat.sub_diag; cbn.
  rewrite firstn_firstn by omega; min_t.
  rewrite (firstn_all2 (n := sz)) by (rewrite vect_to_list_length; omega).
  rewrite app_nil_r; reflexivity.
Qed.

Lemma slice_subst_front :
  forall sz0 sz width (bs0: bits (sz0 + sz)) (bs: bits width) offset,
    offset + width <= sz0 ->
    slice_subst offset width bs0 bs =
    Bits.app (vect_skipn_plus sz0 bs0) (slice_subst offset width (vect_firstn_plus sz0 bs0) bs).
Proof.
  clear.
  intros.
  apply vect_to_list_inj;
    unfold slice_subst, vect_skipn_plus, vect_firstn_plus, vect_extend_end_firstn, vect_extend_end.
  autorewrite with vect_to_list.
  rewrite !firstn_app.
  rewrite firstn_length_le by (rewrite vect_to_list_length; omega).
  rewrite vect_to_list_length; cbn.
  rewrite !firstn_firstn; repeat min_t.
  rewrite firstn_length_le by (rewrite vect_to_list_length; omega).
  rewrite <- !app_assoc.
  rewrite skipn_firstn, firstn_firstn.
  min_t.
  rewrite !(firstn_all2 (vect_to_list bs)) by (rewrite vect_to_list_length; omega).
  replace (sz0 + sz - offset - width) with (sz0 + sz - (offset + width)) by omega.
  replace (sz0 - offset - width) with (sz0 - (offset + width)) by omega.
  rewrite <- !skipn_firstn.
  rewrite (firstn_all2 (n := sz0 + sz)) by (rewrite vect_to_list_length; omega).
  rewrite <- skipn_app by (rewrite firstn_length, vect_to_list_length; min_t; omega).
  rewrite List.firstn_skipn.
  reflexivity.
Qed.

Ltac _eq_t :=
  unfold _eq, _neq, beq_dec;
    intros; repeat destruct eq_dec;
      try match goal with
          | [ H: bits_of_value _ = bits_of_value _ |- _ ] => apply bits_of_value_inj in H
          end; subst; congruence.

Lemma _eq_of_value:
  forall {tau: type} {EQ: EqDec tau} (a1 a2: tau),
    _eq (bits_of_value a1) (bits_of_value a2) =
    _eq a1 a2.
Proof. _eq_t. Qed.

Lemma _neq_of_value:
  forall {tau: type} {EQ: EqDec tau} (a1 a2: tau),
    _neq (bits_of_value a1) (bits_of_value a2) =
    _neq a1 a2.
Proof. _eq_t. Qed.

Lemma get_field_bits_slice:
  forall {sig} (idx : struct_index sig) (a : type_denote (struct_t sig)),
    slice (field_offset_right sig idx) (field_sz sig idx) (bits_of_value a) =
    bits_of_value (get_field (struct_fields sig) a idx).
Proof.
  intro sig;
    repeat (simpl; unfold struct_index, field_type, field_sz, field_offset_right).
  induction (struct_fields sig) as [ | (nm & tau) l ]; simpl.
  * destruct idx.
  * destruct idx as [ | idx], a; cbn in *; intros.
    -- rewrite slice_end, vect_skipn_plus_app.
       reflexivity.
    -- rewrite <- IHl.
       rewrite slice_front, vect_firstn_plus_app by apply struct_slice_correct_le.
       reflexivity.
Qed.

Lemma get_element_bits_slice:
  forall (sig : array_sig) (idx : array_index sig)
    (a : vect (array_type sig) (array_len sig)),
    slice (element_offset_right sig idx) (element_sz sig)
          (Bits.appn (vect_map bits_of_value a)) =
    bits_of_value (vect_nth a idx).
Proof.
  intros sig;
    repeat (simpl; unfold array_index, element_sz, element_offset_right).
  induction (array_len sig); simpl.
  * destruct idx.
  * destruct idx as [ | idx], a; cbn in *; intros.
    -- rewrite Nat.sub_0_r, slice_end, vect_skipn_plus_app.
       reflexivity.
    -- rewrite <- IHn.
       rewrite slice_front, vect_firstn_plus_app by apply array_slice_correct_le, index_to_nat_bounded.
       reflexivity.
Qed.

Lemma subst_field_bits_slice_subst:
  forall {sig} (idx : struct_index sig) (a1 : type_denote (struct_t sig)) (a2 : field_type sig idx),
    slice_subst (field_offset_right sig idx) (field_sz sig idx) (bits_of_value a1) (bits_of_value a2) =
    bits_of_value (tau := struct_t _) (subst_field (struct_fields sig) a1 idx a2).
Proof.
  intro sig;
    repeat (simpl; unfold struct_index, field_type, field_sz, field_offset_right).
  induction (struct_fields sig) as [ | (nm & tau) l ]; simpl.
  * destruct idx.
  * destruct idx as [ | idx], a1; cbn in *; intros.
    -- rewrite slice_subst_end, vect_split_app.
       reflexivity.
    -- rewrite <- IHl.
       rewrite slice_subst_front, vect_firstn_plus_app, vect_skipn_plus_app by apply struct_slice_correct_le.
       reflexivity.
Qed.

Lemma subst_element_bits_slice_subst:
  forall (sig : array_sig) (idx : array_index sig)
    (a1 : vect (array_type sig) (array_len sig)) (a2 : array_type sig),
    slice_subst (element_offset_right sig idx) (element_sz sig)
                (Bits.appn (vect_map bits_of_value a1)) (bits_of_value a2) =
    Bits.appn (vect_map bits_of_value (vect_replace a1 idx a2)).
Proof.
  intro sig;
    repeat (simpl; unfold array_index, element_sz, element_offset_right).
  induction (array_len sig); simpl.
  * destruct 1.
  * destruct idx as [ | idx], a1; cbn in *; intros.
    -- rewrite Nat.sub_0_r, slice_subst_end, vect_split_app.
       reflexivity.
    -- rewrite <- IHn.
       rewrite slice_subst_front, vect_firstn_plus_app, vect_skipn_plus_app by apply array_slice_correct_le, index_to_nat_bounded.
       reflexivity.
Qed.

Lemma sel_msb {sz} (bs: bits sz):
  BitFuns.sel bs (Bits.of_nat (log2 sz) (pred sz)) =
  Ob~(Bits.msb bs).
Proof.
  unfold sel, Bits.to_index.
  rewrite Bits.to_nat_of_nat by eauto using pred_lt_pow2_log2.
  destruct sz.
  - reflexivity.
  - rewrite index_of_nat_largest.
    setoid_rewrite vect_last_nth; reflexivity.
Qed.

Definition slice_subst_impl {sz} offset {width} (a1: bits sz) (a2: bits width) :=
  match le_gt_dec offset sz with
  | left pr =>
    rew le_plus_minus_r offset sz pr in
      ((BitFuns.slice 0 offset a1) ++
       (match le_gt_dec width (sz - offset) with
        | left pr =>
          rew le_plus_minus_r width (sz - offset) pr in
            (a2 ++ BitFuns.slice (offset + width) (sz - offset - width) a1)
        | right _ => BitFuns.slice 0 (sz - offset) a2
        end))%vect
  | right _ => a1
  end.

Hint Unfold BitFuns.slice : vect_to_list.
Hint Unfold BitFuns.slice_subst : vect_to_list.
Hint Unfold slice_subst_impl : vect_to_list.
Hint Unfold vect_extend_end : vect_to_list.
Hint Unfold vect_extend_end_firstn : vect_to_list.

Ltac vect_to_list_t_step :=
  match goal with
  | _ => progress cbn
  | _ => progress (autounfold with vect_to_list)
  | _ => progress autorewrite with vect_to_list vect_to_list_cleanup
  | [ |- context[match ?x with _ => _ end] ] => destruct x
  | _ => repeat rewrite ?Min.min_l, ?Min.min_r by omega
  end.

Ltac vect_to_list_t :=
  try apply vect_to_list_inj; repeat vect_to_list_t_step.

Lemma slice_subst_impl_correct :
  forall {sz} offset {width} (a1: bits sz) (a2: bits width),
    BitFuns.slice_subst offset width a1 a2 =
    slice_subst_impl offset a1 a2.
Proof.
  intros; vect_to_list_t.
  - rewrite (firstn_all2 (n := sz - offset)) by (autorewrite with vect_to_list; omega).
    reflexivity.
  - rewrite (skipn_all2 (n := offset + width)) by (autorewrite with vect_to_list; omega).
    autorewrite with vect_to_list_cleanup; reflexivity.
  - rewrite (firstn_all2 (n := sz)) by (autorewrite with vect_to_list; omega).
    reflexivity.
Qed.

Lemma slice_full {sz}:
  forall (bs: bits sz),
    BitFuns.slice 0 sz bs = bs.
Proof.
  intros; vect_to_list_t.
  rewrite (firstn_all2 (n := sz)) by (autorewrite with vect_to_list; omega);
    reflexivity.
Qed.

Lemma slice_concat_l {sz1 sz2} :
  forall (bs1: bits sz1) (bs2: bits sz2),
    BitFuns.slice 0 sz1 (bs1 ++ bs2)%vect = bs1.
Proof.
  intros; vect_to_list_t.
  rewrite (firstn_all2 (n := sz1)) by (autorewrite with vect_to_list; omega);
    reflexivity.
Qed.

Lemma slice_concat_r {sz1 sz2} :
  forall (bs1: bits sz1) (bs2: bits sz2),
    BitFuns.slice sz1 sz2 (bs1 ++ bs2)%vect = bs2.
Proof.
  intros; vect_to_list_t.
  rewrite (skipn_all2 (n := sz1)) by (autorewrite with vect_to_list; omega).
  vect_to_list_t.
  rewrite (firstn_all2 (n := sz2)) by (autorewrite with vect_to_list; omega).
  reflexivity.
Qed.

Section Arithmetic.
  (* This might require another hypothesis to be correct *)
  Lemma sel_spec :
    forall (sz: nat) (bs: bits sz) idx,
      BitFuns.sel bs idx = Ob~(N.testbit (Bits.to_N bs) (Bits.to_N idx)).
  Proof.
  Admitted.

  Lemma to_N_lsl :
    forall sz1 sz2 (x: bits sz1) (y: bits sz2),
      (Bits.to_N (BitFuns.lsl x y) =
       (Bits.to_N x * (2 ^ (Bits.to_N y))) mod (2 ^ N.of_nat sz1))%N.
  Proof.
  Admitted.

  Lemma to_N_extend_end_false :
    forall sz (x: bits sz) sz', Bits.to_N (Bits.extend_end x sz' false) = Bits.to_N x.
  Proof.
  Admitted.

End Arithmetic.

Ltac Bits_to_N_t :=
  unfold PrimSpecs.sigma1, CircuitPrimSpecs.sigma1,
  PrimSpecs.sigma2, CircuitPrimSpecs.sigma2,
  Bits.plus, Bits.mul in *;
  simpl arg1Sig;
  repeat match goal with
         | _ => progress bool_step
         | _ => progress (rewrite Bits.of_N_to_N in * )
         | [ H: Ob~_ = Ob~_ |- _ ] => injection H as H
         | [ H: Bits.single (Bits.neg _) = true |- _ ] =>
           apply negb_true_iff in H
         | [ H: Bits.single (Bits.neg _) = false |- _ ] =>
           apply negb_false_iff in H
         | [ H: Bits.single (Bits.and _ _) = true |- _ ] =>
           apply andb_true_iff in H; destruct H
         | [ H: Bits.single (Bits.and _ _) = false |- _ ] =>
           apply andb_false_iff in H
         | [ H: Bits.single (BitFuns._eq _ _) = true |- _ ] =>
           apply beq_dec_iff in H
         | [ H: Bits.single (BitFuns._eq _ _) = false |- _ ] =>
           apply beq_dec_false_iff in H
         | [ H: Bits.single ?bs = _ |- _ ] =>
           apply Bits.single_to_bits in H
         | _ => progress (rewrite sel_spec in * )
         | [ H: context[Bits.to_N (BitFuns.lsl ?x ?y)] |- _ ] =>
           rewrite to_N_lsl in H
         | [ |- context[Bits.to_N (BitFuns.lsl ?x ?y)] ] =>
           rewrite to_N_lsl
         | [ H: context[Bits.to_N (Bits.extend_end ?bs ?sz' false)] |- _ ] =>
           setoid_rewrite (to_N_extend_end_false (Bits.size bs) bs sz') in H
         | [ |- context[Bits.to_N (Bits.extend_end ?bs ?sz' false)] ] =>
           setoid_rewrite (to_N_extend_end_false (Bits.size bs) bs sz')
         | [ H: _ = _ |- _ ] =>
           apply (f_equal Bits.to_N) in H
         | [ H: _ <> _ |- _ ] =>
           apply Bits.to_N_inj_contra in H
         end.
