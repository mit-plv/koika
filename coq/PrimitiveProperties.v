(*! Equations showing how to implement functions on structures and arrays as bitfuns !*)
Require Import Koika.Primitives.
Import BitFuns.
Require Import Lia.

Ltac min_t :=
  repeat match goal with
         | [ |- context[Min.min ?x ?y] ] =>
           first [rewrite (Min.min_l x y) by min_t | rewrite (Min.min_r x y) by min_t ]
         | _ => lia
         end.

Lemma slice_end :
  forall sz sz' (v : bits (sz + sz')),
    Bits.slice sz sz' v = vect_skipn_plus sz v.
Proof.
  intros.
  apply vect_to_list_inj.
  unfold Bits.slice, vect_skipn_plus, vect_extend_end_firstn, vect_extend_end.
  autorewrite with vect_to_list.
  min_t; rewrite Nat.sub_diag by lia; cbn.
  rewrite app_nil_r.
  rewrite firstn_skipn.
  rewrite firstn_all2 by (rewrite vect_to_list_length; reflexivity).
  reflexivity.
Qed.

Lemma slice_front :
  forall n sz (v: bits (n + sz)) offset width,
    offset + width <= n ->
    Bits.slice offset width v =
    Bits.slice offset width (vect_firstn_plus n v).
Proof.
  intros.
  apply vect_to_list_inj.
  unfold Bits.slice, vect_extend_end_firstn, vect_extend_end, vect_firstn_plus.
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
    Bits.slice_subst sz0 sz bs0 bs = Bits.app bs (fst (Bits.split bs0)).
Proof.
  unfold Bits.split; intros; rewrite vect_split_firstn_skipn; cbn.
  apply vect_to_list_inj.
  unfold Bits.slice_subst, vect_skipn_plus, vect_firstn_plus, vect_extend_end_firstn, vect_extend_end.
  autorewrite with vect_to_list.
  rewrite !firstn_app.
  rewrite firstn_length_le by (rewrite vect_to_list_length; lia).
  rewrite !minus_plus, vect_to_list_length, Nat.sub_diag; cbn.
  rewrite firstn_firstn by lia; min_t.
  rewrite (firstn_all2 (n := sz)) by (rewrite vect_to_list_length; lia).
  rewrite app_nil_r; reflexivity.
Qed.

Lemma slice_subst_front :
  forall sz0 sz width (bs0: bits (sz0 + sz)) (bs: bits width) offset,
    offset + width <= sz0 ->
    Bits.slice_subst offset width bs0 bs =
    Bits.app (vect_skipn_plus sz0 bs0) (Bits.slice_subst offset width (vect_firstn_plus sz0 bs0) bs).
Proof.
  clear.
  intros.
  apply vect_to_list_inj;
    unfold Bits.slice_subst, vect_skipn_plus, vect_firstn_plus, vect_extend_end_firstn, vect_extend_end.
  autorewrite with vect_to_list.
  rewrite !firstn_app.
  rewrite firstn_length_le by (rewrite vect_to_list_length; lia).
  rewrite vect_to_list_length; cbn.
  rewrite !firstn_firstn; repeat min_t.
  rewrite firstn_length_le by (rewrite vect_to_list_length; lia).
  rewrite <- !app_assoc.
  rewrite skipn_firstn, firstn_firstn.
  min_t.
  rewrite !(firstn_all2 (vect_to_list bs)) by (rewrite vect_to_list_length; lia).
  replace (sz0 + sz - offset - width) with (sz0 + sz - (offset + width)) by lia.
  replace (sz0 - offset - width) with (sz0 - (offset + width)) by lia.
  rewrite <- !skipn_firstn.
  rewrite (firstn_all2 (n := sz0 + sz)) by (rewrite vect_to_list_length; lia).
  rewrite <- skipn_app by (rewrite firstn_length, vect_to_list_length; min_t; lia).
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
    Bits.slice (field_offset_right sig idx) (field_sz sig idx) (bits_of_value a) =
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
    Bits.slice (element_offset_right sig idx) (element_sz sig)
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
    Bits.slice_subst (field_offset_right sig idx) (field_sz sig idx) (bits_of_value a1) (bits_of_value a2) =
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
    Bits.slice_subst (element_offset_right sig idx) (element_sz sig)
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
      ((Bits.slice 0 offset a1) ++
       (match le_gt_dec width (sz - offset) with
        | left pr =>
          rew le_plus_minus_r width (sz - offset) pr in
            (a2 ++ Bits.slice (offset + width) (sz - offset - width) a1)
        | right _ => Bits.slice 0 (sz - offset) a2
        end))%vect
  | right _ => a1
  end.

Hint Unfold Bits.slice : vect_to_list.
Hint Unfold Bits.slice_subst : vect_to_list.
Hint Unfold slice_subst_impl : vect_to_list.
Hint Unfold vect_extend_end : vect_to_list.
Hint Unfold vect_extend_end_firstn : vect_to_list.

Ltac vect_to_list_t_step :=
  match goal with
  | _ => progress cbn
  | _ => progress (autounfold with vect_to_list)
  | _ => progress autorewrite with vect_to_list vect_to_list_cleanup
  | [ |- context[match ?x with _ => _ end] ] => destruct x
  | _ => repeat rewrite ?Min.min_l, ?Min.min_r by lia
  end.

Ltac vect_to_list_t :=
  try apply vect_to_list_inj; repeat vect_to_list_t_step.

Lemma slice_subst_impl_correct :
  forall {sz} offset {width} (a1: bits sz) (a2: bits width),
    Bits.slice_subst offset width a1 a2 =
    slice_subst_impl offset a1 a2.
Proof.
  intros; vect_to_list_t.
  - rewrite (firstn_all2 (n := sz - offset)) by (autorewrite with vect_to_list; lia).
    reflexivity.
  - rewrite (skipn_all2 (n := offset + width)) by (autorewrite with vect_to_list; lia).
    autorewrite with vect_to_list_cleanup; reflexivity.
  - rewrite (firstn_all2 (n := sz)) by (autorewrite with vect_to_list; lia).
    reflexivity.
Qed.

Lemma slice_full {sz}:
  forall (bs: bits sz),
    Bits.slice 0 sz bs = bs.
Proof.
  intros; vect_to_list_t.
  rewrite (firstn_all2 (n := sz)) by (autorewrite with vect_to_list; lia);
    reflexivity.
Qed.

Lemma slice_concat_l {sz1 sz2} :
  forall (bs1: bits sz1) (bs2: bits sz2),
    Bits.slice 0 sz1 (bs1 ++ bs2)%vect = bs1.
Proof.
  intros; vect_to_list_t.
  rewrite (firstn_all2 (n := sz1)) by (autorewrite with vect_to_list; lia);
    reflexivity.
Qed.

Lemma slice_concat_r {sz1 sz2} :
  forall (bs1: bits sz1) (bs2: bits sz2),
    Bits.slice sz1 sz2 (bs1 ++ bs2)%vect = bs2.
Proof.
  intros; vect_to_list_t.
  rewrite (skipn_all2 (n := sz1)) by (autorewrite with vect_to_list; lia).
  vect_to_list_t.
  rewrite (firstn_all2 (n := sz2)) by (autorewrite with vect_to_list; lia).
  reflexivity.
Qed.

Section Arithmetic.

  (* The next lemmas simplify 2 * x *)
  Arguments N.mul / !n !m.

  (* This might require another hypothesis to be correct *)
  Lemma sel_spec :
    forall (sz: nat) (bs: bits sz) idx,
      BitFuns.sel bs idx = Ob~(N.testbit (Bits.to_N bs) (Bits.to_N idx)).
  Proof.
    intros.
    unfold BitFuns.sel.
    f_equal.
    unfold Bits.to_index.
    destruct (index_of_nat sz (Bits.to_nat idx)) eqn:Hindex.
    - rewrite <-(N2Nat.id (Bits.to_N idx)).
      fold (Bits.to_nat idx).
      remember (Bits.to_nat idx) as n_idx eqn:Hn_idx.
      clear Hn_idx idx.
      generalize dependent sz.
      induction n_idx as [| idx IH].
      + intros sz bs i Hindex. cbn.
        destruct sz; [destruct i | ].
        inversion Hindex. repeat cleanup_step.
        destruct bs. repeat cleanup_step.
        rewrite N.add_comm. fold (N.b2n vhd).
        rewrite N.testbit_0_r.
        reflexivity.
      + intros sz bs i Hindex. rewrite Nat2N.inj_succ.
        destruct sz; [destruct i | ].
        cbn in Hindex.
        destruct (index_of_nat sz idx) eqn:Hi; repeat cleanup_step.
        destruct bs. repeat cleanup_step.
        rewrite N.add_comm. fold (N.b2n vhd).
        rewrite N.testbit_succ_r.
        apply IH; auto.
    - apply index_of_nat_none_ge in Hindex.
      unfold Bits.to_nat in Hindex.
      assert (Bits.to_N idx >= N.of_nat sz)%N as Hle by lia.
      pose proof (Bits.to_N_bounded bs).
      destruct (Bits.to_N bs); [ reflexivity | ].
      symmetry. apply N.bits_above_log2.
      apply N.ge_le in Hle.
      eapply N.lt_le_trans; [ | exact Hle].
      apply N.log2_lt_pow2; lia.
  Qed.

  Lemma pow2_nz :
    forall n, N.pow 2 n <> 0%N.
  Proof. intros; apply N.pow_nonzero; lia. Qed.
  Hint Resolve pow2_nz: core.

  Lemma to_N_vect_unsnoc :
    forall sz (x: bits (S sz)),
      (Bits.to_N (snd (vect_unsnoc x)) = Bits.to_N x mod (2 ^ N.of_nat sz))%N.
  Proof.
    intros.
    induction sz.
    - simpl.
      destruct x. destruct vtl. cbn.
      destruct_match; reflexivity.
    - pose proof pow2_nz (N.of_nat sz).
      destruct x.
      rewrite Nat2N.inj_succ, N.pow_succ_r'. cbn.
      specialize (IHsz vtl).
      destruct (vect_unsnoc vtl) eqn:H_unsnoc_vtl.
      cbn in *. rewrite IHsz.
      rewrite N.add_mod; [ | destruct sz; discriminate ].
      rewrite (N.mod_small (if vhd then 1 else 0)).
      + rewrite (N.mod_small _ (2 * 2 ^ N.of_nat sz)).
        * f_equal.
          rewrite N.mul_mod_distr_l by lia;
            reflexivity.
        * destruct vhd.
          -- rewrite N.mul_mod_distr_l by lia.
             eauto using N.mul_2_mono_l, N.mod_lt.
          -- apply N.mod_lt; lia.
      + destruct vhd; lia.
  Qed.

  Lemma to_N_lsl1 :
    forall sz (x: bits sz),
      (Bits.to_N (Bits.lsl1 x) =
       (Bits.to_N x * 2) mod (2 ^ N.of_nat sz))%N.
  Proof.
    destruct sz.
    - intros.
      destruct x.
      reflexivity.
    - intros.
      pose proof pow2_nz (N.of_nat sz).
      rewrite Nat2N.inj_succ, N.pow_succ_r'.
      cbn. rewrite (N.mul_comm _ 2).
      rewrite N.mul_mod_distr_l by lia.
      f_equal.
      apply to_N_vect_unsnoc.
  Qed.

  Lemma to_N_dotimes_lsl :
    forall sz n (x: bits sz),
      (Bits.to_N (vect_dotimes Bits.lsl1 n x) = (Bits.to_N x * 2 ^ N.of_nat n) mod 2 ^ N.of_nat sz)%N.
  Proof.
    induction n as [| n IHn]; intros.
    - cbn.
      rewrite N.mul_1_r, N.mod_small by apply Bits.to_N_bounded.
      reflexivity.
    - rewrite Nat2N.inj_succ, N.pow_succ_r'.
      cbn.
      rewrite IHn, to_N_lsl1.
      rewrite N.mul_mod_idemp_l by (pose proof pow2_nz (N.of_nat sz); lia).
      f_equal. ring.
  Qed.

  Lemma to_N_lsl :
    forall sz1 sz2 (x: bits sz1) (y: bits sz2),
      (Bits.to_N (BitFuns.lsl x y) =
       (Bits.to_N x * (2 ^ (Bits.to_N y))) mod (2 ^ N.of_nat sz1))%N.
  Proof.
    intros. unfold lsl, Bits.lsl.
    rewrite <-(N2Nat.id (Bits.to_N y)).
    apply to_N_dotimes_lsl.
  Qed.

  Lemma to_N_extend_end_false :
    forall sz (x: bits sz) sz', Bits.to_N (Bits.extend_end x sz' false) = Bits.to_N x.
  Proof.
    intros.
    unfold Bits.extend_end.
    rewrite Bits.to_N_rew, Bits.to_N_app, Bits.to_N_zeroes, N.mul_0_l, N.add_0_l.
    reflexivity.
  Qed.
End Arithmetic.
