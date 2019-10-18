Require Import Coq.Lists.List.
Require Import SGA.Primitives.

Import BitFuns.
Import ListNotations.

Ltac min_t :=
  repeat match goal with
         | [ |- context[Min.min ?x ?y] ] =>
           first [rewrite (Min.min_l x y) by min_t | rewrite (Min.min_r x y) by min_t ]
         | _ => omega
         end.

Lemma part_end :
  forall sz sz' (v : bits (sz + sz')),
    part sz sz' v = vect_skipn_plus sz v.
Proof.
  intros.
  apply vect_to_list_inj.
  unfold part, vect_skipn_plus, vect_extend_end_firstn, vect_extend_end.
  autorewrite with vect_to_list.
  min_t; rewrite Nat.sub_diag by omega; cbn.
  rewrite app_nil_r.
  rewrite firstn_skipn.
  rewrite firstn_all2 by (rewrite vect_to_list_length; reflexivity).
  reflexivity.
Qed.

Lemma part_front :
  forall n sz (v: bits (n + sz)) offset width,
    offset + width <= n ->
    part offset width v =
    part offset width (vect_firstn_plus n v).
Proof.
  intros.
  apply vect_to_list_inj.
  unfold part, vect_extend_end_firstn, vect_extend_end, vect_firstn_plus.
  autorewrite with vect_to_list.
  rewrite skipn_firstn, firstn_firstn.
  min_t; reflexivity.
Qed.

Lemma part_correct_le :
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

Lemma part_subst_end :
  forall sz0 sz (bs0: bits (sz0 + sz)) (bs: bits sz),
    part_subst sz0 sz bs0 bs = Bits.app bs (fst (Bits.split bs0)).
Proof.
  unfold Bits.split; intros; rewrite vect_split_firstn_skipn; cbn.
  apply vect_to_list_inj.
  unfold part_subst, vect_skipn_plus, vect_firstn_plus, vect_extend_end_firstn, vect_extend_end.
  autorewrite with vect_to_list.
  rewrite !firstn_app.
  rewrite firstn_length_le by (rewrite vect_to_list_length; omega).
  rewrite !minus_plus, vect_to_list_length, Nat.sub_diag; cbn.
  rewrite firstn_firstn by omega; min_t.
  rewrite (firstn_all2 (n := sz)) by (rewrite vect_to_list_length; omega).
  rewrite app_nil_r; reflexivity.
Qed.

Lemma part_subst_front :
  forall sz0 sz width (bs0: bits (sz0 + sz)) (bs: bits width) offset,
    offset + width <= sz0 ->
    part_subst offset width bs0 bs =
    Bits.app (vect_skipn_plus sz0 bs0) (part_subst offset width (vect_firstn_plus sz0 bs0) bs).
Proof.
  clear.
  intros.
  apply vect_to_list_inj;
    unfold part_subst, vect_skipn_plus, vect_firstn_plus, vect_extend_end_firstn, vect_extend_end.
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
