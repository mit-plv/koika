(*! Tactics for proofs about bits !*)

Require Import Lia.
Require Export Koika.EqDec Koika.Vect Koika.Primitives Koika.PrimitiveProperties.
Import BitFuns.

(* This definition is useful for the next tactics *)
Definition bits_get_size {sz} (bs: bits sz) :=
  sz.

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
           setoid_rewrite (to_N_extend_end_false (bits_get_size bs) bs sz') in H
         | [ |- context[Bits.to_N (Bits.extend_end ?bs ?sz' false)] ] =>
           setoid_rewrite (to_N_extend_end_false (bits_get_size bs) bs sz')
         | [ H: _ = _ |- _ ] =>
           apply (f_equal Bits.to_N) in H
         | [ H: _ <> _ |- _ ] =>
           apply Bits.to_N_inj_contra in H
         end.

Ltac remember_bits_to_N :=
  repeat match goal with
         | [ |- context[Bits.to_N ?bs] ] =>
           remember_once (Bits.to_N bs)
         | [ H: context[Bits.to_N ?bs] |- _ ] =>
           remember_once (Bits.to_N bs)
         end.

Ltac pose_bits_bound_proofs :=
  repeat match goal with
         | [ H: context[Bits.to_N ?bs] |- _ ] =>
           let sz := eval hnf in (bits_get_size bs) in
               pose_once Bits.to_N_bounded sz bs
         | [ |- context[Bits.to_N ?bs] ] =>
           let sz := eval hnf in (bits_get_size bs) in
               pose_once Bits.to_N_bounded sz bs
         end.

(* Lia with some support for the Bits.to_N function *)
Ltac lia_bits :=
  Bits_to_N_t; cbn in *; pose_bits_bound_proofs; remember_bits_to_N; cbn in *; lia.
