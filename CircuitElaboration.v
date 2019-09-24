Require Import Coq.Lists.List.
Require Import SGA.Circuits SGA.CircuitProperties SGA.Primitives SGA.Interop.

Import ListNotations.

Ltac min_t :=
  repeat match goal with
         | [ |- context[Min.min ?x ?y] ] =>
           first [rewrite (Min.min_l x y) by min_t | rewrite (Min.min_r x y) by min_t ]
         | _ => omega
         end.

Section Elaboration.
  Context {name_t var_t reg_t custom_fn_t: Type}.

  Context {R: reg_t -> type}.
  Definition cR := (circuit_R R).

  Context {Sigma: custom_fn_t -> ExternalSignature}.
  Notation cSigma := (circuit_Sigma (interop_Sigma Sigma)).

  Context (custom_sigma: forall f, ExternalSignature_denote (Sigma f)).
  Notation csigma := (circuit_sigma (interop_sigma custom_sigma)).

  Definition elaborate_externals_1 {n} (c: circuit cR cSigma n) : circuit cR cSigma n.
  Proof.
    pose proof c as c0.
    destruct c; [ exact c0.. | | exact c0 ].
    destruct idx; [ | exact c0 ].
    destruct fn; [ | exact c0 | ].
    - (* Conv *)
      destruct op; cbn in *.
      + (* Eq *) exact (CExternal (PrimFn (BitsFn (EqBits tau))) c1 c2).
      + (* Init *) exact (CConst (Bits.zeroes _)).
      + (* Pack *) exact c1.
      + (* Unpack *) exact c1.
    - (* Struct *)
      destruct op; cbn in *.
      + (* GetField *)
        exact (let fn := Part (struct_sz sig) (field_offset_right sig f) (field_sz sig f) in
               CExternal (PrimFn (BitsFn fn)) c1 c2).
      + (* SubstField *)
        exact (let fn := PartSubst (struct_sz sig) (field_offset_right sig f) (field_sz sig f) in
               CExternal (PrimFn (BitsFn fn)) c1 c2).
  Defined.

  Context {REnv: Env reg_t}.

  Context (r: REnv.(env_t) R).
  Notation cr := (circuit_r r).
  Context (rc: REnv.(env_t) (fun reg => circuit cR cSigma (cR reg))).
  Context (sigma: forall f, ExternalSignature_denote (Sigma f)).

  Lemma prim_part_end :
    forall sz sz' (v : bits (sz + sz')),
      prim_part v sz sz' = vect_skipn_plus sz v.
  Proof.
    intros.
    apply vect_to_list_inj.
    unfold prim_part, vect_skipn_plus, vect_extend_firstn, vect_extend.
    autorewrite with vect_to_list.
    min_t; rewrite Nat.sub_diag by omega; cbn.
    rewrite app_nil_r.
    rewrite firstn_skipn.
    rewrite firstn_all2 by (rewrite vect_to_list_length; reflexivity).
    reflexivity.
  Qed.

  Lemma prim_part_front :
    forall n sz (v: bits (n + sz)) offset width,
      offset + width <= n ->
      prim_part v offset width =
      prim_part (vect_firstn_plus n v) offset width.
  Proof.
    intros.
    apply vect_to_list_inj.
    unfold prim_part, vect_extend_firstn, vect_extend, vect_firstn_plus.
    autorewrite with vect_to_list.
    rewrite skipn_firstn, firstn_firstn.
    min_t; reflexivity.
  Qed.

  Lemma prim_part_correct_le :
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

  Lemma prim_part_subst_end :
    forall sz0 sz (bs0: bits (sz0 + sz)) (bs: bits sz),
      prim_part_subst bs0 sz0 sz bs = Bits.app (fst (Bits.split bs0)) bs.
  Proof.
    unfold Bits.split; intros; rewrite vect_split_firstn_skipn; cbn.
    apply vect_to_list_inj.
    unfold prim_part_subst, vect_skipn_plus, vect_firstn_plus, vect_extend_firstn, vect_extend.
    autorewrite with vect_to_list.
    rewrite !firstn_app.
    rewrite firstn_length_le by (rewrite vect_to_list_length; omega).
    rewrite !minus_plus, vect_to_list_length, Nat.sub_diag; cbn.
    rewrite firstn_firstn by omega; min_t.
    rewrite (firstn_all2 (n := sz)) by (rewrite vect_to_list_length; omega).
    rewrite app_nil_r; reflexivity.
  Qed.

  Lemma prim_part_subst_front :
    forall sz0 sz width (bs0: bits (sz0 + sz)) (bs: bits width) offset,
      offset + width <= sz0 ->
      prim_part_subst bs0 offset width bs =
      Bits.app (prim_part_subst (vect_firstn_plus sz0 bs0) offset width bs) (vect_skipn_plus sz0 bs0).
  Proof.
    clear.
    intros.
    apply vect_to_list_inj;
      unfold prim_part_subst, vect_skipn_plus, vect_firstn_plus, vect_extend_firstn, vect_extend.
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

  Theorem elaborate_externals_1_correct :
    forall {sz} (c: circuit cR cSigma sz),
    interp_circuit cr csigma (elaborate_externals_1 c) = interp_circuit cr csigma c.
  Proof.
    destruct c; try reflexivity.
    destruct idx; try reflexivity.
    destruct fn; try reflexivity.
    - (* Conv *)
      destruct op; cbn in *;
        try (rewrite bits_of_value_of_bits; reflexivity).
      + (* Eq *)
        change (_ tau ?x ?y) with (eq_dec x y).
        destruct (eq_dec (interp_circuit _ _ _) _) as [ -> | Hneq ];
          destruct (eq_dec (value_of_bits _) _) as [ Heq | ? ]; try congruence.
        apply (f_equal bits_of_value) in Heq; rewrite !bits_of_value_of_bits in Heq.
        congruence.
    - (* StructFn *)
      destruct op; cbn in *.
      + (* GetField *)
        generalize (interp_circuit cr csigma c1); clear c1.
        repeat unfold struct_index, field_type, field_sz in *;
          induction (struct_fields sig) as [ | (nm & tau) l ]; cbn.
        * destruct f.
        * destruct f; cbn in *; intros.
          -- rewrite bits_of_value_of_bits.
             unfold Bits.split; rewrite vect_split_firstn_skipn; cbn.
             apply prim_part_end.
          -- rewrite <- IHl.
             unfold Bits.split; rewrite vect_split_firstn_skipn; cbn.
             apply prim_part_front.
             apply prim_part_correct_le.
      + set (interp_circuit _ _ _) as bs; clearbody bs; revert bs.
        set (interp_circuit _ _ _) as bs; clearbody bs; revert bs.
        clear c1 c2.
        repeat unfold struct_index, field_type, field_sz in *;
          induction (struct_fields sig) as [ | (nm & tau) l ]; cbn.
        * destruct f.
        * destruct f eqn:?; cbn in *; intros.
          -- rewrite bits_of_value_of_bits.
             setoid_rewrite (bits_of_value_of_bits (struct_t {| struct_name := ""; struct_fields := _ |})).
             apply prim_part_subst_end.
          -- rewrite <- IHl.
             unfold Bits.split; rewrite vect_split_firstn_skipn; cbn.
             rewrite bits_of_value_of_bits.
             apply prim_part_subst_front.
             apply prim_part_correct_le.
  Qed.

  Definition external_elaboration_lco :=
    {| lco_fn := @elaborate_externals_1;
       lco_proof := @elaborate_externals_1_correct |}.
End Elaboration.

Arguments elaborate_externals_1 {_ _ _ _} [_] _.
Arguments external_elaboration_lco {_ _ _ _ _ _ _}.

Section Interop.
  Context {name_t var_t reg_t custom_fn_t: Type}.

  Definition interop_opt
             {R : reg_t -> type}
             {Sigma : custom_fn_t -> ExternalSignature}
    : forall sz : nat, circuit (@cR _ R) (circuit_Sigma (interop_Sigma Sigma)) sz ->
                circuit (@cR _ R) (circuit_Sigma (interop_Sigma Sigma)) sz :=
    (lco_opt_compose simplify_bool_1 elaborate_externals_1).

  Definition compile_sga_package
             (s: @sga_package_t name_t var_t reg_t custom_fn_t) : circuit_package_t :=
    let FT := s.(sga_reg_finite) in
    {| cp_pkg := s;
       cp_reg_Env := ContextEnv;
       cp_circuit :=
         let R := s.(sga_reg_types) in
         let Sigma := interop_Sigma s.(sga_custom_fn_types) in
         let r := ContextEnv.(create) (readRegisters R Sigma) in
         compile_scheduler (REnv := ContextEnv) interop_opt
                           r s.(sga_rules) s.(sga_scheduler) |}.
End Interop.
