(*! Circuits | Local optimization of circuits !*)
Require Export Koika.Common Koika.Environments Koika.CircuitSemantics.

Import PrimTyped CircuitSignatures.

Section CircuitOptimizer.
  Context {rule_name_t reg_t ext_fn_t: Type}.

  Context {CR: reg_t -> nat}.
  Context {CSigma: ext_fn_t -> CExternalSignature}.

  Context {rwdata: nat -> Type}.

  Notation Circuit := circuit.
  Notation circuit := (circuit (rule_name_t := rule_name_t) (rwdata := rwdata) CR CSigma).

  Context (csigma: forall f, CSig_denote (CSigma f)).

  Record local_circuit_optimizer :=
    { lco_fn :> forall {sz}, circuit sz -> circuit sz;
      lco_proof: forall {REnv: Env reg_t} (cr: REnv.(env_t) (fun idx => bits (CR idx))) {sz} (c: circuit sz),
          interp_circuit cr csigma (lco_fn c) =
          interp_circuit cr csigma c }.

  Definition lco_opt_compose
             (o1 o2: forall {sz}, circuit sz -> circuit sz) sz (c: circuit sz) :=
    o2 (o1 c).

  Definition lco_compose (l1 l2: local_circuit_optimizer) :=
    {| lco_fn := @lco_opt_compose (l1.(@lco_fn)) (l2.(@lco_fn));
       lco_proof := ltac:(abstract (intros; unfold lco_opt_compose;
                                     cbn; rewrite !lco_proof; reflexivity)) |}.

  Fixpoint unannot {sz} (c: circuit sz) : circuit sz :=
    match c with
    | CAnnot annot c => unannot c
    | c => c
    end.

  Lemma unannot_sound {REnv cr sz} :
    forall (c: circuit sz),
      interp_circuit (REnv := REnv) cr csigma (unannot c) =
      interp_circuit (REnv := REnv) cr csigma c.
  Proof. induction c; eauto. Qed.

  Section MuxElim.
    (** This pass performs the following Mux simplifications:
          Mux(_, c1, c1) → c1
          Mux(k, Mux(k', c2, c12), c2) → Mux(k && ~k', c12, c2 )
          Mux(k, Mux(k', c11, c2), c2) → Mux(k &&  k', c11, c2 )
          Mux(k, c1, Mux(k', c1, c22)) → Mux(k ||  k', c1 , c22)
          Mux(k, c1, Mux(k', c21, c1)) → Mux(k || ~k', c1 , c21)
          Mux(k, Mux(k, c11, c12), c2) → Mux(k, c11, c2)
          Mux(k, c1, Mux(k, c21, c22)) → Mux(k, c1, c22)
        [equivb] needs to be sound, but does not need to be complete
        (comparing two circuits can be very costly). **)
    Context (equivb: forall {sz}, circuit sz -> circuit sz -> bool).

    Context (equivb_sound: forall {REnv: Env reg_t} (cr: REnv.(env_t) (fun idx => bits (CR idx)))
                          {sz} (c1 c2: circuit sz),
                equivb _ c1 c2 = true ->
                interp_circuit cr csigma c1 = interp_circuit cr csigma c2).

    Context {REnv: Env reg_t}.
    Context (cr: REnv.(env_t) (fun idx => bits (CR idx))).

    Notation equivb_unannot c1 c2 := (equivb _ (unannot c1) (unannot c2)).

    Lemma equivb_unannot_sound :
      forall {sz} (c1 c2: circuit sz),
        equivb_unannot c1 c2 = true ->
        interp_circuit cr csigma c1 = interp_circuit cr csigma c2.
    Proof.
      intros * H%(equivb_sound _ cr).
      rewrite <- (unannot_sound c1), <- (unannot_sound c2); assumption.
    Qed.

    Definition opt_muxelim_identical {sz} (c: circuit sz): circuit sz :=
      match c in Circuit _ _ sz return circuit sz -> circuit sz with
      | CMux k c1 c2 =>
        fun c0 => if equivb_unannot c1 c2 then c1 else c0
      | _  => fun c0 => c0
      end c.

    Lemma opt_muxelim_identical_sound :
      forall {sz} (c: circuit sz),
        interp_circuit cr csigma (opt_muxelim_identical c) = interp_circuit cr csigma c.
    Proof.
      destruct c; simpl; try reflexivity.
      destruct equivb eqn:Hequivb.
      - destruct Bits.single; auto using equivb_unannot_sound.
      - reflexivity.
    Qed.

    Definition opt_muxelim_redundant_l {sz} (c: circuit sz): circuit sz :=
      match c in Circuit _ _ sz return circuit sz -> circuit sz with
      | CMux k c1 c2 =>
        fun c =>
          match unannot c1 in Circuit _ _ sz return circuit sz -> circuit sz -> circuit sz with
          | CMux k' c11 c12 =>
            fun c c2 =>
              if equivb_unannot k k' then
                (* Mux(k, Mux(k, c11, c12), c2) *)
                (CAnnot "simplified_mux" (CMux k c11 c2))
              else c
          | _ =>
            fun c c2 => c
          end c c2
      | _ => fun c => c
      end c.

    Definition opt_muxelim_redundant_r {sz} (c: circuit sz): circuit sz :=
      match c in Circuit _ _ sz return circuit sz -> circuit sz with
      | CMux k c1 c2 =>
        fun c =>
          match unannot c2 in Circuit _ _ sz return circuit sz -> circuit sz -> circuit sz with
          | CMux k' c21 c22 =>
            fun c c1 =>
              if equivb_unannot k k' then
                (* Mux(k, c1, Mux(k, c21, c22)) *)
                (CAnnot "simplified_mux" (CMux k c1 c22))
              else c
          | _ =>
            fun c c1 => c
          end c c1
      | _ => fun c => c
      end c.

    Definition opt_muxelim_nested_l {sz} (c: circuit sz): circuit sz :=
      match c in Circuit _ _ sz return circuit sz -> circuit sz with
      | CMux k c1 c2 =>
        fun c =>
          match unannot c1 in Circuit _ _ sz return circuit sz -> circuit sz -> circuit sz with
          | CMux k' c11 c12 =>
            fun c c2 =>
              if equivb_unannot c11 c2 then
                (* Mux(k, Mux(k', c2, c12), c2) *)
                CMux (CAnnot "nested_mux" (CAnd k (CNot k'))) c12 c2
              else if equivb_unannot c12 c2 then
                     (* Mux(k, Mux(k', c11, c2), c2) *)
                     CMux (CAnnot "nested_mux" (CAnd k k')) c11 c2
                   else c
          | _ =>
            fun c c2 => c
          end c c2
      | _ => fun c => c
      end c.

    Definition opt_muxelim_nested_r {sz} (c: circuit sz): circuit sz :=
      match c in Circuit _ _ sz return circuit sz -> circuit sz with
      | CMux k c1 c2 =>
        fun c =>
          match unannot c2 in Circuit _ _ sz return circuit sz -> circuit sz -> circuit sz with
          | CMux k' c21 c22 =>
            fun c c1 =>
              if equivb_unannot c1 c21 then
                (* Mux(k, c1, Mux(k', c1, c22)) *)
                CMux (CAnnot "nested_mux" (COr k k')) c1 c22
              else if equivb_unannot c1 c22 then
                     (* Mux(k, c1, Mux(k', c21, c1)) *)
                     CMux (CAnnot "nested_mux" (COr k (CNot k'))) c1 c21
                   else c
          | _ =>
            fun c c1 => c
          end c c1
      | _ => fun c => c
      end c.

    Ltac mux_elim_nested_step :=
      match goal with
      | _ => reflexivity
      | _ => congruence
      | _ => progress (intros || simpl)
      | [  |- context[match ?c with _ => _ end] ] =>
        match type of c with circuit _ => destruct c eqn:? end
      | [  |- context[if equivb_unannot ?c ?c' then _ else _] ] =>
        destruct (equivb_unannot c c') eqn:?
      | [ Heq: unannot ?c = _ |- context[interp_circuit _ _ ?c] ] =>
        rewrite <- (unannot_sound c), Heq
      | [  |- context[Bits.single ?c] ] =>
        destruct c as ([ | ] & []) eqn:?
      | [ H: equivb_unannot ?c ?c' = true |- _ ] => apply equivb_unannot_sound in H
      end.

    Lemma opt_muxelim_redundant_l_sound :
      forall {sz} (c: circuit sz),
        interp_circuit cr csigma (opt_muxelim_redundant_l c) = interp_circuit cr csigma c.
    Proof.
      unfold opt_muxelim_redundant_l; repeat mux_elim_nested_step.
    Qed.

    Lemma opt_muxelim_redundant_r_sound :
      forall {sz} (c: circuit sz),
        interp_circuit cr csigma (opt_muxelim_redundant_r c) = interp_circuit cr csigma c.
    Proof.
      unfold opt_muxelim_redundant_r; repeat mux_elim_nested_step.
    Qed.

    Lemma opt_muxelim_nested_l_sound :
      forall {sz} (c: circuit sz),
        interp_circuit cr csigma (opt_muxelim_nested_l c) = interp_circuit cr csigma c.
    Proof.
      unfold opt_muxelim_nested_l; repeat mux_elim_nested_step.
    Qed.

    Lemma opt_muxelim_nested_r_sound :
      forall {sz} (c: circuit sz),
        interp_circuit cr csigma (opt_muxelim_nested_r c) = interp_circuit cr csigma c.
    Proof.
      unfold opt_muxelim_nested_r; repeat mux_elim_nested_step.
    Qed.

    Definition opt_muxelim {sz} :=
      @lco_opt_compose
        (@opt_muxelim_identical)
        (lco_opt_compose
           (lco_opt_compose (@opt_muxelim_redundant_l) (@opt_muxelim_redundant_r))
           (lco_opt_compose (@opt_muxelim_nested_l) (@opt_muxelim_nested_r)))
        sz.

    Lemma opt_muxelim_sound :
      forall {sz} (c: circuit sz),
        interp_circuit cr csigma (opt_muxelim c) = interp_circuit cr csigma c.
    Proof.
      intros; unfold opt_muxelim, lco_opt_compose.
      rewrite
        opt_muxelim_nested_r_sound, opt_muxelim_nested_l_sound,
      opt_muxelim_redundant_r_sound, opt_muxelim_redundant_l_sound,
      opt_muxelim_identical_sound;
        reflexivity.
    Qed.
  End MuxElim.

  Section ConstProp.
    Context {REnv: Env reg_t}.
    Context (cr: REnv.(env_t) (fun idx => bits (CR idx))).

    Definition asconst {sz} (c: circuit sz) : option (list bool) :=
      match unannot c with
      | CConst cst => Some (vect_to_list cst)
      | c => None
      end.

    Notation ltrue := (cons true nil).
    Notation lfalse := (cons false nil).

    Instance EqDec_ListBool : EqDec (list bool) := _.

    (** This pass performs the following simplifications:

        Not(1) => 0
        Not(0) => 1
        And(_, 0) | And(0, _) => 0
        And(c, 1) | And(1, c) => c
        Or(_, 1) | Or(1, _) => 1
        Or(c, 0) | Or(0, c) => c
        Mux(0, x, y) => x
        Mux(1, x, y) => y
        Mux(c, x, x) => x *)

    Definition opt_constprop' {sz} (c: circuit sz): circuit sz :=
      match c in Circuit _ _ sz return circuit sz with
      | (CNot c) as c0 =>
        match asconst c with
        | Some ltrue => CConst Ob~0
        | Some lfalse => CConst Ob~1
        | _ => c0
        end
      | (CAnd c1 c2) as c0 =>
        match asconst c1, asconst c2 with
        | Some lfalse, _ | _, Some lfalse => CConst Ob~0
        | _, Some ltrue => c1
        | Some ltrue, _ => c2
        | _, _ => c0
        end
      | (COr c1 c2) as c0 =>
        match asconst c1, asconst c2 with
        | Some ltrue, _ | _, Some ltrue => CConst Ob~1
        | _, Some lfalse => c1
        | Some lfalse, _ => c2
        | _, _ => c0
        end
      | (CMux select c1 c2) as c0 =>
        match asconst select with
        | Some ltrue => c1
        | Some lfalse => c2
        | _ => match asconst c1, asconst c2 with
              | Some bs1, Some bs2 =>
                if eq_dec bs1 bs2 then c1
                else c0
              | _, _ => c0
              end
        end
      | c => c
      end.

    (** This pass performs the following simplification:

        Mux(c, 1, 0) => c
        Mux(c, 0, 1) => Not(c)
        Mux(c, 1, x) => Or(c, x)
        Mux(c, x, 0) => And(c, x) *)

    Definition opt_mux_bit1 {sz} (c: circuit sz): circuit sz :=
      match c in Circuit _ _ sz return circuit sz -> circuit sz with
      | @CMux _ _ _ _ _ _ n s c1 c2 =>
        fun c0 => match n return Circuit _ _ n -> Circuit _ _ n -> Circuit _ _ n -> Circuit _ _ n with
               | 1 => fun c0 c1 c2 =>
                       let annot := CAnnot "optimized_mux" in
                       match asconst c1, asconst c2 with
                       | Some ltrue, Some lfalse => annot s
                       | Some ltrue, _ => annot (COr s c2)
                       | Some lfalse, Some ltrue => annot (CNot s)
                       (* FIXME: these two increase the circuit size *)
                       (* | Some lfalse, _ => annot (CAnd (CNot s) c2) *)
                       (* | _, Some ltrue => annot (COr (CNot s) c1) *)
                       | _, Some lfalse => annot (CAnd s c1)
                       | _, _ => c0
                       end
               | _ => fun c0 c1 c2 => c0
               end c0 c1 c2
      | _ => fun c0 => c0
      end c.

    Definition opt_constprop {sz} (c: circuit sz): circuit sz :=
      match sz as n return (circuit n -> circuit n) with
      | 0 => fun c => CConst Bits.nil
      | _ => fun c => opt_mux_bit1 (opt_constprop' c)
      end c.

    Arguments opt_constprop sz !c : assert.

    Lemma asconst_Some :
      forall {sz} (c: circuit sz) bs,
        asconst c = Some bs ->
        vect_to_list (interp_circuit cr csigma c) = bs.
    Proof.
      induction c; intros b Heq;
        repeat match goal with
               | _ => progress cbn in *
               | _ => discriminate
               | _ => reflexivity
               | [ H: Some _ = Some _ |- _ ] => inversion H; subst; clear H
               | [ sz: nat |- _ ] => destruct sz; try (tauto || discriminate); []
               end.
      apply IHc; eassumption.
    Qed.

    Arguments EqDec_ListBool: simpl never.
    Lemma opt_constprop'_sound :
      forall {sz} (c: circuit sz),
        interp_circuit cr csigma (opt_constprop' c) = interp_circuit cr csigma c.
    Proof.
      induction c; cbn.
      Ltac t := match goal with
               | _ => reflexivity
               | _ => progress bool_simpl
               | _ => progress cbn in *
               | [  |- context[match asconst ?c with _ => _ end] ] =>
                 destruct (asconst c) as [ | ] eqn:?
               | [ H: asconst _ = Some _ |- _ ] => apply asconst_Some in H
               | [  |- _ = ?y ] =>
                 match y with
                 | context[Bits.single (interp_circuit cr csigma ?c)] =>
                   destruct (interp_circuit cr csigma c) as [ ? [] ] eqn:? ;
                   cbn in *; subst
                 end
               | [ H: ?x = _ |- context[?x] ] => rewrite H
               | [  |- context[if ?b then _ else _] ] => destruct b eqn:?
               | _ => eauto using vect_to_list_inj
               end.
      all: repeat t.
    Qed.

    Lemma opt_mux_bit1_sound :
      forall {sz} (c: circuit sz),
        interp_circuit cr csigma (opt_mux_bit1 c) = interp_circuit cr csigma c.
    Proof.
      destruct c; simpl; try reflexivity; [].
      destruct sz as [ | [ | ] ]; simpl; try reflexivity; [].
      destruct (asconst c2) as [ [ | [ | ] [ | ] ] | ] eqn:Hc2; try reflexivity;
        destruct (asconst c3) as [ [ | [ | ] [ | ] ] | ] eqn:Hc3; try reflexivity.
      Ltac tmux :=
        match goal with
        | _ => progress (cbn in * || subst)
        | [ H: _ :: _ = _ :: _ |- _ ] => inversion H; subst; clear H
        | [ v: vect_nil_t _ |- _ ] => destruct v
        | [ H: asconst _ = Some _ |- _ ] => apply asconst_Some in H
        | [  |- context[interp_circuit _ _ ?c] ] => destruct (interp_circuit _ _ c) eqn:?
        | [  |- context[if ?x then _ else _] ] => destruct x
        | _ => reflexivity || discriminate
        end.
      all: solve [repeat tmux].
    Qed.

    Lemma opt_constprop_sound :
      forall {sz} (c: circuit sz),
        interp_circuit cr csigma (opt_constprop c) = interp_circuit cr csigma c.
    Proof.
      unfold opt_constprop; destruct sz.
      - cbn; intros.
        destruct interp_circuit; reflexivity.
      - intros; rewrite opt_mux_bit1_sound, opt_constprop'_sound; reflexivity.
    Qed.
  End ConstProp.
End CircuitOptimizer.

Arguments unannot {rule_name_t reg_t ext_fn_t CR CSigma rwdata} [sz] c : assert.
Arguments unannot_sound {rule_name_t reg_t ext_fn_t CR CSigma rwdata} csigma [REnv] cr [sz] c : assert.

Arguments opt_constprop {rule_name_t reg_t ext_fn_t CR CSigma rwdata} [sz] c : assert.
Arguments opt_constprop_sound {rule_name_t reg_t ext_fn_t CR CSigma rwdata} csigma [REnv] cr [sz] c : assert.

Arguments opt_muxelim {rule_name_t reg_t ext_fn_t CR CSigma rwdata} equivb [sz] c : assert.
Arguments opt_muxelim_sound {rule_name_t reg_t ext_fn_t CR CSigma rwdata} csigma {equivb} equivb_sound [REnv] cr [sz] c : assert.

Arguments lco_fn {rule_name_t reg_t ext_fn_t CR CSigma rwdata csigma} l [sz] c : assert.
Arguments lco_proof {rule_name_t reg_t ext_fn_t CR CSigma rwdata csigma} l {REnv} cr [sz] c : assert.
Arguments lco_compose {rule_name_t reg_t ext_fn_t CR CSigma rwdata csigma} l1 l2 : assert.

Section LCO.
  Context {rule_name_t reg_t ext_fn_t: Type}.

  Context {CR: reg_t -> nat}.
  Context {CSigma: ext_fn_t -> CExternalSignature}.

  Context {rwdata: nat -> Type}.
  Context (csigma: forall f, CSig_denote (CSigma f)).

  Definition lco_unannot : @local_circuit_optimizer rule_name_t _ _ CR _ rwdata csigma :=
    {| lco_fn := unannot;
       lco_proof := unannot_sound csigma |}.

  Definition lco_constprop: @local_circuit_optimizer rule_name_t _ _ CR _ rwdata csigma :=
    {| lco_fn := opt_constprop;
       lco_proof := opt_constprop_sound csigma |}.

  Definition lco_muxelim equivb equivb_sound
    : @local_circuit_optimizer rule_name_t _ _ CR _ rwdata csigma :=
    {| lco_fn := opt_muxelim equivb;
       lco_proof := opt_muxelim_sound csigma equivb_sound |}.
End LCO.

Arguments lco_unannot {rule_name_t reg_t ext_fn_t CR CSigma rwdata csigma} : assert.
Arguments lco_constprop {rule_name_t reg_t ext_fn_t CR CSigma rwdata csigma} : assert.
Arguments lco_muxelim {rule_name_t reg_t ext_fn_t CR CSigma rwdata csigma} {equivb} equivb_sound : assert.
