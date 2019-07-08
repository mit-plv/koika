Require Import SGA.Common SGA.Syntax SGA.Environments SGA.Types SGA.Typechecking.

Section TypeInference.
  Context {TVar TFn: Type}.
  Context {GammaEnv: Env TVar type}.
  Context {RegEnv: Env nat nat}.
  Context (SigmaEnv: Env TFn ExternalSignature).

  Context (Sigma: SigmaEnv.(env_t)).
  Context (V: RegEnv.(env_t)).

  Open Scope bool_scope.

  Definition type_le_dec tau1 tau2:
    { type_le tau1 tau2 } + { ~ type_le tau1 tau2 }.
  Proof.
    destruct tau1, tau2; try destruct (PeanoNat.Nat.eq_dec n n0);
      cbn; repeat match goal with
                  | [ H: bit_t _ = bit_t _ |- _ ] => inversion H; subst; clear H
                  | _ => discriminate
                  | _ => solve [eauto with types]
                  | _ => right; inversion 1
                  end.
  Defined.

  Arguments type_le_dec: simpl never.

  Fixpoint infer_maxtype
           (Gamma: GammaEnv.(env_t))
           (r: rule TVar TFn)
    : option type :=
    match r with
    | Bind var expr body =>
      opt_bind (infer_maxtype Gamma expr) (fun etau =>
      infer_maxtype (putenv Gamma var etau) body)
    | Var var => getenv Gamma var
    | Skip => Some unit_t
    | Const cst => Some (bit_t (List.length cst))
    | If cond tbranch fbranch =>
      opt_bind (infer_maxtype Gamma cond) (fun ctau =>
      if type_le_dec (bit_t 1) ctau then
        opt_bind (infer_maxtype Gamma tbranch) (fun ttau =>
        opt_bind (infer_maxtype Gamma fbranch) (fun ftau =>
        if type_le_dec ftau ttau then Some ftau
        else if type_le_dec ttau ftau then Some ttau
             else None))
      else None)
    | Fail => Some any_t
    | Read level idx =>
      opt_bind (getenv V idx) (fun sz => Some (bit_t sz))
    | Write level idx value =>
      opt_bind (infer_maxtype Gamma value) (fun vtau =>
      opt_bind (getenv V idx) (fun sz =>
      if type_le_dec (bit_t sz) vtau then Some unit_t
      else None))
    | Call fn args =>
      opt_bind (getenv Sigma fn) (fun '(FunSig argSizes retType) =>
      if (PeanoNat.Nat.eq_dec (List.length args) (List.length argSizes)) then
        if (fold_right2 (fun arg argSize acc =>
                          acc && match infer_maxtype Gamma arg with
                                 | Some tau => if type_le_dec (bit_t argSize) tau then true else false
                                 | None => false
                                 end)
                       true args argSizes) then
          Some retType
        else None
      else None)
    end.

  Hint Resolve (@env_related_putenv _ _ _ GammaEnv): types.
  Hint Resolve fenv_related_putenv: types.
  Hint Constructors HasType : types.
  Hint Extern 0 => unfold id : types.

  Ltac t :=
    repeat match goal with
           | _ => reflexivity
           | _ => progress cleanup_step
           | [ H: opt_bind ?x _ = Some _ |- _ ] =>
             destruct x eqn:?; cbn in H; [ | discriminate]
           | [ H: match ?x with _ => _ end = Some _ |- _ ] =>
             destruct x eqn:?
           | [ H: env_related (Env := ?Env) ?f ?tenv ?env,
                  H': getenv ?env ?k = Some ?v |- _ ] =>
             pose_once (and_fst H k v) H'
           | [ H: forall Gamma gamma tau, _ -> _ = Some _ -> _,
                 H': infer_maxtype ?Gamma ?r = Some ?tau |- _ ] =>
             specialize (H Gamma _ tau ltac:(eauto with types) H')
           | [ H: MaxType ?V ?Sigma ?Gamma ?r ?tau |- _ ] =>
             pose_once (MaxType_HasType V Sigma Gamma r tau) H
           | _ => solve [econstructor] || econstructor; solve [eauto 5 with types]
           end.

   Lemma infer_maxtype_correct_call:
    forall sigma v,
      env_related id v V ->
      env_related id sigma Sigma ->
     forall args argSizes,
       length args = length argSizes ->
       forall Gamma gamma,
         env_related id gamma Gamma ->
         List.Forall
           (fun r : rule TVar TFn =>
              forall Gamma gamma tau,
                env_related id gamma Gamma -> infer_maxtype Gamma r = Some tau -> MaxType v sigma gamma r tau) args ->
         fold_right2
           (fun arg argSize acc =>
              acc &&
                  match infer_maxtype Gamma arg with
                  | Some tau => if type_le_dec (bit_t argSize) tau then true else false
                  | None => false
                  end) true args argSizes = true ->
         fold_right2
           (fun (arg : rule TVar TFn) (argSize : nat) (acc : Prop) => acc /\ HasType v sigma gamma arg (bit_t argSize))
           True args argSizes.
   Proof.
     induction args; destruct argSizes; cbn in *;
       inversion 1; intros ? ? ?; inversion 1; subst; intros Heq.
     - eauto.
     - destruct infer_maxtype eqn:?;
         apply andb_prop in Heq; repeat cleanup_step.
       destruct type_le_dec; try discriminate.
       eauto using MaxType_HasType.
   Qed.

  Lemma infer_maxtype_correct :
    forall sigma v,
      env_related id v V ->
      env_related id sigma Sigma ->
      forall (r: rule TVar TFn) (Gamma: GammaEnv.(env_t)) gamma (tau: type),
        env_related id gamma Gamma ->
        infer_maxtype Gamma r = Some tau ->
        MaxType v sigma gamma r tau.
  Proof.
    induction r using rule_ind'; cbn; intros; t.

    econstructor; eauto.
    eapply fold_right2_forall2;
      eauto using infer_maxtype_correct_call.
  Qed.

  Lemma forall2_cons_inv {A B} (P: A -> B -> Prop) :
    forall a b la lb,
      forall2 P (a :: la) (b :: lb) ->
      P a b /\ forall2 P la lb.
  Proof.
    intros * H; apply forall2_fold_right2 in H; destruct H as (H & ?).
    apply fold_right2_forall2 in H; intuition.
  Qed.

  Ltac tcomplete_step :=
    match goal with
    | _ => progress subst
    | _ => progress intros
    | [ H: fn ?gamma ?k ?v, H': fenv_related ?gamma ?Gamma |- _ ] =>
      try pose_once H' k v;
      match goal with
      | [ H'': fn gamma k v <-> getenv Gamma k = Some v |- _ ] =>
        pose_once (and_fst H'') H
      end
    | [ H: HasType _ _ _ _ _ |- _ ] =>
      apply HasType_MaxType in H; destruct H as (? & ? & ?)
    | [ H: ?x = Some _ |- opt_bind ?x _ = _ ] =>
      rewrite H; cbn
    | [ H: (forall _ _ , _ -> forall _, _ -> infer_maxtype _ ?r  = Some _)  |-
        opt_bind (infer_maxtype _ ?r) _ = Some _ ] =>
      erewrite H by eauto with types; cbn
    | [ H: type_le ?x ?y |- context[type_le_dec ?x ?y] ] =>
      destruct type_le_dec; try tauto
    | _ => cleanup_step
    end.

  Lemma infer_maxtype_complete_call:
    forall (sigma : fenv TFn ExternalSignature) (v : fenv nat nat) (args : list (rule TVar TFn)) argSizes,
      length args = length argSizes ->
      List.Forall
        (fun r : rule TVar TFn =>
           forall (gamma : fenv TVar type) (tau : type),
             MaxType v sigma gamma r tau ->
             forall Gamma : env_t GammaEnv, fenv_related gamma Gamma -> infer_maxtype Gamma r = Some tau) args ->
      forall (gamma : fenv TVar type) (Gamma : env_t GammaEnv),
        forall2 (fun (arg : rule TVar TFn) (argSize : nat) => HasType v sigma gamma arg (bit_t argSize)) args argSizes ->
        fenv_related gamma Gamma ->
        forall b : bool,
          fold_right2
            (fun (arg : rule TVar TFn) (argSize : nat) (acc : bool) =>
             acc &&
             match infer_maxtype Gamma arg with
             | Some tau0 => if type_le_dec (bit_t argSize) tau0 then true else false
             | None => false
             end) b args argSizes = b.
  Proof.
    induction args; cbn; destruct argSizes; inversion 1; intros HForall * Hforall2 **.
    - reflexivity.
    - inversion HForall as [ | x l Hinfer HForall']; subst.

      apply forall2_cons_inv in Hforall2.

      repeat tcomplete_step.
      erewrite Hinfer; eauto.
      repeat tcomplete_step.
      rewrite Bool.andb_true_r.
      eauto.
  Qed.

  Lemma infer_maxtype_complete :
    forall sigma v,
      fenv_related v V ->
      fenv_related sigma Sigma ->
      forall (r: rule TVar TFn) gamma (tau: type),
        MaxType v sigma gamma r tau ->
        forall (Gamma: GammaEnv.(env_t)),
        fenv_related gamma Gamma ->
        infer_maxtype Gamma r = Some tau.
  Proof.
    induction r using rule_ind'; cbn; inversion 1;
      repeat tcomplete_step; eauto using f_equal with types.

    - destruct PeanoNat.Nat.eq_dec; try tauto.
      erewrite infer_maxtype_complete_call; eauto.
  Qed.

  Theorem TypeInference :
    forall Gamma (r: rule TVar TFn),
      match infer_maxtype Gamma r with
      | Some tau => HasType (tenv_of_env id V) (tenv_of_env id Sigma) (tenv_of_env id Gamma) r tau
      | None => forall tau, not (HasType (tenv_of_env id V) (tenv_of_env id Sigma) (tenv_of_env id Gamma) r tau)
      end.
  Proof.
    intros; destruct infer_maxtype eqn:?.
    - eapply MaxType_HasType.
      + eapply infer_maxtype_correct;
          try eapply tenv_of_env_related; eauto.
      + eauto with types.
    - intros tau Habs.
      eapply HasType_MaxType in Habs.
      destruct Habs as (? & Habs & Hle).
      eapply infer_maxtype_complete in Habs;
        try eapply tenv_of_env_frelated.
      congruence.
  Qed.
End TypeInference.
