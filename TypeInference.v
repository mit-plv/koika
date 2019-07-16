Require Import SGA.Common SGA.Environments SGA.Syntax SGA.Types.
Require Import Coq.Lists.List.
Import ListNotations.

Section TypeInference.
  Context {var_t reg_t fn_t: Type}.
  Context {var_t_eq_dec: EqDec var_t}.

  Context (R: reg_t -> type).
  Context (Sigma: fn_t -> ExternalSignature).

  Open Scope bool_scope.

  Notation uexpr := (uexpr var_t reg_t fn_t).
  Notation urule := (urule var_t reg_t fn_t).
  Notation uscheduler := (uscheduler var_t reg_t fn_t).

  Notation expr := (expr var_t R Sigma).
  Notation rule := (rule var_t R Sigma).
  Notation scheduler := (scheduler var_t R Sigma).

  Notation "` x" := (projT1 x) (at level 0).
  Notation "`` x" := (projT2 x) (at level 0).

  Section Expr.
    Context (sig: tsig var_t).

    Definition cast_expr
               {tau1} tau2 (e: expr sig tau1)
      : option (expr sig tau2).
    Proof.
      destruct (eq_dec tau1 tau2); subst.
      - exact (Some e).
      - exact None.
    Defined.

    Notation EX Px := (existT _ _ Px).

    Fixpoint type_expr (e: uexpr)
      : option ({ tau: type & expr sig tau }) :=
      match e with
      | UVar var =>
        let/opt ktau_m := assoc var sig in
        Some (EX (Var ``ktau_m))
      | UConst cst => Some (EX (Const cst))
      | URead port idx => Some (EX (Read port idx))
      | UCall fn arg1 arg2 =>
        let/opt arg1' := type_expr arg1 in
        let/opt arg2' := type_expr arg2 in
        let/opt arg1' := cast_expr (Sigma fn).(arg1Type) (``arg1') in
        let/opt arg2' := cast_expr (Sigma fn).(arg2Type) (``arg2') in
        Some (EX (Call fn arg1' arg2'))
      end.
  End Expr.

  Section Rule.
    Fixpoint type_rule (sig: tsig var_t)
             (r: urule) : option (rule sig) :=
      match r with
      | USkip => Some Skip
      | UFail => Some Fail
      | USeq r1 r2 =>
        let/opt r1 := type_rule sig r1 in
        let/opt r2 := type_rule sig r2 in
        Some (Seq r1 r2)
      | UBind v ex body =>
        let/opt ex := type_expr sig ex in
        let/opt body := type_rule ((v, `ex) :: sig) body in
        Some (Bind v ``ex body)
      | UIf cond tbranch fbranch =>
        let/opt cond := type_expr sig cond in
        let/opt tbranch := type_rule sig tbranch in
        let/opt fbranch := type_rule sig fbranch in
        let/opt cond := cast_expr sig (bits_t 1) (``cond) in
        Some (If cond tbranch fbranch)
      | UWrite port idx value =>
        let/opt value := type_expr sig value in
        let/opt value := cast_expr sig (R idx) (``value) in
        Some (Write port idx value)
      end.
  End Rule.

  Section Scheduler.
    Fixpoint type_scheduler (s: uscheduler) : option scheduler :=
      match s with
      | UDone =>
        Some Done
      | UTry r s1 s2 =>
        let/opt r := type_rule [] r in
        let/opt s1 := type_scheduler s1 in
        let/opt s2 := type_scheduler s2 in
        Some (Try r s1 s2)
      end.
  End Scheduler.
End TypeInference.

Notation tc R Sigma prog :=
  ltac:(let tcopt := match type of prog with
                     | urule _ _ _ => constr:(type_rule R Sigma List.nil prog)
                     | uscheduler _ _ _ => constr:(type_scheduler R Sigma prog)
                     end in
        let tcopt := (eval cbn in tcopt) in
        let tcterm := (eval cbn in (must tcopt)) in
        exact tcterm) (only parsing).

(*   Hint Resolve (@env_related_putenv _ _ _ GammaEnv): types. *)
(*   Hint Resolve fenv_related_putenv: types. *)
(*   Hint Constructors HasType : types. *)
(*   Hint Extern 0 => unfold id : types. *)

(*   Ltac t := *)
(*     repeat match goal with *)
(*            | _ => reflexivity *)
(*            | _ => progress cleanup_step *)
(*            | [ H: opt_bind ?x _ = Some _ |- _ ] => *)
(*              destruct x eqn:?; cbn in H; [ | discriminate] *)
(*            | [ H: match ?x with _ => _ end = Some _ |- _ ] => *)
(*              destruct x eqn:? *)
(*            | [ H: env_related (Env := ?Env) ?f ?tenv ?env, *)
(*                   H': getenv ?env ?k = Some ?v |- _ ] => *)
(*              pose_once (and_fst H k v) H' *)
(*            | [ H: forall Gamma gamma tau, _ -> _ = Some _ -> _, *)
(*                  H': type_expr ?Gamma ?r = Some ?tau |- _ ] => *)
(*              specialize (H Gamma _ tau ltac:(eauto with types) H') *)
(*            | [ H: MaxType ?R ?Sigma ?Gamma ?r ?tau |- _ ] => *)
(*              pose_once (MaxType_HasType R Sigma Gamma r tau) H *)
(*            | _ => solve [econstructor] || econstructor; solve [eauto 5 with types] *)
(*            end. *)

(*    Lemma type_expr_correct_call: *)
(*     forall sigma v, *)
(*       env_related id v R -> *)
(*       env_related id sigma Sigma -> *)
(*      forall args argSizes, *)
(*        length args = length argSizes -> *)
(*        forall Gamma gamma, *)
(*          env_related id gamma Gamma -> *)
(*          List.Forall *)
(*            (fun r : rule var_t fn_t => *)
(*               forall Gamma gamma tau, *)
(*                 env_related id gamma Gamma -> type_expr Gamma r = Some tau -> MaxType v sigma gamma r tau) args -> *)
(*          fold_right2 *)
(*            (fun arg argSize acc => *)
(*               acc && *)
(*                   match type_expr Gamma arg with *)
(*                   | Some tau => if type_le_dec (bits_t argSize) tau then true else false *)
(*                   | None => false *)
(*                   end) true args argSizes = true -> *)
(*          fold_right2 *)
(*            (fun (arg : rule var_t fn_t) (argSize : nat) (acc : Prop) => acc /\ HasType v sigma gamma arg (bits_t argSize)) *)
(*            True args argSizes. *)
(*    Proof. *)
(*      induction args; destruct argSizes; cbn in *; *)
(*        inversion 1; intros ? ? ?; inversion 1; subst; intros Heq. *)
(*      - eauto. *)
(*      - destruct type_expr eqn:?; *)
(*          apply andb_prop in Heq; repeat cleanup_step. *)
(*        destruct type_le_dec; try discriminate. *)
(*        eauto using MaxType_HasType. *)
(*    Qed. *)

(*   Lemma type_expr_correct : *)
(*     forall sigma v, *)
(*       env_related id v R -> *)
(*       env_related id sigma Sigma -> *)
(*       forall (r: rule var_t fn_t) (Gamma: GammaEnv.(env_t)) gamma (tau: type), *)
(*         env_related id gamma Gamma -> *)
(*         type_expr Gamma r = Some tau -> *)
(*         MaxType v sigma gamma r tau. *)
(*   Proof. *)
(*     induction r using rule_ind'; cbn; intros; t. *)

(*     econstructor; eauto. *)
(*     eapply fold_right2_forall2; *)
(*       eauto using type_expr_correct_call. *)
(*   Qed. *)

(*   Lemma forall2_cons_inv {A B} (P: A -> B -> Prop) : *)
(*     forall a b la lb, *)
(*       forall2 P (a :: la) (b :: lb) -> *)
(*       P a b /\ forall2 P la lb. *)
(*   Proof. *)
(*     intros * H; apply forall2_fold_right2 in H; destruct H as (H & ?). *)
(*     apply fold_right2_forall2 in H; intuition. *)
(*   Qed. *)

(*   Ltac tcomplete_step := *)
(*     match goal with *)
(*     | _ => progress subst *)
(*     | _ => progress intros *)
(*     | [ H: fn ?gamma ?k ?v, H': fenv_related ?gamma ?Gamma |- _ ] => *)
(*       try pose_once H' k v; *)
(*       match goal with *)
(*       | [ H'': fn gamma k v <-> getenv Gamma k = Some v |- _ ] => *)
(*         pose_once (and_fst H'') H *)
(*       end *)
(*     | [ H: HasType _ _ _ _ _ |- _ ] => *)
(*       apply HasType_MaxType in H; destruct H as (? & ? & ?) *)
(*     | [ H: ?x = Some _ |- opt_bind ?x _ = _ ] => *)
(*       rewrite H; cbn *)
(*     | [ H: (forall _ _ , _ -> forall _, _ -> type_expr _ ?r  = Some _)  |- *)
(*         opt_bind (type_expr _ ?r) _ = Some _ ] => *)
(*       erewrite H by eauto with types; cbn *)
(*     | [ H: type_le ?x ?y |- context[type_le_dec ?x ?y] ] => *)
(*       destruct type_le_dec; try tauto *)
(*     | _ => cleanup_step *)
(*     end. *)

(*   Lemma type_expr_complete_call: *)
(*     forall (sigma : fenv fn_t ExternalSignature) (v : fenv nat nat) (args : list (rule var_t fn_t)) argSizes, *)
(*       length args = length argSizes -> *)
(*       List.Forall *)
(*         (fun r : rule var_t fn_t => *)
(*            forall (gamma : fenv var_t type) (tau : type), *)
(*              MaxType v sigma gamma r tau -> *)
(*              forall Gamma : env_t GammaEnv, fenv_related gamma Gamma -> type_expr Gamma r = Some tau) args -> *)
(*       forall (gamma : fenv var_t type) (Gamma : env_t GammaEnv), *)
(*         forall2 (fun (arg : rule var_t fn_t) (argSize : nat) => HasType v sigma gamma arg (bits_t argSize)) args argSizes -> *)
(*         fenv_related gamma Gamma -> *)
(*         forall b : bool, *)
(*           fold_right2 *)
(*             (fun (arg : rule var_t fn_t) (argSize : nat) (acc : bool) => *)
(*              acc && *)
(*              match type_expr Gamma arg with *)
(*              | Some tau0 => if type_le_dec (bits_t argSize) tau0 then true else false *)
(*              | None => false *)
(*              end) b args argSizes = b. *)
(*   Proof. *)
(*     induction args; cbn; destruct argSizes; inversion 1; intros HForall * Hforall2 **. *)
(*     - reflexivity. *)
(*     - inversion HForall as [ | x l Hinfer HForall']; subst. *)

(*       apply forall2_cons_inv in Hforall2. *)

(*       repeat tcomplete_step. *)
(*       erewrite Hinfer; eauto. *)
(*       repeat tcomplete_step. *)
(*       rewrite Bool.andb_true_r. *)
(*       eauto. *)
(*   Qed. *)

(*   Lemma type_expr_complete : *)
(*     forall sigma v, *)
(*       fenv_related v R -> *)
(*       fenv_related sigma Sigma -> *)
(*       forall (r: rule var_t fn_t) gamma (tau: type), *)
(*         MaxType v sigma gamma r tau -> *)
(*         forall (Gamma: GammaEnv.(env_t)), *)
(*         fenv_related gamma Gamma -> *)
(*         type_expr Gamma r = Some tau. *)
(*   Proof. *)
(*     induction r using rule_ind'; cbn; inversion 1; *)
(*       repeat tcomplete_step; eauto using f_equal with types. *)

(*     - destruct PeanoNat.Nat.eq_dec; try tauto. *)
(*       erewrite type_expr_complete_call; eauto. *)
(*   Qed. *)

(*   Theorem TypeInference : *)
(*     forall Gamma (r: rule var_t fn_t), *)
(*       match type_expr Gamma r with *)
(*       | Some tau => HasType (tenv_of_env id R) (tenv_of_env id Sigma) (tenv_of_env id Gamma) r tau *)
(*       | None => forall tau, not (HasType (tenv_of_env id R) (tenv_of_env id Sigma) (tenv_of_env id Gamma) r tau) *)
(*       end. *)
(*   Proof. *)
(*     intros; destruct type_expr eqn:?. *)
(*     - eapply MaxType_HasType. *)
(*       + eapply type_expr_correct; *)
(*           try eapply tenv_of_env_related; eauto. *)
(*       + eauto with types. *)
(*     - intros tau Habs. *)
(*       eapply HasType_MaxType in Habs. *)
(*       destruct Habs as (? & Habs & Hle). *)
(*       eapply type_expr_complete in Habs; *)
(*         try eapply tenv_of_env_frelated. *)
(*       congruence. *)
(*   Qed. *)
(* End TypeInference. *)
