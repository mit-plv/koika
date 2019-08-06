Require Import SGA.Common SGA.Environments SGA.Syntax SGA.TypedSyntax.
Require Import Coq.Lists.List.
Import ListNotations.

Section ErrorReporting.
  Context {pos_t var_t reg_t fn_t: Type}.
  Context {R: reg_t -> type}
          {Sigma: fn_t -> ExternalSignature}.

  Inductive error_message :=
  | UnboundVariable (var: var_t)
  | TypeMismatch {sig tau} (e: expr var_t R Sigma sig tau) (expected: type).

  Record error :=
    { epos: pos_t;
      emsg: error_message }.
End ErrorReporting.

Arguments error_message _ {_ _} _ _.
Arguments error _ _ {_ _} _ _.

Section TypeInference.
  Context {pos_t name_t var_t reg_t ufn_t fn_t: Type}.
  Context {var_t_eq_dec: EqDec var_t}.

  Context (R: reg_t -> type).
  Context (Sigma: fn_t -> ExternalSignature).
  Context (uSigma: forall (fn: ufn_t) (tau1 tau2: type), fn_t).

  Notation uexpr := (uexpr pos_t var_t reg_t ufn_t).
  Notation urule := (urule pos_t var_t reg_t ufn_t).
  Notation uscheduler := (uscheduler pos_t name_t).

  Open Scope bool_scope.

  Notation expr := (expr var_t R Sigma).
  Notation rule := (rule var_t R Sigma).
  Notation scheduler := (scheduler name_t).
  Notation schedule := (schedule name_t var_t R Sigma).
  Notation error := (error pos_t var_t R Sigma).
  Notation error_message := (error_message var_t R Sigma).

  Notation "` x" := (projT1 x) (at level 0).
  Notation "`` x" := (projT2 x) (at level 0).

  Inductive result {A} :=
  | WellTyped (tm: A)
  | IllTyped (err: error).
  Arguments result : clear implicits.

  Definition opt_result {A} (o: option A) (e: error): result A :=
    match o with
    | Some x => WellTyped x
    | None => IllTyped e
    end.

  Definition must_typecheck {A} (r: result A) :=
    match r return (match r with
                    | WellTyped tm => A
                    | IllTyped err => error
                    end) with
    | WellTyped tm => tm
    | IllTyped err => err
    end.

  Notation "'let/res' var ':=' expr 'in' body" :=
    (match expr with
     | WellTyped var => body
     | IllTyped err => IllTyped err
     end)
      (at level 200).

  Section Expr.
    Definition cast_expr (pos: pos_t)
               sig {tau1} tau2 (e: expr sig tau1)
      : result (expr sig tau2).
    Proof.
      destruct (eq_dec tau1 tau2); subst.
      - exact (WellTyped e).
      - exact (IllTyped {| epos := pos;
                            emsg := TypeMismatch e tau2 |}).
    Defined.

    Notation EX Px := (existT _ _ Px).

    Fixpoint expos pos (e: uexpr) :=
      match e with
      | UEPos p _ => p
      | _ => pos
      end.

    Definition unbound_variable pos var : error :=
      {| epos := pos; emsg := UnboundVariable var |}.

    Fixpoint type_expr (pos: pos_t) (sig: tsig var_t) (e: uexpr)
      : result ({ tau: type & expr sig tau }) :=
      match e with
      | UVar var =>
        let/res ktau_m := opt_result (assoc var sig) (unbound_variable pos var) in
        WellTyped (EX (Var ``ktau_m))
      | UConst cst => WellTyped (EX (Const cst))
      | URead port idx => WellTyped (EX (Read port idx))
      | UCall ufn arg1 arg2 =>
        let/res arg1' := type_expr pos sig arg1 in
        let/res arg2' := type_expr pos sig arg2 in
        let fn := uSigma ufn `arg1' `arg2' in
        let/res arg1' := cast_expr (expos pos arg1) sig (Sigma fn).(arg1Type) (``arg1') in
        let/res arg2' := cast_expr (expos pos arg2) sig (Sigma fn).(arg2Type) (``arg2') in
        WellTyped (EX (Call fn arg1' arg2'))
      | UEPos pos e => type_expr pos sig e
      end.
  End Expr.

  Section Rule.
    Fixpoint type_rule (pos: pos_t) (sig: tsig var_t)
             (r: urule) : result (rule sig) :=
      match r with
      | USkip => WellTyped Skip
      | UFail => WellTyped Fail
      | USeq r1 r2 =>
        let/res r1 := type_rule pos sig r1 in
        let/res r2 := type_rule pos sig r2 in
        WellTyped (Seq r1 r2)
      | UBind v ex body =>
        let/res ex := type_expr pos sig ex in
        let/res body := type_rule pos ((v, `ex) :: sig) body in
        WellTyped (Bind v ``ex body)
      | UIf cond tbranch fbranch =>
        let/res cond' := type_expr pos sig cond in
        let/res tbranch := type_rule pos sig tbranch in
        let/res fbranch := type_rule pos sig fbranch in
        let/res cond' := cast_expr (expos pos cond) sig (bits_t 1) (``cond') in
        WellTyped (If cond' tbranch fbranch)
      | UWrite port idx value =>
        let/res value' := type_expr pos sig value in
        let/res value' := cast_expr (expos pos value) sig (R idx) (``value') in
        WellTyped (Write port idx value')
      | URPos pos r => type_rule pos sig r
      end.
  End Rule.

  Section Scheduler.
    Fixpoint type_scheduler
             (pos: pos_t)
             (s: uscheduler): scheduler :=
      match s with
      | UDone =>
        Done
      | UTry r s1 s2 =>
        let s1 := type_scheduler pos s1 in
        let s2 := type_scheduler pos s2 in
        Try r s1 s2
      | UCons r s =>
        let s := type_scheduler pos s in
        Cons r s
      | USPos pos s =>
        type_scheduler pos s
      end.
  End Scheduler.
End TypeInference.

Arguments error_message {_ _ _ _ _}.
Arguments WellTyped {_ _ _ _ R Sigma A}.
Arguments IllTyped {_ _ _ _ R Sigma A}.

(* Coq bug: the name must_typecheck is not resolved at notation definition time *)

Notation _must_typecheck R Sigma tcres :=
  ltac:(let tcres := (eval hnf in tcres) in
        let tcterm := (eval cbn in (must_typecheck R Sigma tcres)) in
        exact tcterm) (only parsing).

Notation tc_rule R Sigma uSigma rule :=
  (ltac:(let typed := constr:(type_rule R Sigma uSigma tt List.nil rule) in
         exact (_must_typecheck R%function Sigma%function typed)))
    (only parsing).

Notation tc_rules R Sigma uSigma rules :=
  (ltac:(match type of rules with
         | (?name_t -> _) =>
           let res := constr:(fun r: name_t =>
                               ltac:(destruct r eqn:? ;
                                       lazymatch goal with
                                       | [ H: _ = ?rr |- _ ] =>
                                         exact (tc_rule R Sigma uSigma (rules rr))
                                       end)) in
           let res := (eval cbn in res) in
           exact res
         end))
    (only parsing).

Notation tc_scheduler uscheduler :=
  (type_scheduler tt uscheduler)
    (only parsing).

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
