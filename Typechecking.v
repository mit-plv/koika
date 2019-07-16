Require Export SGA.Common SGA.Syntax SGA.Types.

Tactic Notation "teauto" := eauto with types.
Tactic Notation "teauto" integer(n) := eauto n with types.

Section TC.
  Context {var_t reg_t fn_t: Type}.

  Context (GammaEnv: Env var_t type).
  Context (R: reg_t -> type).
  Context (Sigma: fn_t -> ExternalSignature).

  Notation varenv_t := GammaEnv.(env_t).
  Notation rule := (rule var_t R Sigma).
  Notation expr := (expr var_t R Sigma).

  Inductive WellTypedExpr : forall (Gamma: varenv_t) {tau: type} (e: expr tau), Prop :=
  | WellTypedVar:
      forall (Gamma: varenv_t)
        (tau: type) (var: var_t),
        getenv Gamma var = Some tau ->
        WellTypedExpr Gamma (Var tau var)
  | WellTypedConst:
      forall (Gamma: varenv_t) {n} (cst: bits n),
        WellTypedExpr Gamma (Const cst)
  | WellTypedRead:
      forall (Gamma: varenv_t)
        (port: Port) (idx: reg_t),
        WellTypedExpr Gamma (Read port idx)
  | WellTypedCall:
      forall (Gamma: varenv_t)
        (idx: fn_t)
        (arg1: expr (Sigma idx).(arg1Type))
        (arg2: expr (Sigma idx).(arg2Type)),
        WellTypedExpr Gamma arg1 ->
        WellTypedExpr Gamma arg2 ->
        WellTypedExpr Gamma (Call idx arg1 arg2).

  Inductive WellTypedRule : forall (Gamma: varenv_t) {tau: type} (r: rule), Prop :=
  | WellTypedSkip:
      forall (Gamma: varenv_t),
        WellTypedRule Gamma Skip
  | WellTypedFail:
      forall (Gamma: varenv_t),
        WellTypedRule Gamma Fail
  | WellTypedBind:
      forall (Gamma: varenv_t)
        (tau: type) (k: var_t) (ex: expr tau) (body: rule),
        WellTypedExpr Gamma ex ->
        WellTypedRule (putenv Gamma k tau) body ->
        WellTypedRule Gamma (Bind k ex body)
  | WellTypedIf:
      forall (Gamma: varenv_t)
        (cond: expr (bits_t 1)) (tbranch: rule) (fbranch: rule),
        WellTypedExpr Gamma cond ->
        WellTypedRule Gamma tbranch ->
        WellTypedRule Gamma fbranch ->
        WellTypedRule Gamma (If cond tbranch fbranch)
  | WellTypedWrite:
      forall (Gamma: varenv_t)
        (tau: type) (port: Port) (idx: reg_t) (value: expr tau),
        WellTypedExpr Gamma value ->
        WellTypedRule Gamma (Write port idx value).

  Hint Constructors WellTyped : types.
  Hint Extern 1 => unfold forall2 in * : types.
End TC.

(* FIXME: The new uniqueness theorem should say that removing types should be
          (mostly) injective *)

(*   Inductive MaxType : forall (Gamma: varenv_t) (s: rule) (tau: type), Prop := *)
(*   | MaxTypeBind: *)
(*       forall (Gamma: varenv_t) *)
(*         (var: var_t) (expr: rule) (body: rule) *)
(*         (tau tau': type), *)
(*         MaxType Gamma expr tau' -> *)
(*         MaxType (putenv getenv Gamma var = Some tau') body tau -> *)
(*         MaxType Gamma (Bind var expr body) tau *)
(*   | MaxTypeVar: *)
(*       forall (Gamma: varenv_t) *)
(*         (var: var_t) *)
(*         (tau: type), *)
(*         getenv Gamma var = Some tau -> *)
(*         MaxType Gamma (Var var) tau *)
(*   | MaxTypeSkip: *)
(*       forall (Gamma: varenv_t), *)
(*         MaxType Gamma Skip (bits_t 0) *)
(*   | MaxTypeConst: *)
(*       forall (Gamma: varenv_t) *)
(*         (cst: bits), *)
(*         MaxType Gamma (Const cst) (bits_t (length cst)) *)
(*   | MaxTypeIfF: *)
(*       forall (Gamma: varenv_t) *)
(*         (cond: rule) (tbranch: rule) (fbranch: rule) *)
(*         (tauf taut: type), *)
(*         HasType Gamma cond (bits_t 1) -> *)
(*         MaxType Gamma tbranch taut -> *)
(*         MaxType Gamma fbranch tauf -> *)
(*         type_le tauf taut -> *)
(*         MaxType Gamma (If cond tbranch fbranch) tauf *)
(*   | MaxTypeIfT: *)
(*       forall (Gamma: varenv_t) *)
(*         (cond: rule) (tbranch: rule) (fbranch: rule) *)
(*         (tauf taut: type), *)
(*         HasType Gamma cond (bits_t 1) -> *)
(*         MaxType Gamma tbranch taut -> *)
(*         MaxType Gamma fbranch tauf -> *)
(*         type_le taut tauf -> *)
(*         MaxType Gamma (If cond tbranch fbranch) taut *)
(*   | MaxTypeFail: *)
(*       forall (Gamma: varenv_t), *)
(*         MaxType Gamma Fail any_t *)
(*   | MaxTypeRead: *)
(*       forall (Gamma: varenv_t) *)
(*         (port: Port) (idx: reg_t) *)
(*         (size: nat) (n: nat), *)
(*         R idx = size -> *)
(*         MaxType Gamma (Read port idx) (bits_t size) *)
(*   | MaxTypeWrite: *)
(*       forall (Gamma: varenv_t) *)
(*         (port: Port) (idx: reg_t) (value: rule) *)
(*         (size: nat) (n: nat), *)
(*         R idx = size -> *)
(*         HasType Gamma value (bits_t size) -> *)
(*         MaxType Gamma (Write port idx value) (bits_t 0) *)
(*   | MaxTypeCall: *)
(*       forall (Gamma: varenv_t) *)
(*         (idx: fn_t) (a1 a2: rule) *)
(*         (s1 s2: type) (retType: type), *)
(*         Sigma idx = FunSig s1 s2 retType -> *)
(*         HasType Gamma a1 (bits_t s1) -> *)
(*         HasType Gamma a2 (bits_t s2) -> *)
(*         MaxType Gamma (Call idx a1 a2) (bits_t retType). *)

(*   Hint Constructors MaxType : types. *)

(*   Theorem maxtypes_unicity : *)
(*     forall Gamma s tau, *)
(*       MaxType Gamma s tau -> *)
(*       forall tau', *)
(*         MaxType Gamma s tau' -> *)
(*         tau = tau'. *)
(*   Proof. *)
(*     induction 1; intros * HasType'; *)
(*       inversion HasType'; subst. *)
(*     1-12: solve [firstorder (subst; firstorder (congruence || teauto))]. *)
(*   Qed. *)

(*   Hint Resolve maxtypes_unicity : types. *)

(*   Lemma MaxType_HasType : forall Gamma s tau', MaxType Gamma s tau' -> forall tau, type_le tau tau' -> HasType Gamma s tau. *)
(*     induction 1; teauto. *)
(*   Qed. *)

(*   Notation "Gamma [ k ↦ R ]" := *)
(*     (putenv Gamma k R) (at level 7, left associativity, format "Gamma [ k  ↦  R ]"). *)
(*   Notation "Gamma ⊢ s :: tau" := *)
(*     (HasType Gamma s tau) (at level 8, no associativity). *)
(*   Notation "Gamma ⊩ s :: tau" := *)
(*     (MaxType Gamma s tau) (at level 8, no associativity). *)

(*   Notation "tau ⩽ tau'" := *)
(*     (type_le tau tau') (at level 10, no associativity). *)

(*   Ltac t := *)
(*     repeat match goal with *)
(*            | [ H: fn ?Gamma ?k ?R, Hle: fenv_le ?Gamma _ |- _ ] => *)
(*              pose_once Hle k R H *)
(*            | [ H: exists _, _ |- _ ] => destruct H *)
(*            | [ H: _ /\ _ |- _ ] => destruct H *)
(*            end. *)

(*   Lemma MaxType_increasing'' : forall s Gamma tau, *)
(*       MaxType Gamma s tau -> *)
(*       forall (Gamma': tenv var_t), *)
(*         fenv_le Gamma Gamma' -> *)
(*         exists tau', *)
(*           MaxType Gamma' s tau' /\ *)
(*           type_le tau tau'. *)
(*   Proof. *)
(*     induction 1; intros * le; t; teauto 6. *)

(*     - specialize (IHMaxType1 _ le). *)
(*       t. *)
(*       assert (fenv_le Gamma[var ↦ tau'] Gamma'[var ↦ x]) as Hdiff. *)
(*       { apply putenv_increasing; eassumption. } *)
(*       specialize (IHMaxType2 _ Hdiff). *)
(*       t. *)
(*       teauto. *)

(*     - specialize (IHMaxType1 _ le). *)
(*       t. *)
(*       specialize (IHMaxType2 _ le). *)
(*       t. *)

(*       destruct (type_le_upper_bounds_comparable *)
(*                   tauf taut _ _ *)
(*                   ltac:(eassumption) *)
(*                   ltac:(eassumption) *)
(*                   ltac:(eassumption)). *)
(*       teauto. *)
(*       teauto 6. *)

(*     - specialize (IHMaxType1 _ le). *)
(*       t. *)
(*       specialize (IHMaxType2 _ le). *)
(*       t. *)

(*       destruct (type_le_upper_bounds_comparable *)
(*                   taut tauf _ _ *)
(*                   ltac:(eassumption) *)
(*                   ltac:(eassumption) *)
(*                   ltac:(eassumption)). *)
(*       teauto. *)
(*       teauto 6. *)
(*     - teauto 8. *)
(*   Qed. *)

(*   Lemma HasType_MaxType : forall Gamma s tau, *)
(*       HasType Gamma s tau -> *)
(*       exists tau', MaxType Gamma s tau' /\ tau ⩽ tau'. *)
(*   Proof. *)
(*     induction 1; try solve [teauto || firstorder teauto]. *)
(*     - t. *)

(*       pose proof (MaxType_increasing'' *)
(*                     _ _ _ H1 Gamma[var ↦ x0] *)
(*                     ltac:(teauto)). *)
(*       t. *)
(*       teauto. *)
(*     - t. *)

(*       destruct (type_le_upper_bounds_comparable *)
(*                   tau tau x x0 *)
(*                   ltac:(teauto) *)
(*                   ltac:(eassumption) *)
(*                   ltac:(eassumption)). *)
(*       teauto. *)
(*       teauto. *)
(*   Qed. *)

(*   Hint Resolve MaxType_HasType : types. *)

(*   Theorem types_unicity : *)
(*     forall Gamma s tau, *)
(*       HasType Gamma s tau -> *)
(*       HasType Gamma s any_t \/ *)
(*       forall tau', HasType Gamma s tau' -> tau = tau'. *)
(*   Proof. *)
(*     intros Gamma s tau H. *)
(*     pose proof (HasType_MaxType _ _ _ H). *)
(*     t. *)
(*     destruct (type_eq_dec x any_t); subst. *)
(*     - teauto. *)
(*     - right. *)
(*       intros tau' H'. *)
(*       pose proof (HasType_MaxType _ _ _ H'). *)
(*       t. *)
(*       assert (x = x0) by teauto; subst. *)

(*       transitivity x0. *)
(*       teauto. *)
(*       teauto. *)
(*   Qed. *)

(*   Notation scheduler := (scheduler var_t reg_t fn_t). *)

(*   Inductive SchedulerHasTypes: forall (s: scheduler), Prop := *)
(*   | SchedulerHasTypesDone : SchedulerHasTypes Done *)
(*   | SchedulerHasTypesTry : *)
(*       forall r tau s1 s2, *)
(*         HasType fenv_nil r tau -> *)
(*         SchedulerHasTypes s1 -> *)
(*         SchedulerHasTypes s2 -> *)
(*         SchedulerHasTypes (ry r s1 s2). *)
(* End TC. *)
