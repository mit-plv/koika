Require Import SGA.Common SGA.Syntax SGA.Semantics SGA.Types SGA.Typechecking.

Require Import Coq.Lists.List.
Import ListNotations.

Definition fenv_env_consistent {K V V'} `{EV: Env K V} (ev: env_t EV) (fv: fenv K V'):=
  (forall k v, fv k v -> exists v', getenv ev k = v') /\
  (forall k v, getenv ev k = Some v -> exists v', fv k v').

Lemma opt_result_Success:
  forall {A} (o: option A) (a: A),
    opt_result Stuck o = Success a ->
    o = Some a.
Proof.
  destruct o; cbn in *; inversion 1; congruence.
Qed.

Lemma opt_result_Stuck:
  forall {A} (o: option A),
    opt_result Stuck o = Stuck ->
    o = None.
Proof.
  destruct o; cbn in *; inversion 1; congruence.
Qed.

Lemma assert_size_Success:
  forall l l' sz,
    assert_size l sz = Success l' ->
    l = l' /\ List.length l = sz.
Proof.
  unfold assert_size; intros * H;
    destruct (PeanoNat.Nat.eq_dec _ _);
    inversion H; subst; eauto.
Qed.

Lemma assert_size_Stuck:
  forall l sz,
    assert_size l sz = Stuck ->
    List.length l <> sz.
Proof.
  unfold assert_size; intros;
    destruct (PeanoNat.Nat.eq_dec _ _); discriminate || eauto.
Qed.

Lemma arg_types_forall_fold_left2' {TVar TFn}:
  forall args argSizes (P: _ -> _ -> Prop) Q,
  (forall (n: nat) (s: syntax TVar TFn) (argSize: nat),
      List.nth_error args n = Some s ->
      List.nth_error argSizes n = Some argSize ->
      P s argSize) /\ Q ->
  fold_left2 (fun acc arg argSize => acc /\ P arg argSize)
             args argSizes Q.
Proof.
  induction args; cbn; intros * (H & HP); destruct argSizes; try solve [intuition].
  eapply IHargs.
  repeat split; eauto.
  - intros n' **.
    apply (H (S n')); cbn; eauto.
  - apply (H 0); cbn; eauto.
Qed.

Lemma arg_types_forall_fold_left2 {TVar TFn}:
  forall args argSizes (P: _ -> _ -> Prop),
  (forall (n: nat) (s: syntax TVar TFn) (argSize: nat),
      List.nth_error args n = Some s ->
      List.nth_error argSizes n = Some argSize ->
      P s argSize) ->
  fold_left2 (fun acc arg argSize => acc /\ P arg argSize)
             args argSizes True.
Proof.
  eauto using arg_types_forall_fold_left2'.
Qed.


Lemma arg_types_forall_fold_right2' {TVar TFn}:
  forall args argSizes (P: _ -> _ -> Prop) Q,
  (forall (n: nat) (s: syntax TVar TFn) (argSize: nat),
      List.nth_error args n = Some s ->
      List.nth_error argSizes n = Some argSize ->
      P s argSize) /\ Q ->
  fold_right2 (fun arg argSize acc => acc /\ P arg argSize)
              Q args argSizes.
Proof.
  induction args; cbn; intros * (H & HP); destruct argSizes; try solve [intuition].
  split.
  - eapply IHargs; split; eauto.
    intros n' **; apply (H (S n')); cbn; eauto.
  - apply (H 0); cbn; eauto.
Qed.

Lemma arg_types_forall_fold_right2 {TVar TFn}:
  forall args argSizes (P: _ -> _ -> Prop),
  (forall (n: nat) (s: syntax TVar TFn) (argSize: nat),
      List.nth_error args n = Some s ->
      List.nth_error argSizes n = Some argSize ->
      P s argSize) ->
  fold_right2 (fun arg argSize acc => acc /\ P arg argSize)
              True args argSizes.
Proof.
  eauto using arg_types_forall_fold_right2'.
Qed.

Definition log_write_consistent `{Env nat bits} (log: Log) (V: env_t _):=
  forall reg lvl val val0,
    getenv V reg = Some val0 ->
    List.In {| kind:= LogWrite; level:= lvl; reg:= reg; val:= val |} log ->
    List.length val0 = List.length val.

Definition correct_type `{Env nat bits} V (r: result (Log * value)) (tau: type):=
  match r with
  | Success (l, v) => log_write_consistent l V /\ type_of_value v = tau
  | CannotRun => True
  | Stuck => False
  end.

Ltac not_stuck:=
  intros; unfold may_write, may_read0, may_read1;
  repeat match goal with
         | [  |- match ?x with _ => _ end <> Stuck ] => destruct x
         end;
  discriminate.

Lemma may_write_not_stuck sched_log rule_log level idx:
    may_write sched_log rule_log level idx <> Stuck.
Proof. not_stuck. Qed.

Lemma may_read0_not_stuck sched_log rule_log idx:
    may_read0 sched_log rule_log idx <> Stuck.
Proof. not_stuck. Qed.

Lemma may_read1_not_stuck sched_log rule_log idx:
    may_read1 sched_log rule_log idx <> Stuck.
Proof. not_stuck. Qed.

Hint Extern 1 False => eapply may_write_not_stuck: types.
Hint Extern 1 False => eapply may_read0_not_stuck: types.
Hint Extern 1 False => eapply may_read1_not_stuck: types.

Lemma type_of_value_le_eq:
  forall tau tau' v,
    type_le tau tau' ->
    type_of_value v = tau' ->
    type_of_value v = tau.
Proof.
  destruct v; cbn; inversion 1; congruence.
Qed.

Axiom get_put_Some: (forall {K V} `{Env K V} ev k k' v v',
                         getenv (putenv ev k v) k' = Some v' ->
                         k = k' /\ v = v' \/ k <> k' /\ getenv ev k' = Some v').
Axiom get_put_None: (forall {K V} `{Env K V} ev k k' v,
                         getenv (putenv ev k v) k' = None ->
                         k <> k' /\ getenv ev k' = None).

Section EnvEquiv.
  Context {K V V': Type} {Env: Env K V}.
  Context (f: V -> V').

  Definition env_equiv (Gamma: fenv K V') (gamma: env_t Env):=
    (forall var v, getenv gamma var = Some v -> Gamma var (f v)) /\
    (forall var, getenv gamma var = None -> forall tau, not (Gamma var tau)).

  Lemma env_equiv_putenv:
    forall (Gamma: fenv K V') (gamma: env_t _)
      (k: K) (v': V') (v: V),
      f v = v' ->
      env_equiv Gamma gamma ->
      env_equiv (fenv_add Gamma k v') (putenv gamma k v).
  Proof.
    unfold env_equiv; cbn. intros * ? (H & H') **.
    split; intros; [
      pose proof (get_put_Some _ _ _ _ _ ltac:(eassumption)) |
      pose proof (get_put_None _ _ _ _ ltac:(eassumption))
    ]; firstorder (subst; eauto).
  Qed.

  Lemma env_equiv_getenv_Some:
    forall (Gamma: fenv K V') (k: K) (gamma: env_t _),
      env_equiv Gamma gamma ->
      forall v: V,
        getenv gamma k = Some v ->
        Gamma k (f v).
  Proof. firstorder. Qed.

  Lemma env_equiv_getenv_None:
    forall (Gamma: fenv K V') (k: K) (gamma: env_t _),
      env_equiv Gamma gamma ->
      getenv gamma k = None ->
      forall v', Gamma k v' -> False.
  Proof. firstorder. Qed.
End EnvEquiv.

(*   Definition gamma_well_typed (Gamma: fenv TVar type) (gamma: env_t GammaEnv):= *)
(*     (forall var v, getenv gamma var = Some v -> Gamma var (type_of_value v)) /\ *)
(*     (forall var, getenv gamma var = None -> forall tau, not (Gamma var tau)). *)


(* Lemma gamma_well_typed_putenv: *)
(*   forall (Gamma: fenv TVar type) (gamma: env_t GammaEnv) *)
(*     (var: TVar) (tau: type) (v: value), *)
(*     gamma_well_typed Gamma gamma -> *)
(*     type_of_value v = tau -> *)
(*     gamma_well_typed (fenv_add Gamma var tau) (putenv gamma var v). *)
(* Proof. *)
(*   unfold gamma_well_typed; cbn. intros * (H & H') **. *)
(*   split; intros; [ *)
(*     pose proof (get_put_Some _ _ _ _ _ ltac:(eassumption)) | *)
(*     pose proof (get_put_None _ _ _ _ ltac:(eassumption)) *)
(*   ]; firstorder (subst; eauto). *)
(* Qed. *)

(* Lemma gamma_well_typed_getenv_Some: *)
(*   forall (Gamma: fenv TVar type) (var: TVar) (gamma: env_t GammaEnv), *)
(*     gamma_well_typed Gamma gamma -> *)
(*     forall a: value, *)
(*       getenv gamma var = Some a -> *)
(*       Gamma var (type_of_value a). *)
(* Proof. firstorder. Qed. *)

(* Lemma gamma_well_typed_getenv_None: *)
(*   forall (Gamma: fenv TVar type) (var: TVar) (gamma: env_t GammaEnv), *)
(*     gamma_well_typed Gamma gamma -> *)
(*     getenv gamma var = None -> *)
(*     forall tau, *)
(*       Gamma var tau -> False. *)
(* Proof. firstorder. Qed. *)

Section TypeSafety.
  Context {TVar: Type}.
  Context {TFn: Type}.

  Context (GammaEnv: Env TVar value).
  Context (SigmaEnv: Env TFn ExternalFunction).
  Context (RegEnv: Env nat bits).

  Hint Resolve (@env_equiv_putenv _ _ _ GammaEnv): types.

Definition and_fst {A B}:= fun '(conj a _: and A B) => a.
Definition and_snd {A B}:= fun '(conj _ b: and A B) => b.

Ltac t_step:=
  match goal with
  | _ => discriminate
  | _ => progress (cbn in *; intros; subst)
  | [ H: _ /\ _ |- _ ] => destruct H
  | [ H: Success _ = Success _ |- _ ] =>
    inversion H; clear H
  | [ H: bit_t _ = bit_t _ |- _ ] =>
    inversion H; clear H
  | [ H: forall _, env_equiv _ ?Gamma _ -> _,
        H': env_equiv _ ?Gamma _ |- _ ] =>
    specialize (H _ H')
  | [ H: forall log, log_write_consistent log _ -> correct_type _ (interp _ _ _ _ log _) _,
      H': log_write_consistent ?log _ |- _ ] =>
    pose_once H log H'
  | [ H: env_equiv (Env:= ?Env) ?f ?tenv ?env,
      H': getenv ?env ?k = Some ?v |- _ ] =>
    pose_once (and_fst H k v) H'
  | [ H: env_equiv ?f ?tenv ?env,
         H': getenv ?env ?k = None |- _ ] =>
    pose_once (and_snd H k) H'
  | [ H: assert_size _ _ = Success _ |- _ ] =>
    apply assert_size_Success in H
  | [ H: assert_size _ _ = Stuck |- _ ] =>
    apply assert_size_Stuck in H
  | [ H: opt_result Stuck _ = Success _ |- _ ] =>
    apply opt_result_Success in H
  | [ H: opt_result Stuck _ = Stuck |- _ ] =>
    apply opt_result_Stuck in H
  | [ p: _ * _ |- _ ] => destruct p
  | [  |- _ (opt_result _ ?o) _] =>
    destruct o eqn:?
  | [  |- correct_type _ (result_bind ?r _) _ ] =>
    destruct r eqn:?
  | [  |- correct_type _ (result_map ?r _) _ ] =>
    destruct r eqn:?
  | [  |- correct_type _ ((if ?v then _ else _)) _ ] =>
    destruct v eqn:?
  | [ H: correct_type _ (interp _ ?Gamma _ _ ?log ?s) _,
         H': interp _ ?Gamma _ _ ?log ?s = Stuck |- _ ] =>
    red in H; rewrite H' in H
  | _ => solve [eauto 4 using eq_trans with types]
  end.

Ltac t:=
  repeat t_step;
  repeat match goal with
         | [ H: Posed _ |- _ ] => clear H
         end.

Definition tenv_of_env {K V V'} {env: Env K V} {f: V -> V'} (ev: env_t env): fenv K V'.
  refine {| fn k v':= exists v, getenv ev k = Some v /\ v' = f v |}.
  abstract (intros * (? & Heq & Hfeq) (? & Heq' & Hfeq'); subst;
            rewrite Heq in Heq'; inversion Heq'; eauto).
Defined.


Lemma fold_right2_result_length2':
  forall V Sigma Gamma sched_log args sizes rule_log l bs bs0,
    length args = length sizes ->
    fold_right2
      (fun arg size (acc: result (Log * list bits)) =>
         result_bind acc (fun '(rule_log, argvs) =>
         result_bind (interp V Sigma Gamma sched_log rule_log arg) (fun '(rule_log, argv) =>
         result_map (assert_bits argv size) (fun bs =>
         (rule_log, cons bs argvs)))))
      (Success (rule_log, bs0)) args sizes =
    Success (l, bs) ->
    length bs = length sizes + length bs0.
Proof.
  induction args; simpl; destruct sizes; cbn; inversion 1.
  - inversion 1; subst; reflexivity.
  - intros.
    destruct fold_right2 eqn:Heq; cbn in *; try discriminate.
    destruct a0.
    destruct (interp V Sigma Gamma sched_log l0 a); try discriminate; cbn in *.
    destruct a0.
    destruct (assert_bits _ _); try discriminate; cbn in *.
    inversion H0; subst; cbn in *.
    inversion H.
    rewrite H3.
    eauto.
Qed.

Lemma fold_right2_result_length2:
  forall V Sigma Gamma sched_log args sizes rule_log l bs,
    length args = length sizes ->
    fold_right2
      (fun arg size (acc: result (Log * list bits)) =>
         result_bind acc (fun '(rule_log, argvs) =>
         result_bind (interp V Sigma Gamma sched_log rule_log arg) (fun '(rule_log, argv) =>
         result_map (assert_bits argv size) (fun bs =>
         (rule_log, cons bs argvs)))))
      (Success (rule_log, nil)) (List.rev args) (List.rev sizes) =
    Success (l, bs) ->
    length bs = length sizes.
Proof.
  intros; rewrite <- (PeanoNat.Nat.add_0_r (length sizes)).
  rewrite <- (List.rev_length sizes).
  eapply fold_right2_result_length2' with (bs0:= nil).
  rewrite (List.rev_length args), (List.rev_length sizes); eassumption.
  eauto.
Qed.

Lemma log_read_consistent_add:
  forall l V level reg val,
    log_write_consistent l V ->
    log_write_consistent ({| kind:= LogRead; level:= level; reg:= reg; val:= val |} :: l) V.
Proof.
  unfold log_write_consistent; cbn; intros * Hconsistent * Hget' [Heq | ?].
  - inversion Heq.
  - eauto.
Qed.

Hint Resolve log_read_consistent_add: types.

Lemma log_write_consistent_add:
  forall l V level reg val a,
    getenv V reg = Some a ->
    length a = length val ->
    log_write_consistent l V ->
    log_write_consistent ({| kind:= LogWrite; level:= level; reg:= reg; val:= val |} :: l) V.
Proof.
  unfold log_write_consistent; cbn; intros * Hget ? * Hconsistent * Hget' [Heq | ?].
  - inversion Heq; subst; rewrite Hget in Hget'; inversion Hget'; subst; eauto.
  - eauto.
Qed.

Hint Resolve log_write_consistent_add: types.

Lemma type_safe_call:
  forall v V sigma Sigma gamma Gamma,
    env_equiv (@length bool) v V ->
    env_equiv sig sigma Sigma ->
    forall sched_log retType args sizes impl,
      length args = length sizes ->
      env_equiv type_of_value gamma Gamma ->
      (forall args : list bits,
          length args = length sizes ->
          type_of_value (impl args) = retType) ->
      (fold_right2
         (fun arg argSize acc =>
            acc /\
            (forall Gamma : env_t GammaEnv,
                env_equiv type_of_value gamma Gamma ->
                forall rule_log : Log,
                  log_write_consistent rule_log V ->
                  correct_type V (interp V Sigma Gamma sched_log rule_log arg) (bit_t argSize))) True args sizes) ->
      (fold_right2
         (fun arg argSize acc =>
            acc /\ HasType v sigma gamma arg (bit_t argSize)) True args sizes) ->
      forall (rule_log: Log),
        log_write_consistent rule_log V ->
        forall argvs0 res,
          fold_left2
            (fun (acc: result (Log * list bits)) arg size =>
               result_bind acc (fun '(rule_log, argvs) =>
               result_bind (interp V Sigma Gamma sched_log rule_log arg) (fun '(rule_log, argv) =>
               result_map (assert_bits argv size) (fun bs =>
               (rule_log, bs :: argvs)))))
            args sizes (Success (rule_log, argvs0)) = res ->
          res = CannotRun \/
          exists argvs rule_log',
            res = Success (rule_log', argvs ++ argvs0) /\
            length argvs = length sizes /\
            log_write_consistent rule_log' V /\
            type_of_value (impl argvs) = retType.
Proof.
  (* setoid_rewrite fold_left2_rev_right2. *)
  induction args; destruct sizes; inversion 1.
  - cbn. intros **; destruct res; try discriminate.
    inversion H7; subst; right; exists nil; eexists; intuition eauto.
  - cbn in *; intros Heqv Htypeof (Hargscorrect & Hargcorrect) (Hargtypes & Hargtype) * Hconsistent * Heq.
    specialize (Hargcorrect _ ltac:(eassumption) _ ltac:(eassumption)).
    destruct interp as [(? & ?) | | ] eqn:?; cbn in *; try tauto.
    + destruct Hargcorrect as (Hlconsistent & Htypev0).
      destruct v0; cbn in *; try discriminate.
      inversion Htypev0; subst n; clear Htypev0.
      unfold assert_size in *.
      destruct PeanoNat.Nat.eq_dec; try congruence; cbn in *.

      specialize (IHargs sizes (fun args => impl (args ++ [val]))
                         ltac:(eassumption) ltac:(eassumption)).
      specialize (IHargs ltac:(intros; apply Htypeof; rewrite app_length, PeanoNat.Nat.add_comm; cbn; eauto)
                         ltac:(eassumption) ltac:(eassumption)
                                                   l ltac:(eassumption) _ _ Heq).
      destruct IHargs as [ IHargs | IHargs ]; [ now left | right ].
      destruct IHargs as (argvs & rule_log' & Hreseq & Hlen & Hconsistent' & Htypeof'); subst.
      exists (argvs ++ [val]); exists rule_log'.
      repeat split.
      * rewrite <- app_assoc; reflexivity.
      * rewrite app_length, PeanoNat.Nat.add_comm; cbn; eauto.
      * eauto.
    + (* rewrite fold_left2_rev_right2 in Heq by assumption. *)
      clear -Heq.
      left; revert dependent sizes; induction args; destruct sizes; cbn in *; eauto.
Qed.

Lemma type_safety:
  forall sigma Sigma gamma v V sched_log,
    env_equiv (@length bool) v V ->
    env_equiv sig sigma Sigma ->
    log_write_consistent sched_log V ->
    forall (s: syntax TVar TFn)
      (tau: Types.type),
      Typechecking.HasType v sigma gamma s tau ->
      forall Gamma,
        env_equiv type_of_value gamma Gamma ->
        forall rule_log: Log,
          log_write_consistent rule_log V ->
          correct_type V (interp V Sigma Gamma sched_log rule_log s) tau.
Proof.
  induction 4; cbn; intros.

  Hint Extern 1 => unfold not in *: types.

  all: try solve [t].

  - t.
    destruct (interp V Sigma Gamma0 sched_log rule_log s) as [ (? & ?) | | ]; cbn in *;
      firstorder eauto using type_of_value_le_eq.
  - t.
    split; t.
    split; t.

    + destruct a0.
      destruct l.
      * t.
      * t.

    + destruct a0.
      destruct l.
      * unfold may_read1 in *.
        destruct log_existsb; try discriminate.
        inversion Heqr0; clear Heqr0.
        unfold log_find in *.
        apply List.find_some in H7.
        t.
        destruct PeanoNat.Nat.eq_dec; cbn in *; subst; try discriminate.
        destruct kind; cbn in *; try discriminate.
        destruct level; cbn in *; try discriminate.
        t.
        eapply List.in_app_or in H6.
        destruct H6.
        specialize (H4 _ _ _ _ Heqr H6).
        congruence.
        specialize (H1 _ _ _ _ Heqr H6).
        congruence.
      * t.

  - t.

    destruct v0; cbn in *; try discriminate.
    split; t.

    destruct v0; cbn in *; try discriminate.
    t.

  - t;
    match goal with
    | [ H: @fn ?K ?V ?ev ?k ?v, H': fn ?ev ?k ?v' |- _ ] =>
      pose_once (@uniq K V ev k v v') H H'
    end.

    destruct a; cbn in *.
    destruct sig; cbn in *.
    inversion H9; subst; cbn in *.
    apply arg_types_forall_fold_right2 in H4.
    apply arg_types_forall_fold_right2 in H5.

    eapply type_safe_call in Heqr0; eauto using type_ok.
    destruct Heqr0 as [ Heqr0 | Heqr0 ]; try discriminate.
    destruct Heqr0 as (argvs & rule_log' & HeqSuccess & Heqlen & Hlog & Htypeof).
    inversion HeqSuccess; subst; clear HeqSuccess.
    rewrite app_nil_r.
    split; eauto.

    destruct a; cbn in *.
    destruct sig; cbn in *.
    inversion H9; subst; cbn in *.
    apply arg_types_forall_fold_right2 in H4.
    apply arg_types_forall_fold_right2 in H5.
    eapply type_safe_call in Heqr0; eauto using type_ok.
    destruct Heqr0 as [ Heqr0 | Heqr0 ]; try discriminate.
    destruct Heqr0 as (argvs & rule_log' & HeqSuccess & Heqlen & Hlog & Htypeof); discriminate.

    destruct a; cbn in *.
    destruct sig; cbn in *.
    inversion H9; subst; cbn in *.
    apply arg_types_forall_fold_right2 in H4.
    apply arg_types_forall_fold_right2 in H5.

    clear Heqs.
    cbn in *.
    congruence.
Qed.
