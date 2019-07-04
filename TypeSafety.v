Require Import SGA.Common SGA.Syntax SGA.Semantics SGA.Types SGA.Typechecking.

Require Import Coq.Lists.List.
Import ListNotations.

Definition fenv_env_consistent {K V V'} `{EV: Env K V} (ev: env_t EV) (fv: fenv K V') :=
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

Definition log_write_consistent (log: Log) (v: fenv nat nat) :=
  forall reg lvl val n,
    v reg n ->
    List.In {| kind := LogWrite; level := lvl; reg := reg; val := val |} log ->
    n = List.length val.

Definition correct_type `{Env nat bits} v (r: result (Log * value)) (tau: type) :=
  match r with
  | Success (l, val) => log_write_consistent l v /\ type_of_value val = tau
  | CannotRun => True
  | Stuck => False
  end.

Ltac not_stuck :=
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

  Definition env_equiv (Gamma: fenv K V') (gamma: env_t Env) :=
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

(*   Definition gamma_well_typed (Gamma: fenv TVar type) (gamma: env_t GammaEnv) := *)
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

Ltac constr_hd c :=
      match c with
      | ?f ?x => constr_hd f
      | ?g => g
      end.

Section TypeSafety.
  Context {TVar: Type}.
  Context {TFn: Type}.

  Context (GammaEnv: Env TVar value).
  Context (SigmaEnv: Env TFn ExternalFunction).
  Context (RegEnv: Env nat bits).

  Hint Resolve (@env_equiv_putenv _ _ _ GammaEnv): types.

Definition and_fst {A B} := fun '(conj a _: and A B) => a.
Definition and_snd {A B} := fun '(conj _ b: and A B) => b.

Ltac t_step :=
  match goal with
  | _ => discriminate
  | _ => progress (cbn in *; intros; subst)
  | [  |- _ /\ _ ] => split
  | [ H: _ /\ _ |- _ ] => destruct H
  | [ H: Success _ = Success _ |- _ ] =>
    inversion H; clear H
  | [ H: bit_t _ = bit_t _ |- _ ] =>
    inversion H; clear H
  | [ H: ExternalFunction |- _ ] => destruct H
  | [ H: ?a, H': ?a |- _ ] =>
    let ta := type of a in
    unify ta Prop; clear H'
  | [ H: log_find _ _ _ = Some _ |- _ ] =>
    unfold log_find in H; apply List.find_some in H
  | [ H: List.In ?x (?a ++ ?b) |- _ ] =>
    pose_once (List.in_app_or a b x) H
  | [ H: forall _, env_equiv _ ?Gamma _ -> _,
        H': env_equiv _ ?Gamma _ |- _ ] =>
    specialize (H _ H')
  | [ H: @fn ?K ?V ?ev ?k ?v, H': fn ?ev ?k ?v' |- _ ] =>
    pose_once (@uniq K V ev k v v') H H'
  | [ H: _ |- _ ] => apply forall2_fold_right2 in H
  | [ H: @log_write_consistent ?log ?v,
         H': fn ?v ?reg ?val,
             H'': In {| kind := LogWrite; reg := ?reg; level := ?lvl; val := ?val' |} ?log |- _ ] =>
    pose_once (H reg lvl val' val) H' H''
  | [ H: forall log, log_write_consistent log _ -> correct_type _ (interp _ _ _ _ log _) _,
      H': log_write_consistent ?log _ |- _ ] =>
    pose_once H log H'
  | [ H: env_equiv (Env := ?Env) ?f ?tenv ?env,
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
  | [ H: match ?x with _ => _ end = ?c |- _ ] =>
    let c_hd := constr_hd c in
    is_constructor c_hd; destruct x
  | [ H: _ \/ _ |- _ ] => destruct H
  | _ => progress (unfold assert_bits, may_read1 in *)
  | _ => solve [eauto 4 using eq_trans with types]
  end.

Ltac t :=
  repeat t_step;
  repeat match goal with
         | [ H: Posed _ |- _ ] => clear H
         end.

Definition tenv_of_env {K V V'} {env: Env K V} {f: V -> V'} (ev: env_t env): fenv K V'.
  refine {| fn k v' := exists v, getenv ev k = Some v /\ v' = f v |}.
  abstract (intros * (? & Heq & Hfeq) (? & Heq' & Hfeq'); subst;
            rewrite Heq in Heq'; inversion Heq'; eauto).
Defined.

Lemma log_read_consistent_add:
  forall l V level reg val,
    log_write_consistent l V ->
    log_write_consistent ({| kind := LogRead; level := level; reg := reg; val := val |} :: l) V.
Proof.
  unfold log_write_consistent; cbn; intros * Hconsistent * Hget' [Heq | ?].
  - inversion Heq.
  - eauto.
Qed.

Hint Resolve log_read_consistent_add: types.

Lemma log_write_consistent_add:
  forall l (v: fenv nat nat) level reg val sz,
    v reg sz ->
    sz = length val ->
    log_write_consistent l v ->
    log_write_consistent ({| kind := LogWrite; level := level; reg := reg; val := val |} :: l) v.
Proof.
  unfold log_write_consistent; cbn; intros * Hget ? * Hconsistent * Hget' [Heq | ?].
  - inversion Heq; subst; eauto with types.
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
                  log_write_consistent rule_log v ->
                  correct_type v (interp V Sigma Gamma sched_log rule_log arg) (bit_t argSize))) True args sizes) ->
      (fold_right2
         (fun arg argSize acc =>
            acc /\ HasType v sigma gamma arg (bit_t argSize)) True args sizes) ->
      forall (rule_log: Log),
        log_write_consistent rule_log v ->
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
            log_write_consistent rule_log' v /\
            type_of_value (impl argvs) = retType.
Proof.
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

Lemma type_safety'':
  forall sigma Sigma gamma v V sched_log,
    env_equiv (@length bool) v V ->
    env_equiv sig sigma Sigma ->
    log_write_consistent sched_log v ->
    forall (s: syntax TVar TFn)
      (tau: Types.type),
      Typechecking.HasType v sigma gamma s tau ->
      forall Gamma,
        env_equiv type_of_value gamma Gamma ->
        forall rule_log: Log,
          log_write_consistent rule_log v ->
          correct_type v (interp V Sigma Gamma sched_log rule_log s) tau.
Proof.
  induction 4; cbn; intros.

  all: try solve [t].

  - t;
      destruct (interp V Sigma Gamma0 sched_log rule_log s) as [ (? & ?) | | ]; cbn in *;
        firstorder eauto using type_of_value_le_eq.

  - t.

    all: eapply type_safe_call in Heqr0; eauto using type_ok.
    all: repeat match goal with
                | [ H: exists _, _ |- _ ] => destruct H
                | [  |- context[_ ++ nil] ] => rewrite app_nil_r
                | _ => t_step
                end.
Qed.

Lemma type_safety':
  forall sigma Sigma gamma Gamma v V sched_log rule_log,
    env_equiv sig sigma Sigma ->
    env_equiv (@length bool) v V ->
    env_equiv type_of_value gamma Gamma ->
    log_write_consistent sched_log v ->
    log_write_consistent rule_log v ->
    forall s tau,
      Typechecking.HasType v sigma gamma s tau ->
      interp V Sigma Gamma sched_log rule_log s <> CannotRun ->
      exists rule_log' val,
        log_write_consistent rule_log' v /\
        type_of_value val = tau.
Proof.
  intros;
    pose proof (type_safety'' sigma Sigma gamma v V sched_log) as ts;
    repeat specialize (ts ltac:(eassumption));
    unfold correct_type in ts.
  destruct interp as [(? & ?) | | ]; cbn in *; (congruence || tauto || eauto).
Qed.

Lemma tenv_of_env_equiv  {K V V'} {env: Env K V} {f: V -> V'} :
  forall (ev: env_t env),
    env_equiv f (tenv_of_env (f := f) ev) ev.
Proof.
  intros; unfold env_equiv, tenv_of_env, not; cbn; split.
  - firstorder.
  - intros * Heq * Hex; rewrite Heq in Hex;
      firstorder discriminate.
Qed.

Lemma type_safety:
  forall Sigma Gamma V sched_log rule_log,
    let sigma := tenv_of_env (f := sig) Sigma in
    let v := tenv_of_env (f := (@length bool)) V in
    let gamma := tenv_of_env (f := type_of_value) Gamma in
    log_write_consistent sched_log v ->
    log_write_consistent rule_log v ->
    forall s tau,
      Typechecking.HasType v sigma gamma s tau ->
      interp V Sigma Gamma sched_log rule_log s <> CannotRun ->
      exists rule_log' val,
        log_write_consistent rule_log' v /\
        type_of_value val = tau.
Proof.
  cbv zeta; intros.
  eapply type_safety';
    try eapply tenv_of_env_equiv.
  all: revgoals; eauto.
Qed.
