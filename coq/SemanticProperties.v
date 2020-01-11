(*! ORAAT | Properties of the semantics used in the one-rule-at-a-time theorem !*)
Require Export Koika.Common Koika.TypedSemantics.

Section Lists.
  Lemma list_find_opt_app {A B} (f: A -> option B) (l l': list A) :
    list_find_opt f (l ++ l') =
    match list_find_opt f l with
    | Some x => Some x
    | None => list_find_opt f l'
    end.
  Proof.
    induction l; cbn; intros.
    - reflexivity.
    - rewrite IHl. destruct (f a); reflexivity.
  Qed.

  Lemma find_none_notb {A B}:
    forall (P: A -> option B) l,
      (forall a, List.In a l -> P a = None) ->
      list_find_opt P l = None.
  Proof.
    induction l; cbn; intros * Hnot.
    - reflexivity.
    - pose proof (Hnot a).
      destruct (P a); firstorder discriminate.
  Qed.

  Lemma forallb_exists {A}:
    forall f (l: list A),
      forallb f l = false <->
      exists x, List.In x l /\ f x = false.
  Proof.
    induction l; cbn; split.
    - congruence.
    - intros [x (? & ?)]; exfalso; assumption.
    - intros H; repeat bool_step; destruct H.
      + exists a; eauto.
      + firstorder.
    - intros [x [ [ ? | ? ] Hnx ] ]; subst; try rewrite Hnx.
      + reflexivity.
      + replace (forallb f l) with false by (symmetry; rewrite IHl; eauto);
          bool_simpl; reflexivity.
  Qed.
End Lists.

Section Logs.
  Context {reg_t: Type}.
  Context {R: reg_t -> type}.
  Context {REnv: Env reg_t}.

  Notation Log := (Log R REnv).

  Lemma getenv_logapp:
    forall (l l': Log) idx,
      REnv.(getenv) (log_app l l') idx =
      REnv.(getenv) l idx ++ REnv.(getenv) l' idx.
  Proof.
    unfold log_app, map2; intros; rewrite getenv_create; reflexivity.
  Qed.

  Lemma log_find_empty {T} idx (f: @LogEntry (R idx) -> option T):
    log_find (log_empty: Log) idx f = None.
  Proof.
    unfold log_find, log_empty; intros; rewrite getenv_create; reflexivity.
  Qed.

  Lemma log_find_create {T}:
    forall fn idx (f: LogEntry (R idx) -> option T),
      log_find (REnv.(create) fn) idx f =
      list_find_opt f (fn idx).
  Proof.
    unfold log_find; intros; rewrite getenv_create; reflexivity.
  Qed.

  Lemma log_find_app {T} (l l': Log) reg (f: @LogEntry (R reg) -> option T) :
    log_find (log_app l l') reg f =
    match log_find l reg f with
    | Some x => Some x
    | None => log_find l' reg f
    end.
  Proof.
    unfold log_find, log_app, map2.
    rewrite getenv_create.
    rewrite list_find_opt_app.
    reflexivity.
  Qed.

  Lemma log_cons_eq :
    forall (log: Log) idx le,
      REnv.(getenv) (log_cons idx le log) idx = List.cons le (REnv.(getenv) log idx).
  Proof.
    unfold log_cons; intros; rewrite get_put_eq; reflexivity.
  Qed.

  Lemma log_cons_neq :
    forall (log: Log) idx idx' le,
      idx <> idx' ->
      REnv.(getenv) (log_cons idx' le log) idx = REnv.(getenv) log idx.
  Proof.
    unfold log_cons; intros; rewrite get_put_neq; eauto.
  Qed.

  Lemma log_find_cons_eq {T}:
    forall (log: Log) idx le (f: _ -> option T),
      log_find (log_cons idx le log) idx f =
      match f le with
      | Some v => Some v
      | _ => log_find log idx f
      end.
  Proof.
    unfold log_find; intros;
      rewrite log_cons_eq; reflexivity.
  Qed.

  Lemma log_find_cons_neq {T}:
    forall (log: Log) idx idx' le (f: _ -> option T),
      idx <> idx' ->
      log_find (log_cons idx' le log) idx f =
      log_find log idx f.
  Proof.
    unfold log_find; intros;
      rewrite log_cons_neq by eassumption; reflexivity.
  Qed.

  Lemma log_forallb_not_existsb (log: Log) reg (f: LogEntryKind -> Port -> bool) :
    negb (log_existsb log reg f) = log_forallb log reg (fun k p => negb (f k p)).
  Proof.
    unfold log_existsb, log_forallb.
    induction (getenv _ _ _); cbn.
    - reflexivity.
    - destruct a; cbn.
      rewrite negb_orb, IHy.
      reflexivity.
  Qed.

  Lemma log_existsb_log_cons_eq :
    forall (log: Log) idx k p v f,
      log_existsb (log_cons idx (LE k p v) log) idx f =
      f k p || log_existsb log idx f.
  Proof.
    unfold log_existsb; intros; rewrite log_cons_eq; reflexivity.
  Qed.

  Lemma log_existsb_log_cons_neq :
    forall (log: Log) idx idx' k p v f,
      idx <> idx' ->
      log_existsb (log_cons idx' (LE k p v) log) idx f =
      log_existsb log idx f.
  Proof.
    unfold log_existsb; intros; rewrite log_cons_neq; eauto.
  Qed.

  Lemma log_existsb_empty :
    forall idx f,
      log_existsb (log_empty: Log) idx f = false.
  Proof.
    unfold log_existsb, log_empty; intros;
      rewrite getenv_create; reflexivity.
  Qed.

  Lemma log_forallb_app:
    forall (l l': Log) reg (f: LogEntryKind -> Port -> bool),
      log_forallb (log_app l l') reg f =
      log_forallb l reg f && log_forallb l' reg f.
  Proof.
    unfold log_forallb.
    intros; rewrite getenv_logapp.
    rewrite !forallb_app; reflexivity.
  Qed.

  Lemma log_existsb_app:
    forall (l l': Log) reg (f: LogEntryKind -> Port -> bool),
      log_existsb (log_app l l') reg f =
      log_existsb l reg f || log_existsb l' reg f.
  Proof.
    unfold log_existsb, log_app; intros.
    unfold map2; rewrite getenv_create.
    rewrite existsb_app; reflexivity.
  Qed.

  Lemma log_app_assoc:
    forall (l l' l'': Log),
      log_app l (log_app l' l'') =
      log_app (log_app l l') l''.
  Proof.
    unfold log_app, map2; intros.
    apply create_funext; intros.
    rewrite !getenv_create.
    apply app_assoc.
  Qed.

  Lemma log_app_empty_l : forall (l: Log),
      log_app l log_empty = l.
  Proof.
    intros.
    apply equiv_eq.
    unfold equiv, log_app, map2, log_empty; intros.
    rewrite !getenv_create, app_nil_r.
    reflexivity.
  Qed.

  Lemma log_app_empty_r : forall (l: Log),
      log_app log_empty l = l.
  Proof.
    intros.
    apply equiv_eq.
    unfold equiv, log_app, map2, log_empty; intros.
    rewrite !getenv_create.
    reflexivity.
  Qed.
End Logs.

Section LatestWrites.
  Context {reg_t: Type}.
  Context {R: reg_t -> type}.
  Context {REnv: Env reg_t}.

  Notation Log := (Log R REnv).

  Lemma latest_write0_empty idx:
    latest_write0 (log_empty: Log) idx = None.
  Proof.
    apply log_find_empty.
  Qed.

  Lemma latest_write0_app :
    forall (sl sl': Log) idx,
      latest_write0 (log_app sl sl') idx =
      match latest_write0 sl idx with
      | Some e => Some e
      | None => latest_write0 sl' idx
      end.
  Proof.
    unfold latest_write0; eauto using log_find_app.
  Qed.

  Lemma latest_write0_cons_eq :
    forall (log: Log) idx le,
      latest_write0 (log_cons idx le log) idx =
      match le with
      | LE LogWrite P0 v => Some v
      | _ => latest_write0 log idx
      end.
  Proof.
    unfold latest_write0; intros.
    rewrite log_find_cons_eq; destruct le, kind, port; reflexivity.
  Qed.

  Lemma latest_write0_cons_neq :
    forall (log: Log) idx idx' le,
      idx <> idx' ->
      latest_write0 (log_cons idx' le log) idx =
      latest_write0 log idx.
  Proof.
    unfold latest_write0; intros.
    rewrite log_find_cons_neq by assumption; reflexivity.
  Qed.

  Lemma latest_write1_empty idx:
    latest_write1 (log_empty: Log) idx = None.
  Proof.
    apply log_find_empty.
  Qed.

  Lemma latest_write1_app :
    forall (sl sl': Log) idx,
      latest_write1 (log_app sl sl') idx =
      match latest_write1 sl idx with
      | Some e => Some e
      | None => latest_write1 sl' idx
      end.
  Proof.
    unfold latest_write1; eauto using log_find_app.
  Qed.

  Lemma latest_write1_cons_eq :
    forall (log: Log) idx le,
      latest_write1 (log_cons idx le log) idx =
      match le with
      | LE LogWrite P1 v => Some v
      | _ => latest_write1 log idx
      end.
  Proof.
    unfold latest_write1; intros.
    rewrite log_find_cons_eq; destruct le, kind, port; reflexivity.
  Qed.

  Lemma latest_write1_cons_neq :
    forall (log: Log) idx idx' le,
      idx <> idx' ->
      latest_write1 (log_cons idx' le log) idx =
      latest_write1 log idx.
  Proof.
    unfold latest_write1; intros.
    rewrite log_find_cons_neq by assumption; reflexivity.
  Qed.

  Ltac latest_write_t :=
    unfold latest_write, latest_write0, latest_write1, log_find, log_existsb;
    induction (getenv REnv _ _);
    repeat match goal with
           | _ => reflexivity || discriminate
           | _ => progress (intros; cbn in * )
           | [ H: LogEntry _ |- _ ] => destruct H as [ [ | ] [ | ] ]
           | [ H: _ -> _ = _ |- _ ] => rewrite H by eauto
           | _ => solve [eauto]
           end.

  Lemma latest_write_latest_write0 (l: Log) idx:
    log_existsb l idx is_write1 = false ->
    latest_write l idx = latest_write0 l idx.
  Proof. latest_write_t. Qed.

  Lemma latest_write_latest_write1 (l: Log) idx:
    log_existsb l idx is_write0 = false ->
    latest_write l idx = latest_write1 l idx.
  Proof. latest_write_t. Qed.

  Lemma latest_write_None (l: Log) idx:
    log_existsb l idx is_write0 = false ->
    log_existsb l idx is_write1 = false ->
    latest_write l idx = None.
  Proof. latest_write_t. Qed.

  Lemma latest_write0_None (l: Log) idx:
    log_existsb l idx is_write0 = false ->
    latest_write0 l idx = None.
  Proof. latest_write_t. Qed.

  Lemma latest_write1_None (l: Log) idx:
    log_existsb l idx is_write1 = false ->
    latest_write1 l idx = None.
  Proof. latest_write_t. Qed.
End LatestWrites.

Section CommitUpdates.
  Context {reg_t: Type}.
  Context {R: reg_t -> type}.
  Context {REnv: Env reg_t}.

  Lemma commit_update_assoc:
    forall (r : REnv.(env_t) R) (l l' : Log R REnv),
      commit_update (commit_update r l) l' = commit_update r (log_app l' l).
  Proof.
    unfold commit_update, log_app, map2, latest_write, log_find; intros.
    apply create_funext; intros.
    rewrite !getenv_create.
    rewrite list_find_opt_app.
    destruct list_find_opt; reflexivity.
  Qed.

  Lemma commit_update_empty:
    forall (r : REnv.(env_t) R),
      commit_update r log_empty = r.
  Proof.
    intros; apply equiv_eq; intro.
    unfold commit_update, log_empty, latest_write, log_find; rewrite !getenv_create.
    reflexivity.
  Qed.

  Lemma getenv_commit_update :
    forall sl r idx,
      REnv.(getenv) (commit_update r sl) idx =
      match latest_write (RKind_denote := type_denote) (_R := R) sl idx with
      | Some v' => v'
      | None => REnv.(getenv) r idx
      end.
  Proof.
    unfold commit_update; intros; rewrite getenv_create.
    reflexivity.
  Qed.
End CommitUpdates.
