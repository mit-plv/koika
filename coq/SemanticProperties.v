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
  Context {RKind: Type}.
  Context {RKind_denote: RKind -> Type}.
  Context {_R: reg_t -> RKind}.
  Context {REnv: Env reg_t}.

  Notation Log := (@_Log reg_t RKind RKind_denote _R REnv).

  Lemma getenv_logapp:
    forall (l l': Log) idx,
      REnv.(getenv) (log_app l l') idx =
      REnv.(getenv) l idx ++ REnv.(getenv) l' idx.
  Proof.
    unfold log_app, map2; intros; rewrite getenv_create; reflexivity.
  Qed.

  Lemma log_find_empty {T} idx (f: @LogEntry (RKind_denote (_R idx)) -> option T):
    log_find (log_empty: Log) idx f = None.
  Proof.
    unfold log_find, log_empty; intros; rewrite getenv_create; reflexivity.
  Qed.

  Lemma log_find_create {T}:
    forall fn idx (f: LogEntry (RKind_denote (_R idx)) -> option T),
      log_find (REnv.(create) fn) idx f =
      list_find_opt f (fn idx).
  Proof.
    unfold log_find; intros; rewrite getenv_create; reflexivity.
  Qed.

  Lemma log_find_app {T} (l l': Log) reg (f: LogEntry (RKind_denote (_R reg)) -> option T) :
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

Section LogMaps.
  Context {reg_t: Type}.
  Context {RKind1 RKind2: Type}.
  Context {RKind1_denote: RKind1 -> Type}.
  Context {RKind2_denote: RKind2 -> Type}.
  Context {_R1: reg_t -> RKind1}.
  Context {_R2: reg_t -> RKind2}.
  Context {REnv: Env reg_t}.

  Notation Log1 := (@_Log reg_t RKind1 RKind1_denote _R1 REnv).
  Notation Log2 := (@_Log reg_t RKind2 RKind2_denote _R2 REnv).

  Context (f: forall idx : reg_t, RKind1_denote (_R1 idx) ->
                             RKind2_denote (_R2 idx)).

  Lemma log_existsb_log_map_values :
    forall (l1: Log1) idx pred,
      log_existsb (log_map_values f l1 : Log2) idx pred =
      log_existsb l1 idx pred.
  Proof.
    unfold log_existsb, log_map_values, log_map; intros; rewrite getenv_map.
    induction (getenv _ _) as [| hd tl IH].
    - reflexivity.
    - destruct hd, kind; cbn; rewrite <- IH; reflexivity.
  Qed.

  Lemma log_map_values_empty :
    log_map_values f (log_empty: Log1) = (log_empty: Log2).
  Proof.
    unfold log_app, log_map_values, log_map, log_empty; intros.
    apply equiv_eq; intro; repeat rewrite ?getenv_map, ?getenv_map2, ?getenv_create.
    reflexivity.
  Qed.

  Lemma log_map_values_cons :
    forall (L: Log1) idx le,
      log_map_values f (log_cons idx le L) =
      log_cons idx (LogEntry_map (f idx) le) (log_map_values f L).
  Proof.
    unfold log_cons, log_map_values, log_map; intros.
    apply equiv_eq; intro; repeat rewrite ?getenv_map.
    destruct (let _ := REnv.(finite_keys) in eq_dec k idx); subst; cbn.
    - rewrite !get_put_eq. cbn. reflexivity.
    - rewrite !get_put_neq, !getenv_map; congruence.
  Qed.

  Lemma log_map_values_log_app :
    forall (L l: Log1),
      (log_app (log_map_values f L) (log_map_values f l) : Log2) =
      log_map_values f (log_app L l).
  Proof.
    unfold log_app, log_map_values, log_map; intros.
    apply equiv_eq; intro; repeat rewrite ?getenv_map, ?getenv_map2.
    symmetry; apply map_app.
  Qed.

  Lemma may_read_log_map_values :
    forall (l1: Log1) prt idx,
      may_read (log_map_values f l1 : Log2) prt idx =
      may_read l1 prt idx.
  Proof.
    unfold may_read; intros; rewrite !log_existsb_log_map_values; reflexivity.
  Qed.

  Lemma may_write_log_map_values :
    forall (L1 l1: Log1) prt idx,
      may_write (log_map_values f L1 : Log2) (log_map_values f l1 : Log2) prt idx =
      may_write L1 l1 prt idx.
  Proof.
    unfold may_write; intros.
    repeat setoid_rewrite log_map_values_log_app;
      repeat setoid_rewrite log_existsb_log_map_values;
      reflexivity.
  Qed.

  Lemma log_find_log_map_values (pred: forall {T}, LogEntry T -> option T):
    forall (l1: Log1) idx,
      (forall prt val,
          @pred (RKind2_denote (_R2 idx)) {| kind := LogRead; port := prt; val := val |} =
          match pred {| kind := LogRead; port := prt; val := val |} with
          | Some v => Some (f idx v)
          | None => None
          end) ->
      (forall prt val,
          pred {| kind := LogWrite; port := prt; val := f idx val |} =
          match pred {| kind := LogWrite; port := prt; val := val |} with
          | Some v => Some (f idx v)
          | None => None
          end) ->
      log_find (log_map_values f l1: Log2) idx pred =
      match log_find l1 idx pred with
      | Some v => Some (f idx v)
      | None => None
      end.
  Proof.
    unfold log_find, log_map_values, log_map, RLog_map, LogEntry_map; intros * Hr Hw.
    rewrite !getenv_map; induction (getenv REnv l1 idx) as [ | hd tl ]; cbn.
    - reflexivity.
    - destruct hd, kind, port; cbn in *; auto.
      all: rewrite IHtl, ?Hr, ?Hw.
      all: destruct pred; reflexivity.
  Qed.

  Lemma latest_write_log_map_values :
    forall (l1: Log1) idx,
      latest_write (log_map_values f l1 : Log2) idx =
      match latest_write l1 idx with
      | Some v => Some (f idx v)
      | None => None
      end.
  Proof.
    unfold latest_write; intros;
      apply log_find_log_map_values; reflexivity.
  Qed.

  Lemma latest_write0_log_map_values :
    forall (l1: Log1) idx,
      latest_write0 (log_map_values f l1 : Log2) idx =
      match latest_write0 l1 idx with
      | Some v => Some (f idx v)
      | None => None
      end.
  Proof.
    unfold latest_write0; intros.
    apply log_find_log_map_values; destruct prt; reflexivity.
  Qed.

  Lemma commit_update_log_map_values :
    forall (l1: Log1) (r: REnv.(env_t) (fun idx => RKind1_denote (_R1 idx))),
      commit_update (Environments.map REnv f r) (log_map_values f l1) =
      Environments.map REnv f (commit_update r l1).
  Proof.
    unfold commit_update; intros; apply equiv_eq; intro.
    repeat rewrite ?getenv_create, ?getenv_map.
    rewrite latest_write_log_map_values; destruct latest_write; reflexivity.
  Qed.
End LogMaps.

Section LatestWrites.
  Context {reg_t: Type}.
  Context {RKind: Type}.
  Context {RKind_denote: RKind -> Type}.
  Context {_R: reg_t -> RKind}.
  Context {REnv: Env reg_t}.

  Notation Log := (@_Log reg_t RKind RKind_denote _R REnv).

  Lemma latest_write0_empty idx:
    latest_write0 (log_empty: Log) idx = None.
  Proof.
    apply log_find_empty.
  Qed.

  Lemma latest_write0_app :
    forall (sl sl': Log) (idx: reg_t),
      (* COQ BUG: Why do I need a let binding? *)
      let lw := latest_write0 (log_app sl sl') idx in
      lw =
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
    setoid_rewrite log_find_cons_eq; destruct le, kind, port; reflexivity.
  Qed.

  Lemma latest_write0_cons_neq :
    forall (log: Log) idx idx' le,
      idx <> idx' ->
      latest_write0 (log_cons idx' le log) idx =
      latest_write0 log idx.
  Proof.
    unfold latest_write0; intros.
    setoid_rewrite log_find_cons_neq; auto.
  Qed.

  Lemma latest_write1_empty idx:
    latest_write1 (log_empty: Log) idx = None.
  Proof.
    apply log_find_empty.
  Qed.

  Lemma latest_write1_app :
    forall (sl sl': Log) idx,
      let lw := latest_write1 (log_app sl sl') idx in
      lw =
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
    setoid_rewrite log_find_cons_eq; destruct le, kind, port; reflexivity.
  Qed.

  Lemma latest_write1_cons_neq :
    forall (log: Log) idx idx' le,
      idx <> idx' ->
      latest_write1 (log_cons idx' le log) idx =
      latest_write1 log idx.
  Proof.
    unfold latest_write1; intros.
    setoid_rewrite log_find_cons_neq; auto.
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
  Context {RKind: Type}.
  Context {RKind_denote: RKind -> Type}.
  Context {_R: reg_t -> RKind}.
  Context {REnv: Env reg_t}.

  Notation Log := (@_Log reg_t RKind RKind_denote _R REnv).

  Context (r: REnv.(env_t) (fun idx => RKind_denote (_R idx))).

  Lemma commit_update_assoc:
    forall (l l' : Log), commit_update (commit_update r l) l' = commit_update r (log_app l' l).
  Proof.
    unfold commit_update, log_app, map2, latest_write, log_find; intros.
    apply create_funext; intros.
    rewrite !getenv_create.
    rewrite list_find_opt_app.
    destruct list_find_opt; reflexivity.
  Qed.

  Lemma commit_update_empty:
    commit_update r log_empty = r.
  Proof.
    intros; apply equiv_eq; intro.
    unfold commit_update, log_empty, latest_write, log_find; rewrite !getenv_create.
    reflexivity.
  Qed.

  Lemma getenv_commit_update :
    forall (l: Log) idx,
      REnv.(getenv) (commit_update r l) idx =
      match latest_write l idx with
      | Some v' => v'
      | None => REnv.(getenv) r idx
      end.
  Proof.
    unfold commit_update; intros; rewrite getenv_create.
    reflexivity.
  Qed.
End CommitUpdates.
