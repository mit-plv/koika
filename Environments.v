Require Import Coq.Strings.String.
Require Import SGA.Common.

Create HintDb types discriminated.
Hint Extern 1 => unfold not in *: types.

Record fenv {Key Value: Type} :=
  { fn :> Key -> Value -> Prop;
    uniq: forall k v v', fn k v -> fn k v' -> v = v' }.

Arguments fenv: clear implicits.
Hint Resolve @uniq : types.

Definition fenv_nil {Key Value: Type} : fenv Key Value :=
  {| fn k v := False;
     uniq := ltac:(cbv in *; tauto) |}.

Definition fenv_add {Key Value: Type} (env: fenv Key Value) (k: Key) (v: Value) : fenv Key Value.
  refine {| fn := (fun k' v' => (k = k' /\ v = v') \/ (k <> k' /\ env.(fn) k' v')) |};
    abstract (destruct env; intuition (subst; eauto with types)).
Defined.

Definition fenv_le {Key Value: Type} (cmp : Value -> Value -> Prop) (Gamma Gamma': fenv Key Value) :=
  forall k v, Gamma k v -> exists v', Gamma' k v' /\ cmp v v'.

Class Env {K V: Type}: Type :=
  { env_t: Type;
    env_nil: env_t;
    getenv: env_t -> K -> option V;
    putenv: env_t -> K -> V -> env_t;
    getenv_nil: forall k, getenv env_nil k = None;
    get_put_eq: forall ev k v, getenv (putenv ev k v) k = Some v;
    get_put_neq: forall ev k k' v, k <> k' -> getenv (putenv ev k v) k' = getenv ev k';
    get_put_Some: forall ev k k' v v',
        getenv (putenv ev k v) k' = Some v' <->
        k = k' /\ v = v' \/ k <> k' /\ getenv ev k' = Some v';
    get_put_None: forall ev k k' v,
        getenv (putenv ev k v) k' = None <->
        k <> k' /\ getenv ev k' = None
  }.
Arguments Env : clear implicits.
Arguments env_t {_ _}.

Instance EqEnv {K V: Type} (eqdec: forall k k': K, {k = k'} + {k <> k'}) : Env K V.
Proof.
  refine ({| env_t := list (K * V);
             env_nil := nil;
             getenv e k :=
               match List.find (fun '(k', v) => if eqdec k k' then true else false) e with
               | Some (_, v) => Some v
               | None => None
               end;
             putenv e k v := cons (k, v) e |}); intros.
  - abstract (reflexivity).
  - abstract (cbn; destruct eqdec; congruence).
  - abstract (cbn; destruct eqdec; congruence).
  - abstract (cbn; destruct eqdec; subst; split;
              intuition; repeat cleanup_step; eauto; congruence).
  - abstract (cbn; destruct eqdec; subst; split;
              intuition; repeat cleanup_step; eauto; congruence).
Defined.

Scheme Equality for string.
Instance StringEnv (V: Type) : Env string V := EqEnv string_eq_dec.
Instance NatEnv (V: Type) : Env nat V := EqEnv PeanoNat.Nat.eq_dec.

Section EnvRel.
  Context {K V V': Type} {Env: Env K V}.
  Context (f: V -> V').

  Definition env_related (Gamma: fenv K V') (gamma: env_t Env) :=
    (forall var v, getenv gamma var = Some v -> Gamma var (f v)) /\
    (forall var, getenv gamma var = None -> forall tau, not (Gamma var tau)).

  Lemma env_related_putenv:
    forall (Gamma: fenv K V') (gamma: env_t _)
      (k: K) (v': V') (v: V),
      f v = v' ->
      env_related Gamma gamma ->
      env_related (fenv_add Gamma k v') (putenv gamma k v).
  Proof.
    unfold env_related; cbn. intros * ? (H & H') **.
    split; intros; [
      pose proof (and_fst (get_put_Some _ _ _ _ _) ltac:(eassumption)) |
      pose proof (and_fst (get_put_None _ _ _ _) ltac:(eassumption))
    ]; firstorder (subst; eauto).
  Qed.

  Lemma env_related_getenv_Some:
    forall (Gamma: fenv K V') (k: K) (gamma: env_t _),
      env_related Gamma gamma ->
      forall v: V,
        getenv gamma k = Some v ->
        Gamma k (f v).
  Proof. firstorder. Qed.

  Lemma env_related_getenv_None:
    forall (Gamma: fenv K V') (k: K) (gamma: env_t _),
      env_related Gamma gamma ->
      getenv gamma k = None ->
      forall v', Gamma k v' -> False.
  Proof. firstorder. Qed.

  Definition tenv_of_env (ev: env_t Env): fenv K V'.
    refine {| fn k v' := exists v, getenv ev k = Some v /\ v' = f v |}.
    abstract (intros * (? & Heq & Hfeq) (? & Heq' & Hfeq'); subst;
              rewrite Heq in Heq'; inversion Heq'; eauto).
  Defined.

  Lemma tenv_of_env_related :
    forall (ev: env_t Env),
      env_related (tenv_of_env ev) ev.
  Proof.
    intros; unfold env_related, tenv_of_env, not; cbn; split.
    - firstorder.
    - intros * Heq * Hex; rewrite Heq in Hex;
        firstorder discriminate.
  Qed.

  Lemma tenv_of_env_nil :
    env_related fenv_nil env_nil.
    unfold env_related, fenv_nil; cbn; split; intros.
    - rewrite getenv_nil in H; discriminate.
    - tauto.
  Qed.
End EnvRel.

Section FEnvRel.
  Context {K V: Type} {Env: Env K V}.

  Definition fenv_related (Gamma: fenv K V) (gamma: env_t Env) :=
    forall var v, Gamma var v <-> getenv gamma var = Some v.

  Lemma fenv_related_putenv:
    forall (Gamma: fenv K V) (gamma: env_t _)
      (k: K) (v: V),
      fenv_related Gamma gamma ->
      fenv_related (fenv_add Gamma k v) (putenv gamma k v).
  Proof.
    unfold fenv_related; cbn; intros * H **.
    rewrite get_put_Some, <- H.
    reflexivity.
  Qed.

  Lemma fenv_related_getenv_Some:
    forall (Gamma: fenv K V) (k: K) (gamma: env_t _),
      fenv_related Gamma gamma ->
      forall v: V,
        Gamma k v -> getenv gamma k = Some v.
  Proof. firstorder. Qed.

  Lemma fenv_related_getenv_None:
    forall (Gamma: fenv K V) (k: K) (gamma: env_t _),
      fenv_related Gamma gamma ->
      (forall v', Gamma k v' -> False) ->
      getenv gamma k = None.
  Proof. firstorder.
     destruct getenv eqn:Heq.
     - apply H in Heq; exfalso; eauto.
     - reflexivity.
  Qed.

  Lemma tenv_of_env_frelated :
    forall (ev: env_t Env),
      fenv_related (tenv_of_env id ev) ev.
  Proof.
    intros; unfold fenv_related, tenv_of_env, id; cbn; firstorder (subst; eauto).
  Qed.
End FEnvRel.

Lemma fenv_le_refl {Key Value: Type}:
  forall (cmp: _ -> _ -> Prop) (Gamma : fenv Key Value),
    (forall x, cmp x x) ->
    fenv_le cmp Gamma Gamma.
Proof.
  firstorder.
Qed.

Hint Resolve fenv_le_refl : types.

Lemma fenv_add_increasing {Key Value: Type}:
  forall (cmp: _ -> _ -> Prop) (Gamma1 : fenv Key Value) (var : Key) (tau tau' : Value) (Gamma2 : fenv Key Value),
    cmp tau tau' ->
    fenv_le cmp Gamma1 Gamma2 ->
    fenv_le cmp (fenv_add Gamma1 var tau) (fenv_add Gamma2 var tau').
Proof.
  unfold fenv_le, fenv_add; simpl; firstorder (subst; eauto with types).
Qed.

Hint Resolve fenv_add_increasing : types.

