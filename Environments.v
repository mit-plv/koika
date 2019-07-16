Require Import Coq.Strings.String Coq.Lists.List.
Require Import SGA.Common.

Import ListNotations.

Inductive member {K: Type}: K -> list K -> Type :=
| MemberHd: forall k sig, member k (k :: sig)
| MemberTl: forall k k' sig, member k sig -> member k (k' :: sig).

Definition mdestruct {K sig} {k: K} (m: member k sig)
  : match sig return member k sig -> Type with
    | [] => fun m => False
    | k' :: sig => fun m => ({ eqn: k = k' & m = eq_rect _ _ (fun _ => MemberHd k sig) _ eqn m } +
                        { m': member k sig & m = MemberTl k k' sig m' })%type
    end m.
  destruct m; cbn.
  - left; exists eq_refl; eauto.
  - right; eauto.
Defined.

Fixpoint mem {K} `{EqDec K} (k: K) sig {struct sig} : member k sig + (member k sig -> False).
  destruct sig.
  - right; inversion 1.
  - destruct (eq_dec k k0) as [Heq | Hneq].
    + subst. left. apply MemberHd.
    + destruct (mem _ _ k sig) as [m | ].
      * left. apply MemberTl. exact m.
      * right. inversion 1; congruence.
Defined.

Fixpoint find {K} (fn: K -> bool) sig {struct sig} : option { k: K & member k sig }.
  destruct sig.
  - right.
  - destruct (fn k) eqn:?.
    + left. eexists. apply MemberHd.
    + destruct (find _ fn sig) as [ (k' & m) | ].
      * left. eexists. apply MemberTl. eassumption.
      * right.
Defined.

Fixpoint assoc {K1 K2: Type} `{EqDec K1}
         (k1: K1) sig {struct sig} : option { k2: K2 & member (k1, k2) sig }.
Proof.
  destruct sig as [ | (k1' & k2) sig ].
  - right.
  - destruct (eq_dec k1 k1'); subst.
    + left. eexists. apply MemberHd.
    + destruct (assoc _ _ _ k1 sig) as [ (k2' & m) | ].
      * left. eexists. apply MemberTl. eassumption.
      * right.
Defined.

Section Contexts.
  Context {K: Type}.
  Context {V: K -> Type}.

  Inductive context: forall (sig: list K), Type :=
  | CtxEmpty: context []
  | CtxCons {sig} (k: K) (v: V k) (ctx: context sig): context (k :: sig).

  Definition cdestruct {sig} (ctx: context sig)
    : match sig return context sig -> Type with
      | [] => fun ctx => ctx = CtxEmpty
      | k :: sig => fun ctx => { vs: V k * context sig | ctx = CtxCons k (fst vs) (snd vs) }
      end ctx.
    destruct ctx.
    - reflexivity.
    - exists (v, ctx); reflexivity.
  Defined.

  Fixpoint ccreate (sig: list K) (f: forall k, V k) : context sig :=
    match sig with
    | nil => CtxEmpty
    | cons h t => CtxCons h (f h) (ccreate t f)
    end.

  Fixpoint cassoc {sig} {k} (m: member k sig)
           (ctx: context sig) {struct m} : V k.
  Proof.
    destruct m; inversion ctx; subst; eauto.
  Defined.

  Fixpoint creplace {sig} {k} (m: member k sig) (v: V k)
           (ctx: context sig) {struct m} : context sig.
    destruct m.
    - destruct (cdestruct ctx) as (vtl & H).
      eapply (CtxCons k v (snd vtl)).
    - destruct (cdestruct ctx) as (vtl & H).
      eapply (CtxCons k' (fst vtl) (creplace sig k m v (snd vtl))).
  Defined.

  Lemma cassoc_creplace_eq {sig} :
    forall (ctx: context sig) {k} (m: member k sig) (v: V k),
      cassoc m (creplace m v ctx) = v.
  Proof.
    induction m; cbn; intros.
    - destruct (cdestruct ctx); cbn. reflexivity.
    - destruct (cdestruct ctx) as (vtl & Heq); cbn.
      rewrite IHm; reflexivity.
  Qed.

  Lemma cassoc_creplace_neq {sig} :
    forall (ctx: context sig) {k k'} (m: member k sig) (m': member k' sig) (v: V k),
      k <> k' ->
      cassoc m' (creplace m v ctx) = cassoc m' ctx.
  Proof.
    induction m; cbn; intros.
    - destruct (cdestruct ctx) as (vtl & Heq); cbn; subst.
      destruct (mdestruct m') as [ (eqn & Heq) | (m'' & Heq)]; subst; cbn in *; subst; cbn.
      + congruence.
      + reflexivity.
    - destruct (cdestruct ctx) as (vtl & Heq); cbn; subst.
      destruct (mdestruct m') as [ (eqn & Heq) | (m'' & Heq)]; subst; cbn in *; subst; cbn.
      + reflexivity.
      + cbn. rewrite IHm; eauto.
  Qed.
End Contexts.

Arguments context {_}.

Notation esig K := (forall k: K, Type).

Record Env {K: Type}  :=
  { env_t: forall (V: esig K), Type;
    getenv: forall {V: esig K}, env_t V -> forall k, V k;
    putenv: forall {V: esig K}, env_t V -> forall k, V k -> env_t V;
    create: forall {V: esig K}, forall (fn: forall k : K, V k), env_t V;
    get_put_eq: forall {V: esig K} (ev: env_t V) k v, getenv (putenv ev k v) k = v;
    get_put_neq: forall {V: esig K} (ev: env_t V) k k' v, k <> k' -> getenv (putenv ev k v) k' = getenv ev k';
    fold_right: forall {V: esig K}, forall {T} (fn: forall k, V k -> T -> T) (ev: env_t V) (t0: T), T }.
Arguments Env: clear implicits.

Class FiniteType {T} :=
  { finite_elems: list T;
    finite_nodup: List.NoDup finite_elems;
    finite_index: forall t: T, member t finite_elems }.
Arguments FiniteType: clear implicits.

Definition ContextEnv {K} `{FiniteType K}: Env K.
  unshelve refine {| env_t V := context V finite_elems;
                     getenv {V} ctx k := cassoc (finite_index k) ctx;
                     putenv {V} ctx k v := creplace (finite_index k) v ctx;
                     create {V} fn := ccreate finite_elems fn;
                     fold_right {V T} (f: forall k: K, V k -> T -> T) ctx (t0: T) :=
                       List.fold_right (fun (k: K) (t: T) => f k (cassoc (finite_index k) ctx) t) t0 finite_elems |}.
  - intros; apply cassoc_creplace_eq.
  - intros; apply cassoc_creplace_neq; eassumption.
Defined.

Ltac FiniteType_t :=
  lazymatch goal with
  | [  |- FiniteType ?T ] =>
    econstructor;
      repeat lazymatch goal with
             | [  |- forall _: _, member _ _ ] => let t := fresh "t" in intros t; destruct t
             | [  |- member ?r (_ :: _) ] => apply MemberTl
             | [  |- member ?r ?l ] => is_evar l; apply MemberHd
             | _ => idtac
             end;
      match goal with
      | [  |- List.NoDup _ ] => repeat econstructor
      | _ => fail 2 "Could not prove finiteness of type" T
      end;
      match goal with
      | [  |- ~ List.In _ _ ] => solve [cbv; intuition discriminate]
      | _ => fail 2 "Could not prove side conditions for finiteness of type" T
      end
  end.

Hint Extern 2 (FiniteType _) => FiniteType_t : typeclass_instances.

(* Create HintDb types discriminated. *)

(* Hint Extern 1 => unfold not in *: types. *)

(* Record fenv {Key Value: Type} := *)
(*   { fn :> Key -> Value -> Prop; *)
(*     uniq: forall k v v', fn k v -> fn k v' -> v = v' }. *)

(* Arguments fenv: clear implicits. *)
(* Hint Resolve @uniq : types. *)

(* Definition fenv_nil {Key Value: Type} : fenv Key Value := *)
(*   {| fn k v := False; *)
(*      uniq := ltac:(cbv in *; tauto) |}. *)

(* Definition fenv_add {Key Value: Type} (env: fenv Key Value) (k: Key) (v: Value) : fenv Key Value. *)
(*   refine {| fn := (fun k' v' => (k = k' /\ v = v') \/ (k <> k' /\ env.(fn) k' v')) |}; *)
(*     abstract (destruct env; intuition (subst; eauto with types)). *)
(* Defined. *)

(* Definition fenv_le {Key Value: Type} (cmp : Value -> Value -> Prop) (Gamma Gamma': fenv Key Value) := *)
(*   forall k v, Gamma k v -> exists v', Gamma' k v' /\ cmp v v'. *)

(* Class Env {K R: Type}: Type := *)
(*   { env_t: Type; *)
(*     env_nil: env_t; *)
(*     getenv: env_t -> K -> option R; *)
(*     putenv: env_t -> K -> R -> env_t; *)
(*     getenv_nil: forall k, getenv env_nil k = None; *)
(*     get_put_eq: forall ev k v, getenv (putenv ev k v) k = Some v; *)
(*     get_put_neq: forall ev k k' v, k <> k' -> getenv (putenv ev k v) k' = getenv ev k'; *)
(*     get_put_Some: forall ev k k' v v', *)
(*         getenv (putenv ev k v) k' = Some v' <-> *)
(*         k = k' /\ v = v' \/ k <> k' /\ getenv ev k' = Some v'; *)
(*     get_put_None: forall ev k k' v, *)
(*         getenv (putenv ev k v) k' = None <-> *)
(*         k <> k' /\ getenv ev k' = None *)
(*   }. *)
(* Arguments Env : clear implicits. *)
(* Arguments env_t {_ _}. *)

(* Instance EqEnv {K R: Type} (eqdec: forall k k': K, {k = k'} + {k <> k'}) : Env K R. *)
(* Proof. *)
(*   refine ({| env_t := list (K * R); *)
(*              env_nil := nil; *)
(*              getenv e k := *)
(*                match List.find (fun '(k', v) => if eqdec k k' then true else false) e with *)
(*                | Some (_, v) => Some v *)
(*                | None => None *)
(*                end; *)
(*              putenv e k v := cons (k, v) e |}); intros. *)
(*   - abstract (reflexivity). *)
(*   - abstract (cbn; destruct eqdec; congruence). *)
(*   - abstract (cbn; destruct eqdec; congruence). *)
(*   - abstract (cbn; destruct eqdec; subst; split; *)
(*               intuition; repeat cleanup_step; eauto; congruence). *)
(*   - abstract (cbn; destruct eqdec; subst; split; *)
(*               intuition; repeat cleanup_step; eauto; congruence). *)
(* Defined. *)

(* Scheme Equality for string. *)
(* Instance StringEnv (R: Type) : Env string R := EqEnv string_eq_dec. *)
(* Instance NatEnv (R: Type) : Env nat R := EqEnv PeanoNat.Nat.eq_dec. *)

(* Section EnvRel. *)
(*   Context {K R R': Type} {Env: Env K R}. *)
(*   Context (f: R -> R'). *)

(*   Definition env_related (Gamma: fenv K R') (gamma: env_t Env) := *)
(*     (forall var v, getenv gamma var = Some v -> Gamma var (f v)) /\ *)
(*     (forall var, getenv gamma var = None -> forall tau, not (Gamma var tau)). *)

(*   Lemma env_related_putenv: *)
(*     forall (Gamma: fenv K R') (gamma: env_t _) *)
(*       (k: K) (v': R') (v: R), *)
(*       f v = v' -> *)
(*       env_related Gamma gamma -> *)
(*       env_related (fenv_add Gamma k v') (putenv gamma k v). *)
(*   Proof. *)
(*     unfold env_related; cbn. intros * ? (H & H') **. *)
(*     split; intros; [ *)
(*       pose proof (and_fst (get_put_Some _ _ _ _ _) ltac:(eassumption)) | *)
(*       pose proof (and_fst (get_put_None _ _ _ _) ltac:(eassumption)) *)
(*     ]; firstorder (subst; eauto). *)
(*   Qed. *)

(*   Lemma env_related_getenv_Some: *)
(*     forall (Gamma: fenv K R') (k: K) (gamma: env_t _), *)
(*       env_related Gamma gamma -> *)
(*       forall v: R, *)
(*         getenv gamma k = Some v -> *)
(*         Gamma k (f v). *)
(*   Proof. firstorder. Qed. *)

(*   Lemma env_related_getenv_None: *)
(*     forall (Gamma: fenv K R') (k: K) (gamma: env_t _), *)
(*       env_related Gamma gamma -> *)
(*       getenv gamma k = None -> *)
(*       forall v', Gamma k v' -> False. *)
(*   Proof. firstorder. Qed. *)

(*   Definition tenv_of_env (ev: env_t Env): fenv K R'. *)
(*     refine {| fn k v' := exists v, getenv ev k = Some v /\ v' = f v |}. *)
(*     abstract (intros * (? & Heq & Hfeq) (? & Heq' & Hfeq'); subst; *)
(*               rewrite Heq in Heq'; inversion Heq'; eauto). *)
(*   Defined. *)

(*   Lemma tenv_of_env_related : *)
(*     forall (ev: env_t Env), *)
(*       env_related (tenv_of_env ev) ev. *)
(*   Proof. *)
(*     intros; unfold env_related, tenv_of_env, not; cbn; split. *)
(*     - firstorder. *)
(*     - intros * Heq * Hex; rewrite Heq in Hex; *)
(*         firstorder discriminate. *)
(*   Qed. *)

(*   Lemma tenv_of_env_nil : *)
(*     env_related fenv_nil env_nil. *)
(*     unfold env_related, fenv_nil; cbn; split; intros. *)
(*     - rewrite getenv_nil in H; discriminate. *)
(*     - tauto. *)
(*   Qed. *)
(* End EnvRel. *)

(* Section FEnvRel. *)
(*   Context {K R: Type} {Env: Env K R}. *)

(*   Definition fenv_related (Gamma: fenv K R) (gamma: env_t Env) := *)
(*     forall var v, Gamma var v <-> getenv gamma var = Some v. *)

(*   Lemma fenv_related_putenv: *)
(*     forall (Gamma: fenv K R) (gamma: env_t _) *)
(*       (k: K) (v: R), *)
(*       fenv_related Gamma gamma -> *)
(*       fenv_related (fenv_add Gamma k v) (putenv gamma k v). *)
(*   Proof. *)
(*     unfold fenv_related; cbn; intros * H **. *)
(*     rewrite get_put_Some, <- H. *)
(*     reflexivity. *)
(*   Qed. *)

(*   Lemma fenv_related_getenv_Some: *)
(*     forall (Gamma: fenv K R) (k: K) (gamma: env_t _), *)
(*       fenv_related Gamma gamma -> *)
(*       forall v: R, *)
(*         Gamma k v -> getenv gamma k = Some v. *)
(*   Proof. firstorder. Qed. *)

(*   Lemma fenv_related_getenv_None: *)
(*     forall (Gamma: fenv K R) (k: K) (gamma: env_t _), *)
(*       fenv_related Gamma gamma -> *)
(*       (forall v', Gamma k v' -> False) -> *)
(*       getenv gamma k = None. *)
(*   Proof. firstorder. *)
(*      destruct getenv eqn:Heq. *)
(*      - apply H in Heq; exfalso; eauto. *)
(*      - reflexivity. *)
(*   Qed. *)

(*   Lemma tenv_of_env_frelated : *)
(*     forall (ev: env_t Env), *)
(*       fenv_related (tenv_of_env id ev) ev. *)
(*   Proof. *)
(*     intros; unfold fenv_related, tenv_of_env, id; cbn; firstorder (subst; eauto). *)
(*   Qed. *)
(* End FEnvRel. *)

(* Lemma fenv_le_refl {Key Value: Type}: *)
(*   forall (cmp: _ -> _ -> Prop) (Gamma : fenv Key Value), *)
(*     (forall x, cmp x x) -> *)
(*     fenv_le cmp Gamma Gamma. *)
(* Proof. *)
(*   firstorder. *)
(* Qed. *)

(* Hint Resolve fenv_le_refl : types. *)

(* Lemma fenv_add_increasing {Key Value: Type}: *)
(*   forall (cmp: _ -> _ -> Prop) (Gamma1 : fenv Key Value) (var : Key) (tau tau' : Value) (Gamma2 : fenv Key Value), *)
(*     cmp tau tau' -> *)
(*     fenv_le cmp Gamma1 Gamma2 -> *)
(*     fenv_le cmp (fenv_add Gamma1 var tau) (fenv_add Gamma2 var tau'). *)
(* Proof. *)
(*   unfold fenv_le, fenv_add; simpl; firstorder (subst; eauto with types). *)
(* Qed. *)

(* Hint Resolve fenv_add_increasing : types. *)

