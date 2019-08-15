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

Require Import Program.

(* Definition mdestruct_same {K sig} {k: K} (m: member k (k :: sig)) : *)
(*   { m': member k sig & m = MemberTl k k sig m' } + { m = MemberHd k sig }. *)

Lemma member_In {K} (sig: list K):
  forall k, member k sig -> List.In k sig.
Proof.
  induction 1; firstorder.
Qed.

Fixpoint member_id {K sig} {k: K} (m: member k sig) : nat :=
  match m with
  | MemberHd k sig => 0
  | MemberTl k k' sig m' => S (member_id m')
  end.

Lemma member_id_nth {K sig} (k: K) (m: member k sig) :
  List.nth_error sig (member_id m) = Some k.
Proof.
  induction m; firstorder.
Qed.

Lemma member_NoDup {K} {sig: list K} k:
  EqDec K ->
  NoDup sig ->
  forall (m1 m2: member k sig),
    m1 = m2.
Proof.
  induction 2.
  - intros; destruct (mdestruct m1).
  - intros; destruct (mdestruct m1) as [(-> & ->) | (mem & ->)]; cbn.
    + intros; destruct (mdestruct m2) as [(? & ->) | (absurd & ->)]; cbn.
      * rewrite <- Eqdep_dec.eq_rect_eq_dec by apply eq_dec.
        reflexivity.
      * exfalso; apply member_In in absurd; auto.
    + intros; destruct (mdestruct m2) as [(-> & ->) | (? & ->)]; cbn.
      * exfalso; apply member_In in mem. auto.
      * f_equal; apply IHNoDup.
Qed.

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

  Fixpoint ccreate (sig: list K) (f: forall k, member k sig -> V k) : context sig :=
    match sig return (forall k, member k sig -> V k) -> context sig with
    | nil => fun _ => CtxEmpty
    | cons h t => fun f => CtxCons h (f h (MemberHd h t))
                               (ccreate t (fun k m => f k (MemberTl k h t m)))
    end f.

  Fixpoint cassoc {sig} {k} (m: member k sig)
           (ctx: context sig) {struct m} : V k.
  Proof.
    destruct m; inversion ctx; subst; eauto.
  Defined.

  Lemma cassoc_ccreate {sig} (f: forall k, _ -> V k) {k} (m: member k sig) :
    cassoc m (ccreate sig f) = f k m.
  Proof.
    induction sig; cbn.
    - pose proof (mdestruct m) as Hd; elim Hd.
    - pose proof (mdestruct m) as [(eqn & Heq) | (m' & Heq)].
      + destruct eqn; cbn in *; rewrite Heq.
        reflexivity.
      + rewrite Heq; cbn.
        apply IHsig.
  Qed.

  Lemma ccreate_funext {sig} (f1 f2: forall k, _ -> V k):
    (forall k m, f1 k m = f2 k m) ->
    ccreate sig f1 = ccreate sig f2.
  Proof.
    induction sig; cbn.
    - intros; reflexivity.
    - intros Heq; rewrite Heq; eauto using f_equal.
  Qed.

  Lemma ccreate_cassoc {sig} (ctx: context sig):
    ccreate sig (fun k m => cassoc m ctx) = ctx.
  Proof.
    induction sig; cbn; intros.
    - rewrite (cdestruct ctx).
      reflexivity.
    - destruct (cdestruct ctx) as ((h & t) & ->); cbn.
      rewrite IHsig; reflexivity.
  Qed.

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

  Instance EqDec_member {K} sig (k: K) {EQ: EqDec K} : EqDec (member k sig).
  Proof.
    econstructor.
    induction sig; intros m1 m2.
    - destruct (mdestruct m1).
    - destruct (mdestruct m1) as [(eqn & Heq) | (m1' & Heq)]; subst; cbn in *; subst; cbn;
        destruct (mdestruct m2) as [(eqn & Heq) | (m2' & Heq)];
        try (rewrite <- Eqdep_dec.eq_rect_eq_dec in Heq by apply eq_dec);
        subst; cbn in *; subst.
      + left; reflexivity.
      + right; intro; discriminate.
      + right; intro; discriminate.
      + destruct (IHsig m1' m2'); subst.
        * left; reflexivity.
        * right; intro; inversion H as [H'].
          apply Eqdep_dec.inj_pair2_eq_dec in H'; try apply eq_dec.
          apply Eqdep_dec.inj_pair2_eq_dec in H'; try apply eq_dec.
          eauto.
  Defined.
End Contexts.
Arguments context {_}.

Class FiniteType {T} :=
  { finite_elems: list T;
    finite_nodup: List.NoDup finite_elems;
    finite_index: forall t: T, member t finite_elems }.
Arguments FiniteType: clear implicits.

Instance EqDec_FiniteType {T} `{FiniteType T} : EqDec T.
  econstructor; intros.
  destruct (PeanoNat.Nat.eq_dec (member_id (finite_index t1)) (member_id (finite_index t2))) as [ H' | H' ].
  - left.
    apply (f_equal (List.nth_error finite_elems)) in H'.
    rewrite !member_id_nth in H'.
    congruence.
  - right.
    intros ->.
    congruence.
Qed.

Notation esig K := (forall k: K, Type).

Record Env {K: Type}  :=
  { env_t: forall (V: esig K), Type;
    getenv: forall {V: esig K}, env_t V -> forall k, V k;
    putenv: forall {V: esig K}, env_t V -> forall k, V k -> env_t V;
    create: forall {V: esig K} (fn: forall (k: K), V k), env_t V;

    finite_keys: FiniteType K;
    create_getenv_id: forall {V: esig K} (ev: env_t V),
        create (getenv ev) = ev; (* Not strictly needed *)
    create_funext: forall {V: esig K} (fn1 fn2: forall k : K, V k),
        (forall k, fn1 k = fn2 k) -> create fn1 = create fn2;
    getenv_create: forall {V: esig K} (fn: forall k : K, V k) k,
        getenv (create fn) k = fn k;
    get_put_eq: forall {V: esig K} (ev: env_t V) k v,
        getenv (putenv ev k v) k = v;
    get_put_neq: forall {V: esig K} (ev: env_t V) k k' v,
        k <> k' -> getenv (putenv ev k v) k' = getenv ev k' }.
Arguments Env: clear implicits.

Definition equiv {K} (E: Env K) {V: esig K} (ev1 ev2: E.(env_t) V) :=
  forall k: K, E.(getenv) ev1 k = E.(getenv) ev2 k.

Lemma equiv_refl {K} (E: Env K) {V: esig K} (ev: E.(env_t) V) :
  E.(equiv) ev ev.
Proof. firstorder. Qed.

Lemma equiv_eq {K} (E: Env K) {V: esig K} (ev1 ev2: E.(env_t) V) :
  E.(equiv) ev1 ev2 ->
  ev1 = ev2.
Proof.
  intros.
  rewrite <- (E.(create_getenv_id) ev1), <- (E.(create_getenv_id) ev2).
  apply create_funext; assumption.
Qed.

Definition map {K} (E: Env K) {V1 V2: esig K} (fn: forall k, V1 k -> V2 k)
           (ev1: E.(env_t) V1) : E.(env_t) V2 :=
  E.(create) (fun k => fn k (E.(getenv) ev1 k)).

Definition zip {K} (E: Env K) {V1 V2: esig K} (ev1: E.(env_t) V1) (ev2: E.(env_t) V2)
  : E.(env_t) (fun k => V1 k * V2 k)%type :=
  E.(create) (fun k => (E.(getenv) ev1 k, E.(getenv) ev2 k)).

Lemma getenv_zip {K} (E: Env K) {V1 V2: esig K} (ev1: E.(env_t) V1) (ev2: E.(env_t) V2) k :
  E.(getenv) (E.(zip) ev1 ev2) k = (E.(getenv) ev1 k, E.(getenv) ev2 k).
Proof.
  unfold zip; rewrite getenv_create; reflexivity.
Qed.

Definition map2 {K} (E: Env K) {V1 V2 V3: esig K} (fn: forall k, V1 k -> V2 k -> V3 k)
           (ev1: E.(env_t) V1) (ev2: E.(env_t) V2)
  : E.(env_t) V3 :=
  E.(create) (fun k => fn k (E.(getenv) ev1 k) (E.(getenv) ev2 k)).

Definition fold_right {K} (E: Env K) {V T} (f: forall k: K, V k -> T -> T) (ev: E.(env_t) V) (t0: T) :=
  List.fold_right (fun (k: K) (t: T) => f k (E.(getenv) ev k) t) t0 (@finite_elems K E.(finite_keys)).

Definition to_list {K} (E: Env K) {V} (ev: E.(env_t) V) :=
  E.(fold_right) (fun (k: K) (v: V k) (t: list { k: K & V k }) =>
                    (existT _ k v) :: t) ev List.nil.

Definition ContextEnv {K} `{FT: FiniteType K}: Env K.
  unshelve refine {| env_t V := context V finite_elems;
                     getenv {V} ctx k := cassoc (finite_index k) ctx;
                     putenv {V} ctx k v := creplace (finite_index k) v ctx;
                     create {V} fn := ccreate finite_elems (fun k _ => fn k) |}.
  - intros; rewrite <- ccreate_cassoc; apply ccreate_funext.
    intros; f_equal; apply member_NoDup; try typeclasses eauto; apply finite_nodup.
  - intros; apply ccreate_funext; eauto.
  - intros; apply cassoc_ccreate.
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
