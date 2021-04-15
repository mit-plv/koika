(*! Utilities | Environments used to track variable bindings !*)
Require Import Koika.Common.
Require Export Koika.Member.

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

  Definition chd {k sig} (ctx: context (k :: sig)) : V k :=
    match ctx in (context sig')
          return match sig' with [] => unit | k :: _ => V k end with
    | CtxEmpty => tt
    | CtxCons _ v _ => v
    end.

  Definition ctl {k sig} (ctx: context (k :: sig)) : context sig :=
    match ctx in (context sig')
          return match sig' with [] => unit | _ :: sig => context sig end with
    | CtxEmpty => tt
    | CtxCons _ _ ctx' => ctx'
    end.

  Lemma ceqn {sig} (ctx: context sig)
    : match sig with
      | [] => fun ctx => ctx = CtxEmpty
      | k :: sig => fun ctx => ctx = CtxCons k (chd ctx) (ctl ctx)
      end ctx.
  Proof. destruct ctx; reflexivity. Defined.

  Fixpoint ccreate (sig: list K) (f: forall k, member k sig -> V k) : context sig :=
    match sig return (forall k, member k sig -> V k) -> context sig with
    | nil => fun _ => CtxEmpty
    | cons h t => fun f => CtxCons h (f h (MemberHd h t))
                               (ccreate t (fun k m => f k (MemberTl k h t m)))
    end f.

  Fixpoint cassoc {sig} {k} (m: member k sig)
           (ctx: context sig) {struct m} : V k :=
    match m in (member y l) return (context l -> V y) with
    | MemberHd k sig => fun ctx => chd ctx
    | MemberTl k k' sig m => fun ctx => cassoc m (ctl ctx)
    end ctx.

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
    - rewrite (ceqn ctx).
      reflexivity.
    - rewrite (ceqn ctx); cbn.
      rewrite IHsig; reflexivity.
  Qed.

  Fixpoint creplace {sig} {k} (m: member k sig) (v: V k)
           (ctx: context sig) {struct m} : context sig.
    destruct m.
    - eapply (CtxCons k v (ctl ctx)).
    - eapply (CtxCons k' (chd ctx) (creplace sig k m v (ctl ctx))).
  Defined.

  Lemma cassoc_creplace_eq {sig} :
    forall (ctx: context sig) {k} (m: member k sig) (v: V k),
      cassoc m (creplace m v ctx) = v.
  Proof.
    induction m; cbn; intros.
    - reflexivity.
    - rewrite IHm; reflexivity.
  Qed.

  Lemma cassoc_creplace_neq_idx {sig} :
    forall (ctx: context sig) {k k'} (m: member k sig) (m': member k' sig) (v: V k),
      member_idx m <> member_idx m' ->
      cassoc m' (creplace m v ctx) = cassoc m' ctx.
  Proof.
    induction m; cbn; intros; rewrite (ceqn ctx).
    - destruct (mdestruct m') as [ (-> & Heq) | (m'' & Heq)]; subst; cbn in *; subst; cbn in *.
      + congruence.
      + reflexivity.
    - destruct (mdestruct m') as [ (-> & Heq) | (m'' & Heq)]; subst; cbn in *; subst; cbn in *.
      + reflexivity.
      + rewrite IHm; eauto.
  Qed.

  Lemma cassoc_creplace_neq_k {sig} :
    forall (ctx: context sig) {k k'} (m: member k sig) (m': member k' sig) (v: V k),
      k <> k' ->
      cassoc m' (creplace m v ctx) = cassoc m' ctx.
  Proof.
    eauto using cassoc_creplace_neq_idx, member_idx_inj_k_contra.
  Qed.

  Global Instance EqDec_member sig (k: K) {EQ: EqDec K} : EqDec (member k sig).
  Proof.
    econstructor.
    induction sig; intros m1 m2.
    - destruct (mdestruct m1).
    - destruct (mdestruct m1) as [(-> & Heq) | (m1' & Heq)]; subst; cbn in *; subst; cbn;
        destruct (mdestruct m2) as [(eqn & Heq) | (m2' & Heq)];
        try (rewrite <- Eqdep_dec.eq_rect_eq_dec in Heq by apply eq_dec);
        unfold eq_type in *; subst; cbn in *; subst.
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

  Lemma cassoc_creplace_neq_members {sig} {EQ:EqDec K} :
    forall (ctx: context sig) {k } (m: member k sig) (m': member k sig) (v: V k),
      m <> m' ->
      cassoc m' (creplace m v ctx) = cassoc m' ctx.
  Proof.
    induction m; cbn; intros; rewrite (ceqn ctx).
    -
      destruct (mdestruct m') as [ (eqn & Heq) | (m'' & Heq)]; rewrite Heq in *.
      + rewrite <- Eqdep_dec.eq_rect_eq_dec in H by apply eq_dec.
        congruence.
      + reflexivity.
    -
      destruct (mdestruct m') as [ (eqn & Heq) | (m'' & Heq)]; subst; cbn in *; subst; cbn.
      + rewrite Heq in *. destruct eqn. reflexivity.
      + rewrite IHm; intuition congruence.
  Qed.

  Fixpoint capp {sig sig'} (ctx: context sig) (ctx': context sig'): context (sig ++ sig') :=
    match sig return context sig -> context (sig ++ sig') with
    | [] => fun _ => ctx'
    | k :: sig => fun ctx => CtxCons k (chd ctx) (capp (ctl ctx) ctx')
    end ctx.

  Fixpoint capp_nil_r {A} (l: list A) {struct l}:
    l ++ [] = l.
  Proof. destruct l; cbn; [ | f_equal ]; eauto. Defined.

  Lemma capp_empty:
    forall {sig} (ctx: context sig),
      capp ctx CtxEmpty =
      rew <- capp_nil_r sig in ctx.
  Proof.
    induction ctx; cbn.
    - reflexivity.
    - rewrite IHctx.
      rewrite eq_trans_refl_l.
      unfold eq_rect_r.
      rewrite eq_sym_map_distr.
      rewrite <- rew_map.
      destruct (eq_sym _); reflexivity.
  Qed.

  Fixpoint csplit {sig sig'} (ctx: context (sig ++ sig')): (context sig * context sig') :=
    match sig return context (sig ++ sig') -> (context sig * context sig') with
    | [] => fun ctx => (CtxEmpty, ctx)
    | k :: sig => fun ctx =>
                  let split := csplit (ctl ctx) in
                  (CtxCons k (chd ctx) (fst split), (snd split))
    end ctx.

  Lemma csplit_capp :
    forall {sig sig'} (ctx: context sig) (ctx': context sig'),
      csplit (capp ctx ctx') = (ctx, ctx').
  Proof.
    induction sig; cbn; intros; rewrite (ceqn ctx).
    - reflexivity.
    - rewrite IHsig; reflexivity.
  Qed.

  Definition infix_context {infix} (ctx': context infix)
             {sig sig'} (ctx: context (sig ++ sig')) :=
    capp (fst (csplit ctx)) (capp ctx' (snd (csplit ctx))).

  Lemma cassoc_mprefix:
    forall {k prefix sig} (m: member k sig)
      (ctx: context sig) (ctx': context prefix),
      cassoc (mprefix prefix m) (capp ctx' ctx) = cassoc m ctx.
  Proof. induction prefix; cbn; eauto. Qed.

  Lemma cassoc_minfix:
    forall {k sig sig'} (m: member k (sig ++ sig')) {infix}
      (ctx: context (sig ++ sig')) (ctx': context infix),
      cassoc (minfix infix m) (infix_context ctx' ctx) = cassoc m ctx.
  Proof.
    induction sig; cbn; intros.
    - apply cassoc_mprefix.
    - destruct (mdestruct m) as [(eqn & Heq) | (m' & Heq)];
        [ destruct eqn | ]; cbn in *; subst; rewrite (ceqn ctx).
      + reflexivity.
      + setoid_rewrite IHsig; reflexivity.
  Qed.

  Lemma creplace_mprefix:
    forall {k prefix sig} (m: member k sig)
      (ctx: context sig) (ctx': context prefix)
      (v : V k),
    creplace (mprefix prefix m) v (capp ctx' ctx) =
    capp ctx' (creplace m v ctx).
  Proof. induction prefix; cbn; eauto using f_equal. Qed.

  Lemma creplace_minfix:
    forall {k sig sig'} (m: member k (sig ++ sig')) {infix}
      (ctx: context (sig ++ sig')) (ctx': context infix) v,
      creplace (minfix infix m) v (infix_context ctx' ctx) =
      (infix_context ctx' (creplace m v ctx)).
  Proof.
    induction sig; cbn; intros.
    - apply creplace_mprefix.
    - destruct (mdestruct m) as [(eqn & Heq) | (m' & Heq)];
        [ destruct eqn | ]; cbn in *; subst; rewrite (ceqn ctx).
      + reflexivity.
      + setoid_rewrite IHsig; reflexivity.
  Qed.

  Lemma capp_as_infix':
    forall {sig sig'} (ctx: context sig) (ctx': context sig'),
      (rew <- [fun sig' => context (sig ++ sig')] capp_nil_r sig' in capp ctx ctx') =
      infix_context ctx' (rew <- capp_nil_r sig in ctx).
  Proof.
    unfold infix_context; intros.
    rewrite <- capp_empty.
    rewrite !csplit_capp; cbn.
    rewrite capp_empty.
    unfold eq_rect_r; cbn.
    destruct (eq_sym _); reflexivity.
  Qed.

  Lemma capp_as_infix:
    forall {sig sig'} (ctx: context sig) (ctx': context sig'),
      capp ctx ctx' =
      (rew [fun sig' => context (sig ++ sig')] capp_nil_r sig' in
          infix_context ctx' (rew <- capp_nil_r sig in ctx)).
  Proof.
    intros; rewrite <- capp_as_infix', rew_opp_r; reflexivity.
  Qed.
End Contexts.

Arguments context {K} V sig : assert.

Section Maps.
  Context {K K': Type}.
  Context {V: K -> Type} {V': K' -> Type}.
  Context (fK: K -> K').
  Context (fV: forall k, V k -> V' (fK k)).

  Fixpoint cmap {sig} (ctx: context V sig) {struct ctx} : context V' (List.map fK sig) :=
    match ctx in context _ sig return context V' (List.map fK sig) with
    | CtxEmpty => CtxEmpty
    | CtxCons k v ctx => CtxCons (fK k) (fV k v) (cmap ctx)
    end.

  Lemma cmap_creplace :
    forall {sig} (ctx: context V sig) {k} (m: member k sig) v,
      cmap (creplace m v ctx) =
      creplace (member_map fK m) (fV k v) (cmap ctx).
  Proof.
    induction ctx; cbn; intros.
    - destruct (mdestruct m).
    - destruct (mdestruct m) as [(-> & ->) | (? & ->)]; cbn in *.
      + reflexivity.
      + rewrite IHctx; reflexivity.
  Qed.

  Lemma cmap_cassoc :
    forall {sig} (ctx: context V sig) {k} (m: member k sig),
      cassoc (member_map fK m) (cmap ctx) =
      fV k (cassoc m ctx).
  Proof.
    induction ctx; cbn; intros.
    - destruct (mdestruct m).
    - destruct (mdestruct m) as [(-> & ->) | (? & ->)]; cbn in *.
      + reflexivity.
      + rewrite IHctx; reflexivity.
  Qed.

  Lemma cmap_ctl :
    forall {k sig} (ctx: context V (k :: sig)),
      cmap (ctl ctx) = ctl (cmap ctx).
  Proof.
    intros; rewrite (ceqn ctx); reflexivity.
  Qed.
End Maps.


Section ValueMaps.
  Context {K: Type}.
  Context {V: K -> Type} {V': K -> Type}.
  Context (fV: forall k, V k -> V' k).

  Fixpoint cmapv {sig} (ctx: context V sig) {struct ctx} : context V' sig :=
    match ctx in context _ sig return context V' sig with
    | CtxEmpty => CtxEmpty
    | CtxCons k v ctx => CtxCons k (fV k v) (cmapv ctx)
    end.

  Lemma cmapv_creplace :
    forall {sig} (ctx: context V sig) {k} (m: member k sig) v,
      cmapv (creplace m v ctx) =
      creplace m (fV k v) (cmapv ctx).
  Proof.
    induction ctx; cbn; intros.
    - destruct (mdestruct m).
    - destruct (mdestruct m) as [(-> & ->) | (? & ->)]; cbn in *.
      + reflexivity.
      + rewrite IHctx; reflexivity.
  Qed.

  Lemma cmapv_cassoc :
    forall {sig} (ctx: context V sig) {k} (m: member k sig),
      cassoc m (cmapv ctx) =
      fV k (cassoc m ctx).
  Proof.
    induction ctx; cbn; intros.
    - destruct (mdestruct m).
    - destruct (mdestruct m) as [(-> & ->) | (? & ->)]; cbn in *.
      + reflexivity.
      + rewrite IHctx; reflexivity.
  Qed.

  Lemma cmapv_ctl :
    forall {k sig} (ctx: context V (k :: sig)),
      cmapv (ctl ctx) = ctl (cmapv ctx).
  Proof.
    intros; rewrite (ceqn ctx); reflexivity.
  Qed.
End ValueMaps.

Section Folds.
  Context {K: Type}.
  Context {V: K -> Type}.

  Section foldl.
    Context {T: Type}.
    Context (f: forall (k: K) (v: V k) (acc: T), T).

    Fixpoint cfoldl {sig} (ctx: context V sig) (init: T) :=
      match ctx with
      | CtxEmpty => init
      | CtxCons k v ctx => cfoldl ctx (f k v init)
      end.

    Definition cfoldl' {sig} (ctx: context V sig) (init: T) :=
      match sig return context V sig -> T with
      | [] => fun _ => init
      | k :: sig => fun ctx => cfoldl (ctl ctx) (f k (chd ctx) init)
      end ctx.
  End foldl.

  Section foldr.
    Context {T: list K -> Type}.
    Context (f: forall (sg: list K) (k: K) (v: V k), T sg -> T (k :: sg)).

    Fixpoint cfoldr {sig} (ctx: context V sig) (init: T []) :=
      match ctx with
      | CtxEmpty => init
      | CtxCons k v ctx => f _ k v (cfoldr ctx init)
      end.

    Fixpoint cfoldr' {sig} (ctx: context V sig) (init: T []) :=
      match sig return context V sig -> T sig with
      | [] => fun _ => init
      | k :: sig => fun ctx => f sig k (chd ctx) (cfoldr' (ctl ctx) init)
      end ctx.
  End foldr.
End Folds.

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
Arguments getenv K e V / !env.
Arguments putenv K e V / !env.

Definition equiv {K} (E: Env K) {V: esig K} (ev1 ev2: E.(env_t) V) :=
  forall k: K, E.(getenv) ev1 k = E.(getenv) ev2 k.

Lemma equiv_refl {K} (E: Env K) {V: esig K} (ev: E.(env_t) V) :
  equiv E ev ev.
Proof. firstorder. Qed.

Lemma equiv_eq {K} (E: Env K) {V: esig K} (ev1 ev2: E.(env_t) V) :
  equiv E ev1 ev2 ->
  ev1 = ev2.
Proof.
  intros.
  rewrite <- (E.(create_getenv_id) ev1), <- (E.(create_getenv_id) ev2).
  apply create_funext; assumption.
Qed.

Definition update {K} (E: Env K) {V: esig K}
           (ev: E.(env_t) V) (k: K) (fn: V k -> V k) : E.(env_t) V :=
  E.(putenv) ev k (fn (E.(getenv) ev k)).

Definition map {K} (E: Env K) {V1 V2: esig K} (fn: forall k, V1 k -> V2 k)
           (ev1: E.(env_t) V1) : E.(env_t) V2 :=
  E.(create) (fun k => fn k (E.(getenv) ev1 k)).

Lemma getenv_map {K} (E: Env K) {V1 V2: esig K} (fn: forall k, V1 k -> V2 k) :
    forall ev k, E.(getenv) (map E fn ev) k = fn k (E.(getenv) ev k).
Proof. intros; unfold map; rewrite getenv_create; reflexivity. Qed.

Definition zip {K} (E: Env K) {V1 V2: esig K} (ev1: E.(env_t) V1) (ev2: E.(env_t) V2)
  : E.(env_t) (fun k => V1 k * V2 k)%type :=
  E.(create) (fun k => (E.(getenv) ev1 k, E.(getenv) ev2 k)).

Lemma getenv_zip {K} (E: Env K) {V1 V2: esig K} (ev1: E.(env_t) V1) (ev2: E.(env_t) V2) k :
  E.(getenv) (zip E ev1 ev2) k = (E.(getenv) ev1 k, E.(getenv) ev2 k).
Proof.
  unfold zip; rewrite getenv_create; reflexivity.
Qed.

Definition unzip {K} (E: Env K) {V1 V2: esig K} (ev: E.(env_t) (fun k => V1 k * V2 k)%type)
  : (E.(env_t) V1 * E.(env_t) V2) :=
  (E.(create) (fun k => fst (E.(getenv) ev k)),
   E.(create) (fun k => snd (E.(getenv) ev k))).

Lemma getenv_unzip_1 {K} (E: Env K) {V1 V2: esig K} (ev: E.(env_t) (fun k => V1 k * V2 k)%type) k :
  E.(getenv) (fst (unzip E ev)) k = fst (E.(getenv) ev k).
Proof.
  unfold unzip; cbn; rewrite getenv_create; reflexivity.
Qed.

Lemma getenv_unzip_2 {K} (E: Env K) {V1 V2: esig K} (ev: E.(env_t) (fun k => V1 k * V2 k)%type) k :
  E.(getenv) (snd (unzip E ev)) k = snd (E.(getenv) ev k).
Proof.
  unfold unzip; cbn; rewrite getenv_create; reflexivity.
Qed.

Definition map2 {K} (E: Env K) {V1 V2 V3: esig K} (fn: forall k, V1 k -> V2 k -> V3 k)
           (ev1: E.(env_t) V1) (ev2: E.(env_t) V2)
  : E.(env_t) V3 :=
  E.(create) (fun k => fn k (E.(getenv) ev1 k) (E.(getenv) ev2 k)).

Lemma getenv_map2 {K} (E: Env K) {V1 V2 V3: esig K} (fn: forall k, V1 k -> V2 k -> V3 k) :
    forall ev1 ev2 k, E.(getenv) (map2 E fn ev1 ev2) k = fn k (E.(getenv) ev1 k) (E.(getenv) ev2 k).
Proof. intros; unfold map2; rewrite getenv_create; reflexivity. Qed.

Definition fold_right {K} (E: Env K) {V T} (f: forall k: K, V k -> T -> T) (ev: E.(env_t) V) (t0: T) :=
  List.fold_right (fun (k: K) (t: T) => f k (E.(getenv) ev k) t) t0 (@finite_elements K E.(finite_keys)).

Definition to_list {K} (E: Env K) {V} (ev: E.(env_t) V) :=
  fold_right E (fun (k: K) (v: V k) (t: list { k: K & V k }) =>
                    (existT _ k v) :: t) ev List.nil.

Definition to_alist {K} (E: Env K) {V} (ev: E.(env_t) (fun _ => V)) :=
  fold_right E (fun (k: K) (v: V) (t: list (K * V)) => (k, v) :: t) ev List.nil.

Definition finite_member {T} {FT: FiniteType T} (t: T) :
  member t finite_elements.
Proof.
  eapply nth_member.
  apply finite_surjective.
Defined.

Definition ContextEnv {K} {FT: FiniteType K}: Env K.
  unshelve refine {| env_t V := context V finite_elements;
                     getenv {V} ctx k := cassoc (finite_member k) ctx;
                     putenv {V} ctx k v := creplace (finite_member k) v ctx;
                     create {V} fn := ccreate finite_elements (fun k _ => fn k) |}.
  - intros; rewrite <- ccreate_cassoc; apply ccreate_funext.
    intros; f_equal; apply member_NoDup; try typeclasses eauto; apply finite_nodup.
  - intros; apply ccreate_funext; eauto.
  - intros; apply cassoc_ccreate.
  - intros; apply cassoc_creplace_eq.
  - intros; apply cassoc_creplace_neq_k; eassumption.
Defined.

Notation "env .[ idx ]" := (getenv ContextEnv env idx) (at level 1, format "env .[ idx ]").
