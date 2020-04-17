Require Import Koika.Frontend.
Require Import DynamicIsolation.Tactics.

Record RLift {T} {A B: Type} {projA: A -> T} {projB: B -> T} := mk_RLift
  { rlift: A -> B
  ; pf_R_equal: forall (a: A), projB (rlift a) = projA a
  ; pf_inj_rlift: forall (a1 a2: A), rlift a1 = rlift a2 -> a1 = a2
  }.
Arguments RLift : clear implicits.

Ltac mk_rlift lift :=
  exists lift;
  match goal with
  | [ |- forall r, _ (lift r) = _ r ] =>  destruct r; auto
  | [ |- forall r1 r2, lift r1 = lift r2 -> r1 = r2] =>
      destruct r1; destruct r2; simpl; destruct_all_matches
 end.

Section ScheduleLift.
  Context {pos_t : Type} {rule_name_t : Type} {rule_name_t' : Type}.
  Context (lift: rule_name_t -> rule_name_t').

  Fixpoint lift_scheduler (sched: Syntax.scheduler pos_t rule_name_t)
                           : Syntax.scheduler pos_t rule_name_t' :=
    match sched with
    | Done => Done
    | Cons r s => Cons (lift r) (lift_scheduler s)
    | Try r s1 s2 => Try (lift r) (lift_scheduler s1) (lift_scheduler s2)
    | SPos pos s => SPos pos (lift_scheduler s)
    end.

  Fixpoint schedule_app {rule_name_t: Type} (sched1: scheduler) (sched2: scheduler) : scheduler :=
    match sched1 with
    | Done => sched2
    | Cons r s => Cons r (schedule_app s sched2)
    | Try r s1 s2 => Try r (schedule_app s1 sched2) (schedule_app s2 sched2)
    | SPos v s => SPos (rule_name_t := rule_name_t) v (schedule_app s sched2)
    end.

End ScheduleLift.

Section LiftAction.
  Context {reg_t reg_t' : Type}.
  Context {R: reg_t -> type} {R' : reg_t' -> type}.
  Context {Rlift: RLift type reg_t reg_t' R R'}.

  Context {fn_name_t fn_name_t' ext_fn_t ext_fn_t': Type}.

  Context {Sigma: ext_fn_t -> ExternalSignature}.
  Context {Sigma': ext_fn_t' -> ExternalSignature}.
  Context {Fnlift : RLift ExternalSignature ext_fn_t ext_fn_t' Sigma Sigma'}.
  Context {lift_fn_name : fn_name_t -> fn_name_t'}.

  Definition lift := Rlift.(rlift).

  Section Args.
    Context (lift_action:
               forall {sig: tsig var_t} {ret_ty: type},
                 @TypedSyntax.action pos_t var_t fn_name_t reg_t ext_fn_t R Sigma sig ret_ty ->
                 (@TypedSyntax.action pos_t var_t fn_name_t' reg_t' ext_fn_t' R' Sigma' sig ret_ty)).
    Fixpoint lift_args
      {sig: tsig var_t}
      {argspec: tsig var_t}
      (args: context (fun k_tau => @TypedSyntax.action pos_t var_t fn_name_t reg_t ext_fn_t R Sigma sig (snd k_tau))
                     argspec)
      : context (fun k_tau => @TypedSyntax.action pos_t var_t fn_name_t' reg_t' ext_fn_t' R' Sigma' sig (snd k_tau)) argspec :=
      (match args with
       | CtxEmpty => CtxEmpty
       | @CtxCons _ _ argspec k_tau arg args =>
         CtxCons k_tau (lift_action _ _ arg) (lift_args args)
       end).
  End Args.

  Fixpoint lift_action {sig: tsig var_t}
                       {ret_ty: type}
                       (action: @TypedSyntax.action pos_t var_t fn_name_t reg_t ext_fn_t R Sigma sig ret_ty)
                       : (@TypedSyntax.action pos_t var_t fn_name_t' reg_t' ext_fn_t' R' Sigma' sig ret_ty) :=
    match action in TypedSyntax.action _ _ _ _ _ sig ret_ty
          return TypedSyntax.action _ _ _ _ _ sig ret_ty with
    | Fail tau => Fail tau
    | @Var _ _ _ _ _ _ _ sig k tau m => @Var _ _ _ _ _ _ _ sig k tau m
    | Const cst => Const cst
    | Assign m ex => Assign m (lift_action ex)
    | Seq r1 r2 => Seq (lift_action r1) (lift_action r2)
    | Bind var ex body => Bind var (lift_action ex) (lift_action body)
    | If cond tbranch fbranch => If (lift_action cond)
                                   (lift_action tbranch)
                                   (lift_action fbranch)
    | @Read _ _ _ _ _ _ _ sig0 port idx =>
       rew [fun t : type => TypedSyntax.action pos_t var_t fn_name_t' R' Sigma' sig0 t] (Rlift.(pf_R_equal) idx) in
           (Read port (lift idx))
    | @Write _ _ _ _ _ _ _ sig0 port idx value =>
        Write port (lift idx)
              (rew<-[fun t: type => TypedSyntax.action pos_t var_t fn_name_t' R' Sigma' sig0 t]
                    (Rlift.(pf_R_equal) idx) in (lift_action value))
    | Unop fn arg1 => Unop fn (lift_action arg1)
    | Binop fn arg1 arg2 => Binop fn (lift_action arg1) (lift_action arg2)
    | @ExternalCall _ _ _ _ _ _ _ sig0 fn arg =>
        rew [fun e : ExternalSignature => TypedSyntax.action pos_t var_t fn_name_t' R' Sigma' sig0 (retSig e)]
            pf_R_equal Fnlift fn in
        ExternalCall (rlift Fnlift fn)
          (rew <- [fun t : ExternalSignature => TypedSyntax.action pos_t var_t fn_name_t' R' Sigma' sig0 (arg1Sig t)]
               pf_R_equal Fnlift fn in lift_action arg)

    | InternalCall fn args body =>
        InternalCall (lift_fn_name fn) (lift_args (@lift_action) args) (lift_action body)
    | APos pos a => APos pos (lift_action a)
    end.

    Definition lift_rule (rl: @TypedSyntax.rule pos_t var_t fn_name_t reg_t ext_fn_t R Sigma)
                         : @TypedSyntax.rule pos_t var_t fn_name_t' reg_t' ext_fn_t' R' Sigma' :=
      lift_action rl.

End LiftAction.

Arguments lift_action : clear implicits.
Arguments lift_rule : clear implicits.
