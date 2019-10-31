Require Import
        Koika.Common Koika.Environments
        Koika.Syntax Koika.TypedSyntax Koika.SyntaxMacros
        Koika.Desugaring Koika.ErrorReporting.
Require Import Coq.Lists.List.
Import ListNotations.

Section ErrorReporting.
  Context {pos_t var_t fn_name_t reg_t ext_fn_t: Type}.
  Context {R: reg_t -> type}
          {Sigma: ext_fn_t -> ExternalSignature}.

  Definition lift_basic_error_message
             (pos: pos_t) {sig tau} (e: action pos_t var_t R Sigma sig tau)
             (err: basic_error_message) : error pos_t var_t fn_name_t :=
    {| epos := pos;
       emsg := BasicError err;
       esource := ErrSrc e |}.

  Definition lift_fn1_tc_result
             {A sig tau}
             pos (e: action pos_t var_t R Sigma sig tau)
             (r: result A fn_tc_error)
    : result A (error pos_t var_t fn_name_t) :=
    result_map_failure (fun '(side, err) => lift_basic_error_message pos e err) r.

  Definition lift_fn2_tc_result
             {A sig1 tau1 sig2 tau2}
             pos1 (e1: action pos_t var_t R Sigma sig1 tau1)
             pos2 (e2: action pos_t var_t R Sigma sig2 tau2)
             (r: result A fn_tc_error)
    : result A (error pos_t var_t fn_name_t) :=
    result_map_failure (fun '(side, err) =>
                          match side with
                          | Arg1 => lift_basic_error_message pos1 e1 err
                          | Arg2 => lift_basic_error_message pos2 e2 err
                          end) r.
End ErrorReporting.

Section TypeInference.
  Context {pos_t rule_name_t fn_name_t var_t reg_t ext_fn_t: Type}.
  Context {var_t_eq_dec: EqDec var_t}.

  Context (R: reg_t -> type).
  Context (Sigma: ext_fn_t -> ExternalSignature).

  Notation usugar := (usugar pos_t var_t fn_name_t).
  Notation uaction := (uaction pos_t var_t fn_name_t).
  Notation uscheduler := (uscheduler pos_t rule_name_t).

  Notation action := (action pos_t var_t R Sigma).
  Notation rule := (rule pos_t var_t R Sigma).
  Notation scheduler := (scheduler pos_t rule_name_t).

  Section Action.
    Notation error := (error pos_t var_t fn_name_t).
    Notation error_message := (error_message var_t fn_name_t).
    Notation result A := (result A error).

    Definition mkerror {T} pos msg (src: T) : error :=
      {| epos := pos; emsg := msg; esource := ErrSrc src |}.

    Notation "` x" := (projT1 x) (at level 0).
    Notation "`` x" := (projT2 x) (at level 0).

    Definition cast_action' (pos: pos_t)
               {sig tau1} tau2 (e: action sig tau1) (emsg: error_message)
    : result (action sig tau2).
    Proof.
      destruct (eq_dec tau1 tau2); subst.
      - exact (Success e).
      - exact (Failure (mkerror pos emsg e)).
    Defined.

    Definition cast_action pos {sig tau1} tau2 (e: action sig tau1) :=
      cast_action' pos tau2 e (BasicError (TypeMismatch tau1 tau2)).

    Definition cast_rule (pos: pos_t) {tau} (e: action [] tau) :=
      cast_action' pos (bits_t 0) e (IncorrectRuleType tau).

    Notation EX Px := (existT _ _ Px).

    Fixpoint actpos {reg_t ext_fn_t} pos (e: uaction reg_t ext_fn_t) :=
      match e with
      | UAPos p _ => p
      | _ => pos
      end.

    Fixpoint assert_argtypes' {T} {sig} (src: T) nexpected (fn_name: fn_name_t) pos
             (args_desc: tsig var_t)
             (args: list (pos_t * {tau : type & action sig tau}))
      : result (context (K := (var_t * type)) (fun '(_, tau) => action sig tau) args_desc) :=
      match args_desc, args with
      | [], [] => Success CtxEmpty
      | [], _ => Failure (mkerror pos (TooManyArguments fn_name nexpected (List.length args)) src)
      | _, [] => Failure (mkerror pos (TooFewArguments fn_name nexpected (List.length args_desc)) src)
      | (name1, tau1) :: fn_sig, (pos1, arg1) :: args =>
        let/res arg1 := cast_action pos1 tau1 ``arg1  in
        let/res ctx := assert_argtypes' src nexpected fn_name pos fn_sig args in
        Success (CtxCons (name1, tau1) arg1 ctx)
      end.

    Definition assert_argtypes {T} {sig}
               (src: T)
               (fn_name: fn_name_t) pos
               (args_desc: tsig var_t)
               (args: list (pos_t * {tau : type & action sig tau}))
      : result (context (K := (var_t * type)) (fun '(_, tau) => action sig tau) args_desc) :=
      assert_argtypes' src (List.length args_desc) fn_name pos args_desc args.

    Fixpoint type_action
             (pos: pos_t) (sig: tsig var_t)
             (e: uaction reg_t ext_fn_t) {struct e}
      : result ({ tau: type & action sig tau }) :=
      match e with
      | UError err => Failure err
      | USugar _ => Failure (mkerror pos SugaredConstructorInAst e)
      | UFail n => Success (EX (Fail (bits_t n)))
      | UVar var =>
        let/res tau_m := opt_result (assoc var sig) (mkerror pos (UnboundVariable var) e) in
        Success (EX (Var ``tau_m))
      | UConst cst => Success (EX (Const cst))
      | UAssign var ex =>
        let/res tau_m := opt_result (assoc var sig) (mkerror pos (UnboundVariable var) e) in
        let/res ex' := type_action pos sig ex in
        let/res ex' := cast_action (actpos pos ex) `tau_m (``ex') in
        Success (EX (Assign (k := var) (tau := `tau_m) ``tau_m ex'))
      | USeq r1 r2 =>
        let/res r1' := type_action pos sig r1 in
        let/res r1' := cast_action (actpos pos r1) unit_t (``r1') in
        let/res r2' := type_action pos sig r2 in
        Success (EX (Seq r1' ``r2'))
      | UBind v ex body =>
        let/res ex := type_action pos sig ex in
        let/res body := type_action pos ((v, `ex) :: sig) body in
        Success (EX (Bind v ``ex ``body))
      | UIf cond tbranch fbranch =>
        let/res cond' := type_action pos sig cond in
        let/res cond' := cast_action (actpos pos cond) (bits_t 1) (``cond') in
        let/res tbranch' := type_action pos sig tbranch in
        let/res fbranch' := type_action pos sig fbranch in
        let/res fbranch' := cast_action (actpos pos fbranch) (`tbranch') (``fbranch') in
        Success (EX (If cond' ``tbranch' fbranch'))
      | URead port idx => Success (EX (Read port idx))
      | UWrite port idx value =>
        let/res value' := type_action pos sig value in
        let/res value' := cast_action (actpos pos value) (R idx) (``value') in
        Success (EX (Write port idx value'))
      | UInternalCall fn args =>
        let/res tc_args := result_list_map (type_action pos sig) args in
        let arg_positions := List.map (actpos pos) args in
        let tc_args_w_pos := List.combine arg_positions tc_args in
        let/res arg_ctx := assert_argtypes e fn.(int_name) pos fn.(int_argspec) tc_args_w_pos in
        let/res fn_body' := type_action (actpos pos fn.(int_body)) fn.(int_argspec) fn.(int_body) in
        let/res fn_body' := cast_action (actpos pos fn.(int_body)) fn.(int_retType) (``fn_body') in
        Success (EX (InternalCall sig fn.(int_argspec) fn_body' arg_ctx))
      | UUnop fn arg1 =>
        let pos1 := actpos pos arg1 in
        let/res arg1' := type_action pos sig arg1 in
        let/res fn := lift_fn1_tc_result pos1 ``arg1' (PrimTypeInference.tc1 fn `arg1') in
        let/res arg1' := cast_action pos1 (PrimSignatures.Sigma1 fn).(arg1Type) (``arg1') in
        Success (EX (Unop fn arg1'))
      | UBinop fn arg1 arg2 =>
        let pos1 := actpos pos arg1 in
        let pos2 := actpos pos arg2 in
        let/res arg1' := type_action pos sig arg1 in
        let/res arg2' := type_action pos sig arg2 in
        let/res fn := lift_fn2_tc_result pos1 ``arg1' pos2 ``arg2' (PrimTypeInference.tc2 fn `arg1' `arg2') in
        let/res arg1' := cast_action pos1 (PrimSignatures.Sigma2 fn).(arg1Type) (``arg1') in
        let/res arg2' := cast_action pos2 (PrimSignatures.Sigma2 fn).(arg2Type) (``arg2') in
        Success (EX (Binop fn arg1' arg2'))
      | UExternalCall fn arg1 =>
        let pos1 := actpos pos arg1 in
        let/res arg1' := type_action pos1 sig arg1 in
        let/res arg1' := cast_action pos1 (Sigma fn).(arg1Type) (``arg1') in
        Success (EX (ExternalCall fn arg1'))
      | UAPos pos e =>
        let/res e := type_action pos sig e in
        Success (EX (APos pos ``e))
      end.

    Definition type_rule (pos: pos_t) (e: uaction reg_t ext_fn_t) : result rule :=
      let/res rl := type_action pos [] e in
      cast_rule pos (``rl).
  End Action.

  Section Scheduler.
    Fixpoint type_scheduler
             (pos: pos_t)
             (s: uscheduler): scheduler :=
      match s with
      | UDone =>
        Done
      | UTry r s1 s2 =>
        let s1 := type_scheduler pos s1 in
        let s2 := type_scheduler pos s2 in
        Try r s1 s2
      | UCons r s =>
        let s := type_scheduler pos s in
        Cons r s
      | USPos pos s =>
        SPos pos (type_scheduler pos s)
      end.
  End Scheduler.
End TypeInference.

(*   Hint Resolve (@env_related_putenv _ _ _ GammaEnv): types. *)
(*   Hint Resolve fenv_related_putenv: types. *)
(*   Hint Constructors HasType : types. *)
(*   Hint Extern 0 => unfold id : types. *)

(*   Ltac t := *)
(*     repeat match goal with *)
(*            | _ => reflexivity *)
(*            | _ => progress cleanup_step *)
(*            | [ H: opt_bind ?x _ = Some _ |- _ ] => *)
(*              destruct x eqn:?; cbn in H; [ | discriminate] *)
(*            | [ H: match ?x with _ => _ end = Some _ |- _ ] => *)
(*              destruct x eqn:? *)
(*            | [ H: env_related (Env := ?Env) ?f ?tenv ?env, *)
(*                   H': getenv ?env ?k = Some ?v |- _ ] => *)
(*              pose_once (and_fst H k v) H' *)
(*            | [ H: forall Gamma gamma tau, _ -> _ = Some _ -> _, *)
(*                  H': type_action ?Gamma ?r = Some ?tau |- _ ] => *)
(*              specialize (H Gamma _ tau ltac:(eauto with types) H') *)
(*            | [ H: MaxType ?R ?Sigma ?Gamma ?r ?tau |- _ ] => *)
(*              pose_once (MaxType_HasType R Sigma Gamma r tau) H *)
(*            | _ => solve [econstructor] || econstructor; solve [eauto 5 with types] *)
(*            end. *)

(*    Lemma type_action_correct_call: *)
(*     forall sigma v, *)
(*       env_related id v R -> *)
(*       env_related id sigma Sigma -> *)
(*      forall args argSizes, *)
(*        length args = length argSizes -> *)
(*        forall Gamma gamma, *)
(*          env_related id gamma Gamma -> *)
(*          List.Forall *)
(*            (fun r : rule var_t fn_t => *)
(*               forall Gamma gamma tau, *)
(*                 env_related id gamma Gamma -> type_action Gamma r = Some tau -> MaxType v sigma gamma r tau) args -> *)
(*          fold_right2 *)
(*            (fun arg argSize acc => *)
(*               acc && *)
(*                   match type_action Gamma arg with *)
(*                   | Some tau => if type_le_dec (bits_t argSize) tau then true else false *)
(*                   | None => false *)
(*                   end) true args argSizes = true -> *)
(*          fold_right2 *)
(*            (fun (arg : rule var_t fn_t) (argSize : nat) (acc : Prop) => acc /\ HasType v sigma gamma arg (bits_t argSize)) *)
(*            True args argSizes. *)
(*    Proof. *)
(*      induction args; destruct argSizes; cbn in *; *)
(*        inversion 1; intros ? ? ?; inversion 1; subst; intros Heq. *)
(*      - eauto. *)
(*      - destruct type_action eqn:?; *)
(*          apply andb_prop in Heq; repeat cleanup_step. *)
(*        destruct type_le_dec; try discriminate. *)
(*        eauto using MaxType_HasType. *)
(*    Qed. *)

(*   Lemma type_action_correct : *)
(*     forall sigma v, *)
(*       env_related id v R -> *)
(*       env_related id sigma Sigma -> *)
(*       forall (r: rule var_t fn_t) (Gamma: GammaEnv.(env_t)) gamma (tau: type), *)
(*         env_related id gamma Gamma -> *)
(*         type_action Gamma r = Some tau -> *)
(*         MaxType v sigma gamma r tau. *)
(*   Proof. *)
(*     induction r using rule_ind'; cbn; intros; t. *)

(*     econstructor; eauto. *)
(*     eapply fold_right2_forall2; *)
(*       eauto using type_action_correct_call. *)
(*   Qed. *)

(*   Lemma forall2_cons_inv {A B} (P: A -> B -> Prop) : *)
(*     forall a b la lb, *)
(*       forall2 P (a :: la) (b :: lb) -> *)
(*       P a b /\ forall2 P la lb. *)
(*   Proof. *)
(*     intros * H; apply forall2_fold_right2 in H; destruct H as (H & ?). *)
(*     apply fold_right2_forall2 in H; intuition. *)
(*   Qed. *)

(*   Ltac tcomplete_step := *)
(*     match goal with *)
(*     | _ => progress subst *)
(*     | _ => progress intros *)
(*     | [ H: fn ?gamma ?k ?v, H': fenv_related ?gamma ?Gamma |- _ ] => *)
(*       try pose_once H' k v; *)
(*       match goal with *)
(*       | [ H'': fn gamma k v <-> getenv Gamma k = Some v |- _ ] => *)
(*         pose_once (and_fst H'') H *)
(*       end *)
(*     | [ H: HasType _ _ _ _ _ |- _ ] => *)
(*       apply HasType_MaxType in H; destruct H as (? & ? & ?) *)
(*     | [ H: ?x = Some _ |- opt_bind ?x _ = _ ] => *)
(*       rewrite H; cbn *)
(*     | [ H: (forall _ _ , _ -> forall _, _ -> type_action _ ?r  = Some _)  |- *)
(*         opt_bind (type_action _ ?r) _ = Some _ ] => *)
(*       erewrite H by eauto with types; cbn *)
(*     | [ H: type_le ?x ?y |- context[type_le_dec ?x ?y] ] => *)
(*       destruct type_le_dec; try tauto *)
(*     | _ => cleanup_step *)
(*     end. *)

(*   Lemma type_action_complete_call: *)
(*     forall (sigma : fenv fn_t ExternalSignature) (v : fenv nat nat) (args : list (rule var_t fn_t)) argSizes, *)
(*       length args = length argSizes -> *)
(*       List.Forall *)
(*         (fun r : rule var_t fn_t => *)
(*            forall (gamma : fenv var_t type) (tau : type), *)
(*              MaxType v sigma gamma r tau -> *)
(*              forall Gamma : env_t GammaEnv, fenv_related gamma Gamma -> type_action Gamma r = Some tau) args -> *)
(*       forall (gamma : fenv var_t type) (Gamma : env_t GammaEnv), *)
(*         forall2 (fun (arg : rule var_t fn_t) (argSize : nat) => HasType v sigma gamma arg (bits_t argSize)) args argSizes -> *)
(*         fenv_related gamma Gamma -> *)
(*         forall b : bool, *)
(*           fold_right2 *)
(*             (fun (arg : rule var_t fn_t) (argSize : nat) (acc : bool) => *)
(*              acc && *)
(*              match type_action Gamma arg with *)
(*              | Some tau0 => if type_le_dec (bits_t argSize) tau0 then true else false *)
(*              | None => false *)
(*              end) b args argSizes = b. *)
(*   Proof. *)
(*     induction args; cbn; destruct argSizes; inversion 1; intros HForall * Hforall2 **. *)
(*     - reflexivity. *)
(*     - inversion HForall as [ | x l Hinfer HForall']; subst. *)

(*       apply forall2_cons_inv in Hforall2. *)

(*       repeat tcomplete_step. *)
(*       erewrite Hinfer; eauto. *)
(*       repeat tcomplete_step. *)
(*       rewrite Bool.andb_true_r. *)
(*       eauto. *)
(*   Qed. *)

(*   Lemma type_action_complete : *)
(*     forall sigma v, *)
(*       fenv_related v R -> *)
(*       fenv_related sigma Sigma -> *)
(*       forall (r: rule var_t fn_t) gamma (tau: type), *)
(*         MaxType v sigma gamma r tau -> *)
(*         forall (Gamma: GammaEnv.(env_t)), *)
(*         fenv_related gamma Gamma -> *)
(*         type_action Gamma r = Some tau. *)
(*   Proof. *)
(*     induction r using rule_ind'; cbn; inversion 1; *)
(*       repeat tcomplete_step; eauto using f_equal with types. *)

(*     - destruct PeanoNat.Nat.eq_dec; try tauto. *)
(*       erewrite type_action_complete_call; eauto. *)
(*   Qed. *)

(*   Theorem TypeInference : *)
(*     forall Gamma (r: rule var_t fn_t), *)
(*       match type_action Gamma r with *)
(*       | Some tau => HasType (tenv_of_env id R) (tenv_of_env id Sigma) (tenv_of_env id Gamma) r tau *)
(*       | None => forall tau, not (HasType (tenv_of_env id R) (tenv_of_env id Sigma) (tenv_of_env id Gamma) r tau) *)
(*       end. *)
(*   Proof. *)
(*     intros; destruct type_action eqn:?. *)
(*     - eapply MaxType_HasType. *)
(*       + eapply type_action_correct; *)
(*           try eapply tenv_of_env_related; eauto. *)
(*       + eauto with types. *)
(*     - intros tau Habs. *)
(*       eapply HasType_MaxType in Habs. *)
(*       destruct Habs as (? & Habs & Hle). *)
(*       eapply type_action_complete in Habs; *)
(*         try eapply tenv_of_env_frelated. *)
(*       congruence. *)
(*   Qed. *)
(* End TypeInference. *)