(*! Frontend | Type inference and typechecking !*)
Require Import
        Koika.Common Koika.Environments
        Koika.Syntax Koika.TypedSyntax Koika.SyntaxMacros
        Koika.Desugaring Koika.ErrorReporting.

Section ErrorReporting.
  Context {pos_t var_t fn_name_t reg_t ext_fn_t: Type}.
  Context {R: reg_t -> type}
          {Sigma: ext_fn_t -> ExternalSignature}.

  Definition lift_basic_error_message
             (pos: pos_t) {sig tau} (e: action pos_t var_t fn_name_t R Sigma sig tau)
             (err: basic_error_message) : error pos_t var_t fn_name_t :=
    {| epos := pos;
       emsg := BasicError err;
       esource := ErrSrc e |}.

  Definition lift_fn1_tc_result
             {A sig tau}
             pos (e: action pos_t var_t fn_name_t R Sigma sig tau)
             (r: result A fn_tc_error)
    : result A (error pos_t var_t fn_name_t) :=
    result_map_failure (fun '(side, err) => lift_basic_error_message pos e err) r.

  Definition lift_fn2_tc_result
             {A sig1 tau1 sig2 tau2}
             pos1 (e1: action pos_t var_t fn_name_t R Sigma sig1 tau1)
             pos2 (e2: action pos_t var_t fn_name_t R Sigma sig2 tau2)
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

  Notation action := (action pos_t var_t fn_name_t R Sigma).
  Notation rule := (rule pos_t var_t fn_name_t R Sigma).
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

    Notation EX Px := (existT _ _ Px).

    Definition actpos {reg_t ext_fn_t} pos (e: uaction reg_t ext_fn_t) :=
      match e with
      | UAPos p _ => p
      | _ => pos
      end.

    Fixpoint assert_argtypes' {T} {sig} (src: T) nexpected (fn_name: fn_name_t) pos
             (args_desc: tsig var_t)
             (args: list (pos_t * {tau : type & action sig tau}))
      : result (context (K := (var_t * type)) (fun k_tau => action sig (snd k_tau)) args_desc) :=
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
      : result (context (K := (var_t * type)) (fun k_tau => action sig (snd k_tau)) args_desc) :=
      assert_argtypes' src (List.length args_desc) fn_name pos args_desc args.

    Fixpoint type_action
             (pos: pos_t) (sig: tsig var_t)
             (e: uaction reg_t ext_fn_t) {struct e}
      : result ({ tau: type & action sig tau }) :=
      match e with
      | UError err => Failure err
      | USugar _ => Failure (mkerror pos SugaredConstructorInAst e)
      | UFail tau => Success (EX (Fail tau))
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
        let/res args_ctx := assert_argtypes e fn.(int_name) pos (List.rev fn.(int_argspec)) (List.rev tc_args_w_pos) in

        let/res fn_body' := type_action (actpos pos fn.(int_body)) (List.rev fn.(int_argspec)) fn.(int_body) in
        let/res fn_body' := cast_action (actpos pos fn.(int_body)) fn.(int_retSig) (``fn_body') in

        Success (EX (TypedSyntax.InternalCall fn.(int_name) args_ctx fn_body'))
      | UUnop fn arg1 =>
        let pos1 := actpos pos arg1 in
        let/res arg1' := type_action pos sig arg1 in
        let/res fn := lift_fn1_tc_result pos1 ``arg1' (PrimTypeInference.tc1 fn `arg1') in
        let/res arg1' := cast_action pos1 (PrimSignatures.Sigma1 fn).(arg1Sig) (``arg1') in
        Success (EX (Unop fn arg1'))
      | UBinop fn arg1 arg2 =>
        let pos1 := actpos pos arg1 in
        let pos2 := actpos pos arg2 in
        let/res arg1' := type_action pos sig arg1 in
        let/res arg2' := type_action pos sig arg2 in
        let/res fn := lift_fn2_tc_result pos1 ``arg1' pos2 ``arg2' (PrimTypeInference.tc2 fn `arg1' `arg2') in
        let/res arg1' := cast_action pos1 (PrimSignatures.Sigma2 fn).(arg1Sig) (``arg1') in
        let/res arg2' := cast_action pos2 (PrimSignatures.Sigma2 fn).(arg2Sig) (``arg2') in
        Success (EX (Binop fn arg1' arg2'))
      | UExternalCall fn arg1 =>
        let pos1 := actpos pos arg1 in
        let/res arg1' := type_action pos1 sig arg1 in
        let/res arg1' := cast_action pos1 (Sigma fn).(arg1Sig) (``arg1') in
        Success (EX (ExternalCall fn arg1'))
      | UAPos pos e =>
        let/res e := type_action pos sig e in
        Success (EX (APos pos ``e))
      end.

    Definition tc_action (pos: pos_t)
               (sig: tsig var_t) (expected_tau: type)
               (e: uaction reg_t ext_fn_t) : result (action sig expected_tau) :=
      let/res a := type_action pos sig e in
      cast_action pos expected_tau (``a).

    Definition tc_rule (pos: pos_t) (e: uaction reg_t ext_fn_t) : result rule :=
      tc_action pos [] unit_t e.
  End Action.
End TypeInference.
