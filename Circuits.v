Require Export SGA.Common SGA.Environments.
Require Import SGA.Syntax SGA.TypedSyntax.
Require Import Coq.Strings.String.
Open Scope string_scope.

Record CExternalSignature :=
  CFunSig { arg1Size: nat; arg2Size: nat; retSize: nat }.

Definition CExternalSignature_denote (sig: CExternalSignature) :=
  bits sig.(arg1Size) -> bits sig.(arg2Size) -> bits sig.(retSize).

Definition CExternalSignature_of_ExternalSignature (c: ExternalSignature) :=
  {| arg1Size := type_sz c.(arg1Type);
     arg2Size := type_sz c.(arg2Type);
     retSize := type_sz c.(retType) |}.

Section Circuit.
  Context {reg_t fn_t: Type}.
  Context {R: reg_t -> nat}.
  Context {Sigma: fn_t -> CExternalSignature}.

  Inductive circuit : nat -> Type :=
  | CNot (c: circuit 1): circuit 1
  | CAnd (c1 c2: circuit 1): circuit 1
  | COr (c1 c2: circuit 1): circuit 1
  | CMux {sz} (select: circuit 1) (c1 c2: circuit sz): circuit sz
  | CConst {sz} (cst: bits sz): circuit sz
  | CReadRegister (reg: reg_t): circuit (R reg)
  | CExternal (idx: fn_t)
              (a1: circuit (Sigma idx).(arg1Size))
              (a2: circuit (Sigma idx).(arg2Size))
    : circuit (Sigma idx).(retSize)
  | CAnnot {sz} (annot: string) (c: circuit sz) : circuit sz.
End Circuit.

Arguments circuit {reg_t fn_t} R Sigma sz.

Section Interpretation.
  Context {reg_t fn_t: Type}.

  Context {R: reg_t -> nat}.
  Context {Sigma: fn_t -> CExternalSignature}.
  Context {REnv: Env reg_t}.

  Context (r: REnv.(env_t) (fun idx => bits (R (idx)))).
  Context (sigma: forall f, CExternalSignature_denote (Sigma f)).

  Fixpoint interp_circuit {n} (c: circuit R Sigma n) : bits n :=
    match c with
    | CNot c =>
      Ob~(negb (Bits.single (interp_circuit c)))
    | CAnd c1 c2 =>
      Ob~(andb (Bits.single (interp_circuit c1)) (Bits.single (interp_circuit c2)))
    | COr c1 c2 =>
      Ob~(orb (Bits.single (interp_circuit c1)) (Bits.single (interp_circuit c2)))
    | CMux select c1 c2 =>
      if Bits.single (interp_circuit select) then interp_circuit c1
      else interp_circuit c2
    | CConst cst =>
      cst
    | CReadRegister idx =>
      REnv.(getenv) r idx
    | CExternal idx arg1 arg2 =>
      sigma idx (interp_circuit arg1) (interp_circuit arg2)
    | CAnnot _ c =>
      interp_circuit c
    end.
End Interpretation.

Section CircuitOptimizer.
  Context {reg_t fn_t: Type}.
  Context {R: reg_t -> nat}.
  Context {Sigma: fn_t -> CExternalSignature}.

  Notation Circuit := circuit.
  Notation circuit := (circuit R Sigma).

  Context {REnv: Env reg_t}.

  Context (r: REnv.(env_t) (fun idx => bits (R idx))).
  Context (sigma: forall f, CExternalSignature_denote (Sigma f)).

  Record local_circuit_optimizer :=
    { lco_fn :> forall {sz}, circuit sz -> circuit sz;
      lco_proof: forall {sz} (c: circuit sz),
          interp_circuit r sigma (lco_fn c) =
          interp_circuit r sigma c }.

  Definition lco_opt_compose
             (o1 o2: forall {sz}, circuit sz -> circuit sz) sz (c: circuit sz) :=
    o2 (o1 c).

  Definition lco_compose (l1 l2: local_circuit_optimizer) :=
    {| lco_fn := @lco_opt_compose (l1.(@lco_fn)) (l2.(@lco_fn));
       lco_proof := ltac:(abstract (intros; unfold lco_opt_compose;
                                     cbn; rewrite !lco_proof; reflexivity)) |}.

  Fixpoint unannot {sz} (c: circuit sz) : circuit sz :=
    match c with
    | CAnnot annot c => unannot c
    | c => c
    end.

  Fixpoint asconst {sz} (c: circuit sz) : option (list bool) :=
    match c return option (list bool) with
    | CAnnot annot c =>
      asconst c
    | @CConst _ _ _ _ sz cst =>
      Some (vect_to_list cst)
    | c => None
    end.

  Notation ltrue := (cons true nil).
  Notation lfalse := (cons false nil).

  Instance EqDec_ListBool : EqDec (list bool) := _.

  Definition simplify_bool_1' {sz} (c: circuit sz): circuit sz :=
    match c in Circuit _ _ sz return circuit sz with
    | (CNot c) as c0 =>
      match asconst c with
      | Some ltrue => CConst Ob~0
      | Some lfalse => CConst Ob~1
      | _ => c0
      end
    | (CAnd c1 c2) as c0 =>
      match asconst c1, asconst c2 with
      | Some lfalse, _ | _, Some lfalse => CConst Ob~0
      | _, Some ltrue => c1
      | Some ltrue, _ => c2
      | _, _ => c0
      end
    | (COr c1 c2) as c0 =>
      match asconst c1, asconst c2 with
      | Some ltrue, _ | _, Some ltrue => CConst Ob~1
      | _, Some lfalse => c1
      | Some lfalse, _ => c2
      | _, _ => c0
      end
    | (CMux select c1 c2) as c0 =>
      match asconst select with
      | Some ltrue => c1
      | Some lfalse => c2
      | _ => match asconst c1, asconst c2 with
            | Some bs1, Some bs2 =>
              if eq_dec bs1 bs2 then c1
              else c0
            | _, _ => c0
            end
      end
    | c => c
    end.

  Definition simplify_bool_1 {sz} (c: circuit sz): circuit sz :=
    match sz as n return (circuit n -> circuit n) with
    | 0 => fun c => CConst Bits.nil
    | _ => fun c => simplify_bool_1' c
    end c.

  Lemma asconst_Some :
    forall {sz} (c: circuit sz) bs,
      asconst c = Some bs ->
      vect_to_list (interp_circuit r sigma c) = bs.
  Proof.
    induction c; intros b Heq;
      repeat match goal with
             | _ => progress cbn in *
             | _ => discriminate
             | _ => reflexivity
             | [ H: Some _ = Some _ |- _ ] => inversion H; subst; clear H
             | [ sz: nat |- _ ] => destruct sz; try (tauto || discriminate); []
             end.
    apply IHc; eassumption.
  Qed.

  Arguments simplify_bool_1 sz !c.

  Lemma vect_to_list_inj T :
    forall sz (v1 v2: vect T sz),
      vect_to_list v1 = vect_to_list v2 ->
      v1 = v2.
  Proof.
    induction sz; destruct v1, v2; cbn.
    - reflexivity.
    - inversion 1; subst; f_equal; apply IHsz; eassumption.
  Qed.

  Arguments EqDec_ListBool: simpl never.
  Lemma simplify_bool_1'_correct :
    forall {sz} (c: circuit sz),
      interp_circuit r sigma (simplify_bool_1' c) = interp_circuit r sigma c.
  Proof.
    induction c; cbn.
    Ltac t := match goal with
             | _ => reflexivity
             | _ => progress bool_simpl
             | _ => progress cbn in *
             | [  |- context[match asconst ?c with _ => _ end] ] =>
               destruct (asconst c) as [ | ] eqn:?
             | [ H: asconst _ = Some _ |- _ ] => apply asconst_Some in H
             | [  |- _ = ?y ] =>
               match y with
               | context[Bits.single (interp_circuit r sigma ?c)] =>
                 destruct (interp_circuit r sigma c) as [ ? [] ] eqn:? ;
                 cbn in *; subst
               end
             | [ H: ?x = _ |- context[?x] ] => rewrite H
             | [  |- context[if ?b then _ else _] ] => destruct b eqn:?
             | _ => eauto using vect_to_list_inj
             end.
    all: repeat t.
  Qed.

  Lemma simplify_bool_1_correct :
    forall {sz} (c: circuit sz),
      interp_circuit r sigma (simplify_bool_1 c) = interp_circuit r sigma c.
  Proof.
    unfold simplify_bool_1; destruct sz.
    - cbn; intros.
      destruct interp_circuit; reflexivity.
    - eauto using simplify_bool_1'_correct.
  Qed.

  Definition bool_simpl_lco :=
    {| lco_fn := @simplify_bool_1; lco_proof := @simplify_bool_1_correct |}.
End CircuitOptimizer.

Arguments simplify_bool_1 {_ _ _ _} [_] _.
Arguments lco_fn {_ _ _ _ _ _ _} _ {_}.
Arguments lco_proof {_ _ _ _ _ _ _} _ {_}.
Arguments lco_compose {_ _ _ _ _ _ _} _ _.
Arguments bool_simpl_lco {_ _ _ _ _ _ _}.

Section CircuitCompilation.
  Context {name_t var_t reg_t fn_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.

  Context {R: reg_t -> type}.
  Context {Sigma: fn_t -> ExternalSignature}.
  Context {REnv: Env reg_t}.

  Definition CR idx :=
    type_sz (R idx).

  Definition CSigma fn :=
    {| arg1Size := type_sz (Sigma fn).(arg1Type);
       arg2Size := type_sz (Sigma fn).(arg2Type);
       retSize := type_sz (Sigma fn).(retType) |}.

  Notation circuit := (circuit CR CSigma).

  Context (opt: forall {sz}, circuit sz -> circuit sz).
  Context (r: REnv.(env_t) (fun reg => circuit (CR reg))).

  Notation CAnnotOpt an c := (CAnnot an (opt _ c)).
  (* Notation CAnnotOpt an c := (CAnnot an c). *)

  Notation "f [ arg ]` an `" :=
    (CAnnotOpt an (CExternal f arg (CConst Ob)))
      (at level 99, arg at level 99, format "f [ arg ]` an `") : circuit.
  Notation "f [ arg1 ',' arg2 ]` an `" :=
    (CAnnotOpt an (CExternal f arg1 arg2))
      (at level 99, arg1 at level 99, arg2 at level 99,
       format "f [ arg1 ','  arg2 ]` an `") : circuit.
  Notation "#` an ` reg" :=
    (CAnnotOpt an (CReadRegister reg))
      (at level 75, format "#` an ` reg") : circuit.
  Notation "$` an ` c" :=
    (CAnnotOpt an (CConst c))
      (at level 75, format "$` an ` c") : circuit.
  Notation "!` an ` c" :=
    (CAnnotOpt an (CNot c))
      (at level 30, right associativity, format "!` an ` c") : circuit.
  Notation "c1 &&` an `  c2" :=
    (CAnnotOpt an (CAnd c1 c2))
      (at level 40, left associativity) : circuit.
  Notation "c1 ||` an `  c2" :=
    (CAnnotOpt an (COr c1 c2))
      (at level 50, left associativity) : circuit.
  Notation "c1 ==>` an ` c2" :=
    (CAnnotOpt an (COr (CAnnotOpt "impl" (CNot c1)) c2))
      (at level 70, no associativity) : circuit.
  (* Notation "s ?? c1 // c2" := (CMux s c1 c2) (at level 80, no associativity) : circuit. *)

  Local Open Scope circuit.

  Definition readRegisters : forall idx: reg_t, circuit (CR idx) :=
    fun idx => CReadRegister (R := CR) (Sigma := CSigma) idx.

  Record rwdata {sz} :=
    { read0: circuit 1;
      read1: circuit 1;
      write0: circuit 1;
      write1: circuit 1;
      data0: circuit sz;
      data1: circuit sz }.

  Definition rwset :=
    REnv.(env_t) (fun reg => @rwdata (CR reg)).

  Record rwcircuit :=
    { canFire: circuit 1;
      regs: rwset }.

  Record action_circuit {sz} :=
    { erwc: rwcircuit;
      retVal: circuit sz }.

  Definition scheduler_circuit :=
    rwset.

  Definition ccontext (sig: tsig var_t) :=
    context (fun '(k, tau) => circuit (type_sz tau)) sig.

  Definition mux_rwdata {sz} an (cond: circuit 1) (tReg fReg: @rwdata sz) :=
    {| read0 := CAnnotOpt an (CMux cond (tReg.(read0)) (fReg.(read0)));
       read1 := CAnnotOpt an (CMux cond (tReg.(read1)) (fReg.(read1)));
       write0 := CAnnotOpt an (CMux cond (tReg.(write0)) (fReg.(write0)));
       write1 := CAnnotOpt an (CMux cond (tReg.(write1)) (fReg.(write1)));
       data0 := CAnnotOpt an (CMux cond (tReg.(data0)) (fReg.(data0)));
       data1 := CAnnotOpt an (CMux cond (data1 tReg) (data1 fReg)) |}.

  Definition mux_rwsets an (cond: circuit 1) (tRegs fRegs: rwset) :=
    REnv.(map2) (fun k treg freg => mux_rwdata an cond treg freg)
                tRegs fRegs.

  Fixpoint mux_ccontext {sig} (cond: circuit 1) (ctxT: ccontext sig) (ctxF: ccontext sig) : ccontext sig.
    destruct sig as [ | (k, tau)]; cbn.
    - exact CtxEmpty.
    - apply (CtxCons (k, tau) (CMux cond (chd ctxT) (chd ctxF))
                     (mux_ccontext _ cond (ctl ctxT) (ctl ctxF))).
  Defined.

  Section Action.
    Fixpoint compile_action
             {sig: tsig var_t}
             {tau}
             (Gamma: ccontext sig)
             (a: action var_t R Sigma sig tau)
             (clog: rwcircuit):
      @action_circuit tau * (ccontext sig) :=
      match a in action _ _ _ ts tau return ccontext ts -> @action_circuit tau * ccontext ts with
      | Fail tau => fun Gamma =>
        ({| retVal := $`"fail"`Bits.zero (type_sz tau); (* LATER: Question mark here *)
            erwc := {| canFire := $`"fail_cF"` Ob~0;
                       regs := clog.(regs) |} |},
         Gamma)
      | Var m => fun Gamma =>
        ({| retVal := CAnnotOpt "var_reference" (cassoc m Gamma);
            erwc := clog |},
         Gamma)
      | Const cst => fun Gamma =>
        ({| retVal := CAnnotOpt "constant_value_from_source" (CConst (bits_of_value cst));
           erwc := clog |},
         Gamma)
      | Seq r1 r2 => fun Gamma =>
        let (cex, Gamma) := (compile_action Gamma r1 clog) in
        compile_action Gamma r2 cex.(erwc)
      | @Assign _ _ _ _ _ _ k tau m ex => fun Gamma =>
        let (cex, Gamma) := compile_action Gamma ex clog in
        ({| retVal := $`"assign_retVal"`Bits.nil;
            erwc := cex.(erwc) |},
         creplace m cex.(retVal) Gamma)
      | @Bind _ _ _ _ _ sig tau tau' var ex body => fun Gamma =>
        let (ex, Gamma) := compile_action Gamma ex clog in
        let (ex, Gamma) := compile_action (CtxCons (var, tau) ex.(retVal) Gamma) body ex.(erwc) in
        (ex, ctl Gamma)
      | If cond tbranch fbranch => fun Gamma =>
        let (cond, Gamma) := compile_action Gamma cond clog in
        let (tbranch, Gamma_t) := compile_action Gamma tbranch cond.(erwc) in
        let (fbranch, Gamma_f) := compile_action Gamma fbranch cond.(erwc) in
        ({| retVal := CAnnotOpt "if_retVal" (CMux cond.(retVal) tbranch.(retVal) fbranch.(retVal));
           erwc := {| canFire := CAnnotOpt "if_cF" (CMux cond.(retVal) tbranch.(erwc).(canFire) fbranch.(erwc).(canFire));
                     regs := mux_rwsets "if_mux" cond.(retVal) tbranch.(erwc).(regs) fbranch.(erwc).(regs) |} |},
         mux_ccontext cond.(retVal) Gamma_t Gamma_f)
      | Read P0 idx => fun Gamma =>
        let reg := REnv.(getenv) clog.(regs) idx in
        ({| retVal := CAnnotOpt "read0" (REnv.(getenv) r idx);
           erwc := {| canFire := (clog.(canFire) &&`"read0_cF"`
                                (!`"no_write1"` reg.(write1)));
                     regs := REnv.(putenv) clog.(regs) idx {| read0 := $`"read0"` Ob~1;
                                                             (* Unchanged *)
                                                             read1 := reg.(read1);
                                                             write0 := reg.(write0);
                                                             write1 := reg.(write1);
                                                             data0 := reg.(data0);
                                                             data1 := reg.(data1) |} |} |},
         Gamma)
      | Read P1 idx => fun Gamma =>
        let reg := REnv.(getenv) clog.(regs) idx in
        ({| retVal := reg.(data0);
            erwc := {| canFire := clog.(canFire);
                      regs := REnv.(putenv) clog.(regs) idx {| read1 := $`"read1"` Ob~1;
                                                              (* Unchanged *)
                                                              read0 := reg.(read0);
                                                              write0 := reg.(write0);
                                                              write1 := reg.(write1);
                                                              data0 := reg.(data0);
                                                              data1 := reg.(data1) |} |} |},
         Gamma)
      | Write P0 idx val => fun Gamma =>
        let (val, Gamma) := compile_action Gamma val clog in
        let reg := REnv.(getenv) val.(erwc).(regs) idx in
        ({| retVal := $`"write_retVal"`Bits.nil;
            erwc := {| canFire := (val.(erwc).(canFire) &&`"write0_cF"`
                                 (!`"no_read1"` reg.(read1) &&`"write0_cF"`
                                  !`"no_write0"` reg.(write0) &&`"write0_cF"`
                                  !`"no_write1"` reg.(write1)));
                      regs := REnv.(putenv) val.(erwc).(regs) idx {| write0 := $`"write0"` (Ob~1);
                                                                    data0 := val.(retVal);
                                                                    (* Unchanged *)
                                                                    read0 := reg.(read0);
                                                                    read1 := reg.(read1);
                                                                    write1 := reg.(write1);
                                                                    data1 := reg.(data1) |} |} |},
         Gamma)
      | Write P1 idx val => fun Gamma =>
        let (val, Gamma) := compile_action Gamma val clog in
        let reg := REnv.(getenv) val.(erwc).(regs) idx in
        ({| retVal := $`"write_retVal"`Bits.nil;
            erwc := {| canFire := val.(erwc).(canFire) &&`"write1_cF"` !`"no_write1"` reg.(write1);
                      regs := REnv.(putenv) val.(erwc).(regs) idx {| write1 := $`"write1"` (Ob~1);
                                                                    data1 := val.(retVal);
                                                                    (* Unchanged *)
                                                                    read0 := reg.(read0);
                                                                    read1 := reg.(read1);
                                                                    write0 := reg.(write0);
                                                                    data0 := reg.(data0) |} |} |},
         Gamma)
      | Call fn a1 a2 => fun Gamma =>
        let (a1, Gamma) := compile_action  Gamma a1 clog in
        let (a2, Gamma) := compile_action Gamma a2 a1.(erwc) in
        ({| retVal := fn [a1.(retVal), a2.(retVal)]`"Call_from_source"`;
            erwc := a2.(erwc) |},
         Gamma)
        end Gamma.
  End Action.

  Definition adapter (cs: scheduler_circuit) : rwcircuit :=
    {| canFire := $`"cF_init"` Ob~1;
       regs := REnv.(map) (fun k reg => {| read0 := $`"init_no_read0"` Ob~0;
                                       read1 := $`"init_no_read1"` Ob~0;
                                       write0 := $`"init_no_write0"` Ob~0;
                                       write1 := $`"init_no_write1"` Ob~0;
                                       data0 := reg.(data0);
                                       data1 := reg.(data1) |})
                         cs |}.

  Definition willFire_of_canFire'_read0 {sz} (ruleReg inReg: @rwdata sz) :=
    (ruleReg.(read0)) ==>`"read0_wF_of_cF"`
    (!`"read0_wF_no_writes"` ((inReg.(write0)) ||`""` (inReg.(write1)))).

  Definition willFire_of_canFire'_write0 {sz} (ruleReg inReg: @rwdata sz) :=
    (ruleReg.(write0)) ==>`"write0_wF_of_cF"`
    (!`"write0_wF_no_writes_no_read1"`
       ((inReg.(write0)) ||`""` (inReg.(write1)) ||`""` (inReg.(read1)))).

  Definition willFire_of_canFire'_rw1 {sz} (ruleReg inReg: @rwdata sz) :=
    ((ruleReg.(read1)) ||`""` (ruleReg.(write1))) ==>`"read_write1_wF_of_cF"`
    (!`"read_write1_wF_no_write1"` (inReg.(write1))).

  Definition willFire_of_canFire' {sz} (ruleReg inReg: @rwdata sz) :=
    (willFire_of_canFire'_read0 ruleReg inReg) &&`""`
    (willFire_of_canFire'_write0 ruleReg inReg) &&`""`
    (willFire_of_canFire'_rw1 ruleReg inReg).

  Definition willFire_of_canFire cRule cInput : circuit 1 :=
    REnv.(fold_right)
           (fun k '(ruleReg, inReg) acc =>
              acc &&`"wF_fold_res"` willFire_of_canFire' ruleReg inReg)
           (REnv.(zip) cRule.(regs) cInput) cRule.(canFire).

  Arguments willFire_of_canFire' : simpl never.

  Definition update_accumulated_rwset (rl_rwset acc: rwset) :=
    let an := "compute_accumulated_rwset" in
    REnv.(map2) (fun _ ruleReg accReg =>
                   {| read0 := (ruleReg.(read0)) ||`an` (accReg.(read0));
                      read1 := (ruleReg.(read1)) ||`an` (accReg.(read1));
                      write0 := (ruleReg.(write0)) ||`an` (accReg.(write0));
                      write1 := (ruleReg.(write1)) ||`an` (accReg.(write1));
                      data0 := (ruleReg.(data0));
                      data1 := (ruleReg.(data1)) |})
                rl_rwset acc.

  Context (rules: name_t -> rule var_t R Sigma).

  Fixpoint compile_scheduler'
           (s: scheduler name_t)
           (input: scheduler_circuit):
    scheduler_circuit :=
    match s with
    | Done =>
      input
    | Cons rl s =>
      let (rl, Gamma) := compile_action CtxEmpty (rules rl) (adapter input) in
      let acc := update_accumulated_rwset rl.(erwc).(regs) input in
      let will_fire := willFire_of_canFire rl.(erwc) input in
      let input := mux_rwsets "mux_input" will_fire acc input in
      compile_scheduler' s input
    | Try rl st sf =>
      let (rl, Gamma) := compile_action CtxEmpty (rules rl) (adapter input) in
      let acc := update_accumulated_rwset rl.(erwc).(regs) input in
      let st := compile_scheduler' st acc in
      let sf := compile_scheduler' sf input in
      let will_fire := willFire_of_canFire rl.(erwc) input in
      mux_rwsets "mux_subschedulers" will_fire st sf
    end.

  Definition commit_rwdata {sz} (reg: @rwdata sz) initial_value : circuit sz :=
    CAnnotOpt "commit_write1"
           (CMux (reg.(write1))
                 (reg.(data1))
                 (CAnnotOpt "commit_write0"
                         (CMux (reg.(write0))
                               (reg.(data0))
                               (CAnnotOpt "commit_unchanged" initial_value)))).

  Definition state_transition_circuit :=
    REnv.(env_t) (fun reg => circuit (R reg)).

  Definition init_scheduler_rwdata idx : rwdata :=
    {| read0 := $`"sched_init_no_read0"` Ob~0;
       read1 := $`"sched_init_no_read1"` Ob~0;
       write0 := $`"sched_init_no_write0"` Ob~0;
       write1 := $`"sched_init_no_write1"` Ob~0;
       data0 := CAnnotOpt "sched_init_data0_is_reg" (REnv.(getenv) r idx);
       data1 := CAnnotOpt "sched_init_no_data1" (CConst (Bits.zeroes _)) |}.

  Definition init_scheduler_circuit : scheduler_circuit :=
    REnv.(create) init_scheduler_rwdata.

  Definition compile_scheduler (s: scheduler name_t) : state_transition_circuit :=
    let s := compile_scheduler' s init_scheduler_circuit in
    REnv.(map2) (fun k r1 r2 => commit_rwdata r1 r2) s r.
End CircuitCompilation.

Arguments CR {_} R idx.
Arguments CSigma {_} Sigma fn.

Arguments readRegisters {_ _}.
Arguments rwdata {_ _}.
Arguments action_circuit {_ _}.
Arguments scheduler_circuit {_ _}.
Arguments state_transition_circuit {_ _}.
