(*! Circuits | Compilation from lowered ASTs !*)
Require Export Koika.Common Koika.Environments.
Require Import Koika.Syntax Koika.TypedSyntax Koika.TypedSyntaxTools.
Require Export Koika.CircuitSemantics.

Import PrimTyped CircuitSignatures.

Section CircuitCompilation.
  Context {pos_t var_t rule_name_t reg_t ext_fn_t: Type}.

  Context {R: reg_t -> type}.
  Context {Sigma: ext_fn_t -> ExternalSignature}.
  Context {REnv: Env reg_t}.

  Context {Show_var_t : Show var_t}.
  Context {Show_rule_name_t : Show rule_name_t}.

  Definition CR_of_R idx :=
    type_sz (R idx).
  Notation CR := CR_of_R.

  Definition CSigma_of_Sigma fn :=
    CSig_of_Sig (Sigma fn).
  Notation CSigma := CSigma_of_Sigma.

  Definition cr_of_r (r: REnv.(env_t) R)
    : REnv.(env_t) (fun idx => bits (CR idx)) :=
    map REnv (fun idx v => bits_of_value v) r.

  Definition csigma_of_sigma (sigma: forall f, Sig_denote (Sigma f))
    : forall f, CSig_denote (CSigma f) :=
    fun f => fun bs => bits_of_value (sigma f (value_of_bits bs)).

  Notation circuit' rwdata := (circuit (rule_name_t := rule_name_t) (rwdata := rwdata) CR CSigma).

  Inductive rwdata {sz: nat} :=
    { read0: circuit' (@rwdata) 1;
      read1: circuit' (@rwdata) 1;
      write0: circuit' (@rwdata) 1;
      write1: circuit' (@rwdata) 1;
      data0: circuit' (@rwdata) sz;
      data1: circuit' (@rwdata) sz }.
  Notation circuit := (circuit' (@rwdata)).

  Context (opt: forall {sz}, circuit sz -> circuit sz).
  Context (cr: REnv.(env_t) (fun reg => circuit (CR reg))).

  (* Notation CAnnot an c := (match an : string with _ => c end). *)
  Notation CAnnotOpt an c := (CAnnot an (opt _ c)).

  Declare Scope circuit.
  Notation "f [ arg ]` an `" :=
    (CAnnotOpt an (CExternal f arg (CConst Ob)))
      (at level 99, arg at level 99, format "f [ arg ]` an `") : circuit.
  Notation "f [ arg1 ',' arg2 ]` an `" :=
    (CAnnotOpt an (CExternal f arg1 arg2))
      (at level 99, arg1 at level 99, arg2 at level 99,
       format "f [ arg1 ','  arg2 ]` an `") : circuit.
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
  Notation CMuxAnnotOpt an s c1 c2 :=
    (CAnnotOpt an (CMux s c1 c2)).

  Local Open Scope circuit.

  Definition readRegisters : forall idx: reg_t, circuit (CR idx) :=
    fun idx => CReadRegister (CR := CR) (CSigma := CSigma) idx.

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
    {| read0 := CMuxAnnotOpt an cond (tReg.(read0)) (fReg.(read0));
       read1 := CMuxAnnotOpt an cond (tReg.(read1)) (fReg.(read1));
       write0 := CMuxAnnotOpt an cond (tReg.(write0)) (fReg.(write0));
       write1 := CMuxAnnotOpt an cond (tReg.(write1)) (fReg.(write1));
       data0 := CMuxAnnotOpt an cond (tReg.(data0)) (fReg.(data0));
       data1 := CMuxAnnotOpt an cond (data1 tReg) (data1 fReg) |}.

  Definition mux_rwsets an (cond: circuit 1) (tRegs fRegs: rwset) :=
    map2 REnv (fun k treg freg => mux_rwdata an cond treg freg)
                tRegs fRegs.

  Fixpoint mux_ccontext {sig} (cond: circuit 1) (ctxT: ccontext sig) (ctxF: ccontext sig) : ccontext sig.
    destruct sig as [ | (k, tau)]; cbn.
    - exact CtxEmpty.
    - apply (CtxCons (k, tau) (CMuxAnnotOpt "mux_ccontext" cond (chd ctxT) (chd ctxF))
                     (mux_ccontext _ cond (ctl ctxT) (ctl ctxF))).
  Defined.

  Section Action.
    Definition compile_unop (fn: fn1) (a: circuit (type_sz (PrimSignatures.Sigma1 fn).(arg1Sig))):
      circuit (type_sz (PrimSignatures.Sigma1 fn).(retSig)) :=
      let cArg1 fn := circuit (type_sz (PrimSignatures.Sigma1 fn).(arg1Sig)) in
      let cRet fn := circuit (type_sz (PrimSignatures.Sigma1 fn).(retSig)) in
      match fn return cArg1 fn -> cRet fn with
      | Display fn => fun _ => CConst Ob
      | Conv tau fn => fun a =>
        match fn return cArg1 (Conv tau fn) -> cRet (Conv tau fn) with
        | Pack => fun a => a
        | Unpack => fun a => a
        | Ignore => fun _ => CConst Ob
        end a
      | Bits1 fn => fun a =>
        match fn return cArg1 (Bits1 fn) -> cRet (Bits1 fn) -> cRet (Bits1 fn) with
        | Not _ => fun a c => c
        | Repeat _ _ => fun a c => c
        | SExt sz width => fun a c =>
                            ltac:(subst cRet; simpl; rewrite <- vect_extend_end_cast, <- (Nat.mul_1_r (width - sz));
                                  exact (CBinop (Concat _ _)
                                                (CUnop (Repeat 1 (width - sz))
                                                       (CBinop (Sel sz) a (CConst (Bits.of_nat (log2 sz) (pred sz)))))
                                                a))
        | ZExtL sz width => fun a c =>
                             ltac:(subst cRet; simpl; rewrite <- vect_extend_end_cast;
                                     exact (CBinop (Concat _ _) (CConst Bits.zero) a))
        | ZExtR sz width => fun a c =>
                             ltac:(subst cRet; simpl; rewrite <- vect_extend_beginning_cast;
                                     exact (CBinop (Concat _ _) a (CConst Bits.zero)))
        | Slice sz offset width => fun a c => c
        | Lowered fn => fun a c => c
        end a (CUnop fn a)
      | Struct1 fn sig f => fun a =>
        match fn return cArg1 (Struct1 fn sig f) -> cRet (Struct1 fn sig f) with
        | GetField => fun a =>
          CUnop (GetFieldBits sig f) a
        end a
      | Array1 fn sig idx => fun a =>
        match fn return cArg1 (Array1 fn sig idx) -> cRet (Array1 fn sig idx) with
        | GetElement => fun a =>
          CUnop (GetElementBits sig idx) a
        end a
      end a.

    Definition compile_binop (fn: fn2)
               (a1: circuit (type_sz (PrimSignatures.Sigma2 fn).(arg1Sig)))
               (a2: circuit (type_sz (PrimSignatures.Sigma2 fn).(arg2Sig))):
      circuit (type_sz (PrimSignatures.Sigma2 fn).(retSig)) :=
      let cArg1 fn := circuit (type_sz (PrimSignatures.Sigma2 fn).(arg1Sig)) in
      let cArg2 fn := circuit (type_sz (PrimSignatures.Sigma2 fn).(arg2Sig)) in
      let cRet fn := circuit (type_sz (PrimSignatures.Sigma2 fn).(retSig)) in
      match fn return cArg1 fn -> cArg2 fn -> cRet fn with
      | Eq tau negate => fun a1 a2 => CBinop (EqBits (type_sz tau) negate) a1 a2
      | Bits2 fn => fun a1 a2 => CBinop fn a1 a2
      | Struct2 fn sig f => fun a1 a2 =>
        match fn return cArg1 (Struct2 fn sig f) -> cArg2 (Struct2 fn sig f) -> cRet (Struct2 fn sig f) with
        | SubstField => fun a1 a2 =>
          CBinop (SubstFieldBits sig f) a1 a2
        end a1 a2
      | Array2 fn sig idx => fun a1 a2 =>
        match fn return cArg1 (Array2 fn sig idx) -> cArg2 (Array2 fn sig idx) -> cRet (Array2 fn sig idx) with
        | SubstElement => fun a1 a2 =>
          CBinop (SubstElementBits sig idx) a1 a2
        end a1 a2
      end a1 a2.

    Fixpoint compile_action
             {sig: tsig var_t}
             {tau}
             (Gamma: ccontext sig)
             (a: action pos_t var_t R Sigma sig tau)
             (clog: rwcircuit):
      @action_circuit (type_sz tau) * (ccontext sig) :=
      match a in action _ _ _ _ ts tau return ccontext ts -> @action_circuit (type_sz tau) * ccontext ts with
      | Fail tau => fun Gamma =>
        ({| retVal := $`"fail"`Bits.zeroes (type_sz tau); (* LATER: Question mark here *)
            erwc := {| canFire := $`"fail_cF"` Ob~0;
                       regs := clog.(regs) |} |},
         Gamma)
      | @Var _ _ _ _ _ _ _ k _ m => fun Gamma =>
        ({| retVal := CAnnotOpt (String.append "var_" (show k)) (cassoc m Gamma);
            erwc := clog |},
         Gamma)
      | Const cst => fun Gamma =>
        ({| retVal := CAnnotOpt "constant_value_from_source" (CConst (bits_of_value cst));
           erwc := clog |},
         Gamma)
      | Seq r1 r2 => fun Gamma =>
        let (cex, Gamma) := (compile_action Gamma r1 clog) in
        compile_action Gamma r2 cex.(erwc)
      | @Assign _ _ _ _ _ _ _ k tau m ex => fun Gamma =>
        let (cex, Gamma) := compile_action Gamma ex clog in
        ({| retVal := $`"assign_retVal"`Bits.nil;
            erwc := cex.(erwc) |},
         creplace m cex.(retVal) Gamma)
      | @Bind _ _ _ _ _ _ sig tau tau' var ex body => fun Gamma =>
        let (ex, Gamma) := compile_action Gamma ex clog in
        let (ex, Gamma) := compile_action (CtxCons (var, tau) ex.(retVal) Gamma) body ex.(erwc) in
        (ex, ctl Gamma)
      | If cond tbranch fbranch => fun Gamma =>
        let (cond, Gamma) := compile_action Gamma cond clog in
        let (tbranch, Gamma_t) := compile_action Gamma tbranch cond.(erwc) in
        let (fbranch, Gamma_f) := compile_action Gamma fbranch cond.(erwc) in
        ({| retVal := CMuxAnnotOpt "if_retVal" cond.(retVal) tbranch.(retVal) fbranch.(retVal);
           erwc := {| canFire := CMuxAnnotOpt "if_cF" cond.(retVal) tbranch.(erwc).(canFire) fbranch.(erwc).(canFire);
                     regs := mux_rwsets "if_mux" cond.(retVal) tbranch.(erwc).(regs) fbranch.(erwc).(regs) |} |},
         mux_ccontext cond.(retVal) Gamma_t Gamma_f)
      | Read P0 idx => fun Gamma =>
        let reg := REnv.(getenv) clog.(regs) idx in
        ({| retVal := CAnnotOpt "read0" (REnv.(getenv) cr idx);
           erwc := {| canFire := clog.(canFire);
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
      | Unop fn a => fun Gamma =>
        let (a, Gamma) := compile_action Gamma a clog in
        ({| retVal := compile_unop fn a.(retVal);
            erwc := a.(erwc) |},
         Gamma)
      | Binop fn a1 a2 => fun Gamma =>
        let (a1, Gamma) := compile_action Gamma a1 clog in
        let (a2, Gamma) := compile_action Gamma a2 a1.(erwc) in
        ({| retVal := compile_binop fn a1.(retVal) a2.(retVal);
            erwc := a2.(erwc) |},
         Gamma)
      | ExternalCall fn a => fun Gamma =>
        let (a, Gamma) := compile_action Gamma a clog in
        ({| retVal := CAnnotOpt "External_call" (CExternal fn a.(retVal));
            erwc := a.(erwc) |},
         Gamma)
      | APos _ a => fun Gamma =>
        compile_action Gamma a clog
      end Gamma.
  End Action.

  Definition adapter (cs: scheduler_circuit) : rwcircuit :=
    {| canFire := $`"cF_init"` Ob~1;
       regs := map REnv (fun k reg => {| read0 := $`"init_no_read0"` Ob~0;
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

  Definition willFire_of_canFire rl_name cRule cInput : circuit 1 :=
    let annot := String.append "wF_" (show rl_name) in
    fold_right REnv
           (fun k '(ruleReg, inReg) acc =>
              acc &&`annot` willFire_of_canFire' ruleReg inReg)
           (zip REnv cRule.(regs) cInput) cRule.(canFire).

  Arguments willFire_of_canFire' : simpl never.

  Definition update_accumulated_rwset (rl_rwset acc: rwset) :=
    let an := "compute_accumulated_rwset" in
    map2 REnv (fun _ ruleReg accReg =>
                   {| read0 := (ruleReg.(read0)) ||`an` (accReg.(read0));
                      read1 := (ruleReg.(read1)) ||`an` (accReg.(read1));
                      write0 := (ruleReg.(write0)) ||`an` (accReg.(write0));
                      write1 := (ruleReg.(write1)) ||`an` (accReg.(write1));
                      data0 := (ruleReg.(data0));
                      data1 := (ruleReg.(data1)) |})
                rl_rwset acc.

  Definition bundleref_wrap_rwdata rl rs bundle (r: reg_t) (ruleReg: @rwdata (CR r))
    : @rwdata (CR r) :=
    let ft := REnv.(finite_keys) in
    if List.find (fun r' => beq_dec (EQ := EqDec_FiniteType) r r') rs then
      {| read0 := CBundleRef rl rs bundle (rwcircuit_rwdata r rwdata_r0) (ruleReg.(read0));
         read1 := CBundleRef rl rs bundle (rwcircuit_rwdata r rwdata_r1) (ruleReg.(read1));
         write0 := CBundleRef rl rs bundle (rwcircuit_rwdata r rwdata_w0) (ruleReg.(write0));
         write1 := CBundleRef rl rs bundle (rwcircuit_rwdata r rwdata_w1) (ruleReg.(write1));
         data0 := CBundleRef rl rs bundle (rwcircuit_rwdata r rwdata_data0) (ruleReg.(data0));
         data1 := CBundleRef rl rs bundle (rwcircuit_rwdata r rwdata_data1) (ruleReg.(data1)) |}
    else ruleReg.

  Definition bundleref_wrap_rwset rl rs bundle (rws: rwset) :=
    map REnv (bundleref_wrap_rwdata rl rs bundle) rws.

  Definition bundleref_wrap_erwc rl rs bundle erwc :=
    {| canFire := CBundleRef rl rs bundle rwcircuit_canfire erwc.(canFire);
       regs := bundleref_wrap_rwset rl rs bundle erwc.(regs) |}.

  Definition bundleref_wrap_action_circuit
             {tau} (rs: list reg_t)
             (input: rwset) (rl: @action_circuit tau) (rl_name: rule_name_t)
    : @action_circuit tau :=
    let bundle := ccreate rs (fun r _ => REnv.(getenv) input r) in
    {| erwc := bundleref_wrap_erwc rl_name rs bundle rl.(erwc);
       retVal := rl.(retVal) |}.

  Context (rules: rule_name_t -> rule pos_t var_t R Sigma).
  Context (external: rule_name_t -> bool).

  Fixpoint compile_scheduler_circuit
           (s: scheduler pos_t rule_name_t)
           (input: scheduler_circuit):
    scheduler_circuit :=
    let compile_action rl_name :=
      let rule := rules rl_name in
      let ft := REnv.(finite_keys) in
      let rs := action_registers (EQ := EqDec_FiniteType) rule in
      let (rl, _) := compile_action CtxEmpty rule (adapter input) in
      let rl := if external rl_name then bundleref_wrap_action_circuit rs input rl rl_name else rl in
      let acc := update_accumulated_rwset rl.(erwc).(regs) input in
      (rl, acc) in
    match s with
    | Done =>
      input
    | Cons rl_name s =>
      let (rl, acc) := compile_action rl_name in
      let will_fire := willFire_of_canFire rl_name rl.(erwc) input in
      let input := mux_rwsets "mux_input" will_fire acc input in
      compile_scheduler_circuit s input
    | Try rl_name st sf =>
      let (rl, acc) := compile_action rl_name in
      let st := compile_scheduler_circuit st acc in
      let sf := compile_scheduler_circuit sf input in
      let will_fire := willFire_of_canFire rl_name rl.(erwc) input in
      mux_rwsets "mux_subschedulers" will_fire st sf
    | SPos _ s =>
      compile_scheduler_circuit s input
    end.

  Definition commit_rwdata {sz} (reg: @rwdata sz) : circuit sz :=
    CMuxAnnotOpt "commit_write1" (reg.(write1)) (reg.(data1)) (reg.(data0)).

  Definition init_scheduler_rwdata idx : rwdata :=
    {| read0 := $`"sched_init_no_read0"` Ob~0;
       read1 := $`"sched_init_no_read1"` Ob~0;
       write0 := $`"sched_init_no_write0"` Ob~0;
       write1 := $`"sched_init_no_write1"` Ob~0;
       data0 := CAnnotOpt "sched_init_data0_is_reg" (REnv.(getenv) cr idx);
       data1 := CAnnotOpt "sched_init_no_data1" (CConst Bits.zero) |}.

  Definition init_scheduler_circuit : scheduler_circuit :=
    REnv.(create) init_scheduler_rwdata.

  Definition register_update_circuitry :=
    REnv.(env_t) (fun reg => circuit (CR reg)).

  Definition compile_scheduler' (s: scheduler pos_t rule_name_t)
    : register_update_circuitry :=
    let s := compile_scheduler_circuit s init_scheduler_circuit in
    map REnv (fun k r => commit_rwdata r) s.
End CircuitCompilation.

Arguments CR_of_R {reg_t} R idx : assert.
Arguments CSigma_of_Sigma {ext_fn_t} Sigma fn : assert.
Arguments cr_of_r {reg_t} {R} {REnv} r : assert.
Arguments csigma_of_sigma {ext_fn_t} {Sigma} sigma f a : assert.

Arguments readRegisters {rule_name_t reg_t ext_fn_t} R Sigma idx : assert.
Arguments rwdata {rule_name_t reg_t ext_fn_t} R Sigma sz : assert.
Arguments action_circuit {rule_name_t reg_t ext_fn_t} R Sigma REnv sz : assert.
Arguments scheduler_circuit {rule_name_t reg_t ext_fn_t} R Sigma REnv : assert.
Arguments register_update_circuitry rule_name_t {reg_t ext_fn_t} R Sigma REnv : assert.

Section Helpers.
  Context {pos_t var_t rule_name_t reg_t ext_fn_t: Type}.

  Context {R: reg_t -> type}.
  Context {Sigma: ext_fn_t -> ExternalSignature}.
  Context {FiniteType_reg_t: FiniteType reg_t}.

  Context {Show_var_t: Show var_t}.
  Context {Show_rule_name_t: Show rule_name_t}.

  Notation circuit :=
    (circuit (rule_name_t := rule_name_t)
             (rwdata := rwdata (rule_name_t := rule_name_t) R Sigma)
             (CR_of_R R) (CSigma_of_Sigma Sigma)).
  Context (opt: forall {sz}, circuit sz -> circuit sz).

  Definition compile_scheduler
             (rules: rule_name_t -> rule pos_t var_t R Sigma)
             (external: rule_name_t -> bool)
             (s: scheduler pos_t rule_name_t)
    : register_update_circuitry rule_name_t R Sigma _ :=
    let cr := ContextEnv.(create) (readRegisters R Sigma) in
    compile_scheduler' opt cr rules external s.

  Context {REnv: Env reg_t}.
  Context (r: REnv.(env_t) R).
  Context (sigma: forall f, Sig_denote (Sigma f)).

  Definition interp_circuits
             (circuits: register_update_circuitry rule_name_t R Sigma REnv) :=
    let cr := cr_of_r r in
    let csigma := csigma_of_sigma sigma in
    map REnv (fun _ c => interp_circuit cr csigma c) circuits.
End Helpers.
