(*! Circuits | Compilation of lowered ASTs into RTL circuits !*)
Require Import Koika.Syntax Koika.LoweredSyntax Koika.LoweredSyntaxFunctions.
Require Export Koika.CircuitSemantics Koika.Common Koika.Environments.

Import PrimTyped CircuitSignatures.

Section CircuitCompilation.
  Context {pos_t var_t rule_name_t reg_t ext_fn_t: Type}.

  Context {CR: reg_t -> nat}.
  Context {CSigma: ext_fn_t -> CExternalSignature}.
  Context {REnv: Env reg_t}.

  Context {Show_var_t : Show var_t}.
  Context {Show_rule_name_t : Show rule_name_t}.
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
  Notation COpt c := (opt _ c).
  Notation CAnnotOpt an c := (CAnnot an (COpt c)).

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
  Notation CUnopOpt f c := (COpt (CUnop f c)).
  Notation CBinopOpt f c1 c2 := (COpt (CBinop f c1 c2)).
  Notation CMuxAnnotOpt an s c1 c2 := (CAnnotOpt an (CMux s c1 c2)).

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

  Definition ccontext (sig: lsig) :=
    context (fun sz => circuit sz) sig.

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
    destruct sig as [ | sz]; cbn.
    - exact CtxEmpty.
    - apply (CtxCons sz (CMuxAnnotOpt "mux_ccontext" cond (chd ctxT) (chd ctxF))
                     (mux_ccontext _ cond (ctl ctxT) (ctl ctxF))).
  Defined.

  Section Action.
    Lemma mul_1_r :
      forall n : nat, n * 1 = n.
    Proof. induction n; simpl; congruence. Defined.

    Definition compile_unop (fn: fbits1) (a: circuit (CSigma1 fn).(arg1Sig)):
      circuit (CSigma1 fn).(retSig) :=
      let cArg1 fn := circuit (CSigma1 fn).(arg1Sig) in
      let cRet fn := circuit (CSigma1 fn).(retSig) in
      let c :=
        match fn return circuit (CSigma1 fn).(arg1Sig) ->
                        circuit (CSigma1 fn).(retSig) ->
                        circuit (CSigma1 fn).(retSig) with
        | Not _ => fun a c => c
        | Repeat _ _ => fun a c => c
        | SExt sz width => fun a c =>
          ltac:(subst cRet; simpl; rewrite <- vect_extend_end_cast, <- (mul_1_r (width - sz));
                  exact (CBinopOpt (Concat _ _)
                                   (CUnopOpt (Repeat 1 (width - sz))
                                             (CBinopOpt (Sel sz) a (CConst (Bits.of_nat (log2 sz) (pred sz)))))
                                a))
        | ZExtL sz width => fun a c =>
          ltac:(subst cRet; simpl; rewrite <- vect_extend_end_cast;
                  exact (CBinopOpt (Concat _ _) (CConst Bits.zero) a))
        | ZExtR sz width => fun a c =>
          ltac:(subst cRet; simpl; rewrite <- vect_extend_beginning_cast;
                  exact (CBinopOpt (Concat _ _) a (CConst Bits.zero)))
        | Slice sz offset width => fun a c => c
        | Lowered (IgnoreBits _) => fun a c => CConst Ob
        | Lowered (DisplayBits _) => fun a c => CConst Ob
        end a (CUnop fn a) in
    COpt c.

    Lemma lt_plus_minus_r :
      forall n m : nat, n < m -> n + (m - n) = m.
    Proof.
      auto using le_plus_minus_r, Nat.lt_le_incl.
    Defined.

    Definition slice_subst_macro {sz} offset {width}
               (c1: circuit sz) (c2: circuit width) :=
      match le_gt_dec offset sz with
      | left pr =>
        rew (le_plus_minus_r _ _ pr) in
            (CBinopOpt (Concat _ _)
                       (match le_gt_dec width (sz - offset) with
                        | left pr =>
                          rew (le_plus_minus_r _ _ pr) in
                              (CBinopOpt (Concat _ _) (CUnopOpt (Slice _ (offset + width) (sz - offset - width)) c1) c2)
                        | right _ =>
                          CUnopOpt (Slice _ 0 (sz - offset)) c2
                        end)
                       (CUnopOpt (Slice sz 0 offset) c1))
      | right _ => c1
      end.

    Definition compile_binop (fn: fbits2)
               (c1: circuit (CSigma2 fn).(arg1Sig))
               (c2: circuit (CSigma2 fn).(arg2Sig)):
      circuit (CSigma2 fn).(retSig) :=
      let cArg1 fn := circuit (CSigma2 fn).(arg1Sig) in
      let cArg2 fn := circuit (CSigma2 fn).(arg2Sig) in
      let cRet fn := circuit (CSigma2 fn).(retSig) in
      let c :=
        match fn return circuit (CSigma2 fn).(arg1Sig) ->
                        circuit (CSigma2 fn).(arg2Sig) ->
                        circuit (CSigma2 fn).(retSig) ->
                        circuit (CSigma2 fn).(retSig) with
        | SliceSubst sz offset width => fun c1 c2 c =>
          slice_subst_macro offset c1 c2
        | _ => fun c1 c2 c => c
        end c1 c2 (CBinop fn c1 c2) in
    COpt c.

    Fixpoint compile_action
             {sig: lsig}
             {sz}
             (Gamma: ccontext sig)
             (a: action pos_t var_t CR CSigma sig sz)
             (clog: rwcircuit):
      @action_circuit sz * (ccontext sig) :=
      match a in action _ _ _ _ ts sz return ccontext ts -> @action_circuit sz * ccontext ts with
      | Fail sz => fun Gamma =>
        ({| retVal := $`"fail"`Bits.zeroes sz; (* LATER: Question mark here *)
            erwc := {| canFire := $`"fail_canFire"` Ob~0;
                       regs := clog.(regs) |} |},
         Gamma)
      | @Var _ _ _ _ _ _ _ k _ m => fun Gamma =>
        ({| retVal := CAnnotOpt (String.append "var_" (show k)) (cassoc m Gamma);
            erwc := clog |},
         Gamma)
      | Const cst => fun Gamma =>
        ({| retVal := (CConst cst);
           erwc := clog |},
         Gamma)
      | Seq r1 r2 => fun Gamma =>
        let (cex, Gamma) := (compile_action Gamma r1 clog) in
        compile_action Gamma r2 cex.(erwc)
      | @Assign _ _ _ _ _ _ _ k sz m ex => fun Gamma =>
        let (cex, Gamma) := compile_action Gamma ex clog in
        ({| retVal := $`"assign_retVal"`Bits.nil;
            erwc := cex.(erwc) |},
         creplace m cex.(retVal) Gamma)
      | @Bind _ _ _ _ _ _ sig var sz sz' ex body => fun Gamma =>
        let (ex, Gamma) := compile_action Gamma ex clog in
        let (ex, Gamma) := compile_action (CtxCons sz ex.(retVal) Gamma) body ex.(erwc) in
        (ex, ctl Gamma)
      | If cond tbranch fbranch => fun Gamma =>
        let (cond, Gamma) := compile_action Gamma cond clog in
        let (tbranch, Gamma_t) := compile_action Gamma tbranch cond.(erwc) in
        let (fbranch, Gamma_f) := compile_action Gamma fbranch cond.(erwc) in
        let cond_val := CAnnotOpt "cond" cond.(retVal) in
        ({| retVal := CMuxAnnotOpt "if_retVal" cond_val tbranch.(retVal) fbranch.(retVal);
           erwc := {| canFire := CMuxAnnotOpt "if_canFire" cond_val tbranch.(erwc).(canFire) fbranch.(erwc).(canFire);
                     regs := mux_rwsets "if_mux" cond_val tbranch.(erwc).(regs) fbranch.(erwc).(regs) |} |},
         mux_ccontext cond_val Gamma_t Gamma_f)
      | Read P0 idx => fun Gamma =>
        let reg := REnv.(getenv) clog.(regs) idx in
        ({| retVal := REnv.(getenv) cr idx;
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
            erwc := {| canFire := (val.(erwc).(canFire) &&`"write0_canFire"`
                                 (!`"no_read1"` reg.(read1) &&`"write0_canFire"`
                                  !`"no_write0"` reg.(write0) &&`"write0_canFire"`
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
            erwc := {| canFire := val.(erwc).(canFire) &&`"write1_canFire"` !`"no_write1"` reg.(write1);
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
        ({| retVal := CExternal fn a.(retVal);
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
    (ruleReg.(read0)) ==>`"read0_willFire_of_canFire"`
    (!`"read0_willFire_no_writes"` ((inReg.(write0)) ||`""` (inReg.(write1)))).

  Definition willFire_of_canFire'_write0 {sz} (ruleReg inReg: @rwdata sz) :=
    (ruleReg.(write0)) ==>`"write0_willFire_of_canFire"`
    (!`"write0_willFire_no_writes_no_read1"`
       ((inReg.(write0)) ||`""` (inReg.(write1)) ||`""` (inReg.(read1)))).

  Definition willFire_of_canFire'_rw1 {sz} (ruleReg inReg: @rwdata sz) :=
    ((ruleReg.(read1)) ||`""` (ruleReg.(write1))) ==>`"read_write1_willFire_of_canFire"`
    (!`"read_write1_willFire_no_write1"` (inReg.(write1))).

  Definition willFire_of_canFire' {sz} (ruleReg inReg: @rwdata sz) :=
    (willFire_of_canFire'_read0 ruleReg inReg) &&`""`
    (willFire_of_canFire'_write0 ruleReg inReg) &&`""`
    (willFire_of_canFire'_rw1 ruleReg inReg).

  Definition willFire_of_canFire rl_name cRule cInput : circuit 1 :=
    let wf := String.append "wF_" (show rl_name) in
    let cf := String.append "cF_" (show rl_name) in
    CAnnot wf (fold_right
                 REnv
                 (fun k '(ruleReg, inReg) acc =>
                    acc &&`wf` willFire_of_canFire' ruleReg inReg)
                 (zip REnv cRule.(regs) cInput)
                 (CAnnot cf cRule.(canFire))).

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
             {sz} (rs: list reg_t)
             (input: rwset) (rl: @action_circuit sz) (rl_name: rule_name_t)
    : @action_circuit sz :=
    let bundle := ccreate rs (fun r _ => REnv.(getenv) input r) in
    {| erwc := bundleref_wrap_erwc rl_name rs bundle rl.(erwc);
       retVal := rl.(retVal) |}.

  Context (rules: rule_name_t -> rule pos_t var_t CR CSigma).
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
      let input := mux_rwsets (show rl_name ++ "_out") will_fire acc input in
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

Arguments readRegisters {rule_name_t reg_t ext_fn_t} CR CSigma idx : assert.
Arguments rwdata {rule_name_t reg_t ext_fn_t} CR CSigma sz : assert.
Arguments action_circuit {rule_name_t reg_t ext_fn_t} CR CSigma REnv sz : assert.
Arguments scheduler_circuit {rule_name_t reg_t ext_fn_t} CR CSigma REnv : assert.
Arguments register_update_circuitry rule_name_t {reg_t ext_fn_t} CR CSigma REnv : assert.
