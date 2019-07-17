Require Import SGA.Common SGA.Environments SGA.Syntax SGA.TypedSyntax.
Require Import Coq.Strings.String.
Open Scope string_scope.

Section Circuit.
  Context {reg_t fn_t: Type}.
  Context {R: reg_t -> type}.
  Context {Sigma: fn_t -> ExternalSignature}.

  Inductive circuit : nat -> Type :=
  | CQuestionMark sz: circuit sz
  | CNot (c: circuit 1): circuit 1
  | CAnd (c1 c2: circuit 1): circuit 1
  | COr (c1 c2: circuit 1): circuit 1
  | CMux {sz} (select: circuit 1) (c1 c2: circuit sz): circuit sz
  | CConst {sz} (cst: bits sz): circuit sz
  | CReadRegister (reg: reg_t): circuit (R reg)
  | CExternal (idx: fn_t)
              (a1: circuit (Sigma idx).(arg1Type))
              (a2: circuit (Sigma idx).(arg2Type))
    : circuit (Sigma idx).(retType)
  | CAnnot {sz} (annot: string) (c: circuit sz) : circuit sz.
End Circuit.

Arguments circuit {reg_t fn_t} R Sigma sz.

Module CircuitNotations.
  Notation "f [ arg ]` an `" :=
    (CAnnot an (CExternal f arg (CConst Ob)))
      (at level 99, arg at level 99, format "f [ arg ]` an `") : circuit.
  Notation "f [ arg1 ',' arg2 ]` an `" :=
    (CAnnot an (CExternal f arg1 arg2))
      (at level 99, arg1 at level 99, arg2 at level 99,
       format "f [ arg1 ','  arg2 ]` an `") : circuit.
  Notation "#` an ` reg" :=
    (CAnnot an (CReadRegister reg))
      (at level 75, format "#` an ` reg") : circuit.
  Notation "$` an ` c" :=
    (CAnnot an (CConst c))
      (at level 75, format "$` an ` c") : circuit.
  Notation "!` an ` c" :=
    (CAnnot an (CNot c))
      (at level 30, right associativity, format "!` an ` c") : circuit.
  Notation "c1 &&` an `  c2" :=
    (CAnnot an (CAnd c1 c2))
      (at level 40, left associativity) : circuit.
  Notation "c1 ||` an `  c2" :=
    (CAnnot an (COr c1 c2))
      (at level 50, left associativity) : circuit.
  Notation "c1 ==>` an ` c2" :=
    (CAnnot an (COr (CAnnot "impl" (CNot c1)) c2))
      (at level 70, no associativity) : circuit.
  (* Notation "s ?? c1 // c2" := (CMux s c1 c2) (at level 80, no associativity) : circuit. *)
End CircuitNotations.

Import CircuitNotations.
Local Open Scope circuit.

Section Interpretation.
  Context {reg_t fn_t: Type}.
  Context {R: reg_t -> type}.
  Context {Sigma: fn_t -> ExternalSignature}.
  Context {REnv: Env reg_t}.
  Context (r: REnv.(env_t) R).
  Context (sigma: forall f, Sigma f).

  Fixpoint interp_circuit {n} (c: circuit R Sigma n) : option (bits n) :=
    match c with
    | CQuestionMark sz =>
      None
    | CNot c =>
      let/opt bs := interp_circuit c in
      Some (w1 (negb (Bits.single bs)))
    | CAnd c1 c2 =>
      let/opt bs1 := interp_circuit c1 in
      let/opt bs2 := interp_circuit c2 in
      Some (w1 (andb (Bits.single bs1) (Bits.single bs2)))
    | COr c1 c2 =>
      let/opt bs1 := interp_circuit c1 in
      let/opt bs2 := interp_circuit c2 in
      Some (w1 (orb (Bits.single bs1) (Bits.single bs2)))
    | CMux select c1 c2 =>
      let/opt bs := interp_circuit select in
      if Bits.single bs then interp_circuit c1
      else interp_circuit c2
    | CConst cst =>
      Some cst
    | CReadRegister idx =>
      Some (REnv.(getenv) r idx)
    | CExternal idx arg1 arg2 =>
      let/opt bs1 := interp_circuit arg1 in
      let/opt bs2 := interp_circuit arg2 in
      Some (sigma idx bs1 bs2)
    | CAnnot _ c =>
      interp_circuit c
    end.
End Interpretation.

Section CircuitCompilation.
  Context {var_t reg_t fn_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.
  Context {R: reg_t -> type}.
  Context {Sigma: fn_t -> ExternalSignature}.
  Context {REnv: Env reg_t}.
  Context (r: REnv.(env_t) (fun reg => circuit R Sigma (R reg))).
  Context (sigma: forall f, Sigma f).

  Notation circuit := (circuit R Sigma).

  Record rwdata {sz} :=
    { read0: circuit 1;
      read1: circuit 1;
      write0: circuit 1;
      write1: circuit 1;
      data0: circuit sz;
      data1: circuit sz }.

  Definition rwset :=
    REnv.(env_t) (fun reg => @rwdata (R reg)).

  Record rwcircuit :=
    { canFire: circuit 1;
      regs: rwset }.

  Record expr_circuit {sz} :=
    { erwc: rwcircuit;
      retVal: circuit sz }.

  Definition rule_circuit :=
    rwcircuit.

  Record scheduler_circuit :=
    { sregs: rwset }.

  Definition ccontext (sig: tsig var_t) :=
    context (fun '(k, tau) => circuit (Nat_of_type tau)) sig.

  Definition mux_rwdata {sz} (cond: circuit 1) (tReg fReg: @rwdata sz) :=
    let an := "if_test" in
    {| read0 := CAnnot an (CMux cond (tReg.(read0)) (fReg.(read0)));
       read1 := CAnnot an (CMux cond (tReg.(read1)) (fReg.(read1)));
       write0 := CAnnot an (CMux cond (tReg.(write0)) (fReg.(write0)));
       write1 := CAnnot an (CMux cond (tReg.(write1)) (fReg.(write1)));
       data0 := CAnnot an (CMux cond (tReg.(data0)) (fReg.(data0)));
       data1 := CAnnot an (CMux cond (data1 tReg) (data1 fReg)) |}.

  Section Expr.
    Context {sig: tsig var_t}.
    Context (Gamma: ccontext sig).

    Fixpoint compile_expr
             {tau} (ex: expr var_t R Sigma sig tau)
             (clog: rwcircuit):
      @expr_circuit tau :=
      match ex in expr _ _ _ _ t return expr_circuit with
      | Var m =>
        {| retVal := CAnnot "var_reference" (cassoc m Gamma);
           erwc := clog |}
      | Const cst =>
        {| retVal := $`"constant_value_from_source"`cst;
           erwc := clog |}
      | Read P0 idx =>
        let reg := REnv.(getenv) clog.(regs) idx in
        {| retVal := CAnnot "read0" (REnv.(getenv) r idx);
           erwc := {| canFire := (clog.(canFire) &&`"read0_cF"`
                                !`"no_read1"` reg.(read1) &&`"read0_cF"`
                                !`"no_write1"` reg.(write1));
                     regs := REnv.(putenv) clog.(regs) idx {| read0 := $`"read0"` (w1 true);
                                                             (* Unchanged *)
                                                             read1 := reg.(read1);
                                                             write0 := reg.(write0);
                                                             write1 := reg.(write1);
                                                             data0 := reg.(data0);
                                                             data1 := reg.(data1) |} |} |}
      | Read P1 idx =>
        let reg := REnv.(getenv) clog.(regs) idx in
        {| retVal := reg.(data0);
           (* retVal := CAnnot "read1_retVal_from_L_pred" *)
           (*                  (CMux (Reg.(write0)) (Reg.(data0)) *)
           (*                        (CAnnot "read1_retVal_from_l_pred" *)
           (*                                 (CMux (reg.(write0)) (reg.(data0)) *)
           (*                                       (CAnnot "read1_retVal_from_reg" *)
           (*                                                (REnv.(getenv) r idx))))); *)
           erwc := {| canFire := clog.(canFire);
                     regs := REnv.(putenv) clog.(regs) idx {| read1 := $`"read1"` (w1 true);
                                                             (* Unchanged *)
                                                             read0 := reg.(read0);
                                                             write0 := reg.(write0);
                                                             write1 := reg.(write1);
                                                             data0 := reg.(data0);
                                                             data1 := reg.(data1) |} |} |}
      | Call fn a1 a2 =>
        let a1 := compile_expr a1 clog in
        let a2 := compile_expr a2 a1.(erwc) in
        {| retVal := fn [a1.(retVal), a2.(retVal)]`"Call_from_source"`;
           erwc := a2.(erwc) |}
      end.
  End Expr.

  Section Rule.
    Fixpoint compile_rule
             {sig: tsig var_t}
             (Gamma: ccontext sig)
             (rl: rule var_t R Sigma sig)
             (clog: rwcircuit):
      rule_circuit :=
      match rl in TypedSyntax.rule _ _ _ t return (ccontext t -> rule_circuit) with
      | Skip =>
        fun _ => clog
      | Fail =>
        fun _ => {| canFire := $`"fail_cF"` (w1 false);
                 regs := clog.(regs) |}
      | Seq r1 r2 =>
        fun Gamma =>
        compile_rule Gamma r2 (compile_rule Gamma r1 clog)
      | @Bind _ _ _ _ _ _ tau var ex body =>
        fun Gamma =>
        let ex := compile_expr Gamma ex clog in
        compile_rule (CtxCons (var, tau) ex.(retVal) Gamma) body ex.(erwc)
      | If cond tbranch fbranch =>
        fun Gamma =>
        let cond := compile_expr Gamma cond clog in
        let tbranch := compile_rule Gamma tbranch cond.(erwc) in
        let fbranch := compile_rule Gamma fbranch cond.(erwc) in
        {| canFire := CAnnot "if_cF" (CMux cond.(retVal) tbranch.(canFire) fbranch.(canFire));
           regs := REnv.(map2)
                              (fun k treg freg => mux_rwdata cond.(retVal) treg freg )
                              tbranch.(regs) fbranch.(regs) |}
      | Write P0 idx val =>
        fun Gamma =>
        let val := compile_expr Gamma val clog in
        let reg := REnv.(getenv) val.(erwc).(regs) idx in
        {| canFire := (val.(erwc).(canFire) &&`"write0_cF"`
                      !`"no_read1"` reg.(read1) &&`"write0_cF"`
                      !`"no_write0"` reg.(write0) &&`"write0_cF"`
                      !`"no_write1"` reg.(write1));
           regs := REnv.(putenv) val.(erwc).(regs) idx {| write0 := $`"write0"` (w1 true);
                                                         data0 := val.(retVal);
                                                         (* Unchanged *)
                                                         read0 := reg.(read0);
                                                         read1 := reg.(read1);
                                                         write1 := reg.(write1);
                                                         data1 := reg.(data1) |} |}
      | Write P1 idx val =>
        fun Gamma =>
        let val := compile_expr Gamma val clog in
        let reg := REnv.(getenv) val.(erwc).(regs) idx in
        {| canFire := val.(erwc).(canFire) &&`"write1_cF"` !`"no_write1"` reg.(write1);
           regs := REnv.(putenv) val.(erwc).(regs) idx {| write1 := $`"write1"` (w1 true);
                                                  data1 := val.(retVal);
                                                  (* Unchanged *)
                                                  read0 := reg.(read0);
                                                  read1 := reg.(read1);
                                                  write0 := reg.(write0);
                                                  data0 := reg.(data0) |} |}
      end Gamma.
  End Rule.

  Definition adapter (cs: scheduler_circuit) : rule_circuit :=
    {| canFire := $`"cF_init"` (w1 true);
       regs := REnv.(map) (fun k reg => {| read0 := $`"init_no_read0"` (w1 false);
                                       read1 := $`"init_no_read1"` (w1 false);
                                       write0 := $`"init_no_write0"` (w1 false);
                                       write1 := $`"init_no_write1"` (w1 false);
                                       data0 := reg.(data0);
                                       data1 := CQuestionMark _ |})
                         cs.(sregs) |}.

  Definition willFire_of_canFire' {sz} (ruleReg inReg: @rwdata sz) :=
    ((ruleReg.(read0)) ==>`"read0_wF_of_cF"`
     (!`"read0_wF_no_writes"`
        ((inReg.(write0)) ||`""` (inReg.(write1))))) &&`""`
    ((ruleReg.(write0)) ==>`"write0_wF_of_cF"`
     (!`"write0_wF_no_writes_no_read1"`
        ((inReg.(write0)) ||`""` (inReg.(write1)) ||`""` (inReg.(read1))))) &&`""`
    (((ruleReg.(read1)) ||`""` (ruleReg.(write1))) ==>`"read_write1_wF_of_cF"`
     (!`"read_write1_wF_no_write1"` (inReg.(write1)))).

  Definition willFire_of_canFire cRule cInput : circuit 1 :=
    REnv.(fold_right)
           (fun k '(ruleReg, inReg) acc =>
              acc &&`"wF_fold_res"` willFire_of_canFire' ruleReg inReg)
           (REnv.(zip) cRule.(regs) cInput.(sregs)) cRule.(canFire).

  Arguments willFire_of_canFire' : simpl never.

  Fixpoint compile_scheduler'
           (s: scheduler var_t R Sigma)
           (input: scheduler_circuit):
    scheduler_circuit :=
    match s with
    | Done =>
      input
    | Try rl st sf =>
      let rl := compile_rule CtxEmpty rl (adapter input) in
      let an := "merge_results" in
      let acc := {| sregs := REnv.(map2) (fun _ ruleReg inReg =>
                                               {| read0 := (ruleReg.(read0)) ||`an` (inReg.(read0));
                                                  read1 := (ruleReg.(read1)) ||`an` (inReg.(read1));
                                                  write0 := (ruleReg.(write0)) ||`an` (inReg.(write0));
                                                  write1 := (ruleReg.(write1)) ||`an` (inReg.(write1));
                                                  data0 := (ruleReg.(data0));
                                                  data1 := (data1 ruleReg) |})
                                            rl.(regs) input.(sregs) |} in
      let st := compile_scheduler' st acc in
      let sf := compile_scheduler' sf input in
      let will_fire := willFire_of_canFire rl input in
      let an := "merge_logs" in
      {| sregs := REnv.(map2) (fun _ tReg fReg =>
                                {| read0 := CAnnot an (CMux will_fire (tReg.(read0)) (fReg.(read0)));
                                   read1 := CAnnot an (CMux will_fire (tReg.(read1)) (fReg.(read1)));
                                   write0 := CAnnot an (CMux will_fire (tReg.(write0)) (fReg.(write0)));
                                   write1 := CAnnot an (CMux will_fire (tReg.(write1)) (fReg.(write1)));
                                   data0 := CAnnot an (CMux will_fire (tReg.(data0)) (fReg.(data0)));
                                   data1 := CAnnot an (CMux will_fire (data1 tReg) (data1 fReg)) |})
                             st.(sregs) sf.(sregs) |}
    end.

  Definition commit_rwdata {sz} (reg: @rwdata sz) initial_value : circuit sz :=
    CAnnot "commit_write1"
           (CMux (reg.(write1))
                 (reg.(data1))
                 (CAnnot "commit_write0"
                         (CMux (reg.(write0))
                               (reg.(data0))
                               (CAnnot "commit_unchanged" initial_value)))).

  Definition state_transition_circuit :=
    REnv.(env_t) (fun reg => circuit (R reg)).

  Definition init_scheduler_rwdata idx : rwdata :=
    {| read0 := $`"sched_init_no_read0"` (w1 false);
       read1 := $`"sched_init_no_read1"` (w1 false);
       write0 := $`"sched_init_no_write0"` (w1 false);
       write1 := $`"sched_init_no_write1"` (w1 false);
       data0 := CAnnot "sched_init_data0_is_reg" (REnv.(getenv) r idx);
       data1 := CAnnot "sched_init_no_data1" (CQuestionMark _) |}.

  Definition init_scheduler_circuit : scheduler_circuit :=
    {| sregs := REnv.(create) init_scheduler_rwdata |}.

  Definition compile_scheduler (s: scheduler var_t R Sigma) : state_transition_circuit :=
    let s := compile_scheduler' s init_scheduler_circuit in
    REnv.(map2) (fun k r1 r2 => commit_rwdata r1 r2) s.(sregs) r.
End CircuitCompilation.

Arguments rwdata {_ _}.
Arguments rule_circuit {_ _}.
Arguments scheduler_circuit {_ _}.
Arguments state_transition_circuit {_ _}.
