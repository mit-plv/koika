Require Import SGA.Common SGA.Environments SGA.Syntax SGA.Types.
Require Coq.Vectors.Vector.
Import Vector.VectorNotations.

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
    : circuit(Sigma idx).(retType).
End Circuit.

Arguments circuit {reg_t fn_t} R Sigma sz.

Module CircuitNotations.
  Notation "f [ arg ]" :=
    (CExternal f arg (CConst w0))
      (at level 99, arg at level 99, format "f [ arg ]") : circuit.
  Notation "f [ arg1 ',' arg2 ]" :=
    (CExternal f arg1 arg2)
      (at level 99, arg1 at level 99, arg2 at level 99,
       format "f [ arg1 ','  arg2 ]") : circuit.
  Notation "# reg" := (CReadRegister reg) (at level 75, format "# reg") : circuit.
  Notation "$ c" := (CConst c) (at level 75, format "$ c") : circuit.
  Notation "! c" := (CNot c) (at level 30, right associativity, format "! c") : circuit.
  Notation "c1 && c2" := (CAnd c1 c2) (at level 40, left associativity) : circuit.
  Notation "c1 || c2" := (COr c1 c2) (at level 50, left associativity) : circuit.
  Notation "c1 ==> c2" := (COr (CNot c1) c2) (at level 70, no associativity) : circuit.
  (* Notation "s ?? c1 // c2" := (CMux s c1 c2) (at level 80, no associativity) : circuit. *)
End CircuitNotations.

Import CircuitNotations.
Local Open Scope circuit.

Section Interpretation.
  Context {reg_t fn_t: Type}.
  Context {R: reg_t -> type}.
  Context {Sigma: fn_t -> ExternalSignature}.
  Context (r: forall reg, R reg).
  Context (sigma: forall f, Sigma f).

  Fixpoint interp_circuit {n} (c: circuit R Sigma n) : option (bits n) :=
    match c with
    | CQuestionMark sz =>
      None
    | CNot c =>
      let/opt bs := interp_circuit c in
      Some (w1 (negb (bits_single bs)))
    | CAnd c1 c2 =>
      let/opt bs1 := interp_circuit c1 in
      let/opt bs2 := interp_circuit c2 in
      Some (w1 (andb (bits_single bs1) (bits_single bs2)))
    | COr c1 c2 =>
      let/opt bs1 := interp_circuit c1 in
      let/opt bs2 := interp_circuit c2 in
      Some (w1 (orb (bits_single bs1) (bits_single bs2)))
    | CMux select c1 c2 =>
      let/opt bs := interp_circuit select in
      if bits_single bs then interp_circuit c1
      else interp_circuit c2
    | CConst cst =>
      Some cst
    | CReadRegister idx =>
      Some (r idx)
    | CExternal idx arg1 arg2 =>
      let/opt bs1 := interp_circuit arg1 in
      let/opt bs2 := interp_circuit arg2 in
      Some (sigma idx bs1 bs2)
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
    {| read0 := CMux cond tReg.(read0) fReg.(read0);
       read1 := CMux cond tReg.(read1) fReg.(read1);
       write0 := CMux cond tReg.(write0) fReg.(write0);
       write1 := CMux cond tReg.(write1) fReg.(write1);
       data0 := CMux cond tReg.(data0) fReg.(data0);
       data1 := CMux cond tReg.(data1) fReg.(data1) |}.

  (* FIXME generalize to proper envs? *)
  (* Definition REnv.(putenv) {K} `{EqDec K} {Fn: K -> Type} (fn: forall k, Fn k) (k: K) (v: Fn k): (forall k, Fn k). *)
  (*   intros k'. *)
  (*   destruct (eq_dec k k'); subst. *)
  (*   - exact v. *)
  (*   - exact (fn k'). *)
  (* Defined. *)

  Section Expr.
    Context (cLog: scheduler_circuit).
    Context {sig: tsig var_t}.
    Context (Gamma: ccontext sig).

    Fixpoint compile_expr
             {tau} (ex: expr var_t R Sigma sig tau)
             (clog: rwcircuit):
      @expr_circuit tau :=
      match ex in expr _ _ _ _ t return expr_circuit with
      | Var m =>
        {| retVal := cassoc m Gamma;
           erwc := clog |}
      | Const cst =>
        {| retVal := $cst;
           erwc := clog |}
      | Read P0 idx =>
        let reg := REnv.(getenv) clog.(regs) idx in
        {| retVal := REnv.(getenv) r idx;
           erwc := {| canFire := clog.(canFire) && ! reg.(read1) && ! reg.(write1);
                     regs := REnv.(putenv) clog.(regs) idx {| read0 := $(w1 true);
                                                             (* Unchanged *)
                                                             read1 := reg.(read1);
                                                             write0 := reg.(write0);
                                                             write1 := reg.(write1);
                                                             data0 := reg.(data0);
                                                             data1 := reg.(data1) |} |} |}
      | Read P1 idx =>
        let reg := REnv.(getenv) clog.(regs) idx in
        let Reg := REnv.(getenv) cLog.(sregs) idx in
        {| retVal := CMux Reg.(write0) Reg.(data0) (CMux reg.(write0) reg.(data0) (REnv.(getenv) r idx));
           erwc := {| canFire := clog.(canFire);
                     regs := REnv.(putenv) clog.(regs) idx {| read1 := $(w1 true);
                                                                  (* Unchanged *)
                                                                  read0 := reg.(read0);
                                                                  write0 := reg.(write0);
                                                                  write1 := reg.(write1);
                                                                  data0 := reg.(data0);
                                                                  data1 := reg.(data1) |} |} |}
      | Call fn a1 a2 =>
        let a1 := compile_expr a1 clog in
        let a2 := compile_expr a2 a1.(erwc) in
        {| retVal := CExternal fn a1.(retVal) a2.(retVal);
           erwc := a1.(erwc) |}
      end.
  End Expr.

  Definition zip {K} {E: Env K} {V1 V2: esig K} (ev1: E.(env_t) V1) (ev2: E.(env_t) V2)
    : E.(env_t) (fun k => V1 k * V2 k)%type :=
    E.(create) (fun k => (E.(getenv) ev1 k, E.(getenv) ev2 k)).

  Definition map2 {K} (E: Env K) {V1 V2 V3: esig K} (fn: forall k, V1 k -> V2 k -> V3 k)
             (ev1: E.(env_t) V1) (ev2: E.(env_t) V2)
    : E.(env_t) V3 :=
    E.(create) (fun k => fn k (E.(getenv) ev1 k) (E.(getenv) ev2 k)).

  Section Rule.
    Context (cLog: scheduler_circuit).

    Fixpoint compile_rule
             {sig: tsig var_t}
             (Gamma: ccontext sig)
             (rl: rule var_t R Sigma sig)
             (clog: rwcircuit):
      rule_circuit :=
      match rl in Types.rule _ _ _ t return (ccontext t -> rule_circuit) with
      | Skip =>
        fun _ => clog
      | Fail =>
        fun _ => {| canFire := $(w1 false);
                 regs := clog.(regs) |}
      | Seq r1 r2 =>
        fun Gamma =>
        compile_rule Gamma r2 (compile_rule Gamma r1 clog)
      | @Bind _ _ _ _ _ _ tau var ex body =>
        fun Gamma =>
        let ex := compile_expr cLog Gamma ex clog in
        compile_rule (CtxCons (var, tau) ex.(retVal) Gamma) body ex.(erwc)
      | If cond tbranch fbranch =>
        fun Gamma =>
        let cond := compile_expr cLog Gamma cond clog in
        let tbranch := compile_rule Gamma tbranch cond.(erwc) in
        let fbranch := compile_rule Gamma fbranch cond.(erwc) in
        {| canFire := CMux cond.(retVal) tbranch.(canFire) fbranch.(canFire);
           regs := REnv.(map2)
                              (fun k treg freg => mux_rwdata cond.(retVal) treg freg )
                              tbranch.(regs) fbranch.(regs) |}
      | Write P0 idx val =>
        fun Gamma =>
        let val := compile_expr cLog Gamma val clog in
        let reg := REnv.(getenv) val.(erwc).(regs) idx in
        {| canFire := val.(erwc).(canFire) && ! reg.(read1) &&  ! reg.(write0) &&  ! reg.(write1);
           regs := REnv.(putenv) val.(erwc).(regs) idx {| write0 := $(w1 true);
                                                  data0 := val.(retVal);
                                                  (* Unchanged *)
                                                  read0 := reg.(read0);
                                                  read1 := reg.(read1);
                                                  write1 := reg.(write1);
                                                  data1 := reg.(data1) |} |}
      | Write P1 idx val =>
        fun Gamma =>
        let val := compile_expr cLog Gamma val clog in
        let reg := REnv.(getenv) val.(erwc).(regs) idx in
        {| canFire := val.(erwc).(canFire) && ! reg.(write1);
           regs := REnv.(putenv) val.(erwc).(regs) idx {| write1 := $(w1 true);
                                                  data1 := val.(retVal);
                                                  (* Unchanged *)
                                                  read0 := reg.(read0);
                                                  read1 := reg.(read1);
                                                  write0 := reg.(write0);
                                                  data0 := reg.(data0) |} |}
      end Gamma.
  End Rule.

  (* Definition adapter (cs: scheduler_circuit) : rule_circuit := *)
  (*   {| retVal := CQuestionMark; *)
  (*      canFire := $(w1 true); *)
  (*      regs := Vector.map (fun reg => {| read0 := $(w1 false); *)
  (*                                    write0 := reg.(write0); *)
  (*                                    data0 := reg.(data0); *)
  (*                                    read1 := $(w1 false); *)
  (*                                    write1 := $(w1 false); *)
  (*                                    data1 := CQuestionMark |}) *)
  (*                        cs.(sregs) |}. *)

  Definition willFire_of_canFire' {sz} (ruleReg inReg: @rwdata sz) :=
    ((ruleReg.(read0) || ruleReg.(write0))  ==>
     (! (inReg.(write0) || inReg.(write1) || inReg.(read1)))) &&
    ((ruleReg.(read1) || ruleReg.(write1))  ==>
     (! inReg.(write1))).

  Definition willFire_of_canFire cRule cInput : circuit 1 :=
    REnv.(fold_right)
                (fun k '(ruleReg, inReg) acc =>
                   acc && willFire_of_canFire' ruleReg inReg)
                (zip cRule.(regs) cInput.(sregs)) cRule.(canFire).

  Arguments willFire_of_canFire' : simpl never.

  Definition init_rwdata sz :=
    {| data0 := CQuestionMark sz;
       data1 := CQuestionMark sz;
       read0 := $(w1 false);
       read1 := $(w1 false);
       write0 := $(w1 false);
       write1 := $(w1 false) |}.

  Definition init_rwcircuit (_: unit) :=
    {| canFire := $(w1 true);
       regs := REnv.(create) (fun k => init_rwdata (R k)) |}.

  Definition init_rule_circuit (_: unit) :=
    init_rwcircuit tt.

  Fixpoint compile_scheduler'
           (s: scheduler var_t R Sigma)
           (input: scheduler_circuit):
    scheduler_circuit :=
    match s with
    | Done =>
      input
    | Try rl st sf =>
      let rl := compile_rule input CtxEmpty rl (init_rule_circuit tt) in
      let acc := {| sregs := REnv.(map2) (fun _ ruleReg inReg =>
                                               {| read0 := ruleReg.(read0) || inReg.(read0);
                                                  read1 := ruleReg.(read1) || inReg.(read1);
                                                  write0 := ruleReg.(write0) || inReg.(write0);
                                                  write1 := ruleReg.(write1) || inReg.(write1);
                                                  data0 := ruleReg.(data0);
                                                  data1 := ruleReg.(data1) |})
                                            rl.(regs) input.(sregs) |} in
      let st := compile_scheduler' st acc in
      let sf := compile_scheduler' sf input in
      let will_fire := willFire_of_canFire rl input in
      {| sregs := REnv.(map2) (fun _ tReg fReg =>
                                    {| read0 := CMux will_fire tReg.(read0) fReg.(read0);
                                       read1 := CMux will_fire tReg.(read1) fReg.(read1);
                                       write0 := CMux will_fire tReg.(write0) fReg.(write0);
                                       write1 := CMux will_fire tReg.(write1) fReg.(write1);
                                       data0 := CMux will_fire tReg.(data0) fReg.(data0);
                                       data1 := CMux will_fire tReg.(data1) fReg.(data1) |})
                                 st.(sregs) sf.(sregs) |}
    end.

  Definition commit_rwdata {sz} (reg: @rwdata sz) initial_value : circuit sz :=
    CMux reg.(write1) reg.(data1) (CMux reg.(write0) reg.(data0) initial_value).

  Definition compile_scheduler
             (s: scheduler var_t R Sigma)
    : REnv.(env_t) (fun reg => circuit (R reg)) :=
    let s := compile_scheduler' s {| sregs := REnv.(create) (fun k => init_rwdata (R k)) |} in
    REnv.(map2) (fun k r1 r2 => commit_rwdata r1 r2) s.(sregs) r.
End CircuitCompilation.

Arguments rwdata: clear implicits.
Arguments rule_circuit: clear implicits.
Arguments scheduler_circuit: clear implicits.
