Require Import SGA.Common SGA.Syntax SGA.Environments.
Require Import Coq.Strings.String.
Require Import Coq.Vectors.Vector Coq.Lists.List.
Import ListNotations.

Section Circuit.
  Context {TFn: Type}.

  Inductive circuit : Type :=
  | CQuestionMark
  | CNot (c: circuit)
  | CAnd (c1 c2: circuit)
  | COr (c1 c2: circuit)
  | CMux (select c1 c2: circuit)
  | CConst (cst: bits)
  | CExternal (e: TFn) (args: list circuit).

  Definition circuits nRegs :=
    Vector.t circuit nRegs.
End Circuit.

Arguments circuit: clear implicits.

Notation "$ c" := (CConst c) (at level 75) : circuit.
Notation "~ c" := (CNot c) (at level 75, right associativity) : circuit.
Notation "c1 && c2" := (CAnd c1 c2) (at level 40, left associativity) : circuit.
Notation "c1 || c2" := (COr c1 c2) (at level 50, left associativity) : circuit.
Notation "c1 ==> c2" := (COr (CNot c1) c2) (at level 70, no associativity) : circuit.
(* Notation "s ?? c1 // c2" := (CMux s c1 c2) (at level 80, no associativity) : circuit. *)
Open Scope circuit.

Section Interpretation.
  Context {TFn: Type}.
  Context (interp_external: TFn -> list bits -> option bits).

  Fixpoint interp_circuit c :=
    match c with
    | CQuestionMark => None
    | CNot c =>
      opt_bind (interp_circuit c) (fun bs =>
      Some (List.map negb bs))
    | CAnd c1 c2 =>
      opt_bind (interp_circuit c1) (fun bs1 =>
      opt_bind (interp_circuit c2) (fun bs2 =>
      Some (List.map (fun '(b1, b2) => andb b1 b2) (List.combine bs1 bs2))))
    | COr c1 c2 =>
      opt_bind (interp_circuit c1) (fun bs1 =>
      opt_bind (interp_circuit c2) (fun bs2 =>
      Some (List.map (fun '(b1, b2) => orb b1 b2) (List.combine bs1 bs2))))
    | CMux select c1 c2 =>
      opt_bind (interp_circuit select) (fun bs =>
      match bs with
      | [b] => if b
              then interp_circuit c1
              else interp_circuit c2
      | _ => None
      end)
    | CConst cst => Some cst
    | CExternal e args =>
      opt_bind (List.fold_left (fun acc arg =>
                                  opt_bind acc (fun acc =>
                                  opt_bind (interp_circuit arg) (fun arg =>
                                  Some (arg :: acc))))
                               args (Some [])) (fun args =>
      interp_external e args)
    end.

  Definition interp_circuits (nRegs: nat) (cs: circuits nRegs) :=
    Vector.map interp_circuit cs.
End Interpretation.

Section CircuitCompilation.
  Context {TVar TFn: Type}.
  Context {nRegs: nat}.

  Notation circuit := (circuit TFn).
  Context (V: Vector.t circuit nRegs).

  Record rwdata :=
    { read0: circuit;
      read1: circuit;
      write0: circuit;
      write1: circuit;
      data0: circuit;
      data1: circuit }.
  (* Arguments rwdata: clear implicits. *)
  (* Arguments rule_circuit: clear implicits. *)

  Definition rwset := Vector.t rwdata nRegs.

  Record rule_circuit :=
    { canFire: circuit;
      regs: rwset;
      retVal: circuit }.

  Record scheduler_circuit :=
    { sregs: rwset }.
  Arguments scheduler_circuit: clear implicits.

  Context {GammaEnv: Env TVar circuit}. (* Tracks only retvals *)

  Definition idx_of_nat n :=
    match Fin.of_nat n nRegs with
    | inleft idx => Some idx
    | _ => None
    end.

  Fixpoint compile_rule
           (Gamma: GammaEnv.(env_t))
           (r: rule TVar TFn)
           (input: rule_circuit):
    option rule_circuit :=
    match r with
    | Bind var expr body =>
      opt_bind (compile_rule Gamma expr input) (fun cExpr =>
      opt_bind (compile_rule (putenv Gamma var cExpr.(retVal)) body cExpr) (fun cBody =>
      Some cBody)) (* FIXME merge and apply L *)
    | Var var =>
      opt_bind (getenv Gamma var) (fun cVal =>
      Some {| retVal := cVal;
              (* Unchanged *)
              canFire := input.(canFire);
              regs := input.(regs) |})
    | Skip =>
      Some {| retVal := $nil;
              (* Unchanged *)
              canFire := input.(canFire);
              regs := input.(regs) |}
    | Const cst =>
      Some {| retVal := $cst;
              (* Unchanged *)
              canFire := input.(canFire);
              regs := input.(regs) |}
    | If cond tbranch fbranch =>
      opt_bind (compile_rule Gamma cond input) (fun cCond =>
      opt_bind (compile_rule Gamma tbranch cCond) (fun cTbr =>
      opt_bind (compile_rule Gamma fbranch cCond) (fun cFbr =>
      Some {| canFire := cCond.(canFire) && CMux cCond.(retVal) cTbr.(canFire) cFbr.(canFire);
              retVal := CMux cCond.(retVal) cTbr.(retVal) cFbr.(retVal);
              regs := Vector.map2 (fun tReg fReg =>
                                    {| read0 := CMux cCond.(retVal) tReg.(read0) fReg.(read0);
                                       read1 := CMux cCond.(retVal) tReg.(read1) fReg.(read1);
                                       write0 := CMux cCond.(retVal) tReg.(write0) fReg.(write0);
                                       write1 := CMux cCond.(retVal) tReg.(write1) fReg.(write1);
                                       data0 := CMux cCond.(retVal) tReg.(data0) fReg.(data0);
                                       data1 := CMux cCond.(retVal) tReg.(data1) fReg.(data1) |})
                                 cTbr.(regs) cFbr.(regs) |})))
    | Fail =>
      Some {| canFire := $[false];
              (* Unchanged *)
              regs := input.(regs);
              retVal := input.(retVal) |}
    | Read P0 idx =>
      opt_bind (idx_of_nat idx) (fun idx =>
      let reg := Vector.nth input.(regs) idx in
      Some {| canFire := input.(canFire) && ~ reg.(read1) && ~ reg.(write1);
              retVal := Vector.nth V idx;
              regs := Vector.replace input.(regs) idx {| read0 := $[true];
                                                        (* Unchanged *)
                                                        read1 := reg.(read1);
                                                        write0 := reg.(write0);
                                                        write1 := reg.(write1);
                                                        data0 := reg.(data0);
                                                        data1 := reg.(data1) |} |})
    | Read P1 idx =>
      opt_bind (idx_of_nat idx) (fun idx =>
      let reg := Vector.nth input.(regs) idx in
      Some {| canFire := input.(canFire);
              retVal := CMux reg.(write0) reg.(data0) (Vector.nth V idx);
              regs := Vector.replace input.(regs) idx {| read1 := $[true];
                                                        (* Unchanged *)
                                                        read0 := reg.(read0);
                                                        write0 := reg.(write0);
                                                        write1 := reg.(write1);
                                                        data0 := reg.(data0);
                                                        data1 := reg.(data1) |} |})
    | Write P0 idx val =>
      opt_bind (compile_rule Gamma val input) (fun cVal =>
      opt_bind (idx_of_nat idx) (fun idx =>
      let reg := Vector.nth cVal.(regs) idx in
      Some {| canFire := cVal.(canFire) && ~ reg.(read1) &&  ~ reg.(write0) &&  ~ reg.(write1);
              retVal := $[];
              regs := Vector.replace cVal.(regs) idx {| write0 := $[true];
                                                       data0 := cVal.(retVal);
                                                       (* Unchanged *)
                                                       read0 := reg.(read0);
                                                       read1 := reg.(read1);
                                                       write1 := reg.(write1);
                                                       data1 := reg.(data1) |} |}))
    | Write P1 idx val =>
      opt_bind (compile_rule Gamma val input) (fun cVal =>
      opt_bind (idx_of_nat idx) (fun idx =>
      let reg := Vector.nth cVal.(regs) idx in
      Some {| canFire := cVal.(canFire) && ~ reg.(write1);
              retVal := $[];
              regs := Vector.replace cVal.(regs) idx {| write1 := $[true];
                                                       data1 := cVal.(retVal);
                                                       (* Unchanged *)
                                                       read0 := reg.(read0);
                                                       read1 := reg.(read1);
                                                       write0 := reg.(write0);
                                                       data0 := reg.(data0) |} |}))
    | Call fn args =>
      opt_bind (List.fold_left (fun acc arg =>
                                  opt_bind acc (fun '(input, cArgs) =>
                                  opt_bind (compile_rule Gamma arg input) (fun cArg =>
                                  Some (cArg, cArg.(retVal) :: cArgs))))
                               args (Some (input, []))) (fun '(lastArg, cArgs) =>
      Some {| retVal := CExternal fn cArgs;
              (* Unchanged *)
              canFire := lastArg.(canFire);
              regs := lastArg.(regs) |})
           end.

  Definition adapter (cs: scheduler_circuit) : rule_circuit :=
    {| retVal := CQuestionMark;
       canFire := $[true];
       regs := Vector.map (fun reg => {| data0 := reg.(data0);
                                     data1 := reg.(data1);
                                     read0 := $[false];
                                     read1 := $[false];
                                     write0 := $[false];
                                     write1 := $[false] |})
                         cs.(sregs) |}.

  Fixpoint compile_scheduler'
           (s: scheduler TVar TFn)
           (input: scheduler_circuit):
    option scheduler_circuit :=
    match s with
    | Done =>
      Some input
    | Try r st sf =>
      opt_bind (compile_rule env_nil r (adapter input)) (fun cRule =>
      let acc := {| sregs := Vector.map2 (fun ruleReg inReg =>
                                          {| read0 := ruleReg.(read0) || inReg.(read0);
                                             read1 := ruleReg.(read1) || inReg.(read1);
                                             write0 := ruleReg.(write0) || inReg.(write0);
                                             write1 := ruleReg.(write1) || inReg.(write1);
                                             data0 := ruleReg.(data0);
                                             data1 := ruleReg.(data1) |})
                                       cRule.(regs) input.(sregs) |} in
      opt_bind (compile_scheduler' st acc) (fun cSt =>
      opt_bind (compile_scheduler' sf input) (fun cSf =>
      let will_fire := Vector.fold_left2 (fun acc ruleReg inReg =>
                                           acc &&
                                           ((ruleReg.(read0) || ruleReg.(write0))  ==>
                                            (~ (inReg.(write0) || inReg.(write1) || inReg.(read1)))) &&
                                           ((ruleReg.(read1) || ruleReg.(write1))  ==>
                                            (~ inReg.(write1))))
                                        cRule.(canFire) cRule.(regs) input.(sregs) in
      Some ({| sregs := Vector.map2 (fun tReg fReg =>
                                      {| read0 := CMux will_fire tReg.(read0) fReg.(read0);
                                         read1 := CMux will_fire tReg.(read1) fReg.(read1);
                                         write0 := CMux will_fire tReg.(write0) fReg.(write0);
                                         write1 := CMux will_fire tReg.(write1) fReg.(write1);
                                         data0 := CMux will_fire tReg.(data0) fReg.(data0);
                                         data1 := CMux will_fire tReg.(data1) fReg.(data1) |})
                                   cSt.(sregs) cSf.(sregs) |}))))
    end.

  Definition init_rwdata :=
    {| data0 := CQuestionMark;
       data1 := CQuestionMark;
       read0 := $[false];
       read1 := $[false];
       write0 := $[false];
       write1 := $[false] |}.

  Definition commit_rwdata (reg: rwdata) initial_value : circuit :=
    CMux reg.(write1) reg.(data1) (CMux reg.(write0) reg.(data0) initial_value).

  Print Module Vector.
  Definition compile_scheduler
             (s: scheduler TVar TFn)
    : option (circuits nRegs) :=
    opt_bind (compile_scheduler' s {| sregs := Vector.const init_rwdata nRegs |}) (fun cs =>
    Some (Vector.map2 commit_rwdata cs.(sregs) V)).
End CircuitCompilation.

Arguments rwdata: clear implicits.
Arguments rule_circuit: clear implicits.
