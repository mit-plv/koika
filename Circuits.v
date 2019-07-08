Require Import SGA.Common SGA.Syntax SGA.Environments.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Instance EqEnv {K V: Type} (eqdec: forall k k': K, {k = k'} + {k <> k'}) : Env K V.
Proof.
  refine ({| env_t := list (K * V);
             env_nil := nil;
             getenv e k :=
               match List.find (fun '(k', v) => if eqdec k k' then true else false) e with
               | Some (_, v) => Some v
               | None => None
               end;
             putenv e k v := (k, v) :: e |}); intros.
  - abstract (reflexivity).
  - abstract (cbn; destruct eqdec; congruence).
  - abstract (cbn; destruct eqdec; congruence).
  - abstract (cbn; destruct eqdec; subst; split;
              intuition; repeat cleanup_step; eauto; congruence).
  - abstract (cbn; destruct eqdec; subst; split;
              intuition; repeat cleanup_step; eauto; congruence).
Defined.

Scheme Equality for string.
Instance StringEnv (V: Type) : Env string V := EqEnv string_eq_dec.
Instance NatEnv (V: Type) : Env nat V := EqEnv PeanoNat.Nat.eq_dec.

Inductive circuit {TDo: Type} : Type :=
| CQuestionMark
| CNot (c: circuit)
| CAnd (c1 c2: circuit)
| COr (c1 c2: circuit)
| CMux (select c1 c2: circuit)
| CConst (cst: bits)
| Do (s: TDo).
Arguments circuit: clear implicits.

Notation "$ c" := (CConst c) (at level 75) : circuit.
Notation "~ c" := (CNot c) (at level 75, right associativity) : circuit.
Notation "c1 && c2" := (CAnd c1 c2) (at level 40, left associativity) : circuit.
Notation "c1 || c2" := (COr c1 c2) (at level 50, left associativity) : circuit.
Notation "c1 ==> c2" := (COr (CNot c1) c2) (at level 70, no associativity) : circuit.
(* Notation "s ?? c1 // c2" := (CMux s c1 c2) (at level 80, no associativity) : circuit. *)
Open Scope circuit.

Record rwdata {T} :=
  { read0: circuit T;
    read1: circuit T;
    write0: circuit T;
    write1: circuit T;
    data0: circuit T;
    data1: circuit T;
    original_data: circuit T }.
Arguments rwdata: clear implicits.

Require Vector.

Definition rwset T n := Vector.t (rwdata T) n.

Record compiled_rule {T n} :=
  { canFire: circuit T;
    regs: rwset T n;
    retVal: circuit T }.
Arguments compiled_rule: clear implicits.

Record compiled_scheduler {T n} :=
  { sregs: rwset T n }.
Arguments compiled_scheduler: clear implicits.

Definition init_register {T} (initial_data: circuit T) :=
  {| data0 := CQuestionMark;
     data1 := CQuestionMark;
     read0 := $[false];
     read1 := $[false];
     write0 := $[false];
     write1 := $[false];
     original_data := initial_data |}.

Section CircuitCompilation.
  Context {TDo: Type}.
  Context {TVar TFn: Type}.
  Context {nRegs: nat}.

  Notation rwdata := (rwdata TDo).
  Notation circuit := (circuit TDo).
  Notation compiled_rule := (compiled_rule TDo nRegs).
  Notation compiled_scheduler := (compiled_scheduler TDo nRegs).

  Context {GammaEnv: Env TVar circuit}. (* Tracks only retvals *)
  Context {SigmaEnv: Env TFn (list circuit -> circuit)}.

  Context (Sigma: SigmaEnv.(env_t)).
  (* Context (V: RegEnv.(env_t)). *)

  Definition idx_of_nat n :=
    match Fin.of_nat n nRegs with
    | inleft idx => Some idx
    | _ => None
    end.

  Fixpoint compile_rule
           (Gamma: GammaEnv.(env_t))
           (r: rule TVar TFn)
           (input: compiled_rule):
    option compiled_rule :=
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
      Some {| canFire := CMux cCond.(retVal) cTbr.(canFire) cTbr.(canFire);
              retVal := CMux cCond.(retVal) cTbr.(retVal) cFbr.(retVal);
              regs := Vector.map2 (fun tReg fReg =>
                                    {| read0 := CMux cCond.(retVal) tReg.(read0) fReg.(read0);
                                       read1 := CMux cCond.(retVal) tReg.(read1) fReg.(read1);
                                       write0 := CMux cCond.(retVal) tReg.(write0) fReg.(write0);
                                       write1 := CMux cCond.(retVal) tReg.(write1) fReg.(write1);
                                       data0 := CMux cCond.(retVal) tReg.(data0) fReg.(data0);
                                       data1 := CMux cCond.(retVal) tReg.(data1) fReg.(data1);
                                       original_data := tReg.(original_data) |})
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
              retVal := (Vector.nth input.(regs) idx).(original_data);
              regs := Vector.replace input.(regs) idx {| read0 := $[true];
                                                        (* Unchanged *)
                                                        read1 := reg.(read1);
                                                        write0 := reg.(write0);
                                                        write1 := reg.(write1);
                                                        data0 := reg.(data0);
                                                        data1 := reg.(data1);
                                                        original_data := reg.(original_data) |} |})
    | Read P1 idx =>
      opt_bind (idx_of_nat idx) (fun idx =>
      let reg := Vector.nth input.(regs) idx in
      Some {| canFire := input.(canFire);
              retVal := CMux reg.(write0) reg.(data0) reg.(original_data);
              regs := Vector.replace input.(regs) idx {| read1 := $[true];
                                                        (* Unchanged *)
                                                        read0 := reg.(read0);
                                                        write0 := reg.(write0);
                                                        write1 := reg.(write1);
                                                        data0 := reg.(data0);
                                                        data1 := reg.(data1);
                                                        original_data := reg.(original_data) |} |})
    | Write P0 idx val =>
      opt_bind (compile_rule Gamma val input) (fun cVal =>
      opt_bind (idx_of_nat idx) (fun idx =>
      let reg := Vector.nth cVal.(regs) idx in
      Some {| canFire := input.(canFire) && ~ reg.(read1) &&  ~ reg.(write0) &&  ~ reg.(write1);
              retVal := $[];
              regs := Vector.replace cVal.(regs) idx {| data0 := input.(retVal);
                                                       write0 := $[true];
                                                       (* Unchanged *)
                                                       read0 := reg.(read0);
                                                       read1 := reg.(read1);
                                                       write1 := reg.(write1);
                                                       data1 := reg.(data1);
                                                       original_data := reg.(original_data) |} |}))
    | Write P1 idx val =>
      opt_bind (compile_rule Gamma val input) (fun cVal =>
      opt_bind (idx_of_nat idx) (fun idx =>
      let reg := Vector.nth cVal.(regs) idx in
      Some {| canFire := input.(canFire) && ~ reg.(write1);
              retVal := $[];
              regs := Vector.replace cVal.(regs) idx {| write1 := $[true];
                                                       data1 := input.(retVal);
                                                       (* Unchanged *)
                                                       read0 := reg.(read0);
                                                       read1 := reg.(read1);
                                                       write0 := reg.(write0);
                                                       data0 := reg.(data0);
                                                       original_data := reg.(original_data) |} |}))
    | Call idx args =>
      opt_bind (getenv Sigma idx) (fun cFn =>
      opt_bind (List.fold_left (fun acc arg =>
                                  opt_bind acc (fun '(input, cArgs) =>
                                  opt_bind (compile_rule Gamma arg input) (fun cArg =>
                                  Some (cArg, cArg.(retVal) :: cArgs))))
                               args (Some (input, []))) (fun '(input, cArgs) =>
      Some {| retVal := cFn cArgs;
              (* Unchanged *)
              canFire := input.(canFire);
              regs := input.(regs) |}))
    end.

  Definition adapt_register (data0 data1 initial_data: circuit) :=
    {| data0 := data0;
       data1 := data1;
       read0 := $[false];
       read1 := $[false];
       write0 := $[false];
       write1 := $[false];
       original_data := initial_data |}.

  Definition adapter (cs: compiled_scheduler) : compiled_rule :=
    {| retVal := CQuestionMark;
       canFire := $[true];
       regs := Vector.map (fun reg => adapt_register reg.(data0) reg.(data1) reg.(original_data)) cs.(sregs) |}.

  Fixpoint compile_scheduler'
           (s: scheduler TVar TFn)
           (input: compiled_scheduler):
    option compiled_scheduler :=
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
                                             data1 := ruleReg.(data1);
                                             original_data := inReg.(original_data) |})
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
                                         data1 := CMux will_fire tReg.(data1) fReg.(data1);
                                         original_data := tReg.(original_data) |})
                                   cSt.(sregs) cSf.(sregs) |}))))
    end.

  Definition compile_scheduler (s: scheduler TVar TFn) (registers: Vector.t circuit nRegs) :=
    compile_scheduler' s {| sregs := Vector.map init_register registers |}.
End CircuitCompilation.

Section Ex.
  Open Scope string_scope.
  Example testprog : rule string string :=
    (Bind "x" (Read P0 0)
          (If (Call "even" [Var "x"])
              (Write P0 0 (Const [false; true]))
              (Write P0 0 (Const [true; false])))).

  Inductive specials :=
  | Even (bs: list (circuit specials))
  | Input (field: string)
  | ReadReg (idx: nat).

  Notation circuit := (circuit specials).
  Notation compiled_rule := (compiled_rule specials).

  Definition fnenv : (StringEnv (list circuit -> circuit)).(env_t) :=
    putenv env_nil "even" (fun args => Do (Even args): circuit).

  Import Vector.VectorNotations.
  Definition input :=
    [Do (ReadReg 0)].

  Compute (compile_scheduler fnenv (Try testprog Done Done) input).
End Ex.