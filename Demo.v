Require Import SGA.Notations.

Require Import Coq.Strings.String.
Open Scope string_scope.

Record demo_package_t :=
  { dp_var_t : Type;
    dp_reg_t : Type;
    dp_name_t : Type;
    dp_custom_fn_t : Type;
    sga : @sga_package_t dp_var_t dp_reg_t dp_name_t dp_custom_fn_t;
    vp : @verilog_package_t dp_var_t dp_reg_t dp_name_t dp_custom_fn_t;
    sp : @sim_package_t dp_var_t dp_reg_t dp_name_t dp_custom_fn_t }.

Notation opt := simplify_bool_1.
Notation interop_opt := (lco_opt_compose simplify_bool_1 elaborate_externals_1).
Notation uaction := (uaction unit string).

Module Ex1.
  Notation var_t := string.
  Inductive reg_t := R0 | R1.
  Inductive fn_t := Even | Odd.
  Inductive name_t := r1.

  Definition R reg : type :=
    match reg with
    | R0 => bits_t 3
    | R1 => bits_t 1
    end.

  Definition Sigma fn : ExternalSignature :=
    match fn with
    | Even => {{ bits_t 3 ~> unit_t ~> bits_t 1}}
    | Odd => {{ bits_t 3 ~> unit_t ~> bits_t 1}}
    end.

  Definition uSigma (fn: fn_t) (_ _: type) : result fn_t fn_tc_error := Success fn.

  Definition r idx : R idx :=
    match idx with
    | R0 => Ob~1~0~1
    | R1 => Ob~0
    end.

  Definition sigma idx : Sigma idx :=
    match idx with
    | Even => fun (bs: bits 3) _ => Ob~(negb (Bits.lsb bs))
    | Odd => fun (bs: bits 3) _ => Ob~(Bits.lsb bs)
    end.

  Example uactions r : uaction var_t reg_t fn_t :=
    match r with
    | r1 =>
      {$ let "x" := read0(R0) in
         if (`UCall Even (UVar "x") (UConstBits Ob)`)
         then write0(R1,`UConstBits Ob~1`)
         else write0(R1,`UConstBits Ob~1`)
                       $}
    end.

  Definition rules :=
    tc_rules R Sigma uSigma uactions.

  Example us1 : uscheduler unit name_t :=
    UTry r1 UDone UDone.

  Definition s1 :=
    tc_scheduler us1.

  Definition s1_result :=
    Eval compute in interp_scheduler (ContextEnv.(create) r) sigma rules s1.

  Definition s1_circuit :=
    compile_scheduler opt (ContextEnv.(create) (readRegisters R Sigma)) rules s1.
End Ex1.

Module Ex2.
  Definition var_t := string.
  Inductive reg_t := R0 | R1 | R2.
  Inductive ufn_t := UOr | UNot.
  Inductive fn_t := Or (n: nat) | Not (n: nat).
  Inductive name_t := negate | swap_or_replace.

  Definition R r :=
    match r with
    | R0 => bits_t 7
    | R1 => bits_t 7
    | R2 => bits_t 1
    end.

  Definition Sigma fn :=
    match fn with
    | Or n => {{ bits_t n ~> bits_t n ~> bits_t n }}
    | Not n => {{ bits_t n ~> unit_t ~> bits_t n }}
    end.

  Definition uSigma fn (tau1 _: type) :=
    let/res sz1 := assert_bits_t Arg1 tau1 in
    Success match fn with
            | UOr => Or sz1
            | UNot => Not sz1
            end.

  Example _negate : uaction var_t reg_t ufn_t  :=
    {$
       let "x" := read1(R0) in
       write1(R0,"x")
                $}.

  Example _swap_or_replace : uaction var_t reg_t ufn_t  :=
    {$
      let "should_swap" := read0(R2) in
      if "should_swap"
      then
        write0(R1,read0(R0));
        write0(R0,read0(R1))
      else
        write0(R0,`UCall UOr {$ read0(R0) $} {$  read0(R1) $} `)
                 $}.


  Example _ill_typed_write : uaction var_t reg_t ufn_t  :=
    UWrite P0 R2 (URead P0 R1).

  Example _unbound_variable : uaction var_t reg_t ufn_t  :=
    UWrite P0 R0 (UVar "y").

  Example tsched : scheduler name_t :=
    tc_scheduler (UTry swap_or_replace (UTry negate UDone UDone) (UTry negate UDone UDone)).

  Fail Example trule : rule var_t R Sigma :=
    tc_rule R Sigma uSigma _ill_typed_write.

  Fail Example trule : rule var_t R Sigma :=
    tc_rule R Sigma uSigma _unbound_variable.

  Definition r idx : R idx :=
    match idx with
    | R0 => Ob~0~1~1~0~0~1~0
    | R1 => Ob~1~1~0~0~1~1~0
    | R2 => Ob~1
    end.

  Definition sigma idx : Sigma idx :=
    match idx with
    | Or n => fun bs1 bs2 => Bits.map2 orb bs1 bs2
    | Not n => fun bs _ => Bits.map negb bs
    end.

  Definition rules : name_t -> rule var_t R Sigma :=
    tc_rules R Sigma uSigma
             (fun r => match r with
                    | negate => _negate
                    | swap_or_replace => _swap_or_replace
                    end).

  Definition tsched_result :=
    Eval compute in interp_scheduler (ContextEnv.(create) r) sigma rules tsched.
  Definition tsched_circuit :=
    compile_scheduler opt (ContextEnv.(create) (readRegisters R Sigma)) rules tsched.
End Ex2.

Notation compute t :=
  ltac:(let tt := type of t in
        let t := (eval lazy in t) in
        exact (t: tt)) (only parsing).

Module Collatz.
  Definition var_t := string.
  Inductive reg_t := R0.
  Definition ufn_t := interop_minimal_ufn_t.
  Inductive name_t := divide | multiply.

  Definition logsz := 4.
  Notation sz := (pow2 logsz).

  Definition R r :=
    match r with
    | R0 => bits_t sz
    end.

  Definition r idx : R idx :=
    match idx with
    | R0 => Bits.of_nat 16 19
    end.
  Notation uaction := (uaction var_t reg_t ufn_t).
  Notation InternalFunction := (UInternalFunction unit string reg_t ufn_t).
  (* Example NESVD 2019 *)
  Definition _divide : uaction :=
  {$
    let "v" := read0(R0) in
    let "odd" := "v"[#(Bits.zero logsz)] in
    if !"odd"
    then
       write0(R0,"v" >> #Ob~1)
    else
      fail
  $}.

  Definition TimesThree  : InternalFunction :=
    function "timeThree" ("arg1" : bits_t 16) : bits_t 16 :=
     ("arg1" << #Ob~1)  + "arg1".

  Definition _multiply : uaction :=
    {$
    let "v" := read1(R0) in
    let "odd" := "v"[#(Bits.zero logsz)] in
    if "odd"
    then
       write1(R0, (funcall TimesThree "v") +  #(Bits.one sz))
    else
      fail
        $}.

  Definition collatz : scheduler _ :=
    tc_scheduler (divide |> multiply |> done).

  Definition cr := ContextEnv.(create) r.

  (* Typechecking  *)
  Definition rules :=
    tc_rules R interop_minimal_Sigma interop_minimal_uSigma
             (fun r => match r with
                    | divide => _divide
                    | multiply => _multiply
                    end).

  Definition result :=
    compute (interp_scheduler cr interop_minimal_sigma rules collatz).

  Definition divide_result :=
    compute (interp_action cr interop_minimal_sigma CtxEmpty log_empty log_empty
                           (rules divide)).

  Definition multiply_result :=
    compute (interp_action cr interop_minimal_sigma CtxEmpty log_empty log_empty
                           (rules multiply)).

  Definition circuit :=
    compile_scheduler interop_opt (ContextEnv.(create) (readRegisters R interop_minimal_Sigma)) rules collatz.

  Definition sga_package :=
    {| sga_reg_types := R;
       sga_reg_init := r;
       sga_reg_finite := _;

       sga_custom_fn_types := interop_empty_Sigma;

       sga_reg_names r := match r with
                         | R0 => "r0"
                         end;

       sga_rules := rules;
       sga_rule_names r := match r with
                         | divide => "divide"
                         | multiply => "multiply"
                         end;

       sga_scheduler := collatz;
       sga_module_name := "collatz" |}.

  Definition package :=
    {| sga := sga_package;
       sp := {| sp_pkg := sga_package;
               sp_var_names x := x;
               sp_custom_fn_names := interop_empty_fn_names;
               sp_extfuns := None |};
       vp := {| vp_pkg := sga_package;
               vp_external_rules := List.nil;
               vp_custom_fn_names := interop_empty_fn_names |} |}.
  Check package.
End Collatz.

Require Import Coq.Lists.List.

Module Type Unpacker.
  Axiom unpack : forall reg_t custom_ufn_t (source: string), uaction string reg_t (interop_ufn_t custom_ufn_t).
End Unpacker.

Module Type Fetcher.
  Axiom custom_fn_t : Type.
  Axiom custom_Sigma : custom_fn_t -> ExternalSignature.
  Axiom custom_uSigma : custom_fn_t -> type -> type -> result custom_fn_t fn_tc_error.
  Axiom custom_fn_names : custom_fn_t -> string.
  Axiom fetch_instr : forall reg_t (pc: string), uaction string reg_t (interop_ufn_t custom_fn_t).
End Fetcher.

Definition decoded_sig :=
  {| struct_name := "instr";
     struct_fields := ("src", bits_t 8)
                       :: ("dst", bits_t 8)
                       :: ("immediate", bits_t 16)
                       :: nil |}.

Module Decoder (P: Unpacker) (F: Fetcher).
  Definition var_t := string.
  Inductive reg_t := Rpc | Rencoded | Rdecoded.
  Definition ufn_t := interop_ufn_t F.custom_fn_t.
  Inductive name_t := fetch | decode.

  Definition Sigma := interop_Sigma F.custom_Sigma.
  Definition uSigma := interop_uSigma F.custom_uSigma.

  Definition logsz := 5.
  Notation sz := (pow2 logsz).

  Definition R r :=
    match r with
    | Rpc => bits_t 3
    | Rencoded => bits_t sz
    | Rdecoded => struct_t decoded_sig
    end.

  Notation zero := (Bits.zeroes _).

  Definition r idx : R idx :=
    match idx with
    | Rpc => zero
    | Rencoded => zero
    | Rdecoded => (zero, (zero, (zero, tt)))
    end.

  Notation uaction := (uaction var_t reg_t ufn_t).

  Definition _fetch : uaction :=
    {$
    let "pc" := read0(Rpc) in
    let "encoded" := `F.fetch_instr _ "pc"` in
    write0(Rencoded,"encoded");
    write0(Rpc,"pc" + `UConstBits Ob~0~0~1`)
                $}
  .

  Definition _decode : uaction :=
    {$
    let "encoded" := read1(Rencoded) in
    write0(Rdecoded,`P.unpack _ _ "encoded"`)
     $}.

  Definition cr := ContextEnv.(create) r.

  Definition decoder : scheduler _ :=
    tc_scheduler (fetch |> decode |> done).

  (* Ltac __must_typecheck R Sigma tcres ::= *)
  (*   __must_typecheck_cbn R Sigma tcres. *)

  Notation rulemap_t :=
    (name_t -> rule string R (interop_Sigma F.custom_Sigma)).

  Definition make_package (modname: string) (rules: rulemap_t) :=
    let sga_package :=
        {| sga_reg_types := R;
           sga_reg_init := r;
           sga_reg_finite := _;

           sga_custom_fn_types := F.custom_Sigma;

           sga_reg_names r := match r with
                             | Rpc => "Rpc"
                             | Rencoded => "Rencoded"
                             | Rdecoded => "Rdecoded"
                             end;

           sga_rules := rules;
           sga_rule_names r := match r with
                             | decode => "decode"
                             | fetch => "fetch"
                             end;

           sga_scheduler := decoder;
           sga_module_name := modname |} in
    let sim :=
        {| sp_pkg := sga_package;
           sp_var_names := fun x => x;
           sp_custom_fn_names := F.custom_fn_names;

           sp_extfuns := Some "#include ""../extfuns.hpp""
using extfuns = decoder_extfuns;" |} in
    let verilog :=
        {| vp_pkg := sga_package;
           vp_external_rules := List.nil;
           vp_custom_fn_names := F.custom_fn_names |} in
    {| sga := sga_package; sp := sim; vp := verilog |}.
End Decoder.

Module ManualUnpacker <: Unpacker.
  Notation SCall fn a1 a2 :=
    (UCall (UPrimFn (UStructFn fn)) a1 a2).

  Definition unpack reg_t custom_ufn_t encoded: uaction string reg_t (interop_ufn_t custom_ufn_t) :=
    {$
       let "imm" := `SCall (UDoBits decoded_sig GetField "immediate") {$ encoded $} (UConstBits Ob)` in
       let "src" := `SCall (UDoBits decoded_sig GetField "src") {$ encoded $} (UConstBits Ob)` in
       let "dst" := `SCall (UDoBits decoded_sig GetField "dst") {$ encoded $} (UConstBits Ob)` in
       `SCall (UDo SubstField "immediate")
               (SCall (UDo SubstField "dst")
                      (SCall (UDo SubstField "src")
                             (UCall (UPrimFn (UConvFn (UInit (struct_t decoded_sig))))
                                    (UConstBits Ob) (UConstBits Ob))
                             {$"src"$})
                     {$"dst"$})
               {$"imm"$}`
     $}.
End ManualUnpacker.

Module PrimitiveUnpacker <: Unpacker.
  Definition unpack reg_t custom_ufn_t encoded: uaction string reg_t (interop_ufn_t custom_ufn_t) :=
    (UCall (UPrimFn (UConvFn (UUnpack (struct_t decoded_sig))))
           (UVar encoded) (UConstBits Ob)).
End PrimitiveUnpacker.

Module ManualFetcher <: Fetcher.
  Import ListNotations.

  Definition var_t := string.
  Definition custom_fn_t := interop_empty_t.
  Definition custom_Sigma := interop_empty_Sigma.
  Definition custom_uSigma := interop_empty_uSigma.
  Definition custom_fn_names := interop_empty_fn_names.

  Notation uaction reg_t := (uaction string reg_t (interop_ufn_t custom_fn_t)).

  Definition instructions {reg_t} : list (uaction reg_t) :=
    List.map UConstBits
      [Ob~1~1~0~1~1~0~0~0~0~0~1~0~1~1~0~0~0~0~0~0~0~1~1~1~1~1~0~0~1~1~0~1;
       Ob~0~1~1~0~1~0~1~1~1~0~1~0~1~0~1~0~1~0~0~1~0~1~0~0~0~1~0~1~0~1~0~1;
       Ob~1~0~0~0~0~0~1~0~1~1~1~0~0~0~1~0~1~1~1~0~0~1~1~0~0~1~1~0~0~0~1~0;
       Ob~0~1~1~1~1~0~1~0~0~0~0~0~0~0~1~0~0~1~0~0~0~0~1~0~0~0~0~0~0~1~0~0;
       Ob~1~1~1~0~1~0~0~0~0~1~1~1~1~0~1~0~0~0~0~1~0~1~1~0~0~0~0~1~0~0~1~1;
       Ob~1~0~0~0~0~0~0~1~0~0~1~1~0~0~1~1~0~0~1~0~1~0~0~0~0~1~1~1~0~1~1~0;
       Ob~0~1~0~0~1~0~0~0~0~0~1~0~0~1~1~0~1~0~0~0~0~1~1~0~0~1~1~1~0~0~1~1;
       Ob~1~1~0~0~0~0~0~1~0~1~1~1~1~1~0~0~0~1~1~0~0~0~1~0~0~1~1~1~1~0~0~1].

  Fixpoint all_branches {reg_t} sz (counter: N) actions : list (uaction reg_t * uaction reg_t) :=
    match actions with
    | nil => nil
    | action :: actions =>
      (UConstBits (Bits.of_N sz counter), action)
        :: (all_branches sz (N.add counter N.one) actions)
    end.

  Definition fetch_instr reg_t pc : uaction reg_t :=
    Eval compute in (USwitch (UVar pc) (UConstBits (Bits.zero 32))
                             (all_branches 3 N.zero instructions)).
End ManualFetcher.

Module PrimitiveFetcher <: Fetcher.
  Definition var_t := string.
  Inductive custom_fn_t' := FetchInstr.
  Definition custom_fn_t := custom_fn_t'.

  Definition custom_Sigma (fn: custom_fn_t) : ExternalSignature :=
    match fn with
    | FetchInstr => {{ bits_t 3 ~> unit_t ~> bits_t 32 }}
    end.

  Definition custom_uSigma (fn: custom_fn_t) (_ _: type) : result custom_fn_t fn_tc_error := Success fn.

  Definition custom_fn_names (fn: custom_fn_t) : string :=
    match fn with
    | FetchInstr => "fetch_instr"
    end.

  Notation uaction reg_t := (uaction string reg_t (interop_ufn_t custom_fn_t)).

  Definition fetch_instr reg_t pc : uaction reg_t :=
    Eval compute in (UCall (UCustomFn FetchInstr) (UVar pc) (UConstBits Ob)).
End PrimitiveFetcher.

Module ManualDecoder.
  Module F := ManualFetcher.
  Include (Decoder ManualUnpacker F).

  Definition rules :=
    tc_rules R Sigma uSigma
             (fun r => match r with
                    | fetch => _fetch
                    | decode => _decode
                    end).

  Definition circuit :=
    compile_scheduler interop_opt (ContextEnv.(create) (readRegisters R Sigma)) rules decoder.

  Definition package := make_package "manual_decoder" rules.
End ManualDecoder.

Module PrimitiveDecoder.
  Module F := PrimitiveFetcher.
  Include (Decoder PrimitiveUnpacker F).

  Definition rules :=
    tc_rules R (interop_Sigma F.custom_Sigma) (interop_uSigma F.custom_uSigma)
             (fun r => match r with
                    | fetch => _fetch
                    | decode => _decode
                    end).

  Definition circuit :=
    compile_scheduler interop_opt (ContextEnv.(create) (readRegisters R Sigma)) rules decoder.

  Definition package := make_package "primitive_decoder" rules.
End PrimitiveDecoder.

Module Pipeline.
  Definition var_t := string.
  Inductive reg_t := r0 | outputReg | inputReg | invalid | correct.
  Inductive custom_fn_t := Stream | F | G.
  Definition ufn_t := interop_ufn_t custom_fn_t.
  Inductive name_t := doF | doG.

  Definition sz := (pow2 5).

  Definition R r :=
    match r with
    | r0 => bits_t sz
    | inputReg => bits_t sz
    | outputReg => bits_t sz
    | invalid | correct => bits_t 1
    end.

  Definition Sigma (fn: custom_fn_t) : ExternalSignature :=
    match fn with
    | Stream => {{ bits_t sz ~> unit_t ~> bits_t sz }}
    | F => {{ bits_t sz ~> unit_t ~> bits_t sz }}
    | G => {{ bits_t sz ~> unit_t ~> bits_t sz }}
    end.

  Definition uSigma (fn: custom_fn_t) (_ _: type) : result custom_fn_t fn_tc_error := Success fn.
  Definition iSigma idx := interop_Sigma Sigma idx.
  Definition iuSigma := interop_uSigma uSigma.

  Local Notation "f [ arg ]" :=
    (UCall (UCustomFn f) arg (UConstBits Ob))
      (at level 99, arg at level 99, format "f [ arg ]").
  Local Notation "f [ arg1 ',' arg2 ]" :=
    (UCall (UCustomFn f) arg1 arg2)
      (at level 99, arg1 at level 99, arg2 at level 99,
       format "f [ arg1 ','  arg2 ]").

  Definition _doF : uaction _ _ _ :=
    {$
       let "v" := read0(inputReg) in
       write0(inputReg,`Stream[UVar "v"]`);
       let "invalid" := read1(invalid) in
       if "invalid"
       then
         write1(invalid,`UConstBits Ob~0`);
         write0(r0,`F[UVar "v"]`)
       else
         fail
           $}.

  Definition _doG : uaction _ _ _ :=
    {$
    let "invalid" := read0(invalid) in
    if !"invalid" then
      let "data" := read0(r0) in
      let "v" := read0(outputReg) in
      write0(outputReg,`Stream[{$"v"$}]`);
      write0(invalid,`UConstBits Ob~1`);
      if `G[UVar "data"]` == `G[F[UVar "v"]]`
      then
        `UConstBits Ob`
      else
        write0(correct,`UConstBits Ob~0`)
    else
      fail
        $}.


  Definition rules :=
    tc_rules R iSigma iuSigma
             (fun rl => match rl with
                     | doF => _doF
                     | doG => _doG
                     end).

  Definition Pipeline : scheduler _ :=
    tc_scheduler (doG |> doF |> done).

  Definition circuit :=
    compile_scheduler interop_opt (ContextEnv.(create) (readRegisters R iSigma)) rules Pipeline.

  Definition fn_names fn :=
    match fn with
    | Stream => "stream"
    | F => "f"
    | G => "g"
    end.

  Definition sga_package :=
    {| sga_reg_types := R;
       sga_reg_init r := match r with
                        | r0 => Bits.of_N _ 0
                        | outputReg => Bits.of_N _ 0
                        | inputReg => Bits.of_N _ 0
                        | invalid => Ob~1
                        | correct => Ob~1
                        end%N;
       sga_reg_finite := _;
       sga_reg_names r := match r with
                         | r0 => "r0"
                         | outputReg => "outputReg"
                         | inputReg => "inputReg"
                         | invalid => "invalid"
                         | correct => "correct"
                         end;

       sga_custom_fn_types := Sigma;

       sga_rules := rules;
       sga_rule_names r := match r with
                          | doF => "doF"
                          | doG => "doG"
                          end;

       sga_scheduler := Pipeline;
       sga_module_name := "pipeline"
    |}.

  Definition package :=
    {| sga := sga_package;
       sp := {| sp_pkg := sga_package;
               sp_var_names := fun x => x;
               sp_custom_fn_names := fn_names;
               sp_extfuns := Some "#include ""../extfuns.hpp""
using extfuns = pipeline_extfuns;" |};
       vp := {| vp_pkg := sga_package;
               vp_external_rules := List.nil;
               vp_custom_fn_names := fn_names |} |}.
End Pipeline.

Module RegisterFile_Ordered.
  Definition nregs := 16.
  Definition reg_sz := 32.

  (* Definition instr_sig := *)
  (*   {| struct_name := "instr"; *)
  (*      struct_fields := ("next_reg", bits_t (log2 nregs)) *)
  (*                        :: ("val", bits_t 8) *)
  (*                        :: ("immediate", bits_t 16) *)
  (*                        :: nil |}. *)

  Definition var_t := string.
  Inductive reg_t := rIndex | rData (n: Vect.index nregs) | rOutput.
  Definition ufn_t := interop_minimal_ufn_t.
  Inductive name_t := ReadReg.

  Definition R r :=
    match r with
    | rIndex => bits_t (log2 nregs)
    | rData n => bits_t reg_sz
    | rOutput => bits_t reg_sz
    end.

  Definition Sigma := interop_minimal_Sigma.
  Definition uSigma := interop_minimal_uSigma.

  Definition _ReadReg : uaction _ _ interop_minimal_ufn_t :=

    {$
    let "v" := read0(rIndex) in
    write0(rIndex,"v" + `UConstBits (Bits.of_nat (log2 nregs) 1)`);
    write0(rOutput,`UCompleteSwitch (log2 nregs) (pred nregs) "v"
                    (vect_map (fun idx => {$ read0(rData idx) $}) (all_indices nregs))`)
  $}.

  Definition rules :=
    tc_rules R iSigma iuSigma
             (fun rl => match rl with
                     | ReadReg => _ReadReg
                     end).

  Definition regfile : scheduler _ :=
    tc_scheduler (ReadReg |> done).

  Instance FiniteType_reg_t : FiniteType reg_t := _.

  Definition circuit :=
    compile_scheduler interop_opt (ContextEnv.(create) (readRegisters R Sigma)) rules regfile.

  Definition sga_package :=
    {| sga_reg_types := R;
       sga_reg_init r := match r with
                        | rIndex => Bits.zero _
                        | rData n => Bits.of_nat _ (index_to_nat n)
                        | rOutput => Bits.zero _
                        end%N;
       sga_reg_finite := _;
       sga_reg_names r := match r with
                         | rIndex => "rIndex"
                         | rData n => String.append "rData" (string_of_nat (index_to_nat n))
                         | rOutput => "rOutput"
                         end;

       sga_custom_fn_types := interop_empty_Sigma;

       sga_rules := rules;
       sga_rule_names r := match r with
                          | _ReadReg => "read_reg"
                          end;

       sga_scheduler := regfile;
       sga_module_name := "regfile_ordered"
    |}.

  Definition package :=
    {| sga := sga_package;
       sp := {| sp_pkg := sga_package;
               sp_var_names := fun x => x;
               sp_custom_fn_names := interop_empty_fn_names;
               sp_extfuns := None |};
       vp := {| vp_pkg := sga_package;
               vp_external_rules := List.nil;
               vp_custom_fn_names := interop_empty_fn_names |} |}.
End RegisterFile_Ordered.

Module Enums.
  Definition var_t := string.
  Inductive reg_t := rA | rB.
  Definition ufn_t := interop_minimal_ufn_t.
  Inductive name_t := Incr.

  Import ListNotations.
  Definition flag_sig :=
    {| enum_name := "flag";
       enum_bitsize := 3;
       enum_members := vect_of_list ["ABC"; "DEF"];
       enum_bitpatterns := vect_of_list [Ob~1~1~0; Ob~0~0~1] |}.

  Definition R r :=
    match r with
    | rA | rB => enum_t flag_sig
    end.

  Definition Sigma := interop_minimal_Sigma.
  Definition uSigma := interop_minimal_uSigma.


  Definition _Incr : uaction _ _ interop_minimal_ufn_t :=
    {$
       let "bits_a" := `UCall (UPrimFn (UConvFn UPack))
                               {$read0(rA)$} (UConstBits Ob)` in
       let "bits_b" := `UCall (UPrimFn (UConvFn UPack))
                               {$read0(rB)$} (UConstBits Ob)` in
       let "neg_a" := !"bits_a" in
       let "succ_b" := "bits_b" + `UConstBits Ob~0~0~1` in
       write0(rA,`UCall (UPrimFn (UConvFn (UUnpack (enum_t flag_sig))))
                {$"neg_a"$} (UConstBits Ob)`);
       write0(rB, `UCall (UPrimFn (UConvFn (UUnpack (enum_t flag_sig))))
                   {$"succ_b"$} (UConstBits Ob)`)
       $}.

  (* Ltac __must_typecheck R Sigma tcres ::= *)
  (*   __must_typecheck_cbn R Sigma tcres. *)

  Definition rules :=
    tc_rules R iSigma iuSigma
             (fun rl => match rl with
                     | Incr => _Incr
                     end).

  Definition enum_scheduler : scheduler _ :=
    tc_scheduler (Incr |> done).

  Instance FiniteType_reg_t : FiniteType reg_t := _.

  Definition circuit :=
    compile_scheduler interop_opt (ContextEnv.(create) (readRegisters R Sigma)) rules enum_scheduler.

  Definition sga_package :=
    {| sga_reg_types := R;
       sga_reg_init r := match r with
                        | rA => Ob~1~1~0
                        | rB => Bits.zero _
                        end%N;
       sga_reg_finite := _;
       sga_reg_names r := match r with
                         | rA => "rA"
                         | rB => "rB"
                         end;

       sga_custom_fn_types := interop_empty_Sigma;

       sga_rules := rules;
       sga_rule_names r := match r with
                          | _Incr => "incr"
                          end;

       sga_scheduler := enum_scheduler;
       sga_module_name := "enums"
    |}.

  Definition package :=
    {| sga := sga_package;
       sp := {| sp_pkg := sga_package;
               sp_var_names := fun x => x;
               sp_custom_fn_names := interop_empty_fn_names;
               sp_extfuns := None |};
       vp := {| vp_pkg := sga_package;
               vp_external_rules := List.nil;
               vp_custom_fn_names := interop_empty_fn_names |} |}.
End Enums.

Module IntCall.
  Definition ufn_t := interop_minimal_ufn_t.
  Module Delay.
    Inductive reg_t := buffer.
    Definition swap tau: UInternalFunction unit string reg_t ufn_t  :=
      function "swap" ("arg1" : tau) : tau :=
      write0(buffer, "arg1");
      read0(buffer).

    Instance FiniteType_reg_t : FiniteType reg_t := _.
  End Delay.

  Definition var_t := string.
  Inductive reg_t := rA | rDelay1 (d: Delay.reg_t) | rDelay2 (d: Delay.reg_t).
  Inductive name_t := rl.

  Definition R r :=
    match r with
    | rA => bits_t 16
    | rDelay1 buffer => bits_t 8
    | rDelay2 buffer => bits_t 16
    end.

  Definition Sigma := interop_minimal_Sigma.
  Definition uSigma := interop_minimal_uSigma.
  Notation uaction := (Syntax.uaction unit string).

  Definition nor (sz: nat) : UInternalFunction unit var_t reg_t ufn_t :=
    function ("nor<" ++ string_of_nat sz ++ ">") ("arg1" : bits_t sz, "arg2" : bits_t sz) : bits_t sz :=
  !("arg1" || "arg2").

  Notation UCallFn fn args :=
    (UInternalCall (int_sig fn) (int_body fn) args).
  Notation UCallMethod fR fSigma fn args :=
    (UInternalCall (int_sig fn) (UCallModule fR fSigma (int_body fn)) args).

  Definition display :=
    (Display.Printer (custom_fn_t := interop_empty_t) (reg_t := reg_t) (pos_t := unit)).

  Definition fSigma (fn: interop_empty_t) : ufn_t := match fn with end.
  Definition swap8 := Delay.swap (bits_t 8).
  Definition swap16 := Delay.swap (bits_t 16).

  Definition _rl : uaction string _ interop_minimal_ufn_t :=
    {$
       let "a" := read0(rA) in
       let "old_a" := call rDelay2 swap16 "a" in
       let "old_al" := call rDelay1 swap8 ("old_a"[`UConstBits Ob~0~0~0~0` :+8])  in
       write0(rA, funcall (nor 16) (read0(rA)), "old_a");
       funcall (display (Display.Str "rA: " :: Display.Value (bits_t 16) :: nil)) "a"
       $}.

  (* Ltac __must_typecheck R Sigma tcres ::= *)
  (*   __must_typecheck_cbn R Sigma tcres. *)

  Definition rules :=
    tc_rules R iSigma iuSigma
             (fun rl => match rl with
                     | rl => _rl
                     end).

  Definition sched : scheduler _ :=
    tc_scheduler (rl |> done).

  Instance FiniteType_reg_t : FiniteType reg_t := _.

  Definition circuit :=
    compile_scheduler interop_opt (ContextEnv.(create) (readRegisters R Sigma)) rules sched.

  Definition r reg : R reg :=
    match reg with
    | rA => Bits.of_N _ 12
    | rDelay1 buffer => Bits.zero _
    | rDelay2 buffer => Bits.zero _
    end.

  Definition sched_result :=
    Eval compute in interp_scheduler (ContextEnv.(create) r) interop_minimal_sigma rules sched.

  Definition sga_package :=
    {| sga_reg_types := R;
       sga_reg_init := r;
       sga_reg_finite := _;
       sga_reg_names r := match r with
                         | rA => "rA"
                         | rDelay1 buffer => "rd1_buffer"
                         | rDelay2 buffer => "rd2_buffer"
                         end;

       sga_custom_fn_types := interop_empty_Sigma;

       sga_rules := rules;
       sga_rule_names r := match r with
                          | _rl => "rl"
                          end;

       sga_scheduler := sched;
       sga_module_name := "intfn"
    |}.

  Definition package :=
    {| sga := sga_package;
       sp := {| sp_pkg := sga_package;
               sp_var_names := fun x => x;
               sp_custom_fn_names := interop_empty_fn_names;
               sp_extfuns := None |};
       vp := {| vp_pkg := sga_package;
               vp_external_rules := List.nil;
               vp_custom_fn_names := interop_empty_fn_names |} |}.
End IntCall.

Module ExternallyCompiledRule.
  Open Scope string_scope.
  Definition var_t := string.
  Definition method_name_t := string.
  Definition  custom_t:= interop_empty_t.
  Definition ufn_t := (interop_ufn_t custom_t).
  Definition pos_t := unit.

  Module Type Fifo.
    Parameter  T:type.
  End Fifo.

  Module Fifo1 (f: Fifo).
    Import f.
    Inductive reg_t := data0 |  valid0.

    Definition R r :=
      match r with
      | data0 => T
      | valid0 => bits_t 1
      end.

    Notation zero := (Bits.zeroes _).

    Definition r idx : R idx :=
      match idx with
      | data0 => value_of_bits zero
      | valid0 => zero
      end.

    Definition name_reg r :=
      match r with
      | data0 => "data0"
      | valid0 => "valid0"
      end.


    Local Notation uaction := (uaction pos_t method_name_t var_t reg_t ufn_t).

    Definition enq : @UInternalFunction pos_t method_name_t var_t reg_t ufn_t :=
      function "enq" ("data" : T) : bits_t 0 :=
        if (!read0(valid0)) then
          write0(data0,"data");
            write0(valid0,`UConstBits Ob~1`)
        else
          fail.


    Definition deq : @UInternalFunction pos_t method_name_t var_t reg_t ufn_t :=
      function "deq" : T :=
        if (read0(valid0)) then
          write0(valid0,`UConstBits Ob~0`);
            read0(data0)
        else
          fail 5.

    Instance FiniteType_reg_t : FiniteType reg_t := _.

  End Fifo1.


  Module FifoBit5 <: Fifo.
    Definition T:= bits_t 5.
  End FifoBit5.
  Module Fifo5 := Fifo1 FifoBit5.

  Inductive reg_t := MyFifo (fifof2state:Fifo5.reg_t) | Mem | Rdata .
  Inductive custom_fn_t := .
  Inductive name_t := fetch | ding.

  Definition logsz := 5.
  Notation sz := (pow2 logsz).

  Definition R r :=
    match r with
    | MyFifo f => Fifo5.R f
    | Mem => bits_t 5
    | Rdata => bits_t 5
    end.

  Notation zero := (Bits.zeroes _).

  Definition r idx : R idx :=
    match idx with
    | MyFifo f => Fifo5.r f
    | Mem => zero
    | Rdata => zero
    end.


  Notation uaction := (uaction pos_t method_name_t string reg_t ufn_t).

  Definition _fetch :=
    {$
       let "memory" := read0(Mem) in
       call MyFifo Fifo5.enq "memory"
            $}.


  Definition _ding :=
    {$
       let "dequeued" := call0 MyFifo Fifo5.deq in
       if ("dequeued" == `UConstBits Ob~0~0~0~1~0 `) then
         write0(Rdata,`UConstBits Ob~0~0~0~0~1`)
       else
         fail
           $}.

  Definition cr := ContextEnv.(create) r.
  Definition Sigma := interop_minimal_Sigma.
  Definition uSigma := interop_minimal_uSigma.

  Definition rules :=
    tc_rules R Sigma uSigma
             (fun rl => match rl with
                     | ding => _ding
                     | fetch => _fetch
                     end).

  Definition bring : scheduler _ :=
    tc_scheduler (fetch |> ding |> done).


  Definition sga_package :=
        {| sga_reg_types := R;
           sga_reg_init := r;
           sga_reg_finite := _;

           sga_custom_fn_types := interop_empty_Sigma;

           sga_reg_names r := match r with
                              | Rdata => "Rdata"
                              | Mem => "Mem"
                              | MyFifo s => String.append "MyFifo" (Fifo5.name_reg s)
                             end;

           sga_rules := rules;
           sga_rule_names r := match r with
                             | ding => "ding"
                             | fetch => "fetch"
                             end;

           sga_scheduler := bring;
           sga_module_name := "externalMemory" |}.
  Definition sim :=
        {| sp_pkg := sga_package;
           sp_var_names := fun x => x;
           sp_custom_fn_names := interop_empty_fn_names;

           sp_extfuns := None |}.
  Definition verilog :=
        {| vp_pkg := sga_package;
           vp_external_rules := cons fetch nil;
           vp_custom_fn_names := interop_empty_fn_names |} .
  Definition package := {| sga := sga_package; sp := sim; vp := verilog |}.
End ExternallyCompiledRule.

Import ListNotations.
Definition demo_packages : list demo_package_t :=
  [ Collatz.package;
    ManualDecoder.package; PrimitiveDecoder.package;
    Pipeline.package;
    RegisterFile_Ordered.package;
    Enums.package;
    IntCall.package;
    ExternallyCompiledRule.package].
