Require Import Koika.Frontend.

Module Ex1.
  Notation var_t := string.
  Inductive reg_t := R0 | R1.
  Inductive ext_fn_t := Even | Odd.
  Inductive rule_name_t := r1.

  Definition R reg : type :=
    match reg with
    | R0 => bits_t 3
    | R1 => bits_t 1
    end.

  Definition Sigma fn : ExternalSignature :=
    match fn with
    | Even => {$ bits_t 3 ~> bits_t 1 $}
    | Odd => {$ bits_t 3 ~> bits_t 1 $}
    end.

  Definition r idx : R idx :=
    match idx with
    | R0 => Ob~1~0~1
    | R1 => Ob~0
    end.

  Definition sigma idx : Sig_denote (Sigma idx) :=
    match idx with
    | Even => fun (bs: bits 3) => Ob~(negb (Bits.lsb bs))
    | Odd => fun (bs: bits 3) => Ob~(Bits.lsb bs)
    end.

  Example uactions r : uaction reg_t ext_fn_t :=
    match r with
    | r1 =>
      {{ let x := read0(R0) in
         if (`UExternalCall Even (UVar "x")`)
         then write0(R1,`USugar (UConstBits Ob~1)`)
         else write0(R1,`USugar (UConstBits Ob~1)`)
                       }}
    end.

  Definition rules :=
    tc_rules R Sigma uactions.

  Example us1 : uscheduler :=
    UTry r1 UDone UDone.

  Definition s1 :=
    tc_scheduler us1.

  Definition s1_result :=
    Eval compute in interp_scheduler (ContextEnv.(create) r) sigma rules s1.

  Definition s1_circuits :=
    compile_scheduler rules s1.

  Definition s1_circuits_result :=
    Eval compute in interp_circuits (ContextEnv.(create) r) sigma s1_circuits.
End Ex1.
Module Ex2.
  Inductive reg_t := R0 | R1 | R2.
  Definition ext_fn_t := empty_ext_fn_t.
  Inductive rule_name_t := negate | swap_or_replace.

  Definition R r :=
    match r with
    | R0 => bits_t 7
    | R1 => bits_t 7
    | R2 => bits_t 1
    end.

  Example _negate : uaction reg_t ext_fn_t  :=
    {{
       let x := read1(R0) in
       write1(R0,x)
    }}.

  Example _swap_or_replace : uaction reg_t ext_fn_t  :=
    {{
      let should_swap := read0(R2) in
      if should_swap
      then
        write0(R1,read0(R0));
        write0(R0,read0(R1))
      else
        write0(R0, read0(R0) || read0(R1))
    }}.

  Example _ill_typed_write : uaction reg_t ext_fn_t  :=
    UWrite P0 R2 (URead P0 R1).

  Example _unbound_variable : uaction reg_t ext_fn_t  :=
    UWrite P0 R0 (UVar "y").

  Example tsched : scheduler :=
    tc_scheduler (UTry swap_or_replace (UTry negate UDone UDone) (UTry negate UDone UDone)).

  Fail Example trule : rule pos_t var_t R Sigma :=
    tc_rule R Sigma _ill_typed_write.

  Fail Example trule : rule pos_t var_t R Sigma :=
    tc_rule R Sigma _unbound_variable.

  Definition r idx : R idx :=
    match idx with
    | R0 => Ob~0~1~1~0~0~1~0
    | R1 => Ob~1~1~0~0~1~1~0
    | R2 => Ob~1
    end.

  Definition rules : rule_name_t -> rule R empty_Sigma :=
    tc_rules R empty_Sigma
             (fun r => match r with
                    | negate => _negate
                    | swap_or_replace => _swap_or_replace
                    end).

  Definition tsched_result :=
    Eval compute in interp_scheduler (ContextEnv.(create) r) empty_sigma rules tsched.
  Definition tsched_circuits :=
    compile_scheduler rules tsched.
  Definition tsched_circuits_result :=
    Eval compute in interp_circuits (ContextEnv.(create) r) empty_sigma tsched_circuits.
End Ex2.

Module Collatz.
  Inductive reg_t := R0.
  Definition ext_fn_t := empty_ext_fn_t.
  Inductive rule_name_t := divide | multiply.

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

  Notation zero := (Bits.zero logsz).
  Notation one := (Bits.zero logsz).

  Definition times_three : UInternalFunction reg_t ext_fn_t :=
    {{
        fun (arg1 : bits_t 16) : bits_t 16 =>
          (arg1 << Ob~1)  + arg1
    }}.

  Definition _divide : uaction reg_t ext_fn_t :=
  {{
    let v := read0(R0) in
    let odd := v[Ob~0~0~0~0] in
    if !odd then
      write0(R0,v >> Ob~1)
    else
      fail
  }}.

  Definition _multiply : uaction reg_t ext_fn_t :=
  {{
    let v := read1(R0) in
    let odd := v[Ob~0~0~0~0] in
    if odd then
      write1(R0, (funcall times_three (v)) + Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1)
    else
      fail
  }}.

  Definition collatz : scheduler :=
    tc_scheduler (divide |> multiply |> done).

  Definition cr := ContextEnv.(create) r.

  (* Typechecking  *)
  Definition rules :=
    tc_rules R empty_Sigma
             (fun r => match r with
                    | divide => _divide
                    | multiply => _multiply
                    end).

  Definition result :=
    compute (interp_scheduler cr empty_sigma rules collatz).

  Definition divide_result :=
    compute (interp_action cr empty_sigma CtxEmpty log_empty log_empty
                           (rules divide)).

  Definition multiply_result :=
    compute (interp_action cr empty_sigma CtxEmpty log_empty log_empty
                           (rules multiply)).

  Definition circuits :=
    compile_scheduler rules collatz.

  Definition circuits_result :=
    Eval compute in interp_circuits (ContextEnv.(create) r) empty_sigma circuits.
  Definition koika_package :=
    {| koika_reg_types := R;
       koika_reg_init := r;
       koika_reg_finite := _;

       koika_ext_fn_types := empty_Sigma;

       koika_reg_names r := match r with
                         | R0 => "r0"
                         end;

       koika_rules := rules;
       koika_rule_names r := match r with
                         | divide => "divide"
                         | multiply => "multiply"
                         end;

       koika_scheduler := collatz;
       koika_module_name := "collatz" |}.

  Definition package :=
    {| ip_koika := koika_package;
       ip_sim := {| sp_var_names x := x;
                   sp_ext_fn_names := empty_fn_names;
                   sp_extfuns := None |};
       ip_verilog := {| vp_external_rules := List.nil;
                       vp_ext_fn_names := empty_fn_names |} |}.
End Collatz.

Module Type Unpacker.
  Axiom unpack : forall reg_t ext_fn_t (source: string), uaction reg_t ext_fn_t.
End Unpacker.

Module Type Fetcher.
  Axiom ext_fn_t : Type.
  Axiom Sigma : ext_fn_t -> ExternalSignature.
  Axiom ext_fn_names : ext_fn_t -> string.
  Axiom fetch_instr : forall reg_t (pc: string), uaction reg_t ext_fn_t.
End Fetcher.

Definition decoded_sig :=
  {| struct_name := "instr";
     struct_fields := ("src", bits_t 8)
                       :: ("dst", bits_t 8)
                       :: ("immediate", bits_t 16)
                       :: nil |}.

Module Decoder (P: Unpacker) (F: Fetcher).
  Inductive reg_t := Rpc | Rencoded | Rdecoded.
  Definition ext_fn_t := F.ext_fn_t.
  Inductive rule_name_t := fetch | decode.

  Definition Sigma := F.Sigma.

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

  Definition _fetch : uaction reg_t ext_fn_t :=
    {{
    let pc := read0(Rpc) in
    let encoded := `F.fetch_instr _ "pc"` in
    write0(Rencoded, encoded);
    write0(Rpc, pc + Ob~0~0~1)
    }}
  .

  Definition _decode : uaction reg_t ext_fn_t :=
    {{
    let encoded := read1(Rencoded) in
    write0(Rdecoded,`P.unpack _ _ "encoded"`)
    }}.

  Definition cr := ContextEnv.(create) r.

  Definition decoder : scheduler :=
    tc_scheduler (fetch |> decode |> done).

  (* Ltac __must_typecheck R Sigma tcres ::= *)
  (*   __must_typecheck_cbn R Sigma tcres. *)

  Notation rulemap_t :=
    (rule_name_t -> rule R F.Sigma).

  Definition make_package (modname: string) (rules: rulemap_t) :=
    let koika_package :=
        {| koika_reg_types := R;
           koika_reg_init := r;
           koika_reg_finite := _;

           koika_ext_fn_types := F.Sigma;

           koika_reg_names r := match r with
                             | Rpc => "Rpc"
                             | Rencoded => "Rencoded"
                             | Rdecoded => "Rdecoded"
                             end;

           koika_rules := rules;
           koika_rule_names r := match r with
                             | decode => "decode"
                             | fetch => "fetch"
                             end;

           koika_scheduler := decoder;
           koika_module_name := modname |} in
    let sim :=
        {| sp_var_names := fun x => x;
           sp_ext_fn_names := F.ext_fn_names;

           sp_extfuns := Some "#include ""../demo.extfuns.hpp""
using extfuns = decoder_extfuns;" |} in
    let verilog :=
        {| vp_external_rules := List.nil;
           vp_ext_fn_names := F.ext_fn_names |} in
    {| ip_koika := koika_package; ip_sim := sim; ip_verilog := verilog |}.
End Decoder.

Module ManualUnpacker <: Unpacker.
  Notation SCall1 fn a1 := (UUnop (UStruct1 fn) a1).
  Notation SCall2 fn a1 a2 := (UBinop (UStruct2 fn) a1 a2).

  Definition unpack reg_t ext_fn_t encoded: uaction reg_t ext_fn_t :=
    {{
        let imm := `SCall1 (UGetFieldBits decoded_sig "immediate") (UVar encoded)` in
        let src := `SCall1 (UGetFieldBits decoded_sig "src") (UVar encoded)` in
        let dst := `SCall1 (UGetFieldBits decoded_sig "dst") (UVar encoded)` in
        `SCall2 (USubstField "immediate")
         (SCall2 (USubstField "dst")
                 (SCall2 (USubstField "src")
                         (UUnop (UConv (UUnpack (struct_t decoded_sig))) (USugar (UConstBits (Bits.zero 32))))
                         {{ src }})
                 {{ dst }})
         {{ imm }}`
     }}.

End ManualUnpacker.

Module PrimitiveUnpacker <: Unpacker.
  Definition unpack reg_t ext_fn_t encoded: uaction reg_t ext_fn_t :=
    (UUnop (UConv (UUnpack (struct_t decoded_sig))) (UVar encoded)).
End PrimitiveUnpacker.

Module ManualFetcher <: Fetcher.
  Definition ext_fn_t := empty_ext_fn_t.
  Definition Sigma := empty_Sigma.
  Definition ext_fn_names := empty_fn_names.

  Notation uaction reg_t := (uaction reg_t ext_fn_t).

  Definition instructions {reg_t} : list (uaction reg_t) :=
    List.map USugar
      (List.map UConstBits
        [Ob~1~1~0~1~1~0~0~0~0~0~1~0~1~1~0~0~0~0~0~0~0~1~1~1~1~1~0~0~1~1~0~1;
         Ob~0~1~1~0~1~0~1~1~1~0~1~0~1~0~1~0~1~0~0~1~0~1~0~0~0~1~0~1~0~1~0~1;
         Ob~1~0~0~0~0~0~1~0~1~1~1~0~0~0~1~0~1~1~1~0~0~1~1~0~0~1~1~0~0~0~1~0;
         Ob~0~1~1~1~1~0~1~0~0~0~0~0~0~0~1~0~0~1~0~0~0~0~1~0~0~0~0~0~0~1~0~0;
         Ob~1~1~1~0~1~0~0~0~0~1~1~1~1~0~1~0~0~0~0~1~0~1~1~0~0~0~0~1~0~0~1~1;
         Ob~1~0~0~0~0~0~0~1~0~0~1~1~0~0~1~1~0~0~1~0~1~0~0~0~0~1~1~1~0~1~1~0;
         Ob~0~1~0~0~1~0~0~0~0~0~1~0~0~1~1~0~1~0~0~0~0~1~1~0~0~1~1~1~0~0~1~1;
         Ob~1~1~0~0~0~0~0~1~0~1~1~1~1~1~0~0~0~1~1~0~0~0~1~0~0~1~1~1~1~0~0~1]).

  Fixpoint all_branches {reg_t} sz (counter: N) actions : list (uaction reg_t * uaction reg_t) :=
    match actions with
    | nil => nil
    | action :: actions =>
      (USugar (UConstBits (Bits.of_N sz counter)), action)
        :: (all_branches sz (N.add counter N.one) actions)
    end.

  Definition fetch_instr reg_t pc : uaction reg_t :=
    Eval compute in
      (USugar (USwitch (UVar pc) (USugar (UConstBits (Bits.zero 32)))
                       (all_branches 3 N.zero instructions))).
End ManualFetcher.

Module PrimitiveFetcher <: Fetcher.
  Inductive ext_fn_t' := FetchInstr.
  Definition ext_fn_t := ext_fn_t'.

  Definition Sigma (fn: ext_fn_t) : ExternalSignature :=
    match fn with
    | FetchInstr => {$ bits_t 3 ~> bits_t 32 $}
    end.

  Definition ext_fn_names (fn: ext_fn_t) : string :=
    match fn with
    | FetchInstr => "fetch_instr"
    end.

  Notation uaction reg_t := (uaction reg_t ext_fn_t).

  Definition fetch_instr reg_t pc : uaction reg_t :=
    Eval compute in (UExternalCall FetchInstr (UVar pc)).
End PrimitiveFetcher.

Module ManualDecoder.
  Module F := ManualFetcher.
  Include (Decoder ManualUnpacker F).

  Definition rules :=
    tc_rules R Sigma
             (fun r => match r with
                    | fetch => _fetch
                    | decode => _decode
                    end).

  Definition circuits :=
    compile_scheduler rules decoder.

  Definition circuits_result sigma :=
    interp_circuits (ContextEnv.(create) r) sigma circuits.

  Definition package := make_package "manual_decoder" rules.
End ManualDecoder.

Module PrimitiveDecoder.
  Module F := PrimitiveFetcher.
  Include (Decoder PrimitiveUnpacker F).

  Definition rules :=
    tc_rules R F.Sigma
             (fun r => match r with
                    | fetch => _fetch
                    | decode => _decode
                    end).

  Definition circuits :=
    compile_scheduler rules decoder.

  Definition circuits_result sigma :=
    interp_circuits (ContextEnv.(create) r) sigma circuits.

  Definition package := make_package "primitive_decoder" rules.
End PrimitiveDecoder.

Module Pipeline.
  Inductive reg_t := r0 | outputReg | inputReg | invalid | correct.
  Inductive ext_fn_t := Stream | F | G.
  Inductive rule_name_t := doF | doG.

  Definition sz := (pow2 5).

  Definition R r :=
    match r with
    | r0 => bits_t sz
    | inputReg => bits_t sz
    | outputReg => bits_t sz
    | invalid | correct => bits_t 1
    end.

  Definition r reg : R reg :=
    match reg with
    | r0 => Bits.of_N _ 0
    | outputReg => Bits.of_N _ 0
    | inputReg => Bits.of_N _ 0
    | invalid => Ob~1
    | correct => Ob~1
    end.

  Definition Sigma (fn: ext_fn_t) : ExternalSignature :=
    match fn with
    | Stream => {$ bits_t sz ~> bits_t sz $}
    | F => {$ bits_t sz ~> bits_t sz $}
    | G => {$ bits_t sz ~> bits_t sz $}
    end.

  Local Notation "f [[ arg ]]" :=
    (UExternalCall f arg)
      (at level 99, arg at level 99, format "f [[ arg ]]").

  Definition _doF : uaction _ _ :=
    {{
       let v := read0(inputReg) in
       write0(inputReg,`Stream[[UVar "v"]]`);
       let invalid := read1(invalid) in
       if invalid
       then
         write1(invalid, Ob~0);
         write0(r0,`F[[UVar "v"]]`)
       else
         fail
    }}.

  Definition _doG : uaction _ _ :=
    {{
    let invalid := read0(invalid) in
    if !invalid then
      let data := read0(r0) in
      let v := read0(outputReg) in
      write0(outputReg,`Stream[[{{v}}]]`);
      write0(invalid, Ob~1);
      if `G[[UVar "data"]]` == `G[[F[[UVar "v"]]]]`
      then
        `USugar (UConstBits Ob)`
      else
        write0(correct, Ob~0)
    else
      fail
    }}.

  Definition rules :=
    tc_rules R Sigma
             (fun rl => match rl with
                     | doF => _doF
                     | doG => _doG
                     end).

  Definition Pipeline : scheduler :=
    tc_scheduler (doG |> doF |> done).

  Definition circuits :=
    compile_scheduler rules Pipeline.

  Definition circuits_result sigma :=
    interp_circuits (ContextEnv.(create) r) sigma circuits.

  Definition fn_names fn :=
    match fn with
    | Stream => "stream"
    | F => "f"
    | G => "g"
    end.

  Definition koika_package :=
    {| koika_reg_types := R;
       koika_reg_init reg := r reg;
       koika_reg_finite := _;
       koika_reg_names reg := match reg with
                           | r0 => "r0"
                           | outputReg => "outputReg"
                           | inputReg => "inputReg"
                           | invalid => "invalid"
                           | correct => "correct"
                           end;

       koika_ext_fn_types := Sigma;

       koika_rules := rules;
       koika_rule_names r := match r with
                          | doF => "doF"
                          | doG => "doG"
                          end;

       koika_scheduler := Pipeline;
       koika_module_name := "pipeline"
    |}.

  Definition package :=
    {| ip_koika := koika_package;
       ip_sim := {| sp_var_names := fun x => x;
                    sp_ext_fn_names := fn_names;
                    sp_extfuns := Some "#include ""../demo.extfuns.hpp""
using extfuns = pipeline_extfuns;" |}       ;
       ip_verilog := {| vp_external_rules := List.nil;
                        vp_ext_fn_names := fn_names |} |}.
End Pipeline.

Section CircuitTools.
  Context {rule_name_t reg_t ext_fn_t: Type}.
  Context {CR: reg_t -> nat}.
  Context {CSigma: ext_fn_t -> CExternalSignature}.
  Context {rwdata: nat -> Type}.

  Fixpoint circuit_size {sz: nat}
           (c: circuit (rwdata := rwdata) (rule_name_t := rule_name_t) CR CSigma sz): N :=
    1 + match c with
        | CNot c => circuit_size c
        | CAnd c1 c2 => circuit_size c1 + circuit_size c2
        | COr c1 c2 => circuit_size c1 + circuit_size c2
        | CMux select c1 c2 => circuit_size select + circuit_size c1 + circuit_size c2
        | CConst _ => 0
        | CReadRegister _ => 0
        | CUnop _ a1 => circuit_size a1
        | CBinop _ a1 a2 => circuit_size a1 + circuit_size a2
        | CExternal _ a => circuit_size a
        | CBundleRef _ _ _ _ c => circuit_size c
        | CAnnot _ c => circuit_size c
        end.
End CircuitTools.

Module RegisterFile_Ordered.
  Definition nregs := 2.
  Definition reg_sz := 32.

  (* Definition instr_sig := *)
  (*   {| struct_name := "instr"; *)
  (*      struct_fields := ("next_reg", bits_t (log2 nregs)) *)
  (*                        :: ("val", bits_t 8) *)
  (*                        :: ("immediate", bits_t 16) *)
  (*                        :: nil |}. *)

  Inductive reg_t := rIndex | rData (n: Vect.index nregs) | rOutput.
  Definition ext_fn_t := empty_ext_fn_t.
  Inductive rule_name_t := ReadReg.

  Definition R r :=
    match r with
    | rIndex => bits_t (log2 nregs)
    | rData n => bits_t reg_sz
    | rOutput => bits_t reg_sz
    end.

  Definition r reg : R reg :=
    match reg with
    | rIndex => Bits.zero _
    | rData n => Bits.of_nat _ (index_to_nat n)
    | rOutput => Bits.zero _
    end.


  Definition _ReadReg : uaction _ empty_ext_fn_t :=
    {{
    let v := read0(rIndex) in
    write0(rIndex,v + `USugar (UConstBits (Bits.of_nat (log2 nregs) 1))`);
    write0(rOutput,`UCompleteSwitch (log2 nregs) (pred nregs) "v"
                    (vect_map (fun idx => {{ read0(rData idx) }}) (all_indices nregs))`)
    }}.

  Definition rules :=
    tc_rules R empty_Sigma
             (fun rl => match rl with
                     | ReadReg => _ReadReg
                     end).

  Definition regfile : scheduler :=
    tc_scheduler (ReadReg |> done).

  Instance FiniteType_reg_t : FiniteType reg_t := _.

  Definition circuits :=
    compile_scheduler rules regfile.

  (* Definition circuits_result := *)
  (*   Eval native_compute in interp_circuits (ContextEnv.(create) r) empty_sigma circuits. *)

  Definition koika_package :=
    {| koika_reg_types := R;
       koika_reg_init reg := r reg;
       koika_reg_finite := _;
       koika_reg_names reg := match reg with
                           | rIndex => "rIndex"
                           | rData n => String.append "rData" (string_of_nat (index_to_nat n))
                           | rOutput => "rOutput"
                           end;

       koika_ext_fn_types := empty_Sigma;

       koika_rules := rules;
       koika_rule_names r := match r with
                          | _ReadReg => "read_reg"
                          end;

       koika_scheduler := regfile;
       koika_module_name := "regfile_ordered"
    |}.

  Definition package :=
    {| ip_koika := koika_package;
       ip_sim := {| sp_var_names := fun x => x;
                    sp_ext_fn_names := empty_fn_names;
                    sp_extfuns := None |};
       ip_verilog := {| vp_external_rules := List.nil;
                        vp_ext_fn_names := empty_fn_names |} |}.
End RegisterFile_Ordered.

Module Enums.
  Inductive reg_t := rA | rB.
  Definition ext_fn_t := empty_ext_fn_t.
  Inductive rule_name_t := Incr.

  Definition flag_sig :=
    {| enum_name := "flag";
       enum_bitsize := 3;
       enum_members := vect_of_list ["ABC"; "DEF"];
       enum_bitpatterns := vect_of_list [Ob~1~1~0; Ob~0~0~1] |}.

  Definition R r :=
    match r with
    | rA | rB => enum_t flag_sig
    end.

  Definition r reg : R reg :=
    match reg with
    | rA => Ob~1~1~0
    | rB => Bits.zero _
    end.

  Definition _Incr : uaction _ empty_ext_fn_t :=
    {{
       let bits_a := `UUnop (UConv UPack) {{read0(rA)}}` in
       let bits_b := `UUnop (UConv UPack) {{read0(rB)}}` in
       let neg_a := !bits_a in
       let succ_b := bits_b + `USugar (UConstBits Ob~0~0~1)` in
       write0(rA,`UUnop (UConv (UUnpack (enum_t flag_sig))) {{neg_a}}`);
       write0(rB, `UUnop (UConv (UUnpack (enum_t flag_sig))) {{succ_b}}`)
    }}.

  (* Ltac __must_typecheck R Sigma tcres ::= *)
  (*   __must_typecheck_cbn R Sigma tcres. *)

  Definition rules :=
    tc_rules R empty_Sigma
             (fun rl => match rl with
                     | Incr => _Incr
                     end).

  Definition enum_scheduler : scheduler :=
    tc_scheduler (Incr |> done).

  Instance FiniteType_reg_t : FiniteType reg_t := _.

  Definition circuits :=
    compile_scheduler rules enum_scheduler.

  Definition circuits_result :=
    Eval compute in interp_circuits (ContextEnv.(create) r) empty_sigma circuits.

  Definition koika_package :=
    {| koika_reg_types := R;
       koika_reg_init := r;
       koika_reg_finite := _;
       koika_reg_names r := match r with
                         | rA => "rA"
                         | rB => "rB"
                         end;

       koika_ext_fn_types := empty_Sigma;

       koika_rules := rules;
       koika_rule_names r := match r with
                          | _Incr => "incr"
                          end;

       koika_scheduler := enum_scheduler;
       koika_module_name := "enums"
    |}.

  Definition package :=
    {| ip_koika := koika_package;
       ip_sim := {| sp_var_names := fun x => x;
                    sp_ext_fn_names := empty_fn_names;
                    sp_extfuns := None |};
       ip_verilog := {| vp_external_rules := List.nil;
                        vp_ext_fn_names := empty_fn_names |} |}.
End Enums.

Module IntCall.
  Definition ext_fn_t := empty_ext_fn_t.

  Module Delay.
    Inductive reg_t := buffer.

    Definition swap tau: UInternalFunction reg_t ext_fn_t  :=
      {{
          fun (arg1 : tau) : tau =>
            write0(buffer, arg1);
            read0(buffer)
      }}.

    Instance FiniteType_reg_t : FiniteType reg_t := _.
  End Delay.

  Inductive reg_t := rA | rDelay1 (d: Delay.reg_t) | rDelay2 (d: Delay.reg_t).
  Inductive rule_name_t := rl.

  Definition R r :=
    match r with
    | rA => bits_t 16
    | rDelay1 buffer => bits_t 8
    | rDelay2 buffer => bits_t 16
    end.

  Definition r reg : R reg :=
    match reg with
    | rA => Bits.of_N _ 12
    | rDelay1 buffer => Bits.zero _
    | rDelay2 buffer => Bits.zero _
    end.

  Definition nor (sz: nat) : UInternalFunction reg_t ext_fn_t :=
    {{
        fun  (arg1 : bits_t sz) (arg2 : bits_t sz) : bits_t sz =>
          !(arg1 || arg2)
    }}.

  Definition display :=
    (Display.Printer (ext_fn_t := empty_ext_fn_t) (reg_t := reg_t) (pos_t := pos_t)).

  Definition swap8 := Delay.swap (bits_t 8).
  Definition swap16 := Delay.swap (bits_t 16).

  Definition _rl : uaction reg_t empty_ext_fn_t :=
    {{
       let a := read0(rA) in
       let old_a := call rDelay2 swap16 (a) in
       let old_al := call rDelay1 swap8 (old_a[Ob~0~0~0~0 :+8])  in
       write0(rA, funcall (nor 16) ((read0(rA)), old_a));
       funcall (display (Display.Str "rA: " :: Display.Value (bits_t 16) :: nil)) (a)
    }}.

  (* Ltac __must_typecheck R Sigma tcres ::= *)
  (*   __must_typecheck_cbn R Sigma tcres. *)

  Definition rules :=
    tc_rules R empty_Sigma
             (fun rl => match rl with
                     | rl => _rl
                     end).

  Definition sched : scheduler :=
    tc_scheduler (rl |> done).

  Instance FiniteType_reg_t : FiniteType reg_t := _.

  Definition circuits :=
    compile_scheduler rules sched.

  Definition circuits_result :=
    Eval compute in interp_circuits (ContextEnv.(create) r) empty_sigma circuits.

  Definition sched_result :=
    Eval compute in interp_scheduler (ContextEnv.(create) r) empty_sigma rules sched.

  Definition koika_package :=
    {| koika_reg_types := R;
       koika_reg_init := r;
       koika_reg_finite := _;
       koika_reg_names r := match r with
                         | rA => "rA"
                         | rDelay1 buffer => "rd1_buffer"
                         | rDelay2 buffer => "rd2_buffer"
                         end;

       koika_ext_fn_types := empty_Sigma;

       koika_rules := rules;
       koika_rule_names r := match r with
                          | _rl => "rl"
                          end;

       koika_scheduler := sched;
       koika_module_name := "intfn"
    |}.

  Definition package :=
    {| ip_koika := koika_package;
       ip_sim := {| sp_var_names := fun x => x;
                    sp_ext_fn_names := empty_fn_names;
                    sp_extfuns := None |};
       ip_verilog := {| vp_external_rules := List.nil;
                        vp_ext_fn_names := empty_fn_names |} |}.
End IntCall.

Require Import Koika.Std.

Module ExternallyCompiledRule.

  Module FifoBit5 <: Fifo.
    Definition T:= bits_t 5.
  End FifoBit5.

  Module Fifo5 := Fifo1 FifoBit5.

  Inductive reg_t := MyFifo (fifof2state:Fifo5.reg_t) | Mem | Rdata .
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


  Definition _fetch :=
    {{
       let memory := read0(Mem) in
       call MyFifo Fifo5.enq (memory)
    }}.


  Definition _ding : uaction reg_t empty_ext_fn_t :=
    {{
       let dequeued := call0 MyFifo Fifo5.deq in
       if (dequeued == Ob~0~0~0~1~0) then
         write0(Rdata, Ob~0~0~0~0~1)
       else
         fail
    }}.

  Definition cr := ContextEnv.(create) r.

  Definition rules :=
    tc_rules R empty_Sigma
             (fun rl => match rl with
                     | ding => _ding
                     | fetch => _fetch
                     end).

  Definition bring : scheduler :=
    tc_scheduler (fetch |> ding |> done).

  Definition koika_package :=
        {| koika_reg_types := R;
           koika_reg_init := r;
           koika_reg_finite := _;

           koika_ext_fn_types := empty_Sigma;

           koika_reg_names r := match r with
                              | Rdata => "Rdata"
                              | Mem => "Mem"
                              | MyFifo s => String.append "MyFifo" (Fifo5.name_reg s)
                             end;

           koika_rules := rules;
           koika_rule_names r := match r with
                             | ding => "ding"
                             | fetch => "fetch"
                             end;

           koika_scheduler := bring;
           koika_module_name := "externalMemory" |}.
  Definition sim :=
    {| sp_var_names := fun x => x;
       sp_ext_fn_names := empty_fn_names;
       sp_extfuns := None |}.
  Definition verilog :=
    {| vp_external_rules := cons fetch nil;
       vp_ext_fn_names := empty_fn_names |} .
  Definition package : interop_package_t := {| ip_koika := koika_package; ip_sim := sim; ip_verilog := verilog |}.
End ExternallyCompiledRule.

Notation zero := (Bits.zeroes _).

Module GcdMachine.
  Definition ext_fn_t := empty_ext_fn_t.

  Inductive reg_t := input_data |  input_valid | gcd_busy | gcd_a | gcd_b | output_data.

  Instance FiniteType_reg_t : FiniteType reg_t := _.

  Definition pair_sig :=
  {| struct_name := "pair";
     struct_fields := ("a", bits_t 16)
                        :: ("b", bits_t 16)
                        :: nil |}.

  Definition R r :=
    match r with
    | input_data => struct_t pair_sig
    | input_valid => bits_t 1
    | gcd_busy => bits_t 1
    | gcd_a => bits_t 16
    | gcd_b => bits_t 16
    | output_data => bits_t 16
    end.

  Definition init_r idx : R idx :=
    match idx with
    | input_data => (zero, (zero, tt))
    | input_valid => zero
    | gcd_busy => zero
    | gcd_a => zero
    | gcd_b => zero
    | output_data => zero
    end.

Definition gcd_start : uaction reg_t ext_fn_t  :=
    {{
       if (read0(input_valid) == #(Ob~1)
            && !read0(gcd_busy)) then
         let data := read0(input_data) in
         write0(gcd_a, get(data, a));
         write0(gcd_b, get(data, b));
         write0(gcd_busy, Ob~1);
         write0(input_valid, Ob~0)
       else
         fail
           }}.

  Definition sub  : UInternalFunction reg_t ext_fn_t :=
    {{
        fun (arg1 : bits_t 16) (arg2 : bits_t 16) : bits_t 16 =>
          (arg1 + !arg2 + `USugar (UConstBits (Bits.of_nat 16 1))`)
    }} .

  Definition lt16 : UInternalFunction reg_t ext_fn_t :=
    {{
        fun (arg1 : bits_t 16) (arg2 : bits_t 16) : bits_t 1 =>
          (funcall sub (arg1, arg2))[`USugar (UConstBits (Bits.of_nat 4 15))`]
    }}.

  Fixpoint lt (sz: nat) : UInternalFunction reg_t ext_fn_t :=
    match sz with
    | O => {{ fun (arg1 : bits_t 0) (arg2 : bits_t 0) : bits_t 0 => Ob~1}}
    | S sz => {{ fun (arg1 : bits_t sz) (arg2 : bits_t sz) : bits_t sz =>
      let subLt := funcall (lt sz) (arg1[#(Bits.of_nat sz 0) :+ sz], arg2[#(Bits.of_nat sz 0) :+ sz]) in
      arg1[#(Bits.of_nat sz sz)] || arg2[#(Bits.of_nat sz sz)]}}
    end.

  Definition gcd_compute  : uaction reg_t ext_fn_t :=
    {{
       let a := read0(gcd_a) in
       let b := read0(gcd_b) in
       if !(a == #(Bits.of_nat 16 0)) then
         if (funcall lt16 (a, b)) then
           write0(gcd_b, a);
           write0(gcd_a, b)
         else
           write0(gcd_a, funcall sub (a,b))
       else
         fail
    }}.

    Definition gcd_getresult : uaction reg_t ext_fn_t :=
      {{
       if ((read1(gcd_a) == #(Bits.of_nat 16 0))
          && read1(gcd_busy)) then
         write0(gcd_busy, Ob~0);
         write0(output_data, read1(gcd_b))
       else
         fail
      }}.

  Inductive name_t := start | step_compute | get_result.

  Definition cr := ContextEnv.(create) init_r.

  Definition rules :=
    tc_rules R empty_Sigma
             (fun rl => match rl with
                     | start => gcd_start
                     | step_compute => gcd_compute
                     | get_result => gcd_getresult end).

  Definition bring : scheduler :=
    tc_scheduler (start |> step_compute |> get_result |> done).

  Definition koika_package :=
        {| koika_reg_types := R;
           koika_reg_init := init_r;
           koika_reg_finite := _;

           koika_ext_fn_types := empty_Sigma;

           koika_reg_names r := match r with
                              | input_data =>
                                "input_data"
                              | input_valid =>
                                "input_valid"
                              | gcd_busy =>
                                "gcd_busy"
                              | gcd_a =>
                                "gcd_a"
                              | gcd_b =>
                                "gcd_b"
                              | output_data =>
                                "output_data"
                             end;

           koika_rules := rules;
           koika_rule_names r := match r with
                               | start => "start"
                               | step_compute => "step"
                               | get_result => "gcd_getresult" end;


           koika_scheduler := bring;
           koika_module_name := "externalMemory" |}.

  Definition package :=
    {| ip_koika := koika_package;
       ip_sim := {| sp_var_names := fun x => x;
                   sp_ext_fn_names := empty_fn_names;
                   sp_extfuns := None |};
       ip_verilog := {| vp_external_rules := nil;
                       vp_ext_fn_names := empty_fn_names |} |}.
End GcdMachine.

Definition demo_packages : list interop_package_t :=
  [ Collatz.package;
    ManualDecoder.package; PrimitiveDecoder.package;
    Pipeline.package;
    RegisterFile_Ordered.package;
    Enums.package;
    IntCall.package;
    ExternallyCompiledRule.package].
