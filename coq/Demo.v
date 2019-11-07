Require Import Koika.Frontend.

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

  Definition r idx : R idx :=
    match idx with
    | Rpc => Bits.zero
    | Rencoded => Bits.zero
    | Rdecoded => (Bits.zero, (Bits.zero, (Bits.zero, tt)))
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

  Notation rulemap_t :=
    (rule_name_t -> rule R F.Sigma).

  Definition make_package (modname: string) (rules: rulemap_t) :=
    let koika_package :=
        {| koika_reg_types := R;
           koika_reg_init := r;
           koika_reg_finite := _;

           koika_ext_fn_types := F.Sigma;

           koika_reg_names := show;

           koika_rules := rules;
           koika_rule_names := show;

           koika_scheduler := decoder;
           koika_module_name := modname |} in
    let sim :=
        {| sp_var_names x := x;
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
                         (UUnop (UConv (UUnpack (struct_t decoded_sig))) (USugar (UConstBits (Bits.zeroes 32))))
                         {{ src }})
                 {{ dst }})
         {{ imm }}`
     }}.

End ManualUnpacker.

Module PrimitiveUnpacker <: Unpacker.
  Definition unpack reg_t ext_fn_t encoded: uaction reg_t ext_fn_t :=
    (UUnop (UConv (UUnpack (struct_t decoded_sig))) (UVar encoded)).
End PrimitiveUnpacker.

Require Import Coq.Lists.List.
Module ManualFetcher <: Fetcher.
  Import ListNotations.

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
      (USugar (USwitch (UVar pc) (USugar (UConstBits (Bits.zeroes 32)))
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
       koika_reg_names := show;

       koika_ext_fn_types := Sigma;

       koika_rules := rules;
       koika_rule_names := show;

       koika_scheduler := Pipeline;
       koika_module_name := "pipeline"
    |}.

  Definition package :=
    {| ip_koika := koika_package;
       ip_sim := {| sp_var_names x := x;
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
    | rIndex => Bits.zero
    | rData n => Bits.of_nat _ (index_to_nat n)
    | rOutput => Bits.zero
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
       koika_reg_names := show;

       koika_ext_fn_types := empty_Sigma;

       koika_rules := rules;
       koika_rule_names := show;

       koika_scheduler := regfile;
       koika_module_name := "regfile_ordered"
    |}.

  Definition package :=
    {| ip_koika := koika_package;
       ip_sim := {| sp_var_names x := x;
                    sp_ext_fn_names := empty_fn_names;
                    sp_extfuns := None |};
       ip_verilog := {| vp_external_rules := List.nil;
                       vp_ext_fn_names := empty_fn_names |} |}.
End RegisterFile_Ordered.

Module Enums.
  Inductive reg_t := rA | rB.
  Definition ext_fn_t := empty_ext_fn_t.
  Inductive rule_name_t := Incr.

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

  Definition r reg : R reg :=
    match reg with
    | rA => Ob~1~1~0
    | rB => Bits.zero
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
       koika_reg_names := show;

       koika_ext_fn_types := empty_Sigma;

       koika_rules := rules;
       koika_rule_names := show;

       koika_scheduler := enum_scheduler;
       koika_module_name := "enums"
    |}.

  Definition package :=
    {| ip_koika := koika_package;
       ip_sim := {| sp_var_names x := x;
                    sp_ext_fn_names := empty_fn_names;
                    sp_extfuns := None |};
       ip_verilog := {| vp_external_rules := List.nil;
                        vp_ext_fn_names := empty_fn_names |} |}.
End Enums.

Definition demo_packages : list interop_package_t :=
  [ ManualDecoder.package; PrimitiveDecoder.package;
    Pipeline.package;
    RegisterFile_Ordered.package;
    Enums.package].
