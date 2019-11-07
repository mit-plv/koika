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

Definition demo_packages : list interop_package_t :=
  [ ManualDecoder.package; PrimitiveDecoder.package].
