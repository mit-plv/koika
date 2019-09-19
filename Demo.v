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

  Example uactions r : uaction unit var_t reg_t fn_t :=
    match r with
    | r1 =>
      UBind "x" (URead P0 R0)
            (UIf (UCall Even (UVar "x") (UConstBits Ob))
                 (UWrite P0 R1 (UConstBits Ob~1))
                 (UWrite P0 R1 (UConstBits Ob~1)))
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
    compile_scheduler (ContextEnv.(create) (readRegisters R Sigma)) rules s1.
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

  Example _negate : uaction unit var_t reg_t ufn_t  :=
    UBind "x" (URead P1 R0)
          (UWrite P1 R0 (UVar "x")).

  Example _swap_or_replace : uaction unit var_t reg_t ufn_t  :=
    UBind "should_swap" (URead P0 R2)
          (UIf (UVar "should_swap")
               (USeq (UWrite P0 R1 (URead P0 R0))
                     (UWrite P0 R0 (URead P0 R1)))
               (UWrite P0 R0 (UCall UOr
                                    (URead P0 R0)
                                    (URead P0 R1)))).

  Example _ill_typed_write : uaction unit var_t reg_t ufn_t  :=
    UWrite P0 R2 (URead P0 R1).

  Example _unbound_variable : uaction unit var_t reg_t ufn_t  :=
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
    compile_scheduler (ContextEnv.(create) (readRegisters R Sigma)) rules tsched.
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

  Definition logsz := 5.
  Notation sz := (pow2 logsz).

  Definition R r :=
    match r with
    | R0 => bits_t sz
    end.

  Definition r idx : R idx :=
    match idx with
    | R0 => Ob~0~1~0~1~0~1~1~1~1~0~0~0~1~1~0~0~0~0~1~0~1~0~1~1~1~1~0~0~0~1~1~0
    end.

  (* TODO bug report *)
  (* Notation "!!!!" := ltac:(exact (true, false, tt)). *)
  (* Compute match (true, true, tt) with *)
  (*         | !!!! => 1 *)
  (*         end. *)

  Open Scope sga.

  Definition _divide : uaction unit var_t reg_t ufn_t :=
    Let "v" <- R0#read0 in
    Let "odd" <- USel[[$"v", UConstBits (Bits.zero logsz)]] in
    If UNot[[$"odd"]] Then
       R0#write0(ULsr[[$"v", UConstBits Ob~1]])
    Else
       fail
    EndIf.

  Definition TimesThree (ex: uaction unit var_t reg_t ufn_t) :=
    UUIntPlus[[ULsl[[ex, UConstBits Ob~1]], ex]]%sga_expr.

  Definition _multiply : uaction unit var_t reg_t ufn_t :=
    Let "v" <- R0#read1 in
    Let "odd" <- USel[[$"v", UConstBits (Bits.zero logsz)]] in
    If $"odd" Then
       R0#write1(UUIntPlus[[TimesThree ($"v"),
                            UConstBits (Bits.one sz)]])
    Else
       fail
    EndIf.

(* Bug report *)
(* Require Import Coq.extraction.Extraction. *)
(* (* Extraction Language JSON. *) *)
(* Set Extraction KeepSingleton. *)
(* Extraction Collatz.reg_t. *)

  Definition cr := ContextEnv.(create) r.

  Definition collatz : scheduler _ :=
    tc_scheduler (divide |> multiply |> done).

  (* Ltac __must_typecheck R Sigma tcres ::= *)
  (*   __must_typecheck_cbn R Sigma tcres. *)

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
    compile_scheduler (ContextEnv.(create) (readRegisters R interop_minimal_Sigma)) rules collatz.

  Definition sga_package :=
    {| sga_reg_types := R;
       sga_reg_init := r;
       sga_reg_finite := _;

       sga_custom_fn_types := interop_empty_Sigma;

       sga_reg_names r := match r with
                         | R0 => "r0"
                         end;

       sga_rules := rules;

       sga_scheduler := collatz;
       sga_module_name := "collatz" |}.

  Definition package :=
    {| sga := sga_package;
       sp := {| sp_pkg := sga_package;
               sp_var_names x := x;
               sp_custom_fn_names := interop_empty_fn_names;
               sp_rule_names r := match r with
                                 | divide => "divide"
                                 | multiply => "multiply"
                                 end;
               sp_extfuns := None |};
       vp := {| vp_pkg := sga_package;
               vp_custom_fn_names := interop_empty_fn_names |} |}.
End Collatz.

Require Import Coq.Lists.List.

Module Type Unpacker.
  Axiom unpack : forall reg_t custom_ufn_t (source: string), uaction unit string reg_t (interop_ufn_t custom_ufn_t).
End Unpacker.

Module Type Fetcher.
  Axiom custom_fn_t : Type.
  Axiom custom_Sigma : custom_fn_t -> ExternalSignature.
  Axiom custom_uSigma : custom_fn_t -> type -> type -> result custom_fn_t fn_tc_error.
  Axiom custom_fn_names : custom_fn_t -> string.
  Axiom fetch_instr : forall reg_t (pc: string), uaction unit string reg_t (interop_ufn_t custom_fn_t).
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

  Open Scope sga.

  Notation uaction := (uaction unit var_t reg_t ufn_t).

  Definition _fetch : uaction :=
    Let "pc" <- Rpc#read0 in
    Let "encoded" <- F.fetch_instr _ "pc" in
    ((Rencoded#write0($"encoded"));;
     (Rpc#write0(UUIntPlus[[$"pc", UConstBits Ob~0~0~1]]))).

  Definition _decode : uaction :=
    Let "encoded" <- Rencoded#read1 in
    (Rdecoded#write0 (P.unpack _ _ "encoded")).

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

           sga_scheduler := decoder;
           sga_module_name := modname |} in
    let sim :=
        {| sp_pkg := sga_package;
           sp_var_names := fun x => x;
           sp_custom_fn_names := F.custom_fn_names;
           sp_rule_names r := match r with
                             | decode => "decode"
                             | fetch => "fetch"
                             end;

           sp_extfuns := Some "#include ""../extfuns.hpp""
using extfuns = decoder_extfuns;" |} in
    let verilog :=
        {| vp_pkg := sga_package;
           vp_custom_fn_names := F.custom_fn_names |} in
    {| sga := sga_package; sp := sim; vp := verilog |}.
End Decoder.

Module ManualUnpacker <: Unpacker.
  Notation SCall fn a1 a2 :=
    (UCall (UPrimFn (UStructFn decoded_sig fn)) a1 a2).

  Definition unpack reg_t custom_ufn_t encoded: uaction unit string reg_t (interop_ufn_t custom_ufn_t) :=
    (Let "imm" <- SCall (UDoBits GetField "immediate") ($encoded) (UConstBits Ob) in
     Let "src" <- SCall (UDoBits GetField "src") ($encoded) (UConstBits Ob) in
     Let "dst" <- SCall (UDoBits GetField "dst") ($encoded) (UConstBits Ob) in
     (* Let "imm" <- (UPart 0 16)[[$encoded, UConstBits Ob]] in *)
     (* Let "dst" <- (UPart 16 8)[[$encoded, UConstBits Ob]] in *)
     (* Let "src" <- (UPart 24 8)[[$encoded, UConstBits Ob]] in *)
     (SCall (UDo SubstField "immediate")
            (SCall (UDo SubstField "dst")
                   (SCall (UDo SubstField "src")
                          (UCall (UPrimFn (UConvFn (struct_t decoded_sig) Init))
                                 (UConstBits Ob) (UConstBits Ob))
                          ($"src"))
                   ($"dst"))
            ($"imm"))%sga_expr)%sga.
End ManualUnpacker.

Module PrimitiveUnpacker <: Unpacker.
  Definition unpack reg_t custom_ufn_t encoded: uaction unit string reg_t (interop_ufn_t custom_ufn_t) :=
    (UCall (UPrimFn (UConvFn (struct_t decoded_sig) Unpack))
           (UVar encoded) (UConstBits Ob)).
End PrimitiveUnpacker.

Section Switch.
  Context {pos_t var_t reg_t custom_fn_t: Type}.

  Notation uaction := (uaction pos_t var_t reg_t (interop_ufn_t custom_fn_t)).

  Definition if_eq a1 a2 (tbranch fbranch: uaction) :=
    UIf (UCall (UPrimFn (UBitsFn UEq)) a1 a2)
        tbranch
        fbranch.

  Fixpoint USwitch {sz}
           (var: var_t)
           (default: uaction)
           (branches: list (bits_t sz * uaction))
    : uaction :=
    match branches with
    | nil => default
    | (val, action) :: branches =>
      if_eq (UVar var) (UConstBits val)
            action (USwitch var default branches)
    end.

  Fixpoint gen_switch {sz}
           (var: var_t)
           {nb} (branches: vect (bits_t sz * uaction) (S nb)) : uaction :=
    let '(label, branch) := vect_hd branches in
    match nb return vect _ (S nb) -> uaction with
    | 0 => fun _ => branch
    | S nb => fun branches => if_eq (UVar var) (UConstBits label)
                                branch (gen_switch var (vect_tl branches))
    end branches.

  Definition UCompleteSwitch
             sz bound
             (var: var_t)
             (branches: vect uaction (S bound)) :=
    gen_switch var (vect_map2 (fun n a => (Bits.of_nat sz (index_to_nat n), a))
                              (all_indices (S bound)) branches).
End Switch.

Module ManualFetcher <: Fetcher.
  Import ListNotations.

  Definition var_t := string.
  Definition custom_fn_t := interop_empty_t.
  Definition custom_Sigma := interop_empty_Sigma.
  Definition custom_uSigma := interop_empty_uSigma.
  Definition custom_fn_names := interop_empty_fn_names.

  Notation uaction reg_t := (uaction unit string reg_t (interop_ufn_t custom_fn_t)).

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

  Fixpoint all_branches {reg_t} sz (counter: N) (actions: list (uaction reg_t)) :=
    match actions with
    | nil => nil
    | action :: actions =>
      (Bits.of_N sz counter, action)
        :: (all_branches sz (N.add counter N.one) actions)
    end.

  Definition fetch_instr reg_t pc : uaction reg_t :=
    Eval compute in (USwitch pc (UConstBits (Bits.zero 32)) (all_branches 3 N.zero instructions)).
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

  Notation uaction reg_t := (uaction unit string reg_t (interop_ufn_t custom_fn_t)).

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
    compile_scheduler (ContextEnv.(create) (readRegisters R Sigma)) rules decoder.

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
    compile_scheduler (ContextEnv.(create) (readRegisters R Sigma)) rules decoder.

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

  Open Scope sga.

  Definition _doF : uaction unit _ _ _ :=
    Let "v" <- inputReg#read0 in
    ((inputReg#write0(Stream[$"v"]));;
     Let "invalid" <- invalid#read1 in
     If $"invalid" Then
       invalid#write1(UConstBits Ob~0);;
       (r0#write0(F[$"v"]))
     Else
       fail
     EndIf).

  Definition _doG : uaction unit _ _ _ :=
    Let "invalid" <- invalid#read0 in
    If UNot[[$"invalid"]] Then
      Let "data" <- r0#read0 in
      Let "v" <- outputReg#read0 in
      ((outputReg#write0(Stream[$"v"]));;
       (invalid#write0(UConstBits Ob~1));;
       If UEq[[G[$"data"], G[F[$"v"] ] ]] Then
           skip
       Else
           correct#write0(UConstBits Ob~0)
       EndIf)
    Else
        fail
    EndIf.

  Definition rules :=
    tc_rules R iSigma iuSigma
             (fun rl => match rl with
                     | doF => _doF
                     | doG => _doG
                     end).

  Definition Pipeline : scheduler _ :=
    tc_scheduler (doG |> doF |> done).

  Definition circuit :=
    compile_scheduler (ContextEnv.(create) (readRegisters R iSigma)) rules Pipeline.

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

       sga_scheduler := Pipeline;
       sga_module_name := "pipeline"
    |}.

  Definition package :=
    {| sga := sga_package;
       sp := {| sp_pkg := sga_package;
               sp_var_names := fun x => x;
               sp_custom_fn_names := fn_names;
               sp_rule_names r := match r with
                                 | doF => "doF"
                                 | doG => "doG"
                                 end;
               sp_extfuns := Some "#include ""../extfuns.hpp""
using extfuns = pipeline_extfuns;" |};
       vp := {| vp_pkg := sga_package;
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

  Open Scope sga.

  Definition _ReadReg : uaction unit _ _ interop_minimal_ufn_t :=
    Let "v" <- rIndex#read0 in
    ((rIndex#write0(UUIntPlus[[$"v", UConstBits (Bits.of_nat (log2 nregs) 1)]]));;
     (rOutput#write0(UCompleteSwitch (log2 nregs) (pred nregs) "v"
                                     (vect_map (fun idx => (rData idx)#read0) (all_indices nregs))))).

  Definition rules :=
    tc_rules R iSigma iuSigma
             (fun rl => match rl with
                     | ReadReg => _ReadReg
                     end).

  Definition regfile : scheduler _ :=
    tc_scheduler (ReadReg |> done).

  Instance FiniteType_reg_t : FiniteType reg_t := _.

  Definition circuit :=
    compile_scheduler (ContextEnv.(create) (readRegisters R Sigma)) rules regfile.

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

       sga_scheduler := regfile;
       sga_module_name := "regfile_ordered"
    |}.

  Definition package :=
    {| sga := sga_package;
       sp := {| sp_pkg := sga_package;
               sp_var_names := fun x => x;
               sp_custom_fn_names := interop_empty_fn_names;
               sp_rule_names r := match r with
                                 | _ReadReg => "read_reg"
                                 end;
               sp_extfuns := None |};
       vp := {| vp_pkg := sga_package;
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

  Open Scope sga.

  Definition _Incr : uaction unit _ _ interop_minimal_ufn_t :=
    Let "bits_a" <- (UCall (UPrimFn (UConvFn (enum_t flag_sig) Pack))
                          (rA#read0) (UConstBits Ob)) in
    Let "bits_b" <- (UCall (UPrimFn (UConvFn (enum_t flag_sig) Pack))
                          (rB#read0) (UConstBits Ob)) in
    Let "neg_a" <- UNot[[$"bits_a", UConstBits Ob]] in
    Let "succ_b" <- UUIntPlus[[$"bits_b", UConstBits Ob~0~0~1]] in
    ((rA#write0(UCall (UPrimFn (UConvFn (enum_t flag_sig) Unpack))
                      ($"neg_a") (UConstBits Ob)));;
     (rB#write0(UCall (UPrimFn (UConvFn (enum_t flag_sig) Unpack))
                      ($"succ_b") (UConstBits Ob)))).

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
    compile_scheduler (ContextEnv.(create) (readRegisters R Sigma)) rules enum_scheduler.

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

       sga_scheduler := enum_scheduler;
       sga_module_name := "enums"
    |}.

  Definition package :=
    {| sga := sga_package;
       sp := {| sp_pkg := sga_package;
               sp_var_names := fun x => x;
               sp_custom_fn_names := interop_empty_fn_names;
               sp_rule_names r := match r with
                                 | _Incr => "incr"
                                 end;
               sp_extfuns := None |};
       vp := {| vp_pkg := sga_package;
               vp_custom_fn_names := interop_empty_fn_names |} |}.
End Enums.

Import ListNotations.
Definition demo_packages :=
  [ Collatz.package;
    ManualDecoder.package; PrimitiveDecoder.package;
    Pipeline.package;
    RegisterFile_Ordered.package;
    Enums.package ].
