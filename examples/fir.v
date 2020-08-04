(*! Computing a FIR (Coq version) !*)
Require Import Koika.Frontend.

Section KArray.
  Definition array_init T n {reg_t ext_fn_t} : UInternalFunction reg_t ext_fn_t :=
    {{ fun array_init (X: T ) :  array_t {| array_type:= T; array_len:= n|}  =>
      `USugar( UArrayInit T (repeat {{X}} n) )`
    }}.

Definition static_access  {reg_t ext_fn_t}  array idx: uaction reg_t ext_fn_t :=
  (UUnop (UArray1 (UGetElement idx)) array).

Definition static_update {reg_t ext_fn_t} array idx v: uaction reg_t ext_fn_t :=
                      (UBinop (UArray2 (USubstElement idx)) array v).

Definition static_slice {reg_t ext_fn_t} (T: type) (init: uaction reg_t ext_fn_t) sz  array idx: uaction reg_t ext_fn_t :=
  let ainit := @array_init T sz reg_t ext_fn_t in
  {{
  let returned := ainit(`init`) in
  `List.fold_left (fun acc el =>
  static_update acc el ( UUnop (UArray1 (UGetElement (idx+el))) array)) (seq 0 sz) {{returned}}`
  }}.

Definition access n T {reg_t} : UInternalFunction reg_t empty_ext_fn_t :=
  let sz := log2 n in
   {{ fun access (array : array_t {| array_type:= T; array_len:= n|}  ) (idx: bits_t sz ) : T =>
   ` (USugar (USwitch {{idx}}
           (USugar (UConstBits (sz:= sz) Bits.zero))
            (List.map (fun branch =>
                   ((USugar (UConstBits (Bits.of_nat (sz<:nat) branch))),
                      (UUnop (UArray1 (UGetElement branch)) ) {{array}}))
                       (seq 0 n)))) ` }}.

Definition update n T {reg_t} : UInternalFunction reg_t empty_ext_fn_t :=
  let sz := log2 n in
   {{ fun update (array : array_t {| array_type:= T; array_len:= n|}  ) (idx: bits_t sz ) (v: T) : array_t {| array_type:= T; array_len:= n|}  =>
   ` (USugar (USwitch {{idx}}
           (USugar (UConstBits (sz:= sz) Bits.zero))
            (List.map (fun branch =>
                   ((USugar (UConstBits (Bits.of_nat (sz<:nat) branch))),
                      (UBinop (UArray2 (USubstElement branch)) ) {{array}} {{v}}))
                       (seq 0 n)))) ` }}.
End KArray.

Inductive ext_fn_t :=
  mod19
.


Section Fir.
        Definition T := 4.
        Definition  NI := 8.
  Definition  NO := 2*NI.
  Inductive reg_t := q | x.

  Definition Sigma (fn: ext_fn_t) :=
    match fn with
    | foo => {$ bits_t NI ~> bits_t NI $}
    end.

  Definition inner_prod (i: nat): UInternalFunction reg_t ext_fn_t :=
    {{ fun inner_prod (X: bits_t NI) (W: array_t {| array_type:= bits_t NI ; array_len:= T|}) : bits_t NO =>
    `static_access {{W}} i` *  X
    }}.

  Definition inner_sum (i: nat): UInternalFunction reg_t ext_fn_t :=
    {{ fun inner_sum (q: array_t {| array_type:= bits_t NO ; array_len:= T|})  (mul_out: array_t {| array_type:= bits_t NO ; array_len:= T|}) : bits_t NO =>
    `static_access {{q}} i` +  `static_access {{mul_out}} (T-i-1)`
    }}.

  Definition feed : UInternalFunction reg_t ext_fn_t :=
    let access := access (reg_t:= reg_t) T (bits_t NI) in
    let ainitI := array_init (ext_fn_t:= ext_fn_t) (reg_t:= reg_t) (bits_t NI) T in
    let ainitO := array_init (ext_fn_t:= ext_fn_t) (reg_t:= reg_t) (bits_t NO) T in
    {{ fun feed (X: bits_t NI) (W: array_t {| array_type:= bits_t NI ; array_len:= T|}) :
    bits_t NO
    =>
      let qv := read0(q) in
      let mul_out :=  ainitO(#(Bits.of_nat NO 0)) in
        (* for (genvar i = 0; i < T; i++)
                        assign mul_out[i] = W[i] * X;  *)
      (set mul_out :=
         `List.fold_left (fun acc el =>
        let inner_prod := inner_prod el in
        static_update acc el ({{inner_prod(X,W)}})) (seq 0 T) {{mul_out}}`);
      (* for (genvar i = 0; i < T; i++)
      assign add_out[i] = q[i] + mul_out[T-i-1]; *)
      let add_out :=  ainitO(#(Bits.of_nat NO 0)) in
      (set add_out := `List.fold_left (fun acc el =>
        let inner_sum := inner_sum el in
        static_update acc el ({{inner_sum(qv, mul_out)}})) (seq 0 T) {{add_out}}`);
      (*
        assign q[0] = '0;
        for (genvar i = 1; i < T; i++)
                always_ff @(posedge CLK) q[i] <= add_out[i-1];
      *)
      let new_q :=  ainitO(#(Bits.of_nat NO 0)) in
      (set new_q := `List.fold_left (fun acc el =>
        static_update acc el (static_access {{add_out}} (el-1))) (seq 1 (T-1)) {{new_q}}`);
      write0(q,new_q);
        (* assign Y = add_out[T-1]; *)
      `static_access {{add_out}} (T-1)`
    }}.

  Inductive rule_name_t := tb .

  Definition R r :=
  match r with
  | q => array_t {| array_type:= bits_t NO ; array_len:= T|}
  | x =>  bits_t NI
  end.

  Definition r idx : R idx :=
  match idx with
  | q =>  value_of_bits (Bits.zero)
  | x =>  Bits.zero
  end.

  Definition testbench_fir : scheduler :=
    tb |> done.

  Definition cr := ContextEnv.(create) r.

  Definition _tb : uaction reg_t ext_fn_t :=
  {{
    let X := read0(x) in
    let W := `USugar
        (UArrayInit
          (bits_t NI)
          (List.map
            (fun el => USugar (UConstBits el))
            [Ob~1~1~1~1~1~1~1~0;
            Ob~1~1~1~1~1~1~1~1;
            Ob~0~0~0~0~0~0~1~1;
            Ob~0~0~0~0~0~1~0~0]))` in
    let bla := feed(X, W) in
    write0(x, X + |8`d9|)
  }}.
  (* Typechecking  *)
  Definition rules :=
    tc_rules R Sigma
             (fun r => match r with
                    | tb => _tb
                    end).

  Definition external (r: rule_name_t) := false.

Definition ext_fn_names (fn: ext_fn_t) :=
  match fn with
  | mod19 => "mod19"
  end.


Definition ext_fn_specs fn :=
  match fn with
  | mod19 => {| ef_name := "mod19";
                            ef_internal := true |}
  end.

  Definition package :=
    {| ip_koika := {| koika_reg_types := R;
                     koika_reg_init := r;
                     koika_ext_fn_types := Sigma;
                     koika_rules := rules;
                     koika_rule_external := external;
                     koika_scheduler := testbench_fir;
                     koika_module_name := "fir" |};
     ip_sim :=
       {| sp_ext_fn_names := ext_fn_names;
          sp_extfuns := Some "#include ""extfuns.hpp""" |};

     ip_verilog := {| vp_ext_fn_specs := ext_fn_specs |} |}.
 }
End Fir.

Definition prog := Interop.Backends.register package.
Extraction "fir.ml" prog.
