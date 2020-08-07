(*! Computing an FFT !*)
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


Section FFT.
  Definition complex :=
  {| struct_name := "complex";
     struct_fields :=
       [  ("re", bits_t 32); ("im", bits_t 32)  ] |}.

  Definition log_points := 4.
  Definition points := pow2 log_points.
  Inductive reg_t := localSt.

  Notation ext_fn_t := empty_ext_fn_t.
  (* Inductive ext_fn_t := *)
  (*   foo *)
  (* . *)

  (* Definition Sigma (fn: ext_fn_t) := *)
  (*   match fn with *)
  (*   | foo => {$ bits_t 1 ~> bits_t 1 $} *)
  (*   end. *)
  Notation Sigma := empty_Sigma.


  Definition ctimes : UInternalFunction reg_t ext_fn_t :=
    {{ fun ctimes (a: struct_t complex) (b: struct_t complex) : struct_t complex =>
    let re := (get(a, re) * get(b,re))[#(Bits.of_nat 6 16) :+ 32] - (get(b,im) * get(a,im))[#(Bits.of_nat 6 16) :+ 32] in
    let im := (get(a,re) * get(b,im))[#(Bits.of_nat 6 16) :+ 32] + (get(a,im) * get(b,re))[#(Bits.of_nat 6 16) :+ 32] in
    struct complex { re := re; im:= im }
    }}.

  Definition cplus : UInternalFunction reg_t ext_fn_t :=
    {{ fun ctimes (a: struct_t complex) (b: struct_t complex) : struct_t complex =>
    let re := get(a, re) + get(b,re) in
    let im := get(b,im) + get(a,im)in
    struct complex { re := re; im:= im }
    }}.

  Definition csub : UInternalFunction reg_t ext_fn_t :=
    {{ fun ctimes (a: struct_t complex) (b: struct_t complex) : struct_t complex =>
    let re := get(a, re) - get(b,re) in
    let im := get(a,im) - get(b,im)in
    struct complex { re := re; im:= im }
    }}.

  Definition bfly2 : UInternalFunction reg_t ext_fn_t :=
    let ainit := array_init (reg_t:= reg_t) (struct_t complex) 2 in
    {{ fun bfly2
        (t: array_t {| array_type := struct_t complex ; array_len:= 2|})
        (k:  struct_t complex) :
        array_t {| array_type := struct_t complex ; array_len:= 2|} =>
    let m := ctimes(`static_access {{t}} 1`, k) in
    let zero := #(Bits.of_nat 32 0) in
    let zerocomplex := struct complex {re:= zero; im := zero} in
    let result := ainit(zerocomplex) in
      (set result := `static_update {{result}} 0 {{cplus(`static_access {{t}} 0`,m)}}`);
      `static_update {{result}} 1 {{csub(`static_access {{t}} 0`, m)}}`
    }}.

  Definition permute (dst:nat) (points:nat) : nat :=
    if Nat.ltb dst (points/2) then
      dst*2
    else
      (dst - points/2)*2 + 1.

  Definition twiddle (stage:nat) (idx:nat) : uaction reg_t ext_fn_t  := match stage, idx with
|           0,           0 => {{let r := #(Bits.of_N 32      65536) in let i := #(Bits.of_N 32          0) in struct complex {re:=r;im:=i} }}
|           0,           1 => {{let r := #(Bits.of_N 32      65536) in let i := #(Bits.of_N 32          0) in struct complex {re:=r;im:=i} }}
|           0,           2 => {{let r := #(Bits.of_N 32      65536) in let i := #(Bits.of_N 32          0) in struct complex {re:=r;im:=i} }}
|           0,           3 => {{let r := #(Bits.of_N 32      65536) in let i := #(Bits.of_N 32          0) in struct complex {re:=r;im:=i} }}
|           0,           4 => {{let r := #(Bits.of_N 32      65536) in let i := #(Bits.of_N 32          0) in struct complex {re:=r;im:=i} }}
|           0,           5 => {{let r := #(Bits.of_N 32      65536) in let i := #(Bits.of_N 32          0) in struct complex {re:=r;im:=i} }}
|           0,           6 => {{let r := #(Bits.of_N 32      65536) in let i := #(Bits.of_N 32          0) in struct complex {re:=r;im:=i} }}
|           0,           7 => {{let r := #(Bits.of_N 32      65536) in let i := #(Bits.of_N 32          0) in struct complex {re:=r;im:=i} }}
|           0,           8 => {{let r := #(Bits.of_N 32 4294901760) in let i := #(Bits.of_N 32          0) in struct complex {re:=r;im:=i} }}
|           0,           9 => {{let r := #(Bits.of_N 32 4294901760) in let i := #(Bits.of_N 32          0) in struct complex {re:=r;im:=i} }}
|           0,          10 => {{let r := #(Bits.of_N 32 4294901760) in let i := #(Bits.of_N 32          0) in struct complex {re:=r;im:=i} }}
|           0,          11 => {{let r := #(Bits.of_N 32 4294901760) in let i := #(Bits.of_N 32          0) in struct complex {re:=r;im:=i} }}
|           0,          12 => {{let r := #(Bits.of_N 32 4294901760) in let i := #(Bits.of_N 32          0) in struct complex {re:=r;im:=i} }}
|           0,          13 => {{let r := #(Bits.of_N 32 4294901760) in let i := #(Bits.of_N 32          0) in struct complex {re:=r;im:=i} }}
|           0,          14 => {{let r := #(Bits.of_N 32 4294901760) in let i := #(Bits.of_N 32          0) in struct complex {re:=r;im:=i} }}
|           0,          15 => {{let r := #(Bits.of_N 32 4294901760) in let i := #(Bits.of_N 32          0) in struct complex {re:=r;im:=i} }}
|           1,           0 => {{let r := #(Bits.of_N 32      65536) in let i := #(Bits.of_N 32          0) in struct complex {re:=r;im:=i} }}
|           1,           1 => {{let r := #(Bits.of_N 32      65536) in let i := #(Bits.of_N 32          0) in struct complex {re:=r;im:=i} }}
|           1,           2 => {{let r := #(Bits.of_N 32      65536) in let i := #(Bits.of_N 32          0) in struct complex {re:=r;im:=i} }}
|           1,           3 => {{let r := #(Bits.of_N 32      65536) in let i := #(Bits.of_N 32          0) in struct complex {re:=r;im:=i} }}
|           1,           4 => {{let r := #(Bits.of_N 32          0) in let i := #(Bits.of_N 32 4294901760) in struct complex {re:=r;im:=i} }}
|           1,           5 => {{let r := #(Bits.of_N 32          0) in let i := #(Bits.of_N 32 4294901760) in struct complex {re:=r;im:=i} }}
|           1,           6 => {{let r := #(Bits.of_N 32          0) in let i := #(Bits.of_N 32 4294901760) in struct complex {re:=r;im:=i} }}
|           1,           7 => {{let r := #(Bits.of_N 32          0) in let i := #(Bits.of_N 32 4294901760) in struct complex {re:=r;im:=i} }}
|           1,           8 => {{let r := #(Bits.of_N 32 4294901760) in let i := #(Bits.of_N 32          0) in struct complex {re:=r;im:=i} }}
|           1,           9 => {{let r := #(Bits.of_N 32 4294901760) in let i := #(Bits.of_N 32          0) in struct complex {re:=r;im:=i} }}
|           1,          10 => {{let r := #(Bits.of_N 32 4294901760) in let i := #(Bits.of_N 32          0) in struct complex {re:=r;im:=i} }}
|           1,          11 => {{let r := #(Bits.of_N 32 4294901760) in let i := #(Bits.of_N 32          0) in struct complex {re:=r;im:=i} }}
|           1,          12 => {{let r := #(Bits.of_N 32          0) in let i := #(Bits.of_N 32      65536) in struct complex {re:=r;im:=i} }}
|           1,          13 => {{let r := #(Bits.of_N 32          0) in let i := #(Bits.of_N 32      65536) in struct complex {re:=r;im:=i} }}
|           1,          14 => {{let r := #(Bits.of_N 32          0) in let i := #(Bits.of_N 32      65536) in struct complex {re:=r;im:=i} }}
|           1,          15 => {{let r := #(Bits.of_N 32          0) in let i := #(Bits.of_N 32      65536) in struct complex {re:=r;im:=i} }}
|           2,           0 => {{let r := #(Bits.of_N 32      65536) in let i := #(Bits.of_N 32          0) in struct complex {re:=r;im:=i} }}
|           2,           1 => {{let r := #(Bits.of_N 32      65536) in let i := #(Bits.of_N 32          0) in struct complex {re:=r;im:=i} }}
|           2,           2 => {{let r := #(Bits.of_N 32      46340) in let i := #(Bits.of_N 32 4294920955) in struct complex {re:=r;im:=i} }}
|           2,           3 => {{let r := #(Bits.of_N 32      46340) in let i := #(Bits.of_N 32 4294920955) in struct complex {re:=r;im:=i} }}
|           2,           4 => {{let r := #(Bits.of_N 32          0) in let i := #(Bits.of_N 32 4294901760) in struct complex {re:=r;im:=i} }}
|           2,           5 => {{let r := #(Bits.of_N 32          0) in let i := #(Bits.of_N 32 4294901760) in struct complex {re:=r;im:=i} }}
|           2,           6 => {{let r := #(Bits.of_N 32 4294920955) in let i := #(Bits.of_N 32 4294920955) in struct complex {re:=r;im:=i} }}
|           2,           7 => {{let r := #(Bits.of_N 32 4294920955) in let i := #(Bits.of_N 32 4294920955) in struct complex {re:=r;im:=i} }}
|           2,           8 => {{let r := #(Bits.of_N 32 4294901760) in let i := #(Bits.of_N 32          0) in struct complex {re:=r;im:=i} }}
|           2,           9 => {{let r := #(Bits.of_N 32 4294901760) in let i := #(Bits.of_N 32          0) in struct complex {re:=r;im:=i} }}
|           2,          10 => {{let r := #(Bits.of_N 32 4294920955) in let i := #(Bits.of_N 32      46340) in struct complex {re:=r;im:=i} }}
|           2,          11 => {{let r := #(Bits.of_N 32 4294920955) in let i := #(Bits.of_N 32      46340) in struct complex {re:=r;im:=i} }}
|           2,          12 => {{let r := #(Bits.of_N 32          0) in let i := #(Bits.of_N 32      65536) in struct complex {re:=r;im:=i} }}
|           2,          13 => {{let r := #(Bits.of_N 32          0) in let i := #(Bits.of_N 32      65536) in struct complex {re:=r;im:=i} }}
|           2,          14 => {{let r := #(Bits.of_N 32      46340) in let i := #(Bits.of_N 32      46340) in struct complex {re:=r;im:=i} }}
|           2,          15 => {{let r := #(Bits.of_N 32      46340) in let i := #(Bits.of_N 32      46340) in struct complex {re:=r;im:=i} }}
|           3,           0 => {{let r := #(Bits.of_N 32      65536) in let i := #(Bits.of_N 32          0) in struct complex {re:=r;im:=i} }}
|           3,           1 => {{let r := #(Bits.of_N 32      60547) in let i := #(Bits.of_N 32 4294942216) in struct complex {re:=r;im:=i} }}
|           3,           2 => {{let r := #(Bits.of_N 32      46340) in let i := #(Bits.of_N 32 4294920955) in struct complex {re:=r;im:=i} }}
|           3,           3 => {{let r := #(Bits.of_N 32      25079) in let i := #(Bits.of_N 32 4294906749) in struct complex {re:=r;im:=i} }}
|           3,           4 => {{let r := #(Bits.of_N 32          0) in let i := #(Bits.of_N 32 4294901760) in struct complex {re:=r;im:=i} }}
|           3,           5 => {{let r := #(Bits.of_N 32 4294942216) in let i := #(Bits.of_N 32 4294906749) in struct complex {re:=r;im:=i} }}
|           3,           6 => {{let r := #(Bits.of_N 32 4294920955) in let i := #(Bits.of_N 32 4294920955) in struct complex {re:=r;im:=i} }}
|           3,           7 => {{let r := #(Bits.of_N 32 4294906749) in let i := #(Bits.of_N 32 4294942216) in struct complex {re:=r;im:=i} }}
|           3,           8 => {{let r := #(Bits.of_N 32 4294901760) in let i := #(Bits.of_N 32          0) in struct complex {re:=r;im:=i} }}
|           3,           9 => {{let r := #(Bits.of_N 32 4294906749) in let i := #(Bits.of_N 32      25079) in struct complex {re:=r;im:=i} }}
|           3,          10 => {{let r := #(Bits.of_N 32 4294920955) in let i := #(Bits.of_N 32      46340) in struct complex {re:=r;im:=i} }}
|           3,          11 => {{let r := #(Bits.of_N 32 4294942216) in let i := #(Bits.of_N 32      60547) in struct complex {re:=r;im:=i} }}
|           3,          12 => {{let r := #(Bits.of_N 32          0) in let i := #(Bits.of_N 32      65536) in struct complex {re:=r;im:=i} }}
|           3,          13 => {{let r := #(Bits.of_N 32      25079) in let i := #(Bits.of_N 32      60547) in struct complex {re:=r;im:=i} }}
|           3,          14 => {{let r := #(Bits.of_N 32      46340) in let i := #(Bits.of_N 32      46340) in struct complex {re:=r;im:=i} }}
|           3,          15 => {{let r := #(Bits.of_N 32      60547) in let i := #(Bits.of_N 32      25079) in struct complex {re:=r;im:=i} }}
| _, _ => {{let r := #(Bits.of_N 32 0) in let i := #(Bits.of_N 32 0) in struct complex {re:=r;im:=i} }}
end.


Definition twist (stage:nat) (index:nat) : uaction reg_t ext_fn_t :=
    twiddle stage index
        .

  Definition stage_ft (stage:nat) : UInternalFunction reg_t ext_fn_t :=
    let ainit := array_init (reg_t:= reg_t) (struct_t complex) points in
    {{ fun stage_ft
      (stage_in: array_t {| array_type := struct_t complex ; array_len:= points|}) :
        array_t {| array_type := struct_t complex ; array_len:= points|} =>
    let zero := #(Bits.of_nat 32 0) in
    let zerocomplex := struct complex {re:= zero; im := zero} in
    let interm := ainit(zerocomplex) in
    `List.fold_left (fun acc el =>
        {{`acc`;
          let y := bfly2(`static_slice
                        (struct_t complex)
                        ({{zerocomplex}})
                        2
                        {{stage_in}}
                        (2*el)`,
                      `twist stage el`)
          in
          (set interm :=
             `static_update
                {{interm}}
                (el*2)
                (static_access {{y}} 0)`);
          set interm :=
             `static_update
                {{interm}}
                (el*2 + 1)
                (static_access {{y}} 1)`}})
        (seq 0 (points/2))
        {{ pass }}`;
    let out := ainit(zerocomplex) in
    `List.fold_left (fun acc el =>
    {{
      (set out :=
        `static_update
                {{ out }}
                el
                (static_access {{interm}} (permute el points))`); `acc`}})
        (seq 0 points)
        {{ pass }}`;
    out
    }}.

  Inductive rule_name_t := tb .

  Definition R r :=
  match r with
  | localSt =>  array_t {| array_type := struct_t complex ; array_len:= points|}
  end.

  Import VectNotations.

  Definition unpack_complex n :=
    @value_of_bits (struct_t complex) (Bits.of_N _ n).

  Import VectNotations.

  Definition r idx : R idx :=
  match idx with
    (*| localSt => value_of_bits (Bits.of_N (64*points) 4039432 : bits_t (64*points))*)
  | localSt =>
    vect_map unpack_complex
      [ 4039543289543432;
       4039543289543432;
       4039543289543432;
       4039543289543432;
       4039543289543432;
       4039543289543432;
       4039543289543432;
       4039543289543432;
       4039543289543432;
       4039543289543432;
       4039543289543432;
       4039543289543432;
       4039543289543432;
       4039543289543432;
       4039543289543432;
       4039543289543432]%N%vect
  end.

  Definition testbench_fir : scheduler :=
    tb |> done.

  Definition cr := ContextEnv.(create) r.

  Definition _tb : uaction reg_t ext_fn_t:=

  {{
      let result :=
      `List.fold_left (fun acc el =>
                         let fft := stage_ft el in {{fft(`acc`)}}) (seq 0 log_points) {{read0(localSt)}}` in
      write0(localSt, result)
  }}.

  (* Typechecking  *)
  Definition rules :=
    tc_rules R Sigma
             (fun r => match r with
                    | tb => _tb 
                    end).

  Definition external (r: rule_name_t) := false.
  
  Definition package :=
    {| ip_koika := {| koika_reg_types := R;
                     koika_reg_init := r;
                     koika_ext_fn_types := Sigma;
                     koika_rules := rules;
                     koika_rule_external := external;
                     koika_scheduler := testbench_fir;
                     koika_module_name := "fft" |};

       ip_sim := {| sp_ext_fn_names := empty_ext_fn_names;
                   sp_extfuns := None |};

       ip_verilog := {| vp_ext_fn_specs := empty_ext_fn_specs |} |}.
End FFT.

Definition prog := Interop.Backends.register package.
Extraction "fft.ml" prog.
