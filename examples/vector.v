Require Import Koika.Frontend.

Definition nregs := 16.
Definition reg_sz := 32.

Inductive reg_t := rIndex | rData (n: Vect.index nregs) | rOutput.
Inductive rule_name_t := read_reg_sequential | read_reg_tree | incr_index.

Notation index_sz := (log2 nregs).

Definition R r :=
  match r with
  | rIndex => bits_t index_sz
  | rData n => bits_t reg_sz
  | rOutput => bits_t reg_sz
  end.

Definition r reg : R reg :=
  match reg with
  | rIndex => Bits.zero
  | rData n => Bits.of_nat _ (index_to_nat n)
  | rOutput => Bits.zero
  end.

(* This macro expands into a switch that branches on the value of [idx] to return
   the idx-th register in rData. *)
Definition read_vect_sequential idx : uaction reg_t empty_ext_fn_t :=
  {{ `UCompleteSwitch (SequentialSwitch (bits_t reg_sz) "tmp") index_sz idx
         (fun idx => {{ read0(rData idx) }})` }}.

Definition read_vect_tree idx : uaction reg_t empty_ext_fn_t :=
  {{ `UCompleteSwitch TreeSwitch index_sz idx
         (fun idx => {{ read0(rData idx) }})` }}.

Definition _read_reg_sequential : uaction reg_t empty_ext_fn_t :=
  {{
      let v := read0(rIndex) in
      write1(rOutput, `read_vect_sequential "v"`)
  }}.

Definition _read_reg_tree : uaction reg_t empty_ext_fn_t :=
  {{
      let v := read0(rIndex) in
      write0(rOutput, `read_vect_tree "v"`)
  }}.

Definition _incr_index : uaction reg_t empty_ext_fn_t :=
  {{ write0(rIndex, read0(rIndex) + |index_sz`d1|) }}.

Definition rules :=
  tc_rules R empty_Sigma
           (fun rl => match rl with
                   | read_reg_sequential => _read_reg_sequential
                   | read_reg_tree => _read_reg_tree
                   | incr_index => _incr_index
                   end).

Definition regfile : scheduler :=
  tc_scheduler (read_reg_sequential |> read_reg_tree |> incr_index |> done).

Definition external (r: rule_name_t) := false.

Definition circuits :=
  compile_scheduler rules external regfile.

Definition package :=
  {| ip_koika := {| koika_reg_types := R;
                   koika_reg_init reg := r reg;
                   koika_ext_fn_types := empty_Sigma;
                   koika_rules := rules;
                   koika_rule_external := external;
                   koika_scheduler := regfile;
                   koika_module_name := "vector" |};

     ip_sim := {| sp_ext_fn_names := empty_fn_names;
                 sp_extfuns := None |};

     ip_verilog := {| vp_ext_fn_names := empty_fn_names |} |}.

Definition prog := Interop.Backends.register package.
Extraction "vector.ml" prog.
