Require Import Koika.Frontend.
Require Koika.Std.

(* Koika.Std.Fifo1 is a polymorphic one-element fifo.

  The type of the fifo is indexed by the type of the data it holds, here we
  specialize the type of the fifo to fifo that holds [bits_t 5] values. *)

Module FifoParams <: Std.Fifo.
  Definition T := bits_t 5.
End FifoParams.

Module Bits5Fifo := Std.Fifo1 FifoParams.

(* FifoSt is the state of an instant of Bits5Fifo *)
Inductive reg_t :=
| FifoSt (_: Bits5Fifo.reg_t)
| Mem
| Rdata.

Definition R r :=
  match r with
  | FifoSt f => Bits5Fifo.R f
  | Mem => bits_t 5
  | Rdata => bits_t 5
  end.

Definition r idx : R idx :=
  match idx with
  | FifoSt f => Bits5Fifo.r f
  | Mem => Bits.zero
  | Rdata => Bits.zero
  end.

(* Rules *)

(* This _fetch rule is going to be declared external, so removed from the
generated verilog, instead inputs and output will be generated to
delegate the work that this rule should do to an external circuit *)
Definition _fetch :=
  {{
      let memory := read0(Mem) in
      FifoSt.( Bits5Fifo.enq)(memory)
  }}.

Definition _receive : uaction reg_t empty_ext_fn_t :=
  {{
      let dequeued := FifoSt.( Bits5Fifo.deq)() in
      if (dequeued == Ob~0~0~0~1~0) then
        write0(Rdata, Ob~0~0~0~0~1)
      else
        fail
  }}.


Definition cr := ContextEnv.(create) r.

Inductive name_t := fetch | receive.

Definition rules :=
  tc_rules R empty_Sigma
           (fun rl => match rl with
                   | receive => _receive
                   | fetch => _fetch
                   end).

Definition bring : scheduler :=
  tc_scheduler (fetch |> receive |> done).

Definition koika_package :=
  {| koika_reg_types := R;
     koika_reg_init := r;
     koika_reg_finite := _;

     koika_ext_fn_types := empty_Sigma;

     koika_reg_names := show;

     koika_rules := rules;
     koika_rule_names := show;

     koika_scheduler := bring;
     koika_module_name := "externalMemory" |}.
Definition sim :=
  {| sp_var_names x := x;
     sp_ext_fn_names := empty_fn_names;
     sp_extfuns := None |}.
Definition verilog :=
  {| vp_external_rules := cons fetch nil;
     (* Here we declared the rule that is going to be removed by the verilog backend to let us insert an external circuit *)
     vp_ext_fn_names := empty_fn_names |} .
Definition package : interop_package_t := {| ip_koika := koika_package; ip_sim := sim; ip_verilog := verilog |}.

Definition prog := Interop.Backends.register package.
Extraction "external_rule.ml" prog.
