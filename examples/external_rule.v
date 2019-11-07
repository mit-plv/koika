Require Import Koika.Frontend.
Require Import Koika.Std.

(* Fifo1 of the Koika.Std is a polymorphic one element fifo.

The type of the fifo is indexed by the type of the data it holds, here
we specialize the type of the fifo to fifo that holds t bits values. *)
Module FifoBit5 <: Fifo.
  Definition T:= bits_t 5.
End FifoBit5.
Module Fifo5 := Fifo1 FifoBit5.

(* Define an instance for that fifo *)
Inductive reg_t := MyFifo (fifof2state:Fifo5.reg_t) | Mem | Rdata .

Definition logsz := 5.
Notation sz := (pow2 logsz).

(* Register types *)
Definition R r :=
  match r with
  | MyFifo f => Fifo5.R f
  | Mem => bits_t 5
  | Rdata => bits_t 5
  end.

(* Register's init value *)
Definition r idx : R idx :=
  match idx with
  | MyFifo f => Fifo5.r f
  | Mem => Bits.zeroes _
  | Rdata => Bits.zeroes _
  end.

(* Rules *)

(* This _fetch rule is going to be declared external, so removed from the
generated verilog, instead inputs and output will be generated to
delegate the work that this rule should do to an external circuit *)
Definition _fetch :=
  {{
      let memory := read0(Mem) in
      MyFifo.(Fifo5.enq)(memory)
  }}.

Definition _receive : uaction reg_t empty_ext_fn_t :=
  {{
      let dequeued := MyFifo.(Fifo5.deq)() in
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
