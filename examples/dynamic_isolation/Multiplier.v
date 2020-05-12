(*! Implementation of a multiplier module !*)

Require Import Koika.Frontend Koika.Std.

Module Type Multiplier_sig.
  Parameter n: nat.
End Multiplier_sig.

Module Type MultiplierInterface.
  Axiom reg_t : Type.
  Axiom R : reg_t -> type.
  Axiom r : forall idx: reg_t, R idx.
  Axiom enq : UInternalFunction reg_t empty_ext_fn_t.
  Axiom deq : UInternalFunction reg_t empty_ext_fn_t.
  Axiom step : UInternalFunction reg_t empty_ext_fn_t.
  Axiom enabled : UInternalFunction reg_t empty_ext_fn_t.
  Axiom reset : UInternalFunction reg_t empty_ext_fn_t.
  Axiom FiniteType_reg_t : FiniteType reg_t.
  Axiom Show_reg_t : Show reg_t.
End MultiplierInterface.

Module ShiftAddMultiplier (s: Multiplier_sig) <: MultiplierInterface.
  Import s.

  Inductive _reg_t := valid | operand1 | operand2 | result | n_step | finished.
  Definition reg_t := _reg_t.

  Definition R r :=
    match r with
    | valid => bits_t 1          (* A computation is being done *)
    | operand1 => bits_t n       (* The first operand *)
    | operand2 => bits_t n       (* The second operand *)
    | result => bits_t (n+n)     (* The result being computed *)
    | n_step => bits_t (log2 n)  (* At which step of the computation we are *)
    | finished => bits_t 1       (* Indicates if the computation has finished *)
    end.

  Definition r idx : R idx :=
    match idx with
    | valid => Bits.zero
    | operand1 => Bits.zero
    | operand2 => Bits.zero
    | result => Bits.zero
    | n_step => Bits.zero
    | finished => Bits.zero
    end.

  Definition enq : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun enq (op1 : bits_t n) (op2 : bits_t n): unit_t =>
         guard (!read0(valid));
         write0(valid, #Ob~1);
         write0(operand1, op1);
         write0(operand2, op2);
         write0(result, |(n+n)`d0|);
         write0(n_step, |(log2 n)`d0|)
    }}.

  Definition deq : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun deq () : bits_t (n+n) =>
         guard (read1(valid) && read1(finished));
         write1(finished, #Ob~0);
         write1(valid, #Ob~0);
         read1(result)
    }}.

  Definition step : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun step () : unit_t =>
         guard (read0(valid) && !read0(finished));
         let n_step_val := read0(n_step) in
         (if read0(operand2)[n_step_val] then
            let partial_mul := zeroExtend(read0(operand1), n+n) << n_step_val in
            write0(result, read0(result) + partial_mul)
          else
            pass);
         if (n_step_val == #(Bits.of_nat (log2 n) (n-1))) then
           write0(finished, #Ob~1)
         else
           write0(n_step, n_step_val + |(log2 n)`d1|)
    }}.

  Definition enabled : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun enabled () : bits_t 1 => Ob~1 }}.

  Definition reset : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun reset () : bits_t 0 =>
         write0(valid, Ob~0);
         write0(operand1, `UConst (tau := bits_t n) Bits.zero`);
         write0(operand2, `UConst (tau := bits_t n) Bits.zero`);
         write0(result, `UConst (tau := bits_t (n+n)) Bits.zero`);
         write0(n_step, `UConst (tau := bits_t (log2 n)) Bits.zero`);
         write0(finished, Ob~0)
    }}.

  Instance FiniteType_reg_t : FiniteType reg_t := _.
  Instance Show_reg_t : Show reg_t := _.
End ShiftAddMultiplier.

Module DummyMultiplier (s: Multiplier_sig) <: MultiplierInterface.
  Import s.

  Inductive _reg_t :=.
  Definition reg_t := _reg_t.

  Definition R (idx: reg_t) : type := match idx with end.
  Definition r idx : R idx := match idx with end.

  Definition enq : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun enq (op1 : bits_t n) (op2 : bits_t n): unit_t => pass }}.

  Definition deq : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun deq () : bits_t (n+n) => |(n + n)`d0| }}.

  Definition step : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun step () : unit_t => pass }}.

  Definition enabled : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun enabled () : bits_t 1 => Ob~0 }}.

  Definition reset : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun reset () : bits_t 0 => pass }}.

  Instance FiniteType_reg_t : FiniteType reg_t := _.
  Instance Show_reg_t : Show reg_t := _.
End DummyMultiplier.
