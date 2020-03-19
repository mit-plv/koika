(*! Implementation of a multiplier module !*)

Require Import Koika.Frontend Koika.Std.

Module Type Multiplier_sig.
  Parameter n: nat.
End Multiplier_sig.

Module Multiplier (s: Multiplier_sig).
  Import s.

  Inductive reg_t := valid | operand1 | operand2 | result | n_step | finished.

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

  Definition name_reg r :=
    match r with
    | valid => "valid"
    | operand1 => "operand1"
    | operand2 => "operand2"
    | result => "result"
    | n_step => "n_step"
    | finished => "finished"
    end.

  Definition enq : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun enq (op1 : bits_t n) (op2 : bits_t n): bits_t 0 =>
         if (!read0(valid)) then
           write0(valid, #Ob~1);
           write0(operand1, op1);
           write0(operand2, op2);
           write0(result, |(n+n)`d0|);
           write0(n_step, |(log2 n)`d0|)
         else
           fail
    }}.

  Definition deq : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun deq () : bits_t (n+n) =>
         if (read1(valid) && read1(finished)) then
           write1(finished, #Ob~0);
           write1(valid, #Ob~0);
           read1(result)
         else
           fail@(bits_t (n+n))
    }}.

  Definition step : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun step () : bits_t 0 =>
         if (read0(valid) && !read0(finished)) then
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
         else
           fail
    }}.

  Instance FiniteType_reg_t : FiniteType reg_t := _.

End Multiplier.
