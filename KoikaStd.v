Require Import SGA.Notations.

Definition pos_t := unit.
Definition var_t := string.
Definition fn_name_t := string.
Notation uaction := (uaction pos_t var_t fn_name_t).
Notation UInternalFunction reg_t ext_fn_t := (InternalFunction fn_name_t var_t (uaction reg_t ext_fn_t)).

Module Type Fifo.
  Parameter T:type.
End Fifo.

Module Fifo1 (f: Fifo).
  Import f.
  Inductive reg_t := data0 |  valid0.

  Definition R r :=
    match r with
    | data0 => T
    | valid0 => bits_t 1
    end.

  Notation zero := (Bits.zeroes _).

  Definition r idx : R idx :=
    match idx with
    | data0 => value_of_bits zero
    | valid0 => zero
    end.

  Definition name_reg r :=
    match r with
    | data0 => "data0"
    | valid0 => "valid0"
    end.


  Definition enq : UInternalFunction reg_t empty_ext_fn_t :=
    function (data : T) : bits_t 0 :=
      if (!read0(valid0)) then
        write0(data0,data);
          write0(valid0,#Ob~1)
      else
        fail.


  Definition deq :  UInternalFunction reg_t empty_ext_fn_t :=
    function : T :=
      if (read0(valid0)) then
        write0(valid0,`UConstBits Ob~0`);
          read0(data0)
      else
        fail(5).

  Instance FiniteType_reg_t : FiniteType reg_t := _.

End Fifo1.
