Require Import Koika.Frontend.

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
   {{ fun (data : T) : bits_t 0 =>
      if (!read0(valid0)) then
        write0(data0,data);
          write0(valid0,#Ob~1)
      else
        fail }}.


  Definition deq :  UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun _ : T =>
      if (read0(valid0)) then
        write0(valid0,`USugar (UConstBits Ob~0)`);
          read0(data0)
      else
        fail(5)}}.

  Instance FiniteType_reg_t : FiniteType reg_t := _.

End Fifo1.

Definition Maybe tau :=
  {| struct_name := "maybe";
     struct_fields := ("valid", bits_t 1)
                        :: ("data", tau)
                        :: nil |}.
Notation maybe tau := (struct_t (Maybe tau)).

Definition valid {tau reg_t fn} (x:uaction reg_t fn) : uaction reg_t fn :=
  {{
      struct (Maybe tau) {|
               valid := (#(Bits.of_nat 1 1)) ;
               data := `x`
             |}
  }}.

Definition invalid {tau reg_t fn} : uaction reg_t fn :=
  {{
      struct (Maybe tau) {| valid := (#(Bits.of_nat 1 0)) |}
  }}.

Module Type Rf_sig.
  Parameter lastIdx:nat.
  Parameter T:type.
  Parameter init: T.
End Rf_sig.

Module Rf (s:Rf_sig).
  Definition sz:= S s.lastIdx.
  Inductive reg_t := rData (n: Vect.index sz).

  Definition R r :=
    match r with
    | rData n => s.T
    end.

  Definition r idx : R idx :=
    match idx with
    | rData n => s.init
    end.

  Definition read : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun (idx : bits_t (log2 sz)) : s.T =>
    `UCompleteSwitch (log2 sz) (pred sz) "v"
     (vect_map (fun idx => {{ read0(rData idx) }}) (all_indices sz))`}}.

  Definition write : UInternalFunction reg_t empty_ext_fn_t :=
    {{fun (idx : bits_t (log2 sz)) (val: s.T) : bits_t 0 =>
    `UCompleteSwitch (log2 sz) (pred sz) "v"
     (vect_map (fun idx => {{ write0(rData idx, val) }}) (all_indices sz))`}}.
End Rf.

Fixpoint signExtend {reg_t} (n:nat) (m:nat) : UInternalFunction reg_t empty_ext_fn_t :=
  {{
      fun (arg : bits_t n) : bits_t (m+n) =>
        `match (m) with
         | O => {{ arg }}
         | S m => {{(arg[#(Bits.of_nat (log2 n) n)]) ++ (funcall (signExtend (log2 n) m)(arg))}}
         end`
  }}.
