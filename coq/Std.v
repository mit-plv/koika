(*! Stdlib | Standard library !*)
Require Import Koika.Frontend.

Section Maybe.
  Context (tau: type).

  Definition Maybe :=
    {| struct_name := "maybe_" ++ type_id tau;
       struct_fields := [("valid", bits_t 1); ("data", tau)] |}.

  Definition valid {reg_t fn} : UInternalFunction reg_t fn :=
    {{ fun valid (x: tau) : struct_t Maybe =>
         struct Maybe { valid := Ob~1; data := x } }}.

  Definition invalid {reg_t fn} : UInternalFunction reg_t fn :=
    {{ fun invalid () : struct_t Maybe =>
         struct Maybe { valid := Ob~0 } }}.
End Maybe.

Notation maybe tau := (struct_t (Maybe tau)).

Module Type Fifo.
  Parameter T:type.
End Fifo.

Module Fifo1 (f: Fifo).
  Import f.
  Inductive reg_t := data0 | valid0.

  Definition R r :=
    match r with
    | data0 => T
    | valid0 => bits_t 1
    end.

  Definition r idx : R idx :=
    match idx with
    | data0 => value_of_bits Bits.zero
    | valid0 => Bits.zero
    end.

  Definition name_reg r :=
    match r with
    | data0 => "data0"
    | valid0 => "valid0"
    end.

  Definition can_enq : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun can_enq () : bits_t 1 => !read1(valid0) }}.

  Definition enq : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun enq (data : T) : bits_t 0 =>
        guard (can_enq ());
        write1(data0, data);
        write1(valid0, #Ob~1) }}.

  Definition can_deq : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun can_deq () : bits_t 1 => read0(valid0) }}.

  Definition peek : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun peek () : maybe T =>
         if can_deq () then {valid T}(read0(data0))
         else {invalid T}() }}.

  Definition deq : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun deq () : T =>
        guard (can_deq ());
        write0(valid0, Ob~0);
        read0(data0) }}.

  Instance FiniteType_reg_t : FiniteType reg_t := _.
End Fifo1.

Module Fifo1Bypass (f: Fifo).
  Import f.
  Inductive reg_t := data0 |  valid0.

  Definition R r :=
    match r with
    | data0 => T
    | valid0 => bits_t 1
    end.

  Definition r idx : R idx :=
    match idx with
    | data0 => value_of_bits Bits.zero
    | valid0 => Bits.zero
    end.

  Definition name_reg r :=
    match r with
    | data0 => "data0"
    | valid0 => "valid0"
    end.

  Definition can_enq : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun can_enq () : bits_t 1 => !read0(valid0) }}.

  Definition enq : UInternalFunction reg_t empty_ext_fn_t :=
   {{ fun enq (data : T) : bits_t 0 =>
       guard (can_enq ());
       write0(data0, data);
       write0(valid0, #Ob~1) }}.

  Definition can_deq : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun can_deq () : bits_t 1 => read1(valid0) }}.

  Definition peek : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun peek () : maybe T =>
         if can_deq () then {valid T}(read1(data0))
         else {invalid T}() }}.

  Definition deq :  UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun deq () : T =>
       guard (can_deq ());
       write1(valid0, Ob~0);
       read1(data0) }}.

  Instance FiniteType_reg_t : FiniteType reg_t := _.
End Fifo1Bypass.

Module Type RfPow2_sig.
  Parameter idx_sz: nat.
  Parameter T: type.
  Parameter init: T.
  Parameter read_style : @switch_style var_t.
  Parameter write_style : @switch_style var_t.
End RfPow2_sig.

Module RfPow2 (s: RfPow2_sig).
  Definition sz := pow2 s.idx_sz.
  Inductive reg_t := rData (n: Vect.index sz).

  Definition R r :=
    match r with
    | rData _ => s.T
    end.

  Definition r idx : R idx :=
    match idx with
    | rData _ => s.init
    end.

  Definition name_reg r :=
    match r with
    | rData n => String.append "rData_" (show n)
    end.

  Definition read_0 : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun read_0 (idx : bits_t s.idx_sz) : s.T =>
         `UCompleteSwitch s.read_style s.idx_sz "idx"
              (fun idx => {{ read0(rData idx) }})` }}.

  Definition write_0 : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun write_0 (idx : bits_t s.idx_sz) (val: s.T) : unit_t =>
         `UCompleteSwitch s.write_style s.idx_sz "idx"
              (fun idx => {{ write0(rData idx, val) }})` }}.

  Definition read_1 : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun read_1 (idx : bits_t s.idx_sz) : s.T =>
         `UCompleteSwitch s.read_style s.idx_sz "idx"
              (fun idx => {{ read1(rData idx) }})` }}.

  Definition write_1 : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun write_1 (idx : bits_t s.idx_sz) (val: s.T) : unit_t =>
         `UCompleteSwitch s.write_style s.idx_sz "idx"
              (fun idx => {{ write1(rData idx, val) }})` }}.
End RfPow2.

Module Type Rf_sig.
  Parameter lastIdx: nat.
  Parameter T: type.
  Parameter init: T.
End Rf_sig.

Module Rf (s: Rf_sig).
  Definition lastIdx := s.lastIdx.
  Definition log_sz := log2 lastIdx.
  Definition sz := S lastIdx.
  Inductive reg_t := rData (n: Vect.index sz).

  Definition R r :=
    match r with
    | rData _ => s.T
    end.

  Definition r idx : R idx :=
    match idx with
    | rData _ => s.init
    end.

  Definition name_reg r :=
    match r with
    | rData n => String.append "rData_" (show n)
    end.

  Definition read : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun read (idx : bits_t log_sz) : s.T =>
         `USugar
             (USwitch
                {{idx}}
                {{fail(type_sz s.T)}}
                (List.map
                   (fun idx =>
                      (USugar (UConstBits
                                 (Bits.of_nat log_sz idx)),
                       {{ read0(rData (match (index_of_nat sz idx) with
                                       | Some idx => idx
                                       | _ => thisone
                                       end)) }}))
                   (List.seq 0 sz))) ` }}.

  Definition write : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun write (idx : bits_t log_sz) (val: s.T) : unit_t =>
         `USugar
          (USwitch
             {{idx}}
             {{fail}}
             (List.map
                (fun idx =>
                   (USugar (UConstBits
                              (Bits.of_nat log_sz idx)),
                    {{ write0(rData (match (index_of_nat sz idx) with
                                    | Some idx => idx
                                    | _ => thisone
                                    end), val) }}))
                   (List.seq 0 sz))) ` }}.
End Rf.

Definition signExtend {reg_t} (n:nat) (m:nat) : UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun signExtend (arg : bits_t n) : bits_t (m+n) => sext(arg, m + n) }}.

Module RfEhr (s: Rf_sig).

  Definition lastIdx := s.lastIdx.
  Definition log_sz := log2 lastIdx.
  Definition sz := S lastIdx.
  Inductive reg_t := rData (n: Vect.index sz).

  Definition R r :=
    match r with
    | rData _ => s.T
    end.

  Definition r idx : R idx :=
    match idx with
    | rData _ => s.init
    end.

  Definition name_reg r :=
    match r with
    | rData n => String.append "rData_" (show n)
    end.

  Definition read_0 : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun read_0 (idx : bits_t log_sz) : s.T =>
         `USugar
             (USwitch
                {{idx}}
                {{fail(type_sz s.T)}}
                (List.map
                   (fun idx =>
                      (USugar (UConstBits
                                 (Bits.of_nat log_sz idx)),
                       {{ read0(rData (match (index_of_nat sz idx) with
                                       | Some idx => idx
                                       | _ => thisone
                                       end)) }}))
                   (List.seq 0 sz))) ` }}.

  Definition read_1 : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun read_1 (idx : bits_t log_sz) : s.T =>
         `USugar
             (USwitch
                {{idx}}
                {{fail(type_sz s.T)}}
                (List.map
                   (fun idx =>
                      (USugar (UConstBits
                                 (Bits.of_nat log_sz idx)),
                       {{ read1(rData (match (index_of_nat sz idx) with
                                       | Some idx => idx
                                       | _ => thisone
                                       end)) }}))
                   (List.seq 0 sz))) ` }}.

  Definition write_0 : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun write_0 (idx : bits_t log_sz) (val: s.T) : unit_t =>
         `USugar
          (USwitch
             {{idx}}
             {{fail}}
             (List.map
                (fun idx =>
                   (USugar (UConstBits
                              (Bits.of_nat log_sz idx)),
                    {{ write0(rData (match (index_of_nat sz idx) with
                                    | Some idx => idx
                                    | _ => thisone
                                    end), val) }}))
                (List.seq 0 sz))) ` }}.

  Definition write_1 : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun write_1 (idx : bits_t log_sz) (val: s.T) : unit_t =>
         `USugar
          (USwitch
             {{idx}}
             {{fail}}
             (List.map
                (fun idx =>
                   (USugar (UConstBits
                              (Bits.of_nat log_sz idx)),
                    {{ write1(rData (match (index_of_nat sz idx) with
                                    | Some idx => idx
                                    | _ => thisone
                                    end), val) }}))
                   (List.seq 0 sz))) ` }}.
End RfEhr.
