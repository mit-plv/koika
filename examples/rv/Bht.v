(*! Implementation of a Bht !*)
Require Import Coq.Lists.List.

Require Import Koika.Frontend.
Require Import Koika.Std.

Module Type Bht_sig.
  Parameter idx_sz:nat.
  Parameter addr:nat.
End Bht_sig.
Definition write_style := @NestedSwitch var_t.
Definition read_style (nbits: nat) := @NestedSwitch var_t.

Module Bht (s:Bht_sig).
  Import s.



  Module RfParamsDirs <: RfPow2_sig.
    Definition idx_sz := idx_sz.
    Definition T := bits_t 2.
    Definition init := Bits.zeroes 2.
    Definition read_style := read_style 2.
    Definition write_style := write_style.
  End RfParamsDirs.

  Module Dirs := RfPow2 RfParamsDirs.

  Inductive reg_t := 
    dirs (state: Dirs.reg_t)
  .

  Definition R r :=
    match r with
    | dirs n => Dirs.R n
    end.

  Definition r idx : R idx :=
    match idx with
    | dirs n => Dirs.r n
    end.

  Definition name_reg r :=
    match r with
    | dirs n => String.append "dirs" (Dirs.name_reg n)
    end.

  Definition getIndex : UInternalFunction reg_t empty_ext_fn_t :=
    {{ (* Keep the idx_sz bits of the addr in words - that is drop the bottom two bits *)
        fun getIndex (a: bits_t addr) : bits_t idx_sz =>
          (a >> #(Bits.of_nat (log2 addr) 2))[#(Bits.of_nat (log2 addr) 0) :+ idx_sz] }}.

  Definition computeTarget : UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun computeTarget (pc: bits_t addr) (targetPc: bits_t addr) (taken: bits_t 1) : bits_t addr =>
        if taken
        then targetPc
        else (pc+ #(Bits.of_nat addr 4))
    }}.

  Definition extractDir : UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun extractDir (dp: bits_t 2) : bits_t 1 =>
        (dp == Ob~1~1) || (dp == Ob~1~0)
    }}.

  Definition getEntry : UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun getEntry (index: bits_t idx_sz) : bits_t 2 =>
           dirs.(Dirs.read_0)(index)
    }}.



  Definition newDpBits : UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun newDpBits (dpBits: bits_t 2) (taken: bits_t 1) : bits_t 2 =>
        if (taken )
        then
          (if dpBits == Ob~1~1 then dpBits else (dpBits + Ob~0~1))
        else
          (if dpBits == Ob~0~0 then dpBits else (dpBits - Ob~0~1))
    }}.

  Definition ppcDP: UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun ppcDP(pc: bits_t addr) (targetPC : bits_t addr) : bits_t addr =>
        let index := getIndex(pc) in
        let entry := getEntry(index) in
        let direction := extractDir(entry) in
        computeTarget(pc, targetPC, direction)
    }}.


  Definition update: UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun update(pc: bits_t addr) (taken : bits_t 1) : unit_t =>
        let index := getIndex(pc) in
        let entry := getEntry(index) in
        let newDp := newDpBits(entry,taken) in
        dirs.(Dirs.write_0)(index, newDp)
    }}.

End Bht.
