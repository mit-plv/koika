Require Import Coq.Lists.List.

Require Import Koika.Frontend.
Require Import Koika.Std.

Module Type Scoreboard_sig.
  Parameter lastIdx:nat.
  Parameter maxScore:nat. (* Usually  maxScore ~= 3/4 *)
End Scoreboard_sig.

Module Scoreboard (s:Scoreboard_sig).
  Definition sz:= S s.lastIdx.
  Definition logScore := log2 s.maxScore.

  Module Rf_params <: Rf_sig.
    Definition lastIdx := s.lastIdx.
    Definition T := bits_t logScore.
    Definition init := Bits.zeroes logScore.
  End Rf_params.
  Module Rf := Rf Rf_params.

  Inductive reg_t := Scores (state: Rf.reg_t).
  Definition R r :=
    match r with
    | Scores n => Rf.R n
    end.

  Definition r idx : R idx :=
    match idx with
    | Scores n => Rf.r n
    end.

  Definition name_reg r :=
    match r with
    | Scores n => String.append "rf" (Rf.name_reg n)
    end.
  (* Internal functions *)
  Definition sat_incr : UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun (a: bits_t logScore) : bits_t logScore =>
          if ( a == #(Bits.of_nat logScore s.maxScore)) then fail(logScore)
          else a + #(Bits.of_nat logScore 1)
    }}.

  Definition sat_decr : UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun (a: bits_t logScore) : bits_t logScore =>
          if (a == |logScore`d0|) then fail(logScore)
          else (a - |logScore`d1|)
    }}.

  (* Interface: *)
  Definition insert : UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun (idx: bits_t (log2 sz)) : bits_t 0 =>
          let old_score := Scores.(Rf.read)(idx) in
          let new_score := sat_incr(old_score) in
          Scores.(Rf.write)(idx, new_score)
    }}.

  Definition remove : UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun (idx: bits_t (log2 sz)) : bits_t 0 =>
          let old_score := Scores.(Rf.read)(idx) in
          let new_score := sat_decr(old_score) in
          Scores.(Rf.write)(idx, new_score)
    }}.

  Definition search : UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun (idx: bits_t (log2 sz)) : bits_t logScore =>
          Scores.(Rf.read)(idx)
    }}.
End Scoreboard.
