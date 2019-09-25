Require Import Coq.Lists.List.
Require Import SGA.Syntax SGA.Primitives SGA.Interop.
Import ListNotations.

Section SyntaxMacros.
  Context {pos_t var_t reg_t: Type}.

  Section ConstBits.
    Context {fn_t: Type}.
    Notation uaction := (uaction pos_t var_t reg_t fn_t).

    Definition UConstBits {sz} (bs: bits sz) : uaction :=
      UConst (tau := bits_t sz) bs.
  End ConstBits.

  Context {custom_fn_t: Type}.
  Notation uaction := (uaction pos_t var_t reg_t (interop_ufn_t custom_fn_t)).

  Definition if_eq a1 a2 (tbranch fbranch: uaction) :=
    UIf (UCall (UPrimFn (UConvFn UEq)) a1 a2)
        tbranch
        fbranch.

  Fixpoint USwitch
           (var: uaction)
           (default: uaction)
           (branches: list (uaction * uaction))
    : uaction :=
    match branches with
    | nil => default
    | (val, action) :: branches =>
      if_eq var val
            action (USwitch var default branches)
    end.

  Fixpoint gen_switch {tau}
           (var: var_t)
           {nb} (branches: vect (type_denote tau * uaction) (S nb)) : uaction :=
    let '(label, branch) := vect_hd branches in
    match nb return vect _ (S nb) -> uaction with
    | 0 => fun _ => branch
    | S nb => fun branches => if_eq (UVar var) (UConst label)
                                branch (gen_switch var (vect_tl branches))
    end branches.

  Definition UCompleteSwitch
             sz bound
             (var: var_t)
             (branches: vect uaction (S bound)) :=
    gen_switch (tau := bits_t sz) var
               (vect_map2 (fun n a => (Bits.of_nat sz (index_to_nat n), a))
                          (all_indices (S bound)) branches).

  Fixpoint UInitStruct
           (sig: struct_sig)
           (fields: list (string * uaction)) :=
    match fields with
    | [] => UCall (UPrimFn (UConvFn (UInit (struct_t sig)))) (UConstBits Ob) (UConstBits Ob)
    | (f, a) :: fields => UCall (UPrimFn (UStructFn (UDo SubstField f)))
                              (UInitStruct sig fields) a
    end.
End SyntaxMacros.
