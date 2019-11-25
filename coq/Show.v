(*! Utilities | Show typeclass (α → string) !*)
Require Export Coq.Strings.String.

Class Show (A: Type) :=
  { show: A -> string }.

Module Show_nat.
  Lemma digit_lt_base m {n} : not (m + n < m).
  Proof.
    red; intros; eapply Le.le_Sn_n; eauto using Le.le_trans, Plus.le_plus_l.
  Qed.

  Definition string_of_base10_digit (n: {n | n < 10}) :=
    match n with
    | exist _ 0 _ => "0" | exist _ 1 _ => "1" | exist _ 2 _ => "2" | exist _ 3 _ => "3" | exist _ 4 _ => "4"
    | exist _ 5 _ => "5" | exist _ 6 _ => "6" | exist _ 7 _ => "7" | exist _ 8 _ => "8" | exist _ 9 _ => "9"
    | exist _ n pr => False_rect _ (digit_lt_base 10 pr)
    end%string.

  Fixpoint string_of_nat_rec (fuel: nat) (n: nat) :=
    match fuel with
    | O => ""%string
    | S fuel =>
      match (Compare_dec.lt_dec n 10) with
      | left pr  => string_of_base10_digit (exist _ n pr)
      | right pr => append (string_of_nat_rec fuel (PeanoNat.Nat.div n 10)) (string_of_nat_rec fuel (PeanoNat.Nat.modulo n 10))
      end
    end.

  Definition string_of_nat (n: nat) :=
    string_of_nat_rec (S n) n.
End Show_nat.

Instance Show_nat : Show nat :=
  { show := Show_nat.string_of_nat }.

Instance Show_string : Show string :=
  {| show x := x |}.
