Require Export SGA.Common SGA.Types.

Inductive prim_ufn_t :=
| USel
| UPart (width: nat)
| UAnd
| UOr
| UNot
| ULsl
| ULsr
| UEq
| UConcat
| UUIntPlus
| UZExtL (nzeroes: nat)
| UZExtR (nzeroes: nat).

Inductive prim_fn_t :=
| Sel (sz: nat)
| Part (sz: nat) (width: nat)
| And (sz: nat)
| Or (sz: nat)
| Not (sz: nat)
| Lsl (bits_sz: nat) (shift_sz: nat)
| Lsr (bits_sz: nat) (shift_sz: nat)
| Eq (sz: nat)
| Concat (sz1 sz2 : nat)
| UIntPlus (sz : nat)
| ZExtL (sz: nat) (nzeroes: nat)
| ZExtR (sz: nat) (nzeroes: nat).

(* Like Nat.log2_iter, but switches to next power of two one number earlier
   (computes ceil(log2(n)) instead of floor(log2(n))). *)
Fixpoint log2_iter k_fuel p_logn q_n r_buffer :=
  match k_fuel with
    | O => p_logn
    | S k_fuel =>
      match r_buffer with
      | O => log2_iter k_fuel (S p_logn) (S q_n) (pred q_n)
      | S r_buffer => log2_iter k_fuel p_logn (S q_n) r_buffer
      end
  end.

Definition log2 n := log2_iter (pred n) 0 1 0.

Definition prim_sel {sz} (bs: bits sz) (idx: bits (log2 sz)) :=
  match Bits.to_index sz idx with
  | Some idx => Bits.nth bs idx
  | _ => false (* TODO: x *)
  end.

Definition prim_uint_plus {sz} (bs1 bs2: bits sz) :=
  Bits.of_N sz (Bits.to_N bs1 + Bits.to_N bs2)%N.

Definition prim_uSigma (fn: prim_ufn_t) '(bits_t sz1) '(bits_t sz2): prim_fn_t :=
  match fn with
  | USel => Sel sz1
  | UPart width => Part sz1 width
  | UAnd => And sz1
  | UOr => Or sz1
  | UNot => Not sz1
  | ULsl => Lsl sz1 sz2
  | ULsr => Lsr sz1 sz2
  | UEq => Eq sz1
  | UConcat => Concat sz1 sz2
  | UUIntPlus => UIntPlus sz1
  | UZExtL nzeroes => ZExtL sz1 nzeroes
  | UZExtR nzeroes => ZExtR sz1 nzeroes
  end.

(* Require Import Coq.Lists.List. *)
(* Import ListNotations. *)
(* Compute (List.map (fun x => (x, Nat.log2 x, log2 x)) [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22;23;24;25;26;27;28;29;30;31;32;33;34]). *)

Definition prim_Sigma (fn: prim_fn_t) : ExternalSignature :=
  match fn with
  | Sel sz => {{ sz ~> log2 sz ~> 1 }}
  | Part sz width => {{ sz ~> log2 sz ~> width }}
  | And sz => {{ sz ~> sz ~> sz }}
  | Or sz => {{ sz ~> sz ~> sz }}
  | Not sz => {{ sz ~> 0 ~> sz }}
  | Lsl bits_sz shift_sz => {{ bits_sz ~> shift_sz ~> bits_sz }}
  | Lsr bits_sz shift_sz => {{ bits_sz ~> shift_sz ~> bits_sz }}
  | Eq sz => {{ sz ~> sz ~> 1 }}
  | Concat sz1 sz2 => {{ sz1 ~> sz2 ~> sz1 + sz2 }}
  | UIntPlus sz => {{ sz ~> sz ~> sz }}
  | ZExtL sz nzeroes => {{ sz ~> 0 ~> nzeroes + sz }}
  | ZExtR sz nzeroes => {{ sz ~> 0 ~> sz + nzeroes }}
  end.

Definition prim_sigma (fn: prim_fn_t) : prim_Sigma fn :=
  match fn with
  | Sel _ => fun bs idx => w1 (prim_sel bs idx)
  | Part _ width => fun base _ => __magic__
  | And _ => Bits.map2 andb
  | Or _ => Bits.map2 orb
  | Not _ => fun bs _ => Bits.map negb bs
  | Lsl _ _ => fun bs places => Bits.lsl (Bits.to_nat places) bs
  | Lsr _ _ => fun bs places => Bits.lsr (Bits.to_nat places) bs
  | Eq sz => fun bs1 bs2 => if eq_dec bs1 bs2 then w1 true else w1 false
  | UIntPlus _ => fun bs1 bs2 => prim_uint_plus bs1 bs2
  | Concat _ _ => fun bs1 bs2 => Bits.app bs1 bs2
  | ZExtL _ nzeroes => fun bs _ => Bits.app (Bits.const nzeroes false) bs
  | ZExtR _ nzeroes => fun bs _ => Bits.app bs (Bits.const nzeroes false)
  end.
