Require Export SGA.Common SGA.Types.

Inductive prim_fn_t :=
| Sel (logsz: nat)
| Part (logsz: nat) (width: index (pow2 logsz))
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

Definition prim_sel {logsz} (bs: bits (pow2 logsz)) (idx: bits logsz) :=
  match Bits.to_index (pow2 logsz) bs with
  | Some idx => Bits.nth bs idx
  | _ => false (* TODO: x *)
  end.

Definition prim_uint_plus {sz} (bs1 bs2: bits sz) :=
  Bits.of_N sz (Bits.to_N bs1 + Bits.to_N bs2)%N.

Definition prim_Sigma (fn: prim_fn_t) : ExternalSignature :=
  match fn with
  | Sel logsz => {{ pow2 logsz ~> logsz ~> 1 }}
  | Part logsz width => {{ pow2 logsz ~> logsz ~> (index_to_nat width) }}
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
