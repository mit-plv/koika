Require Export SGA.Common SGA.Types.

Inductive prim_fn_t :=
| Sel (logsz: nat)
| Part (logsz: nat) (width: index (pow2 logsz))
| And (sz: nat)
| Or (sz: nat)
| Not (sz: nat)
| Lsl (sz: nat) (places: index sz)
| Lsr (sz: nat) (places: index sz)
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
  | Lsl sz places => {{ sz ~> 0 ~> sz }}
  | Lsr sz places => {{ sz ~> 0 ~> sz }}
  | Eq sz => {{ sz ~> sz ~> 1 }}
  | Concat sz1 sz2 => {{ sz1 ~> sz2 ~> sz1 + sz2 }}
  | UIntPlus sz => {{ sz ~> sz ~> sz }}
  | ZExtL sz nzeroes => {{ sz ~> 0 ~> nzeroes + sz }}
  | ZExtR sz nzeroes => {{ sz ~> 0 ~> sz + nzeroes }}
  end.

Definition prim_sigma (fn: prim_fn_t) : prim_Sigma fn :=
  match fn with
  | Sel logsz => fun bs idx => w1 (prim_sel bs idx)
  | Part logsz width => fun base _ => __magic__
  | And sz => Bits.map2 andb
  | Or sz => Bits.map2 orb
  | Not sz => fun bs _ => Bits.map negb bs
  | Lsl sz places => fun bs _ => __magic__
  | Lsr sz places => fun bs _ => __magic__
  | Eq sz => fun bs1 bs2 => if eq_dec bs1 bs2 then w1 true else w1 false
  | UIntPlus sz => fun bs1 bs2 => prim_uint_plus bs1 bs2
  | Concat sz1 sz2 => fun bs1 bs2 => Bits.app bs1 bs2
  | ZExtL sz nzeroes => fun bs _ => Bits.app (Bits.const nzeroes false) bs
  | ZExtR sz nzeroes => fun bs _ => Bits.app bs (Bits.const nzeroes false)
  end.
