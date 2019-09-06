Require Export SGA.Common SGA.Environments SGA.IndexUtils SGA.Types.

Inductive prim_bits_ufn_t :=
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

Inductive prim_struct_accessor := Get | Sub.

Inductive prim_struct_uop :=
| UInit
| UDo (op: prim_struct_accessor) (f: string).

Inductive prim_ufn_t :=
| BitsUFn (fn: prim_bits_ufn_t)
| StructUFn (sig: struct_sig) (op: prim_struct_uop).

Inductive prim_bits_fn_t :=
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

Inductive prim_struct_op {sig: struct_sig} :=
| Init
| Do (op: prim_struct_accessor) (f: Vect.index (List.length sig.(struct_fields))).
Arguments prim_struct_op : clear implicits.

Inductive prim_fn_t :=
| BitsFn (fn: prim_bits_fn_t)
| StructFn (sig: struct_sig) (fn: prim_struct_op sig).

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

Definition prim_uSigma (fn: prim_ufn_t) (tau1 tau2: type): result prim_fn_t fn_tc_error :=
  match fn with
  | BitsUFn fn =>
    let/res sz1 := assert_bits_t Arg1 tau1 in
    let/res sz2 := assert_bits_t Arg2 tau2 in
    Success (BitsFn match fn with
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
                    end)
  | StructUFn sig UInit =>
    Success (StructFn sig Init)
  | StructUFn sig (UDo op f) =>
    let/res idx := opt_result (List_assoc f sig.(struct_fields)) (Arg1, FnUnboundField f sig) in
    Success (StructFn sig (Do op idx))
  end.

Definition prim_Sigma (fn: prim_fn_t) : ExternalSignature :=
  match fn with
  | BitsFn fn =>
    match fn with
    | Sel sz => {{ bits_t sz ~> bits_t (log2 sz) ~> bits_t 1 }}
    | Part sz width => {{ bits_t sz ~> bits_t (log2 sz) ~> bits_t width }}
    | And sz => {{ bits_t sz ~> bits_t sz ~> bits_t sz }}
    | Or sz => {{ bits_t sz ~> bits_t sz ~> bits_t sz }}
    | Not sz => {{ bits_t sz ~> bits_t 0 ~> bits_t sz }}
    | Lsl bits_sz shift_sz => {{ bits_t bits_sz ~> bits_t shift_sz ~> bits_t bits_sz }}
    | Lsr bits_sz shift_sz => {{ bits_t bits_sz ~> bits_t shift_sz ~> bits_t bits_sz }}
    | Eq sz => {{ bits_t sz ~> bits_t sz ~> bits_t 1 }}
    | Concat sz1 sz2 => {{ bits_t sz1 ~> bits_t sz2 ~> bits_t (sz1 + sz2) }}
    | UIntPlus sz => {{ bits_t sz ~> bits_t sz ~> bits_t sz }}
    | ZExtL sz nzeroes => {{ bits_t sz ~> bits_t 0 ~> bits_t (nzeroes + sz) }}
    | ZExtR sz nzeroes => {{ bits_t sz ~> bits_t 0 ~> bits_t (sz + nzeroes) }}
    end
  | @StructFn sig Init =>
    {{ bits_t 0 ~> bits_t 0 ~> struct_t sig }}
  | @StructFn sig (Do Get idx) =>
    {{ struct_t sig ~> bits_t 0 ~> snd (List_nth sig.(struct_fields) idx) }}
  | @StructFn sig (Do Sub idx) =>
    {{ struct_t sig ~> snd (List_nth sig.(struct_fields) idx) ~> struct_t sig }}
  end.

Definition prim_sel {sz} (bs: bits sz) (idx: bits (log2 sz)) :=
  match Bits.to_index sz idx with
  | Some idx => Bits.nth bs idx
  | _ => false (* TODO: x *)
  end.

Definition prim_uint_plus {sz} (bs1 bs2: bits sz) :=
  Bits.of_N sz (Bits.to_N bs1 + Bits.to_N bs2)%N.

Fixpoint member_map {K K': Type} (f: K -> K') (k: K) (ls: list K)
         (m: member k ls) : member (f k) (List.map f ls) :=
  match m in (member k ls) return (member (f k) (List.map f ls)) with
  | MemberHd k sig =>
    MemberHd (f k) (List.map f sig)
  | MemberTl k k' sig m' =>
    MemberTl (f k) (f k') (List.map f sig) (member_map f k sig m')
  end.

Fixpoint type_accessor (tau: type) : Type :=
  match tau with
  | bits_t _sz => unit
  | struct_t fields =>
    let fs := fields.(struct_fields) in
    let field_accessors := List.map (fun '(k, tau) => type_accessor tau) fs in
    { k: index (List.length field_accessors) & List_nth field_accessors k }
  end.

Definition prim_sigma (fn: prim_fn_t) : prim_Sigma fn :=
  match fn with
  | BitsFn fn =>
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
    | ZExtL _ nzeroes => fun bs _ => Bits.app (Bits.zeroes nzeroes) bs
    | ZExtR _ nzeroes => fun bs _ => Bits.app bs (Bits.zeroes nzeroes)
    end
  | StructFn sig Init => fun _ _ => value_of_bits (Bits.zeroes (type_sz (struct_t sig)))
  | StructFn sig (Do Get idx) => fun s _ => __magic__
  | StructFn sig (Do Sub idx) => fun s _ => __magic__
  end.
