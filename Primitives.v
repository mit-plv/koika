Require Export SGA.Common SGA.Environments SGA.Types.

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

Inductive prim_struct_op := Init | Get | Put.

Inductive prim_ufn_t :=
| BitsUFn (fn: prim_bits_ufn_t)
| StructUFn (op: prim_struct_op) (sig: struct_sig) (f: string).

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

Inductive prim_fn_t :=
| BitsFn (fn: prim_bits_fn_t)
| StructFn (fn: prim_struct_op) (sig: struct_sig) (idx: Vect.index sig.(sv_len)).

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

Fixpoint Vector_find {K: Type} {n: nat} {EQ: EqDec K} (k: K) (v: Vector.t K n) {struct n} : option (Vect.index n).
Proof.
  destruct n.
  - exact None.
  - destruct (eq_dec k (Vector.hd v)).
    + exact (Some thisone).
    + destruct (Vector_find K n EQ k (Vector.tl v)).
      * exact (Some (anotherone i)).
      * exact None.
Defined.

Fixpoint Vector_assoc {K V: Type} {n: nat} {EQ: EqDec K} (k: K) (v: Vector.t (K * V) n) {struct n} : option (Vect.index n).
Proof.
  destruct n.
  - exact None.
  - destruct (eq_dec k (fst (Vector.hd v))).
    + exact (Some thisone).
    + destruct (Vector_assoc K V n EQ k (Vector.tl v)).
      * exact (Some (anotherone i)).
      * exact None.
Defined.

Definition prim_uSigma (fn: prim_ufn_t) (tau1 tau2: type): result prim_fn_t fn_tc_error :=
  match fn with
  | BitsUFn fn =>
    let/res sz1 := assert_bits_t tau1 in
    let/res sz2 := assert_bits_t tau1 in
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
  | StructUFn op sig f =>
    let/res idx := opt_result (Vector_assoc f sig.(sv_data)) (unbound_field f sig) in
    Success (StructFn op sig idx)
  end.

Fixpoint Vector_nth {K: Type} {n: nat} (v: Vector.t K n) (idx: Vect.index n) {struct n} : K.
Proof.
  destruct n; destruct idx.
  - exact (Vector.hd v).
  - exact (Vector_nth K n (Vector.tl v) a).
Defined.

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
  | @StructFn fn sig idx =>
    {{ struct_t sig ~> bits_t 0 ~> snd (Vector_nth sig.(sv_data) idx) }}
  end.

Definition prim_sel {sz} (bs: bits sz) (idx: bits (log2 sz)) :=
  match Bits.to_index sz idx with
  | Some idx => Bits.nth bs idx
  | _ => false (* TODO: x *)
  end.

Definition prim_uint_plus {sz} (bs1 bs2: bits sz) :=
  Bits.of_N sz (Bits.to_N bs1 + Bits.to_N bs2)%N.

(* Record struct_field_selector {fields: struct_sig} := *)
(*   { sfs_field_name : string; *)
(*     sfs_field_type : type; *)
(*     sfs_correct : member (sfs_field_name, sfs_field_type) fields }. *)
(* Arguments struct_field_selector : clear implicits. *)

Fixpoint member_map {K K': Type} (f: K -> K') (k: K) (ls: list K)
         (m: member k ls) : member (f k) (List.map f ls) :=
  match m in (member k ls) return (member (f k) (List.map f ls)) with
  | MemberHd k sig =>
    MemberHd (f k) (List.map f sig)
  | MemberTl k k' sig m' =>
    MemberTl (f k) (f k') (List.map f sig) (member_map f k sig m')
  end.

Require Import SGA.Vect.
Fixpoint list_nth_index {K: Type} (l: list K) (idx: index (List.length l)) {struct l} : K.
  destruct l; destruct idx.
  - exact k.
  - exact (list_nth_index K l a).
Defined.

Fixpoint type_accessor (tau: type) : Type :=
  match tau with
  | bits_t _sz => unit
  | struct_t fields =>
    let field_accessors := Vector.map (fun '(k, tau) => type_accessor tau) fields.(sv_data) in
    { k: index fields.(sv_len) & Vector_nth field_accessors k }
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
    | ZExtL _ nzeroes => fun bs _ => Bits.app (Bits.const nzeroes false) bs
    | ZExtR _ nzeroes => fun bs _ => Bits.app bs (Bits.const nzeroes false)
    end
  | StructFn Init sig m => fun s _ => __magic__
  | StructFn Get sig m => fun s _ => __magic__
  | StructFn Put sig m => fun s _ => __magic__
  end.
