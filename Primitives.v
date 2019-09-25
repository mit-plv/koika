Require Export SGA.Common SGA.Environments SGA.IndexUtils SGA.Types.

Inductive prim_bits_ufn_t :=
| USel
| UPart (offset: nat) (width: nat)
| UPartSubst (offset: nat) (width: nat)
| UIndexedPart (width: nat)
| UAnd
| UOr
| UNot
| ULsl
| ULsr
| UConcat
| UUIntPlus
| UZExtL (width: nat)
| UZExtR (width: nat).

Inductive prim_uconverter :=
| UEq
| UInit (tau: type)
| UPack
| UUnpack (tau: type).

Inductive prim_struct_accessor := GetField | SubstField.

Inductive prim_struct_uop :=
| UDo (op: prim_struct_accessor) (f: string)
| UDoBits (sig: struct_sig) (op: prim_struct_accessor) (f: string).

Inductive prim_ufn_t :=
| UConvFn (op: prim_uconverter)
| UBitsFn (fn: prim_bits_ufn_t)
| UStructFn (op: prim_struct_uop).

Inductive prim_bits_fn_t :=
| Sel (sz: nat)
| Part (sz: nat) (offset: nat) (width: nat)
| PartSubst (sz: nat) (offset: nat) (width: nat)
| IndexedPart (sz: nat) (width: nat)
| And (sz: nat)
| Or (sz: nat)
| Not (sz: nat)
| Lsl (bits_sz: nat) (shift_sz: nat)
| Lsr (bits_sz: nat) (shift_sz: nat)
| EqBits (sz: nat)
| Concat (sz1 sz2 : nat)
| UIntPlus (sz : nat)
| ZExtL (sz: nat) (width: nat)
| ZExtR (sz: nat) (width: nat).

Inductive prim_converter := Eq | Init | Pack | Unpack.

Inductive prim_fn_t :=
| ConvFn (tau: type) (op: prim_converter)
| BitsFn (fn: prim_bits_fn_t)
| StructFn (sig: struct_sig) (op: prim_struct_accessor) (f: struct_index sig).

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

Definition GetFieldBits (sig: struct_sig) (idx: struct_index sig) : prim_fn_t :=
  BitsFn (Part (struct_sz sig) (field_offset_right sig idx) (field_sz sig idx)).

Definition SubstFieldBits (sig: struct_sig) (idx: struct_index sig) : prim_fn_t :=
  BitsFn (PartSubst (struct_sz sig) (field_offset_right sig idx) (field_sz sig idx)).

Definition prim_uSigma (fn: prim_ufn_t) (tau1 tau2: type): result prim_fn_t fn_tc_error :=
  match fn with
  | UConvFn op =>
    Success (match op with
             | UEq => ConvFn tau1 Eq
             | UPack => ConvFn tau1 Pack
             | UInit tau => ConvFn tau Init
             | UUnpack tau => ConvFn tau Unpack
             end)
  | UBitsFn fn =>
    let/res sz1 := assert_bits_t Arg1 tau1 in
    let/res sz2 := assert_bits_t Arg2 tau2 in
    Success (BitsFn match fn with
                    | USel => Sel sz1
                    | UPart offset width => Part sz1 offset width
                    | UPartSubst offset width => PartSubst sz1 offset width
                    | UIndexedPart width => IndexedPart sz1 width
                    | UAnd => And sz1
                    | UOr => Or sz1
                    | UNot => Not sz1
                    | ULsl => Lsl sz1 sz2
                    | ULsr => Lsr sz1 sz2
                    | UConcat => Concat sz1 sz2
                    | UUIntPlus => UIntPlus sz1
                    | UZExtL width => ZExtL sz1 width
                    | UZExtR width => ZExtR sz1 width
                    end)
  | UStructFn fn =>
    let find_field sig f :=
        opt_result (List_assoc f sig.(struct_fields)) (Arg1, FnUnboundField f sig) in
    match fn with
      | UDo op f =>
        let/res sig := assert_struct_t Arg1 tau1 in
        let/res idx := find_field sig f in
        Success (StructFn sig op idx)
      | UDoBits sig op f =>
        let/res idx := find_field sig f in
        Success match op with
                | GetField => GetFieldBits sig idx
                | SubstField => SubstFieldBits sig idx
                end
    end
  end.

Definition prim_Sigma (fn: prim_fn_t) : ExternalSignature :=
  match fn with
  | ConvFn tau op =>
    match op with
    | Eq => {{ tau ~> tau ~> bits_t 1 }}
    | Init => {{ unit_t ~> unit_t ~> tau }}
    | Pack => {{ tau ~> unit_t ~> bits_t (type_sz tau) }}
    | Unpack => {{ bits_t (type_sz tau) ~> unit_t ~> tau }}
    end
  | BitsFn fn =>
    match fn with
    | Sel sz => {{ bits_t sz ~> bits_t (log2 sz) ~> bits_t 1 }}
    | Part sz offset width => {{ bits_t sz ~> unit_t ~> bits_t width }}
    | PartSubst sz offset width => {{ bits_t sz ~> bits_t width ~> bits_t sz }}
    | IndexedPart sz width => {{ bits_t sz ~> bits_t (log2 sz) ~> bits_t width }}
    | And sz => {{ bits_t sz ~> bits_t sz ~> bits_t sz }}
    | Or sz => {{ bits_t sz ~> bits_t sz ~> bits_t sz }}
    | Not sz => {{ bits_t sz ~> unit_t ~> bits_t sz }}
    | Lsl bits_sz shift_sz => {{ bits_t bits_sz ~> bits_t shift_sz ~> bits_t bits_sz }}
    | Lsr bits_sz shift_sz => {{ bits_t bits_sz ~> bits_t shift_sz ~> bits_t bits_sz }}
    | EqBits sz => {{ bits_t sz ~> bits_t sz ~> bits_t 1 }}
    | Concat sz1 sz2 => {{ bits_t sz1 ~> bits_t sz2 ~> bits_t (sz1 + sz2) }}
    | UIntPlus sz => {{ bits_t sz ~> bits_t sz ~> bits_t sz }}
    | ZExtL sz width => {{ bits_t sz ~> unit_t ~> bits_t (Nat.max sz width) }}
    | ZExtR sz width => {{ bits_t sz ~> unit_t ~> bits_t (Nat.max sz width) }}
    end
  | @StructFn sig op idx =>
    match op with
    | GetField => {{ struct_t sig ~> unit_t ~> field_type sig idx }}
    | SubstField => {{ struct_t sig ~> field_type sig idx ~> struct_t sig }}
    end
  end.

Definition prim_sel {sz} (bs: bits sz) (idx: bits (log2 sz)) :=
  match Bits.to_index sz idx with
  | Some idx => Bits.nth bs idx
  | _ => false (* TODO: x *)
  end.

Definition prim_uint_plus {sz} (bs1 bs2: bits sz) :=
  Bits.of_N sz (Bits.to_N bs1 + Bits.to_N bs2)%N.

(* Fixpoint type_accessor (tau: type) : Type := *)
(*   match tau with *)
(*   | bits_t _sz => unit *)
(*   | struct_t fields => *)
(*     let fs := fields.(struct_fields) in *)
(*     let field_accessors := List.map (fun '(k, tau) => type_accessor tau) fs in *)
(*     { k: index (List.length field_accessors) & List_nth field_accessors k } *)
(*   end. *)

Definition prim_part {sz} (bs: bits sz) (offset: nat) (width: nat) :=
  vect_extend_end_firstn (vect_firstn width (vect_skipn offset bs)) false.

Lemma prim_part_subst_cast :
  forall sz width offset,
    Nat.min sz (Nat.min offset sz + (width + (sz - (offset + width)))) = sz.
Proof.
  induction sz, width, offset; cbn; auto using Min.min_idempotent.
  - f_equal; apply (IHsz 0 offset).
  - f_equal; apply (IHsz width 0).
  - f_equal; apply (IHsz (S width) offset).
Defined.

Definition prim_part_subst {sz}
           (bs: bits sz)
           (offset: nat)
           (width: nat)
           (v: bits width) : bits sz :=
  let head := vect_firstn offset bs in
  let tail := vect_skipn (offset + width) bs in
  ltac:(rewrite <- (prim_part_subst_cast sz width offset);
          exact (vect_firstn sz (vect_app head (vect_app v tail)))).

(* destruct offset. *)
(* - destruct width. *)
(*   + exact bs. *)
(*   + *)
(* destruct sz. *)
(* - exact vect_nil. *)
(* - destruct width. *)
(*   destruct offset. *)
(*   + destruct width. *)

Fixpoint get_field fields
         (v: struct_denote fields)
         (idx: index (List.length fields))
         {struct fields}
  : type_denote (snd (List_nth fields idx)).
  destruct fields, idx, p; cbn.
  - apply (fst v).
  - apply (get_field fields (snd v) a).
Defined.

Fixpoint subst_field fields
         (v: struct_denote fields)
         (idx: index (List.length fields))
         (v': type_denote (snd (List_nth fields idx)))
         {struct fields}
  : (struct_denote fields).
  destruct fields, idx, p; cbn.
  - apply (v', snd v).
  - apply (fst v, subst_field fields (snd v) a v').
Defined.

Definition prim_sigma (fn: prim_fn_t) : prim_Sigma fn :=
  match fn with
  | ConvFn tau fn =>
    match fn with
    | Eq => fun v1 v2 => if eq_dec v1 v2 then Ob~1 else Ob~0
    | Init => fun _ _ => value_of_bits (Bits.zeroes (type_sz tau))
    | Pack => fun v _ => bits_of_value v
    | Unpack => fun bs _ => value_of_bits bs
    end
  | BitsFn fn =>
    match fn with
    | Sel _ => fun bs idx => Ob~(prim_sel bs idx)
    | Part _ offset width => fun bs _ => prim_part bs offset width
    | PartSubst _ offset width => fun bs repl => prim_part_subst bs offset width repl
    | IndexedPart _ width => fun bs offset => prim_part bs (Bits.to_nat offset) width
    | And _ => Bits.map2 andb
    | Or _ => Bits.map2 orb
    | Not _ => fun bs _ => Bits.map negb bs
    | Lsl _ _ => fun bs places => Bits.lsl (Bits.to_nat places) bs
    | Lsr _ _ => fun bs places => Bits.lsr (Bits.to_nat places) bs
    | EqBits sz => fun bs1 bs2 => if eq_dec bs1 bs2 then Ob~1 else Ob~0
    | UIntPlus _ => fun bs1 bs2 => prim_uint_plus bs1 bs2
    | Concat _ _ => fun bs1 bs2 => Bits.app bs1 bs2
    | ZExtL sz width => fun bs _ => Bits.extend_end bs width false
    | ZExtR sz width => fun bs _ => Bits.extend_beginning bs width false
    end
  | StructFn sig GetField idx => fun s _ => get_field sig.(struct_fields) s idx
  | StructFn sig SubstField idx => fun s v => subst_field sig.(struct_fields) s idx v
  end.
