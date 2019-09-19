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
| UEq
| UConcat
| UUIntPlus
| UZExtL (nzeroes: nat)
| UZExtR (nzeroes: nat).

Inductive prim_converter := Init | Pack | Unpack.
Inductive prim_struct_accessor := GetField | SubstField.

Inductive prim_struct_uop :=
| UDo (op: prim_struct_accessor) (f: string)
| UDoBits (op: prim_struct_accessor) (f: string).

Inductive prim_ufn_t :=
| UConvFn (tau: type) (op: prim_converter)
| UBitsFn (fn: prim_bits_ufn_t)
| UStructFn (sig: struct_sig) (op: prim_struct_uop).

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
| Eq (sz: nat)
| Concat (sz1 sz2 : nat)
| UIntPlus (sz : nat)
| ZExtL (sz: nat) (nzeroes: nat)
| ZExtR (sz: nat) (nzeroes: nat).

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
  | UConvFn tau op =>
    Success (ConvFn tau op)
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
                    | UEq => Eq sz1
                    | UConcat => Concat sz1 sz2
                    | UUIntPlus => UIntPlus sz1
                    | UZExtL nzeroes => ZExtL sz1 nzeroes
                    | UZExtR nzeroes => ZExtR sz1 nzeroes
                    end)
  | UStructFn sig fn =>
    let find_field f :=
        opt_result (List_assoc f sig.(struct_fields)) (Arg1, FnUnboundField f sig) in
    match fn with
      | UDo op f =>
        let/res idx := find_field f in
        Success (StructFn sig op idx)
      | UDoBits op f =>
        let/res idx := find_field f in
        Success match op with
                | GetField => GetFieldBits sig idx
                | SubstField => SubstFieldBits sig idx
                end
    end
  end.

Definition prim_Sigma (fn: prim_fn_t) : ExternalSignature :=
  match fn with
  | ConvFn tau Init => {{ unit_t ~> unit_t ~> tau }}
  | ConvFn tau Pack => {{ tau ~> unit_t ~> bits_t (type_sz tau) }}
  | ConvFn tau Unpack => {{ bits_t (type_sz tau) ~> unit_t ~> tau }}
  | BitsFn fn =>
    match fn with
    | Sel sz => {{ bits_t sz ~> bits_t (log2 sz) ~> bits_t 1 }}
    | Part sz offset width => {{ bits_t sz ~> unit_t ~> bits_t width }}
    | PartSubst sz offset width => {{ bits_t sz ~> bits_t width ~> bits_t sz }}
    | IndexedPart sz width => {{ bits_t sz ~> bits_t width ~> bits_t sz }}
    | And sz => {{ bits_t sz ~> bits_t sz ~> bits_t sz }}
    | Or sz => {{ bits_t sz ~> bits_t sz ~> bits_t sz }}
    | Not sz => {{ bits_t sz ~> unit_t ~> bits_t sz }}
    | Lsl bits_sz shift_sz => {{ bits_t bits_sz ~> bits_t shift_sz ~> bits_t bits_sz }}
    | Lsr bits_sz shift_sz => {{ bits_t bits_sz ~> bits_t shift_sz ~> bits_t bits_sz }}
    | Eq sz => {{ bits_t sz ~> bits_t sz ~> bits_t 1 }}
    | Concat sz1 sz2 => {{ bits_t sz1 ~> bits_t sz2 ~> bits_t (sz1 + sz2) }}
    | UIntPlus sz => {{ bits_t sz ~> bits_t sz ~> bits_t sz }}
    | ZExtL sz nzeroes => {{ bits_t sz ~> unit_t ~> bits_t (nzeroes + sz) }}
    | ZExtR sz nzeroes => {{ bits_t sz ~> unit_t ~> bits_t (sz + nzeroes) }}
    end
  | @StructFn sig op idx =>
    match op with
    | GetField => {{ struct_t sig ~> unit_t ~> field_type sig idx }}
    | SubstField => {{ struct_t sig ~> field_type sig idx ~> struct_t sig }}
    (* | LazyGetField => {{ struct_bits_t sig ~> unit_t ~> bits_t (field_sz sig idx) }} *)
    (* | LazySubstField => {{ struct_bits_t sig ~> bits_t (field_sz sig idx) ~> struct_bits_t sig }} *)
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

Definition prim_sigma (fn: prim_fn_t) : prim_Sigma fn :=
  match fn with
  | ConvFn tau fn =>
    match fn with
    | Init => fun _ _ => value_of_bits (Bits.zeroes (type_sz tau))
    | Pack => fun v _ => bits_of_value v
    | Unpack => fun bs _ => value_of_bits bs
    end
  | BitsFn fn =>
    match fn with
    | Sel _ => fun bs idx => Ob~(prim_sel bs idx)
    | Part _ offset width => fun bs _ => __magic__
    | PartSubst _ offset width => fun bs repl => __magic__
    | IndexedPart _ width => fun bs idx => __magic__
    | And _ => Bits.map2 andb
    | Or _ => Bits.map2 orb
    | Not _ => fun bs _ => Bits.map negb bs
    | Lsl _ _ => fun bs places => Bits.lsl (Bits.to_nat places) bs
    | Lsr _ _ => fun bs places => Bits.lsr (Bits.to_nat places) bs
    | Eq sz => fun bs1 bs2 => if eq_dec bs1 bs2 then Ob~1 else Ob~0
    | UIntPlus _ => fun bs1 bs2 => prim_uint_plus bs1 bs2
    | Concat _ _ => fun bs1 bs2 => Bits.app bs1 bs2
    | ZExtL _ nzeroes => fun bs _ => Bits.app (Bits.zeroes nzeroes) bs
    | ZExtR _ nzeroes => fun bs _ => Bits.app bs (Bits.zeroes nzeroes)
    end
  | StructFn sig GetField idx => fun s _ => __magic__
  | StructFn sig SubstField idx => fun s _ => __magic__
  end.
