Require Import Koika.Common Koika.Types.

Section TypeErrors.
  Context {pos_t var_t fn_name_t: Type}.

  Inductive basic_error_message :=
  | UnboundField (f: string) (sig: struct_sig)
  | TypeMismatch (actual: type) (expected: type)
  | KindMismatch (actual: type_kind) (expected: type_kind).

  Inductive error_message :=
  | ExplicitErrorInAst
  | SugaredConstructorInAst
  | UnboundVariable (var: var_t)
  | UnboundEnumMember (f: string) (sig: enum_sig)
  | IncorrectRuleType (tau: type)
  | BasicError (msg: basic_error_message)
  | TooManyArguments (fn_name: fn_name_t) (nexpected: nat) (nextra: nat)
  | TooFewArguments (fn_name: fn_name_t) (nexpected: nat) (nmissing: nat).

  (* FIXME add ability to report error on meta arguments *)
  (* FIXME and use this to fix the location of unbound field errors *)
  Inductive fn_tc_error_loc := Arg1 | Arg2.
  Definition fn_tc_error : Type := fn_tc_error_loc * basic_error_message.

  Definition assert_bits_t arg (tau: type) : result nat fn_tc_error :=
    match tau with
    | bits_t sz => Success sz
    | enum_t _ | struct_t _ => Failure (arg, KindMismatch (kind_of_type tau) kind_bits)
    end.

  Definition assert_struct_t arg (tau: type) : result struct_sig fn_tc_error :=
    match tau with
    | struct_t sg => Success sg
    | bits_t _ | enum_t _ => Failure (arg, KindMismatch (kind_of_type tau) (kind_struct None))
    end.

  (* Error sources live in prop, because they are only useful in interactive
     mode: LV only cares about positions. *)
  Inductive ErrorSource : Prop :=
  | ErrSrc {T: Type} (t: T).

  Record error :=
    { epos: pos_t;
      emsg: error_message;
      esource: ErrorSource }.
End TypeErrors.

Arguments basic_error_message : clear implicits.
Arguments fn_tc_error : clear implicits.
Arguments error_message : clear implicits.
Arguments error : clear implicits.
