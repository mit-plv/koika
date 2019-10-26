Require Import Ltac2.Ltac2.
Import Ltac2.Init.
Require Import NArith.
Import Ltac2.Notations.


Ltac2 rec int_to_coq_N' n :=
  match Int.equal n 0 with
  | true => constr:(N.zero)
  | false => let n := int_to_coq_N' (Int.sub n 1) in
            constr:(N.succ $n)
  end.

Ltac2 eval_compute c :=
  Std.eval_cbv
    {
      Std.rBeta := true; Std.rMatch := true; Std.rFix := true; Std.rCofix := true;
      Std.rZeta := true; Std.rDelta := true; Std.rConst := [];
    } c.

Ltac2 int_to_coq_N n :=
  let val := int_to_coq_N' n in
  eval_compute val.

Ltac2 rec string_to_coq_list_N' s acc pos :=
  match Int.equal pos 0 with
  | true => acc
  | false =>
    let pos := Int.sub pos 1 in
    let n := int_to_coq_N (Char.to_int (String.get s pos)) in
    string_to_coq_list_N' s (constr:(List.cons $n $acc)) pos
  end.

Ltac2 string_to_coq_list_N s :=
  string_to_coq_list_N' s (constr:(@List.nil N)) (String.length s).

Definition string_of_list_N list_N :=
  String.string_of_list_ascii (List.map Ascii.ascii_of_N list_N).

Ltac2 string_to_coq_string s :=
  let list_N := string_to_coq_list_N s in
  eval_compute constr:(string_of_list_N $list_N).

Import String.
Ltac2 Eval (string_to_coq_string "lkgf").

Inductive __Ltac2_IdentMarker := __Ltac2_Mark.

Ltac2 Type exn ::= [ NoIdentInContext ].

Ltac serialize_ident_in_context :=
  ltac2:(match! goal with
  | [ h: __Ltac2_IdentMarker |- _ ] =>
    let ident_string := Ident.to_string h in
    let coq_string := string_to_coq_string ident_string in
    exact ($coq_string)
  | [  |- _ ] => Control.throw NoIdentInContext
  end).


Notation ident_to_string a := (match __Ltac2_Mark return string with
                               | a => ltac:(serialize_ident_in_context)
                               end) (only parsing).
