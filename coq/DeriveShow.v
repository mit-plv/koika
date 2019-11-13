Require Import Koika.Show.

Require Koika.IdentParsing.
Require Import Ltac2.Ltac2.

Import Ltac2.Init.
Import Ltac2.Notations.

Module Internals.
  Import Coq.Lists.List.ListNotations.
  Import IdentParsing.Unsafe.
  Import IdentParsing.

  Ltac2 Type exn ::= [ NotAConstructor (constr) ].

  Ltac2 eval_simpl c :=
    Std.eval_simpl {
        Std.rBeta := true;
        Std.rMatch := true;
        Std.rFix := true;
        Std.rCofix := true;
        Std.rZeta := true;
        Std.rDelta := true;
        Std.rConst := []
      } None c.

  Ltac2 rec list_map fn l :=
    match l with
    | [] => []
    | h :: t => fn h :: list_map fn t
    end.

  Ltac2 rec coq_list_of_list type fn ls :=
    match ls with
    | [] => constr:(@List.nil $type)
    | h :: t =>
      let ch := fn h in
      let ct := coq_list_of_list type fn t in
      constr:($ch :: $ct)
    end.

  Ltac2 path_of_constructor c :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.Constructor cstr _ =>
      let path := Env.path (Std.ConstructRef cstr) in
      coq_list_of_list constr:(String.string) coq_string_of_ident path
    | _ => Control.throw (NotAConstructor c)
    end.

  Ltac2 unpack_app c :=
    let rec loop acc c :=
        match! c with
        | ?f ?x => loop (x :: acc) f
        | ?x => x, acc
        end in
    loop [] c.

  Definition blocked (A: Type) := A.

  Ltac not_blocked t :=
    lazymatch t with
    | blocked _ => fail
    | _ => idtac
    end.

  Inductive Tracked {A} (x: A) := Track.

  Definition type_of {A} (a: A) := A.

  Fixpoint butlast {A} (l: list A) :=
    match l with
    | [] => []
    | [x] => [x]
    | hd :: tl => butlast tl
    end.

  Ltac2 derive_show_begin () :=
    ltac1:(match goal with
           | [  |- Show ?type ] =>
             econstructor;
               let term := fresh in
               intro term; pose proof (@Track type term); destruct term
           end).

  Ltac2 derive_show_recurse arg :=
    (* let instance := constr:(ltac:(typeclasses eauto) : Show (type_of $arg)) in *)
    constr:(show $arg).

  Ltac2 rec derive_show_app () :=
    lazy_match! goal with
    | [ _: Tracked ?app |- _ ] =>
      match unpack_app app with
      | (hd, args) => let hd_path := path_of_constructor hd in
                     let hd_str := constr:(String.concat "_" (butlast $hd_path)) in
                     let arg_strs := coq_list_of_list constr:(String.string) derive_show_recurse args in
                     let str := constr:(String.concat "_" ($hd_str :: $arg_strs)) in
                     let str := eval_simpl str in
                     exact $str
      end
    end.

  Ltac2 rec derive_show () :=
    Control.enter derive_show_begin; Control.enter derive_show_app.

  Hint Extern 2 (Show _) => ltac2:(derive_show ()) : typeclass_instances.
End Internals.

Ltac derive_show :=
  ltac2:(Control.enter Internals.derive_show).

Module Examples.
  Inductive x := X0 | X1 | X2.
  Inductive y := Y0 (_: x) | Y1 .

  Definition test (n: nat) : Show y := _.
End Examples.
