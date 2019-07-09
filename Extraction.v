Require Import Coq.extraction.Extraction.
Require Import Coq.extraction.ExtrOcamlBasic Coq.extraction.ExtrOcamlString.

Require Import SGA.Common SGA.Syntax SGA.Circuits SGA.Examples.

Section Collatz.
  Open Scope string_scope.

  Notation scheduler := (scheduler Extfuns).
  Notation circuit := (circuit Extfuns).

  (* Example simple : rule _ _ := *)
  (*   (Bind "x" (Read P0 0) *)
  (*         (If (Call Even [Var "x"]) *)
  (*             (Write P0 1 (Const [true])) *)
  (*             (Write P0 1 (Const [false])))). *)

  Import Vector.VectorNotations.

  Definition compiled_collatz : option (circuits 1) :=
    compile_scheduler collatz [CExternal (Register 0) nil].

  Definition compiled_collatz_ls : list circuit :=
    match compiled_collatz with
    | Some cs => Vector.to_list cs
    | None => nil
    end.

  (* Definition interp_Extfuns ext (args: list bits) : option bits := *)
  (*     match ext, args with *)
  (*     | Even, [[b0; b1]] => Some [negb b1] *)
  (*     | ReadReg 0, [] => Some [false; false] *)
  (*     | ReadReg 1, [] => Some [false] *)
  (*     | _, _ => None *)
  (*     end%list. *)

  (* Compute (interp_circuits interp_Extfuns _ compiled_example). *)

  (* Lemma interp_circuit_unfold_once interp_external (c: circuit) : *)
  (*   interp_circuit interp_external c = *)
  (*   match c with *)
  (*   | CQuestionMark => None *)
  (*   | CNot c => *)
  (*     opt_bind (interp_circuit interp_external c) (fun bs => *)
  (*     Some (List.map negb bs)) *)
  (*   | CAnd c1 c2 => *)
  (*     opt_bind (interp_circuit interp_external c1) (fun bs1 => *)
  (*     opt_bind (interp_circuit interp_external c2) (fun bs2 => *)
  (*     Some (List.map (fun '(b1, b2) => andb b1 b2) (List.combine bs1 bs2)))) *)
  (*   | COr c1 c2 => *)
  (*     opt_bind (interp_circuit interp_external c1) (fun bs1 => *)
  (*     opt_bind (interp_circuit interp_external c2) (fun bs2 => *)
  (*     Some (List.map (fun '(b1, b2) => orb b1 b2) (List.combine bs1 bs2)))) *)
  (*   | CMux select c1 c2 => *)
  (*     opt_bind (interp_circuit interp_external select) (fun bs => *)
  (*     match bs with *)
  (*     | [b] => if b *)
  (*             then interp_circuit interp_external c1 *)
  (*             else interp_circuit interp_external c2 *)
  (*     | _ => None *)
  (*     end) *)
  (*   | CConst cst => Some cst *)
  (*   | CExternal e args => *)
  (*     opt_bind (List.fold_left (fun acc arg => *)
  (*                                 opt_bind acc (fun acc => *)
  (*                                 opt_bind (interp_circuit interp_external arg) (fun arg => *)
  (*                                 Some (arg :: acc)))) *)
  (*                              args (Some [])) (fun args => *)
  (*     interp_external e args) *)
  (*   end%list. *)
  (* Proof. *)
  (*   destruct c; reflexivity. *)
  (* Qed. *)

  (* Goal (opt_bind compiled_example (fun example => *)
  (*                                    Some (interp_circuits interp_Extfuns _ example))) = None. *)
  (* Proof. *)
  (*   rewrite interp_circuit_unfold_once. *)
  (*   change (opt_bind ?o ?f) with ltac:(let o := (eval cbv in o) in exact (opt_bind o f)). *)
  (*   cbv -[interp_circuit interp_TFn]. *)
End Collatz.

Extract Inductive list => "list" [ "[]" "(::)" ].
Extraction Inline Environments.StringEnv Environments.NatEnv.
Extraction "ocaml/sga.ml" circuit compiled_collatz_ls.
