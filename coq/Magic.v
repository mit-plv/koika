(*! Tools | Universal axiom to replace the ‘admit’ tactic !*)
(* Having this here makes it possible to type “Require Import Magic” to get a
   universal axiom that allows Qed to go through (as ‘admit’ did in Coq 8.4) *)
Axiom __magic__ : forall {A}, A.
