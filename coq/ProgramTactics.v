(*! Tactics for proving user-defined circuits !*)
Require Import Koika.Common Koika.SemanticProperties.
Require Export Koika.BitTactics.

(** Rewrite all hypotheses that would change a term being matched in the context
 into a constructor **)
Ltac rewrite_hypotheses_in_match :=
  repeat match goal with
         | [ H: ?x = ?y |- context[match ?x with | _ => _ end ] ] =>
           let y_hnf := head_hnf y in
           is_constructor y_hnf;
           rewrite H
         | [ H: ?x = ?y, H2: context[match ?x with | _ => _ end ] |- _ ] =>
           let y_hnf := head_hnf y in
           is_constructor y_hnf;
           rewrite H in H2
         end.

Hint Rewrite @log_existsb_app @log_existsb_log_cons_eq @getenv_commit_update
     @latest_write_cons_eq @latest_write_app
     @latest_write0_cons_eq @latest_write0_app
     @latest_write1_cons_eq @latest_write1_app : log_cleanup.

Hint Rewrite @latest_write_None @latest_write0_None @latest_write1_None
     @latest_write_None_latest_write0 @latest_write_None_latest_write1
     using assumption : log_cleanup.

Hint Rewrite @log_existsb_log_cons_neq @latest_write_cons_neq
     @latest_write0_cons_neq @latest_write1_cons_neq
     using discriminate : log_cleanup.

Ltac log_cleanup_step :=
  match goal with
  | [ H: ?x = ?x |- _ ] => clear H
  | [ H: _ /\ _ |- _ ] => destruct H
  | [ x: _ * _ |- _ ] => destruct x
  | [ H: Some _ = Some _ |- _ ] => apply Some_inj in H
  | [ H: (_, _) = (_, _) |- _ ] => apply pair_inj in H
  | _ => progress subst
  | _ => progress bool_step
  | _ => progress rewrite_hypotheses_in_match
  | [ H: may_read _ _ _ = _ |- _ ] => unfold may_read in H
  | [ H: may_write _ _ _ _ = _ |- _ ] => unfold may_write in H
  | _ => progress autorewrite with log_cleanup in *
  end.

(** Interpret an action until a branch **)
Ltac interp_action_t :=
  repeat match goal with
         | [ H: interp_action _ _ _ _ _ ?action = Some _ |- _] =>
           unfold action in H;
           simpl (extract_success _ _) in H;
           unfold interp_action, opt_bind, no_latest_writes in *;
           repeat log_cleanup_step
         | _ => progress (simpl cassoc in *; simpl ctl in *; simpl chd in * )
         | [ H: match ?x with | Some(_) => _ | None => None end = Some (_) |- _ ] =>
           destruct x eqn:?; [ | solve [inversion H] ]
         | [ H: (if ?x then _ else None) = Some _ |- _ ] =>
           destruct x eqn:?; [ | solve [inversion H] ]
         | _ => progress log_cleanup_step
         end.

(** Interpret all possible branches of an action **)
Ltac interp_action_all_t :=
  repeat match goal with
         | _ => progress interp_action_t
         | [ H: (if ?c then _ else _) = Some (_, _, _) |- _ ] =>
           destruct c eqn:?
         end.
