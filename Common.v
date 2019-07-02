Class Env {K V: Type}: Type :=
  { env_t: Type;
    getenv: env_t -> K -> option V;
    putenv: env_t -> K -> V -> env_t }.
Arguments Env : clear implicits.
Arguments env_t {_ _}.

Inductive Posed {P: Prop}: P -> Prop :=
| AlreadyPosed : forall p: P, Posed p.

Tactic Notation "pose_once" uconstr(thm) :=
  (progress match goal with
            | [ H: Posed ?thm' |- _ ] =>
              unify thm thm'
            | _ => pose proof thm;
                  pose proof (AlreadyPosed thm)
            end).
