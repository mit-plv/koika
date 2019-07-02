Class Env {K V: Type}: Type :=
  { env_t: Type;
    getenv: env_t -> K -> option V;
    putenv: env_t -> K -> V -> env_t }.
Arguments Env : clear implicits.
Arguments env_t {_ _}.
