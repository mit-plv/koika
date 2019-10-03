Require Import SGA.Member SGA.TypedSyntax.
Require Import Coq.Bool.Bool.

Section SyntaxTools.
  Context {name_t var_t reg_t fn_t: Type}.
  Context {R: reg_t -> type}
          {Sigma: fn_t -> ExternalSignature}.

  Fixpoint existsb_subterm (f: forall sig tau, action var_t R Sigma sig tau -> bool) {sig tau} (a: action var_t R Sigma sig tau) :=
    f _ _ a ||
      match a with
      | Fail tau => false
      | Var m => false
      | Const cst => false
      | Assign m ex => existsb_subterm f ex
      | Seq r1 r2 => existsb_subterm f r1 || existsb_subterm f r2
      | Bind var ex body => existsb_subterm f ex || existsb_subterm f body
      | If cond tbranch fbranch => existsb_subterm f cond || existsb_subterm f tbranch || existsb_subterm f fbranch
      | Read port idx => false
      | Write port idx value => existsb_subterm f value
      | Call fn arg1 arg2 => existsb_subterm f arg1 || existsb_subterm f arg2
      end.

  Fixpoint member_mentions_shadowed_binding
           {K V} {EQ: EqDec K} {sig: list (K * V)} {k v} (m: member (k, v) sig) : bool :=
    match m return bool with
    | MemberHd k _ => false
    | MemberTl (k, _) (k', _) sig' m' => beq_dec k k' || member_mentions_shadowed_binding m'
    end.

  Fixpoint action_mentions_shadowed_var {EQ: EqDec var_t} {sig tau} (a: action var_t R Sigma sig tau) :=
    existsb_subterm (fun _ _ a => match a with
                               | Var m => member_mentions_shadowed_binding m
                               | _ => false
                               end) a.

  Fixpoint action_mentions_var {EQ: EqDec var_t} {sig tau} (k: var_t) (a: action var_t R Sigma sig tau) :=
    existsb_subterm (fun _ _ a => match a with
                               | @Var _ _ _ _ _ _ k' _ m => beq_dec k k'
                               | _ => false
                               end) a.
End SyntaxTools.
