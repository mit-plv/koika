(*! Using WP calculus !*)
Require Import Koika.Frontend.
Require Import Koika.WP.
Require Import Koika.CompactSemantics.

Notation uaction := (uaction pos_t var_t fn_name_t).
Notation action := (action pos_t var_t fn_name_t).
Notation rule := (rule pos_t var_t fn_name_t).

Notation scheduler := (scheduler pos_t _).

Notation UInternalFunction reg_t ext_fn_t := (InternalFunction var_t fn_name_t (uaction reg_t ext_fn_t)).
Notation InternalFunction R Sigma sig tau := (InternalFunction var_t fn_name_t (action R Sigma sig tau)).

Inductive reg_t := queue_data | output_buffer | input_buffer | queue_invalid.
Inductive ext_fn_t := Stream | F | G.
Inductive rule_name_t := doF | doG.

Definition sz := (pow2 5).

Definition R r :=
  match r with
  | queue_data => bits_t sz
  | input_buffer => bits_t sz
  | output_buffer => bits_t sz
  | queue_invalid => bits_t 1
  end.

Definition r reg : R reg :=
  match reg with
  | queue_data => Bits.zero
  | output_buffer => Bits.zero
  | input_buffer => Bits.zero
  | queue_invalid => Ob~1
  end.

Definition Sigma (fn: ext_fn_t) : ExternalSignature :=
  match fn with
  | Stream => {$ bits_t sz ~> bits_t sz $}
  | F => {$ bits_t sz ~> bits_t sz $}
  | G => {$ bits_t sz ~> bits_t sz $}
  end.

Definition _doF : uaction _ _ :=
  {{
     let v := read0(input_buffer) in
     write0(input_buffer, extcall Stream(v));
     let queue_invalid := read1(queue_invalid) in
     if queue_invalid then
       write1(queue_invalid, Ob~0);
       write0(queue_data,extcall F(v))
     else
       fail
  }}.

Definition _doG : uaction _ _ :=
  {{
      let queue_invalid := read0(queue_invalid) in
      if !queue_invalid then
        let data := read0(queue_data) in
        write0(output_buffer, extcall G(data));
        write0(queue_invalid, Ob~1)
      else
        fail
  }}.

Definition rules :=
  tc_rules R Sigma
           (fun rl => match rl with
                   | doF => _doF
                   | doG => _doG
                   end).

Definition pipeline : scheduler :=
  doG |> doF |> done.

Section correct.
  Context {REnv: Env reg_t}.

  Definition rls :=
    Eval cbv in rules.

  Instance FiniteType_reg_t : FiniteType reg_t := _.


  Lemma beq_dec_refl {A} {EQ: EqDec A}:
    forall a, beq_dec a a = true.
  Proof.
    intros.
    unfold beq_dec.
    rewrite eq_dec_refl; reflexivity.
  Qed.

  (* FIXME: is it a cbn bug that adding exclamation points below prevents reduction?*)
  (* Probably due to implicits *)
  (* Arguments may_read _ _ _ /. *)
  (* Arguments may_write _ _ _ /. *)
  (* cbn. *)

  Context (sigma: forall f, Sig_denote (Sigma f)).
  Context (r: ContextEnv.(env_t) R).

  Arguments wp_action {pos_t var_t fn_name_t} {reg_t ext_fn_t} {R Sigma} {REnv} r sigma
            {sig tau} _ !_ _ /.

  Arguments interp_scheduler_cps {pos_t var_t fn_name_t rule_name_t reg_t ext_fn_t}%type_scope {R Sigma}%function_scope {REnv} r (sigma rules)%function_scope !s / {A}%type_scope k : assert.
  Arguments interp_rule_cps {pos_t var_t fn_name_t reg_t ext_fn_t}%type_scope {R Sigma}%function_scope {REnv} r sigma%function_scope !rl / {A}%type_scope k log : assert.

  Arguments wp_scheduler {pos_t var_t fn_name_t rule_name_t reg_t ext_fn_t}%type_scope {R Sigma}%function_scope {REnv} r (sigma rules)%function_scope !s / post : assert.

  Lemma scheduler_correct :
    exists l', interp_scheduler r sigma rls pipeline = l'.
  Proof.
    unfold pipeline.
    (* unfold interp_scheduler, interp_scheduler', interp_rule; simpl. *)
    (* rewrite <- interp_scheduler_cps_correct; simpl. *)
    apply wp_scheduler_correct.
    simpl.
    Arguments logentry_app {T}%type_scope !l1 !l2 /: assert.
    simpl.
    destruct (Bits.single (getenv ContextEnv r queue_invalid)); simpl.
    all: eexists; reflexivity.
  Qed.

  Arguments wp_cycle {pos_t var_t fn_name_t rule_name_t reg_t ext_fn_t}%type_scope {R Sigma}%function_scope {REnv} r (sigma rules)%function_scope !s / post : assert.

  Notation "env .[ idx ]" := (getenv ContextEnv env idx) (at level 1, format "env .[ idx ]").
  (* FIXME remove these notations *)
  Notation "0b0" := {| vhd := false; vtl := _vect_nil |}.
  Notation "0b1" := {| vhd := true; vtl := _vect_nil |}.

  Arguments may_read /.
  Arguments may_write /.

  Lemma cycle_correct :
    forall (init: ContextEnv.(env_t) R),
    exists l', Logs.commit_update init (TypedSemantics.interp_scheduler init sigma rls pipeline) = l'.
  Proof.
    intros; unfold pipeline.
    Time unfold TypedSemantics.interp_scheduler, TypedSemantics.interp_scheduler', TypedSemantics.interp_rule; simpl. (* 11s *)
  Abort.

  Lemma cycle_correct :
    forall (init: ContextEnv.(env_t) R),
    exists l', CompactLogs.commit_update init (CompactSemantics.interp_scheduler init sigma rls pipeline) = l'.
  Proof.
    intros; unfold pipeline.
    Time unfold CompactSemantics.interp_scheduler, CompactSemantics.interp_scheduler', CompactSemantics.interp_rule; simpl. (* 17s *)
  Abort.

  Lemma cycle_correct :
    forall (init: ContextEnv.(env_t) R),
    exists l', CompactLogs.commit_update init (CompactSemantics.interp_scheduler init sigma rls pipeline) = l'.
  Proof.
    intros; unfold pipeline.
    apply wp_cycle_correct.
    Time simpl. (* 0.6s *)

    destruct (Bits.single init.[queue_invalid]); simpl.
    - (* Initialization: nothing in the queue yet *)
      eexists; reflexivity.
    - (* Steady state: queue remains full *)
      eexists; reflexivity.
  Qed.







  Lemma doG_correct :
    Bits.single (ContextEnv.(getenv) r queue_invalid) = false ->
    (* ContextEnv.(getenv) r queue_data = (sigma F) (ContextEnv.(getenv) r output_buffer) -> *)
    exists l,
      interp_rule r sigma log_empty (rls doG) = Some l /\
      (ContextEnv.(getenv) l queue_invalid).(lwrite0) = Some Ob~1.
  (* FIXME: which style is better; exists or match? *)
  (* match interp_rule r sigma log_empty (rls doG) with *)
  (* | Some l => *)
  (*   ContextEnv.(getenv) l queue_invalid = [LE LogWrite P0 Ob~1; LE LogRead P0 tt] *)
  (* | None => False *)
  (* end. *)
  Proof.
    intros Hvalid.
    unfold interp_rule.
    (* Time simpl; rewrite Hvalid; simpl; eexists; split; reflexivity. *)
    apply (wp_action_correct (rule_name_t := rule_name_t)).
    Time simpl; rewrite Hvalid; simpl; eexists; split; reflexivity.
  Qed.

  Ltac autorew :=
    repeat match goal with
           | [ H: ?a = ?a' |- context[match ?b with _ => _ end] ] =>
             unify a b; replace b with a' by assumption
           (* The variant below isn't enough, because primitive projections are weird *)
           (* | [ H: ?a = _ |- _ ] => *)
           (*   match goal with (* Merging the two matches together results in a 20x slowdown *) *)
           (*   | [  |- context[a] ] => rewrite !H *)
           (*   end *)
           end.

  (* FIXME *)
  Arguments may_read0 /.
  Arguments may_read1 /.
  Arguments may_write0 /.
  Arguments may_write1 /.
  Arguments vect_cons: simpl never.

  Lemma doF_correct :
    forall l,
      let l_input_buffer := ContextEnv.(getenv) l input_buffer in
      let l_queue_invalid := ContextEnv.(getenv) l queue_invalid in
      let l_queue_data := ContextEnv.(getenv) l queue_data in
      l_input_buffer.(lwrite0) = None ->
      l_input_buffer.(lwrite1) = None ->
      l_input_buffer.(lread1) = false ->
      l_queue_data.(lread1) = false ->
      l_queue_data.(lwrite0) = None ->
      l_queue_data.(lwrite1) = None ->
      l_queue_invalid.(lwrite1) = None ->
      l_queue_invalid.(lwrite0) = Some Ob~1 ->
      (* ContextEnv.(getenv) r queue_data = (sigma F) (ContextEnv.(getenv) r output_buffer) -> *)
      exists l',
        interp_rule r sigma l (rls doF) = Some l'.
  Proof.
    intros.
    unfold interp_rule.
    (* rewrite (interp_action_cps_correct_rev (rule_name_t := rule_name_t)). *)
    (* simpl. *)
    apply (wp_action_correct (rule_name_t := rule_name_t)).
    Time simpl.
    Time autorew.
    simpl.
    eexists; split; reflexivity.
  Qed.


Definition external (r: rule_name_t) := false.

Definition circuits :=
  compile_scheduler rules external pipeline.

Definition circuits_result sigma :=
  interp_circuits (ContextEnv.(create) r) sigma circuits.

Definition cpp_extfuns := "class extfuns {
public:
  static bits<32> stream(bits<32> lfsr) {
    return lfsr + bits<32>{1};
  }

  static bits<32> f(bits<32> x) {
    return ~(x << bits<32>{2}) - bits<32>{1};
  }

  static bits<32> g(bits<32> x) {
    return bits<32>{5} + ((x + bits<32>{1}) >> bits<32>{1});
  }
};".

Definition ext_fn_names fn :=
  match fn with
  | Stream => "stream"
  | F => "f"
  | G => "g"
  end.

Definition package :=
  {| ip_koika := {| koika_reg_types := R;
                   koika_reg_init reg := r reg;
                   koika_ext_fn_types := Sigma;
                   koika_rules := rules;
                   koika_rule_external := external;
                   koika_scheduler := pipeline;
                   koika_module_name := "pipeline" |};

     ip_sim := {| sp_ext_fn_specs fn :=
                   {| efs_name := ext_fn_names fn;
                      efs_method := false |};
                 sp_prelude := Some cpp_extfuns |};

     ip_verilog := {| vp_ext_fn_specs fn :=
                       {| efr_name := ext_fn_names fn;
                          efr_internal := true |} |} |}.

Definition prog := Interop.Backends.register package.
Extraction "pipeline.ml" prog.
