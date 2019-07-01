(* Copyright (c) 2019 Thomas Bourgeat *)
Require Import GeneralizationSimpler.
Require Import Coq.Lists.List.
Import Datatypes.
Require Import Coq.Arith.Compare_dec.

Import ListNotations.


Definition add_rule (av:ActionValue) (system: list(option value* option value)*scheduler) : list(option value* option value) * scheduler :=
  (app (fst system) [(Some bottomValue, None)], try_rule (List.length (fst system)) av (snd system) (snd system)).

Definition add_method (av:value -> ActionValue) (args: option value) (system: list(option value* option value)*scheduler) : list(option value* option value) * scheduler :=
  (app (fst system) [(args, None)], try_method (List.length (fst system)) av (snd system) (snd system)).

Fixpoint partial_perform_update' (partial_regs_content : (list value)) (s: list sort_write) : list value :=
  match s with
  | cons (write_0 reg val) t =>
    match replace_nth reg partial_regs_content val
    with
    | None => partial_perform_update' partial_regs_content t
    | Some newregs => partial_perform_update' newregs t
    end
  | cons ( write_past reg val) t =>
    match replace_nth reg partial_regs_content val
    with
    | None => partial_perform_update' partial_regs_content t
    | Some newregs => partial_perform_update' newregs t
    end
  | cons ( write_1 reg val) t =>
    match replace_nth reg partial_regs_content val
    with
    | None => partial_perform_update' partial_regs_content t
    | Some newregs => partial_perform_update' newregs t
    end
  | cons (write_past_1 reg val) t =>
    match replace_nth reg partial_regs_content val
    with
    | None => partial_perform_update' partial_regs_content t
    | Some newregs => partial_perform_update' newregs t
    end
  | nil => partial_regs_content
  end.

Definition partial_perform_update (partial_regs_content : (list value)) (s: list sort_write) : list value :=
  partial_perform_update' partial_regs_content (rev s).

Definition perform_update (regs_content : list (list value)) (s: list (ReadLog*WriteLog)) :=
  List.map (fun (x: list value * (ReadLog*WriteLog)) => let (regs,log) := x in
                  partial_perform_update regs (snd log)) (combine regs_content s).


(* Call tried and avs are related: the nat correspond to the argument to do *)
Fixpoint one_rule_at_a_time (regs_content: list (list value)) (avs: list (nat *(value -> ActionValue))) (call_tried:list (option value *option value))
  (* (logs: list(ReadLog*WriteLog)) *): (list (list (value)) * list (option value * option value)) :=
  match avs with
  | nil => (regs_content,call_tried)
  | cons (which_args,av) t =>
    match nth_error call_tried which_args with (* LABEL0 *)
    | Some (Some arg,None) =>
      match atomic_av regs_content (blank_state (* (map (fun x : list sort_read * WriteLog => (filter_read (fst x), snd x)) logs) *) regs_content call_tried) (av arg) with
      | None => one_rule_at_a_time regs_content t call_tried (* logs *) (* This is never taken in the theorem! *)
      | Some (rv, s) => let newstate := (perform_update regs_content (Reg s)) in
                       match replace_nth which_args call_tried (Some arg, Some rv) with
                       | None => one_rule_at_a_time regs_content t call_tried (* logs *) (* Impossible because of LABEL0 (-6lines) *)
                       | Some nxt => one_rule_at_a_time newstate t nxt (* logs *)
                       end
      end
    | _ => one_rule_at_a_time regs_content t call_tried (*  logs *)
    end
  end.



Lemma permutation_combines : forall logs x x0, (map (fun x : ReadLog * WriteLog * (ReadLog * WriteLog) => let (log, new) := x in (fst new ++ fst log, snd new ++ snd log))
   (combine
      (map (fun x : ReadLog * WriteLog * (ReadLog * WriteLog) => let (log, new) := x in (fst new ++ fst log, snd new ++ snd log))
         (combine logs x)) x0) =
 map (fun x : ReadLog * WriteLog * (ReadLog * WriteLog) => let (log, new) := x in (fst new ++ fst log, snd new ++ snd log))
   (combine logs
      (map (fun x1 : ReadLog * WriteLog * (ReadLog * WriteLog) => let (log, new) := x1 in (fst new ++ fst log, snd new ++ snd log))
           (combine x x0)))).
    induction logs, x, x0;simpl; try reflexivity.
    rewrite app_assoc.
    rewrite app_assoc.
    apply f_equal.
    apply IHlogs.
Qed.





Lemma replace_in_right_size : forall {A} (pastlog: list (A)) n a b,
    nth_error pastlog n = Some a ->
    match replace_nth n pastlog b with
    | Some l => nth_error l n = Some b
    | None => False
    end.
  intros.
  generalize dependent n.
  induction pastlog, n;intros.
  -
    simpl in *.
    inversion H.
  -
    simpl in *.
    inversion H.
  -
    simpl in *.
    reflexivity.
  -
    simpl in *.
    specialize (IHpastlog n H).
    destruct (replace_nth n pastlog b) eqn:replaceByB.
    apply IHpastlog.
    apply IHpastlog.
Qed.


Lemma replace_in_right_size_none : forall {A} (pastlog: list (A)) n b,
    nth_error pastlog n = None ->
    match replace_nth n pastlog b with
    | Some l => False
    | None => True
    end.
  intros.
  generalize dependent n.
  induction pastlog; intros.
  -
    destruct n;
    simpl in *; trivial.
  -
    simpl in *.
    destruct n; simpl in *.
    inversion H.
    specialize (IHpastlog _ H).
    destruct (replace_nth n pastlog b) eqn:?.
    contradiction.
    trivial.
Qed.

Lemma replace_in : forall {A} (pastlog: list (A)) n b,
    match replace_nth n pastlog b with
    | Some l => nth_error l n = Some b
    | None => True
    end.
  intros.
  generalize dependent n.
  induction pastlog, n;intros.
  -
    simpl in *.
    trivial.
  -
    simpl in *.
    trivial.
  -
    simpl in *.
    reflexivity.
  -
    simpl in *.
    specialize (IHpastlog n).
    destruct (replace_nth n pastlog b) eqn:replaceByB.
    apply IHpastlog.
    apply IHpastlog.
Qed.


Lemma filter_projector {A} : forall l (f: A->bool),
    filter f (filter f l) = filter f l.
Proof.
induction l.
-
  simpl.
  intro.
  reflexivity.
-
  intros.
  simpl.
  destruct (f a) eqn:?.
  simpl.
  rewrite Heqb.
  f_equal.
  apply IHl.
  apply IHl.
Qed.


Lemma filter_app_morphism {A} : forall l l' (f: A->bool),
    filter f (l ++ l') = filter f l ++ filter f l'.
Proof.
induction l.
-
  simpl.
  intro.
  reflexivity.
-
  intros.
  simpl.
  destruct (f a) eqn:?.
  simpl.
  f_equal.
  apply IHl.
  apply IHl.
Qed.


Definition remove_unseen  (call_tried: list (option value * option value)) := filter
                                 (fun (x:nat*(value -> ActionValue)) => let (pos,avf) := x in
                                        match nth_error call_tried pos with
                                        | Some (Some _, Some _) =>true
                                        | _ => false
                                        end).

Lemma retire_write_projector:
      forall a : WriteLog,
        map
          (fun x : sort_write =>
             match x with
             | write_0 n v | write_past n v => write_past n v
             | write_1 n v | write_past_1 n v => write_past_1 n v
             end) ( a) =
        map
          (fun x : sort_write =>
             match x with
             | write_0 n v | write_past n v => write_past n v
             | write_1 n v | write_past_1 n v => write_past_1 n v
             end)
          (map
             (fun x : sort_write =>
                match x with
                | write_0 n v | write_past n v => write_past n v
                | write_1 n v | write_past_1 n v => write_past_1 n v
                end) ( a)).
Proof.
  induction a.
  simpl in *.
  reflexivity.
  simpl.
  f_equal.
  destruct a; simpl; reflexivity.
  assumption.
Qed.

Lemma retire_write_projector':
      forall a : WriteLog,
        retire_write a =
retire_write (retire_write a).
Proof.
  unfold retire_write.
  intro.
  rewrite <- retire_write_projector.
  reflexivity.
Qed.

Lemma retire_projector :  forall logs, (retire (retire logs) = retire logs).
  induction logs.
  -
    simpl.
    reflexivity.
  -
    simpl.
    f_equal.
    2: apply IHlogs.
    f_equal.
    rewrite <- retire_write_projector.
    reflexivity.
Qed.

Lemma atomic_av_preserve_length :
  forall a regs_content s ,
    match atomic_av regs_content s a with
    | Some (v0, ns) => length (Reg ns) = length (Reg s)
    | None => True
    end.
  induction a;simpl;intros.
  -
    destruct atomic_av eqn:?.
    destruct p.
    match goal with
    | [  |- match ?g with _=>_ end ] =>  destruct g eqn:?
    end.
    destruct p.
    specialize (H v regs_content s0).
    specialize (IHa regs_content s).
    rewrite Heqo0 in *.
    rewrite Heqo in *.
    firstorder.
    all:trivial.
  -
    specialize (IHa1 regs_content s).
    destruct atomic_av eqn:?.
    destruct p.
    destruct v.
    trivial.
    destruct b.
    specialize (IHa2 regs_content s0 ).
    destruct (atomic_av regs_content s0 a2).
    destruct p. firstorder.
    all: firstorder.
  -
    Ltac destruct_l l := match l with
                         | match ?g with _ => _ end =>
                           destruct_l g
                         | ?f => destruct f eqn:?
                         end.
    repeat (match goal with
    | [  |- ?g ] => destruct_l g
    end).
    all:trivial.
    simpl.
    pose proof (replace_nth_length (let (r, w) := p in (read n0 :: r, w)) n (Reg s)).
    rewrite Heqo1 in H.
    exact H.
  -
    repeat (match goal with
    | [  |- ?g ] => destruct_l g
    end).
    all:trivial.
    simpl.
    pose proof (replace_nth_length (let (r, w) := p in (forward n0 :: r, w)) n (Reg s)).
    rewrite Heqo2  in H.
    exact H.
  -
    repeat (match goal with
    | [  |- ?g ] => destruct_l g
    end).
    all:trivial.
    simpl.
    pose proof (replace_nth_length (let (r, w) := p in (r,write_0 n0 v :: w)) n (Reg s)).
    rewrite Heqo0 in H.
    exact H.
  -
    repeat (match goal with
    | [  |- ?g ] => destruct_l g
    end).
    all:trivial.
    simpl.
    pose proof (replace_nth_length (let (r, w) := p in (r,write_1 n0 v :: w)) n (Reg s)).
    rewrite Heqo0 in H.
    exact H.
  -
        repeat (match goal with
    | [  |- ?g ] => destruct_l g
    end).
    all:trivial.
    simpl.
    specialize (IHa1 regs_content s).
    specialize (IHa2 regs_content s0).
    rewrite Heqo in *.
    rewrite Heqo0 in *.
    firstorder.
  -
    trivial.
  - trivial.
Qed.

Require Import Omega.
Lemma prim_caract_nth_replace {A} : forall call_tried n n0 (a:A),
    match replace_nth n call_tried a with
    | None => True
    | Some l0 => if n =? n0
                then
                  nth_error l0 n0 = Some a
                else
                  nth_error l0 n0 = nth_error call_tried n0
    end.
  induction call_tried.
  -
    intros.
    simpl.
    destruct n; simpl; trivial.
  -
    intros.
    simpl.
    destruct n eqn:?; simpl.
    destruct n0 eqn:?.
    simpl.
    reflexivity.
    simpl.
    reflexivity.
    destruct ( replace_nth n1 call_tried a0) eqn:?.
    destruct n0 eqn:?.
    simpl.
    reflexivity.
    specialize (IHcall_tried n1 n2 a0).
    rewrite Heqo in IHcall_tried.
    simpl.
    exact IHcall_tried.
    trivial.
Qed.


Lemma caract_nth_replace : forall call_tried n n0 (v:value) (s:value),
    match replace_nth n call_tried (Some v, Some s) with
    | None => True
    | Some l0 => if n =? n0
                then
                  nth_error l0 n0 = Some (Some v, Some s)
                else
                  nth_error l0 n0 = nth_error call_tried n0
    end.
  intros.
  apply (prim_caract_nth_replace call_tried n n0 (Some v, Some s)).
Qed.

Lemma remove_unseen_works :
  forall dyn l0 call_tried n a v s ,
    replace_nth n call_tried (Some v, Some s) = Some l0 ->
    (remove_unseen l0
                   ((remove_unseen
                      call_tried
                      dyn) ++ [(n, a)])) =
     (remove_unseen call_tried dyn) ++ [(n, a)].
  induction dyn; simpl; intros.
  -
    intros.
    specialize (replace_in call_tried n (Some v, Some s)).
    intro.
    rewrite H in H0.
    rewrite H0.
    trivial.
  -
    destruct a.
    destruct (nth_error call_tried n0) eqn:?.
    destruct p ; destruct o; destruct o0.
    simpl.
    destruct (nth_error l0 n0) eqn:?.
    destruct p.
    destruct o; destruct o0;
      f_equal;  try apply (IHdyn l0 call_tried n a0 v s H);
          pose proof (caract_nth_replace);
    specialize (H0 call_tried n n0 v s);
    try rewrite H in H0;
    try destruct (n =? n0);
    try rewrite Heqo0 in H0;
    try rewrite Heqo in H0;
    inversion H0.
    pose proof (caract_nth_replace);
    specialize (H0 call_tried n n0 v s).
    rewrite H in H0.
    destruct (n =? n0).
    rewrite Heqo0 in H0.
    inversion H0.
    rewrite Heqo0 in H0;
      try rewrite Heqo in H0;
      inversion H0.
    apply (IHdyn l0 call_tried n a0 v s H).
    apply (IHdyn l0 call_tried n a0 v s H).
    apply (IHdyn l0 call_tried n a0 v s H).
    apply (IHdyn l0 call_tried n a0 v s H).
Qed.


Definition log_append logs x :=    map (fun x : ReadLog * WriteLog * (ReadLog * WriteLog) => let (log, new) := x in (fst new ++ fst log, snd new ++ snd log))
                                       (combine logs x).

Lemma permutation_append : forall logs x x0, log_append logs (log_append x x0) = log_append (log_append logs x) x0.
  intros.
  unfold log_append.
  rewrite <- permutation_combines.
  reflexivity.
Qed.


Lemma chain_oraat : forall l l' call_tried regs_content,
    
    one_rule_at_a_time regs_content (l ++ l') call_tried =
    (let (newreg,newmet) := one_rule_at_a_time regs_content l call_tried in
    one_rule_at_a_time newreg l' newmet).
induction l; induction l'; simpl.
-
  reflexivity.
-
  intros.
 destruct a.
 destruct (nth_error call_tried n) eqn:?.
 destruct p.
 destruct o. destruct o0.
 reflexivity.
 destruct ( atomic_av regs_content (blank_state regs_content call_tried)
                      (a v)) eqn:?.

  destruct p.
  destruct ( replace_nth n call_tried (Some v, Some v0)) eqn:?.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
-
  intros.
  destruct a.
  destruct (nth_error call_tried n) eqn:?.
  destruct p.
  destruct o. destruct o0.
  rewrite <- (app_nil_end l).
   destruct (    one_rule_at_a_time regs_content l call_tried) eqn:?.
 reflexivity.

  destruct (    atomic_av regs_content (blank_state regs_content call_tried)
      (a v)) eqn:?.
  destruct p.
  destruct ( replace_nth n call_tried (Some v, Some v0)) eqn:?.
  rewrite <- (app_nil_end l).
  destruct (one_rule_at_a_time (perform_update regs_content (Reg s)) l l0).
  reflexivity.
    rewrite <- (app_nil_end l).
   destruct (    one_rule_at_a_time regs_content l call_tried) eqn:?.
 reflexivity.
  rewrite <- (app_nil_end l).
   destruct (    one_rule_at_a_time regs_content l call_tried) eqn:?.
 reflexivity.
  rewrite <- (app_nil_end l).
   destruct (    one_rule_at_a_time regs_content l call_tried) eqn:?.
 reflexivity.
  rewrite <- (app_nil_end l).
   destruct (    one_rule_at_a_time regs_content l call_tried) eqn:?.
 reflexivity.
-  
  intros.
  destruct a0.
  destruct a.
  destruct (nth_error call_tried n0) eqn:?.
  destruct p.
  destruct o . destruct o0.
  destruct (    one_rule_at_a_time regs_content l call_tried) eqn:?.
  destruct (nth_error l1 n) eqn:?.
  destruct p. destruct o . destruct o0.
  specialize (IHl ((n, a0) :: l') call_tried regs_content).
  rewrite Heqp in IHl.
  rewrite IHl.
  simpl.
  rewrite Heqo0.
  reflexivity.

  destruct (atomic_av l0 (blank_state l0 l1) (a0 v1)) eqn:?.
  destruct p.
  destruct (replace_nth n l1 (Some v1, Some v2)) eqn:?.
  specialize (IHl ((n, a0) :: l') call_tried regs_content).
  rewrite Heqp in IHl.
  rewrite IHl.
  simpl.
  rewrite Heqo0.
  rewrite Heqo1.
  rewrite Heqo2.
  reflexivity.

  specialize (IHl ((n, a0) :: l') call_tried regs_content).
  rewrite Heqp in IHl.
  rewrite IHl.
  simpl.
  rewrite Heqo0.
  rewrite Heqo1.
  rewrite Heqo2.
  reflexivity.

  specialize (IHl ((n, a0) :: l') call_tried regs_content).
  rewrite Heqp in IHl.
  rewrite IHl.
  simpl.
  rewrite Heqo0.
  rewrite Heqo1.
  reflexivity.

  specialize (IHl ((n, a0) :: l') call_tried regs_content).
  rewrite Heqp in IHl.
  rewrite IHl.
  simpl.
  rewrite Heqo0.
  reflexivity.

  specialize (IHl ((n, a0) :: l') call_tried regs_content).
  rewrite Heqp in IHl.
  rewrite IHl.
  simpl.
  rewrite Heqo0.
  reflexivity.

  destruct (atomic_av regs_content (blank_state regs_content call_tried) (a v)) eqn:?.
  destruct p .
  destruct (replace_nth n0 call_tried (Some v, Some v0)) eqn:?.
  destruct ( one_rule_at_a_time (perform_update regs_content (Reg s)) l l0) eqn:?.
  destruct (nth_error l2 n) eqn:?.
  destruct p.
  destruct o.
  destruct o0.

  specialize (IHl ((n, a0) :: l') l0 (perform_update regs_content (Reg s))).
  rewrite Heqp in IHl.
  rewrite IHl.
  simpl.
  rewrite Heqo2.
  reflexivity.

  specialize (IHl ((n, a0) :: l') l0 (perform_update regs_content (Reg s))).
  rewrite Heqp in IHl.
  rewrite IHl.
  simpl.
  rewrite Heqo2.
  reflexivity.

  specialize (IHl ((n, a0) :: l') l0 (perform_update regs_content (Reg s))).
  rewrite Heqp in IHl.
  rewrite IHl.
  simpl.
  rewrite Heqo2.
  reflexivity.

  specialize (IHl ((n, a0) :: l') l0 (perform_update regs_content (Reg s))).
  rewrite Heqp in IHl.
  rewrite IHl.
  simpl.
  rewrite Heqo2.
  reflexivity.

  destruct (   one_rule_at_a_time regs_content l call_tried) eqn:?.
  specialize (IHl ((n, a0) :: l') call_tried  regs_content).
  rewrite Heqp in IHl.
  rewrite IHl.
  simpl.
  reflexivity.

  destruct (   one_rule_at_a_time regs_content l call_tried) eqn:?.
  specialize (IHl ((n, a0) :: l') call_tried  regs_content).
  rewrite Heqp in IHl.
  rewrite IHl.
  simpl.
  reflexivity.

  destruct (   one_rule_at_a_time regs_content l call_tried) eqn:?.
  specialize (IHl ((n, a0) :: l') call_tried  regs_content).
  rewrite Heqp in IHl.
  rewrite IHl.
  simpl.
  reflexivity.

  destruct (   one_rule_at_a_time regs_content l call_tried) eqn:?.
  specialize (IHl ((n, a0) :: l') call_tried  regs_content).
  rewrite Heqp in IHl.
  rewrite IHl.
  simpl.
  reflexivity.
Qed.


Lemma replacing_log_append_is_appending_read : forall n pastlog x r w l0,
    nth_error pastlog n = Some (r,w) ->
    replace_nth n pastlog (x :: r, w) = Some l0 ->
    exists newl, l0 = log_append pastlog newl /\ length newl = length pastlog.
  intros.
  generalize dependent pastlog.
  generalize dependent x.
  generalize dependent r.
  generalize dependent w.
  generalize dependent l0.
  (* generalize dependent n. *)
  induction n,pastlog.
  -
    intros. simpl in *.
    inversion H.
  -
    simpl in *.
    intros.
    eexists.
    inversion H.
    inversion H0.
    instantiate (1:=_::_).
    simpl.
    unfold log_append.
    simpl.
    instantiate (3:= (_,_)).
    simpl.
    split.
    f_equal.
    simpl.
    f_equal.
    instantiate (1:= cons _ nil).
    rewrite <-app_comm_cons.
    simpl.
    f_equal.
    instantiate (1:= nil).
    simpl;reflexivity.
    instantiate (1:= (repeat ([],[]) (length pastlog))).
    {
      clear H H0 H2 H3.
      induction pastlog.
      cbv.
      reflexivity.
      simpl.
      rewrite <- surjective_pairing.
      f_equal.
      apply IHpastlog.
    }
    rewrite repeat_length.
    reflexivity.
  -
    simpl.
    intros.
    inversion H0.
  -
    simpl.
    intros.
    destruct (replace_nth n pastlog (x :: r, w)) eqn:?.
    +
      inversion H0.
      specialize (IHn l w r x pastlog H Heqo).
      destruct IHn.
      eexists.
      split.
      instantiate (1:= _::_).
      unfold log_append.
      simpl.
      instantiate(2:= ([],[])).
      simpl.
      rewrite <- surjective_pairing.
      f_equal.
      destruct H1.
      rewrite e.
      unfold log_append.
      f_equal.
      simpl.
      destruct H1.
      rewrite H3.
      reflexivity.
    +
      inversion H0.
Qed.

Lemma replacing_log_append_is_appending_write : forall n pastlog x r w l0,
    nth_error pastlog n = Some (r,w) ->
    replace_nth n pastlog (r, x:: w) = Some l0 ->
    exists newl, l0 = log_append pastlog newl /\ length newl = length pastlog.
  intros.
  generalize dependent pastlog.
  generalize dependent x.
  generalize dependent r.
  generalize dependent w.
  generalize dependent l0.
  (* generalize dependent n. *)
  induction n,pastlog.
  -
    intros. simpl in *.
    inversion H.
  -
    simpl in *.
    intros.
    eexists.
    split.
    inversion H.
    inversion H0.
    instantiate (1:=_::_).
    simpl.
    unfold log_append.
    simpl.
    f_equal.
    instantiate (1:= (_,_)).
    simpl.
    f_equal.
    instantiate (1:= nil).
    simpl.
    reflexivity.
    instantiate (1:= cons _ nil).
    simpl;reflexivity.
    instantiate (1:= (repeat ([],[]) (length pastlog))).
    {
      clear H H0 H2 H3.
      induction pastlog.
      cbv.
      reflexivity.
      simpl.
      rewrite <- surjective_pairing.
      f_equal.
      apply IHpastlog.
    }
    simpl.
    rewrite repeat_length.
    reflexivity.
  -
    simpl.
    intros.
    inversion H0.
  -
    simpl.
    intros.
    destruct (replace_nth n pastlog (r, x::w)) eqn:?.
    +
      inversion H0.
      specialize (IHn l w r x pastlog H Heqo).
      destruct IHn.
      eexists.
      split.
      instantiate (1:= _::_).
      unfold log_append.
      simpl.
      instantiate(2:= ([],[])).
      simpl.
      rewrite <- surjective_pairing.
      f_equal.
      destruct H1.
      rewrite e.
      unfold log_append.
      f_equal.
      simpl.
      destruct H1.
      rewrite H3.
      reflexivity.
    +
      inversion H0.
Qed.


Lemma expand_state :   (forall s, s= {| Reg := Reg s; Met := Met s; dynamicOrder := dynamicOrder s |}).
    destruct s; reflexivity.
Qed.

Ltac rewriteall A B :=
    match type of A with
    | ?a = ?b => (* idtac "rewrite" a "in " b "within " B ; *) rewrite A in B
    | ?A1 /\ ?A2 => let name1 := fresh A in
                  let name2 := fresh A in
                  destruct A as [name1 name2] ; rewriteall name1 B; rewriteall name2 B
    | ?g => idtac  (* idtac "skip" g *)
    end.

Lemma atomic_only_reg : forall a regs_content r c d s v,
    atomic_av regs_content {|Reg:= r; Met := c; dynamicOrder := d|} a = Some (v, s) ->
    Met s = c /\ dynamicOrder s = d.
induction a.
- intros.
  simpl in *.
  match goal with
  | [ H: match ?g with _=>_ end = _ |- _ ] =>  destruct g eqn:?
  end.
  destruct p.
  rewrite (expand_state s0) in *.
  specialize (IHa _ _ _ _ _ _ Heqo).
  specialize (H _ _ _ _ _ _ _ H0).
  simpl in *.
  rewriteall IHa H.
  exact H.
  inversion H0.
-
  intros.
  simpl in *.
  repeat match goal with
  | [ H: match ?g with _=>_ end = _ |- _ ] =>  destruct g eqn:?
         end; try congruence.
  rewrite (expand_state s0) in *.
  specialize (IHa1 _ _ _ _ _ _ Heqo).
  specialize (IHa2 _ _ _ _ _ _  H).
  simpl in *.
  rewriteall IHa1 IHa2.
  exact IHa2.
  rewrite (expand_state s0) in *.
  specialize (IHa1 _ _ _ _ _ _ Heqo).
  inversion H.
  exact IHa1.
-
  intros.
  simpl in *.
  repeat match goal with
  | [ H: match ?g with _=>_ end = _ |- _ ] =>  destruct g eqn:?
         end; try congruence.
  inversion H.
  simpl in *.
  firstorder.
-
  intros;
  simpl in *;
  repeat match goal with
  | [ H: match ?g with _=>_ end = _ |- _ ] =>  destruct g eqn:?
         end; try congruence;
  inversion H;
  simpl in *;
  firstorder.
-
  intros;
  simpl in *;
  repeat match goal with
  | [ H: match ?g with _=>_ end = _ |- _ ] =>  destruct g eqn:?
         end; try congruence;
  inversion H;
  simpl in *;
  firstorder.
-
  intros;
  simpl in *;
  repeat match goal with
  | [ H: match ?g with _=>_ end = _ |- _ ] =>  destruct g eqn:?
         end; try congruence;
  inversion H;
  simpl in *;
  firstorder.
-
  intros.
  simpl in *.
  repeat match goal with
  | [ H: match ?g with _=>_ end = _ |- _ ] =>  destruct g eqn:?
         end; try congruence.
  rewrite (expand_state s0) in *.
  specialize (IHa1 _ _ _ _ _ _ Heqo).
  specialize (IHa2 _ _ _ _ _ _ Heqo0).
  inversion H.
  simpl in *.
  rewriteall IHa1 IHa2.
  rewrite H2 in IHa2.
  exact IHa2.
-
  intros.
  simpl in *.
  inversion H.
-
  intros.
  simpl in *.
  inversion H.
  simpl.
  firstorder.
Qed.

Lemma nth_error_append :
     (forall n l0 l1 p, nth_error (log_append l0 l1) n = Some p -> exists (l0n:ReadLog*WriteLog) (l1n:ReadLog*WriteLog), nth_error l1 n = Some l1n /\ nth_error l0 n = Some l0n /\ p = (fun rw1 rw2 =>
                                                                                                                                      let (r1,w1) := (rw1:ReadLog*WriteLog) in
                                                                                                                                      let (r2,w2) := (rw2:ReadLog*WriteLog) in
                                                                                                                                      (r1++r2, w1++w2)
                                                                                                                                   ) l1n l0n ).
  induction n.
  -
    intros.
    simpl.
    unfold log_append in H.
    rewrite nth_error_nth_map in H.
    destruct (combine l0 l1) eqn:combine_eq.
    unfold nth_map in H.
    +
       cbv in H;
      inversion H.
    +
      unfold nth_map in H.
      simpl in H.
      inversion H.
      destruct p0.
        exists p0.
        exists p1.
        destruct l1, l0; simpl in combine_eq;try congruence.
        inversion combine_eq.
        repeat split; trivial.
        destruct p1, p0.
        simpl.
        reflexivity.
  -
    intros.
    simpl.
    destruct p.
    unfold log_append in H.
    rewrite nth_error_nth_map in H.
    destruct (combine l0 l1) eqn:combine_eq.
    unfold nth_map in H.
    destruct n.
    {
      simpl in H.
      inversion H.
    }
    {
      simpl in H.
      inversion H.
    }
    {
      destruct l0, l1.
      simpl in combine_eq.
      inversion combine_eq.
      simpl in combine_eq.
      inversion combine_eq.
      simpl in combine_eq.
      inversion combine_eq.
      specialize (IHn l0 l1).
      rewrite <- nth_error_nth_map in H.
      simpl in H.
      simpl in combine_eq.
      inversion combine_eq.
      rewrite <- H2 in H.
      fold (log_append l0 l1) in H.
      specialize (IHn (l,l2) H).
      apply IHn.
    }
Qed.

Definition compute_log_append {A B} (n:nat) x lpastlog : list (list A * list B) :=
  repeat ([],[]) n ++ ([x],[]):: (repeat ([],[]) (lpastlog - S n)).

Definition compute_log_append_write {A B} (n:nat) x lpastlog : list (list A * list B) :=
  repeat ([],[]) n ++ ([],[x]):: (repeat ([],[]) (lpastlog - S n)).

Lemma log_append_id:
  forall pastlog : list (ReadLog * WriteLog),
    pastlog =
    log_append pastlog (repeat ([], []) (length pastlog - 0)).
Proof.
  induction pastlog.
  +
    cbv; reflexivity.
  +
    simpl.
    unfold log_append.
    simpl.
    fold (log_append  pastlog (repeat ([], []) (length pastlog))).
    f_equal.
    apply surjective_pairing.
    rewrite Nat.sub_0_r in IHpastlog.
    assumption.
Qed.

Lemma log_append_id_l:
  forall pastlog : list (ReadLog * WriteLog),
    pastlog =
    log_append (repeat ([], []) (length pastlog - 0)) pastlog.
Proof.
  induction pastlog.
  +
    cbv; reflexivity.
  +
    simpl.
    unfold log_append.
    simpl.
    fold (log_append  pastlog (repeat ([], []) (length pastlog))).
    f_equal.
    rewrite ?app_nil_r.
    apply surjective_pairing.
    rewrite Nat.sub_0_r in IHpastlog.
    assumption.
Qed.


Lemma log_append_id':
  forall pastlog : list (ReadLog * WriteLog),
    pastlog =
    log_append pastlog (repeat ([], []) (length pastlog)).
Proof.
  intros.
  assert ((repeat ([], []) (length pastlog)) = (repeat (([]:ReadLog), ([]:WriteLog)) (length pastlog - 0))).
  rewrite Nat.sub_0_r.
  reflexivity.
  rewrite H.
  rewrite <- log_append_id.
  reflexivity.
Qed.


Lemma log_append_id'_l:
  forall pastlog : list (ReadLog * WriteLog),
    pastlog =
    log_append (repeat ([], []) (length pastlog)) pastlog.
Proof.
  intros.
  assert ((repeat ([], []) (length pastlog)) = (repeat (([]:ReadLog), ([]:WriteLog)) (length pastlog - 0))).
  rewrite Nat.sub_0_r.
  reflexivity.
  rewrite H.
  rewrite <- log_append_id_l.
  reflexivity.
Qed.

Lemma replacing_log_append_is_appending_read' : forall n pastlog x r w,
    nth_error pastlog n = Some (r,w) ->
    replace_nth n pastlog (x :: r, w) = Some (log_append pastlog (compute_log_append n x (length pastlog))).
Proof.
  (* generalize dependent n. *)
  induction n; simpl in *; intros; destruct pastlog; try discriminate.
  -
    match goal with
    | [ H: Some _ = Some _ |- _ ] => inversion H; subst; clear H
    end.
    unfold log_append.
    simpl.
    fold (log_append pastlog (repeat ([],[]) (length pastlog - 0))).
    replace (log_append pastlog (repeat ([], []) (length pastlog -0  ))) with pastlog.
    reflexivity.
    apply log_append_id.
  -
    specialize (IHn _ x _ _ H).
    rewrite IHn.
    unfold log_append at 2. simpl.
    fold (log_append pastlog (repeat ([], []) n ++ ([x], []) :: repeat ([], []) (length pastlog - S n))).
    rewrite <- surjective_pairing.
    unfold compute_log_append.
    reflexivity.
Qed.

Lemma replacing_log_append_is_appending_write' : forall n pastlog x r w,
    nth_error pastlog n = Some (r,w) ->
    replace_nth n pastlog (r, x:: w) = Some (log_append pastlog (compute_log_append_write n x (length pastlog))).
Proof.
  (* generalize dependent n. *)
  induction n; simpl in *; intros; destruct pastlog; try discriminate.
  -
    match goal with
    | [ H: Some _ = Some _ |- _ ] => inversion H; subst; clear H
    end.
    unfold log_append.
    simpl.
    fold (log_append pastlog (repeat ([],[]) (length pastlog - 0))).
    replace (log_append pastlog (repeat ([], []) (length pastlog -0  ))) with pastlog.
    reflexivity.
    apply log_append_id.
  -
    specialize (IHn _ x _ _ H).
    rewrite IHn.
    unfold log_append at 2. simpl.
    fold (log_append pastlog (repeat ([], []) n ++ ([], [x]) :: repeat ([], []) (length pastlog - S n))).
    rewrite <- surjective_pairing.
    unfold compute_log_append.
    reflexivity.
Qed.

Lemma app_inj_left {A}:
      forall l l2 l4 :list A, l2 ++ l = l4 ++ l -> l2 = l4.
    Proof.
      induction l; simpl ; intros.
      -
        rewrite <- !app_nil_end in H.
        assumption.
      -
        change (a::l) with ([a]++l) in H.
        rewrite !app_assoc in H.
        apply IHl in H.
        apply app_inj_tail in H.
        firstorder.
Qed.

Lemma log_append_injR :
  forall l1 x y, length l1 = length x ->
            length x = length y ->
            log_append l1 x = log_append l1 y -> x = y.
  induction l1; simpl; intros.
  -
    unfold log_append in H1; simpl in H1.
    destruct x,y ; simpl in *; try discriminate; reflexivity.
  -
    destruct x,y ; simpl in *; try discriminate.
    unfold log_append in H1; simpl in H1.
    fold (log_append l1 x) in H1.
    fold (log_append l1 y) in H1.
    repeat match goal with
           | [ H: Some _ = Some _ |- _ ] => inversion H; subst; clear H
           | [ H: cons _ _ = cons _ _ |- _ ] => inversion H; subst; clear H
           | [ H: S _ = S _ |- _ ] => inversion H; subst; clear H
           end.
    f_equal.
    apply  app_inj_left in H3.
    apply  app_inj_left in H4.
    destruct p,p0;  simpl in *.
    congruence.
    firstorder.
Qed.


Lemma replace_consistent :
  forall l1 l0 n0 n read1r read1w read0r read0w elReplacenl1,
    length l0 = length l1 ->
    length elReplacenl1 = length l1 ->
    nth_error l1 n = Some (read1r, read1w) ->
    nth_error l0 n = Some (read0r,read0w) ->
    nth_error (log_append l0 l1) n = Some (read1r ++ read0r, read1w ++ read0w) ->
    replace_nth n l1
                ( n0::read1r, read1w) =
    Some (log_append l1 elReplacenl1) ->
    replace_nth n (log_append l0 l1)
                ( n0 :: read1r ++ read0r, read1w ++ read0w) =
    Some (log_append (log_append l0 l1)  elReplacenl1).
Proof.
  intros.
  rewrite replacing_log_append_is_appending_read' in H4 by assumption.
  rewrite replacing_log_append_is_appending_read' by assumption.
  repeat f_equal.
  inversion H4.
  unfold log_append.
  rewrite map_length.
  rewrite combine_length.
  rewrite H.
  rewrite Nat.min_id.
  apply (log_append_injR) in H6.
  assumption.
  unfold compute_log_append.
  assert (nth_error l1 n <> None).
  rewrite H1.
  congruence.
  pose proof (nth_error_Some l1 n).
  destruct H7.
  specialize (H7 H5).
  rewrite app_length.
  rewrite repeat_length.
  simpl.
  rewrite repeat_length.
  omega.
  unfold compute_log_append.
  assert (nth_error l1 n <> None).
  rewrite H1.
  congruence.
  pose proof (nth_error_Some l1 n).
  destruct H7.
  specialize (H7 H5).
  rewrite app_length.
  rewrite repeat_length.
  simpl.
  rewrite repeat_length.
  rewrite H0.
  omega.
Qed.


Lemma replace_consistent_write :
  forall l1 l0 n0 n read1r read1w read0r read0w elReplacenl1,
    length l0 = length l1 ->
    length elReplacenl1 = length l1 ->
    nth_error l1 n = Some (read1r, read1w) ->
    nth_error l0 n = Some (read0r,read0w) ->
    nth_error (log_append l0 l1) n = Some (read1r ++ read0r, read1w ++ read0w) ->
    replace_nth n l1
                ( read1r, n0::read1w) =
    Some (log_append l1 elReplacenl1) ->
    replace_nth n (log_append l0 l1)
                ( read1r ++ read0r, n0 :: read1w ++ read0w) =
    Some (log_append (log_append l0 l1)  elReplacenl1).
Proof.
  intros.
  rewrite replacing_log_append_is_appending_write' in H4 by assumption.
  rewrite replacing_log_append_is_appending_write' by assumption.
  repeat f_equal.
  inversion H4.
  unfold log_append.
  rewrite map_length.
  rewrite combine_length.
  rewrite H.
  rewrite Nat.min_id.
  apply (log_append_injR) in H6.
  assumption.
  unfold compute_log_append_write.
  assert (nth_error l1 n <> None).
  rewrite H1.
  congruence.
  pose proof (nth_error_Some l1 n).
  destruct H7.
  specialize (H7 H5).
  rewrite app_length.
  rewrite repeat_length.
  simpl.
  rewrite repeat_length.
  omega.
  unfold compute_log_append_write.
  assert (nth_error l1 n <> None).
  rewrite H1.
  congruence.
  pose proof (nth_error_Some l1 n).
  destruct H7.
  specialize (H7 H5).
  rewrite app_length.
  rewrite repeat_length.
  simpl.
  rewrite repeat_length.
  rewrite H0.
  omega.
Qed.

Lemma find_forward_morphism : forall read1w read0w n0,
    find_forward (read1w ++ read0w) n0 = orb (find_forward read1w n0) (find_forward read0w n0).
Proof.
  induction read1w.
  -
    simpl.
    reflexivity.
  -
    simpl.
    destruct a; try apply IHread1w.
    intros.
    rewrite (IHread1w read0w n0).
    rewrite Bool.orb_assoc.
    reflexivity.
Qed.

Lemma find_write_past_morphism : forall read1w read0w n0,
    find_write_past (read1w ++ read0w) n0 = orb (find_write_past read1w n0) (find_write_past read0w n0).
Proof.
  induction read1w.
  -
    simpl.
    reflexivity.
  -
    simpl.
    destruct a; try apply IHread1w.
    intros.
    rewrite (IHread1w read0w n0).
    rewrite Bool.orb_assoc.
    reflexivity.
Qed.


Lemma find_write1_morphism : forall read1w read0w n0,
    find_write1 (read1w ++ read0w) n0 = orb (find_write1 read1w n0) (find_write1 read0w n0).
Proof.
  induction read1w.
  -
    simpl.
    reflexivity.
  -
    simpl.
    destruct a; try apply IHread1w.
    intros.
    rewrite (IHread1w read0w n0).
    rewrite Bool.orb_assoc.
    reflexivity.
    intros.
    destruct (n0 =? n) eqn:?.
    simpl in *.
    reflexivity.
    simpl in *.
    apply IHread1w.
Qed.

Lemma find_write1_past_morphism : forall read1w read0w n0,
    find_write1_past (read1w ++ read0w) n0 = orb (find_write1_past read1w n0) (find_write1_past read0w n0).
Proof.
  induction read1w.
  -
    simpl.
    reflexivity.
  -
    
    simpl.
    intro.
    destruct a; try apply IHread1w.
    intros.
    destruct (n0 =? n). reflexivity.
    simpl.
    rewrite (IHread1w read0w n0).
    reflexivity.
Qed.



Lemma find_anywrite_morphism : forall read1w read0w n0,
    find_anywrite (read1w ++ read0w) n0 = orb (find_anywrite read1w n0) (find_anywrite read0w n0).
Proof.
  induction read1w.
  -
    simpl.
    reflexivity.
  -
    simpl.
    destruct a; try apply IHread1w.
    all: intros;
    destruct (n0 =? n) eqn:?;
    simpl in *;
    try reflexivity;
    simpl in *;
    apply IHread1w.
Qed.


Lemma extract_read0_in_replaced:
  forall (l : list value) (n0 n : nat) (v : value),
    n0 <> n -> forall l0 : list value, replace_nth n l v = Some l0 -> extract_read0 l0 n0 = extract_read0 l n0.
Proof.
  intros.
  unfold extract_read0.
  pose proof (prim_caract_nth_replace l n n0 v).
  rewrite  H0 in H1.
  destruct (n =? n0) eqn:?.
  apply beq_nat_true in  Heqb.
  congruence.
  congruence.
Qed.

Lemma extract_read1_in_replaced:
  forall read1w (l : list value) (n0 n : nat) (v : value),
    n0 <> n -> forall l0 : list value, replace_nth n l v = Some l0 -> extract_read1 l0 read1w n0 = extract_read1 l read1w n0.
Proof.
  induction read1w.
  - simpl. intros. apply (extract_read0_in_replaced l n0 n v); assumption.
  -
    simpl.
    intros.
    destruct a;
    destruct (n =? n1) eqn:?;destruct (n0 =? n1) eqn:?; try congruence;
    apply (IHread1w l n0 n v); assumption.
Qed.




Lemma read_when_not_updated' :
  forall read0w l n0,
    let read0w := retire_write read0w  in
    find_write_past read0w n0 = false ->
    find_write1 read0w n0 = false ->
    extract_read0 (partial_perform_update' l read0w) n0 = extract_read0 l n0.
  induction read0w.
  -
    intros.
    simpl in *.
    reflexivity.
  -
    intros.
    simpl in *.
    destruct a eqn:?;
      subst read0w0.
    {
      destruct (n0 =? n) eqn:?.
      apply beq_nat_true in Heqb.
      simpl in *.
      inversion H.
      simpl in H.
      apply beq_nat_false in  Heqb.
      destruct (replace_nth n l v) eqn:replacenth.
      rewrite IHread0w.
      apply (extract_read0_in_replaced l n0 n v); assumption.
      assumption.
      assumption.
      rewrite IHread0w.
      reflexivity.
      assumption.
      assumption.
    }
    {
      destruct (n0 =? n) eqn:?.
      apply beq_nat_true in Heqb.
      simpl in *.
      inversion H.
      simpl in H.
      apply beq_nat_false in  Heqb.
      destruct (replace_nth n l v) eqn:replacenth.
      rewrite IHread0w.
      apply (extract_read0_in_replaced l n0 n v); assumption.
      assumption.
      assumption.
      rewrite IHread0w.
      reflexivity.
      assumption.
      assumption.
    }
    {
      destruct (n0 =? n) eqn:?.
      apply beq_nat_true in Heqb.
      simpl in *.
      inversion H0.
      simpl in H0.
      apply beq_nat_false in  Heqb.
      destruct (replace_nth n l v) eqn:replacenth.
      rewrite IHread0w.
      apply (extract_read0_in_replaced l n0 n v); assumption.
      assumption.
      assumption.
      rewrite IHread0w.
      reflexivity.
      assumption.
      assumption.
    }
    {
      destruct (n0 =? n) eqn:?.
      apply beq_nat_true in Heqb.
      simpl in *.
      inversion H0.
      simpl in H0.
      apply beq_nat_false in  Heqb.
      destruct (replace_nth n l v) eqn:replacenth.
      rewrite IHread0w.
      apply (extract_read0_in_replaced l n0 n v); assumption.
      assumption.
      assumption.
      rewrite IHread0w.
      reflexivity.
      assumption.
      assumption.
    }
Qed.


Lemma rev_retire : forall read0w, (rev (retire_write read0w) = retire_write (rev read0w)).
  induction read0w; simpl;auto; destruct a.
  all: unfold retire_write.
  all: rewrite map_app.
  all: fold (retire_write (rev read0w)).
  all: simpl.
  all: fold (retire_write (read0w)).
  all: rewrite IHread0w.
  all: reflexivity.
Qed.


Lemma find_writepast_retire_rev:
    forall (read0w : WriteLog) (n0 : nat),
      find_write_past (retire_write read0w) n0 = false -> find_write_past (retire_write (rev read0w)) n0 = false.
Proof.
  induction read0w.
  -
    simpl in *.
    trivial.
  -
    simpl in *.
    destruct a.
    unfold retire_write;
    rewrite map_app;
    fold (retire_write (rev read0w));
    simpl;
    intros;
    rewrite find_write_past_morphism;
    fold (retire_write read0w) in H;
    simpl;
    destruct (n0 =? n) eqn:?;
    [simpl in *;
    inversion H |
    simpl in *;
    rewrite IHread0w;
    simpl; try reflexivity;     assumption].
    unfold retire_write;
    rewrite map_app;
    fold (retire_write (rev read0w));
    simpl;
    intros;
    rewrite find_write_past_morphism;
    fold (retire_write read0w) in H;
    simpl;
    destruct (n0 =? n) eqn:?;
    [simpl in *;
    inversion H |
    simpl in *;
    rewrite IHread0w;
    simpl; try reflexivity;     assumption].
    unfold retire_write;
    rewrite map_app;
    fold (retire_write (rev read0w));
    simpl;
    intros;
    rewrite find_write_past_morphism;
    fold (retire_write read0w) in H;
    simpl;
    destruct (n0 =? n) eqn:?;
    [simpl in *;
    inversion H |
    simpl in *;
    rewrite IHread0w;
    simpl; try reflexivity;     assumption].
    rewrite IHread0w.
    rewrite H.
    simpl. reflexivity.
    assumption.
    intros.
    unfold retire_write;
    rewrite map_app;
    fold (retire_write (rev read0w));
    simpl;
    intros;
    rewrite find_write_past_morphism;
    fold (retire_write read0w) in H;
    simpl.
    rewrite IHread0w.
    simpl. reflexivity.
    assumption.
Qed.


Lemma find_write1_retire_rev:
    forall (read0w : WriteLog) (n0 : nat),
      find_write1 (retire_write read0w) n0 = false -> find_write1 (retire_write (rev read0w)) n0 = false.
Proof.
  induction read0w.
  -
    simpl in *.
    trivial.
  -
    simpl in *.
    destruct a.
    intros;
    unfold retire_write;
    rewrite map_app;
    fold (retire_write (rev read0w));
    simpl;
    intros;
    rewrite find_write1_morphism;
    fold (retire_write read0w) in H;
    simpl;
    rewrite IHread0w;
    simpl; try reflexivity;try assumption.
        intros;
    unfold retire_write;
    rewrite map_app;
    fold (retire_write (rev read0w));
    simpl;
    intros;
    rewrite find_write1_morphism;
    fold (retire_write read0w) in H;
    simpl;
    rewrite IHread0w;
    simpl; try reflexivity;try assumption.
        unfold retire_write;
    rewrite map_app;
    fold (retire_write (rev read0w));
    simpl;
    intros;
    rewrite find_write1_morphism;
    fold (retire_write read0w) in H;
    simpl;
    destruct (n0 =? n) eqn:?;
    [simpl in *;
    inversion H |
    simpl in *;
    rewrite IHread0w;
    simpl; try reflexivity;     assumption].
        unfold retire_write;
    rewrite map_app;
    fold (retire_write (rev read0w));
    simpl;
    intros;
    rewrite find_write1_morphism;
    fold (retire_write read0w) in H;
    simpl;
    destruct (n0 =? n) eqn:?;
    [simpl in *;
    inversion H |
    simpl in *;
    rewrite IHread0w;
    simpl; try reflexivity;     assumption].
Qed.


Lemma find_write1_past_retire_rev:
    forall (read0w : WriteLog) (n0 : nat),
      find_write1_past (retire_write read0w) n0 = false -> find_write1_past (retire_write (rev read0w)) n0 = false.
Proof.
  induction read0w.
  -
    simpl in *.
    trivial.
  -
    simpl in *.
    destruct a.
    intros;
    unfold retire_write;
    rewrite map_app;
    fold (retire_write (rev read0w));
    simpl;
    intros;
    rewrite find_write1_past_morphism;
    fold (retire_write read0w) in H;
    simpl;
    rewrite IHread0w;
    simpl; try reflexivity;try assumption.
        intros;
    unfold retire_write;
    rewrite map_app;
    fold (retire_write (rev read0w));
    simpl;
    intros;
    rewrite find_write1_past_morphism;
    fold (retire_write read0w) in H;
    simpl;
    rewrite IHread0w;
    simpl; try reflexivity;try assumption.
        unfold retire_write;
    rewrite map_app;
    fold (retire_write (rev read0w));
    simpl;
    intros;
    rewrite find_write1_past_morphism;
    fold (retire_write read0w) in H;
    simpl;
    destruct (n0 =? n) eqn:?;
    [simpl in *;
    inversion H |
    simpl in *;
    rewrite IHread0w;
    simpl; try reflexivity;     assumption].
        unfold retire_write;
    rewrite map_app;
    fold (retire_write (rev read0w));
    simpl;
    intros;
    rewrite find_write1_past_morphism;
    fold (retire_write read0w) in H;
    simpl;
    destruct (n0 =? n) eqn:?;
    [simpl in *;
    inversion H |
    simpl in *;
    rewrite IHread0w;
    simpl; try reflexivity;     assumption].
Qed.

Lemma read_when_not_updated :
  forall read0w ,
    let read0w0 := ((retire_write read0w))  in
    forall l n0,
    find_write_past read0w0 n0 = false ->
    find_write1 read0w0 n0 = false ->
    extract_read0 (partial_perform_update l ( read0w0)) n0 = extract_read0 l n0.
  intros.
  unfold partial_perform_update.
  subst read0w0.
  pose proof rev_retire.
  rewrite H1.
  apply (rev_list_ind (fun read0w0 =>
                         let read0w0 := ((retire_write read0w0))  in
                         forall l n0,
                           find_write_past read0w0 n0 = false ->
                           find_write1 read0w0 n0 = false ->
                           extract_read0 (partial_perform_update' l ( read0w0)) n0 = extract_read0 l n0)) .
  simpl.
  reflexivity.
  intros.
  subst read0w0.
  rewrite read_when_not_updated'.
  reflexivity.
  simpl in *.
  assumption.
  assumption.
  rewrite find_writepast_retire_rev.
  reflexivity.
  assumption.
  rewrite find_write1_retire_rev.
  reflexivity.
  assumption.
Qed.



Lemma retired_retired_write :
  forall l0 n read0r read0w,
    nth_error (retire l0) n = Some (read0r, read0w) ->
    read0w = retire_write read0w.
  induction l0; intros.
  -
    simpl.
    destruct n; cbv in H; inversion H.
  -
    simpl in *.
    destruct n.
    simpl in *.
    inversion H.
    unfold retire_write.
    apply retire_write_projector.
    simpl in H.
    rewrite <- (IHl0 n read0r read0w ).
    reflexivity.
    assumption.
Qed.

Ltac destruct_res IHa :=
  let name_bind := fresh "element_" IHa in
  let name_length := fresh "length_" IHa in
  let name_reg := fresh "reg_" IHa in
  let name_double := fresh "nodoublewrite_" IHa in
  let name_perform := fresh "perform_" IHa in
  destruct IHa as [name_bind IHa];
  destruct IHa as [name_length IHa];
  destruct IHa as [name_reg IHa];
  destruct IHa as [name_double name_perform].

Lemma read_n_from_perform:
  forall(l0 : list (ReadLog * WriteLog)) (n nb_scopes : nat) (regs_content : list (list value)) (l : list value) (read0 : ReadLog * WriteLog),
    length regs_content = nb_scopes ->
    length (retire l0) = nb_scopes ->
    nth_error regs_content n = Some l ->
    nth_error (retire l0) n = Some read0 ->
    nth_error
      (map
         (fun x : list value * (ReadLog * WriteLog) =>
            let (regs, log) := x in
            partial_perform_update regs (snd log))
         (combine regs_content (retire l0))) n =
    Some
      (partial_perform_update l
                              (map
                                 (fun x : sort_write =>
                                    match x with
                                    | write_0 n0 v | write_past n0 v => write_past n0 v
                                    | write_1 n0 v | write_past_1 n0 v => write_past_1 n0 v
                                    end) (snd read0))).
Proof.
  induction l0; simpl.
  -
    intros.
    destruct n; simpl in H2; congruence.
  -
    intros.
    destruct regs_content;
      destruct n; simpl in H1; try congruence.
    {
      inversion H1.
      subst.
      clear H1.
      simpl in H0.
      inversion H0. clear H0.
      simpl in IHl0.
      simpl in *.
      inversion H2.
      simpl.
      rewrite <- retire_write_projector.
      reflexivity.
    }
    {
      simpl.
      rewrite (IHl0 n (nb_scopes - 1) regs_content l read0)  .
      reflexivity.
      simpl in H.
      rewrite <- H.
      simpl.
      rewrite Nat.sub_0_r; reflexivity.
      rewrite <- H0.
      simpl.
      rewrite Nat.sub_0_r; reflexivity.
      assumption.
      simpl in H2.
      assumption.
    }
Qed.


Fixpoint no_double_write_aux  (w:WriteLog) : bool :=
  match w with
  | nil => true
  | cons (write_0 n v) t => andb (negb (find_anywrite t n)) (no_double_write_aux t)
  | cons (write_past n v) t => andb (negb (find_anywrite t n)) (no_double_write_aux t)
  | cons (write_1 n v) t => andb (negb (find_write1 t n)) (no_double_write_aux t)
  | cons (write_past_1 n v) t => andb (negb (find_write1 t n)) (no_double_write_aux t)
  end.


Fixpoint no_double_write (l: list (ReadLog*WriteLog)) : bool
  := match l with
     | nil => true
     | cons h t => andb (no_double_write_aux (snd h)) (no_double_write t)
     end
.

Lemma anywrite_moregeneral : forall n0 read0w,
      find_anywrite (retire_write read0w) n0 = false ->
      find_write_past (retire_write read0w) n0 = false /\
      find_write1 (retire_write read0w) n0 = false.
induction read0w.
-
  simpl in *.
  firstorder.
-
  simpl in *.
  intros.
  destruct a;
    destruct (n0 =? n) eqn:?;
             simpl in *;
  try congruence; apply IHread0w; assumption.
Qed.


Lemma ppu_preserves_length' : forall u l, length (partial_perform_update' l u) = length (l).
Proof.

  induction u.
  -
    simpl in *.
    reflexivity.
  -
    simpl in *.
    destruct a; simpl in *;
    intros;
    destruct (replace_nth n l v) eqn:?;
    rewrite IHu;
    pose proof (replace_nth_length v n l );
    rewrite Heqo in H;
    try reflexivity; try assumption;
    firstorder.
Qed.


Lemma ppu_preserves_length : forall u l, length (partial_perform_update l u) = length (l).
Proof.
  unfold partial_perform_update.
  intros.
  apply (rev_list_ind (fun u =>
                         forall (l : list value), length (partial_perform_update' l ( u)) = length l)) .
  intros.
  simpl.
  reflexivity.
  intros.
  simpl.
  rewrite ppu_preserves_length'.
  reflexivity.
Qed.


Lemma ppu_preserves_nth_error:
  forall  (l l' : list value) (n0 : nat) (v0 : value) ,
    nth_error l n0 = Some v0 ->
    length l = length l' ->
    exists foo : value,
      nth_error
        l' n0 = Some foo.
Proof.
induction l , l'.
-
  simpl in *.
  intros.
  destruct n0; simpl in *; inversion H.
-
  simpl in *; intros.
  destruct n0; simpl in *; inversion H.
-
  simpl in *; intros.
  inversion H0.
-
  simpl in *.
  intros.
  inversion H0.
  destruct n0.
  simpl in *.
  eexists;reflexivity.
  simpl in *.
  apply (IHl l' n0 v0).
  exact H.
  exact H2.
Qed.


Lemma useless_log_in_extract1:
  forall l n n0 read0w v,
    n <> n0 ->
    extract_read1 l
                  (write_past_1 n v :: read0w)
                  n0 =
    extract_read1 l
                  read0w
                  n0.
  simpl in *.
  intros.
  pose proof (Nat.eqb_neq n n0).
  destruct H0.
  specialize (H1 H).
  clear H0.
  rewrite Nat.eqb_sym in H1.
  rewrite H1.
  reflexivity.
Qed.


Lemma useless_log_in_extract_past:
  forall l n n0 read0w v,
    n <> n0 ->
    extract_read1 l
                  (write_past n v :: read0w)
                  n0 =
    extract_read1 l
                  read0w
                  n0.
  simpl in *.
  intros.
  pose proof (Nat.eqb_neq n n0).
  destruct H0.
  specialize (H1 H).
  clear H0.
  rewrite Nat.eqb_sym in H1.
  rewrite H1.
  reflexivity.
Qed.

Lemma useless_middlelog_in_extractpast1:
  forall read1w l n n0 read0w v,
    n <> n0 ->
    extract_read1 l
                  (read1w ++ write_past_1 n v :: read0w)
                  n0 =
    extract_read1 l
                  (read1w ++ read0w)
                  n0.
  induction read1w.
  -
    simpl.
    pose proof useless_log_in_extract1.
    simpl in *.
    assumption.
  -
    simpl in *.
    destruct a;
      [intros;
       destruct (n1 =? n) eqn:?;
                [reflexivity|
                 rewrite IHread1w;
                 [
                   reflexivity| assumption]]
      |intros;
       destruct (n1 =? n) eqn:?;
                [reflexivity |
                 rewrite IHread1w;
                 [
                   reflexivity| assumption
                 ]
                ]
      |intros;
       rewrite IHread1w;
       [
         reflexivity | assumption
       ]
      |intros;
       rewrite IHread1w;
       [
         reflexivity | assumption
       ]
      ].
Qed.

Lemma useless_middlelog_in_extract_past:
  forall read1w l n n0 read0w v,
    n <> n0 ->
    extract_read1 l
                  (read1w ++ write_past n v :: read0w)
                  n0 =
    extract_read1 l
                  (read1w ++ read0w)
                  n0.
  induction read1w.
  -
    simpl.
    pose proof useless_log_in_extract_past.
    simpl in *.
    assumption.
  -
    simpl in *.
    destruct a;
      [intros;
       destruct (n1 =? n) eqn:?;
                [reflexivity|
                 rewrite IHread1w;
                 [
                   reflexivity| assumption]]
      |intros;
       destruct (n1 =? n) eqn:?;
                [reflexivity |
                 rewrite IHread1w;
                 [
                   reflexivity| assumption
                 ]
                ]
      |intros;
       rewrite IHread1w;
       [
         reflexivity | assumption
       ]
      |intros;
       rewrite IHread1w;
       [
         reflexivity | assumption
       ]
      ].
Qed.

Lemma extract1_on_base : forall read1w l l' n0, nth_error l n0 = nth_error l' n0 -> extract_read1 l read1w n0 =
        extract_read1 l' read1w n0.
induction read1w.
-
  simpl in *.
  intros.
  unfold extract_read0.
  assumption.
-
  simpl in *.
  intros.
  destruct a;
    [destruct (n0 =? n) eqn:?;
              [reflexivity|
               apply IHread1w;
               assumption]
    |destruct (n0 =? n) eqn:?;
              [reflexivity|
               apply IHread1w;
               assumption]
    |apply IHread1w;
     assumption
    |destruct (n0 =? n) eqn:?;
              [reflexivity|
               apply IHread1w;
               assumption]]
      .
Qed.

Lemma extract1_from_log:
  forall (read1w read0w : WriteLog) (l : list value)
    (n0 : nat) (v0 v : value),
    nth_error l n0 = Some v0 ->
    find_anywrite (retire_write read0w) n0 = false ->
    extract_read1
      match replace_nth n0 l v with
      | Some newregs =>
        partial_perform_update newregs (retire_write read0w)
      | None => partial_perform_update l (retire_write read0w)
      end read1w n0 =
    extract_read1 l
                  (read1w ++ write_past n0 v :: retire_write read0w) n0.
Proof.
  induction read1w.
  -
    simpl.
    intros.
    rewrite (Nat.eqb_refl).
    pose proof (replace_in_right_size l n0 v0 v H).
    destruct (replace_nth n0 l v) eqn:?.
    unfold extract_read0.
    pose proof (anywrite_moregeneral n0 read0w H0) as anywrite.
    destruct anywrite as [writepast write1].
    pose proof (read_when_not_updated read0w l0 n0 writepast write1) as extract0.
    unfold extract_read0 in extract0.
    rewrite extract0.
    rewrite H1.
    reflexivity.
    contradiction.
  -
    simpl in *.
    intros.
    destruct a; simpl in *.
    destruct (n0 =? n) eqn:?.
    reflexivity.
    rewrite (IHread1w _ _ _ v0 v) by assumption.
    reflexivity.
    destruct (n0 =? n) eqn:?.
    reflexivity.
    rewrite (IHread1w _ _ _ v0 v) by assumption.
    reflexivity.
    rewrite (IHread1w _ _ _ v0 v) by assumption.
    reflexivity.
    destruct (n0 =? n) eqn:?.
    reflexivity.
    rewrite (IHread1w _ _ _ v0 v) by assumption.
    reflexivity.
Qed.


Lemma extract1_from_log':
  forall (read1w read0w : WriteLog) (l : list value)
    (n0 : nat) (v0 v : value),
    nth_error l n0 = Some v0 ->
    find_anywrite (retire_write read0w) n0 = false ->
    extract_read1
      match replace_nth n0 l v with
      | Some newregs =>
        partial_perform_update' newregs (retire_write read0w)
      | None => partial_perform_update' l (retire_write read0w)
      end read1w n0 =
    extract_read1 l
                  (read1w ++ write_past n0 v :: retire_write read0w) n0.
Proof.
  induction read1w.
  -
    simpl.
    intros.
    rewrite (Nat.eqb_refl).
    pose proof (replace_in_right_size l n0 v0 v H).
    destruct (replace_nth n0 l v) eqn:?.
    unfold extract_read0.
    pose proof (anywrite_moregeneral n0 read0w H0) as anywrite.
    destruct anywrite as [writepast write1].
    pose proof (read_when_not_updated' read0w l0 n0 writepast write1) as extract0.
    unfold extract_read0 in extract0.
    rewrite extract0.
    rewrite H1.
    reflexivity.
    contradiction.
  -
    simpl in *.
    intros.
    destruct a; simpl in *.
    destruct (n0 =? n) eqn:?.
    reflexivity.
    rewrite (IHread1w _ _ _ v0 v) by assumption.
    reflexivity.
    destruct (n0 =? n) eqn:?.
    reflexivity.
    rewrite (IHread1w _ _ _ v0 v) by assumption.
    reflexivity.
    rewrite (IHread1w _ _ _ v0 v) by assumption.
    reflexivity.
    destruct (n0 =? n) eqn:?.
    reflexivity.
    rewrite (IHread1w _ _ _ v0 v) by assumption.
    reflexivity.
Qed.

Lemma nth_error_morphism_ppu':
  forall (read0w : WriteLog) (l : list value) (l0 : list value) (n0 : nat),
    nth_error l0 n0 = nth_error l n0 ->
    nth_error (partial_perform_update' l0 read0w) n0 = nth_error (partial_perform_update' l read0w) n0.
Proof.
  induction read0w.
  -
    simpl in *.
    intros;assumption.
  -
    simpl in *.
    intros.
    destruct a.
    (* Same script 4 times *)
    {
      destruct (replace_nth n l0 v) eqn:?.
      +
        destruct (replace_nth n l v) eqn:?.
        *
          pose proof (fun n0 => prim_caract_nth_replace l n n0 v) as nlv;
            pose proof (fun n0 => prim_caract_nth_replace l0 n n0 v)as nl0v;
            rewrite Heqo in nl0v;
            rewrite Heqo0 in nlv;
            apply IHread0w;
            specialize (nlv n0);
            specialize (nl0v n0);
            destruct (n =? n0).
          --
            rewrite nlv, nl0v;
              reflexivity.
          --
            rewrite nlv, nl0v;
              rewrite H;
              reflexivity.
        *
          pose proof (replace_in l0 n v ) as nlv;
            rewrite  Heqo in  nlv;
            pose proof (prim_caract_nth_replace l0 n n0 v)as nl0v;
            rewrite Heqo in nl0v;
            apply IHread0w;
            rewrite <- H;
            destruct (n =? n0) eqn:?.
          --
            pose proof (Nat.eqb_eq n n0) as equivbool;
              destruct equivbool as [decToReal realToDec];
              specialize (decToReal Heqb);
              rewrite decToReal in *;
              clear realToDec;
              clear Heqb;
              clear decToReal;
              destruct (nth_error l0 n0) eqn:?.
            ++
              apply eq_sym in H;
                pose proof (replace_in_right_size l n0 v0 v H);
                rewrite Heqo0 in H0;
                contradiction.
            ++
              pose proof (replace_in_right_size_none l0 n0 v Heqo1);
                rewrite Heqo in H0;
                contradiction.
          --
            assumption.
      +
        destruct (replace_nth n l v) eqn:?.
        *
          pose proof (replace_in l n v ) as nl0v;
            rewrite  Heqo0 in  nl0v;
            pose proof (prim_caract_nth_replace l n n0 v)as nlv;
            rewrite Heqo0 in nlv;
            apply IHread0w;
            destruct (n =? n0) eqn:?.
          --
            pose proof (Nat.eqb_eq n n0) as equivbool;
              destruct equivbool as [decToReal realToDec];
              specialize (decToReal Heqb);
              rewrite decToReal in *;
              clear realToDec;
              clear Heqb;
              clear decToReal;
              destruct (nth_error l0 n0) eqn:?.
            ++
              apply eq_sym in H;
                pose proof (replace_in_right_size l0 n0 v0 v Heqo1);
                rewrite Heqo in H0;
                contradiction.
            ++
              apply eq_sym in H;
                pose proof (replace_in_right_size_none l n0 v H);
                rewrite Heqo0 in H0;
                contradiction.
          --
            rewrite nlv, H;
              reflexivity.
        *
          apply IHread0w;
            assumption.
    }
    {
      destruct (replace_nth n l0 v) eqn:?.
      +
        destruct (replace_nth n l v) eqn:?.
        *
          pose proof (fun n0 => prim_caract_nth_replace l n n0 v) as nlv;
            pose proof (fun n0 => prim_caract_nth_replace l0 n n0 v)as nl0v;
            rewrite Heqo in nl0v;
            rewrite Heqo0 in nlv;
            apply IHread0w;
            specialize (nlv n0);
            specialize (nl0v n0);
            destruct (n =? n0).
          --
            rewrite nlv, nl0v;
              reflexivity.
          --
            rewrite nlv, nl0v;
              rewrite H;
              reflexivity.
        *
          pose proof (replace_in l0 n v ) as nlv;
            rewrite  Heqo in  nlv;
            pose proof (prim_caract_nth_replace l0 n n0 v)as nl0v;
            rewrite Heqo in nl0v;
            apply IHread0w;
            rewrite <- H;
            destruct (n =? n0) eqn:?.
          --
            pose proof (Nat.eqb_eq n n0) as equivbool;
              destruct equivbool as [decToReal realToDec];
              specialize (decToReal Heqb);
              rewrite decToReal in *;
              clear realToDec;
              clear Heqb;
              clear decToReal;
              destruct (nth_error l0 n0) eqn:?.
            ++
              apply eq_sym in H;
                pose proof (replace_in_right_size l n0 v0 v H);
                rewrite Heqo0 in H0;
                contradiction.
            ++
              pose proof (replace_in_right_size_none l0 n0 v Heqo1);
                rewrite Heqo in H0;
                contradiction.
          --
            assumption.
      +
        destruct (replace_nth n l v) eqn:?.
        *
          pose proof (replace_in l n v ) as nl0v;
            rewrite  Heqo0 in  nl0v;
            pose proof (prim_caract_nth_replace l n n0 v)as nlv;
            rewrite Heqo0 in nlv;
            apply IHread0w;
            destruct (n =? n0) eqn:?.
          --
            pose proof (Nat.eqb_eq n n0) as equivbool;
              destruct equivbool as [decToReal realToDec];
              specialize (decToReal Heqb);
              rewrite decToReal in *;
              clear realToDec;
              clear Heqb;
              clear decToReal;
              destruct (nth_error l0 n0) eqn:?.
            ++
              apply eq_sym in H;
                pose proof (replace_in_right_size l0 n0 v0 v Heqo1);
                rewrite Heqo in H0;
                contradiction.
            ++
              apply eq_sym in H;
                pose proof (replace_in_right_size_none l n0 v H);
                rewrite Heqo0 in H0;
                contradiction.
          --
            rewrite nlv, H;
              reflexivity.
        *
          apply IHread0w;
            assumption.
    }
    {
      destruct (replace_nth n l0 v) eqn:?.
      +
        destruct (replace_nth n l v) eqn:?.
        *
          pose proof (fun n0 => prim_caract_nth_replace l n n0 v) as nlv;
            pose proof (fun n0 => prim_caract_nth_replace l0 n n0 v)as nl0v;
            rewrite Heqo in nl0v;
            rewrite Heqo0 in nlv;
            apply IHread0w;
            specialize (nlv n0);
            specialize (nl0v n0);
            destruct (n =? n0).
          --
            rewrite nlv, nl0v;
              reflexivity.
          --
            rewrite nlv, nl0v;
              rewrite H;
              reflexivity.
        *
          pose proof (replace_in l0 n v ) as nlv;
            rewrite  Heqo in  nlv;
            pose proof (prim_caract_nth_replace l0 n n0 v)as nl0v;
            rewrite Heqo in nl0v;
            apply IHread0w;
            rewrite <- H;
            destruct (n =? n0) eqn:?.
          --
            pose proof (Nat.eqb_eq n n0) as equivbool;
              destruct equivbool as [decToReal realToDec];
              specialize (decToReal Heqb);
              rewrite decToReal in *;
              clear realToDec;
              clear Heqb;
              clear decToReal;
              destruct (nth_error l0 n0) eqn:?.
            ++
              apply eq_sym in H;
                pose proof (replace_in_right_size l n0 v0 v H);
                rewrite Heqo0 in H0;
                contradiction.
            ++
              pose proof (replace_in_right_size_none l0 n0 v Heqo1);
                rewrite Heqo in H0;
                contradiction.
          --
            assumption.
      +
        destruct (replace_nth n l v) eqn:?.
        *
          pose proof (replace_in l n v ) as nl0v;
            rewrite  Heqo0 in  nl0v;
            pose proof (prim_caract_nth_replace l n n0 v)as nlv;
            rewrite Heqo0 in nlv;
            apply IHread0w;
            destruct (n =? n0) eqn:?.
          --
            pose proof (Nat.eqb_eq n n0) as equivbool;
              destruct equivbool as [decToReal realToDec];
              specialize (decToReal Heqb);
              rewrite decToReal in *;
              clear realToDec;
              clear Heqb;
              clear decToReal;
              destruct (nth_error l0 n0) eqn:?.
            ++
              apply eq_sym in H;
                pose proof (replace_in_right_size l0 n0 v0 v Heqo1);
                rewrite Heqo in H0;
                contradiction.
            ++
              apply eq_sym in H;
                pose proof (replace_in_right_size_none l n0 v H);
                rewrite Heqo0 in H0;
                contradiction.
          --
            rewrite nlv, H;
              reflexivity.
        *
          apply IHread0w;
            assumption.
    }
    {
      destruct (replace_nth n l0 v) eqn:?.
      +
        destruct (replace_nth n l v) eqn:?.
        *
          pose proof (fun n0 => prim_caract_nth_replace l n n0 v) as nlv;
            pose proof (fun n0 => prim_caract_nth_replace l0 n n0 v)as nl0v;
            rewrite Heqo in nl0v;
            rewrite Heqo0 in nlv;
            apply IHread0w;
            specialize (nlv n0);
            specialize (nl0v n0);
            destruct (n =? n0).
          --
            rewrite nlv, nl0v;
              reflexivity.
          --
            rewrite nlv, nl0v;
              rewrite H;
              reflexivity.
        *
          pose proof (replace_in l0 n v ) as nlv;
            rewrite  Heqo in  nlv;
            pose proof (prim_caract_nth_replace l0 n n0 v)as nl0v;
            rewrite Heqo in nl0v;
            apply IHread0w;
            rewrite <- H;
            destruct (n =? n0) eqn:?.
          --
            pose proof (Nat.eqb_eq n n0) as equivbool;
              destruct equivbool as [decToReal realToDec];
              specialize (decToReal Heqb);
              rewrite decToReal in *;
              clear realToDec;
              clear Heqb;
              clear decToReal;
              destruct (nth_error l0 n0) eqn:?.
            ++
              apply eq_sym in H;
                pose proof (replace_in_right_size l n0 v0 v H);
                rewrite Heqo0 in H0;
                contradiction.
            ++
              pose proof (replace_in_right_size_none l0 n0 v Heqo1);
                rewrite Heqo in H0;
                contradiction.
          --
            assumption.
      +
        destruct (replace_nth n l v) eqn:?.
        *
          pose proof (replace_in l n v ) as nl0v;
            rewrite  Heqo0 in  nl0v;
            pose proof (prim_caract_nth_replace l n n0 v)as nlv;
            rewrite Heqo0 in nlv;
            apply IHread0w;
            destruct (n =? n0) eqn:?.
          --
            pose proof (Nat.eqb_eq n n0) as equivbool;
              destruct equivbool as [decToReal realToDec];
              specialize (decToReal Heqb);
              rewrite decToReal in *;
              clear realToDec;
              clear Heqb;
              clear decToReal;
              destruct (nth_error l0 n0) eqn:?.
            ++
              apply eq_sym in H;
                pose proof (replace_in_right_size l0 n0 v0 v Heqo1);
                rewrite Heqo in H0;
                contradiction.
            ++
              apply eq_sym in H;
                pose proof (replace_in_right_size_none l n0 v H);
                rewrite Heqo0 in H0;
                contradiction.
          --
            rewrite nlv, H;
              reflexivity.
        *
          apply IHread0w;
            assumption.
    }
Qed.


Lemma nth_error_morphism_pp:
  forall (read0w : WriteLog) (l : list value) (l0 : list value) (n0 : nat),
    nth_error l0 n0 = nth_error l n0 ->
    nth_error (partial_perform_update l0 read0w) n0 = nth_error (partial_perform_update l read0w) n0.
Proof.
  unfold partial_perform_update.
  intros.
  apply (rev_list_ind (fun read0w =>
                         forall (l l0 : list value) (n0 : nat),
                           nth_error l0 n0 = nth_error l n0 ->
                           nth_error (partial_perform_update' l0 (read0w)) n0 =
                           nth_error (partial_perform_update' l (read0w)) n0)).
  intros.
  simpl .
  assumption.
  simpl.
  intros.
  erewrite nth_error_morphism_ppu'.
  reflexivity.
  assumption.
  assumption.
Qed.

Lemma read1_when_not_updated' :
  forall read0w read1w l n0 v0,
    let read0w := retire_write read0w  in
    find_write1_past read0w n0 = false ->
    nth_error l n0 = Some v0 ->
    no_double_write_aux read0w = true ->
    extract_read1 (partial_perform_update' l read0w) read1w n0 = extract_read1 l (read1w ++ read0w) n0.
Proof.
  induction read0w.
  +
    simpl.
    intros.
    rewrite app_nil_r.
    trivial.
  +
    simpl.
    intros.
    destruct a eqn:?;
             [destruct ( n=? n0) eqn:?;
                       [pose proof (Nat.eqb_eq n n0) as equivbool;
                        destruct equivbool as [decToReal realToDec];
                        specialize (decToReal Heqb);
                        rewrite decToReal;
                        rewrite decToReal in H1;
                        apply eq_sym in H1;
                        apply Bool.andb_true_eq in H1;
                        destruct H1 as [findanywrite nodoublewrite];
                        apply Bool.negb_sym in findanywrite;
                        simpl in *;
                        apply (extract1_from_log' _ _ _ _ v0) ; assumption
                       |pose proof (Nat.eqb_neq n n0);
                        destruct H2;
                        specialize (H2 Heqb);
                        clear H3;
                        rewrite useless_middlelog_in_extract_past by assumption;
                        apply eq_sym in H1;
                        apply Bool.andb_true_eq in H1;
                        destruct H1 as [findanywrite nodoublewrite];
                        apply Bool.negb_sym in findanywrite;
                        simpl in *;
                        apply eq_sym in nodoublewrite;
                        rewrite <- (IHread0w _ _ _ v0) by assumption;
                        destruct (replace_nth n l v) eqn:?;
                                 [pose proof (prim_caract_nth_replace l n n0 v);
                                  rewrite Heqo in H1;
                                  rewrite Heqb in H1;
                                  rewrite (extract1_on_base
                                             read1w
                                             (partial_perform_update' l0 (retire_write read0w))
                                             (partial_perform_update' l (retire_write read0w)));
                                  [reflexivity
                                  |apply nth_error_morphism_ppu';
                                   assumption
                                  ]
                                 | reflexivity
                                 ]
                       ]
             |destruct ( n=? n0) eqn:?;
                       [pose proof (Nat.eqb_eq n n0) as equivbool;
                        destruct equivbool as [decToReal realToDec];
                        specialize (decToReal Heqb);
                        rewrite decToReal;
                        rewrite decToReal in H1;
                        apply eq_sym in H1;
                        apply Bool.andb_true_eq in H1;
                        destruct H1 as [findanywrite nodoublewrite];
                        apply Bool.negb_sym in findanywrite;
                        simpl in *;
                        apply (extract1_from_log' _ _ _ _ v0) ; assumption
                       |pose proof (Nat.eqb_neq n n0);
                        destruct H2;
                        specialize (H2 Heqb);
                        clear H3;
                        rewrite useless_middlelog_in_extract_past by assumption;
                        apply eq_sym in H1;
                        apply Bool.andb_true_eq in H1;
                        destruct H1 as [findanywrite nodoublewrite];
                        apply Bool.negb_sym in findanywrite;
                        simpl in *;
                        apply eq_sym in nodoublewrite;
                        rewrite <- (IHread0w _ _ _ v0) by assumption;
                        destruct (replace_nth n l v) eqn:?;
                                 [pose proof (prim_caract_nth_replace l n n0 v);
                                  rewrite Heqo in H1;
                                  rewrite Heqb in H1;
                                  rewrite (extract1_on_base
                                             read1w
                                             (partial_perform_update' l0 (retire_write read0w))
                                             (partial_perform_update' l (retire_write read0w)));
                                  [reflexivity
                                  |apply nth_error_morphism_ppu';
                                   assumption
                                  ]
                                 |reflexivity
                                 ]
                       ]
             | (* Don't try anything yet *)
             | (* Don't try anything yet *)
             ].
    (* I am mad at those proof scripts that cannot be folded *)
    {
      destruct ( n0=? n) eqn:?.
      simpl in *.
      inversion H.
      pose proof (Nat.eqb_neq n0 n).
      destruct H2.
      specialize (H2 Heqb).
      clear H3.
      simpl in *.
      apply eq_sym in H1.
      apply Bool.andb_true_eq in H1.
      destruct H1 as [findanywrite nodoublewrite].
      apply Bool.negb_sym in findanywrite.
      simpl in *.
      apply not_eq_sym in H2.
      rewrite useless_middlelog_in_extractpast1 by assumption.
      apply eq_sym in nodoublewrite.
      rewrite <- (IHread0w _ _ _ v0) by assumption.
      destruct (replace_nth n l v) eqn:?;
               [  | reflexivity].
      pose proof (prim_caract_nth_replace l n n0 v).
      rewrite Heqo in H1.
      rewrite Nat.eqb_sym in H1.
      rewrite Heqb in H1.
      rewrite (extract1_on_base
                 read1w
                 (partial_perform_update' l0 (retire_write read0w))
                 (partial_perform_update' l (retire_write read0w)));
        [reflexivity
        |apply nth_error_morphism_ppu';
         assumption
        ].
    }
    {
      destruct ( n0=? n) eqn:?.
      simpl in *.
      inversion H.
      pose proof (Nat.eqb_neq n0 n).
      destruct H2.
      specialize (H2 Heqb).
      clear H3.
      simpl in *.
      apply eq_sym in H1.
      apply Bool.andb_true_eq in H1.
      destruct H1 as [findanywrite nodoublewrite].
      apply Bool.negb_sym in findanywrite.
      simpl in *.
      apply not_eq_sym in H2.
      rewrite useless_middlelog_in_extractpast1 by assumption.
      apply eq_sym in nodoublewrite.
      rewrite <- (IHread0w _ _ _ v0) by assumption.
      destruct (replace_nth n l v) eqn:?;
               [  | reflexivity].
      pose proof (prim_caract_nth_replace l n n0 v).
      rewrite Heqo in H1.
      rewrite Nat.eqb_sym in H1.
      rewrite Heqb in H1.
      rewrite (extract1_on_base
                 read1w
                 (partial_perform_update' l0 (retire_write read0w))
                 (partial_perform_update' l (retire_write read0w)));
        [reflexivity
        |apply nth_error_morphism_ppu';
         assumption
        ].
    }
Qed.


Lemma no_double_on_every_reg:
  forall (l0 : list (ReadLog * WriteLog)) (read0w : WriteLog) (n : nat) (read0r : ReadLog) ,
    no_double_write (retire l0) = true ->
    nth_error (retire l0) n = Some (read0r, read0w) ->
    no_double_write_aux (retire_write read0w) = true.
Proof.
  induction l0.
  -
    simpl in *.
    intros.
    destruct n; simpl in *; inversion H0.
  -
    intros.
    simpl in *.
    destruct a as [r w].
    simpl in *.
    destruct n eqn:?.
    +
      simpl in *.
      apply eq_sym in H.
      apply Bool.andb_true_eq in H.
      destruct H as [nodoublefuture nodoublewrite].
      apply eq_sym in nodoublewrite.
      inversion H0.
      clear H0.
      destruct w eqn:?.
      simpl in *.
      reflexivity.
      simpl in *.
      destruct s;
        simpl in *;
        unfold retire_write;
        rewrite <- retire_write_projector;
        apply eq_sym;
        assumption.
    +
      simpl in H0.
      eapply IHl0.
      apply eq_sym in H.
      apply Bool.andb_true_eq in H.
      destruct H as [nodoublefuture nodoublewrite].
      apply eq_sym in nodoublewrite.
      exact nodoublewrite.
      apply H0.
Qed.



Lemma find_continuous_l : forall l l' n,
    (find_anywrite (l ++ l') n) = false  ->
    (find_anywrite (l) n) = false.
  induction l.
  -
    simpl.
    trivial.
  -    
    simpl.
    intros.
    destruct a;
      try (destruct (n =? n0);
      [
        simpl in *;
        inversion H|
        simpl in *;
    apply (IHl l'); assumption]).
Qed.

Lemma find_continuous_l' : forall l l' n,
    (find_anywrite (l ++ l') n) = false  ->
    (find_anywrite (l') n) = false.
  induction l.
  -
    simpl.
    trivial.
  -
    simpl.
    intros.
    destruct a;
      try (destruct (n =? n0);
      [
        simpl in *;
        inversion H|
        simpl in *;
    apply (IHl l'); assumption]).
Qed.


Lemma find1_continuous_l : forall l l' n,
    (find_write1 (l ++ l') n) = false  ->
    (find_write1 (l) n) = false.
  induction l.
  -
    simpl.
    trivial.
  -
    simpl.
    intros.
    destruct a.
    eapply IHl.
    exact H.
    eapply IHl.
    exact H.
    all:(destruct (n =? n0);
      [
        simpl in *;
        inversion H|
        simpl in *;
    apply (IHl l'); assumption]).
Qed.

Lemma find1_continuous_l' : forall l l' n,
    (find_write1 (l ++ l') n) = false  ->
    (find_write1 (l') n) = false.
    induction l.
  -
    simpl.
    trivial.
  -
    simpl.
    intros.
    destruct a.
    eapply IHl.
    exact H.
    eapply IHl.
    exact H.
    all:(destruct (n =? n0);
      [
        simpl in *;
        inversion H|
        simpl in *;
    apply (IHl l'); assumption]).
Qed.


Lemma no_double_aux_l : forall l l',  true = no_double_write_aux (l ++ l') -> true = no_double_write_aux l.
induction l.
- intros.
  trivial.
-
  simpl.
  destruct a;
    try(
    intros;
    rewrite <- (IHl l');
    apply Bool.andb_true_eq in H;
    destruct H;
    apply Bool.negb_sym in H;
    simpl in H;
    pose proof (find_continuous_l l l' n H);
    [
      rewrite H1;
    simpl;
    reflexivity|
      destruct H;
      apply H0
      ]).
    intros;
    rewrite <- (IHl l');
    apply Bool.andb_true_eq in H;
    destruct H;
    apply Bool.negb_sym in H;
    simpl in H.
    pose proof (find1_continuous_l l l' n H).
    rewrite H1.
    simpl.
    reflexivity.
    assumption.
    intros.
    erewrite <- IHl.
    erewrite find1_continuous_l.
    simpl.
    reflexivity.
    apply Bool.andb_true_eq in H.
    destruct H.
    apply Bool.negb_sym in H.
    simpl.
    exact H.
        apply Bool.andb_true_eq in H.
    destruct H.
    exact H0.
Qed.


Lemma no_double_aux_l' : forall l l',  true = no_double_write_aux (l ++ l') -> true = no_double_write_aux l'.
induction l.
- intros.
  trivial.
-
  simpl.
  destruct a;
  try (intros;
      apply Bool.andb_true_eq in H;
    destruct H;
    apply Bool.negb_sym in H;
    simpl in H;
    rewrite <- (IHl l');[
    reflexivity|
    assumption]).
Qed.



Lemma no_double_append_l : forall l1 l0,
    length l0 = length l1 ->
    no_double_write (log_append l0 l1) = true ->
    no_double_write l0= true.
Proof.
induction l1.
-
  intros.
  simpl in *.
  rewrite length_zero_iff_nil in H.
  rewrite H.
  simpl.
  reflexivity.
-
  simpl.
  destruct l0.
  simpl.
  reflexivity.
  simpl.
  intros.
  fold (log_append l0 l1) in H0.
  apply eq_sym in H0.
  apply Bool.andb_true_eq in H0.
  destruct H0.
  apply eq_sym.
  rewrite IHl1.
  pose proof (no_double_aux_l' (snd a) (snd p) H0).
  rewrite <- H2.
  simpl.
  reflexivity.
  inversion H.
  reflexivity.
  apply eq_sym.
  assumption.
Qed.



Lemma no_double_append_r : forall l1 l0,
    length l0 = length l1 ->
    no_double_write (log_append l0 l1) = true ->
                               no_double_write l1 = true.
induction l1.
-
  intros.
  simpl in *.

  reflexivity.
-
  intros.
  simpl.
  destruct l0.
  simpl in *.
  inversion H.
  simpl in *.
  fold (log_append l0 l1) in H0.
  apply eq_sym in H0.
  apply Bool.andb_true_eq in H0.
  destruct H0.
  apply eq_sym.
  rewrite (IHl1 l0).
  pose proof (no_double_aux_l (snd a) (snd p) H0).
  rewrite <- H2.
  simpl.
  reflexivity.
  inversion H.
  reflexivity.
  apply eq_sym.
  assumption.
Qed.


Lemma append_no_write:
  forall (l : list (ReadLog * WriteLog)) (n : nat) x, 
    no_double_write l = true ->
    no_double_write
      (log_append l (compute_log_append n x (length l))) =
    true.
Proof.
induction l.
-
  simpl.
  trivial.
-
  simpl. intros.
  destruct n.
  simpl.
  fold (log_append l (repeat ([], []) (length l - 0))).
  rewrite <- log_append_id.
  exact H.
  simpl.
  fold (log_append l (repeat ([], []) n ++
                             ([x], []) :: repeat ([], []) (length l - S n))).
  fold (@compute_log_append sort_read sort_write n (x) (length l)).
  rewrite IHl.
  apply eq_sym in H.
  apply Bool.andb_true_eq in H.
  destruct H.
  rewrite <- H.
  cbv.
  reflexivity.
  apply eq_sym in H.
  apply Bool.andb_true_eq in H.
  destruct H.
  rewrite <- H0.
  reflexivity.
Qed.

Lemma read_preserve_no_double_write:
  forall (n n0 : nat)
    (l : list (ReadLog * WriteLog))
    (l2 : list (ReadLog * WriteLog))
    (r : ReadLog )
    (w : WriteLog)
    ( element_logctx : list (ReadLog * WriteLog)),
    length element_logctx = length l ->
    no_double_write l = true ->
    nth_error l n =
         Some (r, w) ->
    replace_nth n l
                (read n0 :: r, w) = Some l2 ->
    l2 = log_append l element_logctx ->
    no_double_write
      (log_append l element_logctx) = true.
intros.
pose proof (replacing_log_append_is_appending_read' n l (read n0) r w H1).
rewrite H2 in H4.
inversion H4.
rewrite H6 in H3.
clear H6 H4.
pose proof (log_append_injR l (compute_log_append n
            (read n0) (length l)) element_logctx).
unfold compute_log_append in H4.
rewrite app_length in H4.
rewrite repeat_length in H4.
simpl in H4.
rewrite repeat_length in H4.
assert (n < length l).
apply nth_error_Some.
rewrite H1.
discriminate.
assert ( length l = n + S (length l - S n)).
omega.
rewrite <- H6 in H4.
specialize (H4 eq_refl).
clear H5 H6.
rewrite H in H4.
specialize (H4 eq_refl).
rewrite <- H4.
fold (@compute_log_append sort_read sort_write n (read n0) (length l)).
apply append_no_write.
apply H0.
fold (@compute_log_append sort_read sort_write n (read n0) (length l)).
rewrite H3.
reflexivity.
Qed.

(* Exactly same proof module read/fwd *)
Lemma forward_preserve_no_double_write:
  forall (n n0 : nat)
    (l : list (ReadLog * WriteLog))
    (l2 : list (ReadLog * WriteLog))
    (r : ReadLog )
    (w : WriteLog)
    ( element_logctx : list (ReadLog * WriteLog)),
    length element_logctx = length l ->
    no_double_write l = true ->
    nth_error l n =
         Some (r, w) ->
    replace_nth n l
                (forward n0 :: r, w) = Some l2 ->
    l2 = log_append l element_logctx ->
    no_double_write
      (log_append l element_logctx) = true.
intros.
pose proof (replacing_log_append_is_appending_read' n l (forward n0) r w H1).
rewrite H2 in H4.
inversion H4.
rewrite H6 in H3.
clear H6 H4.
pose proof (log_append_injR l (compute_log_append n
            (forward n0) (length l)) element_logctx).
unfold compute_log_append in H4.
rewrite app_length in H4.
rewrite repeat_length in H4.
simpl in H4.
rewrite repeat_length in H4.
assert (n < length l).
apply nth_error_Some.
rewrite H1.
discriminate.
assert ( length l = n + S (length l - S n)).
omega.
rewrite <- H6 in H4.
specialize (H4 eq_refl).
clear H5 H6.
rewrite H in H4.
specialize (H4 eq_refl).
rewrite <- H4.
fold (@compute_log_append sort_read sort_write n (forward n0) (length l)).
apply append_no_write.
apply H0.
fold (@compute_log_append sort_read sort_write n (forward n0) (length l)).
rewrite H3.
reflexivity.
Qed.




Lemma write_safe_double:
  forall (n n0 : nat) (v : value) (read0r read1r : ReadLog) (read0w read1w : WriteLog)
    (l : list (ReadLog * WriteLog)) (element_logctx : list (ReadLog * WriteLog)),
    no_double_write l = true ->
    nth_error l n = Some (read1r ++ read0r, read1w ++ read0w) ->
    find_anywrite read1w n0 = false ->
    find_anywrite read0w n0 = false ->
    replace_nth n l
                (read1r ++ read0r, write_0 n0 v :: read1w ++ read0w) =
    Some (log_append l element_logctx) ->
    length element_logctx = length l ->
    no_double_write
      (log_append l element_logctx) = true.
Proof.
  intros.
  pose proof (replacing_log_append_is_appending_write' n l (write_0 n0 v) _ _ H0).
  rewrite H5 in H3.
  inversion H3.
  apply log_append_injR in H7.
  2:{
    unfold compute_log_append_write.
    rewrite app_length.
    simpl in *.
    rewrite repeat_length.
    rewrite repeat_length.
    assert (n < length l).
    apply nth_error_Some.
    rewrite H0.
    discriminate.
    omega.
  }
  2:{
    unfold compute_log_append_write.
    rewrite app_length.
    simpl in *.
    rewrite repeat_length.
    rewrite repeat_length.
    assert (n < length l).
    apply nth_error_Some.
    rewrite H0.
    discriminate.
    rewrite H4.
    omega.
  }
  clear H3 H4 H5 H7 element_logctx.
  generalize dependent n.
  induction l.
  -
    simpl.
    reflexivity.
  -
    intros.
    simpl.
    destruct n.
    +
      simpl in *.
      inversion H0; clear H0.
      simpl.
      rewrite find_anywrite_morphism.
      rewrite H1, H2.
      simpl.
      rewrite H4 in *.
      simpl in H.
      fold (log_append l (repeat ([], []) (length l - 0))).
      rewrite <- log_append_id.
      assumption.
    +
      simpl in *.
      fold (log_append l ((repeat ([], []) n ++ ([], [write_0 n0 v]) :: repeat ([], []) (length l - S n)))).
      fold (@compute_log_append_write sort_read sort_write ( n) (write_0 n0 v) (length l)).
      rewrite IHl.
      apply eq_sym in H.
      apply Bool.andb_true_eq in H.
      destruct H.
      apply eq_sym in H0.
      rewrite <- H.
      reflexivity.
      apply eq_sym in H.
      apply Bool.andb_true_eq in H.
      destruct H.
      apply eq_sym in H0.
      rewrite <- H3.
      reflexivity.
      assumption.
Qed.


Lemma write1_safe_double:
  forall (n n0 : nat) (v : value) (read0r read1r : ReadLog) (read0w read1w : WriteLog)
    (l : list (ReadLog * WriteLog)) (element_logctx : list (ReadLog * WriteLog)),
    no_double_write l = true ->
    nth_error l n = Some (read1r ++ read0r, read1w ++ read0w) ->
    find_write1 read1w n0 = false ->
    find_write1 read0w n0 = false ->
    replace_nth n l
                (read1r ++ read0r, write_1 n0 v :: read1w ++ read0w) =
    Some (log_append l element_logctx) ->
    length element_logctx = length l ->
    no_double_write
      (log_append l element_logctx) = true.
Proof.
  intros.
  pose proof (replacing_log_append_is_appending_write' n l (write_1 n0 v) _ _ H0).
  rewrite H5 in H3.
  inversion H3.
  apply log_append_injR in H7.
  2:{
    unfold compute_log_append_write.
    rewrite app_length.
    simpl in *.
    rewrite repeat_length.
    rewrite repeat_length.
    assert (n < length l).
    apply nth_error_Some.
    rewrite H0.
    discriminate.
    omega.
  }
  2:{
    unfold compute_log_append_write.
    rewrite app_length.
    simpl in *.
    rewrite repeat_length.
    rewrite repeat_length.
    assert (n < length l).
    apply nth_error_Some.
    rewrite H0.
    discriminate.
    rewrite H4.
    omega.
  }
  clear H3 H4 H5 H7 element_logctx.
  generalize dependent n.
  induction l.
  -
    simpl.
    reflexivity.
  -
    intros.
    simpl.
    destruct n.
    +
      simpl in *.
      inversion H0; clear H0.
      simpl.
      rewrite find_write1_morphism.
      rewrite H1, H2.
      simpl.
      rewrite H4 in *.
      simpl in H.
      fold (log_append l (repeat ([], []) (length l - 0))).
      rewrite <- log_append_id.
      assumption.
    +
      simpl in *.
      fold (log_append l ((repeat ([], []) n ++ ([], [write_1 n0 v]) :: repeat ([], []) (length l - S n)))).
      fold (@compute_log_append_write sort_read sort_write ( n) (write_1 n0 v) (length l)).
      rewrite IHl.
      apply eq_sym in H.
      apply Bool.andb_true_eq in H.
      destruct H.
      apply eq_sym in H0.
      rewrite <- H.
      reflexivity.
      apply eq_sym in H.
      apply Bool.andb_true_eq in H.
      destruct H.
      apply eq_sym in H0.
      rewrite <- H3.
      reflexivity.
      assumption.
Qed.


Lemma partial_perform_seq' :
  forall regs_content logs regx,
    (partial_perform_update'
       regs_content
       (logs ++ regx) =
                partial_perform_update'
                  (partial_perform_update' regs_content (logs))
                  (regx)) .

  intros.
  generalize dependent regs_content.
  induction logs.
  -
    intros.
    simpl.
    reflexivity.
  - intros.
    simpl.
    repeat rewrite IHlogs .
    destruct a.
    destruct (replace_nth n regs_content v).
    rewrite IHlogs; reflexivity.
    reflexivity.
    destruct (replace_nth n regs_content v).
    rewrite IHlogs; reflexivity.
    reflexivity.
    destruct (replace_nth n regs_content v).
    rewrite IHlogs; reflexivity.
    reflexivity.
    destruct (replace_nth n regs_content v).
    rewrite IHlogs; reflexivity.
    reflexivity.
Qed.


Lemma partial_perform_seq :
  forall regs_content logs regx,
    (partial_perform_update
       regs_content
       (logs ++ regx) =
                partial_perform_update
                  (partial_perform_update regs_content ( regx))
                  (logs)) .
  intros.
  unfold partial_perform_update.
  rewrite rev_app_distr.
  rewrite partial_perform_seq'.
  reflexivity.
Qed.

Lemma ppu_empty : forall l, (partial_perform_update' [] l) = [].
  induction l.
  cbv;reflexivity.
  simpl.
  destruct a;
  destruct n; simpl; assumption.
Qed.

Lemma write_disjoint :
  forall (log : WriteLog) v n1 n0 (l : list value),
    not(n1 = n0)->
    (extract_read0 (partial_perform_update l ([write_past n1 v] ++ log)) n0 =  extract_read0 (partial_perform_update l log) n0).
intros.
rewrite partial_perform_seq.
cbn.
destruct (nth_error (partial_perform_update l log) n1) eqn:?.
pose proof (prim_caract_nth_replace (partial_perform_update l log) n1 n0 v).
pose proof (replace_in_right_size (partial_perform_update l log) n1 v0 v Heqo).
destruct (replace_nth n1 (partial_perform_update l log) v) eqn:?.
pose proof (Nat.eqb_neq n1 n0) .
destruct H2.
specialize ( H3 H).
rewrite H3 in H0.
unfold extract_read0.
rewrite H0.
reflexivity.
contradiction.
pose proof (prim_caract_nth_replace (partial_perform_update l log) n1 n0 v).
pose proof (replace_in_right_size_none (partial_perform_update l log) n1  v Heqo).
destruct (replace_nth n1 (partial_perform_update l log) v) eqn:?.
pose proof (Nat.eqb_neq n1 n0) .
destruct H2.
specialize ( H3 H).
rewrite H3 in H0.
contradiction.
reflexivity.
Qed.


Lemma write_disjoint_1 :
  forall (log : WriteLog) v n1 n0 (l : list value),
    not(n1 = n0)->
    (extract_read0 (partial_perform_update l ([write_past_1 n1 v] ++ log)) n0 =  extract_read0 (partial_perform_update l log) n0).
  intros.
rewrite partial_perform_seq.
cbn.
destruct (nth_error (partial_perform_update l log) n1) eqn:?.
pose proof (prim_caract_nth_replace (partial_perform_update l log) n1 n0 v).
pose proof (replace_in_right_size (partial_perform_update l log) n1 v0 v Heqo).
destruct (replace_nth n1 (partial_perform_update l log) v) eqn:?.
pose proof (Nat.eqb_neq n1 n0) .
destruct H2.
specialize ( H3 H).
rewrite H3 in H0.
unfold extract_read0.
rewrite H0.
reflexivity.
contradiction.
pose proof (prim_caract_nth_replace (partial_perform_update l log) n1 n0 v).
pose proof (replace_in_right_size_none (partial_perform_update l log) n1  v Heqo).
destruct (replace_nth n1 (partial_perform_update l log) v) eqn:?.
pose proof (Nat.eqb_neq n1 n0) .
destruct H2.
specialize ( H3 H).
rewrite H3 in H0.
contradiction.
reflexivity.
Qed.

Lemma write_past_alone:
  forall (log : WriteLog) v n1 (l : list value),
    n1 < length l ->
    find_anywrite log n1 = false ->
    nth_error (partial_perform_update l ([write_past n1 v] ++ log)) n1 =
    nth_error (partial_perform_update l [write_past n1 v]) n1.
Proof.
  intros.
  rewrite partial_perform_seq.
  cbn.
  Search replace_nth.
  pose proof (nth_error_Some l n1).
  destruct H1.
  specialize (H2 H).
  destruct (nth_error l n1) eqn:?.
  pose proof (replace_in_right_size l n1 v0 v Heqo).
  destruct (replace_nth n1 l v) eqn:?.
  rewrite H3.
  pose proof (nth_error_Some (partial_perform_update l log) n1).
  destruct H4.
  rewrite ppu_preserves_length in H5.
  specialize (H5 H).
  destruct (nth_error (partial_perform_update l log) n1) eqn:?.
  pose proof (replace_in_right_size (partial_perform_update l log) n1 v1 v Heqo1).
  destruct (replace_nth n1 (partial_perform_update l log) v) eqn:?.
  rewrite H6.
  reflexivity.
  contradiction.
  contradiction.
  contradiction.
  contradiction.
Qed.

Lemma read_from : forall read0w l0 n read0r  ,
    nth_error (retire l0) n = Some (read0r, read0w) ->
    forall read1w  l n0  v0     (lengthGood :n0 < length l),
    nth_error l n0 = Some v0 ->
    find_write1_past read0w n0 = false ->
    no_double_write_aux (retire_write read0w) = true ->
    extract_read1
       (partial_perform_update
          l
          (retire_write read0w))
       read1w
       n0 =
     extract_read1
       l
       (read1w ++ read0w)
       n0.
  (* Par induction sur read1w, je crois que seul le cas de base est intéressant *)
  intros read0w l0 n read0r nth.
  assert ( exists read0w', read0w = retire_write read0w').
  unfold retire in nth.
  rewrite nth_error_nth_map in nth.
  unfold nth_map in nth.
  destruct (nth_error l0 n).
  inversion nth.
  eexists.
  reflexivity.
  inversion nth.
  destruct H as [read0w' eqread0w'].
  rewrite eqread0w'.
  clear eqread0w'.
  clear nth read0r l0 read0w.
  induction read1w.
  -
    simpl in *.
    intro.
    intros.
    induction read0w'; simpl in *.
    +
      intros.
      destruct l; simpl.
      cbv.
      reflexivity.
      cbv.
      reflexivity.
    +
      destruct a; simpl.
      destruct (n0 =? n1) eqn:?.
      {
        apply Nat.eqb_eq in Heqb.
        rewrite Heqb in *.
        clear Heqb.
        assert (nth_error (partial_perform_update l (write_past n1 v :: retire_write (retire_write read0w'))) n1 = nth_error (partial_perform_update l (write_past n1 v :: nil)) n1).
        apply eq_sym in H1.
        apply Bool.andb_true_eq in H1.
        destruct H1.
        apply Bool.negb_sym in H1.
        simpl in H1.
        change (write_past n1 v :: retire_write (retire_write read0w')) with ([write_past n1 v]++ retire_write (retire_write read0w')).
        erewrite write_past_alone.
        reflexivity.
        assumption.
        assumption.
        unfold extract_read0.
        rewrite H2.
        unfold partial_perform_update.
        simpl.
        destruct ( replace_nth n1 l v) eqn:?.
        *
          unfold extract_read0.
          pose proof replace_in l n1 v.
          rewrite Heqo in H3.
          assumption.
        *
          pose proof (replace_in_right_size l n1 v0 v H).
          rewrite Heqo in H3.
          contradiction.
      }
      {
        apply Nat.eqb_neq in Heqb.
        assert (extract_read0 (partial_perform_update l (write_past n1 v :: retire_write (retire_write read0w'))) n0 =  extract_read0 (partial_perform_update l (retire_write (retire_write read0w'))) n0).
        change (write_past n1 v :: retire_write (retire_write read0w')) with ([write_past n1 v]++ retire_write (retire_write read0w')).
        erewrite write_disjoint.
        reflexivity.
        apply not_eq_sym in Heqb.
        assumption.
        rewrite H2.
        rewrite IHread0w'.
        reflexivity.
        assumption.
        apply eq_sym in H1.
        apply Bool.andb_true_eq in H1.
        destruct H1.
        rewrite H3.
        reflexivity.
      }
      destruct (n0 =? n1) eqn:?.
      {
        apply Nat.eqb_eq in Heqb.
        rewrite Heqb in *.
        clear Heqb.
        assert (nth_error (partial_perform_update l (write_past n1 v :: retire_write (retire_write read0w'))) n1 = nth_error (partial_perform_update l (write_past n1 v :: nil)) n1).
        apply eq_sym in H1.
        apply Bool.andb_true_eq in H1.
        destruct H1.
        apply Bool.negb_sym in H1.
        simpl in H1.
        change (write_past n1 v :: retire_write (retire_write read0w')) with ([write_past n1 v]++ retire_write (retire_write read0w')).
        erewrite write_past_alone.
        reflexivity.
        assumption.
        assumption.
        unfold extract_read0.
        rewrite H2.
        unfold partial_perform_update.
        simpl.
        destruct ( replace_nth n1 l v) eqn:?.
        *
          unfold extract_read0.
          pose proof replace_in l n1 v.
          rewrite Heqo in H3.
          assumption.
        *
          pose proof (replace_in_right_size l n1 v0 v H).
          rewrite Heqo in H3.
          contradiction.
      }
      {
        apply Nat.eqb_neq in Heqb.
        assert (extract_read0 (partial_perform_update l (write_past n1 v :: retire_write (retire_write read0w'))) n0 =  extract_read0 (partial_perform_update l (retire_write (retire_write read0w'))) n0).
        change (write_past n1 v :: retire_write (retire_write read0w')) with ([write_past n1 v]++ retire_write (retire_write read0w')).
        erewrite write_disjoint.
        reflexivity.
        apply not_eq_sym in Heqb.
        assumption.
        rewrite H2.
        rewrite IHread0w'.
        reflexivity.
        assumption.
        apply eq_sym in H1.
        apply Bool.andb_true_eq in H1.
        destruct H1.
        rewrite H3.
        reflexivity.
      }
      destruct (n0 =? n1) eqn:?.
      {
        apply Nat.eqb_eq in Heqb.
        rewrite Heqb in *.
        simpl in H0.
        inversion H0.
      }
      {
        apply Nat.eqb_neq in Heqb.
        assert (extract_read0 (partial_perform_update l (write_past_1 n1 v :: retire_write (retire_write read0w'))) n0 =  extract_read0 (partial_perform_update l (retire_write (retire_write read0w'))) n0).
        change (write_past_1 n1 v :: retire_write (retire_write read0w')) with ([write_past_1 n1 v]++ retire_write (retire_write read0w')).
        erewrite write_disjoint_1.
        reflexivity.
        apply not_eq_sym in Heqb.
        assumption.
        rewrite H2.
        rewrite IHread0w'.
        reflexivity.
        assumption.
        apply eq_sym in H1.
        apply Bool.andb_true_eq in H1.
        destruct H1.
        rewrite H3.
        reflexivity.
      }
      destruct (n0 =? n1) eqn:?.
      {
        apply Nat.eqb_eq in Heqb.
        rewrite Heqb in *.
        simpl in H0.
        inversion H0.
      }
      {
        apply Nat.eqb_neq in Heqb.
        assert (extract_read0 (partial_perform_update l (write_past_1 n1 v :: retire_write (retire_write read0w'))) n0 =  extract_read0 (partial_perform_update l (retire_write (retire_write read0w'))) n0).
        change (write_past_1 n1 v :: retire_write (retire_write read0w')) with ([write_past_1 n1 v]++ retire_write (retire_write read0w')).
        erewrite write_disjoint_1.
        reflexivity.
        apply not_eq_sym in Heqb.
        assumption.
        rewrite H2.
        rewrite IHread0w'.
        reflexivity.
        assumption.
        apply eq_sym in H1.
        apply Bool.andb_true_eq in H1.
        destruct H1.
        rewrite H3.
        reflexivity.
      }
  -
    intros.
    simpl in *.
    destruct a.
    all:erewrite IHread1w.
    all: try reflexivity; try assumption.
    all: try exact H.
    all: exact H0.
Qed.

Lemma atomic_oraat : forall a nb_scopes regs_content l0 l1 v new_s
                       (no_double_write_l0: no_double_write (log_append (retire l0) l1) = true)
                       (length_regs: length regs_content = nb_scopes)
                       (length_l0: length (retire l0) = nb_scopes)
                       (length_l1 : length l1 = nb_scopes)
                       m d
                       (hyp_av: atomic_av regs_content
                                         {|Reg:= log_append (retire l0) l1; Met := m; dynamicOrder :=d |}
                                         a = Some (v,new_s))
                      ,
    exists newlog,
      length newlog = nb_scopes /\
      Reg new_s = log_append (log_append (retire l0) l1) newlog /\
      no_double_write (log_append (log_append (retire l0) l1) newlog) = true /\
      atomic_av (perform_update regs_content (retire l0))
                {|Reg:= l1; Met := m; dynamicOrder := d|}
                a = Some (v,{|Reg:= log_append l1 newlog; Met:= m; dynamicOrder := d|})
.
  induction a; simpl.
  - (* avlet *)
    intros.
    match goal with
    | [ H0: match ?g with _=>_ end = _ |- _ ] => destruct g eqn:av
    end.
    destruct p.
    specialize (IHa nb_scopes regs_content (l0) l1 v0 s no_double_write_l0 length_regs length_l0 length_l1 m d av).
    destruct_res IHa.
    rewrite perform_IHa.
    rewrite (expand_state s) in hyp_av.
    pose proof (atomic_only_reg _ _ _ _ _ _ _ av) as carac_trash.
    rewriteall carac_trash hyp_av.
    rewrite reg_IHa in hyp_av.
    rewrite <- permutation_append in hyp_av.
    assert (length (log_append l1 element_IHa) = nb_scopes) as length_app.
    Hint Rewrite map_length combine_length :Length.
    unfold log_append.
    (* Ltac for lengths *)
    autorewrite  with Length using try rewrite !length_l1,!length_IHa, Nat.min_id; try unfold log_append; try congruence.
    (* apply no_double_append_l  in no_double_write_l0. *)
    rewrite <- permutation_append in nodoublewrite_IHa.
    specialize (H v0 nb_scopes regs_content l0  (log_append l1 element_IHa) v new_s nodoublewrite_IHa (* no_double_write_l0 *) length_regs length_l0 length_app m d hyp_av).
    destruct_res H.
    eexists.
    split.
    Focus 2.
    split.
    rewrite reg_H.
    rewrite  permutation_append at 1.
    rewrite permutation_append.
    f_equal.
    rewrite permutation_append.
    rewrite permutation_append
            in nodoublewrite_H.
    rewrite nodoublewrite_H.
    split.
    reflexivity.
    rewrite perform_H.
    rewrite permutation_append.
    reflexivity.
    unfold log_append.
    autorewrite  with Length using try rewrite !length_IHa, !length_H, Nat.min_id; try congruence.
    inversion hyp_av.
  - (* avif *)
    intros.
    repeat match goal with
           | [ H0: match ?g with _=>_ end = _ |- _ ] => let name := fresh "term" in destruct g eqn:name
           end; try congruence.
    move IHa1 at bottom.
    specialize (IHa1 nb_scopes regs_content l0 l1 (Bool true) s no_double_write_l0 length_regs length_l0 length_l1 m d term).
    destruct_res IHa1.
    rewrite perform_IHa1.
    rewrite (expand_state s) in hyp_av.
    pose proof (atomic_only_reg _ _ _ _ _ _ _ term) as met_trash.
    rewriteall met_trash  hyp_av.                      (* apply beq_nat_true in Heqb; *)
    rewrite reg_IHa1 in hyp_av.
    rewrite <- permutation_append in hyp_av.
    assert (length (log_append l1 element_IHa1) = nb_scopes ) as length_app.
    unfold log_append.
    (* Ltac for lengths *)
    autorewrite  with Length using try rewrite !length_l1,!length_IHa1, Nat.min_id; try unfold log_append; try congruence.
    rewrite <- permutation_append in nodoublewrite_IHa1.
    specialize (IHa2 nb_scopes regs_content l0 (log_append l1 element_IHa1) v new_s nodoublewrite_IHa1 length_regs length_l0 length_app m d hyp_av ).
    destruct_res IHa2.
    eexists.
    split.
    Focus 2.
    split.
    rewrite reg_IHa2.
    rewrite  permutation_append at 1.
    rewrite permutation_append.
    f_equal.
    rewrite permutation_append.
    rewrite permutation_append
            in nodoublewrite_IHa2.
    rewrite nodoublewrite_IHa2.
    split.
    reflexivity.
    rewrite permutation_append.
    exact perform_IHa2.
    unfold log_append.
    autorewrite with Length.
    repeat (autorewrite  with Length; rewrite ?length_l1,?length_IHa1, ?length_IHa2, ?Nat.min_id; try unfold log_append; try congruence).
    inversion hyp_av.
    specialize (IHa1 nb_scopes regs_content l0 l1 (Bool false) s no_double_write_l0 length_regs length_l0 length_l1 m d term).
    destruct_res IHa1.
    rewrite perform_IHa1.
    rewrite (expand_state s) in hyp_av.
    pose proof (atomic_only_reg _ _ _ _ _ _ _ term) as met_trash.
    rewriteall met_trash  hyp_av.
    rewrite reg_IHa1 in hyp_av.
    rewrite <- permutation_append in hyp_av.
    eexists.
    split.
    Focus 2.
    split.
    rewrite <- H1.
    rewrite reg_IHa1.
    f_equal.
    rewrite nodoublewrite_IHa1.
    split.
    reflexivity.
    reflexivity.
    repeat (autorewrite  with Length; rewrite ?length_l1,?length_IHa1, ?length_IHa2, ?Nat.min_id; try unfold log_append; try congruence).
  - (* avread *)
    intros.
    repeat match goal with
           | [ H0: match ?g with _=>_ end = _ |- _ ] => let name := fresh "term" in destruct g eqn:name
           end; try congruence.
    destruct (nth_error_append _ _ _ _ term) as [read0 [read1 [read1_eq [read0_eq read_inv]]]].

    rewrite read1_eq.
    unfold perform_update.
    pose proof (read_n_from_perform l0 n nb_scopes regs_content l read0).
    rewrite H by assumption.
    destruct read1 as [read1r read1w].
    destruct read0 as [read0r read0w].
    destruct p as [pread pwrite].
    simpl in *.
    inversion read_inv.
    rewrite H1 in term2.
    rewrite H2 in term1.
    rewrite H2 in term3.
    rewrite (find_write_past_morphism read1w read0w n0) in term1 .
    rewrite (find_forward_morphism read1r read0r n0) in term2 .
    rewrite (find_write1_morphism read1w read0w n0) in term3 .
    apply Bool.orb_false_elim in term1.
    destruct term1 as [term1_read1w term1_read0w].
    apply Bool.orb_false_elim in term2.
    destruct term2 as [term2_read1r term2_read0r].
    apply Bool.orb_false_elim in term3.
    destruct term3 as [term3_read1w term3_read0w].
    rewrite term1_read1w; try trivial.
    rewrite term2_read1r; try trivial.
    rewrite term3_read1w; try trivial.
    pose proof (replacing_log_append_is_appending_read _ _ _ _ _ _ term  term4) as replacing_ctx.
    destruct replacing_ctx as [element_logctx replacing_ctx].
    destruct replacing_ctx as [replacing_ctx length_ctx].
    inversion hyp_av.
    simpl.
    rewrite  replacing_ctx.
    eexists.
    repeat split.
    rewrite length_ctx.
    unfold log_append.
    rewrite map_length.
    rewrite combine_length.
    rewrite length_l0, length_l1, Nat.min_id.
    reflexivity.
    (* we just added a read *)
    eapply read_preserve_no_double_write; try assumption.
    exact term.
    exact term4.
    exact replacing_ctx.
    destruct (replace_nth n l1 (read n0 :: read1r, read1w)) eqn: replace_inl1.
    pose proof (replacing_log_append_is_appending_read n l1 (read n0) read1r read1w l3 read1_eq replace_inl1) as replace_nl1.
    destruct replace_nl1 as [elReplacenl1 replace_nl1].
    destruct replace_nl1 as [replace_nl1 length_nl1].
    rewrite replace_nl1 in replace_inl1.
    rewrite replace_nl1.
    rewrite replacing_ctx in term4.
    rewrite H1 in term4.
    rewrite H2 in term4.
    move term4 at bottom.
    move term at bottom.
    pose proof (replace_consistent l1 (retire l0) (read n0) n read1r read1w read0r read0w  elReplacenl1).
    rewrite length_nl1 in H0.
    unfold log_append at 1 in H0.
    repeat (autorewrite  with Length in H0; rewrite ?length_regs, ?length_l0, ?length_l1, ?length_ctx, ?Nat.min_id in H0).
    rewrite H1, H2 in term.
    specialize (H0 eq_refl eq_refl read1_eq read0_eq term replace_inl1).
    rewrite H0 in term4.
    inversion term4.
    pose proof (log_append_injR (log_append (retire l0) l1) elReplacenl1 element_logctx).
    rewrite ?length_regs, ?length_l0, ?length_l1, ?length_ctx, ?Nat.min_id in H5.
    unfold log_append at 1 in H5.
    unfold log_append at 1 in H5.
    repeat (autorewrite  with Length in H5; rewrite ?length_regs, ?length_l0, ?length_l1, ?length_ctx, ?length_nl1 , ?Nat.min_id in H5).
    specialize (H5 eq_refl eq_refl H6).
    rewrite H5.
    rewrite (read_when_not_updated).
    rewrite term5.
    rewrite H3.
    reflexivity.
    rewrite <- (retired_retired_write l0 n read0r read0w read0_eq).
    assumption.
    rewrite <- (retired_retired_write l0 n read0r read0w read0_eq).
    assumption.
    simpl.
    pose proof (replace_in_right_size l1 n ( (read1r, read1w)) (read n0 :: read1r, read1w) read1_eq).
    rewrite replace_inl1 in H0.
    contradiction.
  - (* avforward require more lemma than avread but similar *)
    intros.
    repeat match goal with
           | [ H0: match ?g with _=>_ end = _ |- _ ] => let name := fresh "term" in destruct g eqn:name
           end; try congruence.
    pose proof (nth_error_append _ _ _ _ term) as break_read.
    destruct break_read as [read0 break_read].
    destruct break_read as [read1 break_read].
    destruct break_read as [read1_eq break_read].
    destruct break_read as [read0_eq read_inv].
    rewrite read1_eq.
    unfold perform_update.
    pose proof (read_n_from_perform l0 n nb_scopes regs_content l read0).
    rewrite H by assumption.
    destruct read1 as [read1r read1w].
    destruct read0 as [read0r read0w].
    (* assert (exists read0w, read0w'=   read0w). *)
    (* eexists. *)
    (* instantiate (1:=   read0w'). *)
    (* rewrite rev _involutive. *)
    (* reflexivity. *)
    (* destruct H0 as [read0w eqread0w]. *)
    (* rewrite eqread0w in *. *)
    destruct p as [pread pwrite].
    simpl in *.
    inversion read_inv.
    pose proof (ppu_preserves_nth_error
                  l
                  (partial_perform_update l
                                          (map
                                             (fun x : sort_write =>
                                                match x with
                                                | write_0 n1 v2 | write_past n1 v2 => write_past n1 v2
                                                | write_1 n1 v2 | write_past_1 n1 v2 => write_past_1 n1 v2
                                                end) (  read0w))) n0 v0 term1 ).
    rewrite ppu_preserves_length in H0 .
    specialize (H0 eq_refl).
    destruct H0 as [foo thisregsexists].
    rewrite thisregsexists.
    rewrite H2 in term2.
    rewrite (find_write1_past_morphism ( read1w) (  read0w) n0) in term2 .
    apply Bool.orb_false_elim in term2.
    destruct term2 as [term2_read1w term2_read0w].
    rewrite term2_read1w.
    pose proof (replacing_log_append_is_appending_read _ _ _ _ _ _ term  term3) as replacing_ctx.
    destruct replacing_ctx as [element_logctx replacing_ctx].
    destruct replacing_ctx as [replacing_ctx length_ctx].
    inversion hyp_av.
    simpl.
    rewrite  replacing_ctx.
    eexists.
    repeat split.
    rewrite length_ctx.
    unfold log_append.
    rewrite map_length.
    rewrite combine_length.
    rewrite length_l0, length_l1, Nat.min_id.
    reflexivity.
    (* element_logctx just adds a forward *)
    eapply forward_preserve_no_double_write; try assumption.
    exact term.
    exact term3.
    exact replacing_ctx.
    destruct (replace_nth n l1 (forward n0 :: read1r, read1w)) eqn: replace_inl1.
    pose proof (replacing_log_append_is_appending_read n l1 (forward n0) read1r (read1w) l3 read1_eq replace_inl1) as replace_nl1.
    destruct replace_nl1 as [elReplacenl1 replace_nl1].
    destruct replace_nl1 as [replace_nl1 length_nl1].
    rewrite replace_nl1 in replace_inl1.
    rewrite replace_nl1.
    rewrite replacing_ctx in term3.
    rewrite H1 in term3.
    rewrite H2 in term3.
    pose proof (replace_consistent l1 (retire l0) (forward n0) n read1r (read1w) read0r (  read0w)  elReplacenl1).
    rewrite length_nl1 in H0.
    unfold log_append at 1 in H0.
    repeat (autorewrite  with Length in H0; rewrite ?length_regs, ?length_l0, ?length_l1, ?length_ctx, ?Nat.min_id in H0).
    rewrite H1, H2 in term.
    specialize (H0 eq_refl eq_refl read1_eq read0_eq term replace_inl1).
    rewrite H0 in term3.
    inversion term3.
    pose proof (log_append_injR (log_append (retire l0) l1) elReplacenl1 element_logctx).
    rewrite ?length_regs, ?length_l0, ?length_l1, ?length_ctx, ?Nat.min_id in H5.
    unfold log_append at 1 in H5.
    unfold log_append at 1 in H5.
    repeat (autorewrite  with Length in H5; rewrite ?length_regs, ?length_l0, ?length_l1, ?length_ctx, ?length_nl1 , ?Nat.min_id in H5).
    specialize (H5 eq_refl eq_refl H6).
    rewrite H5.
    rewrite H2 in term4.
    assert
      (extract_read1
         (partial_perform_update
            l
            (retire_write read0w))
         read1w
         n0 =
       extract_read1
         l
         (read1w ++ read0w)
         n0).
    erewrite read_from.
    reflexivity.
    exact read0_eq.
    pose proof (nth_error_Some l n0) as lengthgoodbuild.
    destruct lengthgoodbuild as [lengthgood1 lengthgood2].
    rewrite term1 in  lengthgood1.
    assert (not(Some v0 = None)) as absurdity.
    congruence.
    specialize (lengthgood1 absurdity).
    exact lengthgood1.
    exact term1.
    assumption.
    Search no_double_write_aux.
    eapply no_double_on_every_reg.
    Search no_double_write.
    eapply no_double_append_l.
    2:{
      exact no_double_write_l0.
    }
    rewrite length_l0, length_l1.
    reflexivity.
    exact read0_eq.
    fold (retire_write read0w).
    rewrite H7.
    rewrite term4.
    rewrite H3.
    reflexivity.
    simpl.
    pose proof (replace_in_right_size l1 n ( (read1r, read1w)) (forward n0 :: read1r, read1w) read1_eq).
    rewrite replace_inl1 in H0.
    contradiction.
  - (* avwrite very similar to read *)
    intros.
    repeat match goal with
           | [ H0: match ?g with _=>_ end = _ |- _ ] => let name := fresh "term" in destruct g eqn:name
           end; try congruence.
    pose proof (nth_error_append _ _ _ _ term) as break_read.
    destruct break_read as [read0 break_read].
    destruct break_read as [read1 break_read].
    destruct break_read as [read1_eq break_read].
    destruct break_read as [read0_eq read_inv].
    rewrite read1_eq.
    unfold perform_update.
    destruct read1 as [read1r read1w].
    destruct read0 as [read0r read0w].
    destruct p as [pread pwrite].
    simpl in *.
    inversion read_inv.
    clear read_inv.
    rewrite H0 in *.
    rewrite H1 in *.
    rewrite (find_forward_morphism read1r read0r n0) in term0 .
    apply Bool.orb_false_elim in term0.
    destruct term0 as [term0_read1r term0_read0r].
    rewrite (find_anywrite_morphism read1w read0w n0) in term1.
    apply Bool.orb_false_elim in term1.
    destruct term1 as [term1_read1w term1_read0w].
    rewrite term0_read1r.
    rewrite term1_read1w.
    pose proof (replacing_log_append_is_appending_write _ _ _ _ _ _ term term2) as replace_ctx.
    destruct replace_ctx as [element_logctx replacing_ctx].
    destruct replacing_ctx as [replacing_ctx length_ctx].
    inversion hyp_av.
    rewrite replacing_ctx in *.
    simpl in *.
    eexists.
    repeat split.
    rewrite length_ctx.
    unfold log_append.
    rewrite map_length.
    rewrite combine_length.
    rewrite length_l0, length_l1, Nat.min_id.
    reflexivity.
    (* Important no double_write *)
    erewrite write_safe_double.
    reflexivity.
    assumption.
    exact term.
    exact term1_read1w.
    exact term1_read0w.
    exact term2.
    rewrite length_ctx.
    reflexivity.
    destruct (replace_nth n l1 (read1r, write_0 n0  v:: read1w)) eqn: replace_inl1.
    pose proof (replacing_log_append_is_appending_write n l1 (write_0 n0 v) read1r read1w _ read1_eq replace_inl1) as replace_nl1.
    destruct replace_nl1 as [elReplacenl1 replace_nl1].
    destruct replace_nl1 as [replace_nl1 length_nl1].
    rewrite replace_nl1 in replace_inl1.
    rewrite replace_nl1.
    pose proof (replace_consistent_write l1 (retire l0) (write_0 n0 v) n read1r read1w read0r read0w  elReplacenl1).
    rewrite length_nl1 in H.
    unfold log_append at 1 in H.
    repeat (autorewrite  with Length in H0; rewrite ?length_regs, ?length_l0, ?length_l1, ?length_ctx, ?Nat.min_id in H).
    specialize (H eq_refl eq_refl read1_eq read0_eq term replace_inl1).
    rewrite H in term2.
    inversion term2.
    pose proof (log_append_injR (log_append (retire l0) l1) elReplacenl1 element_logctx).
    rewrite ?length_regs, ?length_l0, ?length_l1, ?length_ctx, ?Nat.min_id in H4.
    unfold log_append at 1 in H4.
    unfold log_append at 1 in H4.
    repeat (autorewrite  with Length in H4; rewrite ?length_regs, ?length_l0, ?length_l1, ?length_ctx, ?length_nl1 , ?Nat.min_id in H4).
    specialize (H4 eq_refl eq_refl H5).
    rewrite H4.
    reflexivity.
    simpl.
    pose proof (replace_in_right_size l1 n ( (read1r, read1w)) (read1r, write_0 n0 v:: read1w) read1_eq).
    rewrite replace_inl1 in H.
    contradiction.
  - (* avwrite1 very similar to avread and avwrite *)
    intros.
    repeat match goal with
           | [ H0: match ?g with _=>_ end = _ |- _ ] => let name := fresh "term" in destruct g eqn:name
           end; try congruence.
    pose proof (nth_error_append _ _ _ _ term) as break_read.
    destruct break_read as [read0 break_read].
    destruct break_read as [read1 break_read].
    destruct break_read as [read1_eq break_read].
    destruct break_read as [read0_eq read_inv].
    rewrite read1_eq.
    destruct read1 as [read1r read1w].
    destruct read0 as [read0r read0w].
    destruct p as [pread pwrite].
    simpl in *.
    inversion read_inv.
    clear read_inv.
    rewrite H0 in *.
    rewrite H1 in *.
    rewrite (find_write1_morphism read1w read0w n0) in term0.
    apply Bool.orb_false_elim in term0.
    destruct term0 as [term0_read1w term0_read0w].
    rewrite term0_read1w.
    pose proof (replacing_log_append_is_appending_write _ _ _ _ _ _ term term1) as replace_ctx.
    destruct replace_ctx as [element_logctx replacing_ctx].
    destruct replacing_ctx as [replacing_ctx length_ctx].
    inversion hyp_av.
    rewrite replacing_ctx in *.
    simpl in *.
    eexists.
    repeat split.
    rewrite length_ctx.
    unfold log_append.
    rewrite map_length.
    rewrite combine_length.
    rewrite length_l0, length_l1, Nat.min_id.
    reflexivity.
    (* Important no double write *)
    erewrite write1_safe_double.
    reflexivity.
    assumption.
    exact term.
    exact term0_read1w.
    exact term0_read0w.
    exact term1.
    repeat (autorewrite  with Length ; rewrite ?length_regs, ?length_l0, ?length_l1, ?length_ctx, ?Nat.min_id).
    reflexivity. 
    destruct (replace_nth n l1 (read1r, write_1 n0  v:: read1w)) eqn: replace_inl1.
    pose proof (replacing_log_append_is_appending_write n l1 (write_1 n0 v) read1r read1w _ read1_eq replace_inl1) as replace_nl1.
    destruct replace_nl1 as [elReplacenl1 replace_nl1].
    destruct replace_nl1 as [replace_nl1 length_nl1].
    rewrite replace_nl1 in replace_inl1.
    rewrite replace_nl1.
    pose proof (replace_consistent_write l1 (retire l0) (write_1 n0 v) n read1r read1w read0r read0w  elReplacenl1).
    rewrite length_nl1 in H.
    unfold log_append at 1 in H.
    repeat (autorewrite  with Length in H0; rewrite ?length_regs, ?length_l0, ?length_l1, ?length_ctx, ?Nat.min_id in H).
    specialize (H eq_refl eq_refl read1_eq read0_eq term replace_inl1).
    rewrite H in term1.
    inversion term1.
    pose proof (log_append_injR (log_append (retire l0) l1) elReplacenl1 element_logctx).
    rewrite ?length_regs, ?length_l0, ?length_l1, ?length_ctx, ?Nat.min_id in H4.
    unfold log_append at 1 in H4.
    unfold log_append at 1 in H4.
    repeat (autorewrite  with Length in H4; rewrite ?length_regs, ?length_l0, ?length_l1, ?length_ctx, ?length_nl1 , ?Nat.min_id in H4).
    specialize (H4 eq_refl eq_refl H5).
    rewrite H4.
    reflexivity.
    simpl.
    pose proof (replace_in_right_size l1 n ( (read1r, read1w)) (read1r, write_1 n0 v:: read1w) read1_eq).
    rewrite replace_inl1 in H.
    contradiction.
  - (* avlift similar than avif/avlet but easier *)
    intros.
    repeat match goal with
           | [ H0: match ?g with _=>_ end = _ |- _ ] => let name := fresh "term" in destruct g eqn:name
           end; try congruence.
    move IHa1 at bottom.
    specialize (IHa1 nb_scopes regs_content l0 l1 _ s no_double_write_l0 length_regs length_l0 length_l1 m d term).
    destruct_res IHa1.
    rewrite perform_IHa1.
    inversion hyp_av.
    rewrite (expand_state s) in term1.
    pose proof (atomic_only_reg _ _ _ _ _ _ _ term) as met_trash.
    rewriteall met_trash  term1.                      (* apply beq_nat_true in Heqb; *)
    rewrite reg_IHa1 in term1.
    rewrite <- permutation_append in term1.
    rewrite H0.
    assert (length (log_append l1 element_IHa1) = nb_scopes ) as length_app.
    unfold log_append.
    (* Ltac for lengths *)
    autorewrite  with Length using try rewrite !length_l1,!length_IHa1, Nat.min_id; try unfold log_append; try congruence.
    rewrite <- permutation_append in nodoublewrite_IHa1.
    specialize (IHa2 nb_scopes regs_content l0 (log_append l1 element_IHa1) _ s0 nodoublewrite_IHa1 length_regs length_l0 length_app m d  term1 ).
    destruct_res IHa2.
    eexists.
    split.
    Focus 2.
    split.
    rewrite <- H1.
    rewrite reg_IHa2.
    rewrite  permutation_append at 1.
    rewrite permutation_append.
    f_equal.
    rewrite permutation_append.
    rewrite permutation_append in nodoublewrite_IHa2.
    rewrite nodoublewrite_IHa2.
    split.
    reflexivity.
    rewrite permutation_append.
    rewrite perform_IHa2.
    rewrite H0.
    reflexivity.
    unfold log_append.
    autorewrite with Length.
    repeat (autorewrite  with Length; rewrite ?length_l1,?length_IHa1, ?length_IHa2, ?Nat.min_id; try unfold log_append; try congruence).
  - (* avblock lol *)
    intros.
    inversion hyp_av.
  - (* avempty *)
    intros.
    inversion hyp_av.
    eexists.
    repeat split.
    Focus 2.
    instantiate (1:= repeat ([],[]) (length (log_append (retire l0) l1))).
    simpl in *.
    pose proof (log_append_id (log_append (retire l0) l1)).
    rewrite Nat.sub_0_r in H.
    rewrite <- H.
    reflexivity.
    rewrite repeat_length.
    unfold log_append.
    autorewrite with Length.
    repeat (autorewrite  with Length; rewrite ?length_l0, ?length_l1, ?Nat.min_id; try unfold log_append; try congruence).
    pose proof ( log_append_id (log_append (retire l0) l1)) as ll.
    rewrite Nat.sub_0_r in ll.
    rewrite <- ll.
    exact no_double_write_l0.
    unfold log_append at 2.
    repeat (autorewrite  with Length; rewrite ?length_l0, ?length_l1, ?Nat.min_id; try congruence).
    rewrite <- length_l1.
    pose proof (log_append_id l1).
    rewrite Nat.sub_0_r in H.
    rewrite <- H.
    reflexivity.
Qed.


Lemma find_anywrite_preserve_retire_write : forall l,
    find_anywrite l = find_anywrite (retire_write l).
Proof.
  induction l.
  -
    cbv. reflexivity.
  -
    simpl.
    destruct a;
    rewrite IHl;
    reflexivity.
Qed.


Lemma find_write1_preserve_retire_write : forall l,
    find_write1 l = find_write1 (retire_write l).
Proof.
  induction l.
  -
    cbv. reflexivity.
  -
    simpl.
    destruct a;
    rewrite IHl;
    reflexivity.
Qed.

Lemma remove_retire_no_double_write_aux_l : forall a ,
      (no_double_write_aux
                (retire_write (a)) = no_double_write_aux
                ((a))).
induction a.
-
  simpl.
  reflexivity.
-
  simpl.
  destruct a; try(
  intros;
  rewrite IHa;
  rewrite <- find_anywrite_preserve_retire_write;
  reflexivity);
  try(
  intros;
  rewrite IHa;
  rewrite <- find_write1_preserve_retire_write;
  reflexivity).
Qed.


Lemma retire_write_morphism : forall l l', retire_write (l++l') = retire_write l ++ retire_write l'.
induction l.
-
  simpl.
  reflexivity.
-
  intros.
  simpl.
  f_equal.
  apply IHl.
Qed.

Lemma no_double_write_invariant_retire : forall l, no_double_write l = no_double_write (retire l).
intros.
induction l.
-
  cbv.
  reflexivity.
-
  simpl.
  rewrite IHl.
  rewrite remove_retire_no_double_write_aux_l.
  reflexivity.
Qed.


Lemma one_update_fail_both_fail : forall {A} a0 (l: list A)  n v n0 v0, (replace_nth n a0 v = Some l -> replace_nth n0 a0 v0 = None -> replace_nth n0 l v0 = None).
induction a0.
-
  simpl in *.
  intros.
  destruct n; simpl in *; inversion H.
-
  intros. 
  destruct n;
  destruct n0;
  simpl in *.
  inversion H0.
  inversion H.
  destruct (replace_nth n0 a0 v0) eqn:?.
  inversion H0.
  reflexivity.
  inversion H0.
  destruct (replace_nth n a0 v) eqn:?.
  destruct (replace_nth n0 a0 v0) eqn:?.
  inversion H0.
  inversion H.
  erewrite IHa0.
  reflexivity.
  exact Heqo.
  exact Heqo0.
  inversion H.
Qed.


Lemma commute_replace :
forall {A} (a0 l0 l: list A) n n0 v v0 ,
 ( not ( n = n0) -> replace_nth n a0 v = Some l -> replace_nth n0 a0 v0 = Some l0 ->
             replace_nth n l0 v = replace_nth n0 l v0).
  simpl.
  induction a0.
  -
    intros.
    destruct n.
    simpl in *.
    inversion H0.
    simpl in *.
    inversion H0.
  -
    intros.
    destruct n, n0.
    specialize (H eq_refl).
    contradiction.
    simpl in *.
    inversion H0.
    clear H0.
    destruct (replace_nth n0 a0 v0) eqn:?.
    inversion H1.
    clear H1.
    reflexivity.
    inversion H1.
    simpl in *.
    inversion H1.
    destruct (replace_nth n a0 v) eqn:?.
    inversion H0.
    reflexivity.
    inversion H0.
    simpl in *.
    destruct (replace_nth  n a0 v) eqn:?.
    destruct (replace_nth n0 a0 v0) eqn:?.
    inversion H0.
    inversion H1.
    rewrite  Nat.succ_inj_wd_neg in H.
    erewrite IHa0.
    Focus 2.
    exact H.
    Focus 2.
    exact Heqo.
    Focus 2.
    exact Heqo0.
    reflexivity.
    inversion H1.
    inversion H0.
Qed.


Lemma commute_exists :
forall {A} (a0 l0 l: list A) n n0 v v0 ,
 ( not ( n = n0) -> replace_nth n a0 v = Some l -> replace_nth n0 a0 v0 = Some l0 ->
             exists lnew, replace_nth n l0 v = Some lnew ).
  simpl.
  induction a0.
  -
    intros.
    destruct n.
    simpl in *.
    inversion H0.
    simpl in *.
    inversion H0.
  -
    intros.
    destruct n, n0.
    specialize (H eq_refl).
    contradiction.
    simpl in *.
    inversion H0.
    clear H0.
    destruct (replace_nth n0 a0 v0) eqn:?.
    inversion H1.
    clear H1.
    eexists.
    reflexivity.
    inversion H1.
    simpl in *.
    inversion H1.
    destruct (replace_nth n a0 v) eqn:?.
    inversion H0.
    eexists.
    reflexivity.
    inversion H0.
    simpl in *.
    destruct (replace_nth  n a0 v) eqn:?.
    destruct (replace_nth n0 a0 v0) eqn:?.
    inversion H0.
    inversion H1.
    rewrite  Nat.succ_inj_wd_neg in H.
    clear H1 H0.
    specialize (IHa0 l2 l1 n n0 v v0 H Heqo Heqo0).
    destruct IHa0.
    rewrite H0.
    eexists.
    reflexivity.

    inversion H1.
    inversion H0.
Qed.


Lemma find_anywrite_commute :
  forall p0 p n,
    (find_anywrite (p ++ p0) n) = find_anywrite (p0  ++ p ) n.
  induction p0.
  -
    simpl.
    intros.
    rewrite app_nil_r.
    reflexivity.
  -
    simpl.
    (* destruct a *)
    induction p.
    +
      simpl.
      rewrite app_nil_r.
      reflexivity.
    +
      simpl.
      intros.
      rewrite IHp.
      rewrite <- (IHp0 (a0::p)).
      simpl.
      destruct a , a0 ;      rewrite IHp0;
        destruct (find_anywrite (p0 ++ p) n);
        destruct (n =? n1);
        destruct (n =? n0); cbv; reflexivity.
Qed.


Lemma perform_update_seq : forall regs_content logs newlog_atomic,
    no_double_write (log_append (logs) (newlog_atomic)) = true ->
   perform_update regs_content (log_append ( logs) ( newlog_atomic))
   =
   perform_update (perform_update regs_content ( logs)) ( newlog_atomic).
  (* unfold perform_update. *)
  (* unfold log_append. *)
  induction regs_content.
  -
    cbv; trivial.
  -
    intros.
    simpl.
    destruct logs eqn:?.
    cbv; trivial.
    destruct newlog_atomic eqn:?.
    cbv.
    reflexivity.
    unfold perform_update.
    simpl.
    fold (log_append l l0).
    fold (perform_update regs_content (log_append l l0)).
    fold (perform_update regs_content l).
    fold (perform_update (perform_update regs_content l) ( l0)).
    f_equal.
    erewrite partial_perform_seq.
    fold (log_append l l0).
    trivial.
    simpl.
    rewrite IHregs_content.
    reflexivity.
    simpl in *.
    fold (log_append l l0) in H.
    apply eq_sym in H.
    apply Bool.andb_true_eq in H.
    destruct H.
    apply eq_sym in H0.
    exact H0.
Qed.



Lemma ppu_invariant_retire' : forall l a0,
    partial_perform_update' a0 l = partial_perform_update' a0 (retire_write l).
Proof.

induction l.
-
  simpl.
  reflexivity.
-
  simpl in *.
  intros.
  destruct a;
  destruct (replace_nth n a0 v);
  rewrite IHl; reflexivity.
Qed.


Lemma ppu_invariant_retire : forall l a0,
    partial_perform_update a0 l = partial_perform_update a0 (retire_write l).
Proof.
  intros.
  unfold partial_perform_update.
  rewrite ppu_invariant_retire'.
  rewrite rev_retire.
  reflexivity.
Qed.

Lemma perform_update_invariant_retire : forall logs regs_content,
   perform_update regs_content logs
   =
   perform_update regs_content (retire logs).
induction logs.
-
  simpl.
  reflexivity.
-
  simpl.
  induction regs_content.
  +
    unfold perform_update.
    simpl.
    reflexivity.
  +
    unfold perform_update.
    simpl.
    fold (perform_update regs_content logs).
    fold (perform_update regs_content (retire logs)).
    rewrite IHlogs.
    f_equal.
    rewrite ppu_invariant_retire.
    reflexivity.
Qed.

Lemma retire_push_retire_update:
  forall logs newlog_atomic : list (ReadLog * WriteLog),
    retire (log_append (retire logs) newlog_atomic) = log_append (retire logs) (retire newlog_atomic).
Proof.
  induction logs.
  -
    simpl.
    destruct newlog_atomic.
    cbv.
    reflexivity.
    cbv.
    reflexivity.
  -
    simpl in *.
    intros.
    destruct newlog_atomic.
    cbv.
    reflexivity.
    simpl.
    unfold log_append.
    simpl.
    fold (log_append (retire logs) newlog_atomic).
    fold (log_append (retire logs) (retire newlog_atomic)).
    rewrite IHlogs.
    f_equal.
    f_equal.
    unfold retire_write.
    rewrite map_app.
    fold (retire_write (snd p)).
    rewrite <- retire_write_projector.
    reflexivity.
Qed.


Lemma remove_unseen_overapproximation:
  forall (n : nat) (a : value -> ActionValue) arg res  (call_tried : list (option value * option value)) (dyn : list (nat * (value -> ActionValue))) l (newcall : list (nat * (value -> ActionValue))),
    (forall i a b, nth_error call_tried i = Some (Some a, Some b) -> nth_error l i = Some (Some a, Some b)) ->
    nth_error l n = Some (Some arg, Some res) ->
    nth_error call_tried n = Some (Some arg, None) ->
    remove_unseen l (remove_unseen call_tried dyn ++ [(n, a)]) ++ newcall =
    remove_unseen call_tried dyn ++ [(n, a)] ++ newcall.
Proof.
intros.
unfold remove_unseen at 1.
rewrite filter_app_morphism.
simpl.
rewrite H0.
induction dyn.
-
  simpl.
  reflexivity.
-
  simpl.
  destruct a0.
  destruct (nth_error call_tried n0) eqn:?.
  {
    simpl.
    destruct p.
    destruct o; destruct o0;
    simpl.
    erewrite H;
    [    simpl;
    rewrite IHdyn;
    reflexivity
        |exact Heqo].
    rewrite IHdyn;
      reflexivity.
    rewrite IHdyn;
      reflexivity.
    rewrite IHdyn;
    reflexivity.
  }
  {
    rewrite IHdyn;
      reflexivity.
  }
Qed.


Lemma replace_nop : forall (l : list (option value * option value)) n0 v v0,
    nth_error l n0 = Some (Some v, Some v0) -> replace_nth n0 l (Some v, Some v0) = Some l.
Proof.
  induction l.
  -
    simpl in *.
    intros.
    destruct n0; simpl in *; inversion H.
  -
    intros.
    simpl in *.
    destruct n0.
    simpl in *.
    inversion H.
    reflexivity.
    simpl in *.
    rewrite IHl.
    reflexivity.
    assumption.
Qed.




Lemma replace_identity:
  forall  (l : list (option value * option value)) (n : nat) (v v0 : value)
    (n0 : nat) (v1 v2 : value) (l0 : list (option value * option value)),
    not (n = n0) ->
    nth_error l n0 = Some (Some v, Some v0) ->
    replace_nth n l (Some v1, Some v2) = Some l0 -> replace_nth n0 l0 (Some v, Some v0) = Some l0.
Proof.
induction l.
-
  intros.
  destruct n0; simpl in H0; inversion H0.
-
  intros.
  simpl in *.
  destruct n0.
  simpl in *.
  inversion H0.
  destruct n.
  {specialize (H eq_refl).
   contradiction.
   }{
  simpl in H1.
  destruct (replace_nth n l (Some v1, Some v2)).
  inversion H1.
  rewrite H3 in *.
  reflexivity.
  inversion H1.
  }
  destruct n;
    simpl in *.
  {
    inversion H1.
    rewrite replace_nop.
    reflexivity.
    exact H0.
  }
  {
    rewrite  Nat.succ_inj_wd_neg in H.
    destruct ( replace_nth n l (Some v1, Some v2)) eqn:?.
    inversion H1.
    erewrite IHl.
    reflexivity.
    exact H.
    exact H0.
    exact Heqo.
    inversion H1.
  }
Qed.


Lemma preserve_metcall_next_sga_aux:
  forall s r l d v v0 call_tried n regs_content,
    (replace_nth n call_tried (Some v, Some v0) = Some l ->
     nth_error (Met
                  (next_sga_aux regs_content
                                {| Reg := r; Met := l; dynamicOrder := d |}
                                s)) n = Some (Some v, Some v0)).
induction s.
-
  intros.
  simpl.
  destruct (n =? n0) eqn:?.
  {
    apply Nat.eqb_eq in Heqb.
    rewrite Heqb.
    pose proof (replace_in call_tried n0 (Some v, Some v0)).
    rewrite H in H0.
    rewrite H0.
    eapply IHs2.
    exact H.
  }
  {
    apply Nat.eqb_neq in Heqb.
    destruct (nth_error l n) eqn:?.
    destruct p.
    destruct o.
    destruct o0.
    eapply IHs2.
    exact H.
    destruct (atomic_av regs_content (wrap_state r l) (a v1)).
    destruct p.
    destruct (replace_nth n l (Some v1, Some v2)) eqn:?.
    simpl.
    eapply IHs1.
    instantiate (1:= l0).
    erewrite replace_identity.
    reflexivity.
    exact Heqb.
    pose proof ( replace_in call_tried n0 (Some v, Some v0)).
    rewrite H in H0.
    exact H0.
    exact Heqo0.
    eapply IHs2.
    exact H.
    eapply IHs2.
    exact H.
    destruct o0;
    eapply IHs2;
    exact H.
    eapply IHs2;
    exact H.
  }
-
  intros.
  simpl in *.
  pose proof (replace_in call_tried n (Some v, Some v0)).
  rewrite H in H0.
  exact H0.
Qed.








Theorem one_rule_at_a_time_property :forall (sched:scheduler) (regs_content:list (list value)) (logs:list (ReadLog*WriteLog)) (call_tried: list (option value * option value)) (dyn:list (nat* (value -> ActionValue))),
    length logs = length regs_content ->
    no_double_write (retire logs) = true ->
    let new_state := (next_sga_aux
                        regs_content
                        {|Reg := retire logs ;
                          Met := call_tried;
                          dynamicOrder := remove_unseen call_tried
                                                        dyn;|}
                        sched) in
    let new_reg := (perform_update regs_content (retire logs)) in
    exists newcall newlog, (Reg new_state) = log_append (retire logs) newlog /\
                      no_double_write (log_append (retire logs) newlog) = true /\
                      (dynamicOrder new_state) = (remove_unseen (Met new_state) (remove_unseen call_tried dyn) ++ newcall) /\
                      length newlog = length regs_content /\
                      (perform_update new_reg newlog, Met new_state) = (one_rule_at_a_time new_reg newcall
                                                                                           call_tried).
  induction sched. intros.
  -
    hnf in new_state.
    time match (eval cbv delta [new_state] in new_state) with
         | match ?g with _=>_ end =>
           (* idtac "desturct g" g; *) destruct g eqn:was_called
         | ?f => idtac "hmm" f
         end.
    {
      destruct p.
      destruct o eqn:?.
      destruct o0 eqn:?.
      {
        simpl in *.
        move IHsched2 at bottom.
        subst new_state.
        apply (IHsched2 _ _ _ _ H H0).
      }
      {
        cbv zeta in new_state.
        match (eval cbv delta [new_state] in new_state) with
        | match ?g with _=>_ end =>
          (* idtac "desturct g" g;  *) destruct g eqn:av
        | ?f => idtac (* idtac "hmm" f *)
        end.
        {
          simpl in *.
          destruct p.
          match (eval cbv delta [new_state] in new_state) with
          | match ?g with _=>_ end =>
            (* idtac "desturct g" g; *) destruct g eqn:newlogs
          | ?f => (* idtac "hmm" f *) idtac
          end.
          {
            clear IHsched2.
            pose proof (atomic_oraat (a v) (length regs_content) regs_content ) as atomic_oraat.
            move av at bottom.
            specialize (atomic_oraat ( logs)
                                     (repeat ([],[]) (length regs_content))
                                     v0 s).
            assert (length (retire logs) = length logs) as length_retirelog.
            unfold retire.
            rewrite map_length.
            reflexivity.
            assert ( no_double_write
                       (log_append
                          (retire
                             logs)
                          (repeat ([], []) (length regs_content))) =
                     true) as no_double_retireempty.
            rewrite <- H.
            rewrite <- length_retirelog.
            rewrite <- log_append_id'.
            assumption.
            specialize (atomic_oraat no_double_retireempty eq_refl).
            unfold retire at 1 in atomic_oraat.
            rewrite map_length in atomic_oraat.
            specialize (atomic_oraat H).
            rewrite repeat_length in atomic_oraat.
            specialize (atomic_oraat eq_refl call_tried []).
            unfold wrap_state in av.
            rewrite <- H  in atomic_oraat .
            rewrite <- length_retirelog in atomic_oraat.
            rewrite <- log_append_id' in atomic_oraat.
            specialize (atomic_oraat av).
            simpl in *.
            destruct atomic_oraat as [newlog_atomic atomic_oraat].
            destruct atomic_oraat as [length_atomic atomic_oraat].
            destruct atomic_oraat as [regeq_atomic atomic_oraat].
            destruct atomic_oraat as [nowrite_atomic perform_atomic_eq].
            simpl in *.
            (* Let's collapse in a better form: *)
            assert ( {|
                       Reg := repeat ([], [])
                                     (length
                                        (retire
                                           logs) );
                       Met := call_tried;
                       dynamicOrder := [] |} = blank_state regs_content call_tried) as collapse_empty.
            unfold blank_state.
            unfold wrap_state.
            unfold init_state.
            unfold retire.
            rewrite ?map_length.
            rewrite H.
            reflexivity.
            rewrite collapse_empty in perform_atomic_eq.
            assert ({|
                       Reg := log_append (repeat ([], []) (length (retire logs))) newlog_atomic;
                       Met := call_tried;
                       dynamicOrder := [] |} = wrap_state newlog_atomic call_tried) as collapse_newlogc.
            unfold wrap_state.
            rewrite <- length_atomic.
            rewrite <- log_append_id'_l.
            reflexivity.
            rewrite collapse_newlogc in perform_atomic_eq.

            (* Call recursively *)
            specialize (IHsched1 regs_content (Reg s) l (remove_unseen call_tried dyn++[(n,a)])).
            pose proof (f_equal (@length (ReadLog*WriteLog)) regeq_atomic).
            rewrite H1 in IHsched1.
            unfold log_append at 1 in IHsched1.
            rewrite map_length in IHsched1.
            rewrite combine_length in IHsched1.
            rewrite length_atomic in IHsched1.
            rewrite Nat.min_id in IHsched1.
            rewrite length_retirelog in IHsched1.
            rewrite <- regeq_atomic in nowrite_atomic.
            specialize (IHsched1 H).
            rewrite <- no_double_write_invariant_retire  in IHsched1.
            specialize (IHsched1 nowrite_atomic).
            destruct IHsched1 as [newcall IHsched1].
            destruct IHsched1 as [newlog IHsched1].
            destruct IHsched1 as [regnewlog IHsched1].
            destruct IHsched1 as [nodoublesched IHsched1].
            destruct IHsched1 as [donewcall IHsched1].
            destruct IHsched1 as [length_newlog perform_induction_eq].
            assert ( (perform_update
                        (perform_update regs_content
                                        (retire logs))
                        (retire newlog_atomic)) = (perform_update
                                                     (perform_update regs_content
                                                                     (retire logs))
                                                     ( newlog_atomic))) as erase_retire.
            rewrite <- perform_update_invariant_retire.
            reflexivity.
            rewrite regeq_atomic in perform_induction_eq.
            assert (retire
                      (log_append
                         (retire logs)
                         newlog_atomic) =
                    (log_append (retire logs) (retire newlog_atomic))) as push_retire_update.
            apply retire_push_retire_update.
            rewrite push_retire_update in perform_induction_eq.

            rewrite perform_update_seq in perform_induction_eq.
            assert (one_rule_at_a_time (perform_update regs_content (retire logs)) [(n,a)] call_tried =(perform_update
                                                                                                          (perform_update regs_content (retire logs))
                                                                                                          (retire newlog_atomic), l) ) as do_atom.
            simpl.
            rewrite was_called.
            assert ((blank_state regs_content call_tried) = (blank_state (perform_update regs_content (retire logs)) call_tried)).
            unfold blank_state.
            unfold init_state.
            unfold perform_update.
            rewrite map_length.
            rewrite combine_length.
            rewrite <- H.
            rewrite length_retirelog.
            rewrite Nat.min_id.
            reflexivity.
            rewrite H2 in perform_atomic_eq.
            rewrite perform_atomic_eq.
            rewrite newlogs.
            simpl.
            rewrite erase_retire.
            reflexivity.
            assert (one_rule_at_a_time
                      (perform_update
                         (perform_update regs_content
                                         (retire logs))
                         (retire newlog_atomic)) newcall l
                    =
                    ( let (newreg,newmet) := one_rule_at_a_time (perform_update regs_content (retire logs)) [(n,a)] call_tried in

                  one_rule_at_a_time newreg newcall newmet)).
            rewrite do_atom.
            reflexivity.
            pose proof (chain_oraat [(n,a)] newcall call_tried (perform_update regs_content (retire logs))).
            rewrite H2 in perform_induction_eq.
            (* rewrite do_atom in perform_induction_eq. *)
            rewrite <- H3 in perform_induction_eq.
            (* clear H2 H3 do_atom. *)
            eexists.
            eexists.
            repeat split.
            5:{
              subst new_reg.
              subst new_state.
              rewrite regeq_atomic.
              rewrite <- perform_induction_eq.
              f_equal.
              instantiate (1:= log_append (retire  newlog_atomic) newlog ).
              rewrite perform_update_seq.
              reflexivity.
              rewrite regeq_atomic in nodoublesched.
              rewrite retire_push_retire_update in nodoublesched.
              rewrite <- permutation_append in nodoublesched.
              apply no_double_append_r in nodoublesched.
              assumption.
              unfold log_append.
              rewrite map_length.
              rewrite combine_length.
              unfold retire.
              rewrite ?map_length.
              rewrite length_atomic.
              rewrite length_newlog.
              rewrite length_retirelog.
              rewrite H.
              rewrite Nat.min_id.
              reflexivity.
              rewrite retire_push_retire_update.
              simpl.
              rewrite (remove_unseen_works _ _ _ _ _ v v0 ).
              reflexivity.
              assumption.
            }
            subst new_state.
            rewrite (remove_unseen_works _ _ _ _ _ v v0 ) in regnewlog.
            rewrite regnewlog.
            rewrite regeq_atomic.
            rewrite push_retire_update.
            rewrite permutation_append.
            reflexivity.
            assumption.
            rewrite regeq_atomic in nodoublesched.
            rewrite retire_push_retire_update in nodoublesched.
            rewrite <- permutation_append in nodoublesched.
            assumption.
            subst new_state.
            move donewcall at bottom.
            rewrite (remove_unseen_works _ _ _ _ _ v v0 ) in donewcall.
            rewrite donewcall.
            unfold remove_unseen at 1.
            rewrite filter_app_morphism.
            fold (remove_unseen  (Met
       (next_sga_aux regs_content
          {| Reg := retire (Reg s); Met := l; dynamicOrder := remove_unseen call_tried dyn ++ [(n, a)] |}
          sched1)) (remove_unseen call_tried dyn)).
            simpl.
            (* assert ((* replace_nth n call_tried (Some v, Some v0) = Some l -> *) *)
            (*         nth_error (Met *)
            (*                      (next_sga_aux regs_content *)
            (*                                    {| Reg := r; Met := l; dynamicOrder := d |} *)
            (*                                    s)) n = Some (Some v, Some v0)). *)
            assert (nth_error (Met
        (next_sga_aux regs_content
           {| Reg := retire (Reg s); Met := l; dynamicOrder := remove_unseen call_tried dyn ++ [(n, a)] |}
           sched1)) n = Some (Some v, Some v0)).
            erewrite preserve_metcall_next_sga_aux.
            reflexivity.
            exact newlogs.
            rewrite H4.
            rewrite <- app_assoc.
            simpl.
            reflexivity.
            assumption.
            subst new_state.
            unfold retire.
            unfold log_append.
            rewrite map_length.
            rewrite combine_length.
            rewrite map_length.
            rewrite length_atomic.
            rewrite length_newlog.
            rewrite length_retirelog.
            rewrite H.
            rewrite Nat.min_id.
            reflexivity.
            rewrite regeq_atomic in nodoublesched.
            apply no_double_append_l in nodoublesched.
            rewrite retire_push_retire_update in nodoublesched.
            assumption.
            rewrite length_newlog.
            unfold retire.
            rewrite map_length.
            unfold log_append.
            rewrite map_length.
            rewrite combine_length.
            rewrite map_length.
            rewrite H.
            rewrite length_atomic.
            rewrite length_retirelog.
            rewrite H.
            rewrite Nat.min_id.
            reflexivity.
          }
          {
            simpl in was_called.
            pose proof (replace_in_right_size call_tried n (Some v,None) (Some v, Some v0)  was_called).
            rewrite newlogs in H1.
            contradiction.
          }
        }
        { (* Rule not compatible, call subschedule2 *)
          Ltac bad_case regs_content logs H IHsched2 call_tried H0 dyn new_state who_has_been_called H1 new_reg:=
            assert(length (retire logs) = length regs_content);
            unfold retire;try rewrite map_length, H; try reflexivity;
            specialize (IHsched2 regs_content (retire logs) call_tried);
            rewrite retire_projector in IHsched2;
            specialize(IHsched2 dyn H1 H0);
            simpl in IHsched2;
            move IHsched2 at bottom;
            subst new_state;
            destruct IHsched2 as [el ih];
            destruct ih as [el2 ih];
            destruct ih as [H2 ih];
            destruct ih as [nodouble ih];
            destruct ih as [H3 ih];
            destruct ih as [H4 H5];
            (* destruct ih as [H5 ih]; *)
            eexists; eexists;
            repeat split;
            [rewrite H2; f_equal
            | fold (retire logs);
              assumption
            |rewrite H3; f_equal
            |rewrite H4; reflexivity
            |subst new_reg;
             rewrite H5; reflexivity].

              bad_case regs_content logs H IHsched2 call_tried H0 dyn new_state who_has_been_called H1 new_reg.
          }
      }
      {
        destruct o0;
       bad_case regs_content logs H IHsched2 call_tried H0 dyn new_state who_has_been_called H1 new_reg.
      }
    }
    { (* Method does not have an argument *)
      bad_case regs_content logs H IHsched2 call_tried H0 dyn new_state who_has_been_called H1 new_reg.
    }
  -
    intros.
    simpl.
    subst new_state.
    simpl.
    eexists. eexists.
    repeat split.
    instantiate (1:= (repeat ([],[]) (length (retire logs)))).
    unfold log_append.
    subst new_reg.
    clear H call_tried regs_content dyn.
    induction  (retire logs).
    simpl.
    reflexivity.
    simpl.
    rewrite <- surjective_pairing.
    f_equal.
    simpl in H0.
    apply eq_sym in H0.
    apply Bool.andb_true_eq in H0.
    destruct H0.
    apply eq_sym in H0.
    exact (IHl H0).
    rewrite <- (log_append_id' (retire logs)).
    assumption.
    instantiate (1:= []).
    rewrite <- app_nil_end.
    unfold remove_unseen.
    rewrite filter_projector.
    reflexivity.
    unfold retire.
    rewrite map_length.
    rewrite <- H.
    clear H dyn .
    induction regs_content.
    unfold perform_update.
    simpl.
    rewrite repeat_length.
    reflexivity.
    simpl.
    unfold perform_update.
    rewrite repeat_length.
    reflexivity.
    simpl.
    subst new_reg.
    f_equal.
    clear H0 dyn call_tried.
    generalize dependent regs_content.
    induction logs.
    +
      simpl.
      destruct regs_content.
      cbv.
      reflexivity.
      unfold perform_update.
      simpl.
      reflexivity.
    +
      simpl.
      destruct regs_content.
      simpl.
      unfold perform_update.
      simpl.
      reflexivity.
      unfold perform_update.
      simpl.
      f_equal.
      intros.
      inversion H.
      specialize (IHlogs regs_content H1).
      f_equal.
      fold ( perform_update regs_content (retire logs)).
      fold (perform_update
             (perform_update regs_content (retire logs))
             (repeat ([], []) (length (retire logs)))).
      assumption.
Qed.


Lemma empty_no_double_write :
  forall  (n : nat),
    no_double_write (repeat ([],[]) n) = true .
Proof.
induction n.
-
  simpl.
  trivial.
-
  simpl.
  assumption.
Qed.

Lemma retire_nothing : forall n, retire (repeat ([], []) n) = (repeat ([], []) n).
induction n.
reflexivity.
simpl.
f_equal; assumption.
Qed.


Lemma perform_nothing : forall regs_content, 
  (perform_update regs_content (repeat ([], []) (Datatypes.length regs_content))) = regs_content.
  induction regs_content.
  cbv.
  reflexivity.
  simpl.
  cbn.
  f_equal.
  fold (perform_update regs_content (repeat ([],[]) (length regs_content))).
  assumption.
Qed.

Lemma remove_nothing : forall call_tried, remove_unseen call_tried [] = [].
  induction call_tried; cbv; try reflexivity; try assumption.
Qed.

Theorem one_rule_at_a_time_theorem :forall (sched:scheduler) (regs_content:list (list value)) (call_tried: list (option value * option value)),
    let new_state := next_sga_aux
                        regs_content
                        (blank_state regs_content call_tried)
                        sched in
    exists newcall,
      (perform_update regs_content (Reg new_state), Met new_state) = (one_rule_at_a_time regs_content newcall call_tried).
{
  intros.
  pose proof (one_rule_at_a_time_property sched regs_content (repeat ([],[]) (length regs_content)) call_tried []).
  rewrite repeat_length in H.
  rewrite <- no_double_write_invariant_retire in H.
  rewrite empty_no_double_write in H.
  specialize (H eq_refl eq_refl).
  cbv zeta in H.
  destruct H as [newcall H].
  destruct H as [newlog H].
  destruct H as [regcarac H].
  destruct H as [nodouble H].
  destruct H as [dynamic H].
  destruct H as [length performupdate].
  eexists.
  subst new_state.
  instantiate (1:= newcall).
  rewrite <- length in regcarac.
  rewrite retire_nothing in regcarac.
  rewrite <- log_append_id'_l in regcarac.
  rewrite <- regcarac in performupdate.
  rewrite retire_nothing in performupdate.
  rewrite perform_nothing in performupdate.
  rewrite remove_nothing in performupdate.
  rewrite length in performupdate.
  fold (init_state regs_content) in performupdate.
  fold (wrap_state (init_state regs_content) call_tried) in performupdate.
  fold (blank_state regs_content call_tried) in performupdate.
  exact performupdate.
}
Qed.

