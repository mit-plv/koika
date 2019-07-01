(* Copyright (c) 2019 Thomas Bourgeat, Clément Pit-Claudel *)


Record signature := {
                     Tin : Type;
                     Tout: Type;
                     Spec: Tin -> Tout;
                   }.

Class context :=
  {
    types: nat -> Type;
      (* Those function are considered combinational *)
    externals: nat -> signature
  }.

Section ActionValue.
  Context {var: Type -> Type}.
  Context {ctx:context}.

  Inductive Val :Type -> Type :=
  (* vec,idx,port*)
  | avread : forall (vec port:nat) (idx: Val nat), Val (types vec)
  | avcall : forall (f: nat), Val (Tin (externals f)) ->
                       Val (Tout (externals f))
  | avbool : bool -> Val bool
  | avinteger : nat -> Val nat
  | avvar : forall {T}, var T -> Val T
  (* vec,idx,port *)
  .

  Inductive ActionValue : Type -> Type :=
  | avif: forall {T}, Val bool -> ActionValue T -> ActionValue T
  | avbind: forall {T}, Val T -> (var T -> ActionValue) -> ActionValue
  | avwrite : forall (vec  port:nat) (idx: Val nat), Val (types vec) -> ActionValue
  | avblock : ActionValue
  | avempty : ActionValue.

End ActionValue.


Arguments Val: clear implicits.
Arguments ActionValue: clear implicits.
Check avread.

Example term0 {var} {ctx} : Val var ctx  _ :=
  (avread 0 0 (avinteger 0)).

Example term1 {var} {ctx}: ActionValue var ctx :=
  (avbind (avread 0 0 (avinteger 0))
          (fun x =>
             (avwrite 0 0 (avinteger 0) (avvar x)))).


Module example_term2.
  Local Instance ctx : context :=
    {|
      types:= (fun n =>
                       match n with
                       | 0 => bool
                       | _ => unit
                       end);
      externals := (fun n => {|Tin := bool;
                            Tout := unit;
                            Spec := (fun x => tt)
                          |})
    |}.

  Example term2 {var}
  : ActionValue var _ :=
    (avwrite 1 0 (avinteger 0)
             (avcall 0 (avbool true))).
End example_term2.


Module example_term3.
  (* Alternative way *)
  Example term3 {var}
  : ActionValue var _ :=
    let ctx := {|
      types:= (fun n =>
                       match n with
                       | 0 => bool
                       | _ => unit
                       end);
      externals := (fun n => {|Tin := bool;
                            Tout := unit;
                            Spec := (fun x => tt)
                          |})
    |} in
    (avbind (avread 0 0 (avinteger 0))
            (fun x =>
               (avwrite 1 0 (avinteger 0)  (avcall 0 (avvar x))))).

End example_term3.


Definition MethodState := list (option value * option value).
Inductive State := mkState {Reg: list(ReadLog*WriteLog) ; Met: MethodState; dynamicOrder: list (nat*(value -> ActionValue))}.

Require Import Coq.Arith.Compare_dec.
(* idx  timestamp generation *)
Inductive sort_write (ty:Type) : Type :=
| write :  nat -> nat -> nat -> ty -> sort_write ty.

(* idx timestamp generation *)
Inductive sort_read : Type :=
| read : nat -> nat -> nat -> sort_read.





Axiom notb: bool -> bool.

Import Datatypes.

(* Semantics development *)
Fixpoint replace_nth (n:nat)  {A: Type} (l: list A) (e:A) : option (list A) :=
  match (n,l) with
  | (_, nil) => None
  | (O, cons t q) => Some (cons e q)
  | (S n, cons t q) =>
    let continuation := (replace_nth n q e) in
    match continuation with
    | None => None
    | Some a => Some (cons t a)
    end
  end.

Lemma replace_nth_length : forall {A:Type} e n (l: list A) , match replace_nth n l e with
                                         | Some l1=> length l1 = length l
                                         | None => True
                                                    end.
  induction n;induction l;intros;simpl;firstorder.
  destruct  (replace_nth n l e) eqn:? .
  specialize (IHn l ).
  rewrite Heqo in IHn.
  simpl.
  f_equal.
  exact IHn.
  trivial.
Qed.

Definition value_is_true :=
  (fun a =>
     match a with
     | Bool a => Some a
     | _ => None
     end).


Fixpoint find_read (r:ReadLog) (reg:nat) : bool :=
  match (r) with
  | (cons (read l) t) => orb (PeanoNat.Nat.eqb reg l) (find_read (t) reg)
  | (cons _ t) => find_read (t) reg
  | _ => false
  end.

Fixpoint find_forward (r:ReadLog) (reg:nat) : bool :=
  match (r) with
  | (cons (forward l) t) => orb (PeanoNat.Nat.eqb reg l) (find_forward (t) reg)
  | (cons _ t) => find_forward (t) reg
  | _ => false
  end.

Fixpoint find_anywrite (w:WriteLog) (reg:nat) : bool :=
  match (w) with
  | (cons (write_0 l v) t) => orb (PeanoNat.Nat.eqb reg l) (find_anywrite (t) reg)
  | (cons (write_past l v) t) => orb (PeanoNat.Nat.eqb reg l) (find_anywrite (t) reg)
  | (cons (write_1 l v) t) => orb (PeanoNat.Nat.eqb reg l) (find_anywrite (t) reg)
  | (cons (write_past_1 l v) t) => orb (PeanoNat.Nat.eqb reg l) (find_anywrite (t) reg)
  | _ => false
  end.


Fixpoint find_write_past (w:WriteLog) (reg:nat) : bool :=
  match (w) with
  | (cons (write_0 l v) t) => (find_write_past (t) reg)
  | (cons (write_past l v) t) =>orb (PeanoNat.Nat.eqb reg l) (find_write_past (t) reg)
  | (cons (write_1 l v) t) =>  (find_write_past (t) reg)
  | (cons (write_past_1 l v) t) =>(find_write_past (t) reg)
  | _ => false
  end.

Fixpoint find_write1 (w:WriteLog) (reg:nat) : bool :=
  match (w) with
  | (cons (write_0 l v) t) => (find_write1 (t) reg)
  | (cons (write_past l v) t) => (find_write1 (t) reg)
  | (cons (write_1 l v) t) => orb (PeanoNat.Nat.eqb reg l) (find_write1 (t) reg)
  | (cons (write_past_1 l v) t) => orb (PeanoNat.Nat.eqb reg l) (find_write1 (t) reg)
  | _ => false
  end.

Fixpoint find_write1_past (w:WriteLog) (reg:nat) : bool :=
  match (w) with
  | (cons (write_0 l v) t) => (find_write1_past (t) reg)
  | (cons (write_past l v) t) => (find_write1_past (t) reg)
  | (cons (write_1 l v) t) => (find_write1_past (t) reg)
  | (cons (write_past_1 l v) t) => orb (PeanoNat.Nat.eqb reg l) (find_write1_past (t) reg)
  | _ => false
  end.

Definition extract_read0  (reg_content:list value) (reg:nat) : option value :=
  nth_error reg_content reg .


Fixpoint extract_read1 (reg_content:list value) (log: WriteLog) (reg: nat) : option value :=
  match log with
  | nil => extract_read0 reg_content reg
  | cons (write_0 a v) t => if PeanoNat.Nat.eqb reg a
                           then None (* TODO fail in some case but not other? No always fail *)
                           else extract_read1 reg_content t reg
  | cons (write_past a v) t => if PeanoNat.Nat.eqb reg a
                           then Some v
                              else extract_read1 reg_content t reg
  | cons (write_past_1 a v) t => if PeanoNat.Nat.eqb reg a
                           then None (* TODO fail in some case but not other? No always fail *)
                           else extract_read1 reg_content t reg
  | cons (write_1 a v) t => extract_read1 reg_content t reg
                                         end.

Fixpoint atomic_av (regs_content: list (list value)) (state: State) (av : ActionValue) : option (value * State) :=
         match av with
         | avblock => None
         | avempty => Some (bottomValue, state)
         | avlet avbind avbody =>
           let acb := atomic_av regs_content state  avbind in
           match acb with
           | None => None
           | Some (v, state) =>
             atomic_av regs_content state (avbody v)
           end
         | avlift f a b =>
           let aca := atomic_av regs_content state a in
           match aca with
           | None => None
           | Some (rva, state) =>
             let acb := atomic_av regs_content state b in
             match acb with
             | None => None
             | Some (rvb, state) =>
               Some (f rva rvb, state)
             end
           end
         | avif avcond avthen =>
           let accond := atomic_av regs_content state avcond in
           match accond with
           | None => None
           | Some (rv, state) =>
             match rv with
             | Bool true => atomic_av regs_content state avthen
             | Bool false => Some (bottomValue, state)
             | _ => None
             end
           end
         | avwrite moduleset reg arg =>
           match nth_error (Reg state) moduleset with
           | None => None
           | Some rw =>
             if find_forward (fst rw) reg then
               None
             else
               if find_anywrite (snd rw) reg then
                 None
               else
                 match replace_nth moduleset
                                   (Reg state)
                                   ((fun (x: ReadLog*WriteLog) => let (r,w) := x in (r,cons (write_0 reg arg) w))
                                      rw)
                 with
                 | None => None
                 | Some newlog => Some (bottomValue, {|Reg := newlog ;
                                                      Met:= Met state ;
                                                      dynamicOrder := dynamicOrder state
                                                    |})
                 end
           end
         | avwrite1 moduleset reg arg =>
           match nth_error (Reg state) moduleset with
           | None => None
           | Some rw =>
             if (find_write1 (snd rw) reg) then
               None
             else
               match replace_nth moduleset
                                 (Reg state)
                                 ((fun (x: ReadLog*WriteLog) => let (r,w) := x in (r, cons (write_1 reg arg) w)) rw)
               with
               | None => None
               | Some newlog =>
                 Some
                   (bottomValue, {|Reg := newlog ;
                                   Met:= Met state ;
                                   dynamicOrder := dynamicOrder state
                                   |})
               end
           end
         | avread moduleset reg =>
           match (nth_error (Reg state) moduleset, nth_error regs_content moduleset) with
           | (Some rw, Some regs_content) =>
             if find_write_past (snd rw) reg then
               None
             else
               if find_forward (fst rw) reg then
                 None
               else
                 if find_write1 (snd rw) reg then
                   None
                 else
                   match replace_nth moduleset
                                     (Reg state)
                                     ((fun (x: ReadLog*WriteLog ) =>
                                         let (r,w) := x in
                                         (* if find_read (fst x) reg then *)
                                         (*   (r,w) *)
                                         (* else *)
                                         (cons (read reg) r, w)) rw)
                   with
                   | None => None
                   | Some newlog =>
                     match extract_read0 regs_content reg with
                     | None => None
                     | Some rv =>
                       Some (rv,
                             {|Reg := newlog ;
                               Met:= Met state ;
                               dynamicOrder := dynamicOrder state;
                               |})
                     end
                   end
           | (_,_) => None
           end
         | avread1 moduleset reg =>
           match (nth_error (Reg state) moduleset, nth_error regs_content moduleset) with
           | (Some rw, Some regs_content) =>
             (* Check added on Thursday 23, May *)
             match nth_error regs_content reg with
             | None => None
             | Some _ =>
               if find_write1_past (snd rw) reg then
                 None
               else
                 match replace_nth moduleset
                                   (Reg state)
                                   ((fun (x: ReadLog*WriteLog) =>
                                       let (r,w) := x in
                                       (* if find_forward (fst x) reg then (r,w) else *)
                                       (cons (forward reg) r, w)) rw)
                 with
                 | Some newlog =>
                   match extract_read1
                           regs_content
                           (snd rw) reg with
                   | None => None
                   | Some rv =>
                     Some (rv,
                           {|Reg := newlog ; Met:= Met state; dynamicOrder := dynamicOrder state |})
                   end
                 | None => None
                 end
             end
           | _ => None
           end
         end.

Inductive scheduler : Type :=
| try_method : nat -> (value -> ActionValue) -> scheduler -> scheduler -> scheduler
| empty_rule.

Definition try_rule (n:nat) (av:ActionValue) (yes:scheduler) (no:scheduler) : scheduler :=
  try_method n (fun x => av) yes no.



Definition retire_write (l: WriteLog ) : WriteLog :=
  (map
     (fun x : sort_write =>
        match x with
        | write_0 n v | write_past n v => write_past n v
        | write_1 n v | write_past_1 n v => write_past_1 n v
        end) l).


Definition retire p := map (fun (x:ReadLog*WriteLog) =>
                              ((* fwd_then_read *) (fst x),
                               (retire_write (snd x)))) p.



Definition init_state (l : list (list value)) : list ( ReadLog * WriteLog):=
  List.repeat ([],[]) (List.length l).

Definition wrap_state l m := {| Reg := l; Met := m; dynamicOrder := [] |}.
Definition blank_state l m := wrap_state (init_state l) m.

Fixpoint next_sga_aux (regs_content:list (list value)) (s:State) (sched:scheduler) : State :=
  match sched with
  | empty_rule => s
  | try_method which v_to_av schedIfTrue schedIfFalse =>
    match nth_error (Met s) which with
    | None => next_sga_aux regs_content s schedIfFalse
    | Some (_, Some _) =>  next_sga_aux regs_content s schedIfFalse  (* Already fired *)
    | Some (None, _) =>  next_sga_aux regs_content s schedIfFalse
    | Some (Some arg, None ) =>  (* Only case where it's asked to fire it *)
      let av := v_to_av arg in
      let to_rule_rw := (Reg s) in
      let rule_tried := atomic_av regs_content (wrap_state (* (Reg s) *)to_rule_rw (Met s)) av in (* Pass the new s! So we have the whole history. *)
      match rule_tried with
      | None => next_sga_aux regs_content s schedIfFalse
      | Some (rv, new_s) =>
        match replace_nth which (Met s) (Some arg, Some (rv)) with
        | Some newmet=> next_sga_aux regs_content
                                    {|Reg:= retire (Reg new_s);
                                      Met:= newmet;
                                      dynamicOrder := app (dynamicOrder s) [(which,v_to_av)]
                                    |}
                                    schedIfTrue
        | None =>  next_sga_aux regs_content s schedIfFalse
        end
      end
    end
  end.

Definition nth_map {A B:Type} (f:A->B) (l:list A) (idx:nat) : option B :=
  match nth_error l idx with
  | None => None
  | Some k => Some (f k)
  end.

Lemma nth_error_nth_map :
  forall {A B:Type} (f:A->B) (l:list A) (idx:nat),
    nth_error (map f l) idx = nth_map f l idx.
Proof.
  cbv - [nth_error map].
  induction l; simpl.
  - destruct idx; simpl;reflexivity.
  - destruct idx; simpl; [reflexivity|].
    rewrite IHl; reflexivity.
Qed.

Fixpoint mymap {A B} f (l:list A) : list B :=
    match l with
      | [] => []
      | a :: t => (f a) :: (mymap f t)
    end.

Ltac dd x := destruct x eqn:?.

Ltac reduce_leftmost_match t :=
  match (t) with
  | match ?x with _ => _ end =>
    match x with
    | PeanoNat.Nat.eqb ?a ?a =>
      progress rewrite PeanoNat.Nat.eqb_refl
    | atomic_av _ _ (match ?hole with _ => _ end) =>
      match x with
      | atomic_av _ _ ?t =>
        reduce_leftmost_match t
      end
    | nth_error (map ?f ?l) ?idx =>
      (* idtac "rewrite nth_error nmap"; *)
      rewrite nth_error_nth_map
    | nth_error _ (match ?hole with _ => _ end) =>
      match x with
      | nth_error _ ?t =>
        reduce_leftmost_match t
      end
    | next_sga_aux _ _ (match ?hole with _ => _ end) =>
      match x with
      | next_sga_aux _ _ ?t =>
            reduce_leftmost_match t
      end
    | match ?y with _ => _ end =>
      match y with
      | match _ with _ => _ end => reduce_leftmost_match x
      | PeanoNat.Nat.eqb ?a ?a =>
        progress rewrite PeanoNat.Nat.eqb_refl
      | nth_error (map ?f ?l) ?idx =>
        (* idtac "rewrite nth_error nmap"; *)
        rewrite nth_error_nth_map
      | atomic_av _ _ (match ?hole with _ => _ end) =>
        match y with
        | atomic_av _ _ ?t =>
          reduce_leftmost_match t
        end
      | nth_error _ (match ?hole with _ => _ end) =>
        match y with
        | nth_error _ ?t =>
          reduce_leftmost_match t
        end
      (* | merge_state _ (match ?hole with _ => _ end) => *)
      (*   match y with *)
      (*   | merge_state _ ?t => *)
      (*     reduce_leftmost_match t *)
      (*   end *)
      (* | merge_state (match ?hole with _ => _ end) _ => *)
      (*   match y with *)
      (*   | merge_state ?t _ => *)
      (*     reduce_leftmost_match t *)
      (*   end *)
      | next_sga_aux _ _ (match ?hole with _ => _ end) =>
        match y with
        | next_sga_aux _ _ ?t =>
          reduce_leftmost_match t
        end
      | ?final =>
        (* idtac "Consider" final; *)
        let r := eval hnf  in final in
        tryif (constr_eq r final) then
          match goal with
          | [ H: final = _ |- _ ] => rewrite H
          | [  |- _ ] => ((* idtac "destruct" final; *)  (instantiate (1:= ltac:(destruct final))); ( dd final))
         end
        else
          (change final with r)
      end
    | ?final =>
       let r := (eval hnf in final) in
       tryif (constr_eq r final) then
                   match goal with
          | [ H: final = _ |- _ ] => rewrite H
          | [  |- _ ] => ((* idtac "destruct" final; *)  (instantiate (1:= ltac:(destruct final))); ( dd final))
         end
       else
         (change final with r)
    end
  | mymap _ ?f => reduce_leftmost_match f
  | replace_nth ?idx ?l ?v => reduce_leftmost_match idx; reduce_leftmost_match v
  | ?final =>
    let r := (eval hnf in final) in
    tryif (constr_eq r final) then
      idtac
    else
      (change final with r)
  end.


Ltac reduce_rec :=
  match goal with
  | [  |- ?g = _] => reduce_leftmost_match g
  end.

Ltac compute_sga mymodule:=
  eexists;  cbv - [next_sga_aux nth_error mymodule mymap map];
  (cbn - [atomic_av nth_error mymap map replace_nth next_sga_aux Nat.eqb]);
  repeat(reduce_rec;
         (cbn - [atomic_av nth_error mymap map replace_nth next_sga_aux Nat.eqb])).



Ltac simplify' := match goal with
                  | [  |- (match ?x with _ => _ end) = _] =>
                    etransitivity;
                    [instantiate (1:=  ltac:(destruct x));
                     destruct x;cbv;
                     simplify'|
                     (destruct x; cbv; reflexivity ) || ( instantiate (1:= ltac:(destruct x)); destruct x;cbv;simplify')]
                   | _ =>  reflexivity
                  end.

Require Import Omega.
Ltac destruct_enough i := intros; destruct i; [intros;cbv; eexists; etransitivity;[ repeat(match goal with
  | [  |- ?g = _ ] => reduce_leftmost_match g
   end; cbv ) |] | try omega ].

Definition lift_nat_nat_nat f := fun a b => match (a,b) with
                            | (Nat a, Nat b) => Nat (f a b)
                            | (_,_) => bottomValue
                             end.

Definition lift_nat_nat f := fun a => match (a) with
                            | (Nat a) => Nat (f a )
                            | (_) => bottomValue
                             end.

Definition lift_nat_nat_bool f := fun a b => match (a,b) with
                             | (Nat a, Nat b) => Bool (f a b)
                             | (_,_) => bottomValue
                             end.
Definition lift_bool_bool f := fun a => match a with
                               | Bool a => Bool (f a)
                               | _ => bottomValue
                                       end.

Fixpoint makelistint (size:nat) datavector : list (value) :=
  let  names := (map datavector (seq 0 size)) in
  map Nat names.

Definition add_register_to_environment (initV: value) (env:list (list (value))) : (nat * list(list (value))) :=
  (length (hd [] env), match replace_nth 0 env (app (hd [] env) [(initV)]) with
                       | Some a => a
                       | None => []
                       end).

Definition add_vector_int_to_environment (size:nat) datavector (env:list(list (value))) : (nat * list( list (value))) :=
  ((length env), app env [((makelistint size datavector))]).


Fixpoint maybe_select {A:Type} (l: list A) (pos: nat) : option A :=
  match l with
  | [] => None
  | cons h t => match pos with
               | O => Some h
               | S p => maybe_select t p
               end
  end.
