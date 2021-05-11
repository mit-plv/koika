(*! Frontend | Functions on untyped ASTs, including error localization !*)
Require Import Koika.Syntax.

Section SyntaxFunctions.
  Section CoqErrorReporting.
    (* We don't have explicit positions in Coq, so the next best thing is to
  annotate terms ourselves. *)
    Context {var_t fn_name_t reg_t ext_fn_t: Type}.

    Notation usugar pos_t := (usugar pos_t var_t fn_name_t).
    Notation uaction pos_t := (uaction pos_t var_t fn_name_t).

    Open Scope N.

    Inductive path := PThis | PThat (p: path) (n: N).
    Scheme Equality for path.

    Definition foldi {A B: Type} (f : N -> B -> A -> A) (n: N) (a0: A) (bb: list B): N * A :=
      List.fold_right (fun b '(n, a) => (N.succ n, f n b a)) (0, a0) bb.

    Fixpoint reposition {reg_t ext_fn_t} (p: path) (a: uaction unit reg_t ext_fn_t)
      : uaction path reg_t ext_fn_t :=
      let r {reg_t ext_fn_t} n := @reposition reg_t ext_fn_t (PThat p n) in
      let annotated : uaction path reg_t ext_fn_t :=
        match a with
        | UError err =>
          UError {| epos := p; emsg := err.(emsg); esource := err.(esource) |}
        | UFail tau => UFail tau
        | UVar var => UVar var
        | UConst cst => UConst cst
        | UAssign v ex => UAssign v (r 0 ex)
        | USeq a1 a2 => USeq (r 0 a1) (r 1 a2)
        | UBind v ex body => UBind v (r 0 ex) (r 1 body)
        | UIf cond tbranch fbranch =>
          UIf (r 0 cond) (r 1 tbranch) (r 2 fbranch)
        | URead port idx => URead port idx
        | UWrite port idx value => UWrite port idx (r 0 value)
        | UUnop ufn1 arg1 => UUnop ufn1 (r 0 arg1)
        | UBinop ufn2 arg1 arg2 => UBinop ufn2 (r 0 arg1) (r 1 arg2)
        | UExternalCall ufn arg =>
          UExternalCall ufn (r 0 arg)
        | UInternalCall ufn arg =>
          let ufn := map_intf_body (r 0) ufn in
          let args := snd (foldi (fun n a args => (r n a :: args)) 1 [] arg) in
          UInternalCall ufn args
        | UAPos _ e => (r 0 e)
        | USugar s => USugar (reposition_sugar p s)
        end in
      UAPos p annotated
    with reposition_sugar {reg_t ext_fn_t} (p: path) (s: usugar unit reg_t ext_fn_t)
         : usugar path reg_t ext_fn_t :=
           let r {reg_t ext_fn_t} n := @reposition reg_t ext_fn_t (PThat p n) in
           match s with
           | UErrorInAst => UErrorInAst
           | USkip => USkip
           | UConstBits bs => UConstBits bs
           | UConstString s => UConstString s
           | UConstEnum sig cst => UConstEnum sig cst
           | UProgn aa =>
             let aa := snd (foldi (fun n a aa => (r n a :: aa)) 0 [] aa) in
             UProgn aa
           | ULet bindings body =>
             let '(n, bindings) :=
                 foldi (fun n '(v, a) bindings => (v, r n a) :: bindings) 0 [] bindings in
             ULet bindings (r n body)
           | UWhen cond body =>
             UWhen (r 0 cond) (r 1 body)
           | USwitch var default branches =>
             let '(_, branches) :=
                 foldi (fun n '(a1, a2) branches => (r n a1, r (1 + 2 * n) a2) :: branches) 2 [] branches in
             USwitch (r 0 var) (r 1 default) branches
           | UStructInit sig fields =>
             let '(_, fields) :=
                 foldi (fun n '(nm, a) fields => (nm, r n a) :: fields) 0 [] fields in
             UStructInit sig fields
           | UArrayInit tau elements =>
             let '(_, elements) :=
                 foldi (fun n a elements => (r n a) :: elements) 0 [] elements in
             UArrayInit tau elements
           | UCallModule fR fSigma ufn args =>
             let ufn := map_intf_body (r 0) ufn in
             let args := snd (foldi (fun n a args => (r n a :: args)) 1 [] args) in
             UCallModule fR fSigma ufn args
           end.

    Fixpoint rev_path acc (p: path) :=
      match p with
      | PThis => acc
      | PThat p n => rev_path (PThat acc n) p
      end.

    Definition on_track (rev_target current_path: path) :=
      match rev_target, current_path with
      | PThis, _ => Some PThis
      | p, PThis => Some p
      | PThat p n, PThat _ n' =>
        if N.eqb n n' then Some p else None
      end.

    Open Scope bool.
    Inductive ErrorBeacon : Prop :=
      | ErrorHere: forall {A}, A -> ErrorBeacon.

    Fixpoint place_error_beacon {reg_t ext_fn_t}
             (rev_target current_path: path) (a: uaction unit reg_t ext_fn_t)
      : list ErrorBeacon * (uaction unit reg_t ext_fn_t) :=
      match on_track rev_target current_path with
      | Some PThis =>
        let beacon := ErrorHere a in
        ([beacon], UError {| epos := tt;
                             emsg := ExplicitErrorInAst;
                             esource := ErrSrc beacon |})
      | Some rev_target =>
        let pe n := place_error_beacon rev_target (PThat current_path n) in
        let '(beacons, annotated) :=
            match a with
            | UError err =>
              ([], a)
            | UFail tau =>
              ([], a)
            | UVar var =>
              ([], a)
            | UConst cst =>
              ([], a)
            | UAssign v ex =>
              let '(found, ex) := pe 0 ex in
              (found, UAssign v ex)
            | USeq a1 a2 =>
              let '(f1, a1) := pe 0 a1 in
              let '(f2, a2) := pe 1 a2 in
              (f1 ++ f2, USeq a1 a2)
            | UBind v ex body =>
              let '(fex, ex) := pe 0 ex in
              let '(fbody, body) := pe 1 body in
              (fex ++ fbody, UBind v ex body)
            | UIf cond tbranch fbranch =>
              let '(fcond, cond) := pe 0 cond in
              let '(ftbranch, tbranch) := pe 1 tbranch in
              let '(ffbranch, fbranch) := pe 2 fbranch in
              (fcond ++ ftbranch ++ ffbranch, UIf cond tbranch fbranch)
            | URead port idx =>
              ([], a)
            | UWrite port idx value =>
              let '(f, value) := pe 0 value in
              (f, UWrite port idx value)
            | UUnop ufn1 arg1 =>
              let '(f1, arg1) := pe 0 arg1 in
              (f1, UUnop ufn1 arg1)
            | UBinop ufn2 arg1 arg2 =>
              let '(f1, arg1) := pe 0 arg1 in
              let '(f2, arg2) := pe 1 arg2 in
              (f1 ++ f2, UBinop ufn2 arg1 arg2)
            | UExternalCall ufn arg =>
              let '(f, arg) := pe 0 arg in
              (f, UExternalCall ufn arg)
            | UInternalCall ufn args =>
              let '(fbody, body) := pe 0 ufn.(int_body) in
              let ufn :=
                  if fbody then
                    (* Only unfold the body if the error is in it *)
                    map_intf_body (fun _ => body) ufn
                  else ufn in
              let '(n, (fargs, args)) :=
                  foldi (fun n arg '(fargs, args) =>
                           let '(f, arg) := pe n arg in (fargs ++ f, arg :: args))
                        1 ([], []) args in
              (fbody ++ fargs, UInternalCall ufn args)
            | UAPos _ e => pe 0 e
            | USugar s =>
              let '(fs, s) := place_error_beacon_in_sugar rev_target current_path s in
              (fs, USugar s)
            end in
        (beacons, match beacons with
                  | [] => a
                  | _ => annotated
                  end)
      | None => ([], a)
      end
    with place_error_beacon_in_sugar
           {reg_t ext_fn_t}
           (rev_target current_path: path) (s: usugar unit reg_t ext_fn_t)
         : list ErrorBeacon * usugar unit reg_t ext_fn_t :=
           let pe {reg_t ext_fn_t} n :=
               @place_error_beacon reg_t ext_fn_t rev_target (PThat current_path n) in
           match s with
           | UErrorInAst => ([], s)
           | USkip => ([], s)
           | UConstBits _ => ([], s)
           | UConstString _ => ([], s)
           | UConstEnum _ _ => ([], s)
           | UProgn aa =>
             let '(n, (faa, aa)) :=
                 foldi (fun n arg '(faa, aa) =>
                          let '(f, arg) := pe n arg in (faa ++ f, arg :: aa))
                       0 ([], []) aa in
             (faa, UProgn aa)
           | ULet bindings body =>
             let '(n, (fbindings, bindings)) :=
                 foldi (fun n '(v, a) '(fbindings, bindings) =>
                          let '(f, a) := pe n a in (fbindings ++ f, (v, a) :: bindings))
                       0 ([], []) bindings in
             let '(fbody, body) := pe n body in
             (fbindings ++ fbody, ULet bindings body)
           | UWhen cond body =>
             let '(fcond, cond) := pe 0 cond in
             let '(fbody, body) := pe 1 body in
             (fcond ++ fbody, UWhen cond body)
           | USwitch var default branches =>
             let '(_, (fbranches, branches)) :=
                 foldi (fun n '(a1, a2) '(fbranches, branches) =>
                          let '(f1, a1) := pe (2 * n) a1 in
                          let '(f2, a2) := pe (1 + 2 * n) a2 in
                          (fbranches ++ f1 ++ f2, (a1, a2) :: branches))
                       2 ([], []) branches in
             let '(fvar, var) := pe 0 var in
             let '(fdefault, default) := pe 1 default in
             (fbranches ++ fvar ++ fdefault, USwitch var default branches)
           | UArrayInit tau elements =>
             let '(_, (felements, elements)) :=
                 foldi (fun n a '(felements, elements) =>
                          let '(f, a) := pe n a in (felements ++ f, a :: elements))
                       0 ([], []) elements in
             (felements, UArrayInit tau elements)
           | UStructInit sig fields =>
             let '(_, (ffields, fields)) :=
                 foldi (fun n '(v, a) '(ffields, fields) =>
                          let '(f, a) := pe n a in (ffields ++ f, (v, a) :: fields))
                       0 ([], []) fields in
             (ffields, UStructInit sig fields)
           | UCallModule fR fSigma ufn args =>
              let '(fbody, body) := pe 0 ufn.(int_body) in
              let ufn :=
                  if fbody then (* Only unfold the body if the error is in it *)
                    map_intf_body (fun _ => body) ufn
                  else ufn in
              let '(n, (fargs, args)) :=
                  foldi (fun n arg '(fargs, args) =>
                           let '(f, arg) := pe n arg in (fargs ++ f, arg :: args))
                        1 ([], []) args in
              (fbody ++ fargs, UCallModule fR fSigma ufn args)
           end.
  End CoqErrorReporting.

  Section TermSize.
    Context {pos_t var_t fn_name_t reg_t ext_fn_t: Type}.

    Fixpoint uaction_size
             {reg_t ext_fn_t}
             (ua: Syntax.uaction pos_t var_t fn_name_t reg_t ext_fn_t) :=
      (1 + match ua with
           | UAssign v ex =>
             uaction_size ex
           | USeq a1 a2 =>
             uaction_size a1 + uaction_size a2
           | UBind v ex body =>
             uaction_size ex + uaction_size body
           | UIf cond tbranch fbranch =>
             uaction_size cond + uaction_size tbranch + uaction_size fbranch
           | UWrite port idx value =>
             uaction_size value
           | UUnop ufn1 arg1 =>
             uaction_size arg1
           | UBinop ufn2 arg1 arg2 =>
             uaction_size arg1 + uaction_size arg2
           | UExternalCall ufn arg =>
             uaction_size arg
           | UInternalCall ufn args =>
             List.fold_left
               (fun acc arg => acc + uaction_size arg)
               args (uaction_size ufn.(int_body))
           | UAPos p e => uaction_size e
           | USugar s => usugar_size s
           | _ => 0
           end)%N
    with usugar_size
           {reg_t ext_fn_t}
           (us: usugar pos_t var_t fn_name_t reg_t ext_fn_t) :=
           (1 + match us with
                | UProgn aa =>
                  List.fold_left
                    (fun acc arg => acc + uaction_size arg)
                    aa 0
                | ULet bindings body =>
                  List.fold_left
                    (fun acc '(_, value) => acc + uaction_size value)
                    bindings (uaction_size body)
                | UWhen cond body =>
                  uaction_size cond + uaction_size body
                | USwitch var default branches =>
                  List.fold_left
                    (fun acc '(_, body) => acc + uaction_size body)
                    branches (uaction_size default)
                | UStructInit sig fields =>
                  List.fold_left
                    (fun acc '(_, value) => acc + uaction_size value)
                    fields 0
                | UArrayInit tau elements =>
                  List.fold_left
                    (fun acc elem => acc + uaction_size elem)
                    elements 0
                | UCallModule fR fSigma fn args =>
                  List.fold_left
                    (fun acc arg => acc + uaction_size arg)
                    args (uaction_size fn.(int_body))
                | _ => 0
                end)%N.
  End TermSize.
End SyntaxFunctions.
