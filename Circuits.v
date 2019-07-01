
Section circuits.
  Inductive circuit : nat -> Type :=
  | CAnd : forall {nOut},
      circuit nOut -> circuit nOut -> circuit nOut
  | COr : forall {nOut},
      circuit nOut -> circuit nOut -> circuit nOut
  | CMux : forall {n nOut n'} (select: circuit n),
      circuit nOut -> circuit n' -> circuit nOut
  | CConst : forall (l: list bool),
      circuit (length l)
  | CRef : forall nOut (var: nat),
      circuit nOut
  | CLet : forall {n n'} (var: nat) (expr: circuit n) (body: circuit n'),
      circuit n'.

  Record Bundle {n} :=
    { consistent: circuit 1;
      read0: circuit 1;
      read1: circuit 1;
      write0: circuit 1;
      write1: circuit 1;
      write0Data: circuit n;
      write1Data: circuit n;
      retVal: { n & circuit n } }.
  Arguments Bundle: clear implicits.

  Notation env := (list {n & circuit n}).

  Print Module List.
  Import ListNotations.

  Notation cenv := (list (nat * nat)).

  Axiom magic : forall {A} (_: unit), A.

  Definition max (l: list nat) :=
    List.fold_left max l 0.

  Definition CRefBundle n var :=
    {| consistent := CRef 1 var;
       read0 := CRef _ var;
       read1 := CRef _ var;
       write0 := CRef _ var;
       write1 := CRef _ var;
       write0Data := CRef n var;
       write1Data := CRef n var;
       retVal := existT _ n (CRef n var) |}.

  Definition CLetBundle {n n'} var (expr: Bundle n) (body: Bundle n') :=
    {| consistent := CLet var expr.(consistent) body.(consistent);
       read0 := CLet var expr.(read0) body.(read0);
       read1 := CLet var expr.(read1) body.(read1);
       write0 := CLet var expr.(write0) body.(write0);
       write1 := CLet var expr.(write1) body.(write1);
       write0Data := CLet var expr.(write0Data) body.(write0Data);
       write1Data := CLet var expr.(write1Data) body.(write1Data);
       retVal := existT _ _ (CLet var (projT2 expr.(retVal)) (projT2 body.(retVal))) |}.

  Fixpoint compile {n} (s: @syntax nat) (Gamma: cenv) input : Bundle n * cenv :=
    match s with
    | Bind var expr body =>
      let '(cExpr, Gamma') := compile expr Gamma input in
      let '(cBody, Gamma'') := compile body Gamma' cExpr in
      (cBody, Gamma'')          (* FIXME merge *)
    | Ref var =>
      let (cst, size) :=
          match List.find (fun x => Nat.eqb (fst x) var) Gamma with
          | Some (_, size) => (CConst [true], size)
          | None => (CConst [false], 0)
          end in
      ({| consistent := CAnd input.(consistent) cst;
          read0 := input.(read0);
          read1 := input.(read1);
          write0 := input.(write0);
          write1 := input.(write1);
          write0Data := input.(write0Data);
          write1Data := input.(write1Data);
          retVal := existT _ n (CRef _ var) |},
       Gamma)
    | PureUnit =>
      ({| consistent := input.(consistent);
         read0 := input.(read0);
         read1 := input.(read1);
         write0 := input.(write0);
         write1 := input.(write1);
         write0Data := input.(write0Data);
         write1Data := input.(write1Data);
         retVal := existT _ 0 (CConst nil) |},
       Gamma)
    | PureBits bits =>
      ({| consistent := input.(consistent);
          read0 := input.(read0);
          read1 := input.(read1);
          write0 := input.(write0);
          write1 := input.(write1);
          write0Data := input.(write0Data);
          write1Data := input.(write1Data);
          retVal := existT _ _ (CConst bits) |},
       Gamma)
    | If cond tbranch fbranch =>
      let var := S (max (List.map fst Gamma)) in
      let '(cCond, Gamma') := compile cond Gamma input in
      let '(cTbr, GammaT) := compile tbranch Gamma (CRefBundle n var) in
      let '(cFbr, GammaF) := compile fbranch Gamma (CRefBundle n var) in
      (CLetBundle var cCond {| consistent := CAnd cTbr.(consistent) cTbr.(consistent);
          read0 := COr cTbr.(read0) cFbr.(read0);
          read1 := COr cTbr.(read1) cFbr.(read1);
          write0 := COr cTbr.(write0) cFbr.(write0);
          write1 := COr cTbr.(write1) cFbr.(write1);
          write0Data := CMux (projT2 cCond.(retVal)) cTbr.(write0Data) cFbr.(write0Data);
          write1Data := CMux (projT2 cCond.(retVal)) cTbr.(write1Data) cFbr.(write1Data);
          retVal := existT _ _ (CMux (projT2 cCond.(retVal)) (projT2 cTbr.(retVal)) (projT2 cFbr.(retVal))); |},
       Gamma')
    | Fail =>
      ({| consistent := CConst [false];
          read0 := input.(read0);
          read1 := input.(read1);
          write0 := input.(write0);
          write1 := input.(write1);
          write0Data := input.(write0Data);
          write1Data := input.(write1Data);
          retVal := input.(retVal) |},
       Gamma)
    | Read level idx offset =>
      
      ({| consistent := CNot input.(read0);
          read0 := input.(read0);
          read1 := input.(read1);
          write0 := input.(write0);
          write1 := input.(write1);
          write0Data := input.(write0Data);
          write1Data := input.(write1Data);
          retVal := input.(retVal) |},
       Gamma)
    | Write level idx offset value => magic tt
    | Call idx args => magic tt
    end.
  End circuits.
