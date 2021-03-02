(*! Morse transmitter !*)
Require Import Koika.Frontend.
Require Import Koika.Std.

Module Morse.

  Inductive reg_t :=
  | tx_state
  | message
  | pointer
  | timer
  | sink_led.

  Inductive ext_fn_t := ext_led.
  Inductive rule_name_t := print_token | fetch_next_token.

  Definition tx_state_t :=
    {| enum_name := "tx_state_t";
       enum_members := ["idle"; "short"; "long"; "spaceLetter"; "spaceWord"];
       enum_bitpatterns := [Ob~0~0~0; Ob~0~1~0; Ob~1~0~0; Ob~1~1~0; Ob~1~1~1] |}%vect.

  Definition Short := Ob~0~1~0.
  Definition Long := Ob~1~0~0.
  Definition SpaceLetter := Ob~1~1~0.
  Definition SpaceWord := Ob~1~1~1.
  Definition message_t :=
    {| array_len := 16;
       array_type := enum_t tx_state_t|}.


  Definition R r :=
    match r with
    | tx_state => enum_t tx_state_t
    | message => array_t message_t
    | pointer => bits_t 6
    | timer => bits_t 32
    | sink_led => bits_t 1
    end.

  Infix "+b+" := Bits.app (at level 60).
  Definition r idx : R idx :=
    match idx with
    | tx_state => (Ob~0~0~0 : type_denote  (R tx_state))
    | message =>
        value_of_bits (
        (Bits.zero:bits 12) +b+ SpaceWord 
        +b+ Short +b+ SpaceLetter +b+ Short +b+ SpaceLetter +b+ Short +b+ SpaceLetter +b+ Short +b+ (* H *)
        SpaceWord +b+ Long +b+ (* T *)
        SpaceWord +b+  Short (* E *)
        : bits (type_sz (R message)))
    | pointer => Bits.zero
    | timer => Bits.zero
    | sink_led => Bits.zero
    end.

  Definition Sigma (fn: ext_fn_t) :=
    match fn with
    | ext_led => {$ bits_t 1 ~> bits_t 1 $}
    end.

  Definition unitshort : uaction reg_t ext_fn_t := {{ |32`d5000000| }}.
  Definition unitlong : uaction reg_t ext_fn_t := {{ |32`d15000000| }}.
  
  (* Definition unitshort : uaction reg_t ext_fn_t := {{ |32`d2| }}.
  Definition unitlong : uaction reg_t ext_fn_t := {{ |32`d6| }}.*)
  Definition finish_token : uaction reg_t ext_fn_t :=
     {{  set newtime := |32`d0|;
         set led := Ob~0;
         write0(pointer, read0(pointer) + |6`d3|);
         write0(tx_state, enum tx_state_t { idle })}}.

  Definition _print_token : uaction reg_t ext_fn_t :=
    {{
      let newtime := read0(timer) in
      let led := Ob~0 in
      set newtime := (newtime + |32`d1|);
      match read0(tx_state) with
      | enum tx_state_t { short } =>
        (if (newtime <  ` unitshort `) then
           set led := Ob~1
        else
           `finish_token`)
      | enum tx_state_t { long } =>
        (if (newtime < (` unitlong `) ) then
           set led := Ob~1
        else
           `finish_token`)
      | enum tx_state_t { spaceLetter } =>
        (if (newtime < ` unitshort `) then
           set led := Ob~0
        else
           `finish_token`)
      | enum tx_state_t { spaceWord } =>
        (if (newtime < (` unitlong `)) then
           set led := Ob~0
        else
           `finish_token`)
      return default:
        pass
      end;
      write0(timer, newtime);
      write0( sink_led, extcall ext_led(led))
    }}.

  Definition _fetch_next_token : uaction reg_t ext_fn_t :=
    {{
        let ready := read0(tx_state) == enum tx_state_t { idle } in
        when ready do
           (let message := pack(read0(message)) in
            let newtoken := unpack(enum_t tx_state_t,message[read0(pointer) :+ 3]) in
           if ( newtoken == enum tx_state_t { idle })
           then (* restart from the beginning *)
             write0(pointer, |6`d0|);
             write0(tx_state, unpack(enum_t tx_state_t, message[|6`d0| :+ 3]))
           else
             write0(tx_state, newtoken)
           )
    }}.
  Definition _dummy: uaction reg_t ext_fn_t := {{ pass }}.

  Definition morse : scheduler :=
    fetch_next_token |> print_token |> done.

  Definition cr := ContextEnv.(create) r.
  (* Typechecking  *)
  Definition rules :=
    tc_rules R Sigma
             (fun r => match r with
                    | print_token => _print_token
                    | fetch_next_token =>  _fetch_next_token
                    (* | print_token => _print_token *)
                    (* | fetch_new_token => _fetch_new_token *)

                    end).

  Definition ext_fn_specs (fn : ext_fn_t) :=
    match fn with
    | ext_led => {| efr_name := "led"; efr_internal := false |}
    end.

  Definition package :=
    {| ip_koika := {| koika_reg_types := R;
                     koika_reg_init := r;
                     koika_ext_fn_types := Sigma;
                     koika_rules := rules;
                     koika_rule_external := (fun _ => false);
                     koika_scheduler := morse;
                     koika_module_name := "morse" |};

       ip_sim := {| sp_ext_fn_specs fn := {| efs_name := show fn; efs_method := false |};
                   sp_prelude := None |};

       ip_verilog := {| vp_ext_fn_specs := ext_fn_specs |} |}.
End Morse.

Definition prog := Interop.Backends.register Morse.package.
Extraction "morse.ml" prog.
