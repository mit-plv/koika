Require Import Koika.Frontend.
Require Import RV.RVCore.
Import RV32ICore.

Definition rv_schedule : scheduler :=
  tc_scheduler (ExternalI |> ExternalD |>
                Writeback |> Execute |> Decode |> Fetch |> done).

Definition circuits :=
  compile_scheduler rv_rules rv_schedule.


Definition koika_package :=
  {| koika_reg_types := R;
     koika_reg_init := r;
     koika_ext_fn_types := empty_Sigma;
     koika_reg_names := {| show := show
                                       (* match r with *)
                                       (* (* Declare state *) *)
                                       (* | toIMem s => String.append "toIMem_" (MemReq.name_reg s) *)
                                       (* | fromIMem s => String.append "fromIMem_" (MemResp.name_reg s) *)
                                       (* | toDMem s => String.append "toDMem_" (MemReq.name_reg s) *)
                                       (* | fromDMem s => String.append "fromDMem_" (MemResp.name_reg s) *)
                                       (* | f2d s => String.append "f2d_" (fromFetch.name_reg s) *)
                                       (* | d2e s => String.append "d2e_" (fromDecode.name_reg s) *)
                                       (* | e2w s => String.append "e2w_" (fromExecute.name_reg s) *)
                                       (* | rf s => String.append "rf_" (Rf.name_reg s) *)
                                       (* | scoreboard s => String.append "scoreboard_" (Scoreboard.name_reg s) *)
                                       (* | pc => "pc" *)
                                       (* | epoch => "epoch" *)
                        (* end  *)|};
     koika_rules := rv_rules;
     koika_rule_names := {| show := show (*  match r with *)
                                        (*              | O => "fetch" *)
                                        (*              | 1 => "decode" *)
                                        (*              | 2 => "execute" *)
                                        (*              | 3 => "writeback" *)
                                        (*              | 4 => "externalI" *)
                                        (*     | _ => "externalD" *)
                         (* end *) |};
     koika_scheduler := rv_schedule;
     koika_module_name := "rv32i_core_pipelined" |}.

Definition package :=
  {| ip_koika := koika_package;
     ip_sim := {| sp_ext_fn_names := empty_fn_names;
                  sp_extfuns := None |};
     ip_verilog := {| vp_external_rules := [ ExternalI; ExternalD];
                      vp_ext_fn_names := empty_fn_names |} |}.

Definition prog := Interop.Backends.register package.
Extraction "rv32i_core_pipelined.ml" prog.
