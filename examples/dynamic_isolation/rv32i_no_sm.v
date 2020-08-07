Require Import dynamic_isolation.rv32.
Module RV32INoSMPackage := Package_rv32i_no_sm.
Definition prog := Interop.Backends.register RV32INoSMPackage.package.
Extraction "rv32i_no_sm.ml" prog.
