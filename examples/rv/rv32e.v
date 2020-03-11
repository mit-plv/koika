(*! Pipelined instantiation of an RV32E core !*)
Require Import RV.RVCore RV.rv32.
Module RV32EPackage := Package RV32E.
Definition prog := Interop.Backends.register RV32EPackage.package.
Extraction "rv32e.ml" prog.
