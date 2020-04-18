(*! Pipelined instantiation of an RV32E core !*)
Require Import DynamicIsolation.rv32.
Module RV32EPackage := Package_rv32e.
Definition prog := Interop.Backends.register RV32EPackage.package.
Extraction "rv32e.ml" prog.
