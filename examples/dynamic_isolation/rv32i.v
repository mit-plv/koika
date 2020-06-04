(*! Pipelined instantiation of an RV32I core !*)
Require Import dynamic_isolation.rv32.
Module RV32IPackage := Package_rv32i.
Definition prog := Interop.Backends.register RV32IPackage.package.
Extraction "rv32i.ml" prog.
