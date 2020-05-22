(lang dune 2.5)
(using coq 0.2)

(generate_opam_files true)
(allow_approximate_merlin)

(name koika)
(version 0.0.1)
(source (github mit-plv/koika))
(authors "Clément Pit-Claudel <clement.pitclaudel@live.com>" "Thomas Bourgeat <bthom@mit.edu>")
(maintainers "Clément Pit-Claudel <clement.pitclaudel@live.com>")
(documentation "https://github.com/mit-plv/koika/")

(package
 (name koika)
  ;; FIXME dependencies should move here once https://github.com/ocaml/dune/issues/3497 is fixed
  ;; In the meantime, use koika.opam.template
  ;; (coq (>= 8.11))
  ;; (coq-ltac2 (>= 0.3))
  ;; (base (>= 0.12.2))
  ;; (core (>= 0.12.4))
  ;; (dune (and :build (>= 1.10)))
  ;; (hashcons (>= 1.3))
  ;; (parsexp (>= 0.12.0))
  ;; (ppx_jane (>= 0.9.0))
  ;; (stdio (>= 0.12.0))
  ;; (zarith (>= 1.9.1))
 (depends)
 (synopsis "A core language for rule-based hardware design 🦑️")
 (description "Kôika is a hardware design language inspired by BlueSpec SystemVerilog. Kôika programs are built from rules, small bits of hardware that operate concurrently to compute state updates but provide the illusion of serializable (atomic) updates. Kôika has simple, precise semantics that give you strong guarantees about the behavior of your designs."))
