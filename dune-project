(lang dune 1.10)
(using coq 0.1)

(generate_opam_files true)
(allow_approximate_merlin)

(name sga)
(version 0.0.1)
(source (github mit-plv/sga))
(authors "Clément Pit-Claudel <cpitclaudel@live.com>, Thomas Bourgeat <…>")
(maintainers "Clément Pit-Claudel <cpitclaudel@live.com>, Thomas Bourgeat <…>")
(documentation "https://github.com/mit-plv/sga/")

(package
 (name sga)
 (depends
  (ocaml (>= 4.02.3))
  (dune (and :build (>= 1.10)))
  (bisect_ppx (and :dev (>= 2.0.0)))
  (base (>= 0.9.0))
  (core (>= 0.9.0))
  (hashcons (>= 1.3))
  (parsexp (>= 0.12.0))
  (ppx_deriving (>= 4.1.5))
  (ppx_jane (>= 0.9.0))
  (stdio (>= 0.9.0))
  (zarith (>= 1.7)))
 (synopsis "sga")
 (description ""))
