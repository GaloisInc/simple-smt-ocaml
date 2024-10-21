(lang dune 3.12)

(name simple_smt)

(generate_opam_files true)

(source
 (github GaloisInc/simple-smt-ocaml))

(authors "Iavor S. Diatchki")

(maintainers "Iavor S. Diatchki")

; (license LICENSE)

(documentation "https://galoisinc.github.io/simple-smt-ocaml/simple_smt/Simple_smt/index.html")

(package
 (name simple_smt)
 (synopsis "Simple SMT")
 (description "A library for interacting with an SMT solver process.")
 (depends ocaml dune ppx_deriving sexplib zarith)
;  (tags
;    (topics "to describe" your project))
)
