(lang dune 3.15)

(name shapedtt)

(generate_opam_files true)

(source
 (github TOTBWF/shapedtt))

(authors "Reed Mullanix")

(maintainers "Reed Mullanix")

(package
 (name shapedtt)
 (synopsis "A type theory with shapes")
 (depends
   ocaml
   dune
  (bwd (>= 2.3.0))
  (algaeff (>= 2.0.0))))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
