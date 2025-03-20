(lang dune 3.17)

(name shapedtt)

(generate_opam_files true)

(source
 (github TOTBWF/shapedtt))

(authors "Reed Mullanix")

(maintainers "Reed Mullanix")

; We need 'Bwd.append : 'a bwd -> 'a bwd -> 'a bwd', which
; is not available in bwd-2.3.0.
(pin
 (url "git+https://github.com/TOTBWF/ocaml-bwd.git#append")
 (package (name bwd)))

(package
 (name shapedtt)
 (synopsis "A type theory with shapes")
 (depends
  (ocaml (>= 5.2))
  (algaeff (>= 2.0.0))
   dune
   bwd))
