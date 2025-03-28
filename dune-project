(lang dune 3.14)

(using menhir 2.0)

(name tardis_dcr_translation_tool)

(generate_opam_files true)

(source
 (github DCR-NOVALINCS/TaRDIS-DCR))

(authors "TaRDIS Project Team")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name tardis_dcr_translation_tool)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends
  (dune
   (>= 3.14))
  (menhir
   (>= 2.0))
  (ocaml
   (>= 4.08))
  (ocamlfind
   (>= 1.8))
  (ppxlib
   (>= 0.22))
  (ppx_derivers
   (>= 1.2))
  (ppx_deriving
   (>= 4.5))
  (ppx_blob
   (>= 0.8.0))
  (js_of_ocaml
   (>= 3.7))
  (js_of_ocaml-ppx
   (>= 3.7))
  (ounit2
   (>= 2.2.7)))
   
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
