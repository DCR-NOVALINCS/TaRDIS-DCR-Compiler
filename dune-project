(lang dune 3.19)

(using menhir 2.0)

(name tardis_dcr_compiler)

(generate_opam_files true)

(source
 (github DCR-NOVALINCS/TaRDIS-DCR-Compiler))

(authors "TaRDIS Project - WP3/DCR Team")
(maintainers "TaRDIS Project - WP3/DCR Team")

(license MIT)

(documentation https://url/to/documentation)

(package
 (name tardis_dcr_compiler)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends
  (ocaml
   (>= 5.3.0))
  (dune
   (>= 3.19))
  (menhir
   (>= 2.0))
   (yojson
   (>= 3.0.0))
  (ounit2 
   (>= 2.2.7)))
   
 (tags
  (topics "to describe" your project)))
