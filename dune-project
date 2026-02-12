(lang dune 3.21)

(warnings (deprecated_coq_lang disabled))

(name testing-theory)

(generate_opam_files true)
(source (github GLmaths/testing-theory))

(authors "Paul Laforgue"
         "Léo Stefanesco"
         "Peio Borthelle"
         "Gaëtan Lopez"
         "Hugo Férée")

(maintainers "Gaëtan Lopez")

(license MIT)

(using coq 0.11)

(documentation https://GLmaths.github.io/testing-theory)

(package
 (name testing-theory)
 (synopsis "Coq library for characterisations of testing preorders")
 (description "Coq library for characterisations of testing preorders")
 (depends (coq(>= 8.20.1))
          (coq-stdpp(>= 1.12.0))
          (coq-coinduction(>= 1.20))
          (coq-equations(>= 1.3.1)))
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
