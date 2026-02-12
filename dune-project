(lang dune 3.21)

(warnings (deprecated_coq_lang disabled))

(name testing-theory)

(generate_opam_files false)

(source
 (github GLmaths/testing-theory))

(authors "Gaëtan Lopez")

(maintainers "Gaëtan Lopez")

(license MIT)

(using coq 0.11)

(documentation https:GLmaths.github.io/testing-theory)

(package
 (name testing-theory)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends dune coq-stdpp coq-coinduction)
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
