(lang dune 3.14)

(name must-testing)

(generate_opam_files false)

(source
 (github username/reponame))

(authors "Author Name")

(maintainers "Maintainer Name")

(license LICENSE)

(using coq 0.8)

(documentation https://url/to/documentation)

(package
 (name must-testing)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends dune coq-stdpp)
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
