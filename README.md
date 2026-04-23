[![Build doc](https://github.com/GLmaths/testing-theory/actions/workflows/build_docs.yml/badge.svg)](https://github.com/GLmaths/testing-theory/actions/workflows/build_docs.yml)

# testing-theory

This repository is the fork by G. Lopez of
[this project](https://github.com/gbtito/testing-theory).
The code here will be developed througout Lopez PhD thesis.

The work is lead by [Giovanni Bernardi](https://www.irif.fr/~gio/),
with the help of [Hugo Férée](https://hugo.feree.fr/).

A pi-calculus development in [theories/pi](theories/pi/README.md) including a proof of the Harmony Lemma (see [theories/pi/Pi_Instance.v](theories/pi/Pi_Instance.v#L984)) by
[Matteo Manighetti](https://www.mmanighetti.io/).


## Installation

Install the dependencies automatically via opam:
`opam install . --deps-only`

Or install them manually (see `dune-project` for the list of dependencies).

Then compile with `make`.
