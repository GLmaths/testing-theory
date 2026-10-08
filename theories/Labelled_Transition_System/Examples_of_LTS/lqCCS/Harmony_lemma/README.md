# Rocq development

| File | Content | Toolchain |
|---|---|---|
| `Lifted.v` | Adequacy of tag schedulers (Thm. 4.10; Thm. 6.6, countable outcomes) over an abstract ω-cpo `Alg` | Rocq 9.1, stdlib only |
| `Paths.v` | Lemma 4.7 (path sums, each path once); `nodup_wl`/`adequacy_nodup`: Thm. 4.10 under the paper's "distinct labels" hypothesis | Rocq 9.1 |
| `Harmony.v` | Lemma 5.1 (Harmony): configuration LTS ≅ (program ∥ memory)\L, on steps and paths | Rocq 9.1 |
| `States.v` | Abstract quantum states acted upon linearly by super-operators | Rocq 9.1 |
| `Corollaries.v` | Cor. 4.12 (`cor_states`), Cor. 5.6 (`cor_par`), pruning (`pruning`); composed paths enumerated exactly once (`penum_spec`, `penum_nodup`) | Rocq 9.1 |
| `Kierner.v` | Inclusion ⊆ of Kierner's Lemma 3.2: every tag scheduler is realised by a history-dependent scheduler reading only past states (`lifted_in_mdp`) | Rocq 9.1 |
| `Counterexample.v` | Counterexample to Kierner's Lemma 3.2; non-compositionality of the MDP | same |

Imported from `~/GitProject/article/rocq` (not under version control there).
Changes: imports `NDQ.X` → `From TestingTheory Require Import X`, `From Coq` → `From Stdlib`.
Built by the repository's dune project (`dune build`), no extra dependency.
Not imported: `coqq/` (`CoqQInst.v`, `CoqQBridge.v`), which needs Coq 8.18 + CoqQ.
