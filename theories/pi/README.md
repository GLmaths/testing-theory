# Pi calculus

This folder contains a formalization of the harmony lemma for the full 
π-calculus in Rocq using Autosubst for handling name binding and renaming. Syntax/renamings come first, then structural congruence and the labelled semantics, and finally the instance that proves the Harmony Lemma.

## Layout
- Autosubst signatures: [signatures](signatures/) contains the generated signatures used by Autosubst (core definitions, scoped and unscoped syntax). These files are not meant to be edited manually.
- Renamings and notation: [Renamings.v](Renamings.v) introduces the pi-calculus syntax, Autosubst-based renamings (`shift`, `swap`, `nvars`) and convenient notations for processes and actions.
- Structural congruence: [Congruence.v](Congruence.v) defines the congruence relation `cgr` over processes and proves basic algebraic laws used throughout the instance.
- Labelled semantics: [LTS.v](LTS.v) gives the labelled transition system `lts` (including name extrusion and communication).
- Renaming lemmas for the LTS: [LTS_Renamings.v](LTS_Renamings.v) develops inversion and renaming lemmas for `lts`.
- Main lemmas and theorems: [Pi_Instance.v](Pi_Instance.v) defines the reduction relation `sts`, establishes shape lemmas, shows both directions of the equivalence between reductions and τ-labelled transitions up to congruence, and proves the Harmony Lemma (`HarmonyLemma` at [Pi_Instance.v#L984](Pi_Instance.v#L984)).