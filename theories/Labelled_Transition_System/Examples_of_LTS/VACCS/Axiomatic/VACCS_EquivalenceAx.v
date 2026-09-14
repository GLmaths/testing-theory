(*
   Copyright (c) 2026 Gaëtan Lopez <gaetanlopez.maths@gmail.com>

   Permission is hereby granted, free of charge, to any person obtaining a copy
   of this software and associated documentation files (the "Software"), to deal
   in the Software without restriction, including without limitation the rights
   to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
   copies of the Software, and to permit persons to whom the Software is
   furnished to do so, subject to the following conditions:

   The above copyright notice and this permission notice shall be included in all
   copies or substantial portions of the Software.

   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
   OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
   SOFTWARE.
*)

(** * THE CHARACTERISATION

    On the recursion-free [Static] fragment the 9-rule system is **sound
    and complete** for the asynchronous must-preorder, with no side
    condition on either side.

    Soundness holds for ALL VACCS processes, not merely [Static] ones
    ([VACCS_SoundnessAx.soundness_ax]): every rule is sound outright, so
    there is no invariant to thread through a derivation.  The [Static]
    restriction is needed only for completeness
    ([VACCS_Matching.completeness_ax]), whose recursion measures the size
    of the right-hand side. *)

From Stdlib Require Import List PeanoNat Lia.
From stdpp Require Import base gmultiset.
From TestingTheory Require Import MultisetLTSConstruction.
From TestingTheory Require Import VACCS VACCS_Instance Must ActTau InputOutputActions
  gLts Bisimulation InteractionBetweenLts Testing_Predicate VACCS_Good WeakTransitions
  Subset_Act DefinitionAS Convergence VACCS_Static VACCS_Must_Characterization
  VACCS_Erasure VACCS_Shift VACCS_Precongruence VACCS_Expansion VACCS_ResNormalize
  VACCS_Copycat VACCS_Absorb VACCS_DefinitionAxiomatic VACCS_SoundnessAx VACCS_NormalForm
  VACCS_Forwarder VACCS_Cond2 VACCS_ReadySet VACCS_Canonical VACCS_Descent VACCS_Matching
  VACCS_DerivedRules.
Import ListNotations.

Section VACCS_EquivalenceAx.

Context `{VP : VACCS_Parameters}.

Theorem must_iff_ax_pre : forall (p q : proc),
  Static p -> Static q ->
  (p ᴠᴀᴄᴄꜱ⊑ₐₓ q <-> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q).
Proof.
  intros p q Hp Hq. split.
  - apply soundness_ax.
  - apply completeness_ax; assumption.
Qed.

Theorem must_eq_iff_ax_eq : forall (p q : proc),
  Static p -> Static q ->
  ((p ᴠᴀᴄᴄꜱ≂ₐₓ q) <-> p ≂ₘᵤₛₜᵢ q).
Proof.
  intros p q Hp Hq. split.
  - intros (H1 & H2). split;
      [ apply (proj1 (must_iff_ax_pre q p Hq Hp)); exact H2
      | apply (proj1 (must_iff_ax_pre p q Hp Hq)); exact H1 ].
  - intros (H1 & H2). split;
      [ apply (proj2 (must_iff_ax_pre p q Hp Hq)); exact H2
      | apply (proj2 (must_iff_ax_pre q p Hq Hp)); exact H1 ].
Qed.

Corollary ax_pre_sound_and_complete : forall (p q : proc),
  Static p -> Static q ->
  (p ᴠᴀᴄᴄꜱ⊑ₐₓ q -> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q) /\ (p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> p ᴠᴀᴄᴄꜱ⊑ₐₓ q).
Proof.
  intros p q Hp Hq. split;
    [ apply (proj1 (must_iff_ax_pre p q Hp Hq))
    | apply (proj2 (must_iff_ax_pre p q Hp Hq)) ].
Qed.


End VACCS_EquivalenceAx.
