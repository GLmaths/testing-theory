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

From stdpp Require Import gmap gmultiset.

From TestingTheory Require Import VCCS_ta_tc_gen DefinitionAS Equivalence Must
  ParallelLTSConstruction InteractionBetweenLts Bisimulation
  ActTau InputOutputActions Convergence
  gLts Lts_OBA FiniteImageLTS Testing_Predicate Completeness Lts_FW Lts_OBA_FB MultisetLTSConstruction
  DefinitionMS EquivalenceMS DefinitionFMS EquivalenceFMS Coin_tower
  SetLTSConstruction ForwarderConstruction DefinitionCI EquivalenceCI VCCS_ta_tc_gen.
From TestingTheory Require Import coFiniteImage DefinitionASco EquivalenceASco
  TestSpecBridge VCCS_CoFiniteImage.

From Coinduction Require Import all.

Notation "p ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ q" := (p ⊑ₘᵤₛₜᵢ q) (at level 70).

Section VCCS_Must_Alt_Corollary.

Context `{VP : VCCS_Parameters}.

Corollary must_iff_acceptance_set_VCCS (p q : proc) :
  p ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ q <-> p ▷ ∅ ≼ₐₛ q ▷ ∅.
Proof.
  now rewrite equivalence_acc_set_and_must_i.
Qed.

Corollary must_iff_acceptance_set_VCCS_without_toFW (p q : proc) :
  p ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ q <-> p ≼ₐₛ q.
Proof.
  now rewrite equivalence_fw_acc_set_and_must_i.
Qed.

Corollary must_iff_co_inductive_acceptance_VCCS_without_toFW (p q : proc) :
  p ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ q <-> ({[ p ]} : gset proc) ᶜᵒ≼ₐₛ ({[ q ]} : gset proc).
Proof.
  now rewrite equivalence_fw_co_inductive_acc_set_and_must_i.
Qed.

Corollary must_iff_tower_co_inductive_tower_acceptance_VCCS_without_toFW (p q : proc) :
  p ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ q <-> ({[ p ]} : gset proc) ᶜᵒ≼ₜₒᵥᵥₑᵣ ({[ q ]} : gset proc).
Proof.
  now rewrite equivalence_fw_co_inductive_acceptance_and_must_i_singleton.
Qed.

Corollary must_iff_must_set_VCCS_without_toFW (p q : proc) :
  p ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ q <-> p ≾ₘᵤₛₜ q.
Proof.
  now rewrite<- equivalence_fw_must_set_and_must_i.
Qed.

Corollary must_iff_failure_set_VCCS_without_toFW (p q : proc) :
  p ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ q <-> p ⋖ꜰᴀɪʟ q.
Proof.
  now rewrite<- equivalence_fw_failure_set_and_must_i.
Qed.

Corollary must_iff_co_acceptance_set_VCCS_without_toFW (p q : proc) :
  p ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ q <-> p ≼꜀ₒ₋ₐₛ q.
Proof.
  now rewrite equivalence_fw_acc_set_and_must_i_co.
Qed.

End VCCS_Must_Alt_Corollary.

