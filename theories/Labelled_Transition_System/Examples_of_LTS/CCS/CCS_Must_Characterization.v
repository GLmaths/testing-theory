(*
   Copyright (c) 2024 Nomadic Labs
   Copyright (c) 2024 Paul Laforgue <paul.laforgue@nomadic-labs.com>
   Copyright (c) 2024 Léo Stefanesco <leo.stefanesco@mpi-sws.org>
   Copyright (c) 2025 Gaëtan Lopez <glopez@irif.fr>

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

From TestingTheory Require Import VCCS_Must_Characterization DefinitionAS Equivalence Must 
  ForwarderConstruction ParallelLTSConstruction InteractionBetweenLts Bisimulation
  DefinitionCI Coin_tower DefinitionMS DefinitionFMS.
From Coinduction Require Import all.

Module Type CCS_Must_Alt_Corollary.
Include VCCS_Must_Alt_Corollary.

Axiom Value_is_unit : Value = unit.

Corollary must_iff_acceptance_set_CCS (p q : proc) : p ⊑ₘᵤₛₜᵢ q <-> p ▷ ∅ ≼ₐₛ q ▷ ∅.
Proof.
   eapply must_iff_acceptance_set_VCCS.
Qed.

Corollary must_iff_acceptance_set_CCS_without_toFW (p q : proc) :
  p ⊑ₘᵤₛₜᵢ q <-> p ≼ₐₛ q.
Proof.
  eapply must_iff_acceptance_set_VCCS_without_toFW.
Qed.

Corollary must_iff_tower_co_inductive_acceptance_CCS_without_toFW (p q : proc) :
  p ⊑ₘᵤₛₜᵢ q <-> {[ p ]} ᶜᵒ≼ₐₛ {[ q ]}.
Proof.
  eapply must_iff_co_inductive_acceptance_VCCS_without_toFW.
Qed.

Corollary must_iff_tower_co_inductive_tower_acceptance_CCS_without_toFW (p q : proc) :
  p ⊑ₘᵤₛₜᵢ q <-> {[ p ]} ᶜᵒ≼ₜₒᵥᵥₑᵣ {[ q ]}.
Proof.
  eapply must_iff_tower_co_inductive_tower_acceptance_VCCS_without_toFW.
Qed.

Corollary must_iff_must_set_CCS_without_toFW (p q : proc) :
  p ⊑ₘᵤₛₜᵢ q <-> p ≾ₘᵤₛₜ q.
Proof.
  eapply must_iff_must_set_VCCS_without_toFW.
Qed.

Corollary must_iff_failure_set_CCS_without_toFW (p q : proc) :
  p ⊑ₘᵤₛₜᵢ q <-> p ⋖ꜰᴀɪʟ q.
Proof.
  eapply must_iff_failure_set_VCCS_without_toFW.
Qed.

End CCS_Must_Alt_Corollary.