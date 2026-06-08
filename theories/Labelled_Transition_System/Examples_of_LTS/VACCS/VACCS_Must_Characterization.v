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

From TestingTheory Require Import VACCS_ta_tc_gen DefinitionAS Equivalence Must MustE
  Completeness InputOutputActions Lts_OBA_FB MultisetLTSConstruction Lts_Finite_Output_Chain gLts
  DefinitionMS EquivalenceMS DefinitionFMS EquivalenceFMS Coin_tower Soundness SetLTSConstruction
  StateTransitionSystems FiniteImageLTS ForwarderConstruction ParallelLTSConstruction
  InteractionBetweenLts Bisimulation DefinitionCI EquivalenceCI VACCS_ta_tc_gen.

From Coinduction Require Import all.

Notation "p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q" := (@ctx_pre proc _ _ (@gLtsEq_gLts proc _ _ VACCS_gLtsEq) proc 
  (@gLtsEq_gLts proc _ _ VACCS_gLtsEq) _ _ _ _ _ _ p q) (at level 70).

Section VACCS_Must_Alt_Corollary.

Context `{VP : VACCS_Parameters}.

Corollary must_iff_acceptance_set_VACCS (p q : proc) :
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q <-> p ▷ ∅ ≼ₐₛ q ▷ ∅.
Proof.
  now rewrite equivalence_acc_set_and_must_i.
Qed.

Corollary must_iff_co_inductive_acceptance_VACCS (p q : proc) :
   p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q <-> 
   ({[ p ▷ ∅ ]} : gset (proc * MO (ExtAct TypeOfActions))) 
   ᶜᵒ≼ₐₛ ({[ q ▷ ∅ ]} : gset (proc * MO (ExtAct TypeOfActions))).
Proof.
  now rewrite equivalence_co_inductive_acc_set_and_must_i.
Qed.

Corollary must_iff_tower_co_inductive_acceptance_VACCS (p q : proc) :
   p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q <-> 
   ({[ p ▷ ∅ ]} : gset (proc * MO (ExtAct TypeOfActions))) 
      ᶜᵒ≼ₜₒᵥᵥₑᵣ ({[ q ▷ ∅ ]} : gset (proc * MO (ExtAct TypeOfActions))).
Proof.
  now rewrite equivalence_co_inductive_acceptance_and_must_i_singleton.
Qed.

Corollary must_iff_must_set_VACCS (p q : proc) : p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q <-> p ▷ ∅ ≾ₘᵤₛₜ q ▷ ∅.
Proof.
  now rewrite equivalence_must_set_and_must_i.
Qed.

Corollary must_iff_failure_set_VACCS (p q : proc) : p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q <-> p ▷ ∅ ⋖ꜰᴀɪʟ q ▷ ∅.
Proof.
  now rewrite equivalence_failure_set_and_must_i.
Qed.

End VACCS_Must_Alt_Corollary.