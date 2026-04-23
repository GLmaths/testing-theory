(*
   Copyright (c) 2024 Nomadic Labs
   Copyright (c) 2024 Paul Laforgue <paul.laforgue@nomadic-labs.com>
   Copyright (c) 2024 Léo Stefanesco <leo.stefanesco@mpi-sws.org>

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

From Stdlib Require ssreflect.
From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From Stdlib.Program Require Import Equality Wf.
From Stdlib.Wellfounded Require Import Inverse_Image.
From Stdlib.Logic Require Import ProofIrrelevance.

From stdpp Require Import base countable finite gmap list finite base decidable finite gmap.

From TestingTheory Require Import ActTau InputOutputActions gLts Bisimulation Lts_OBA Lts_OBA_FB Lts_FW FiniteImageLTS
            Subset_Act Must SoundnessAS CompletenessAS EquivalenceAS StateTransitionSystems
              GeneralizeLtsOutputs Termination WeakTransitions Convergence  
               InteractionBetweenLts
               DefinitionAS.

CoInductive copre
  `{@FiniteImagegLts P A H gLtsP, @FiniteImagegLts Q A H gLtsQ}
  `{PreAP : @PreExtAction P A H FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP}
  `{PreAQ : @PreExtAction Q A H FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsQ}
  (ps : gset P) (q : Q) : Prop := {
    c_tau q' : q ⟶ q' -> copre ps q'
  ; c_now : (forall p, p ∈ ps -> p ⤓) -> q ↛ ->
            exists p p', p ∈ ps /\ p ⟹ p' /\ p' ↛ /\ pre_co_actions_of p' ⊆ pre_co_actions_of q
  ; c_step : forall μ q' ps', (forall p, p ∈ ps -> p ⇓ [μ]) ->
                         q ⟶[μ] q' -> wt_set_from_pset_spec ps [μ] ps' -> copre ps' q'
  ; c_cnv : (forall p, p ∈ ps -> p ⤓) -> q ⤓
  }.

Notation "p ⩽ q" := (copre p q) (at level 70).

Lemma co_preserved_by_wt_nil
  `{@FiniteImagegLts P A H gLtsP, @FiniteImagegLts Q A H gLtsQ}
  `{PreAP : @PreExtAction P A H FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP}
  `{PreAQ : @PreExtAction Q A H FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsQ}
  (ps : gset P) (q q' : Q) : q ⟹ q' -> ps ⩽ q -> ps ⩽ q'.
Proof. intro hw. dependent induction hw; eauto. destruct 1. eauto. Qed.


