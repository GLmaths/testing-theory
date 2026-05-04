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
            Subset_Act Must Soundness Completeness Equivalence StateTransitionSystems
              Termination WeakTransitions Convergence  
               InteractionBetweenLts
               DefinitionAS.

CoInductive copre `{
  gLtsP : @gLts P A H, !FiniteImagegLts P A, AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳P  gLtsP gLtsT,
  gLtsQ : @gLts Q A H, !FiniteImagegLts Q A, AbsQT : @AbsAction Q T FinA PreAct A H Φ 𝝳Q  gLtsQ gLtsT}
  (ps : gset P) (qs : gset Q) : Prop := {
    c_tau qs' : wt_set_from_pset_spec1 qs [] qs' -> copre ps qs'
  ; c_now : ps ⤓ -> forall q , q ∈ qs -> q ↛ ->
            exists p , p ∈ ps /\ exists p', p ⟹ p' /\ p' ↛ /\ ⌈ (𝝳P ∘ Φ) ⌉ (coR p') ⊆ ⌈ (𝝳Q ∘ Φ) ⌉ (coR q)
  ; c_step : forall μ qs' ps', ps ⇓ [μ] ->
                         wt_set_from_pset_spec1 qs [μ] qs' -> wt_set_from_pset_spec ps [μ] ps' -> copre ps' qs'
  ; c_cnv : ps ⤓ -> qs ⤓
  }.

Notation "p ⩽ q" := (copre p q) (at level 70).

Lemma co_preserved_by_wt_nil `{
  gLtsP : @gLts P A H, !FiniteImagegLts P A, AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳P  gLtsP gLtsT,
  gLtsQ : @gLts Q A H, !FiniteImagegLts Q A, AbsQT : @AbsAction Q T FinA PreAct A H Φ 𝝳Q  gLtsQ gLtsT}
  (ps : gset P) (qs qs' : gset Q) : wt_set_from_pset_spec1 qs [] qs' -> ps ⩽ qs -> ps ⩽ qs'.
Proof. intros. eapply c_tau;eauto. Qed.


