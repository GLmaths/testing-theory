(*
   Copyright (c) 2026 Gaëtan Lopez <glopez@irif.fr>

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


From Stdlib.Unicode Require Import Utf8.
From Stdlib.Program Require Import Equality Basics.
From stdpp Require Import finite gmap decidable gmultiset.
From TestingTheory Require Import ActTau gLts Bisimulation Lts_OBA Subset_Act
    coWeakTransition Testing_Predicate
    StateTransitionSystems InteractionBetweenLts coConvergence Termination 
    DefinitionAS FiniteImageLTS Subset_Act.


(** ** Termination condition *)
Definition bhv_pre_co_cond1 `{gLts P A, gLts Q A} 
  (p : P) (q : Q) := forall s, p ⇓ᶜᵒ s -> q ⇓ᶜᵒ s.

Notation "p ₁≼꜀ₒ₋ₐₛ q" := (bhv_pre_co_cond1 p q) (at level 70).

(** ** Smyth preorder on acceptance sets *)
Definition bhv_pre_co_cond2 `{
  gLtsP : @gLts P A H, AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳P _ gLtsT,
  gLtsQ : @gLts Q A H, AbsQT : @AbsAction Q T FinA PreAct A H Φ 𝝳Q _ gLtsT}
  (p : P) (q : Q) :=
  forall (s : trace A) q',
    p ⇓ᶜᵒ s -> q ⟹ᶜᵒ[s] q' -> q' ↛ ->
    ∃ p', p ⟹ᶜᵒ[s] p' /\ p' ↛ /\ (⌈ (𝝳P ∘ Φ) ⌉ (coR p') ⊆ ⌈ (𝝳Q ∘ Φ) ⌉ (coR q')).

Notation "p ₂≼꜀ₒ₋ₐₛ q" := (bhv_pre_co_cond2 p q) (at level 70).

(** ** Definition of the alternative preorder *)
Definition bhv_pre_co `{
  gLtsP : @gLts P A H, AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳P _ gLtsT,
  gLtsQ : @gLts Q A H, AbsQT : @AbsAction Q T FinA PreAct A H Φ 𝝳Q _ gLtsT}
    (p : P) (q : Q) :=
      p ₁≼꜀ₒ₋ₐₛ q /\ p ₂≼꜀ₒ₋ₐₛ q.

Notation "p ≼꜀ₒ₋ₐₛ q" := (bhv_pre_co p q) (at level 70).
