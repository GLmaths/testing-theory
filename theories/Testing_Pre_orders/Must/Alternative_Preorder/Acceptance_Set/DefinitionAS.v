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

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Program Require Import Equality.
From stdpp Require Import finite gmap decidable.
From TestingTheory Require Import ActTau gLts Bisimulation Lts_OBA Subset_Act WeakTransitions Testing_Predicate
    StateTransitionSystems InteractionBetweenLts Convergence Termination FiniteImageLTS.

(* * Alternative preorder for Must based on acceptance-sets *)

(** ** Label abstractions *)

(** Client-side condition for label abstractions **)
Class AbsAction {P T FinA : Type}  `{H : ExtAction A} (A : Type) (PreAct : Type) (gLtsP : gLts P H) (gLtsT : gLts T H)  (Φ : A → FinA) (𝝳 : FinA → PreAct) :=
  MkAbsAction {
    abstraction_test_spec μ μ' t : (Φ μ) = (Φ μ') -> μ ∈ (R t)-> μ' ∈ (R t)
    abstraction_prog_spec μ μ' t : 𝝳 (Φ μ) = 𝝳 (Φ μ') -> (Φ μ) ∈ map_set Φ (coR p) -> (Φ μ') ∈ map_set Φ (coR p)
  }.


(** Server-side condition for label abstractions **)
Class FinitaryAbsAction `{AbsAction A PreAct gLtsP gLtsT Φ 𝝳} `{Countable PreAct} :=
  MkPreExtAction {
      coR_abs : P -> gset PreAct;
      preactions_of_spec1 (p : P) (pre_μ : PreAct) : pre_μ ∈ (coR_abs p) -> pre_μ ∈ map (fun x => 𝝳 (Φ μ)) (coR p);
      preactions_of_spec2 (pre_μ : FinA) (p : P) : pre_μ ∈ map (fun x => 𝝳 (Φ μ)) (coR p) -> pre_μ ∈ (coR_abs p);
  }.


(** ** Termination condition *)
Definition bhv_pre_cond1 `{gLts P A, gLts Q A} 
  (p : P) (q : Q) := forall s, p ⇓ s -> q ⇓ s.

Notation "p ≼₁ q" := (bhv_pre_cond1 p q) (at level 70).

(** ** Smyth preorder on acceptance sets *)
Definition bhv_pre_cond2 `{
  LtsP : @gLts P A H, PreAP : @PreExtAction P A H FinA PreA PreA_eq PreA_countable 𝝳 Φ LtsP,
  LtsQ : @gLts Q A H, PreAQ : @PreExtAction Q A H FinA PreA PreA_eq PreA_countable 𝝳 Φ LtsQ}
  (p : P) (q : Q) :=
  forall s q',
    p ⇓ s -> q ⟹[s] q' -> q' ↛ ->
    ∃ p', p ⟹[s] p' /\ p' ↛ /\ (pre_co_actions_of p' ⊆ pre_co_actions_of q').

Notation "p ≼₂ q" := (bhv_pre_cond2 p q) (at level 70).

(** ** Definition of the alternative preorder *)
Definition bhv_pre `{PreA_countable : Countable PreA} `{
  LtsP : @gLts P A H, PreAP : @PreExtAction P A _ FiniteA PreA _ _ 𝝳 Φ LtsP,
  LtsQ : @gLts Q A H, PreAQ : @PreExtAction Q A _ FiniteA PreA _ _ 𝝳 Φ LtsQ}
    (p : P) (q : Q) := 
      p ≼₁ q /\ p ≼₂ q.

Notation "p ≼ₐₛ q" := (bhv_pre p q) (at level 70).

