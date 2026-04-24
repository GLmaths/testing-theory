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
From Stdlib.Program Require Import Equality Basics.
From stdpp Require Import finite gmap decidable.
From TestingTheory Require Import ActTau gLts Bisimulation Lts_OBA Subset_Act WeakTransitions Testing_Predicate
    StateTransitionSystems InteractionBetweenLts Convergence Termination FiniteImageLTS Subset_Act.

(* * Alternative preorder for Must based on acceptance-sets *)

(** ** Label abstractions *)

Class AbsAction {P T FinA PreAct: Type} (A : Type) (H : ExtAction A) (gLtsP : gLts P H) (gLtsT : gLts T H) (Φ : A → FinA) (𝝳 : FinA → PreAct) :=
  MkAbsAction {
    (** Client-side condition for label abstractions , Definition 5 (1) **)
    abstraction_test_spec (t : T) (μ : A) (μ' : A) : (Φ μ) = (Φ μ') -> μ ∈ (R t)-> μ' ∈ (R t);
    (** Server-side condition for label abstractions,  Definition 5 (2) **)
    abstraction_prog_spec (p : P) μ μ' : 𝝳 (Φ μ) = 𝝳 (Φ μ') -> (Φ μ) ∈ map_set Φ (coR p) -> (Φ μ') ∈ map_set Φ (coR p);
  }.

Arguments AbsAction {_} {_} {_} {_} A H gLtsP gLtsT Φ 𝝳.


(** ** Finitary Label abstractions *)

Class FinitaryAbsAction {FinA PreAct: Type} P T (A : Type) (H : ExtAction A) {gLtsP : gLts P H} {gLtsT : gLts T H} (Φ : A → FinA) (𝝳 : FinA → PreAct)
  `{Countable PreAct} :=
  MkFinitaryAbsAction {
      FinitaryAbsAction_Abs :: AbsAction A H gLtsP gLtsT Φ 𝝳;

      (* 𝝳 (Φ (coR p)) is a finite set, called (coR_abs p) *)
      coR_abs : P -> gset PreAct;
      preactions_of_spec1 (p : P) (pre_μ : PreAct) : pre_μ ∈ (coR_abs p) -> pre_μ ∈ map_set (fun μ => 𝝳 (Φ μ)) (coR p);
      preactions_of_spec2 (pre_μ : PreAct) (p : P) : pre_μ ∈ ⌈ (𝝳 ∘ Φ) ⌉ (coR p) -> pre_μ ∈ (coR_abs p);
  }.

(** ** Termination condition *)
Definition bhv_pre_cond1 `{gLts P A, gLts Q A} 
  (p : P) (q : Q) := forall s, p ⇓ s -> q ⇓ s.

Notation "p ≼₁ q" := (bhv_pre_cond1 p q) (at level 70).

(** ** Smyth preorder on acceptance sets *)
Definition bhv_pre_cond2 `{
  gLtsP : @gLts P A H, AbsPT : @AbsAction P T FinA PreAct A H gLtsP gLtsT Φ 𝝳,
  gLtsQ : @gLts Q A H, AbsQT : @AbsAction Q T FinA PreAct A H gLtsQ gLtsT Φ 𝝳}
  (p : P) (q : Q) :=
  forall (s : trace A) q',
    p ⇓ s -> q ⟹[s] q' -> q' ↛ ->
    ∃ p', p ⟹[s] p' /\ p' ↛ /\ (⌈ (𝝳 ∘ Φ) ⌉ (coR p') ⊆ ⌈ (𝝳 ∘ Φ) ⌉ (coR q')).

Notation "p ≼₂ q" := (bhv_pre_cond2 p q) (at level 70).

(** ** Definition of the alternative preorder *)
Definition bhv_pre `{
  gLtsP : @gLts P A H, AbsPT : @AbsAction P T FinA PreAct A H gLtsP gLtsT Φ 𝝳,
  gLtsQ : @gLts Q A H, AbsQT : @AbsAction Q T FinA PreAct A H gLtsQ gLtsT Φ 𝝳}
    (p : P) (q : Q) := 
      p ≼₁ q /\ p ≼₂ q.

Notation "p ≼ₐₛ q" := (bhv_pre p q) (at level 70).

