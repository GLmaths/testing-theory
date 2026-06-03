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
    StateTransitionSystems InteractionBetweenLts Convergence Termination FiniteImageLTS DefinitionAS.

(* https://arxiv.org/pdf/1612.03191.pdf *)

(* Local Open Scope positive. *)

Definition MUST `{
  gLtsP : @gLts P A H, CC : Countable PreAct, @FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 _ gLtsEqT _ _}
  (p : P) (G : gset PreAct) :=
  forall p', p ⟹ p' -> exists β μ p0, ( 𝝳 ∘ Φ ) β ∈ G /\ p' ⟹{μ} p0 /\ dual μ β /\ blocking β.

Definition MUST__s `{
  gLtsP : @gLts P A H, !FiniteImagegLts P A,
  CC : Countable PreAct, @FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 _ gLtsEqT _ _ }
  (ps : gset P) (G : gset PreAct) := 
  forall p, p ∈ ps -> MUST p G.

(* Residuals of a process p AFTER the execution of s. *)

Definition AFTER `{FiniteImagegLts P A} 
  (p : P) (s : trace A) (hcnv : p ⇓ s) := 
  wt_set p s hcnv.

Definition bhv_pre_ms_cond1 `{@gLts P A H, @gLts Q A H} 
(p : P) (q : Q) := forall s, p ⇓ s -> q ⇓ s.

Definition bhv_pre_ms_cond2 `{
  gLtsP : @gLts P A H, !FiniteImagegLts P A, CC : Countable PreAct,
  @FinitaryAbsAction P T FinA PreAct A H Φ 𝝳P _ gLtsEqT _ _,
  gLtsQ : @gLts Q A H, !FiniteImagegLts Q A,
  @FinitaryAbsAction Q T FinA PreAct A H Φ 𝝳Q _ gLtsEqT _ _}
  (p : P) (q : Q) :=
  forall s (hp : p ⇓ s) (hq : q ⇓ s) G, MUST__s (AFTER p s hp) G -> MUST__s (AFTER q s hq) G.

Definition bhv_pre_ms `{
  gLtsP : @gLts P A H, !FiniteImagegLts P A, CC : Countable PreAct,
  @FinitaryAbsAction P T FinA PreAct A H Φ 𝝳P _ gLtsEqT _ _,
  gLtsQ : @gLts Q A H, !FiniteImagegLts Q A,
  @FinitaryAbsAction Q T FinA PreAct A H Φ 𝝳Q _ gLtsEqT _ _}
  (p : P) (q : Q) :=
  bhv_pre_ms_cond1 p q /\ bhv_pre_ms_cond2 p q.

Global Hint Unfold bhv_pre_ms:mdb.

Notation "p 'MUST' G" := (MUST p G) (at level 70).

Notation "p ₁≾ₘᵤₛₜ q" := (bhv_pre_ms_cond1 p q) (at level 70).

Notation "p ₂≾ₘᵤₛₜ q" := (bhv_pre_ms_cond2 p q) (at level 70).

Notation "p ≾ₘᵤₛₜ q" := (bhv_pre_ms p q) (at level 70).

