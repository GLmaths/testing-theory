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

From Coq.Unicode Require Import Utf8.
From Coq.Program Require Import Equality.
From stdpp Require Import finite gmap decidable.
From Must Require Import ActTau gLts Bisimulation Lts_OBA Subset_Act WeakTransitions Testing_Predicate
    StateTransitionSystems InteractionBetweenLts Convergence Termination FiniteImageLTS.

Section must_sets.

  (* https://arxiv.org/pdf/1612.03191.pdf *)

  Local Open Scope positive.

  Definition MUST `{gLts P A} 
    (p : P) (G : gset A) :=
    forall p', p ⟹ p' -> exists μ p0, μ ∈ G /\ p' ⟹{μ} p0.

  Definition MUST__s `{FiniteImagegLts P A} 
    (ps : gset P) (G : gset A) := 
    forall p, p ∈ ps -> MUST p G.

  (* Residuals of a process p AFTER the execution of s. *)

  Definition AFTER `{FiniteImagegLts P A} 
    (p : P) (s : trace A) (hcnv : p ⇓ s) := 
    wt_set p s hcnv. 

  Definition bhv_pre_ms_cond1 `{gLts P A, gLts Q A} 
  (p : P) (q : Q) := forall s, p ⇓ s -> q ⇓ s.

  Definition bhv_pre_ms_cond2 `{@FiniteImagegLts P A H gLtsP, @FiniteImagegLts Q A H gLtsQ} 
    (p : P) (q : Q) :=
    forall s h1 h2 G, MUST__s (AFTER p s h1) G -> MUST__s (AFTER q s h2) G.

  Definition bhv_pre_ms `{@FiniteImagegLts P A H gLtsP, @FiniteImagegLts Q A H gLtsQ} 
    (p : P) (q : Q) :=
    bhv_pre_ms_cond1 p q /\ bhv_pre_ms_cond2 p q.
End must_sets.

Global Hint Unfold bhv_pre_ms:mdb.

Notation "p ≾₁ q" := (bhv_pre_ms_cond1 p q) (at level 70).

Notation "p ≾₂ q" := (bhv_pre_ms_cond2 p q) (at level 70).

Notation "p ≾ q" := (bhv_pre_ms p q) (at level 70).

