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

Section failure.

  Definition Failure `{FiniteImagegLts P A} 
    (p : P) (s : trace A) (G : gset A) :=
    p ⇓ s -> exists p', p ⟹[s] p' /\ forall μ, μ ∈ G -> ¬ exists p0, p' ⟹{μ} p0.

  Definition fail_pre_ms_cond1 `{gLts P A, gLts Q A} 
  (p : P) (q : Q) := forall s, p ⇓ s -> q ⇓ s.

  Definition fail_pre_ms_cond2 `{@FiniteImagegLts P A H gLtsP, @FiniteImagegLts Q A H gLtsQ} 
    (p : P) (q : Q) :=
    forall s G, Failure q s G -> Failure p s G.

  Definition fail_pre_ms `{@FiniteImagegLts P A H gLtsP, @FiniteImagegLts Q A H gLtsQ} 
    (p : P) (q : Q) :=
    fail_pre_ms_cond1 p q /\ fail_pre_ms_cond2 p q.

End failure.

Global Hint Unfold fail_pre_ms:mdb. 

Notation "p ⋖₁ q" := (fail_pre_ms_cond1 p q) (at level 70).

Notation "p ⋖₂ q" := (fail_pre_ms_cond1 p q) (at level 70).

Notation "p ⋖ q" := (fail_pre_ms p q) (at level 70).

