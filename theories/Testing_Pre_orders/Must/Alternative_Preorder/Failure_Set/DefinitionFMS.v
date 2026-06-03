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

Definition Failure `{
  gLtsP : @gLts P A H, CC : Countable PreAct, @FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 _ gLtsEqT _ _ }
  (p : P) (s : trace A) (G : gset PreAct) :=
  p ⇓ s -> exists p', p ⟹[s] p' /\ forall β μ, ( 𝝳 ∘ Φ ) β ∈ G -> dual μ β -> blocking β
  -> ¬ exists p0, p' ⟹{μ} p0.

Definition fail_pre_ms_cond1 `{gLts P A, gLts Q A} 
  (p : P) (q : Q) := forall s, p ⇓ s -> q ⇓ s.

Notation "p ₁⋖ꜰᴀɪʟ q" := (fail_pre_ms_cond1 p q) (at level 70).

Definition fail_pre_ms_cond2 `{ CC : Countable PreAct,
  gLtsP : @gLts P A H, @FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 _ gLtsEqT _ _ ,
  gLtsQ : @gLts Q A H, @FinitaryAbsAction Q T FinA PreAct A H Φ 𝝳 _ gLtsEqT _ _ }
  (p : P) (q : Q) :=
  forall s G, Failure q s G -> Failure p s G.

Notation "p ₂⋖ꜰᴀɪʟ q" := (fail_pre_ms_cond1 p q) (at level 70).

Definition fail_pre_ms `{ CC : Countable PreAct,
  gLtsP : @gLts P A H, @FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 _ gLtsEqT _ _ ,
  gLtsQ : @gLts Q A H, @FinitaryAbsAction Q T FinA PreAct A H Φ 𝝳 _ gLtsEqT _ _ }
  (p : P) (q : Q) :=
  fail_pre_ms_cond1 p q /\ fail_pre_ms_cond2 p q.

Global Hint Unfold fail_pre_ms:mdb. 

Notation "p ⋖ꜰᴀɪʟ q" := (fail_pre_ms p q) (at level 70).

