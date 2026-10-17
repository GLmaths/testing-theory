(* begin hide *)
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
(* end hide *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib Require Import Relations.Relation_Definitions Classes.RelationClasses.
From stdpp Require Import base tactics decidable countable gmap.
From TestingTheory Require Import ActTau gLts SyncActions Bisimulation Subset_Act coWeakTransition coConvergence.

Definition convergence_preorder_on_co_trace `{gLtsP : @gLts P Ap Hp}
  `{Ht : ExtAction At} `{SA : !SyncAction Ap At}
  (p : P) (q : P) := ∀ (s : trace At), p ⇓ᶜᵒ s → q ⇓ᶜᵒ s.

Notation "p ꜀ₙᵥ≼꜀ₒ₋ₐₛ q" := (convergence_preorder_on_co_trace p q) (at level 70, format "p  ꜀ₙᵥ≼꜀ₒ₋ₐₛ  q").

Definition acceptance_set_preorder_on_co_trace `{gLtsP : @gLts P Ap Hp}
  `{Ht : ExtAction At} `{SA : !SyncAction Ap At} {PreAct : Type} (Γ : At → PreAct)
  (p : P) (q : P) :=
  ∀ (s : trace At) q',
    p ⇓ᶜᵒ s → q ⟹ᶜᵒ[s] q' → q' ↛ →
    ∃ p', p ⟹ᶜᵒ[s] p' ∧ p' ↛ ∧ ⌈ Γ ⌉ (coR p') ⊆ ⌈ Γ ⌉ (coR q').

Notation "p ₐ꜀꜀≼꜀ₒ₋ₐₛ[ Γ ] q" := (acceptance_set_preorder_on_co_trace Γ p q) (at level 70, format "p  ₐ꜀꜀≼꜀ₒ₋ₐₛ[ Γ ]  q").

Definition cnv_acceptance_set_preorder_on_co_trace `{gLtsP : @gLts P Ap Hp}
  `{Ht : ExtAction At} `{SA : !SyncAction Ap At} {PreAct : Type} (Γ : At → PreAct)
  (p : P) (q : P) :=
  convergence_preorder_on_co_trace (At := At) p q ∧ p ₐ꜀꜀≼꜀ₒ₋ₐₛ[ Γ ] q.

Notation "p ≼꜀ₒ₋ₐₛ[ Γ ] q" := (cnv_acceptance_set_preorder_on_co_trace Γ p q) (at level 70, format "p  ≼꜀ₒ₋ₐₛ[ Γ ]  q").