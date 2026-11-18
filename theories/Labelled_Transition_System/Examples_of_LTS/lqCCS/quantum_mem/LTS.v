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

(* * LTS of the quantum memory *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base gmultiset countable decidable list sets numbers.
From TestingTheory Require Import ActTau.
From TestingTheory Require Import lqCCS.General_definition.Algebra lqCCS.quantum_mem.Syntax.
From TestingTheory Require Import lqCCS.lqCCS_prog.Syntax lqCCS.General_definition.Parallel_choice_LTS.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

Reserved Notation "ρ ⟶ₘ{ μ } ρ'" (at level 70, format "ρ  ⟶ₘ{ μ }  ρ'").
Reserved Notation "? ℰ" (at level 30, ℰ at level 9, format "?  ℰ").
Reserved Notation "ℳ !ₘ n" (at level 30, n at level 9, format "ℳ  !ₘ  n").

Section Memory.
  Context `{QM : QuantumModel}.

  Inductive mem_action : Type :=
  | MeSop (ℰ : Act)
  | MeMeas (ℳ : Meas) (n : nat).

  Notation "? ℰ" := (MeSop ℰ) : lqccs_scope.
  Notation "ℳ !ₘ n" := (MeMeas ℳ n) : lqccs_scope.

  Inductive mem_step : St → choice → Labels mem_action → St → Prop :=
  | me_sop ρ (ℰ : Act) :
      ρ ⟶ₘ{? ℰ} (ℰ · ρ)
  | me_meas ρ ℳ n :
      n ∈ outs ℳ → ρ ⟶ₘ{ℳ !ₘ n} (ℳ ·[n] ρ)
  where "ρ ⟶ₘ{ μ } ρ'" := (mem_step ρ ∅ (ActExt (μ : mem_action)) ρ') : lqccs_scope.

  Lemma mem_step_choice ρ c 𝜆 ρ' : mem_step ρ c 𝜆 ρ' → c = ∅ ∧ ∃ μ, 𝜆 = ActExt μ.
  Proof. inversion 1; eauto. Qed.
End Memory.

Notation "? ℰ" := (MeSop ℰ) : lqccs_scope.
Notation "ℳ !ₘ n" := (MeMeas ℳ n) : lqccs_scope.
Notation "ρ ⟶ₘ{ μ } ρ'" := (mem_step ρ ∅ (ActExt (μ : mem_action)) ρ')
  (at level 70, only parsing) : lqccs_scope.
Notation "ρ ⟶ₘ{ μ } ρ'" := (mem_step ρ ∅ (ActExt μ) ρ')
  (at level 70, only printing, format "ρ  ⟶ₘ{ μ }  ρ'") : lqccs_scope.
Notation "ρ ↛ₘ{ μ } ρ'" := (¬ mem_step ρ ∅ (ActExt μ) ρ') (at level 70, format "ρ  ↛ₘ{ μ }  ρ'") : lqccs_scope.