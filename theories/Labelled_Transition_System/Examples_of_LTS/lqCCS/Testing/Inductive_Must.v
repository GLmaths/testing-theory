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
From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list.
From TestingTheory Require Import ActTau pMust_scheduled pMust_almost_sure pMust_smyth pMust_transfer pMust_canonical pMust_inductive.
From TestingTheory Require Import lqCCS.Harmony_Lemma.Lifted lqCCS.Harmony_Lemma.Paths lqCCS.Harmony_Lemma.States lqCCS.Language.Quantum lqCCS.Language.Quantum_Weights.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.LTS lqCCS.Testing.Scheduled lqCCS.Testing.DistLTS lqCCS.Testing.Programs lqCCS.Testing.Observers lqCCS.Testing.Smyth_Soundness lqCCS.Testing.Canonical lqCCS.Testing.Branching.

#[local] Open Scope lqccs_scope.

Theorem ctx_pre_pmust `{QM : QuantumModel} (W_total : ∀ a b : W, W_le a b ∨ W_le b a) (DC : dep_choice)
    (Ts : proc → Prop) (p q : proc * St) :
  ctx_pre_sm_on Stay Ts p q ↔ ∀ T, Ts T → pmust_pre (compose p T) (compose q T).
Proof.
  assert (Hfin : ∀ D : dist (proc * proc), fin (rstep lq_SchedSts D)).
  { apply rstep_fin. intros ρ c.
    apply (fin_mono _ (λ Δ, ∃ Δ0, (∃ s, sched_step ρ (par_of c) s Δ0) ∧ dmap par_of Δ = Δ0)).
    - intros Δ (s & Hs). exists (dmap par_of Δ). split; [by exists s|done].
    - apply (fin_bind _ _ (sched_fin ρ (par_of c))). intros Δ0 _. apply fin_uniq.
      intros x y <-. revert y. induction x as [|[[P1 T1] ρ1] x IH]; intros [|[[P2 T2] ρ2] y] E; try done.
      simpl in E. injection E as -> -> -> E. f_equal. by apply IH. }
  assert (Wt : ∀ a b : prob (Weights := Weights_of_QuantumModel), a ≤ₚ b ∨ b ≤ₚ a) by exact W_total.
  split; intros Hc T HT.
  - apply (smyth_pmust (SS := lq_SchedSts) Wt Hfin DC). exact (Hc T HT).
  - apply (smyth_pmust (SS := lq_SchedSts) Wt Hfin DC). exact (Hc T HT).
Qed.
(* end hide *)
