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
(* begin hide *)
From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list.
From TestingTheory Require Import ActTau pMust_scheduled pMust_almost_sure pMust_smyth pMust_transfer pMust_canonical.
From TestingTheory Require Import lqCCS.Harmony_Lemma.Lifted lqCCS.Harmony_Lemma.Paths lqCCS.Harmony_Lemma.States lqCCS.Language.Quantum lqCCS.Language.Quantum_Weights.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.LTS lqCCS.Testing.Scheduled lqCCS.Testing.DistLTS lqCCS.Testing.Programs lqCCS.Testing.Observers lqCCS.Testing.Smyth_Soundness lqCCS.Testing.Canonical lqCCS.Testing.Final.

#[local] Open Scope lqccs_scope.

Section Trace.
  Context `{QM : QuantumModel} (p q : proc * St).

  Definition visited (r : nat → dist comp) (n : node) : Prop := ∃ i c ρ, (c, ρ) ∈ r i ∧ c.1 = n.

  Definition used_by (O : node → list msg) (S : node → bool) (r : nat → dist comp) (w : nat → item) :
      node → offer → Prop :=
    cells (M := lq_menu O) S r w.

  Definition computation (O : node → list msg) (S : node → bool) (r : nat → dist comp) (w : nat → item) : Prop :=
    run_word (M := lq_menu O) (used_by O S r w) S (dinit O q) r w
    ∧ fin (visited r).

  Definition quiet_outside (O : node → list msg) (S : node → bool) (r : nat → dist comp) : Prop :=
    ∀ n, ¬ visited r n → S n = true ∧ O n = [].

  Definition cells_sync (O : node → list msg) (S : node → bool) (Ch : channel → Prop) (K : tag → okind)
      (r : nat → dist comp) (w : nat → item) : Prop :=
    ∀ n o, used_by O S r w n o → real_off p q Ch K o.

  Definition outputs_sync (O : node → list msg) (S : node → bool) (Ch : channel → Prop) (K : tag → okind) : Prop :=
    ∀ n k c v, S n = false → (k, c, v) ∈ O n → K k = KOut ∧ k ∉ tags p.1 ∧ k ∉ tags q.1 ∧ Ch c.

  Definition one_output_per_tag (O : node → list msg) (S : node → bool) : Prop :=
    ∀ n k c v c' v', S n = false → (k, c, v) ∈ O n → (k, c', v') ∈ O n → c = c' ∧ v = v'.

  Definition outputs_persist (O : node → list msg) (S : node → bool) : Prop :=
    ∀ n a m, S (n ++ [a]) = false → m ∈ O n → m ∈ O (n ++ [a]).

  Definition coherent (O : node → list msg) (S : node → bool) (Ch : channel → Prop) (K : tag → okind)
      (r : nat → dist comp) (w : nat → item) : Prop :=
    ext_closed S ∧ quiet_outside O S r ∧ cells_sync O S Ch K r w ∧ outputs_sync O S Ch K
    ∧ one_output_per_tag O S ∧ outputs_persist O S.

  Definition refused_by (O : node → list msg) (S : node → bool) (r : nat → dist comp) (w : nat → item) :
      node → offer → Prop :=
    refused (M := lq_menu O) (used_by O S r w) S r w.

  Definition trace_menu (O : node → list msg) (S : node → bool) (Ch : channel → Prop) (K : tag → okind)
      (r : nat → dist comp) (w : nat → item) : node → offer → Prop :=
    Jstar (M := lq_menu O) (real_off p q Ch K) (used_by O S r w) S r w.

  Definition trace_succ (O : node → list msg) (S : node → bool) (Ch : channel → Prop) (K : tag → okind)
      (r : nat → dist comp) (w : nat → item) : node → bool :=
    Sstar (M := lq_menu O) (real_off p q Ch K) (used_by O S r w) S r w.

  Definition trace_sts (O : node → list msg) (S : node → bool) (Ch : channel → Prop) (K : tag → okind)
      (r : nat → dist comp) (w : nat → item) : SchedSts comp item :=
    mdlts (M := lq_menu O) (trace_menu O S Ch K r w) (trace_succ O S Ch K r w).

  Lemma trace_menu_spec O S Ch K r w n o :
    trace_menu O S Ch K r w n o ↔ used_by O S r w n o ∨ (real_off p q Ch K o ∧ ¬ refused_by O S r w n o).
  Proof. done. Qed.

  Lemma trace_succ_spec O S Ch K r w n :
    trace_succ O S Ch K r w n = true ↔
    S n = true ∨ ∃ m a m2, n = m ++ [a] ++ m2 ∧ trace_menu O S Ch K r w m (offer_of a)
                           ∧ ¬ used_by O S r w m (offer_of a).
  Proof.
    split.
    - intros Hs. exact (Sstar_inv (M := lq_menu O) _ _ _ _ _ _ Hs).
    - intros [Hs|Hc]; [by apply Sstar_S|by apply Sstar_crossed].
  Qed.

  Definition alt_trace : Prop :=
    ∀ O S Ch K r w, coherent O S Ch K r w → computation O S r w →
      ∃ r', is_run (SchedSts0 := trace_sts O S Ch K r w) Stay (dinit O p) r'
          ∧ run_le (SchedSts0 := trace_sts O S Ch K r w) r' r.
End Trace.
(* end hide *)
