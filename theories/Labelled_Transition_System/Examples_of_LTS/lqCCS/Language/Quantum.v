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
(* * lqCCS: an abstract model of quantum states

    The semantics of lqCCS (Ceragioli, Gadducci, Lomurno, Tedeschi,
    arXiv:2604.23756, Section 6) only uses a handful of operations on density
    operators.  They are taken from the abstract algebra of
    [Harmony_lemma/]: super-operators [T] ([Alg], [FinAlg]) acting linearly
    on states [St] ([StAlg]).  This file only adds what lqCCS needs on top:

    - names: a superoperator [E] applied to qubits [q̃] is an atomic
      operation [sop_act E q̃ : Act], a measurement [M] on [q̃] is
      [meas_of M q̃ : Meas]; padding [E] to the whole state ([E^q̃] in the
      paper) is the instance's business;
    - states are partial density operators, not normalised: addition is
      total, and the bound [tr ≤ 1] of the paper (Definition 6.1) is a
      property of distributions, not of [St];
    - a trace [tr] into an ordered commutative monoid [W] of probabilities,
      for which superoperators are trace preserving and measurements
      complete ([br m (λ _, one)] is [Σ_k ℳ_k]);
    - linearity in the state, which [StAlg] states in the operator only;
    - the qubits of a state ([Σ_ρ]) and partial traces, for typing and for
      the environment of a distribution (Definition 6.6);
    - [EqDecision St], because [gLts] asks for decidable states.  A model
      over the real numbers cannot provide it constructively; this is the
      price of reusing the existing development as it is. *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib Require Import List.
From stdpp Require Import base countable decidable gmap.
From TestingTheory Require Import lqCCS.Harmony_Lemma.Lifted lqCCS.Harmony_Lemma.Paths lqCCS.Harmony_Lemma.States pMust_almost_sure lqCCS.Language.Syntax.
Class QuantumModel `{StAlg} := MkQuantumModel {
    (* Names of the syntax. *)
    sop_act : sop → list qubit → Act;
    meas_of : meas → list qubit → Meas;

    (* States: a commutative monoid, acted upon linearly. *)
    St_eqdec :: EqDecision St;
    sadd_comm ρ σ : sadd ρ σ = sadd σ ρ;
    sadd_assoc ρ σ θ : sadd ρ (sadd σ θ) = sadd (sadd ρ σ) θ;
    sadd_szero_l ρ : sadd szero ρ = ρ;
    app_sadd a ρ σ : app a (sadd ρ σ) = sadd (app a ρ) (app a σ);

    (* Probabilities. *)
    W : Type;
    W_zero : W;
    W_add : W → W → W;
    W_le : W → W → Prop;
    W_le_preorder :: PreOrder W_le;
    W_add_comm a b : W_add a b = W_add b a;
    W_add_assoc a b c : W_add a (W_add b c) = W_add (W_add a b) c;
    W_add_zero a : W_add W_zero a = a;
    W_zero_le a : W_le W_zero a;
    W_add_mono a b c : W_le a b → W_le (W_add a c) (W_add b c);

    (* Trace. *)
    tr : St → W;
    tr_szero : tr szero = W_zero;
    tr_sadd ρ σ : tr (sadd ρ σ) = W_add (tr ρ) (tr σ);
    (* Positivity: only [O] has trace zero. *)
    tr_zero_inv ρ : tr ρ = W_zero → ρ = szero;
    (* Superoperators of the syntax are trace preserving. *)
    sop_tr E qs ρ : tr (app (act (sop_act E qs)) ρ) = tr ρ;
    (* Completeness of measurements, [Σ_k M_k† M_k = I], read on traces. *)
    meas_tr M qs ρ : tr (app (br (meas_of M qs) (λ _, one)) ρ) = tr ρ;

    (* Qubits of a state, preserved by the operations of the syntax. *)
    St_qubits : St → gset qubit;
    sop_qubits E qs ρ : St_qubits (app (act (sop_act E qs)) ρ) = St_qubits ρ;
    meas_qubits M qs k ρ :
      St_qubits (app (kraus (meas_of M qs) k) ρ) = St_qubits ρ;

    (* Partial trace [tr_Σ'(ρ)]. *)
    ptrace : gset qubit → St → St;
    ptrace_sadd Σ ρ σ : ptrace Σ (sadd ρ σ) = sadd (ptrace Σ ρ) (ptrace Σ σ);
    ptrace_tr Σ ρ : tr (ptrace Σ ρ) = tr ρ;
  }.

Arguments W {_ _ _ _ _}.

(* [E^q̃(ρ)] and the branch [k] of [M^q̃(ρ)], unnormalised: its trace is
    the probability of outcome [k]. *)
Definition sop_apply `{QuantumModel} E qs ρ := app (act (sop_act E qs)) ρ.
Definition meas_branch `{QuantumModel} M qs (k : Out (meas_of M qs)) ρ :=
  app (kraus (meas_of M qs) k) ρ.

(* ** First consequences *)

Section Consequences.
  Context `{QuantumModel}.

  Lemma sadd_szero_r ρ : sadd ρ szero = ρ.
  Proof. by rewrite sadd_comm, sadd_szero_l. Qed.

  Lemma W_add_zero_r a : W_add a W_zero = a.
  Proof. by rewrite W_add_comm, W_add_zero. Qed.

  Lemma sop_szero E qs : sop_apply E qs szero = szero.
  Proof. apply app_szero. Qed.

  Lemma tr_ssum l : tr (ssum l) = fold_right W_add W_zero (map tr l).
  Proof. induction l; simpl; [apply tr_szero | by rewrite tr_sadd, IHl]. Qed.

  Lemma le_fold_right x l :
    In x l → W_le x (fold_right W_add W_zero l).
  Proof.
    induction l as [|y l IH]; [done|]. simpl. intros [->|Hin].
    - rewrite <- (W_add_zero x) at 1. rewrite (W_add_comm x).
      apply W_add_mono, W_zero_le.
    - etransitivity; [by apply IH|].
      rewrite <- (W_add_zero (fold_right _ _ l)) at 1.
      apply W_add_mono, W_zero_le.
  Qed.

  (* A measurement branch never weighs more than the state it comes from. *)
  Lemma meas_branch_le M qs k ρ : W_le (tr (meas_branch M qs k ρ)) (tr ρ).
  Proof.
    rewrite <- (meas_tr M qs ρ), br_sum. fold (sum (map (λ k, one ⋅ kraus (meas_of M qs) k)
                                                 (outs (meas_of M qs)))).
    rewrite app_ssum, tr_ssum, !map_map.
    apply le_fold_right, in_map_iff. exists k. split; [|apply outs_all].
    unfold meas_branch. by rewrite comp_1l.
  Qed.

  Lemma fold_W_zero l : (∀ x, x ∈ l → x = W_zero) → fold_right W_add W_zero l = W_zero.
  Proof.
    induction l as [|x l IH]; simpl; [done|]. intros Hl.
    rewrite (Hl x) by set_solver. rewrite IH by set_solver. apply W_add_zero.
  Qed.

  (* A measurement of a non-zero state has an outcome of non-zero weight. *)
  Lemma meas_nonzero_branch M qs ρ : ρ ≠ szero → ∃ k, meas_branch M qs k ρ ≠ szero.
  Proof.
    intros Hρ.
    destruct (decide (Exists (λ k, meas_branch M qs k ρ ≠ szero) (outs (meas_of M qs))))
      as [HE|HE].
    - apply Exists_exists in HE as (k & _ & Hk). eauto.
    - exfalso. apply Hρ, tr_zero_inv.
      rewrite <- (meas_tr M qs ρ), br_sum. fold (sum (map (λ k, one ⋅ kraus (meas_of M qs) k)
                                                   (outs (meas_of M qs)))).
      rewrite app_ssum, tr_ssum, !map_map. apply fold_W_zero.
      intros w (k & -> & Hk)%list_elem_of_fmap. rewrite comp_1l.
      destruct (decide (meas_branch M qs k ρ = szero)) as [Hz|Hz].
      + unfold meas_branch in Hz. by rewrite Hz, tr_szero.
      + exfalso. apply HE, Exists_exists. exists k. split; [done|done].
  Qed.
End Consequences.

(* ** Weights of the probabilistic must

    Quantum distributions (Definition 6.1) are distributions in the sense of
    [pMust_almost_sure] whose weights are states and whose mass is the
    trace. *)
#[global] Instance Weights_of_QuantumModel `{QuantumModel} : Weights := {|
  prob := W;
  prob_zero := W_zero;
  prob_add := W_add;
  prob_le := W_le;
  weight := St;
  weight_zero := szero;
  weight_add := sadd;
  weight_add_comm := sadd_comm;
  weight_add_assoc := sadd_assoc;
  weight_add_zero := sadd_szero_l;
  mass := tr;
|}.
(* end hide *)
