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
(* * lqCCS: well-typed tested configurations

    A tested configuration [ρ • (P, Q)] — a process [P] and an observer [Q]
    sharing the memory [ρ] — is well typed when [P] and [Q] own disjoint sets
    of qubits, all in [ρ] (the paper's configuration typing, Definition 4.3,
    with the context of Definition 5.3 owning the observer's qubits).

    - [bstep_wt_conf]: every branch of a step keeps a configuration well
      typed;
    - [com_owner], [op_owner]: in a well-typed configuration, the side
      conditions that the paper's semantics checks and ours does not
      ([lqCCS.Language.Program]) always hold: a qubit received comes from [ρ] and is
      owned by the sender, so not by the receiver (rules [Recv], [ParL],
      [ParR]); an operation or a measurement acts on qubits owned by the
      component that performs it. *)

From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base countable decidable list sets gmap.
From TestingTheory Require Import lqCCS.Harmony_Lemma.Lifted lqCCS.Harmony_Lemma.Paths lqCCS.Harmony_Lemma.States lqCCS.Language.Quantum.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.Program lqCCS.Language.Composition lqCCS.Characterisations.AlmostSure
  lqCCS.Language.Typing.
Section TypedConf.
  Context `{QM : QuantumModel}.
  Context (qchan : chan → bool) (qvar : var → bool).

  Notation wt := (wt qchan qvar).
  Notation sr_post := (sr_post qchan qvar).

  Definition in_state (ρ : St) (Σ : gset qt) : Prop := ∀ q, QN q ∈ Σ → q ∈ St_qubits ρ.

  Definition wt_conf (ρ : St) (C : conf) : Prop :=
    ∃ ΣP ΣQ, wt ΣP C.1 ∧ wt ΣQ C.2 ∧ ΣP ## ΣQ ∧ names (ΣP ∪ ΣQ) ∧ in_state ρ (ΣP ∪ ΣQ).

  Lemma in_state_sop E qs ρ Σ : in_state ρ Σ → in_state (sop_apply E qs ρ) Σ.
  Proof. intros Hs q Hq. unfold sop_apply. rewrite sop_qubits. by apply Hs. Qed.

  Lemma in_state_meas M qs k ρ Σ : in_state ρ Σ → in_state (meas_branch M qs k ρ) Σ.
  Proof. intros Hs q Hq. unfold meas_branch. rewrite meas_qubits. by apply Hs. Qed.

  (* A communication from [P] to [Q] in a well-typed configuration: on a
      qubit channel, the qubit is in [ρ], owned by [P] and not by [Q]; the
      configuration stays well typed. *)
  Lemma com_owner ρ P Q ΣP ΣQ t t' c v P' Q' :
    wt ΣP P → wt ΣQ Q → ΣP ## ΣQ → in_state ρ (ΣP ∪ ΣQ) →
    pstep P (LAct t (AOut c v)) P' → pstep Q (LAct t' (AIn c v)) Q' →
    (qchan c = true → ∃ q, v = VQubit q ∧ q ∈ St_qubits ρ ∧ QN q ∈ ΣP ∧ QN q ∉ ΣQ)
    ∧ ∃ ΣP' ΣQ', wt ΣP' P' ∧ wt ΣQ' Q' ∧ ΣP' ## ΣQ' ∧ ΣP' ∪ ΣQ' = ΣP ∪ ΣQ.
  Proof.
    intros HP HQ Hd Hs Hp Hq.
    pose proof (subject_reduction qchan qvar _ _ _ _ HP Hp) as SP.
    pose proof (subject_reduction qchan qvar _ _ _ _ HQ Hq) as SQ.
    simpl in SP, SQ. destruct (qchan c).
    - destruct SP as (q & -> & Hin & HP').
      assert (Hn : QN q ∉ ΣQ) by set_solver.
      split.
      + intros _. exists q. split_and!; [done| |done|done]. apply Hs. set_solver.
      + exists (ΣP ∖ {[QN q]}), ({[QN q]} ∪ ΣQ). split_and!.
        * done.
        * by apply SQ.
        * set_solver.
        * symmetry. by apply move_l.
    - destruct SP as [Hv HP']. split; [done|].
      exists ΣP, ΣQ. split_and!; auto.
  Qed.

  Lemma bstep_wt_conf ρ C C' ρ' : wt_conf ρ C → bstep ρ C C' ρ' → wt_conf ρ' C'.
  Proof.
    intros (ΣP & ΣQ & HP & HQ & Hd & Hn & Hs) Hb.
    inversion Hb as [P Q s P' Hp|P Q s Q' Hq|P Q t E qs P' Hp|P Q t E qs Q' Hq
                    |P Q t M qs x P' k Hp|P Q t M qs x Q' k Hq
                    |P Q t t' c v P' Q' Hp Hq|P Q t t' c v P' Q' Hp Hq]; subst; simpl in *.
    - pose proof (subject_reduction qchan qvar _ _ _ _ HP Hp) as SP.
      exists ΣP, ΣQ. split_and!; auto.
    - pose proof (subject_reduction qchan qvar _ _ _ _ HQ Hq) as SQ.
      exists ΣP, ΣQ. split_and!; auto.
    - pose proof (subject_reduction qchan qvar _ _ _ _ HP Hp) as [_ SP].
      exists ΣP, ΣQ. split_and!; auto. by apply in_state_sop.
    - pose proof (subject_reduction qchan qvar _ _ _ _ HQ Hq) as [_ SQ].
      exists ΣP, ΣQ. split_and!; auto. by apply in_state_sop.
    - pose proof (subject_reduction qchan qvar _ _ _ _ HP Hp) as (_ & Hx & SP).
      exists ΣP, ΣQ. split_and!; auto.
      + by apply (proj1 (wt_subst_c qchan qvar)).
      + by apply in_state_meas.
    - pose proof (subject_reduction qchan qvar _ _ _ _ HQ Hq) as (_ & Hx & SQ).
      exists ΣP, ΣQ. split_and!; auto.
      + by apply (proj1 (wt_subst_c qchan qvar)).
      + by apply in_state_meas.
    - destruct (com_owner ρ' P Q ΣP ΣQ t t' c v P' Q' HP HQ Hd Hs Hp Hq)
        as [_ (ΣP' & ΣQ' & HP' & HQ' & Hd' & HU)].
      exists ΣP', ΣQ'. rewrite HU. split_and!; done.
    - destruct (com_owner ρ' Q P ΣQ ΣP t' t c v Q' P' HQ HP ltac:(set_solver)
                  ltac:(by rewrite union_comm_L) Hq Hp)
        as [_ (ΣQ' & ΣP' & HQ' & HP' & Hd' & HU)].
      assert (HU' : ΣP' ∪ ΣQ' = ΣP ∪ ΣQ) by (rewrite union_comm_L, HU; apply union_comm_L).
      exists ΣP', ΣQ'. rewrite HU'. split_and!; [done|done|set_solver|done|done].
  Qed.

  (* An operation or a measurement of a component acts on qubits it owns,
      which are in [ρ] and not owned by the other component. *)
  Lemma op_owner ρ P ΣP ΣQ t E qs P' :
    wt ΣP P → ΣP ## ΣQ → in_state ρ (ΣP ∪ ΣQ) → pstep P (LAct t (AOp E qs)) P' →
    ∀ q, q ∈ qs → q ∈ St_qubits ρ ∧ QN q ∈ ΣP ∧ QN q ∉ ΣQ.
  Proof.
    intros HP Hd Hs Hp q Hq.
    destruct (subject_reduction qchan qvar _ _ _ _ HP Hp) as [Hsub _].
    assert (Hin : QN q ∈ ΣP).
    { apply Hsub, elem_of_list_to_set, list_elem_of_fmap. by exists q. }
    split_and!; [apply Hs; set_solver|done|set_solver].
  Qed.

  Lemma meas_owner ρ P ΣP ΣQ t M qs x P' :
    wt ΣP P → ΣP ## ΣQ → in_state ρ (ΣP ∪ ΣQ) → pstep P (LAct t (AMeas M qs x)) P' →
    ∀ q, q ∈ qs → q ∈ St_qubits ρ ∧ QN q ∈ ΣP ∧ QN q ∉ ΣQ.
  Proof.
    intros HP Hd Hs Hp q Hq.
    destruct (subject_reduction qchan qvar _ _ _ _ HP Hp) as [Hsub _].
    assert (Hin : QN q ∈ ΣP).
    { apply Hsub, elem_of_list_to_set, list_elem_of_fmap. by exists q. }
    split_and!; [apply Hs; set_solver|done|set_solver].
  Qed.
End TypedConf.
(* end hide *)
