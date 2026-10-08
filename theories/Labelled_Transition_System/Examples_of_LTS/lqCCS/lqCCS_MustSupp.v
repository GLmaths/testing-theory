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

(** * lqCCS: the must on supports is the must of the two LTSs

    [must_supp] ([lqCCS_AlmostSure.v]) is the classical [must] of the
    repository ([Must.v]), for the process LTS [(P, ρ)] and the observer
    LTS of [lqCCS_LTS.v], linked by [sync] ([must_supp_iff_must]).  With
    [lq_must_as_iff], the almost-sure must of lqCCS is this classical must.

    Hypothesis: the memory is not zero. *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list sets gmap.
From TestingTheory Require Import Lifted Paths States pMust_almost_sure lqCCS_Quantum.
From TestingTheory Require Import lqCCS_Syntax lqCCS_Program lqCCS_Composition lqCCS_Succ
  lqCCS_AlmostSure lqCCS_LTS.
From TestingTheory Require Import ActTau gLts SyncActions Bisimulation Testing_Predicate
  StateTransitionSystems InteractionBetweenLts Must.

Section Bridge.
  Context `{QM : QuantumModel}.

  Lemma nonzero_tr ρ : nonzero ρ ↔ tr ρ ≠ W_zero.
  Proof.
    unfold nonzero. split.
    - intros Hn Hz. by apply Hn, tr_zero_inv.
    - intros Hn ->. apply Hn, tr_szero.
  Qed.

  (** ** Branch steps of [(P, Q)] are the steps of the two LTSs *)

  Lemma ustep_inv P u P' : ustep P u P' →
    match u with
    | UTau => ∃ s, pstep P (LTau s) P'
    | UAct a => ∃ t, pstep P (LAct t a) P'
    end.
  Proof. intros ([s|t a] & <- & Hs); simpl; eauto. Qed.

  (** *** From the steps of the LTSs to branch steps *)

  Lemma proc_tau_bstep P ρ Q x :
    nonzero ρ → (P, ρ) ⟶ x →
    ∃ P' ρ', x = (P', ρ') ∧ bstep ρ (P, Q) (P', Q) ρ' ∧ nonzero ρ'.
  Proof.
    intros Hn Hs. apply pstep_tau in Hs
      as [(P' & -> & Hu)|[(t & E & qs & P' & Hs & ->)|(t & M & qs & y & P0 & k & Hs & Hk & ->)]].
    - apply ustep_inv in Hu as (s & Hs). eexists _, _. split; [done|].
      split; [by econstructor|done].
    - eexists _, _. split; [done|]. split; [by econstructor|].
      apply nonzero_tr. unfold sop_apply. rewrite sop_tr. by apply nonzero_tr.
    - eexists _, _. split; [done|]. split; [by econstructor|done].
  Qed.

  Lemma test_tau_bstep ρ P Q Q' : Q ⟶ Q' → bstep ρ (P, Q) (P, Q') ρ.
  Proof. intros Hs. apply tstep_tau, ustep_inv in Hs as (s & Hs). by econstructor. Qed.

  Lemma sync_bstep P ρ Q μ1 μ2 x Q' :
    nonzero ρ → sync μ1 μ2 → (P, ρ) ⟶[μ1] x → Q ⟶[μ2] Q' →
    ∃ P' ρ', x = (P', ρ') ∧ bstep ρ (P, Q) (P', Q') ρ' ∧ nonzero ρ'.
  Proof.
    intros Hn Hsy Hp Ht. change (μ2 = partner μ1) in Hsy. subst.
    destruct μ1 as [c v|c v|E qs|M qs j]; cbn [partner] in Ht.
    - apply pstep_out in Hp as (P' & -> & Hu). apply ustep_inv in Hu as (t & Hs).
      apply tstep_ext, ustep_inv in Ht as (t' & Ht); [|done].
      eexists _, _. split; [done|]. split; [|done]. by eapply bs_comLR.
    - apply pstep_in in Hp as (P' & -> & Hu). apply ustep_inv in Hu as (t & Hs).
      apply tstep_ext, ustep_inv in Ht as (t' & Ht); [|done].
      eexists _, _. split; [done|]. split; [|done]. by eapply bs_comRL.
    - apply pstep_apply in Hp as ->. apply tstep_ext, ustep_inv in Ht as (t & Ht); [|done].
      eexists _, _. split; [done|]. split; [by eapply bs_opR|].
      apply nonzero_tr. unfold sop_apply. rewrite sop_tr. by apply nonzero_tr.
    - apply pstep_smeas in Hp as (k & <- & Hk & ->).
      apply tstep_meas in Ht as (_ & t & y & Q0 & Ht & ->).
      eexists _, _. split; [done|]. split; [by eapply bs_measR|done].
  Qed.

  (** *** From branch steps to the steps of the LTSs *)

  Lemma bstep_lts ρ P Q P' Q' ρ' :
    bstep ρ (P, Q) (P', Q') ρ' → nonzero ρ' →
      ((P, ρ) ⟶ (P', ρ') ∧ Q' = Q)
    ∨ (Q ⟶ Q' ∧ P' = P ∧ ρ' = ρ)
    ∨ (∃ μ1 μ2, sync μ1 μ2 ∧ (P, ρ) ⟶[μ1] (P', ρ') ∧ Q ⟶[μ2] Q').
  Proof.
    intros Hb Hn. inversion Hb; subst.
    - left. split; [|done]. apply pstep_tau. left. eexists. split; [done|].
      by exists (LTau s).
    - right; left. split_and!; [|done|done]. apply tstep_tau. by exists (LTau s).
    - left. split; [|done]. apply pstep_tau. right; left. eauto 10.
    - right; right. exists (SApply E qs), (TOp E qs). split_and!; [done| |].
      + by apply pstep_apply.
      + apply tstep_ext; [done|]. by exists (LAct t (AOp E qs)).
    - left. split; [|done]. apply pstep_tau. right; right. eauto 20.
    - right; right. exists (SMeas M qs (code _ k)), (TMeas M qs (code _ k)). split_and!; [done| |].
      + apply pstep_smeas. eauto.
      + apply tstep_meas. split; [|eauto 10].
        apply list_elem_of_fmap. exists k. split; [done|]. apply list_elem_of_In, outs_all.
    - right; right. exists (POut c v), (TIn c v). split_and!; [done| |].
      + apply pstep_out. eexists. split; [done|]. by exists (LAct t (AOut c v)).
      + apply tstep_ext; [done|]. by exists (LAct t' (AIn c v)).
    - right; right. exists (PIn c v), (TOut c v). split_and!; [done| |].
      + apply pstep_in. eexists. split; [done|]. by exists (LAct t (AIn c v)).
      + apply tstep_ext; [done|]. by exists (LAct t' (AOut c v)).
  Qed.

  (** A step of non-zero weight has a branch of non-zero weight. *)
  Lemma cstep_nonzero_branch ρ C s Δ :
    cstep ρ C s Δ → nonzero ρ → ∃ C' ρ', (C', ρ') ∈ Δ ∧ nonzero ρ'.
  Proof.
    intros Hs Hn. apply nonzero_tr in Hn. rewrite <- (cstep_mass _ _ _ _ Hs) in Hn.
    clear Hs. induction Δ as [|[C' ρ'] Δ IH]; [done|].
    destruct (decide (nonzero ρ')) as [Hz|Hz].
    - exists C', ρ'. split; [set_solver|done].
    - assert (ρ' = szero) as -> by (unfold nonzero in Hz; destruct (decide (ρ' = szero)); tauto).
      rewrite dmass_cons in Hn. simpl in Hn. rewrite tr_szero, W_add_zero in Hn.
      destruct (IH Hn) as (C'' & ρ'' & Hin & Hnz). exists C'', ρ''. split; [set_solver|done].
  Qed.

  (** ** The theorem *)

  Theorem must_supp_must P ρ Q :
    must_supp (P, Q) ρ → nonzero ρ →
    must (outcome := good) (P, ρ) Q.
  Proof.
    intros Hm. remember (P, Q) as C eqn:EC. revert P Q EC.
    induction Hm as [C ρ Hg|C ρ Hz|C ρ Hg Hex Hall IH]; intros P Q -> Hn.
    - by apply m_now.
    - exfalso. apply nonzero_tr in Hn. contradiction.
    - apply m_step.
      + exact Hg.
      + destruct Hex as (s & Δ & Hs).
        destruct (cstep_nonzero_branch _ _ _ _ Hs Hn) as ([P' Q'] & ρ' & Hin & Hnz).
        pose proof (cstep_branches _ _ _ _ _ _ Hs Hin) as Hb.
        destruct (bstep_lts _ _ _ _ _ _ Hb Hnz)
          as [[Hp ->]|[[Ht [-> ->]]|(μ1 & μ2 & Hsy & Hp & Ht)]].
        * eexists. by apply par_step_left.
        * eexists. by apply par_step_right.
        * eexists. by eapply par_step_sync.
      + intros x Hp. destruct (proc_tau_bstep P ρ Q x Hn Hp) as (P' & ρ' & -> & Hb & Hnz).
        by eapply IH.
      + intros Q' Ht. pose proof (test_tau_bstep ρ P Q Q' Ht) as Hb.
        by eapply IH.
      + intros x Q' μ1 μ2 Hsy Hp Ht.
        destruct (sync_bstep P ρ Q μ1 μ2 x Q' Hn Hsy Hp Ht) as (P' & ρ' & -> & Hb & Hnz).
        by eapply IH.
  Qed.

  Theorem must_must_supp P ρ Q :
    must (outcome := good) (P, ρ) Q → nonzero ρ →
    must_supp (P, Q) ρ.
  Proof.
    intros Hm. remember (P, ρ) as x eqn:Ex. revert P ρ Ex.
    induction Hm as [p t Ho|p t nh ex pt IHpt et IHet com IHcom];
      intros P ρ -> Hn.
    - by apply ms_now.
    - apply ms_step; [exact nh| |].
      + destruct ex as (y & Hy).
        destruct (par_step_inv _ _ _ Hy)
          as [(x & -> & Hp)|[(t' & -> & Ht)|(x & t' & μ1 & μ2 & -> & Hsy & Hp & Ht)]].
        * destruct (proc_tau_bstep P ρ t x Hn Hp) as (P' & ρ' & -> & Hb & _).
          destruct (branch_cstep _ _ _ _ Hb) as (s & Δ & Hs & _). eauto.
        * destruct (branch_cstep _ _ _ _ (test_tau_bstep ρ P t t' Ht)) as (s & Δ & Hs & _).
          eauto.
        * destruct (sync_bstep P ρ t μ1 μ2 x t' Hn Hsy Hp Ht) as (P' & ρ' & -> & Hb & _).
          destruct (branch_cstep _ _ _ _ Hb) as (s & Δ & Hs & _). eauto.
      + intros [P' Q'] ρ' Hb. destruct (decide (nonzero ρ')) as [Hnz|Hz].
        * destruct (bstep_lts _ _ _ _ _ _ Hb Hnz)
            as [[Hp ->]|[[Ht [-> ->]]|(μ1 & μ2 & Hsy & Hp & Ht)]].
          -- by eapply IHpt.
          -- by eapply IHet.
          -- by eapply IHcom.
        * apply ms_zero.
          assert (ρ' = szero) as ->
            by (destruct (decide (ρ' = szero)); [done|by destruct Hz]).
          apply tr_szero.
  Qed.

  Theorem must_supp_iff_must P ρ Q :
    nonzero ρ →
    must_supp (P, Q) ρ ↔ must (outcome := good) (P, ρ) Q.
  Proof.
    intros Hn. split; intros Hm; [by apply must_supp_must|by apply must_must_supp].
  Qed.

  (** ** The almost-sure must of lqCCS is a classical must

      With [lq_must_as_iff] (and its hypotheses: excluded middle, strict
      positivity and density of the probabilities). *)
  Corollary lq_must_as_iff_must
    (XM : ∀ P : Prop, P ∨ ¬ P)
    (W_strict : ∀ a b, W_le (W_add a b) a → b = W_zero)
    (W_dense : ∀ a b : W, a <ₚ b → ∃ c, a <ₚ c ∧ c <ₚ b)
    P ρ Q :
    nonzero ρ →
    (P, ρ) must_as Q ↔ must (outcome := good) (P, ρ) Q.
  Proof.
    intros Hn. rewrite (lq_must_as_iff XM W_strict W_dense).
    by apply must_supp_iff_must.
  Qed.
End Bridge.
