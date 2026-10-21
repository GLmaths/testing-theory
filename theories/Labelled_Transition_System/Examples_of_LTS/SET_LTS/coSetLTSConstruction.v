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

From Stdlib Require ssreflect Setoid.
From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From Stdlib.Program Require Import Wf Equality.

From stdpp Require Import base countable finite gmap list gmultiset.

From TestingTheory Require Import ActTau gLts SyncActions Bisimulation FiniteImageLTS
    coFiniteImage InListPropHelper Termination Convergence WeakTransitions

  coWeakTransition coConvergence.

(** *** The LTS of sets, co version *)

Section coSetLTS.

Context {P Aproc Atest : Type}.
Context `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest}.
Context `{gLtsP : !gLts P Hp}.
Context `{SA : !SyncAction Aproc Atest}.
Context `{CFI : !coFiniteImagegLts P Atest}.

End coSetLTS.

(** ***** [coToSET] itself *)

#[global] Program Instance coToSET {P Aproc Atest : Type}
  `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest} `{gLtsP : !gLts P Hp}
  `{SA : !SyncAction Aproc Atest} `{CFI : !coFiniteImagegLts P Atest} :
  gLts (gset P) Ht.
Next Obligation.
  intros. destruct X.
  + exact (H0 = colts_extaction_set_from_pset H μ ∧ H0 ≠ ∅).
  + exact (H0 = colts_tau_set_from_pset H ∧ H0 ≠ ∅).
Defined.
Next Obligation.
  intros; simpl in *. unfold coToSET_obligation_1.
  destruct 𝜆.
  - destruct (decide (b = colts_extaction_set_from_pset a μ ∧ b ≠ ∅)).
    + left. eauto.
    + right. eauto.
  - destruct (decide (b = colts_tau_set_from_pset a ∧ b ≠ ∅)).
    + left. eauto.
    + right. eauto.
Qed.
Next Obligation.
  intros. destruct X.
  + exact (¬ ∀ p, p ∈ H → ∀ μ', sync μ' μ → (p ↛[μ'])).
  + exact (¬ ∀ p, p ∈ H → (p ↛)).
Defined.
Next Obligation.
  intros. simpl in *. unfold coToSET_obligation_3.
  destruct 𝜆 as [η |]; apply not_dec.
  - destruct (colts_extaction_set_from_pset_ispec p η) as (Espec1 & Espec2).
    destruct (decide (colts_extaction_set_from_pset p η = ∅)) as [Hemp | Hnemp].
    + left. intros p' mem μ hsy.
      intros n.
      exfalso. eapply lts_performs_spec1 in n as (q & tr).
      assert (q ∈ colts_extaction_set_from_pset p η) by (eapply Espec2; eauto).
      set_solver.
    + right. intro Hall.
      apply Hnemp. apply leibniz_equiv. intros q. split; [| set_solver].
      intros mem. eapply Espec1 in mem as (p' & memp & μ & hsy & tr).
      pose proof (Hall p' memp μ hsy) as memp'.
      exfalso. apply memp', (lts_performs_spec2 p' (ActExt μ) (exist _ q tr)).
  - destruct (colts_tau_set_from_pset_ispec p) as (Tspec1 & Tspec2).
    destruct (decide (colts_tau_set_from_pset p = ∅)) as [Hemp | Hnemp].
    + left. intros p' mem.
      intros n.
      exfalso. eapply lts_performs_spec1 in n as (q & tr).
      assert (q ∈ colts_tau_set_from_pset p) by (eapply Tspec2; eauto).
      set_solver.
    + right. intro Hall.
      apply Hnemp. apply leibniz_equiv. intros q. split; [| set_solver].
      intros mem. eapply Tspec1 in mem as (p' & memp & tr).
      eapply Hall in memp.
      exfalso. apply memp, (lts_performs_spec2 p' τ (exist _ q tr)).
Qed.
Next Obligation.
  intros. simpl in *. unfold coToSET_obligation_3 in H.
  unfold coToSET_obligation_1.
  destruct 𝜆 as [η |].
  - exists (colts_extaction_set_from_pset p η). split; eauto.
    intro Hemp.
    apply H. intros p' mem μ hsy.
    intros n.
    exfalso. eapply lts_performs_spec1 in n as (q & tr).
    assert (q ∈ colts_extaction_set_from_pset p η) as Hin.
    { destruct (colts_extaction_set_from_pset_ispec p η) as (_ & Hspec2).
      eapply Hspec2; eauto. }
    set_solver.
  - exists (colts_tau_set_from_pset p). split; eauto.
    intro Hemp.
    apply H. intros p' mem.
    intros n.
    exfalso. eapply lts_performs_spec1 in n as (q & tr).
    assert (q ∈ colts_tau_set_from_pset p) as Hin.
    { destruct (colts_tau_set_from_pset_ispec p) as (_ & Hspec2).
      eapply Hspec2; eauto. }
    set_solver.
Qed.
Next Obligation.
  unfold coToSET_obligation_3, coToSET_obligation_1.
  intros. destruct 𝜆 as [η |].
  - destruct H as (X' & Heq & Hne). subst.
    intro Hall.
    apply Hne. apply leibniz_equiv. intros q. split; [| set_solver].
    intros mem. eapply colts_extaction_set_from_pset_ispec in mem
      as (p' & memp & μ & hsy & tr).
    pose proof (Hall p' memp μ hsy) as memp'.
    exfalso. apply memp', (lts_performs_spec2 p' (ActExt μ) (exist _ q tr)).
  - destruct H as (X' & Heq & Hne). subst.
    intro Hall.
    apply Hne. apply leibniz_equiv. intros q. split; [| set_solver].
    intros mem. eapply colts_tau_set_from_pset_ispec in mem as (p' & memp & tr).
    eapply Hall in memp.
    exfalso. apply memp, (lts_performs_spec2 p' τ (exist _ q tr)).
Qed.

Set Typeclasses Depth 8.

Section coSetLTSFacts.

Context {P Aproc Atest : Type}.
Context `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest}.
Context `{gLtsP : !gLts P Hp}.
Context `{SA : !SyncAction Aproc Atest}.
Context `{CFI : !coFiniteImagegLts P Atest}.

(** ****** Co-termination of a set of states *)

Lemma co_empty_set_termination : (∅ : gset P) ⤓.
Proof.
  constructor. intros X tr.
  destruct tr as (eq & not_empty).
  subst. unfold colts_tau_set_from_pset in not_empty.
  rewrite elements_empty in not_empty. simpl in *.
  exfalso. set_solver.
Qed.

Lemma co_termination_sum (X : gset P) (Y : gset P) :
  X ⤓ → Y ⤓ → (X ∪ Y) ⤓.
Proof.
  intros conv1 conv2. revert Y conv2.
  induction conv1.
  intros ps2 hmx2.
  constructor. intros.
  rename H1 into hstep. rename H0 into IH. rename H into hter.
  assert (hsub1 : q ⊆ colts_tau_set_from_pset p ∪ colts_tau_set_from_pset ps2).
  { intros q' mem. destruct hstep as (eq1 & eq2). subst.
    destruct (colts_tau_set_from_pset_ispec (p ∪ ps2)) as (Hyp1 & Hyp2).
    eapply Hyp1 in mem as (q0 & mem & l).
    eapply elem_of_union in mem. destruct mem.
    eapply elem_of_union. left. eapply colts_tau_set_from_pset_ispec; eassumption.
    eapply elem_of_union. right. eapply colts_tau_set_from_pset_ispec; eassumption. }
  assert (hsub2 : colts_tau_set_from_pset p ∪ colts_tau_set_from_pset ps2 ⊆ q).
  { intros a ha. eapply elem_of_union in ha.
    destruct ha as [ha | ha].
    ++ destruct hstep as (eq & not_empty). subst.
       destruct (colts_tau_set_from_pset_ispec p) as (Hyp1 & Hyp2).
       eapply Hyp1 in ha as (p'' & mem & tr).
       assert (hm2 : p'' ∈ p ∪ ps2) by set_solver.
       eapply colts_tau_set_from_pset_ispec; [exact hm2 | exact tr].
    ++ destruct hstep as (eq & not_empty). subst.
       destruct (colts_tau_set_from_pset_ispec ps2) as (Hyp1 & Hyp2).
       eapply Hyp1 in ha as (p'' & mem & tr).
       assert (hm2 : p'' ∈ p ∪ ps2) by set_solver.
       eapply colts_tau_set_from_pset_ispec; [exact hm2 | exact tr]. }
  assert (eq : colts_tau_set_from_pset p ∪ colts_tau_set_from_pset ps2 ≡ q)
    by set_solver.
  remember (colts_tau_set_from_pset p) as Y_'.
  remember (colts_tau_set_from_pset ps2) as Z_'.
  destruct Y_' using set_ind_L.
  + destruct Z_' using set_ind_L.
    ++ exfalso. destruct hstep. set_solver.
    ++ assert (h2 : colts_tau_set_from_pset ps2 = q) by set_solver.
       inversion hmx2 as [hter2].
       eapply hter2. split; [by symmetry | destruct hstep as (_ & hne); exact hne].
  + destruct Z_' using set_ind_L.
    ++ assert (h2 : colts_tau_set_from_pset p = q) by set_solver.
       eapply hter. split; [by symmetry | destruct hstep as (_ & hne); exact hne].
    ++ subst.
       replace q with (({[x]} ∪ X) ∪ ({[x0]} ∪ X0)) by set_solver.
       eapply IH.
       +++ split; [eauto | set_solver].
       +++ inversion hmx2 as [hter2]. eapply hter2. split; [eauto | set_solver].
Qed.

Lemma co_termination_forall (ps : gset P) :
  (∀ (p : P), p ∈ ps → ({[p]} : gset P) ⤓) → ps ⤓.
Proof.
  intro hm.
  induction ps using set_ind_L.
  - intros. eapply co_empty_set_termination.
  - destruct (set_choose_or_empty X).
    + eapply co_termination_sum; set_solver.
    + assert (heq : X = ∅) by set_solver.
      rewrite heq, union_empty_r_L. set_solver.
Qed.

Lemma co_termination_set_if_termination (p : P) : p ⤓ → ({[ p ]} : gset P) ⤓.
Proof.
  intro hm. induction hm. rename H0 into IH.
  constructor. intros Y hstep.
  eapply co_termination_forall. intros p' mem.
  destruct hstep as (eq & eq'). subst. unfold colts_tau_set_from_pset in mem.
  rewrite elements_singleton in mem. simpl in *.
  eapply elem_of_union in mem as [mem | mem].
  - eapply elem_of_list_to_set in mem. eapply colts_tau_set_spec in mem.
    eapply IH. eauto.
  - set_solver.
Qed.

Lemma co_termination_if_termination_set_helper (ps : gset P) :
  ps ⤓ → ∀ p, p ∈ ps → p ⤓.
Proof.
  intro hm. induction hm. rename H0 into IH.
  intros p' mem. constructor.
  intros p'' tr.
  eapply IH.
  + split; [reflexivity | eapply colts_tau_set_from_pset_ispec in tr; set_solver].
  + eapply colts_tau_set_from_pset_ispec; set_solver.
Qed.

Lemma co_termination_if_termination_set (p : P) : ({[ p ]} : gset P) ⤓ → p ⤓.
Proof. intros. eapply co_termination_if_termination_set_helper; set_solver. Qed.

Lemma co_termination_set_iff_termination (p : P) : p ⤓ ↔ ({[ p ]} : gset P) ⤓.
Proof.
  split; [eapply co_termination_set_if_termination
         | eapply co_termination_if_termination_set].
Qed.

Lemma co_termination_set_for_all (X : gset P) : (∀ p, p ∈ X → p ⤓) → X ⤓.
Proof.
  intros hm. eapply co_termination_forall.
  intros p mem. eapply hm, co_termination_set_iff_termination in mem. eauto.
Qed.

Lemma co_termination_set_iff_termination_forall (X : gset P) :
  (∀ p, p ∈ X → p ⤓) ↔ X ⤓.
Proof.
  split; [now eapply co_termination_set_for_all
         | now eapply co_termination_if_termination_set_helper].
Qed.

(** ***** Co-convergence and co-traces on [coToSET] *)

Lemma co_empty_set_stable 𝜆 : (∅ : gset P) ↛{ 𝜆 }.
Proof. destruct 𝜆; intros Imp; apply Imp; intros p mem; exfalso; set_solver. Qed.

Lemma co_empty_set_stable_wk_not_emp_list
  (a : Atest) (s : trace Atest) (ps : gset P) :
  ¬ (∅ : gset P) ⟹[a :: s] ps.
Proof.
  intro imp.
  inversion imp; subst.
  + eapply co_empty_set_stable. eapply (@lts_performs_spec2 (gset P)); eauto.
  + eapply co_empty_set_stable. eapply (@lts_performs_spec2 (gset P)); eauto.
Qed.

Lemma co_empty_set_conv (s : trace Atest) : (∅ : gset P) ⇓ s.
Proof.
  induction s.
  + constructor. eapply co_empty_set_termination.
  + constructor.
    * eapply co_empty_set_termination.
    * intros. exfalso. eapply co_empty_set_stable_wk_not_emp_list; eauto.
Qed.

Lemma co_wk_tr_inv (ps : gset P) (s : trace Atest) (qs : gset P) :
  ps ⟹[s] qs → ∀ q, q ∈ qs → ∃ p, (p : P) ⟹ᶜᵒ[s] (q : P) ∧ p ∈ ps.
Proof.
  intro Hyp.
  induction Hyp.
  + intros. exists q. split; [constructor | assumption].
  + intros q0 mem0. eapply IHHyp in mem0 as (p' & wk_tr & mem).
    destruct l as (eq & non_empty).
    subst. eapply (colts_tau_set_from_pset_ispec p) in mem as (p'' & mem' & tr).
    exists p''. split; eauto. eapply cowt_tau; eauto.
  + intros q0 mem0. eapply IHHyp in mem0 as (p' & wk_tr & mem).
    destruct l as (eq & non_empty).
    subst. destruct (colts_extaction_set_from_pset_ispec p μ) as (Hspec1 & _).
    eapply Hspec1 in mem as (p'' & mem' & μ' & hsy & tr).
    exists p''. split; eauto. eapply cowt_act; eauto.
Qed.

Lemma co_convergence_set_if_convergence_forall (ps : gset P) (s : trace Atest) :
  (∀ (p : P), p ∈ ps → p ⇓ᶜᵒ s) → ps ⇓ s.
Proof.
  revert ps.
  induction s.
  + intros ps hall. constructor. eapply co_termination_set_for_all.
    intros p mem. assert (hc : p ⇓ᶜᵒ []) by (eapply hall; eauto).
    inversion hc; eauto.
  + intros ps hall. constructor.
    ++ eapply co_termination_set_for_all.
       intros p mem. assert (hc : p ⇓ᶜᵒ (a :: s)) by (eapply hall; eauto).
       inversion hc; subst; eauto.
    ++ intros qs w. eapply IHs.
       intros q mem. eapply co_wk_tr_inv in w as (p' & wk_tr & memp); [| exact mem].
       eapply hall in memp. inversion memp; subst. eapply H3; eauto.
Qed.

Lemma co_witness_wk_tr (ps : gset P) p0 (s0 : trace Atest) q0 :
  p0 ⟹ᶜᵒ[s0] q0 → p0 ∈ ps → (∃ qs, ps ⟹[s0] qs ∧ q0 ∈ qs).
Proof.
  intro wk_tr. revert ps.
  induction wk_tr.
  + intros. exists ps. split; [constructor | assumption].
  + intros ps mem. eapply (colts_tau_set_from_pset_ispec (SA := SA)) in l as eq; [| exact mem].
    eapply IHwk_tr in eq as (qs' & wk_tr' & mem').
    exists qs'. split; [| exact mem']. eapply wt_tau; [| exact wk_tr'].
    split; [reflexivity |].
    intro himp. eapply (colts_tau_set_from_pset_ispec (SA := SA)) in l as eq; [| exact mem].
    rewrite himp in eq. inversion eq.
  + intros ps mem.
    assert (hq : q ∈ (colts_extaction_set_from_pset ps μ)).
    { eapply colts_extaction_set_from_pset_ispec; eauto. }
    eapply IHwk_tr in hq as (qs' & wk_tr' & mem').
    exists qs'. split; [| exact mem']. eapply wt_act; [| exact wk_tr'].
    split; [reflexivity |].
    intro himp.
    assert (hq2 : q ∈ colts_extaction_set_from_pset ps μ)
      by (eapply colts_extaction_set_from_pset_ispec; eauto).
    rewrite himp in hq2. inversion hq2.
Qed.

Lemma co_convergence_forall_if_convergence_set (ps : gset P) (s : trace Atest) :
  ps ⇓ s → ∀ p, p ∈ ps → p ⇓ᶜᵒ s.
Proof.
  revert ps.
  induction s.
  + intros ps hm p mem. inversion hm; subst. constructor.
    eapply co_termination_set_iff_termination_forall; eauto.
  + intros ps hm p mem. inversion hm; subst.
    constructor.
    eapply co_termination_set_iff_termination_forall; eauto.
    intros q w. assert (∃ qs, ps ⟹{a} qs ∧ q ∈ qs) as (qs & wk_tr & memq).
    { eapply co_witness_wk_tr; eauto. }
    eapply H3 in wk_tr.
    eapply IHs; eauto.
Qed.

Lemma co_convergence_set_iff_convergence_forall (ps : gset P) (s : trace Atest) :
  (∀ (p : P), p ∈ ps → p ⇓ᶜᵒ s) ↔ ps ⇓ s.
Proof.
  split; [eapply co_convergence_set_if_convergence_forall
         | eapply co_convergence_forall_if_convergence_set].
Qed.

End coSetLTSFacts.