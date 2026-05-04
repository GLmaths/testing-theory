(*
   Copyright (c) 2024 Nomadic Labs
   Copyright (c) 2024 Paul Laforgue <paul.laforgue@nomadic-labs.com>
   Copyright (c) 2024 Léo Stefanesco <leo.stefanesco@mpi-sws.org>

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

From Stdlib Require ssreflect.
From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From Stdlib.Program Require Import Equality Wf.
From Stdlib.Wellfounded Require Import Inverse_Image.
From Stdlib Require Import Setoid.
From Stdlib .Logic Require Import ProofIrrelevance.

From stdpp Require Import base countable finite gmap list finite base decidable finite gmap.

From TestingTheory Require Import ActTau InputOutputActions gLts Bisimulation Lts_OBA Lts_OBA_FB Lts_FW FiniteImageLTS
            Subset_Act Must Soundness Completeness Equivalence StateTransitionSystems
              Termination WeakTransitions Convergence  
               InteractionBetweenLts MultisetLTSConstruction ForwarderConstruction ParallelLTSConstruction
               Testing_Predicate DefinitionAS DefinitionCI SetLTSConstruction.

Lemma equiv_termination `{gLtsP : @gLts P A H} p : p ⇓ [] <-> p ⤓.
Proof.
  split.
  + intros. dependent induction H0; eauto.
  + intros. constructor. eauto.
Qed.

Lemma prex1_if_copre `{
  gLtsP : @gLts P A H, !FiniteImagegLts P A, AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳P  gLtsP gLtsT,
  gLtsQ : @gLts Q A H, !FiniteImagegLts Q A, AbsQT : @AbsAction Q T FinA PreAct A H Φ 𝝳Q  gLtsQ gLtsT}
  (ps : gset P) (qs : gset Q) : ps ⩽ qs -> ps ₁≼ₛₑₜ_ₐₛ qs.
Proof.
  intros Hyp_PreO s hcnv.
  revert ps qs Hyp_PreO hcnv.
  dependent induction s; intros ps qs Hyp_PreO hcnv; destruct Hyp_PreO.
  + eapply convergence_forall_if_convergence_set.
    eapply convergence_set_if_convergence_forall in hcnv.
    constructor. eapply c_cnv. eapply equiv_termination. exact hcnv.
  + eapply convergence_forall_if_convergence_set. constructor.
    - eapply c_cnv. eapply convergence_set_iff_convergence_forall in hcnv.
      inversion hcnv; eauto.
    - intros. assert (∀ p : P, p ∈ ps → p ⇓ [a]) as hcnv_a.
      { eapply convergence_forall_if_convergence_set.
        eapply convergence_set_if_convergence_forall in hcnv. eapply cnv_wk;eauto. }
      eapply convergence_set_if_convergence_forall.
      eapply (IHs (wt_s_set_from_pset ps [a] hcnv_a));eauto.
      * eapply c_step.
        ++ eapply convergence_set_if_convergence_forall in hcnv_a. exact hcnv_a.
        ++ intros q' mem'. eapply wk_tr_inv in H0 as (q'' & wk_tr'' & mem'');eauto.
        ++ exact (wt_s_set_from_pset_ispec ps [a] hcnv_a).
      * intros. edestruct (wt_s_set_from_pset_ispec ps [a] hcnv_a) as (Hyp1 & Hyp2).
        eapply Hyp1 in H1 as (p' & mem & wk_tr). eapply hcnv in mem.
        eapply cnv_preserved_by_wt_act;eauto.
Qed.

Lemma prex2_if_copre `{
  gLtsP : @gLts P A H, !FiniteImagegLts P A, AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳P  gLtsP gLtsT,
  gLtsQ : @gLts Q A H, !FiniteImagegLts Q A, AbsQT : @AbsAction Q T FinA PreAct A H Φ 𝝳Q  gLtsQ gLtsT}
  (ps : gset P) (qs : gset Q) : ps ⩽ qs -> ps ₂≼ₛₑₜ_ₐₛ qs.
Proof.
  revert ps qs.
  intros ps qs hsub q s.
  revert ps qs q hsub.
  dependent induction s; intros ps qs q hsub.
  + intros q' mem hw hstq' hcnv. revert ps qs hstq' hcnv mem hsub.
    dependent induction hw; try rename p into q; intros.
    ++ destruct hsub. edestruct c_now;eauto.
       - eapply equiv_termination. eapply convergence_set_if_convergence_forall; eauto.
    ++ eapply IHhw.
       - eauto.
       - eauto.
       - eauto.
       - eapply elem_of_singleton. reflexivity.
       - eapply c_tau. eassumption.
         intros q' mem'. assert (q' = q) by set_solver. subst.
         exists p. split; eauto. eapply lts_to_wt_tau;eauto.
  + intros. rename a into μ.
    replace (μ :: s) with ([μ] ++ s) in H1 by eauto.
    eapply wt_split in H1 as (q0 & hw0 & hw1).
    eapply wt_decomp_one in hw0 as (q0' & q1' & q1 & hlt & hw0').
    assert (ps ⩽ {[q0']}).
    { eapply co_preserved_by_wt_nil; eauto. intros q'' mem''.
      assert (q0' = q'') by set_solver. subst. exists q. split;eauto. }
    assert (hcnv' : ∀ p : P, p ∈ ps → p ⇓ [μ]).
    { intros. constructor. edestruct (H3 p H4); eauto.
      intros. constructor. eapply cnv_terminate.
      eapply cnv_preserved_by_wt_act; eauto. }
    set (ps' := wt_s_set_from_pset ps [μ] hcnv').
    assert (ps ⩽ {[ q0' ]}).
    { eapply co_preserved_by_wt_nil; eauto. intros q'' mem''.
      assert (q0' = q'') by set_solver. subst. exists q''. split;eauto. eapply wt_nil. }
    assert (ps' ⩽ {[ q1' ]}). 
    { destruct H4. eapply c_step.
      + eapply convergence_set_if_convergence_forall. exact hcnv'.
      + intros q''' mem'''.
        assert(q''' = q1') by set_solver. subst.
        exists q0'. split. set_solver. eapply lts_to_wt. exact hlt.
      + eapply wt_s_set_from_pset_ispec. }
    assert (ps' ⩽ {[ q0 ]}).
    { eapply co_preserved_by_wt_nil; eauto.
      intros q'' mem''. exists q1'. split. set_solver.
      assert (q'' = q0) by set_solver. subst. eauto. }
    assert (q0 ∈ ({[q0]}: gset Q)) as mem_sing by set_solver.
    edestruct (IHs ps' ({[ q0 ]}) q0 H6 _ mem_sing hw1 H2) 
    as (r & memr & p' & hwr & hst & hsub').
    * intros. edestruct (wt_s_set_from_pset_ispec ps [μ] hcnv') as (Hyp1 & Hyp2). 
      eapply Hyp1 in H7 as (p0  & hmem0 & hw0).
      eapply cnv_preserved_by_wt_act; eauto.
    * edestruct (wt_s_set_from_pset_ispec ps [μ] hcnv') as (Hyp1 & Hyp2).
      eapply Hyp1 in memr as (p0  & hmem0 & hw0).
      exists p0. split ;eauto. exists p'.
      split.
      ++ eapply wt_push_left; eassumption.
      ++ split;eauto.
Qed.
