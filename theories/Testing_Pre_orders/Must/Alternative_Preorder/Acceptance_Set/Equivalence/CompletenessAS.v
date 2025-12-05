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

From Coq Require ssreflect Setoid.
From Coq.Unicode Require Import Utf8.
From Coq.Lists Require Import List.
Import ListNotations.
From Coq.Program Require Import Wf Equality.
From Coq.Wellfounded Require Import Inverse_Image.
From Coq.Logic Require Import JMeq ProofIrrelevance.
From stdpp Require Import sets base countable finite gmap list finite decidable finite gmap.
From Must Require Import gLts Bisimulation Lts_OBA WeakTransitions Lts_OBA_FB Lts_FW FiniteImageLTS
      InteractionBetweenLts MultisetLTSConstruction ParallelLTSConstruction ForwarderConstruction
       Must Lift Subset_Act Convergence Termination Testing_Predicate DefinitionAS.
From Must Require Import ActTau.

(* TODO : MOVE *)
Lemma co_cnv_annhil
  `{@gLtsObaFW P A H gLtsP gLtsEqP gLtsObaP}
  `{@Prop_of_Inter P T A parallel_inter H gLtsP gLtsT} :
     ∀ (p : P) (μ η : A) (s1 s2 s3 : list A),
         Forall non_blocking s1
         → Forall non_blocking s2
           → non_blocking η
             → dual μ η
               → p ⇓ᶜᵒ (s1 ++ [η] ++ s2 ++ [μ] ++ s3)
                 → p ⇓ᶜᵒ (s1 ++ s2 ++ s3).
Proof.
  intros p μ η s1 s2 s3 his1 his2 nb inter co_cnv. intros s0 inter_trace.
  eapply Forall2_app_inv_r in inter_trace as (s'1 & s'2 & his'1 & his'2 & eq); subst.
  eapply Forall2_app_inv_r in his'2 as (s''2 & s'3 & his'2 & his'3 & eq); subst.
  eapply cnv_annhil; eauto.
  + eapply EquivDef. exists s1. split; eauto.
  + eapply EquivDef. exists s2. split; eauto.
  + eapply co_cnv; eauto.
    eapply Forall2_app_inv_r. exists s'1. exists ([μ] ++ s''2 ++ [η] ++ s'3).
    split; eauto. split; eauto. constructor; eauto.
    eapply Forall2_app_inv_r. exists s''2. exists ([η] ++ s'3). split; eauto.
    split; eauto. constructor; eauto. symmetry ;eauto.
Qed.

(* TODO : MOVE *)
Lemma co_cnv_preserved_by_wt_act 
  `{@Prop_of_Inter P T A parallel_inter H gLtsP gLtsT}
  s (p : P) μ :
  p ⇓ᶜᵒ (μ :: s) -> forall q μ', parallel_inter μ' μ -> p ⟹{μ'} q -> q ⇓ᶜᵒ s.
Proof.
  intros hcnv q μ' inter wt. intros s0 inter_trace.
  eapply cnv_preserved_by_wt_act ; eauto. eapply hcnv.
  constructor; eauto.
Qed.

(* TODO : MOVE *)
Lemma co_cnv_drop_action_in_the_middle
  `{@Prop_of_Inter P T A parallel_inter H gLtsP gLtsT}
     : ∀ (p : P) (s1 s2 : list A) (μ : A),
         Forall non_blocking s1
         → p ⇓ᶜᵒ (s1 ++ [μ] ++ s2) → ∀ (r : P) (μ' : A), 
         parallel_inter μ' μ -> p ⟶[μ'] r → r ⇓ᶜᵒ (s1 ++ s2).
Proof.
  intros p s1 s2 μ his1 co_conv r μ' inter Tr. intros s0 inter_trace.
  eapply Forall2_app_inv_r in inter_trace as (l1 & l2 & his2 & his3 & eq2).
  subst. eapply cnv_drop_action_in_the_middle; eauto. eapply EquivDef.
  exists s1. split; eauto. eapply co_conv. 
  admit.
Admitted.

(** Test generators specification. **)

Class test_spec
  `{gLts T A, !gLtsEq T A, !Testing_Predicate T A outcome}
  (gen : list A -> T) := {
    (* 1 *) test_ungood : 
              forall s, ¬ outcome (gen s) ;
    (* 2 *) test_next_step μ1 s :
              gen (μ1 :: s) ⟶⋍[μ1] gen s;
    (* 3 *) test_tau_transition β s : 
              blocking β ->
              ∃ t', gen (β :: s) ⟶ t';
    (* 4 *) test_reset_tau_path β s t : 
              blocking β ->
              gen (β :: s) ⟶ t -> outcome t;
    (* 5 *) test_follows_trace_determinacy {β s t}:
              blocking β ->
              gen (β :: s) ⟶[β] t -> t ⋍ gen s;
    (* 6 *) test_side_effect_by_construction {t β μ' s} :
              blocking β ->
              gen (β :: s) ⟶[μ'] t -> μ' ≠ β -> outcome t ;
  }.

Lemma test_spec_determinacy `{
  @gLtsOba T A H gLtsT gLtsEqT, !Testing_Predicate T A outcome, !test_spec f} 
  μ1 s t:
  f (μ1 :: s) ⟶[μ1] t -> t ⋍ f s.
Proof.
  intro HypTr.
  destruct (decide (non_blocking μ1)) as [nb | not_nb].
  + assert (f (μ1 :: s) ⟶⋍[μ1] f s) as (t' & Tr & Eq).
    { eapply test_next_step. }
    assert (t' ⋍ t) as equiv.
    { eapply lts_oba_non_blocking_action_deter; eauto. }
    etransitivity; eauto. symmetry; eauto.
  + eapply test_follows_trace_determinacy in not_nb as equiv; eauto.
Qed.

Class test_convergence_spec
  `{gLts T A, ! gLtsEq T A, !Testing_Predicate T A outcome}
  (tconv : list A -> T) := {
    tconv_test_spec : test_spec tconv ;
    (* c1 *) tconv_does_no_external_action μ : tconv ε ↛[μ] ;
    (* c2 *) tconv_can_compute : ∃ e', tconv ε ⟶ e';
    (* c2 *) tconv_computes_to_good e : tconv ε ⟶ e -> outcome e;
  }.

#[global] Existing Instance tconv_test_spec.

Class test_co_acceptance_set_spec (PreAct : Type) `{CC : Countable PreAct}
  `{gLtsT : @gLts T A H, ! gLtsEq T A, !Testing_Predicate T A outcome}
  (ta : gset PreAct -> list A -> T) (Γ : A -> PreAct)
    := {
    ta_test_spec (E : gset PreAct) : test_spec (ta E) ;
    (* t1 *) ta_does_no_tau (E : gset PreAct) : 
                ta E ε ↛ ; 
    (* t2 *) ta_does_no_non_blocking_actions (E : gset PreAct) η : 
                non_blocking η -> ta E ε ↛[η] ;
  (* t4-> *) ta_actions_are_in_its_gamma_set (E : gset PreAct) β e : 
                blocking β -> ta E ε ⟶[β] e
                    -> (Γ β) ∈ E ;
  (* t4<- *) ta_has_a_representative_transition_for_its_gamma_set (E : gset PreAct) pβ : 
                pβ ∈ E -> 
                ∃ r β, ta E ε ⟶[β] r /\ (Γ β = pβ);
    (* t3 *) ta_transition_to_good β t' (E : gset PreAct) : 
                blocking β -> ta E ε ⟶[β] t' -> outcome t' ;
  }.

#[global] Existing Instance ta_test_spec.

(* Definition union_of_co_actions_without `{gLts P A} `{gLts Q A}
  (p_L : list P * Q) := (⋃ map co_actions_of p_L.1) ∖ (co_actions_of p_L.2).

Definition union_of_pre_co_actions_without 
  `{gLtsP : @gLts P A H, PreActP : @PreExtAction A H P FinA PreAct PreAct_eq PreAct_countable 𝝳 Φ gLtsP}
  `{gLtsQ : @gLts Q A H, PreActQ : @PreExtAction A H Q FinA PreAct PreAct_eq PreAct_countable 𝝳 Φ gLtsQ}
  (p_L : list P * Q) := ⋃ map pre_co_actions_of p_L.1 ∖ (pre_co_actions_of p_L.2). *)


(* Facts about test generators. *)

Lemma tconv_always_reduces `{
  @gLtsOba T A H gLtsT gLtsEqT, !Testing_Predicate T A outcome, !test_convergence_spec tconv} s :
  ∃ e, tconv s ⟶ e.
Proof.
  induction s as [|μ s'].
  - eapply tconv_can_compute.
  - destruct (decide (non_blocking μ)) as [nb | not_nb]. 
    + destruct IHs' as (e & l).
      destruct (test_next_step μ s') as (e' & hl' & heq).
      destruct (eq_spec e' e τ) as (e0 & hl0 & heqe0). eauto with mdb.
      destruct (lts_oba_non_blocking_action_delay nb hl' hl0)
        as (r & l1 & l2); eauto.
    + eapply test_tau_transition. exact not_nb.
Qed.

Lemma terminate_must_test_conv_nil `{
  gLtsP : gLts P A, 
  gLtsT : !gLts T A, !gLtsEq T A,
  !Testing_Predicate T A outcome, !test_convergence_spec tconv}

  `{@Prop_of_Inter P T A parallel_inter H gLtsP gLtsT}

  (p : P) : 
  p ⤓ -> must p (tconv ε).
Proof.
  intros ht.
  induction ht.
  eapply m_step; eauto with mdb.
  - eapply test_ungood.
  - destruct tconv_can_compute as (e' & l); eauto with mdb.
    exists (p ▷ e'). eapply ParRight; eauto.
  - intros e' l. eapply tconv_computes_to_good in l. eauto with mdb.
  - intros p0 e0 μ μ' inter l1 l2.
    exfalso. eapply lts_refuses_spec2.
    exists e0. eassumption. eapply tconv_does_no_external_action.
Qed.

Lemma must_tconv_wt_mu `{
  gLtsP : gLts P A, 
  gLtsT : ! gLts T A, ! gLtsEq T A,
  !Testing_Predicate T A outcome, ! test_convergence_spec tconv}

  `{@Prop_of_Inter P T A parallel_inter H gLtsP gLtsT}

  μ μ' s' (p q : P): 
  must p (tconv (μ' :: s')) -> parallel_inter μ μ' ->
    p ⟹{μ} q -> must q (tconv s').
Proof.
  intros hm inter w.
  dependent induction w.
  + eapply IHw; eauto with mdb.
    eapply must_preserved_by_lts_tau_srv; eauto.
  + edestruct test_next_step as (t' & hlt' & heqt').
    eapply (must_eq_client _ _ _ heqt').
    eapply (must_preserved_by_weak_nil_srv q t); eauto.
    eapply must_preserved_by_synch_if_notoutcome; eauto with mdb.
    eapply test_ungood.
Qed.

(** First implication of the first requirement. *)
Lemma co_cnv_if_must `{
  gLtsP : gLts P A, 
  gLtsT : !gLts T A, !gLtsEq T A, !Testing_Predicate T A outcome, !test_convergence_spec tconv}

  `{@Prop_of_Inter P T A parallel_inter H gLtsP gLtsT}

  s (p : P) : 
  must p (tconv s) -> p ⇓ᶜᵒ s.
Proof.
  revert p.
  induction s as [|μ s']; intros p hm.
  - eapply co_cnv_nil.
    eapply (must_terminate_unoutcome _ _ hm), test_ungood.
  - eapply co_cnv_act.
    + eapply (must_terminate_unoutcome _ _ hm), test_ungood.
    + intros q μ' w inter. eapply IHs', must_tconv_wt_mu; eauto.
Qed.

Lemma f_gen_lts_mu_in_the_middle `{
  @gLtsOba T A H gLtsT gLtsEqT, !Testing_Predicate T A outcome, !test_spec f} 
  s1 s2 μ:
  Forall non_blocking s1
    -> f (s1 ++ μ :: s2) ⟶⋍[μ] f (s1 ++ s2).
Proof.
  revert s2 μ.
  induction s1 as [|ν s']; intros s2 μ his ; simpl in *.
  - eapply (test_next_step μ).
  - inversion his as [| ? ? nb his']; subst.
    destruct (IHs' s2 μ his') as (r & hlr & heqr).
    edestruct (test_next_step ν (s' ++ μ :: s2))
      as (t & hlt & heqt).
    edestruct (eq_spec t r) as (u & hlu & hequ).
    { eauto with mdb. }
    destruct (lts_oba_non_blocking_action_delay nb hlt hlu)
      as (v & l1 & (t' & l2 & heq')).
    exists v. split. eassumption.
    destruct (test_next_step ν (s' ++ s2)) as (w & hlw & heqw).
    eapply lts_oba_non_blocking_action_deter_inv; try eassumption.
    etrans. eauto. etrans. eauto. etrans. eauto. now symmetry.
Qed.

Lemma f_gen_lts_mu_in_the_middle' `{
  @gLtsOba T A H gLtsT gLtsEqT, !Testing_Predicate T A outcome, !test_spec f} 
  s1 s2 μ t:
  Forall non_blocking s1
    -> f (s1 ++ μ :: s2) ⟶⋍[μ] t -> t ⋍ f (s1 ++ s2).
Proof.
  revert s2 μ t.
  induction s1 as [|ν s']; intros s2 μ t his HypTr; simpl in *.
  - destruct (decide (non_blocking μ)) as [nb | not_nb].
    + assert (f (ε ++ μ :: s2) ⟶⋍[μ] f (ε ++ s2)) as HypTr'.
      { eapply f_gen_lts_mu_in_the_middle. eauto. }
      destruct HypTr as (e & HypTr & equiv).
      destruct HypTr' as (e' & HypTr' & equiv'); simpl in *.
      assert (e ⋍ e').
      { eapply lts_oba_non_blocking_action_deter; eauto. } 
      etransitivity. symmetry. exact equiv. etransitivity; eauto.
    + destruct HypTr as (e & HypTr & equiv).
      assert (e ⋍ f s2) as equiv'. 
      { eapply test_follows_trace_determinacy; eauto. }
      etransitivity. symmetry. exact equiv. eauto.
  - inversion his; subst.
    destruct (decide (non_blocking μ)) as [nb | not_nb].
    + assert (f ((ν :: s') ++ μ :: s2) ⟶⋍[μ] f ((ν :: s') ++ s2)) as HypTr'.
      { eapply f_gen_lts_mu_in_the_middle. eauto. }
      destruct HypTr as (e & HypTr & equiv).
      destruct HypTr' as (e' & HypTr' & equiv').
      assert (e ⋍ e').
      { eapply lts_oba_non_blocking_action_deter; eauto. }
      etransitivity. symmetry. exact equiv. etransitivity; eauto.
    + destruct HypTr as (e & HypTr & equiv).
      destruct (decide (non_blocking ν)) as [nb' | not_nb'].
      ++ assert (f (ν :: s' ++ μ :: s2) ⟶⋍[ν] f (s' ++ μ :: s2)) as HypTr'.
         { eapply test_next_step. }
         destruct HypTr' as (e' & HypTr' & equiv').
         assert (μ <> ν) as not_eq.
         { intro imp. rewrite imp in not_nb. contradiction. }
         destruct (lts_oba_non_blocking_action_confluence nb' not_eq HypTr' HypTr )
           as (t' & l2 & (t'' & l1 & heq)).
         assert (f (s' ++ μ :: s2) ⟶⋍[μ] f (s' ++ s2)) as HypTr''.
         { eapply f_gen_lts_mu_in_the_middle; eauto. }
         edestruct (eq_spec (f (s' ++ μ :: s2)) t' (ActExt μ))
          as (v & hlv & heqv).
         exists e'. split; eauto. symmetry; eauto.
         assert (t' ⋍ (f (s' ++ s2))) as heq'.
         { eapply IHs'; eauto. exists v. split; eauto. }
         assert (f (ν :: s' ++ s2) ⟶⋍[ν] f (s' ++ s2)) as (v' & hlv' & heqv').
         { eapply test_next_step. }
         assert (e ⋍ f (ν :: s' ++ s2)) as final. 
         { eapply lts_oba_non_blocking_action_deter_inv; eauto.
         etransitivity. exact heq. etransitivity. exact heq'. symmetry; eauto. }
         etransitivity. symmetry. exact equiv. eauto.
      ++ inversion his; subst. 
         contradiction.
Qed.


Lemma side_effect_by_blocking_action `{
  @gLtsOba T A H gLtsT gLtsEqT, !Testing_Predicate T A outcome, !test_spec f} 
  s β β' t:
  blocking β -> f (β :: s) ⟶[β'] t -> blocking β'.
Proof.
  intros not_nb HypTr.
  intro nb. destruct (decide (β' = β)) as [eq | neq].
  + subst ;eauto.
  + assert (outcome t).
    { eapply test_side_effect_by_construction; eauto. }
    assert (outcome (f (β :: s))).
    { eapply outcome_preserved_by_lts_non_blocking_action_converse; eauto. }
    assert (¬ outcome (f (β :: s))).
    { eapply test_ungood; eauto. }
    contradiction.
Qed.

Lemma f_gen_lts_mu_in_the_middle_b_or_neq `{
  @gLtsOba T A H gLtsT gLtsEqT, !Testing_Predicate T A outcome, !test_spec f} 
  s1 s2 β β' t:
  Forall non_blocking s1 -> blocking β -> β' ≠ β -> blocking β'
    -> f (s1 ++ β :: s2) ⟶[β'] t -> outcome t.
Proof.
  revert s2 β β' t.
  induction s1 as [|ν s']; intros s2 β β' t his b neq b' HypTr; simpl in *.
  - eapply test_side_effect_by_construction in neq; eauto.
  - inversion his as [| ? ? nb his'];subst.
    assert (f (ν :: (s' ++ β :: s2)) ⟶⋍[ν] f (s' ++ β :: s2)) as (e'' & hl & equiv).
    { eapply test_next_step; eauto. }
    destruct (decide (β' = ν)) as [eq' | neq'].
    + subst. contradiction. 
    + edestruct (lts_oba_non_blocking_action_confluence nb neq' hl HypTr) 
      as (p' & HypTr''' & p'' & HypTr'' & equiv''').
      edestruct (eq_spec (f (s' ++ β :: s2)) p') as (t' & HypTr' & equiv'').
      { symmetry in equiv. eauto. }
      assert (outcome t') as happy.
      { eapply IHs' in neq; eauto. }
      eapply outcome_preserved_by_lts_non_blocking_action_converse; eauto.
      eapply outcome_preserved_by_eq; eauto. etransitivity ;eauto. now symmetry.
Qed.

Lemma inversion_test_b_external_action `{
  @gLtsOba T A H gLtsT gLtsEqT, !Testing_Predicate T A outcome, !test_spec f} 
  s β' t :
  (forall μ, f ε ↛[μ] \/ (forall t, f ε ⟶[μ] t -> outcome t)) ->
  f s ⟶[β'] t ->
  blocking β' ->
  outcome t \/
  ∃  s1 s2 β, s = s1 ++ β :: s2 
  /\ t ⋍ f (s1 ++ s2)
  /\ β' = β
  /\ Forall non_blocking s1.
Proof.
  revert β' t.
  induction s
    as (s & Hlength) using
         (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
  destruct s as [|ν s']; intros μ t h l not_nb.
  - edestruct (h μ) as [refuses_f | f_to_outcome].
    + now eapply lts_refuses_spec2 in refuses_f; eauto.
    + left. eapply f_to_outcome. eauto.
  - destruct (decide (non_blocking ν)) as [nb | b].
    + assert (f (ν :: s') ⟶⋍[ν] f s') as (v & hlv & eqv).
      { eapply test_next_step. }
      assert (μ <> ν) as not_eq.
      { intro. subst. contradiction. }
      destruct (lts_oba_non_blocking_action_confluence nb not_eq hlv l)
           as (t' & l2 & (t'' & l1 & heq)).
      destruct (eq_spec (f s') t' (ActExt μ)) as (v' & hlv' & heqv').
      { exists v. split. symmetry; eauto. exact l2. }
      destruct (decide (outcome v')) as [happy' | not_happy'].
      ++ left. eapply outcome_preserved_by_lts_non_blocking_action_converse; eauto.
         eapply outcome_preserved_by_eq; eauto. etransitivity; eauto. symmetry. eauto.
      ++ edestruct (Hlength s') as [happy | (s1 & s2 & μ' & eq & equiv & eq_action & his)]; eauto.
         +++ contradiction.
         +++ right. subst.
             assert (t ⋍ f ((ν :: s1) ++ s2)).
             { eapply f_gen_lts_mu_in_the_middle'. constructor; eauto.
               exists t. split; eauto. reflexivity. } 
             exists (ν :: s1). exists s2. exists μ'.
             split. eauto. repeat split; eauto.
    + destruct (decide (μ = ν)) as [eq | neq].
      ++ right. subst.
         exists ε, s', ν. simpl. repeat split; simpl; eauto with mdb.
         repeat split;eauto. intros. eapply test_follows_trace_determinacy; eauto.
      ++ left. eapply test_side_effect_by_construction; eauto.
Qed.

Lemma inversion_test_nb_external_action `{
  @gLtsOba T A H gLtsT gLtsEqT, !Testing_Predicate T A outcome, !test_spec f} 
  s η' t :
  (forall μ, f ε ↛[μ] \/ (forall t, f ε ⟶[μ] t -> outcome t)) ->
  f s ⟶[η'] t ->
  non_blocking η' -> 
  outcome t \/
  ∃ s1 s2 η, s = s1 ++ η :: s2
  /\ t ⋍ f (s1 ++ s2) 
  /\ η' = η
  /\ Forall non_blocking s1.
Proof.
  revert η' t.
  induction s
    as (s & Hlength) using
         (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
  destruct s as [|ν s']; intros η t h l nb.
  - edestruct (h η) as [Tr|]; eauto. now eapply lts_refuses_spec2 in Tr; eauto.
  - edestruct (test_next_step ν s') as (r & hlr & heqr).
    destruct (decide (ν = η)) as [eq | not_eq].
    + right. subst. exists ε, s', η. repeat split; simpl; eauto with mdb.
      transitivity r; eauto. eapply (lts_oba_non_blocking_action_deter nb l hlr); eauto.
    + destruct (lts_oba_non_blocking_action_confluence nb not_eq l hlr )
        as (t' & l2 & (t'' & l1 & heq)).
      destruct (eq_spec (f s') t'' (ActExt $ η)) as (v & hlv & heqv).
      { exists r. split; eauto with mdb. now symmetry. }
      destruct (decide (outcome v)) as [happy' | not_happy'].
      * exfalso. assert (outcome (f s')). 
        { eapply outcome_preserved_by_lts_non_blocking_action_converse; eauto. }
        assert (¬ outcome (f s')).
        { eapply test_ungood. }
        contradiction.
      * edestruct (Hlength s' ltac:(eauto) η v h hlv nb)
             as [happy' | (s1' & s2' & μ' & eq0 & eq1 & eq2 & eq3)]; try contradiction.
        destruct (decide (non_blocking ν)) as [nb' | not_nb'].
        -- right. subst.
           assert (Forall non_blocking (ν :: s1')) as Hyp.
           { constructor; eauto. }
           exists (ν :: s1'), s2', μ'. repeat split; eauto.
           edestruct (f_gen_lts_mu_in_the_middle (ν :: s1') s2' ν)
            as (r' & hlr' & heqr'); eauto.
           edestruct (test_next_step ν (s1' ++ s2'))
            as (w & hlw & heqw).
           eapply lts_oba_non_blocking_action_deter_inv; try eassumption.
           transitivity t''. symmetry. eassumption.
           transitivity v. now symmetry.
           transitivity (f (s1' ++ s2')). eassumption. now symmetry.
        -- subst. assert (outcome t).
           { eapply test_side_effect_by_construction; eauto. } eauto. 
Qed.

Lemma inversion_test_external_action `{
  @gLtsOba T A H gLtsT gLtsEqT, !Testing_Predicate T A outcome, !test_spec f} 
  s η' t :
  (forall μ, f ε ↛[μ] \/ (forall t, f ε ⟶[μ] t -> outcome t)) ->
  f s ⟶[η'] t ->
  outcome t \/
  ∃ s1 s2 η, s = s1 ++ η :: s2 
  /\ t ⋍ f (s1 ++ s2)
  /\ η' = η
  /\ Forall non_blocking s1.
Proof.
  intros. destruct (decide (non_blocking η')) as [nb | not_nb].
  + eapply inversion_test_nb_external_action; eauto.
  + eapply inversion_test_b_external_action; eauto.
Qed.

Lemma inversion_tconv_external_action `{
  @gLtsOba T A H gLtsT gLtsEqT, !Testing_Predicate T A outcome, !test_convergence_spec f} 
  s μ' t :
  f s ⟶[μ'] t ->
  outcome t \/ 
  ∃ s1 s2 μ, s = s1 ++ μ :: s2 
  /\ t ⋍ f (s1 ++ s2)
  /\ μ' = μ
  /\ Forall non_blocking s1.
Proof.
  intros. eapply inversion_test_external_action; eauto.
  left. eapply tconv_does_no_external_action; eauto.
Qed.

Lemma inversion_ta_external_action `{CC: Countable PreAct} `{
  @gLtsOba T A H gLtsT gLtsEqT,
  !Testing_Predicate T A outcome, !test_co_acceptance_set_spec PreAct f Γ} 
  s μ' (t : T) (O : gset PreAct) :
  f O s ⟶[μ'] t ->
  outcome t \/ 
  ∃ s1 s2 μ, s = s1 ++ μ :: s2 
  /\ t ⋍ f O (s1 ++ s2)
  /\ μ' = μ
  /\ Forall non_blocking s1.
Proof.
  eapply inversion_test_external_action; eauto. intros μ.
  destruct (decide (non_blocking μ)) as [nb' | not_nb'].
       +++ left. eapply ta_does_no_non_blocking_actions; eauto.
       +++ right. intro e. eapply ta_transition_to_good; eauto.
Qed.

Lemma inversion_test_tau_action `{
  @gLtsOba T A H gLtsT gLtsEqT, !Testing_Predicate T A outcome, !test_spec f}
  s t :
  (f ε ↛ \/ (forall t, f ε ⟶ t -> outcome t)) ->
  (forall μ, f ε ↛[μ] \/ (forall t, f ε ⟶[μ] t -> outcome t)) ->
  f s ⟶ t ->
  outcome t \/
  ∃ η μ s1 s2 s3, 
  s = s1 ++ [η] ++ s2 ++ [μ] ++ s3
  /\ t ⋍ f (s1 ++ s2 ++ s3)
  /\ non_blocking η
  /\ Forall non_blocking s1 
  /\ Forall non_blocking s2
  /\ dual μ η.
Proof.
  revert t. induction s as [|μ' s']; intros t h1 h2 HypTr.
  - destruct h1 as [refuses_f | f_to_outcome].
    + eauto. now eapply lts_refuses_spec2 in refuses_f ; eauto.
    + eauto. 
  - destruct (decide (non_blocking μ')) as [nb | not_nb].
    + destruct (decide (outcome t)) as [happy | not_happy].
      ++ left. exact happy.
      ++ edestruct (test_next_step μ' s') as (r & hlr & heqr).
         destruct (lts_oba_non_blocking_action_tau nb hlr HypTr)
         as [(r1 & l1 & (r2 & l2 & heq))| HypTr''].
         +++ destruct (eq_spec (f s') r1 τ) as (v & hlv & heqv).
             exists r. split; eauto with mdb. now symmetry.
             destruct (IHs' _ h1 h2 hlv) as [happy' | Hyp].
             ++++ exfalso. 
                  assert (¬ outcome r2) as not_happy''.
                  { eapply unoutcome_preserved_by_lts_non_blocking_action; eauto. }
                  assert (¬ outcome v) as not_happy'.
                  { eapply unoutcome_preserved_by_eq; eauto.
                    etrans. eapply heqv. now symmetry. }
                  contradiction.
             ++++ right. destruct Hyp 
                  as (η & μ & s1 & s2 & s3 & eq_trace & equiv & hi & his1 & his2 & duo). subst.
                  exists η, μ, (μ' :: s1), s2, s3. repeat split; eauto.
                  repeat split; eauto.
                  edestruct (test_next_step μ') as (w & hlw & heqw).
                  eapply lts_oba_non_blocking_action_deter_inv. exact nb.
                  eassumption. eassumption.
                  etrans. eassumption.
                  etrans. symmetry. eapply heqv.
                  etrans. eassumption.
                  now symmetry.
         +++ destruct HypTr'' as (μ & duo & HypTr').
             destruct HypTr' as (r'' & HypTr'' & equiv'').
             destruct (eq_spec (f s') r'' (ActExt $ μ)) as (t0 & hlt0 & heqt0).
             { exists r. split; eauto. now symmetry. }
             assert (f s' ⟶[μ] t0) as Hyp; eauto.
             eapply inversion_test_external_action in Hyp; eauto.
             destruct Hyp as [good | continue].
             ++++ assert (t0 ⋍ t) as equiv.
                  { etrans. eauto. now symmetry. }
                  eapply outcome_preserved_by_eq in equiv; eauto.
             ++++ destruct continue as 
                    (s1 & s2 & μ'' & eq1 & eq_trace & equiv & his); subst.
                  right. exists μ' ,μ'', ε, s1, s2. repeat split; simpl; subst; eauto.
                  symmetry. etrans; eauto. symmetry in heqt0. symmetry; etrans ; eauto.
    + left. eapply test_reset_tau_path. exact not_nb. exact HypTr.
Qed.

Lemma inversion_tconv_tau_action `{
  @gLtsOba T A H gLtsT gLtsEqT, !Testing_Predicate T A outcome, !test_convergence_spec f} 
  s t :
  f s ⟶ t ->
  outcome t \/
  ∃ η μ' s1 s2 s3,
  s = s1 ++ [η] ++ s2 ++ [μ'] ++ s3
  /\ t ⋍ f (s1 ++ s2 ++ s3)
  /\ non_blocking η
  /\ Forall non_blocking s1 
  /\ Forall non_blocking s2
  /\ dual μ' η.
Proof.
  intros.
  eapply inversion_test_tau_action; eauto.
  + right. eapply tconv_computes_to_good.
  + intro μ. left. eapply tconv_does_no_external_action.
Qed.

Lemma inversion_ta_tau_action `{CC : Countable PreAct} `{
  @gLtsOba T A H gLtsT gLtsEqT,
  !Testing_Predicate T A outcome, !test_co_acceptance_set_spec PreAct f Γ}
  s O t :
  f O s ⟶ t ->
  outcome t \/ (∃ η μ s1 s2 s3, s = s1 ++ [η] ++ s2 ++ [μ] ++ s3
                          /\ t ⋍ f O (s1 ++ s2 ++ s3)
                          /\ non_blocking η
                          /\ Forall non_blocking s1 
                          /\ Forall non_blocking s2
                          /\ dual μ η).
Proof.
  intros.
  eapply inversion_test_tau_action; eauto.
  + left. eapply ta_does_no_tau; eauto.
  + intro μ. destruct (decide (non_blocking μ)) as [nb | not_nb]. 
    ++ left. eapply ta_does_no_non_blocking_actions; eauto.
    ++ right. intro e. 
       eapply ta_transition_to_good ; eauto.
Qed.

(** Converse implication of the first requirement. *)

Lemma must_if_co_cnv `{
  @gLtsObaFW P A H gLtsP gLtsEqP gLtsObaP,
  @gLtsObaFB T A H gLtsT gLtsEqT gLtsObaT, !Testing_Predicate T A outcome,
  !test_convergence_spec tconv} 

  `{@Prop_of_Inter P T A parallel_inter H gLtsP gLtsT}

  s (p : P) :
  p ⇓ᶜᵒ s -> must p (tconv s).
Proof.
  revert p.
  induction s
    as (s & Hlength) using
         (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
  intros p hcnv.
  induction (co_cnv_terminate p s hcnv) as [p hp IHtp].
  apply m_step.
  + eapply test_ungood.
  + edestruct tconv_always_reduces. exists (p ▷ x). eapply ParRight; eauto.
  + intros p' l. eapply IHtp; [|eapply co_cnv_preserved_by_lts_tau]; eauto.
  + intros e' l.
    destruct (inversion_tconv_tau_action s e' l)
      as [hu | (η & ν & s1 & s2 & s3 & eq__s & sc & i0 & i1 & i2 & duo)]; eauto with mdb.
    eapply must_eq_client. symmetry. eassumption.
    eapply Hlength.
    * subst. rewrite 6 length_app. simpl. lia.
    * subst. eapply co_cnv_annhil; eauto.
  + intros p' e' ν' ν inter hlp hle.
    destruct (inversion_tconv_external_action s ν e' hle)
      as [hg | (s1 & s2 & ν'' & heq & sc & eq & his)]; eauto with mdb. subst.
    destruct s1.
    * simpl in *.
      eapply must_eq_client. symmetry. eassumption.
      eapply Hlength; subst; eauto with mdb.
      eapply co_cnv_preserved_by_wt_act; eauto.
      eapply lts_to_wt; eauto.
    * eapply (co_cnv_drop_action_in_the_middle p (a :: s1) s2) in hlp; subst; eauto with mdb.
      eapply must_eq_client. symmetry. eassumption.
      eapply Hlength; subst; eauto with mdb.
      rewrite 2 length_app. simpl. lia.
Qed.

Lemma must_iff_cnv `{
  @gLtsObaFW P A H gLtsP gLtsEqP gLtsObaP,
  @gLtsObaFB T A H gLtsT gLtsEqT gLtsObaT, !Testing_Predicate T A outcome, 
  !test_convergence_spec tconv}

  `{@Prop_of_Inter P T A parallel_inter H gLtsP gLtsT}

  (p : P) s : must p (tconv s) <-> p ⇓ᶜᵒ s.
Proof. split; [eapply co_cnv_if_must | eapply must_if_co_cnv]; eauto. Qed.

Lemma completeness1 `{
    @gLtsObaFW P A H gLtsP gLtsEqP gLtsObaP,
    @gLtsObaFW Q A H gLtsQ gLtsEqQ gLtsObaQ,
    @gLtsObaFB T A H gLtsT gLtsEqT gLtsObaT, !Testing_Predicate T A outcome,
    ! test_convergence_spec tconv}

    `{@Prop_of_Inter P T A parallel_inter H gLtsP gLtsT}
    `{@Prop_of_Inter Q T A parallel_inter H gLtsQ gLtsT}

  (p : P) (q : Q) : p ⊑ₘᵤₛₜᵢ q -> p ≼₁ q.
Proof.
  intros hleq s hcnv.
  intros. now eapply must_iff_cnv, hleq, must_iff_cnv.
Qed.

(** Second requirement. *)

Lemma exists_forall_in {B} (ps : list B) (P : B -> Prop) (Q : B -> Prop)
  (h : forall p, p ∈ ps -> P p \/ Q p) : Exists P ps \/ Forall Q ps.
Proof.
  induction ps as [|p ?]. eauto.
  destruct IHps; destruct (h p); eauto; set_solver.
Qed.

Lemma exists_forall_in_gset `{Countable A} (ps : gset A) (P : A -> Prop) (Q : A -> Prop)
  (h : forall p, p ∈ ps -> P p \/ Q p) : (exists p, p ∈ ps /\ P p)\/ (forall p, p ∈ ps -> Q p).
Proof.
  induction ps using set_ind_L. set_solver.
  destruct IHps; destruct (h x); eauto; set_solver.
Qed.

Lemma wt_acceptance_set_subseteq
  `{gLtsP : @gLts P A H, !FiniteImagegLts P A, PreActP : @PreExtAction A H P FinA PreAct PreAct_eq PreAct_countable 𝝳 Φ gLtsP}
  μ s p q hacnv1 hacnv2 :
  p ⟹{μ} q ->
  map pre_co_actions_of (elements (wt_refuses_set q s hacnv1)) ⊆
    map pre_co_actions_of (elements (wt_refuses_set p (μ :: s) hacnv2)).
Proof.
  intros.
  intros a in__a.
  assert (wt_refuses_set q s hacnv1 ⊆ wt_refuses_set p (μ :: s) hacnv2).
  intros t in__t.
  eapply wt_refuses_set_spec2.
  eapply wt_refuses_set_spec1 in in__t.
  destruct in__t. split; eauto with mdb.
  eapply wt_push_left; eauto.
  set_solver.
Qed.

Lemma lts_tau_acceptance_set_subseteq
  `{gLtsP : @gLts P A H, !FiniteImagegLts P A, PreActP : @PreExtAction A H P FinA PreAct PreAct_eq PreAct_countable 𝝳 Φ gLtsP}
  s p q hacnv1 hacnv2 :
  p ⟶ q ->
  map pre_co_actions_of (elements $ wt_refuses_set q s hacnv1) ⊆
    map pre_co_actions_of (elements $ wt_refuses_set p s hacnv2).
Proof.
  intros.
  intros a in__a.
  assert (wt_refuses_set q s hacnv1 ⊆ wt_refuses_set p s hacnv2).
  { intros t in__t. eapply wt_refuses_set_spec2.
    eapply wt_refuses_set_spec1 in in__t.
    destruct in__t. split; eauto with mdb. }
  set_solver.
Qed.

Definition oas 
  `{gLtsP : @gLts P A H, FiniteImagegLts P A, PreActP : @PreExtAction A H P FinA PreAct PreAct_eq PreAct_countable 𝝳 Φ gLtsP}
  (p : P) (s : list A) (hcnv : p ⇓ s) : gset PreAct:=
  let ps : list P := elements (wt_refuses_set p s hcnv) in
  ⋃ map pre_co_actions_of ps.

Lemma union_wt_acceptance_set_subseteq
  `{gLtsP : @gLts P A H, !FiniteImagegLts P A, PreActP : @PreExtAction A H P FinA PreAct PreAct_eq PreAct_countable 𝝳 Φ gLtsP}
  μ s p q h1 h2 :
  p ⟹{μ} q -> oas q s h1 ⊆ oas p (μ :: s) h2.
Proof.
  intros hw a (O & mem1 & mem2)%elem_of_union_list.
  eapply elem_of_union_list.
  exists O. split; eauto. eapply wt_acceptance_set_subseteq; eauto.
Qed.

Lemma union_acceptance_set_lts_tau_subseteq
  `{gLtsP : @gLts P A H, !FiniteImagegLts P A, PreActP : @PreExtAction A H P FinA PreAct PreAct_eq PreAct_countable 𝝳 Φ gLtsP}
  s p q h1 h2 :
  p ⟶ q -> oas q s h1 ⊆ oas p s h2.
Proof.
  intros l a (L & mem1 & mem2)%elem_of_union_list.
  eapply elem_of_union_list.
  exists L. split; eauto.
  eapply lts_tau_acceptance_set_subseteq; eauto.
Qed.

Lemma after_blocking_co_of_must_tacc `{CC : Countable PreAct} `{
  @gLtsOba P A H gLtsP gLtsEqP,
  @gLtsOba T A H gLtsT gLtsEqT, !Testing_Predicate T A outcome,
  !test_co_acceptance_set_spec PreAct ta Γ}

  `{@Prop_of_Inter P T A parallel_inter H gLtsP gLtsT}

  (p : P) μ s E :
  p ⤓ -> blocking μ -> (forall q μ', parallel_inter μ' μ -> p ⟹{μ'} q -> must q (ta E s)) 
              -> must p (ta E (μ :: s) : T).
Proof.
  intro tp. revert E μ s. induction tp.
  intros L μ s not_nb hmq.
  eapply m_step.
  - eapply test_ungood.
  - edestruct (@test_tau_transition T A); eauto with mdb.
    now destruct test_co_acceptance_set_spec0. exists (p ▷ x). eapply ParRight; eauto.
  - intros. eapply H4. exact H5. eassumption. eauto with mdb.
  - intros e' l. eapply m_now.
    apply (test_reset_tau_path μ s e'). eassumption. eassumption.
  - intros p' e' μ' μ'' inter l0 l1.
    destruct (decide (μ'' = μ)) as [eq | neq].
    + subst. eapply test_follows_trace_determinacy in l1 as h1; eauto.
      eapply must_eq_client. symmetry; eauto.
      eapply hmq. eauto with mdb. eauto with mdb.
    + eapply m_now. eapply test_side_effect_by_construction;eauto.
Qed.

Lemma ta_tau_ex `{CC : Countable PreAct}`{
  @gLtsObaFB E A H gLtsE LtsEqE LtsOBAE,
  !Testing_Predicate E A outcome, !test_co_acceptance_set_spec PreAct f Γ} 
  s1 s2 s3 η μ L :
  non_blocking η -> Forall non_blocking s1 -> Forall non_blocking s2 -> dual μ η ->
  f L (s1 ++ [η] ++ s2 ++ [μ] ++ s3) ⟶⋍ f L (s1 ++ s2 ++ s3).
Proof.
  intros nb Hyp Hyp' duo.
  assert (f L (s1 ++ [η] ++ s2 ++ [μ] ++ s3) ⟶⋍[η]
            f L (s1 ++ s2 ++ [μ] ++ s3)) as (e1 & l1 & heq1).
  { eapply (@f_gen_lts_mu_in_the_middle E A _ _ _ _ _ _ (f L) _
            s1 (s2 ++ [μ] ++ s3) η); simpl in *; eauto. }
  assert (f L (s1 ++ s2 ++ [μ] ++ s3) ⟶⋍[μ]
            f L ((s1 ++ s2) ++ s3)) as (e2 & l2 & heq2).
  { replace (s1 ++ s2 ++ [μ] ++ s3) with ((s1 ++ s2) ++ [μ] ++ s3).
    eapply (@f_gen_lts_mu_in_the_middle E A _ _ _ _ _ _ (f L) _
            (s1 ++ s2) s3 μ); simpl in *; eauto.
    eapply Forall_app. split; eauto. now rewrite <- app_assoc. }
  simpl in *. edestruct (eq_spec e1 e2) as (e' & l' & heq'). eauto.
  destruct (lts_oba_fb_feedback nb duo l1 l') as (t & lt & heqt); eauto.
  exists t. split; eauto.
  rewrite <- app_assoc in heq2.
  transitivity e'. eauto.
  transitivity e2; eauto.
Qed.

Lemma must_ta_monotonicity_non_blocking `{CC : Countable PreAct} `{
  @gLtsObaFB E A H gLtsE gLtsEqE W, AbE : @AbsAction A H E FinA gLtsE Φ, 
  !Testing_Predicate E A outcome, !test_co_acceptance_set_spec PreAct ta Γ} 
  s e η L1 :
  non_blocking η -> ta L1 s ⟶[η] e 
    -> forall L2, L1 ⊆ L2
      -> exists t, ta L2 s ⟶[η] t.
Proof.
  revert e L1.
  induction s as [|μ s']; intros e L1 nb l L2 hsub.
  - exfalso. eapply lts_refuses_spec2, ta_does_no_non_blocking_actions; eauto.
  - destruct (decide (non_blocking μ)) as [nb' | not_nb'].
    + edestruct
        (@test_next_step E A _ _ _ _ _ (ta L1) _ μ s')
        as (e1 & hle1 & heqe1). (* simpl in hle1. *)
       edestruct
         (@test_next_step E A _ _ _ _ _ (ta L2) _ μ s')
         as (e2 & hle2 & heqe2). (* simpl in hle2. *)
       destruct (decide (non_blocking μ)) as [nb'' | not_nb''].
       * destruct (decide (η = μ)) as [eq | not_eq]. 
         -- subst; eauto.
         -- destruct (lts_oba_non_blocking_action_confluence nb'' not_eq hle1 l)
              as (r1 & l1 & r2 & l2 & heq).
            edestruct (eq_spec (ta L1 s') r1) as (e' & hle' & heqe').
            symmetry in heqe1. eauto.
            eapply IHs' in hle' as (t & hlt); eauto.
            edestruct (eq_spec e2 t) as (e2' & hle2' & heqe2'). eauto.
            edestruct (lts_oba_non_blocking_action_delay nb'' hle2 hle2') as (v & l3 & l4).
            eauto with mdb.
       * assert (¬ non_blocking η) as imp.
           { eapply side_effect_by_blocking_action; eauto. }
           contradiction.
    + edestruct
         (@test_next_step E A _ _ _ _ _  (ta L2) _ μ s')
         as (r' & hl' & heqr').
       assert (¬ non_blocking η) as imp.
       { eapply side_effect_by_blocking_action; eauto. } 
       contradiction.
Qed.

Lemma must_ta_monotonicity_nil {P Q : Type} `{
  gLtsP: @gLts P A H, PreActP : @PreExtAction A H P FinA PreAct PreAct_eq PreAct_countable 𝝳 Φ gLtsP,
  gLtsQ: @gLts Q A H, PreActQ : @PreExtAction A H Q FinA PreAct PreAct_eq PreAct_countable 𝝳 Φ gLtsQ,
  @gLtsObaFB E A H gLtsE gLtsEqE W, AbE : @AbsAction A H E FinA gLtsE Φ,
  !Testing_Predicate E A outcome, !test_co_acceptance_set_spec PreAct ta (fun x => 𝝳 (Φ x))}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p : P) L1 : 
  must p (ta L1 ε) 
    -> forall L2, L1 ⊆ L2 
      -> must p (ta L2 ε).
Proof.
  intros hm.
  assert (hpt : p ⤓)
    by now (eapply must_terminate_unoutcome , test_ungood; eauto).
  induction hpt. dependent induction hm; intros L2 hsub.
  - assert (¬ outcome (ta L1 ε)).
    { now eapply test_ungood. }
    contradiction.
  - eapply m_step; eauto with mdb.
    + eapply test_ungood.
    + destruct ex as ((p' & e') & l').
      inversion l'; subst.
      +++ exists (p' ▷ (ta L2 ε)). eapply ParLeft; eauto.
      +++ exfalso. assert ({q : E | ta L1 ε ⟶ q}) as impossible.
          eauto.
          eapply lts_refuses_spec2 in impossible.
          assert (ta L1 ε ↛). { eapply ta_does_no_tau; eauto. }
          contradiction.
      +++ destruct (decide (non_blocking μ2)) as [nb2 | not_nb2].
          ++++ exfalso.
               assert ({q : E | ta L1 ε ⟶[μ2] q}) as impossible; eauto.
               eapply lts_refuses_spec2 in impossible. 
               assert (ta L1 ε ↛[μ2]).
               { eapply ta_does_no_non_blocking_actions; eauto. }
               contradiction.
          ++++ assert (μ2 ∈ co_actions_of p) as co_set.
               { exists μ1. repeat split; eauto. eapply lts_refuses_spec2; eauto. }
               eapply preactions_of_fin_test_spec1 in co_set.
               eapply preactions_of_spec in co_set.
               eapply ta_actions_are_in_its_gamma_set in l2 as mem; eauto.
               eapply hsub in mem.
               eapply ta_has_a_representative_transition_for_its_gamma_set in mem as (r & μ'2 & Tr' & eq'); eauto.
               rewrite<- eq' in co_set.
               eapply preactions_of_spec in co_set; eauto.
               eapply preactions_of_fin_test_spec2 in co_set as (μ'' & co_set & eq'').
               destruct co_set as (μ'1 & Tr & duo & b).
               assert (blocking μ'2).
               { intro imp. eapply ta_does_no_non_blocking_actions in imp. 
                 eapply (@lts_refuses_spec2 E). exists r. exact Tr'. eauto. }
               assert (¬ ta L2 ε ↛[μ'']) as Tr''.
               { eapply (abstraction_test_spec μ'2 μ'' (ta L2 ε)) in eq''; eauto.
                 eapply lts_refuses_spec2; eauto. }
               eapply lts_refuses_spec1 in Tr'' as (e'' & Tr'').
               eapply lts_refuses_spec1 in Tr as (p'' & Tr).
               exists (p'', e''). eapply ParSync. exact duo. exact Tr. exact Tr''.
    + intros e l.
      exfalso. 
      assert ({q : E | ta L2 ε ⟶ q}) as impossible. eauto.
      eapply lts_refuses_spec2 in impossible. 
      assert (ta L2 ε ↛). eapply ta_does_no_tau; eauto.
      contradiction.
    + intros p' e' μ μ' inter l2 l1.
      destruct (decide (non_blocking μ')) as [nb | not_nb].
      ++ exfalso. 
         assert ({q : E | ta L2 ε ⟶[μ'] q}) as impossible. eauto.
         eapply lts_refuses_spec2 in impossible. 
         assert (ta L2 ε ↛[μ']). eapply ta_does_no_non_blocking_actions; eauto.
         contradiction.
      ++ eapply (@ta_transition_to_good 
            PreAct PreAct_eq PreAct_countable E A H gLtsE gLtsEqE
                  outcome Testing_Predicate0 ta (fun x => 𝝳 (Φ x))) in l1;eauto.
         eapply m_now; eauto.
Qed.

Lemma must_ta_monotonicity {P : Type} `{
  @gLtsObaFW P A H gLtsP gLtsEqP gLtsObaP, PreActP : @PreExtAction A H P FinA PreAct PreAct_eq PreAct_countable 𝝳 Φ gLtsP,
  @gLtsObaFB T A H gLtsT gLtsEqT gLtsObaT,
  @AbsAction A H T FinA gLtsT Φ, !Testing_Predicate T A outcome,
  !test_co_acceptance_set_spec PreAct ta (fun x => (𝝳 (Φ x)))}

  `{@Prop_of_Inter P T A parallel_inter H gLtsP gLtsT}

  s (p : P) E1 :

  must p (ta E1 s) 
    -> forall E2, E1 ⊆ E2
      -> must p (ta E2 s).
Proof.
  revert p E1.
  induction s
    as (s & Hlength) using
         (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
  destruct s as [|ν s']; intros p E1 hm E2 hsub; subst.
  - eapply must_ta_monotonicity_nil; eauto.
  - assert (htp : p ⤓) by (eapply must_terminate_unoutcome, test_ungood; eauto).
    induction htp.
    inversion hm.
    * now eapply test_ungood in H6.
    * eapply m_step; eauto with mdb.
      + eapply test_ungood.
      + destruct (decide (non_blocking ν)) as [nb | not_nb].
        ++ edestruct (lts_oba_fw_forward p ν (co ν)) as (p' & Hyp').
           assert (p ⟶[(co ν)] p').
           { eapply Hyp'; eauto. destruct (exists_dual ν) as (x & duo).
             symmetry. eauto. }
           assert (ta E2 (ν :: s') ⟶⋍[ν] ta E2 s') as (t' & tr' & eq').
           { eapply test_next_step. }
           exists (p' , t'). eapply ParSync; eauto.
           destruct (exists_dual ν) as (x & duo). symmetry. eauto.
        ++ assert (∃ e', ta E2 (ν :: s') ⟶ e') as (e' & tr').
           { eapply test_tau_transition. eauto. }
           exists (p , e'). eapply ParRight. exact tr'.
      + intros e' l.
        edestruct @inversion_ta_tau_action as [|Hyp]; eauto with mdb.
        destruct Hyp as (η & μ & s1 & s2 & s3 & heqs & sc & himu & his1 & his2 & duo).
        eapply (must_eq_client p (ta E2 (s1 ++ s2 ++ s3))). now symmetry.
        edestruct (@ta_tau_ex _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s1 s2 s3 η μ E1) as (t & hlt & heqt); eauto.
        eapply Hlength; eauto.
        ++ rewrite heqs, 6 length_app. simpl. lia.
        ++ eapply must_eq_client. eapply heqt. eapply et. now rewrite heqs.
      + intros p' e' μ μ' inter l1 l2.
        edestruct @inversion_ta_external_action as [|Hyp]; eauto with mdb.
        destruct Hyp as (s1 & s2 & μ''' & heqs & heq & eq & his1). subst.
        eapply must_eq_client. symmetry. eassumption.
        edestruct @f_gen_lts_mu_in_the_middle as (t & l & heq'); eauto.
        now destruct test_co_acceptance_set_spec0.
        eapply Hlength. rewrite heqs.
        rewrite 2 length_app. simpl. lia.
        eapply must_eq_client. eapply heq'.
        eapply com; eauto. rewrite heqs. eassumption.
        eassumption.
Qed.

Lemma stable_process_must_ta_or_empty_pre_action_set {P : Type} `{
  @gLtsOba P A H gLtsP gLtsEqP, @PreExtAction A H P FinA PreAct PreAct_eq PreAct_countable 𝝳 Φ gLtsP,
  @gLtsOba T A H gLtsT gLtsEqT,
  @AbsAction A H T FinA gLtsT Φ, !Testing_Predicate T A outcome, 
  !test_co_acceptance_set_spec PreAct ta (fun x => (𝝳 (Φ x)))}

  `{@Prop_of_Inter P T A parallel_inter H gLtsP gLtsT}

  (p : P) (E : gset PreAct): 

  p ↛ 
  -> must p (ta ((pre_co_actions_of p) ∖ E) ε)
          \/ (pre_co_actions_of p ⊆ E).
Proof.
  intros.
  remember ((pre_co_actions_of p) ∖ E) as D.
  destruct D as [|a D'] using set_ind_L.
  + right. set_solver.
  + left.
      eapply m_step.
      ++ now eapply test_ungood.
      ++ assert (a ∈ pre_co_actions_of p ∖ E) as mem'.
         { set_solver. }
         assert (a ∈ pre_co_actions_of p) as co_set. 
         { eauto. eapply elem_of_difference; eauto. }
         eapply ta_has_a_representative_transition_for_its_gamma_set in mem' as (r & μ & Tr & eq); eauto.
         subst. eapply preactions_of_spec in co_set.
         eapply preactions_of_fin_test_spec2 in co_set as (μ'' & co_set & eq). 
         destruct co_set as (μ' & Tr' & duo & b).
         assert (blocking μ).
         { intro imp. eapply ta_does_no_non_blocking_actions in imp. 
           eapply (@lts_refuses_spec2 T). exists r. exact Tr. eauto. }
         assert (¬ (ta (pre_co_actions_of p ∖ E) ε) ↛[μ'']) as Tr''.
         { eapply abstraction_test_spec; eauto. eapply lts_refuses_spec2; eauto. }
         rewrite<- HeqD in Tr''.
         eapply lts_refuses_spec1 in Tr'' as (e'' & Tr'').
         eapply lts_refuses_spec1 in Tr' as (p'' & Tr').
         exists (p'' , e''). eapply ParSync; eauto.
      ++ intros p' l'. exfalso. eapply (lts_refuses_spec2 p); eauto with mdb.
      ++ intros e' l'. exfalso.
         assert (¬ ta (pre_co_actions_of p ∖ E) ε ↛ ).
         { rewrite<- HeqD. eapply lts_refuses_spec2; eauto. }
         assert (ta (pre_co_actions_of p ∖ E) ε ↛).
         { rewrite<- HeqD. eapply ta_does_no_tau ; eauto. }
         contradiction.
      ++ intros p'' e'' μ' μ inter l'1 l'0.
         destruct (decide (non_blocking μ)) as [nb' | not_nb'].
         ++++++ exfalso.
                eapply (@lts_refuses_spec2 T); eauto with mdb.
                eapply ta_does_no_non_blocking_actions ; eauto.
         ++++++ eapply ta_transition_to_good in l'0. 
                eapply m_now. exact l'0. eauto.
Qed.

Lemma must_ta_or_empty_pre_action_set_for_empty_trace {P : Type} `{
  gLtsP : @gLts P A H,
  @gLtsObaFW P A H gLtsP gLtsEqP gLtsObaP, !FiniteImagegLts P A, @PreExtAction A H P FinA PreAct PreAct_eq PreAct_countable 𝝳 Φ gLtsP,
  @gLtsObaFB T A H gLtsT gLtsEqT gLtsObaT,
  @AbsAction A H T FinA gLtsT Φ, !Testing_Predicate T A outcome,
  !test_co_acceptance_set_spec PreAct ta (fun x => (𝝳  (Φ x)))}

  `{@Prop_of_Inter P T A parallel_inter H gLtsP gLtsT}

  (p : P) (hcnv : p ⇓ ε) (E : gset PreAct):

  (exists p', p ⟹ p' /\ lts_refuses p' τ /\ pre_co_actions_of p' ⊆ E)
  \/ must p (ta ((oas p ε hcnv) ∖ E) ε).
Proof.
  induction (cnv_terminate p ε hcnv) as (p, hpt, ihhp).
  destruct (decide (lts_refuses p τ)) as [st | (p'' & l)%lts_refuses_spec1].
  + destruct (stable_process_must_ta_or_empty_pre_action_set p E st) as [Hyp | Hyp].
    ++ right. assert (oas p ε hcnv = pre_co_actions_of p) as eq.
       { unfold oas. rewrite wt_refuses_set_refuses_singleton, elements_singleton; eauto.
         simpl. now rewrite union_empty_r_L. } rewrite eq.
       exact Hyp.
    ++ left. exists p. split; eauto. constructor.
  + assert (∀ q0 : P,
         q0 ∈ lts_tau_set p
         → (∃ p' : P, q0 ⟹ p' ∧ p' ↛ ∧ pre_co_actions_of p' ⊆ E)
             ∨ (∃ h, must q0 (ta ((oas q0 ε h) ∖ E) ε))) as Hyp.
    { intros q' l'%lts_tau_set_spec. destruct (hpt q' l') as (hq).
      assert (q' ⇓ ε) as cnv_nil' by (eapply (cnv_nil q' (tstep q' hq))).
      edestruct (ihhp q' l') as [hl | hr].
      * now left.
      * right. exists (cnv_nil _ (tstep q' hq)). eauto. }
    destruct (@exists_forall_in P (lts_tau_set p) _ _ Hyp) as [Hyp' | Hyp'].
    - eapply Exists_exists in Hyp' as (t & l'%lts_tau_set_spec & t' & w & st & sub).
        left. exists t'. eauto with mdb.
    - right. eapply m_step.
      * eapply test_ungood.
      * exists (p'' ▷ ta ((oas p ε hcnv) ∖ E) ε). eapply ParLeft; eauto.
      * intros p0 l0%lts_tau_set_spec.
        eapply Forall_forall in Hyp' as (h0 & hm); eauto.
        eapply must_ta_monotonicity; eauto.
        eapply difference_mono_r. eapply union_acceptance_set_lts_tau_subseteq. 
        eapply lts_tau_set_spec. exact l0.
      * intros e' l'. exfalso.
             eapply (@lts_refuses_spec2 T). eauto. eapply ta_does_no_tau; eauto.
      * intros p0 e0 μ' μ inter lp le.
             destruct (decide (non_blocking μ)) as [nb | not_nb].
        ++ exfalso.
           assert ({q' : T | ta ((oas p ε hcnv) ∖ E) ε ⟶[μ] q'}).
           { eauto. } eapply (lts_refuses_spec2); eauto. 
           eapply ta_does_no_non_blocking_actions; eauto.
        ++ eapply m_now. eapply ta_transition_to_good; eauto.
Qed.

(* Lemma must_ta_or_empty_pre_action_set_for_all_trace {P : Type} `{
  @gLtsObaFW P A H gLtsP gLtsEqP gLtsObaP, !FiniteImagegLts P A, @PreExtAction A H P FinA PreAct PreAct_eq PreAct_countable 𝝳 Φ gLtsP,
  @gLtsObaFB T A H gLtsT gLtsEqT gLtsObaT, @AbsAction A H T FinA gLtsT Φ,
  !Testing_Predicate T A outcome, !test_co_acceptance_set_spec PreAct ta (fun x => (𝝳 (Φ x)))} 

  `{@Prop_of_Inter P T A parallel_inter H gLtsP gLtsT}

  s (p : P) (hcnv : p ⇓ᶜᵒ s) (E : gset PreAct):

  (exists p' s'', Forall2 parallel_inter s'' s /\ p ⟹[s''] p' /\ lts_refuses p' τ /\ pre_co_actions_of p' ⊆ E) 
      \/ must p (ta ((oas p s hcnv) ∖ E) s).
Proof.
  revert p hcnv E.
  induction s as [|μ s'].
  - intros. edestruct (must_ta_or_empty_pre_action_set_for_empty_trace p hcnv E) as [(p' & Hyp & wt & stable) | hm].
    + left. exists p', ε. repeat split; eauto.
    + right. exact hm.
  - intros p hcnv E.
    (* set (ps := wt_set_mu p μ s' hcnv).
    inversion hcnv as [| ? ? ? conv Hyp_conv]; subst.
    assert (hcnv0 : forall p', p' ∈ ps -> p' ⇓ s') by (intros ? mem%wt_set_mu_spec1; eauto).
    assert (he : ∀ p', p' ∈ ps ->
     ((exists pr p0, p0 ∈ wt_refuses_set p' s' pr ∧ pre_co_actions_of p0 ⊆ E) 
             \/ (exists h, must p' (ta ((oas p' s' h) ∖ E) s')))).
    { intros p' mem. destruct (IHs' p' (hcnv0 _ mem) E) as [(r & w & st & sub)| hm].
      * left. eapply wt_set_mu_spec1 in mem.
        exists (Hyp_conv _ mem), r. split; [eapply wt_refuses_set_spec2 |]; eauto.
      * right. eauto. }
    destruct (exists_forall_in_gset ps _ _ he) as [Hyp | Hyp].
    + left. destruct Hyp
          as (p1 & ?%wt_set_mu_spec1 & ? & r & (? & ?)%wt_refuses_set_spec1 & ?).
      exists r. repeat split; eauto. eapply wt_push_left; eauto.
    + right.
      destruct (decide (non_blocking μ)) as [nb | b].
      +++ inversion hcnv; subst.
          (* destruct (lts_oba_fw_forward p (co_of μ) μ) as (p' & l0 & l1); eauto.
          assert (ta ((oas p (μ :: s') hcnv) ∖ E) (μ :: s')
                   ⟶⋍[co_of $ μ] ta ((oas p (μ :: s') hcnv) ∖ E) s')
            as (e' & hle' & heqe') by eapply test_next_step.
          eapply must_non_blocking_action_swap_l_fw; eauto.
          eapply (must_eq_client _ _ _ (symmetry heqe')).
          edestruct (Hyp p') as (? & hm).
          eapply wt_set_mu_spec2; eauto with mdb.
          assert (oas p' s' x ∖ E ⊆ oas p (μ :: s') hcnv ∖ E).
          { eapply difference_mono_r. eapply union_wt_acceptance_set_subseteq; eauto with mdb. }
          eapply must_ta_monotonicity; eauto. *) admit.
      +++ (* eapply after_blocking_co_of_must_tacc; eauto.
          intros p' μ' inter hw.
          edestruct (Hyp p') as (? & hm).
          eapply wt_set_mu_spec2. ; eauto.
          assert ((oas p' s' x ∖ E) ⊆ oas p (μ :: s') hcnv ∖ E).
          { eapply difference_mono_r. eapply union_wt_acceptance_set_subseteq; eauto with mdb. }
          eapply must_ta_monotonicity; eauto. Unshelve. exact (⋃ map pre_co_actions_of (elements ps) ∖ E). *)
          admit. *)
Admitted. *)

Lemma not_must_ta_without_required_acc_set {Q : Type} `{
  @gLtsObaFW Q A H gLtsQ gLtsEqQ gLtsObaQ, @PreExtAction A H Q FinA PreAct PreAct_eq PreAct_countable 𝝳 Φ gLtsQ,
  @gLtsObaFB T A H gLtsT gLtsEqT gLtsObaT,
  @AbsAction A H T FinA gLtsT Φ,!Testing_Predicate T A outcome,
  !test_co_acceptance_set_spec PreAct ta (fun x => (𝝳  (Φ x)))} 

  `{@Prop_of_Inter Q T A parallel_inter H gLtsQ gLtsT}

  (q q' : Q) s' s (E : gset PreAct) :

  Forall2 parallel_inter s' s -> q ⟹[s'] q' -> q' ↛ -> ¬ must q (ta (E ∖ (pre_co_actions_of q')) s).
Proof.
  intros inter_trace wt hst. revert inter_trace. revert s.
  dependent induction wt; intros s' inter_trace hm. rename p into q.
  - inversion inter_trace; subst. inversion hm as [happy | ]; subst.
    ++ contradict happy. eapply test_ungood.
    ++ destruct ex as (t & l). inversion l; subst.
       +++ eapply (lts_refuses_spec2 q τ); eauto with mdb.
       +++ eapply lts_refuses_spec2, ta_does_no_tau; eauto.
       +++ destruct (decide (non_blocking μ2)) as [nb2 | not_nb2].
           ++++ exfalso. eapply lts_refuses_spec2.
                eauto. eapply ta_does_no_non_blocking_actions ;eauto. 
           ++++ eapply ta_actions_are_in_its_gamma_set in l2 as mem; eauto.
                assert (𝝳 (Φ μ2) ∉ pre_co_actions_of q) as not_in_mem.
                { set_solver. }
                assert (𝝳 (Φ μ2) ∈ pre_co_actions_of q) as in_mem.
                { eapply preactions_of_spec. eapply preactions_of_fin_test_spec1. exists μ1. repeat split; eauto.
                eapply lts_refuses_spec2; eauto. }
                contradiction.
  - eapply (IHwt hst s' inter_trace), (must_preserved_by_lts_tau_srv p q _ hm l).
  - inversion inter_trace as [| ? ? ? ? inter inter_trace']; subst.
    assert (ta (E ∖ (pre_co_actions_of t)) (y :: l') ⟶⋍[y]
              ta (E ∖ (pre_co_actions_of t)) l') as (e' & hle' & heqe')
    by eapply test_next_step.
    assert (¬ outcome (ta (E ∖ pre_co_actions_of t) (y :: l'))).
    { eapply test_ungood. }
    eapply (IHwt hst l' inter_trace').
    eapply must_eq_client; eauto.
    eapply must_preserved_by_synch_if_notoutcome; eauto.
Qed.

(* Lemma completeness2 {P Q : Type} `{
  @gLtsObaFW P A H gLtsP gLtsEqP gLtsObaP, !FiniteImagegLts P A, @PreExtAction A H P FinA PreAct PreAct_eq PreAct_countable 𝝳 Φ gLtsP,
  @gLtsObaFW Q A H gLtsQ gLtsEqQ gLtsObaQ, !FiniteImagegLts Q A, @PreExtAction A H Q FinA PreAct PreAct_eq PreAct_countable 𝝳 Φ gLtsQ,
  @gLtsObaFB T A H gLtsT gLtsEqT gLtsObaT, 
  @AbsAction A H T FinA gLtsT Φ, !Testing_Predicate T A outcome, !test_co_acceptance_set_spec PreAct ta (fun x => (𝝳 (Φ x)))}

  `{@Prop_of_Inter P T A parallel_inter H gLtsP gLtsT}
  `{@Prop_of_Inter Q T A parallel_inter H gLtsQ gLtsT}

  (p : P) (q : Q) : p ⊑ₘᵤₛₜᵢ q -> p ≼₂ q.
Proof.
  intros hpre s s' q' hacnv inter_trace w st.
  destruct (must_ta_or_empty_pre_action_set_for_all_trace s p hacnv (pre_co_actions_of q')) as [|hm].
  + eauto.
  + eapply hpre in hm. contradict hm.
    (* eapply not_must_ta_without_required_acc_set; set_solver. *) admit.
Admitted.

Lemma completeness_fw {P Q : Type} `{
  @gLtsObaFW P A H gLtsP gLtsEqP gLtsObaP, !FiniteImagegLts P A, @PreExtAction A H P FinA PreAct PreAct_eq PreAct_countable 𝝳 Φ gLtsP,
  @gLtsObaFW Q A H gLtsQ gLtsEqQ gLtsObaQ, !FiniteImagegLts Q A, @PreExtAction A H Q FinA PreAct PreAct_eq PreAct_countable 𝝳 Φ gLtsQ,
  @gLtsObaFB T A H gLtsT gLtsEqT gLtsObaT, !FiniteImagegLts T A,
  @AbsAction A H T FinA gLtsT Φ, !Testing_Predicate T A outcome, !test_convergence_spec tconv, !test_co_acceptance_set_spec PreAct ta (fun x => (𝝳  (Φ x)))}

  `{@Prop_of_Inter P T A parallel_inter H gLtsP gLtsT}
  `{@Prop_of_Inter Q T A parallel_inter H gLtsQ gLtsT}

  (p : P) (q : Q) : p ⊑ₘᵤₛₜᵢ q -> p ≼ₐₛ q.
Proof.
  intros. split.
  - now apply completeness1.
  - now apply completeness2.
Qed. *)

(*
From stdpp Require Import gmultiset.

#[global] Program Instance PreActconvtionForFW 
  `{@PreExtAction A H P FinA PreAct PreAct_eq PreAct_countable 𝝳 Φ gLtsP}
  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts} 
  : @PreExtAction A H (P * mb A) FinA PreAct PreAct_eq PreAct_countable 𝝳 Φ (FW_gLts gLtsP) := 
  {| pre_co_actions_of p := pre_co_actions_of p.1 ∪ dom (gmultiset_map (fun x => 𝝳 (Φ (co x))) p.2); 
     pre_co_actions_of_fin p := 
     fun pre_μ => ∃ μ', μ' ∈ co_actions_of p /\ pre_μ = (Φ μ'); |}.
Next Obligation.
  intros. exists μ. repeat split; eauto.
Qed.
Next Obligation.
  intros. destruct H2 as (μ' & mem & eq). exists μ'. repeat split; eauto.
Qed.
Next Obligation.
 intros. split.
 - intro mem. destruct p as (p , m). destruct mem as (μ' & mem & eq).
   destruct mem as (μ'' & tr & duo & b). eapply lts_refuses_spec1 in tr as ((p',m') & tr).
   inversion tr; subst.
   + eapply elem_of_union_l. simpl. eapply preactions_of_spec.
     eapply preactions_of_fin_test_spec1. exists μ''. repeat split; eauto.
     eapply lts_refuses_spec2; eauto.
   + destruct (decide (non_blocking μ'')) as [nb | not_nb].
     * assert (non_blocking μ''); eauto. eapply (non_blocking_action_in_ms m μ'' m') in nb; eauto. subst.
       eapply elem_of_union_r. eapply gmultiset_elem_of_dom. simpl.
       assert (gmultiset_map (λ x : A, 𝝳 (Φ (co x))) ({[+ μ'' +]} ⊎ m') = 
        gmultiset_map (λ x : A, 𝝳 (Φ (co x))) {[+ μ'' +]} ⊎ gmultiset_map (λ x : A, 𝝳 (Φ (co x))) m') as eq.
       by eapply gmultiset_map_disj_union.
       rewrite eq. rewrite gmultiset_map_singleton.
       assert (μ'' = (co μ')). { eapply unique_nb; eauto. } subst.
       assert ((co (co μ')) = μ') as eq'. { admit. } rewrite eq'. multiset_solver. 
     * assert (¬ non_blocking μ''); eauto.
       eapply blocking_action_in_ms in not_nb as (eq & duo' & nb); eauto. subst.
       symmetry in duo. eapply (nb_not_nb (co μ'') μ') in nb ;eauto. contradiction.
 - intro mem. destruct p as (p , m). eapply elem_of_union in mem. destruct mem as [p_co_act | multiset_co_act].
   + simpl in p_co_act. eapply preactions_of_spec in p_co_act.
     eapply preactions_of_fin_test_spec2 in p_co_act as (μ' & mem & eq). simpl.
     subst. exists μ'. destruct mem as (μ'' & tr & duo & b).
     repeat split; eauto. exists μ''. repeat split; eauto. eapply lts_refuses_spec2.
     eapply lts_refuses_spec1 in tr as (p' & tr). exists (p' ▷ m).
     eapply ParLeft. exact tr.
   + eapply gmultiset_elem_of_dom in multiset_co_act. simpl in *.
     admit.
Admitted. *)

(* Lemma completeness {P Q : Type} `{
  @gLtsObaFB P A H gLtsP gLtsEqP gLtsObaP, !FiniteImagegLts P A,
  @gLtsObaFB Q A H gLtsQ gLtsEqQ gLtsObaQ, !FiniteImagegLts Q A,
  @gLtsObaFB T A H gLtsT gLtsEqT gLtsObaT, !FiniteImagegLts T A,
  @AbsAction A H T FinA gLtsT Φ, !Testing_Predicate T A outcome}

  `{@Prop_of_Inter P T A parallel_inter H gLtsP gLtsT}
  `{@Prop_of_Inter Q T A parallel_inter H gLtsQ gLtsT}

  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}
  `{@Prop_of_Inter (P * mb A) T A parallel_inter H (FW_gLts gLtsP) gLtsT}

  `{@Prop_of_Inter Q (mb A) A fw_inter H gLtsQ MbgLts}
  `{@Prop_of_Inter (Q * mb A) T A parallel_inter H (FW_gLts gLtsQ) gLtsT}

  `{@PreExtAction A H (P * mb A) FinA PreAct PreAct_eq PreAct_countable 𝝳 Φ (FW_gLts gLtsP)}
  `{@PreExtAction A H (Q * mb A) FinA PreAct PreAct_eq PreAct_countable 𝝳 Φ (FW_gLts gLtsQ)}

  `{!test_convergence_spec tconv, !test_co_acceptance_set_spec PreAct ta (fun x => (𝝳 (Φ x)))}

  (p : P) (q : Q) : (ctx_pre p q) -> p ▷ ∅ ≼ₐₛ q ▷ ∅.
Proof.
  intros hctx.
  eapply (@completeness_fw (P * mb A) (Q * mb A)); eauto.
  exact FW_gLtsObaFW. exact gLtsMBFinite. exact FW_gLtsObaFW. exact gLtsMBFinite.
  now rewrite <- Lift.lift_fw_ctx_pre.
Qed. *)