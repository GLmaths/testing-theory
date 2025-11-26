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

From Coq.Unicode Require Import Utf8.
From Coq.Program Require Import Equality.
From stdpp Require Import finite gmap decidable.
From Must Require Import ActTau gLts Bisimulation Lts_OBA Subset_Act WeakTransitions Testing_Predicate
    StateTransitionSystems InteractionBetweenLts Convergence Termination FiniteImageLTS.

(********************************************* Definition of Must_i ********************************************)

Inductive must_sts 
  `{Sts (P1 * P2), outcome : P2 -> Prop}
  (p : P1) (e : P2) : Prop :=
| m_sts_now : outcome e -> must_sts p e
| m_sts_step
    (nh : ¬ outcome e)
    (nst : ¬ sts_refuses (p, e))
    (l : forall p' e', sts_step (p, e) (p', e') -> must_sts p' e')
  : must_sts p e
.

Global Hint Constructors must_sts:mdb.

(********************* Definition of Must_i decomposed with parallel computation definition *****************)

Inductive must `{
    gLtsP : @gLts P A H, 
    gLtsE : ! gLts E A, ! gLtsEq E A, !Testing_Predicate E A outcome} 

    `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

    (p : P) (e : E) : Prop :=
| m_now : outcome e -> must p e
| m_step
    (nh : ¬ outcome e)
    (ex : ∃ t, (p, e) ⟶ t)
    (pt : forall p', p ⟶ p' -> must p' e)
    (et : forall e', e ⟶ e' -> must p e')
    (com : forall p' e' μ1 μ2, parallel_inter μ1 μ2
      -> p ⟶[μ1] p' 
        -> e ⟶[μ2] e'  
          -> must p' e')
  : must p e
.

Notation "p 'must_pass' e" := (must p e) (at level 70).

Global Hint Constructors must:mdb.

(****************** Must_i and Must decomposed with parallel computation definition are equivalent ****************)

Lemma must_sts_iff_must `{
  gLtsP : @gLts P A H, 
  gLtsE : !gLts E A, !gLtsEq E A, !Testing_Predicate E A outcome}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p : P) (e : E) :
  @must_sts P E _ outcome p e <-> p must_pass e.
Proof.
  split.
  - intro hm. dependent induction hm; eauto with mdb.
    eapply m_step; eauto with mdb.
    + eapply sts_refuses_spec1 in nst as ((p', e') & hl).
      exists (p', e'). now simpl in hl.
    + simpl in *; eauto with mdb.
    + simpl in *; eauto with mdb.
    + intros p' e' μ1 μ2 duo hl1 hl2.
      eapply H1. simpl.
      eapply (ParSync μ1 μ2); eauto.
  - intro hm. dependent induction hm; eauto with mdb.
    eapply m_sts_step; eauto with mdb.
    + eapply sts_refuses_spec2.
      destruct (decide (sts_refuses (p, e))).
      ++ exfalso.
         destruct ex as ((p', e'), hl).
         eapply sts_refuses_spec2 in s; eauto.
         exists (p', e'). now simpl.
      ++ now eapply sts_refuses_spec1 in n.
    + intros p' e' hl.
      inversion hl; subst; eauto with mdb.
Qed.

(********************************* Definition of the contextual pre order with Must_i *********************************)

Definition ctx_pre `{
  gLtsP : gLts P A, 
  gLtsQ : !gLts Q A, 
  gLtsE : ! gLts E A, ! gLtsEq E A, !Testing_Predicate E A outcome}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE} 
  `{@Prop_of_Inter Q E A parallel_inter H gLtsQ gLtsE}

  (p : P) (q : Q) 
  := forall (e : E), p must_pass e -> q must_pass e.

Global Hint Unfold ctx_pre: mdb.

Notation "p ⊑ₘᵤₛₜᵢ q" := (ctx_pre p q) (at level 70).


(********************************************* Properties on Must_i **********************************************)

Lemma must_eq_client `{
  gLtsP : gLts P A, 
  gLtsQ : ! gLts Q A, ! gLtsEq Q A, !Testing_Predicate Q A outcome}

  `{@Prop_of_Inter P Q A parallel_inter H gLtsP gLtsQ} :

  forall (p : P) (q r : Q), q ⋍ r -> p must_pass q -> p must_pass r.
Proof.
  intros p q r heq hm.
  revert r heq.
  dependent induction hm; intros.
  - apply m_now. eapply outcome_preserved_by_eq; eauto.
  - apply m_step; eauto with mdb.
    + intro rh. eapply nh. eapply outcome_preserved_by_eq; eauto with mdb.
      now symmetry.
    + destruct ex as (t & l).
      inversion l; subst.
      ++ exists (a2 ▷ r). eapply ParLeft; eauto.
      ++ symmetry in heq.
         assert (r ⟶⋍ b2) as (t & l3 & l4).
         { eapply eq_spec; eauto. }
         exists (p ▷ t). eapply ParRight; eauto.
      ++ symmetry in heq.
         assert (r ⟶⋍[μ2] b2) as (t & l3 & l4).
         { eapply eq_spec; eauto. }
         exists (a2 ▷ t). eapply ParSync; eauto.
    + intros r' l.
      assert (e ⟶⋍ r') as (t & l3 & l4).
      { eapply eq_spec; eauto. }
      eauto.
    + intros p' r' μ1 μ2 inter l__r l__p.
      assert (e ⟶⋍[μ2] r') as (e' & l__e' & eq').
      { eapply eq_spec; eauto. } eauto.
Qed.

Lemma must_eq_server `{
  gLtsP : gLts P A, 
  gLtsE : ! gLts E A, ! gLtsEq P A, ! gLtsEq E A, !Testing_Predicate E A outcome} 

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE} :

  forall (p q : P) (e : E), p ⋍ q -> p must_pass e -> q must_pass e.
Proof.
  intros p q e heq hm.
  revert q heq.
  dependent induction hm; intros.
  - now apply m_now.
  - apply m_step; eauto with mdb.
    + destruct ex as (t & l).
      inversion l; subst; eauto with mdb.
      ++ symmetry in heq.
         assert (q ⟶⋍ a2) as (t & l3 & l4).
         { eapply eq_spec; eauto. }
         exists (t ▷ e). eapply ParLeft; eauto.
      ++ exists (q ▷ b2). eapply ParRight; eauto.
      ++ symmetry in heq.
         assert (q ⟶⋍[μ1] a2) as (t & l3 & l4).
         { eapply eq_spec; eauto. }
         exists (t ▷ b2). eapply ParSync; eauto.
    + intros q' l.
      assert (p ⟶⋍ q') as (t & l3 & l4).
      { eapply eq_spec; eauto. } eauto.
    + intros q' e' μ1 μ2 inter l__e l__q.
      assert (p ⟶⋍[μ1] q') as (t & l3 & l4).
      { eapply eq_spec; eauto. } eauto.
Qed.

Lemma must_preserved_by_lts_tau_srv `{
  gLtsP : gLts P A, 
  gLtsE : ! gLts E A, ! gLtsEq E A, !Testing_Predicate E A outcome}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p1 p2 : P) (e : E) : 
  p1 must_pass e -> p1 ⟶ p2 -> p2 must_pass e.
Proof. by inversion 1; eauto with mdb. Qed.

Lemma must_preserved_by_weak_nil_srv `{
  gLtsP : gLts P A, 
  gLtsE : ! gLts E A, ! gLtsEq E A, !Testing_Predicate E A outcome}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p q : P) (e : E) : 
  p must_pass e -> p ⟹ q 
    -> q must_pass e.
Proof.
  intros hm w.
  dependent induction w; eauto with mdb.
  eapply IHw; eauto.
  eapply must_preserved_by_lts_tau_srv; eauto.
Qed.

Lemma must_preserved_by_lts_tau_clt `{
  gLtsP : gLts P A, 
  gLtsE : ! gLts E A, ! gLtsEq E A, !Testing_Predicate E A outcome}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p : P) (e1 e2 : E) : 
  p must_pass e1 -> ¬ outcome e1 -> e1 ⟶ e2 -> p must_pass e2.
Proof. by inversion 1; eauto with mdb. Qed.

Lemma must_preserved_by_synch_if_notoutcome `{
  gLtsP : gLts P A, 
  gLtsE : ! gLts E A, ! gLtsEq E A, !Testing_Predicate E A outcome}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p p' : P) (r r' : E) μ μ':
  p must_pass r -> ¬ outcome r -> parallel_inter μ μ' -> p ⟶[μ] p' -> r ⟶[μ'] r' 
    -> p' must_pass r'.
Proof.
  intros hm u inter l__p l__r.
  inversion hm; subst.
  - contradiction.
  - eapply com; eauto with mdb.
Qed.

Lemma must_preserved_by_lts_tau_clt_rev `{
  gLtsP : gLts P A, 
  gLtsE : ! gLts E A, ! gLtsEq E A, !Testing_Predicate E A outcome}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p : P) (e1 e2 : E) : 
  p must_pass e2 -> e1 ⟶ e2 -> ¬ outcome e2 -> (forall μ, e1 ↛[μ]) -> (forall e', e1 ⟶ e' -> e' ⋍ e2)
    -> p must_pass e1.
Proof.
  intros must_hyp hyp_tr not_happy not_ext_action tau_determinacy.
  revert e1 hyp_tr not_happy not_ext_action tau_determinacy.
  dependent induction must_hyp.
  - intros. contradiction.
  - intros. destruct (decide (outcome e1)) as [happy' | not_happy'].
    + now eapply m_now.
    + eapply m_step; eauto.
      ++ exists (p ▷ e). eapply ParRight; eauto.
      ++ intros. assert (e ⋍ e'). { symmetry; eauto. }
         eapply must_eq_client; eauto. eauto.
         eapply m_step; eauto.
      ++ intros p' e' μ1 μ2 inter tr_server tr_client. 
         assert (e1 ↛[μ2]); eauto.
         assert (¬ e1 ↛[μ2]). eapply lts_refuses_spec2; eauto. contradiction.
Qed.

Lemma must_preserved_by_lts_tau_clt_rev_rev `{
  gLtsP : gLts P A, 
  gLtsE : ! gLts E A, ! gLtsEq E A, !Testing_Predicate E A outcome}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p : P) (e1 e2 : E) : 
  p must_pass e2 -> e1 ⟶ e2 -> (forall μ, e1 ↛[μ]) -> (forall e', e1 ⟶ e' -> outcome e') -> p ⤓
    -> p must_pass e1.
Proof.
  intros must_hyp hyp_tr not_ext_action happy_determinacy conv.
  revert e1 e2 must_hyp hyp_tr not_ext_action happy_determinacy.
  dependent induction conv.
  - intros. destruct (decide (outcome e1)) as [happy | not_happy].
    + now eapply m_now.
    + eapply m_step; eauto.
      ++ exists (p ▷ e2). eapply ParRight; eauto.
      ++ intros. assert (must p e2).
      { eapply m_now; eauto. }
      assert (must p' e2).
      { eapply must_preserved_by_lts_tau_srv; eauto. }
      assert (p' ⤓); eauto.
      ++ intros. assert (outcome e'); eauto. now eapply m_now.
      ++ intros. assert (e1 ↛[μ2]); eauto.
         assert (¬ e1 ↛[μ2]). eapply lts_refuses_spec2; eauto. contradiction.
Qed.

Lemma must_terminate_unoutcome `{
  gLtsP : gLts P A, 
  gLtsT : ! gLts T A, ! gLtsEq T A, !Testing_Predicate T A outcome}

  `{@Prop_of_Inter P T A parallel_inter H gLtsP gLtsT}

  (p : P) (e : T) : p must_pass e -> ¬ outcome e -> p ⤓.
Proof.
  intros hm. dependent induction hm.
  + contradiction.
  + eauto with mdb.
Qed.

Lemma must_terminate_unoutcome' `{
  gLtsP : gLts P A, 
  gLtsT : ! gLts T A, ! gLtsEq T A, !Testing_Predicate T A outcome}

  `{@Prop_of_Inter P T A parallel_inter H gLtsP gLtsT}

  (p : P) (e : T) : p must_pass e -> outcome e \/ p ⤓.
Proof. 
  intros hm. destruct (decide (outcome e)) as [happy | not_happy].
  + now left. 
  + right. eapply must_terminate_unoutcome; eauto.
Qed.

Lemma must_preserved_by_lts_wk_clt `{
  gLtsP : gLts P A, 
  gLtsE : ! gLts E A, ! gLtsEq E A, !Testing_Predicate E A outcome}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p : P) (e1 e2 : E) : 
  p must_pass e1 -> ¬ outcome e1 -> (∀ e', e1 ⟹ e' -> e' ≠ e2 -> ¬ outcome e') -> e1 ⟹ e2 -> p must_pass e2.
Proof.
  intros Hyp not_happy Hyp_not_happy wk_tr.
  remember e2.
  dependent induction wk_tr. 
  + subst. eauto.
  + subst. assert (∀ e' : E, q ⟹ e' → e' ≠ e2 → ¬ outcome e') as Hyp_final.
    {intros. eapply Hyp_not_happy. econstructor; eauto. eauto. }
    assert (must p q).
    {eapply must_preserved_by_lts_tau_clt; eauto. }
    destruct (decide (q = e2)) as [ eq | not_eq].
    ++ subst. eauto.
    ++ eapply IHwk_tr; eauto. eapply Hyp_not_happy; eauto with mdb.
Qed.

Lemma must_preserved_by_wt_synch_if_notoutcome `{
  gLtsP : gLts P A, 
  gLtsE : !gLts E A, ! gLtsEq E A, !Testing_Predicate E A outcome}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p p' : P) (r r' : E) (μ : A) (μ' : A):
  p must_pass r 
    -> ¬ outcome r 
      -> parallel_inter μ μ'
        -> p ⟹{μ} p' 
          -> r ⟶[μ'] r' 
            -> p' must_pass r'.
Proof.
  intros hm u duo hwp hwr.
  dependent induction hwp.
  - eapply IHhwp; eauto. eapply must_preserved_by_lts_tau_srv; eauto.
  - eapply must_preserved_by_weak_nil_srv; eauto.
    inversion hm. contradiction. eapply com.
    eassumption. eassumption. eassumption.
Qed.

Lemma ctx_pre_not `{
  gLtsP : gLts P A, 
  gLtsQ : !gLts Q A, 
  gLtsE : ! gLts E A, ! gLtsEq E A, !Testing_Predicate E A outcome}
  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE} 
  `{@Prop_of_Inter Q E A parallel_inter H gLtsQ gLtsE}
  (p : P) (q : Q) (e : E) :
  p ⊑ₘᵤₛₜᵢ q -> ¬ q must_pass e -> ¬ p must_pass e.
Proof.
  intros hpre not_must.
  intro Hyp. eapply hpre in Hyp.
  contradiction.
Qed.
