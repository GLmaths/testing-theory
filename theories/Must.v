(*
   Copyright (c) 2024 Gaëtan Lopez <glopez@irif.fr>

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
From stdpp Require Import base countable finite gmap list finite base decidable finite gmap.
From Must Require Import TransitionSystems Subset_Act.

Class Good (P A : Type) (good : P -> Prop) `{gLts P A, !gLtsEq P A} := {
    good_decidable e : Decision (good e);
    good_preserved_by_eq (p : P) q : good p -> p ⋍ q -> good q;
    good_preserved_by_lts_non_blocking_action p q η : non_blocking η -> p ⟶[η] q -> good p -> good q;
    good_preserved_by_lts_non_blocking_action_converse p q η : non_blocking η -> p ⟶[η] q -> good q -> good p;
}.

#[global] Instance good_dec `{Good P A good} e : Decision (good e).
Proof. eapply good_decidable. Defined.

Lemma ungood_preserved_by_lts_non_blocking_action `{gLtsOba P A, !Good P A good} p q η :
  non_blocking η -> p ⟶[η] q -> ~ good p -> ~ good q.
Proof.
  intros nb l1 hp hq.
  eapply hp. eapply good_preserved_by_lts_non_blocking_action_converse; eauto with mdb.
Qed.

Lemma ungood_preserved_by_eq `{gLtsOba P A, !Good P A good} p q :
  ~ good p -> q ⋍ p -> ~ good q.
Proof.
  intros not_happy eq. intro happy.
  eapply good_preserved_by_eq in happy; eauto with mdb.
Qed.

Lemma ungood_preserved_by_wt_non_blocking_action 
  `{gLtsOba P A, !Good P A good} 
  r1 r2 s :
  Forall non_blocking s -> r1 ↛ -> ~ good r1 -> r1 ⟹[s] r2 -> ~ good r2.
Proof.
  intros s_spec hst hng hw.
  induction hw; eauto.
  - eapply lts_refuses_spec2 in hst. now exfalso. eauto.
  - inversion s_spec; subst.
    inversion s_spec; subst.
    eapply IHhw. eassumption.
    eapply refuses_tau_preserved_by_lts_non_blocking_action; eauto.
    eapply ungood_preserved_by_lts_non_blocking_action; eauto.
Qed.

Inductive must_sts 
  `{Sts (P1 * P2), good : P2 -> Prop}
  (p : P1) (e : P2) : Prop :=
| m_sts_now : good e -> must_sts p e
| m_sts_step
    (nh : ¬ good e)
    (nst : ¬ sts_refuses (p, e))
    (l : forall p' e', sts_step (p, e) (p', e') -> must_sts p' e')
  : must_sts p e
.

Global Hint Constructors must_sts:mdb.

Inductive must `{
    gLtsP : @gLts P A H, 
    gLtsE : ! gLts E A, ! gLtsEq E A, !Good E A good} 

    `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

    (p : P) (e : E) : Prop :=
| m_now : good e -> must p e
| m_step
    (nh : ¬ good e)
    (ex : ∃ t, inter_step (p, e) τ t)
    (pt : forall p', p ⟶ p' -> must p' e)
    (et : forall e', e ⟶ e' -> must p e')
    (com : forall p' e' μ1 μ2, parallel_inter μ1 μ2
      -> p ⟶[μ1] p' 
        -> e ⟶[μ2] e'  
          -> must p' e')
  : must p e
.

Global Hint Constructors must:mdb.

Lemma must_sts_iff_must `{
  gLtsP : @gLts P A H, 
  gLtsE : !gLts E A, !gLtsEq E A, !Good E A good}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p : P) (e : E) :
  @must_sts P E _ good p e <-> must p e.
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

Definition ctx_pre `{
  gLtsP : gLts P A, 
  gLtsQ : !gLts Q A, 
  gLtsE : ! gLts E A, ! gLtsEq E A, !Good E A good}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE} 
  `{@Prop_of_Inter Q E A parallel_inter H gLtsQ gLtsE}

  (p : P) (q : Q) 
  := forall (e : E), must p e -> must q e.

Global Hint Unfold ctx_pre: mdb.

Notation "p ⊑ q" := (ctx_pre p q) (at level 70).

Lemma ctx_pre_not `{
  gLtsP : gLts P A, 
  gLtsQ : !gLts Q A, 
  gLtsE : ! gLts E A, ! gLtsEq E A, !Good E A good}
  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE} 
  `{@Prop_of_Inter Q E A parallel_inter H gLtsQ gLtsE}
  (p : P) (q : Q) (e : E) :
  p ⊑ q -> ¬ must q e -> ¬ must p e.
Proof.
  intros hpre not_must.
  intro Hyp. eapply hpre in Hyp.
  contradiction.
Qed.

Definition bhv_pre_cond1 `{gLts P A, gLts Q A} 
  (p : P) (q : Q) := forall s, p ⇓ s -> q ⇓ s.

Notation "p ≼₁ q" := (bhv_pre_cond1 p q) (at level 70).

Definition bhv_pre_cond2 `{
  @gLts P A H, 
  @gLts Q A H}
  
  (p : P) (q : Q) :=
  forall s q',
    p ⇓ s -> q ⟹[s] q' -> q' ↛ ->
    ∃ p', p ⟹[s] p' /\ p' ↛ /\ (lts_acc_set_of p' ⊆ lts_acc_set_of q').

Notation "p ≼₂ q" := (bhv_pre_cond2 p q) (at level 70). 

Definition bhv_pre `{@gLts P A H, @gLts Q A H} (p : P) (q : Q) := 
      p ≼₁ q /\ p ≼₂ q.

Notation "p ≼ q" := (bhv_pre p q) (at level 70).

Lemma must_eq_client `{
  gLtsP : gLts P A, 
  gLtsQ : ! gLts Q A, ! gLtsEq Q A, !Good Q A good}

  `{@Prop_of_Inter P Q A parallel_inter H gLtsP gLtsQ} :

  forall (p : P) (q r : Q), q ⋍ r -> must p q -> must p r.
Proof.
  intros p q r heq hm.
  revert r heq.
  dependent induction hm; intros.
  - apply m_now. eapply good_preserved_by_eq; eauto.
  - apply m_step; eauto with mdb.
    + intro rh. eapply nh. eapply good_preserved_by_eq; eauto with mdb.
      now symmetry.
    + destruct ex as (t & l).
      inversion l; subst; eauto with mdb.
      ++ symmetry in heq.
         edestruct (eq_spec r b2 τ) as (t & l3 & l4); eauto with mdb.
      ++ symmetry in heq.
         edestruct (eq_spec r b2 (ActExt μ2) ) as (t & l3 & l4); eauto with mdb.
    + intros r' l.
      edestruct (eq_spec e r' τ) as (t & l3 & l4); eauto with mdb.
    + intros p' r' μ1 μ2 inter l__r l__p.
      edestruct (eq_spec e r' (ActExt μ2)) as (e' & l__e' & eq'); eauto with mdb.
Qed.

Lemma must_eq_server `{
  gLtsP : gLts P A, 
  gLtsE : ! gLts E A, ! gLtsEq P A, ! gLtsEq E A, !Good E A good} 

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE} :

  forall (p q : P) (e : E), p ⋍ q -> must p e -> must q e.
Proof.
  intros p q e heq hm.
  revert q heq.
  dependent induction hm; intros.
  - now apply m_now.
  - apply m_step; eauto with mdb.
    + destruct ex as (t & l).
      inversion l; subst; eauto with mdb.
      ++ symmetry in heq.
         edestruct (eq_spec q a2 τ) as (t & l3 & l4); eauto with mdb.
      ++ symmetry in heq.
         edestruct (eq_spec q a2 (ActExt μ1)) as (t & l3 & l4); eauto with mdb.
    + intros q' l.
      edestruct (eq_spec p q' τ) as (t & l3 & l4); eauto with mdb.
    + intros q' e' μ1 μ2 inter l__e l__q.
      edestruct (eq_spec p q' (ActExt (μ1))) as (p' & l' & heq'); eauto with mdb.
Qed.

Lemma must_preserved_by_lts_tau_srv `{
  gLtsP : gLts P A, 
  gLtsE : ! gLts E A, ! gLtsEq E A, !Good E A good}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p1 p2 : P) (e : E) : 
  must p1 e -> p1 ⟶ p2 -> must p2 e.
Proof. by inversion 1; eauto with mdb. Qed.

Lemma must_preserved_by_lts_tau_clt `{
  gLtsP : gLts P A, 
  gLtsE : ! gLts E A, ! gLtsEq E A, !Good E A good}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p : P) (e1 e2 : E) : 
  must p e1 -> ¬ good e1 -> e1 ⟶ e2 -> must p e2.
Proof. by inversion 1; eauto with mdb. Qed.

Lemma must_terminate_ungood `{
  gLtsP : gLts P A, 
  gLtsE : ! gLts E A, ! gLtsEq E A, !Good E A good}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p : P) (e : E) : must p e -> ¬ good e -> p ⤓.
Proof. intros hm. dependent induction hm; eauto with mdb. contradiction. Qed.

Lemma must_terminate_ungood' `{
  gLtsP : gLts P A, 
  gLtsE : ! gLts E A, ! gLtsEq E A, !Good E A good}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p : P) (e : E) : must p e -> good e \/ p ⤓.
Proof. 
  intros hm. destruct (decide (good e)) as [happy | not_happy].
  + now left. 
  + right. eapply must_terminate_ungood; eauto.
Qed.

(** Must sets. *)

Section must_sets.

  (* https://arxiv.org/pdf/1612.03191.pdf *)

  Local Open Scope positive.

  Definition MUST `{gLts P A} 
    (p : P) (G : subset_of A) :=
    forall p', p ⟹ p' -> exists μ p0, μ ∈ G /\ p' ⟹{μ} p0.

  Definition MUST__s `{FiniteImagegLts P A} 
    (ps : gset P) (G : subset_of A) := 
    forall p, p ∈ ps -> MUST p G.

  (* Residuals of a process p AFTER the execution of s. *)

  Definition AFTER `{FiniteImagegLts P A} 
    (p : P) (s : trace A) (hcnv : p ⇓ s) := 
    wt_set p s hcnv. 

  Definition bhv_pre_ms_cond2 `{@FiniteImagegLts P A H gLtsP, @FiniteImagegLts Q A H gLtsQ} 
    (p : P) (q : Q) :=
    forall s h1 h2 G, MUST__s (AFTER p s h1) G -> MUST__s (AFTER q s h2) G.

  Definition bhv_pre_ms `{@FiniteImagegLts P A H gLtsP, @FiniteImagegLts Q A H gLtsQ} 
    (p : P) (q : Q) :=
    p ≼₁ q /\ bhv_pre_ms_cond2 p q.
End must_sets.

Global Hint Unfold bhv_pre_ms:mdb. 

Notation "p ≾₂ q" := (bhv_pre_ms_cond2 p q) (at level 70).

Notation "p ≾ q" := (bhv_pre_ms p q) (at level 70).

Section failure.

  Definition Failure `{FiniteImagegLts P A} 
    (p : P) (s : trace A) (G : subset_of A) :=
    p ⇓ s -> exists p', p ⟹[s] p' /\ forall μ, μ ∈ G -> ¬ exists p0, p' ⟹{μ} p0.

  Definition fail_pre_ms_cond2 `{@FiniteImagegLts P A H gLtsP, @FiniteImagegLts Q A H gLtsQ} 
    (p : P) (q : Q) :=
    forall s G, Failure q s G -> Failure p s G.

  Definition fail_pre_ms `{@FiniteImagegLts P A H gLtsP, @FiniteImagegLts Q A H gLtsQ} 
    (p : P) (q : Q) :=
    p ≼₁ q /\ fail_pre_ms_cond2 p q.

End failure.

Notation "p ⋖ q" := (fail_pre_ms p q) (at level 70).
