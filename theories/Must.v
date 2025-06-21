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

Require ssreflect.
Require Import Coq.Unicode.Utf8.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Program.Equality.
Require Import Coq.Wellfounded.Inverse_Image.
Require Import Coq.Logic.JMeq.
Require Import Coq.Program.Wf Setoid.
Require Import Coq.Program.Equality.
From Coq.Logic Require Import ProofIrrelevance.
From stdpp Require Import base countable finite gmap list finite base decidable finite gmap.
From Must Require Import TransitionSystems Subset_Act.

Class Good (P A : Type) (good : P -> Prop) `{Lts P A, !LtsEq P A} := {
    good_decidable e : Decision (good e);
    good_preserved_by_eq (p : P) q : good p -> p ⋍ q -> good q;
    good_preserved_by_lts_non_blocking_action p q η : non_blocking η -> p ⟶[η] q -> good p -> good q;
    good_preserved_by_lts_non_blocking_action_converse p q η : non_blocking η -> p ⟶[η] q -> good q -> good p;
}.


#[global] Instance good_dec `{Good P A good} e : Decision (good e).
Proof. eapply good_decidable. Defined.

Lemma ungood_preserved_by_lts_non_blocking_action `{LtsOba P A, !Good P A good} p q η :
  non_blocking η -> p ⟶[η] q -> ~ good p -> ~ good q.
Proof.
  intros nb l1 hp hq.
  eapply hp. eapply good_preserved_by_lts_non_blocking_action_converse; eauto with mdb.
Qed.

Lemma ungood_preserved_by_eq `{LtsOba P A, !Good P A good} p q :
  ~ good p -> q ⋍ p -> ~ good q.
Proof.
  intros not_happy eq. intro happy.
  eapply good_preserved_by_eq in happy; eauto with mdb.
Qed.

Lemma ungood_preserved_by_wt_non_blocking_action 
  `{LtsOba P A, !Good P A good} 
  r1 r2 s :
  Forall non_blocking s -> r1 ↛ -> ~ good r1 -> r1 ⟹[s] r2 -> ~ good r2.
Proof.
  intros s_spec hst hng hw.
  induction hw; eauto.
  - eapply lts_stable_spec2 in hst. now exfalso. eauto.
  - inversion s_spec; subst.
    inversion s_spec; subst.
    eapply IHhw. eassumption.
    eapply stable_tau_preserved_by_lts_non_blocking_action; eauto.
    eapply ungood_preserved_by_lts_non_blocking_action; eauto.
Qed.

Inductive must_sts 
  `{Sts (P1 * P2), good : P2 -> Prop}
  (p : P1) (e : P2) : Prop :=
| m_sts_now : good e -> must_sts p e
| m_sts_step
    (nh : ¬ good e)
    (nst : ¬ sts_stable (p, e))
    (l : forall p' e', sts_step (p, e) (p', e') -> must_sts p' e')
  : must_sts p e
.

Global Hint Constructors must_sts:mdb.

Inductive must `{
    LtsP : @Lts P A H, 
    LtsE : ! Lts E A, ! LtsEq E A, !Good E A good} 
    
    `{@Prop_of_Inter P E A parallel_inter H LtsP LtsE}
    
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
  LtsP : @Lts P A H, 
  LtsE : !Lts E A, !LtsEq E A, !Good E A good}

  `{@Prop_of_Inter P E A parallel_inter H LtsP LtsE}

  (p : P) (e : E) :
  @must_sts P E _ good p e <-> must p e.
Proof.
  split.
  - intro hm. dependent induction hm; eauto with mdb.
    eapply m_step; eauto with mdb.
    + eapply sts_stable_spec1 in nst as ((p', e') & hl).
      exists (p', e'). now simpl in hl.
    + simpl in *; eauto with mdb.
    + simpl in *; eauto with mdb.
    + intros p' e' μ1 μ2 duo hl1 hl2.
      eapply H1. simpl.
      eapply (ParSync μ1 μ2); eauto.
  - intro hm. dependent induction hm; eauto with mdb.
    eapply m_sts_step; eauto with mdb.
    + eapply sts_stable_spec2.
      destruct (decide (sts_stable (p, e))).
      ++ exfalso.
         destruct ex as ((p', e'), hl).
         eapply sts_stable_spec2 in s; eauto.
         exists (p', e'). now simpl.
      ++ now eapply sts_stable_spec1 in n.
    + intros p' e' hl.
      inversion hl; subst; eauto with mdb.
Qed.

Definition ctx_pre `{
  LtsP : Lts P A, 
  LtsQ : !Lts Q A, 
  LtsE : ! Lts E A, ! LtsEq E A, !Good E A good}

  `{@Prop_of_Inter P E A parallel_inter H LtsP LtsE} 
  `{@Prop_of_Inter Q E A parallel_inter H LtsQ LtsE}

  (p : P) (q : Q) 
  := forall (e : E), must p e -> must q e.

Global Hint Unfold ctx_pre: mdb.

Notation "p ⊑ q" := (ctx_pre p q) (at level 70).

Definition bhv_pre_cond1 `{Lts P A, Lts Q A} 
  (p : P) (q : Q) := forall s, p ⇓ s -> q ⇓ s.

Notation "p ≼₁ q" := (bhv_pre_cond1 p q) (at level 70).

Definition bhv_pre_cond2 `{
  @Lts P A H, 
  @Lts Q A H}
  
  (p : P) (q : Q) :=
  forall s q',
    p ⇓ s -> q ⟹[s] q' -> q' ↛ ->
    ∃ p', p ⟹[s] p' /\ p' ↛ /\ (lts_pre_acc_set_of p' ⊆ lts_pre_acc_set_of q'). 

Notation "p ≼₂ q" := (bhv_pre_cond2 p q) (at level 70). 

Definition bhv_pre `{@Lts P A H, @Lts Q A H} (p : P) (q : Q) := 
      p ≼₁ q /\ p ≼₂ q.

Notation "p ≼ q" := (bhv_pre p q) (at level 70).

Lemma must_eq_client `{
  LtsP : Lts P A, 
  LtsQ : ! Lts Q A, ! LtsEq Q A, !Good Q A good}
  
  `{@Prop_of_Inter P Q A parallel_inter H LtsP LtsQ} :
  
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
  LtsP : Lts P A, 
  LtsE : ! Lts E A, ! LtsEq P A, ! LtsEq E A, !Good E A good} 

  `{@Prop_of_Inter P E A parallel_inter H LtsP LtsE} :

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
  LtsP : Lts P A, 
  LtsE : ! Lts E A, ! LtsEq E A, !Good E A good}

  `{@Prop_of_Inter P E A parallel_inter H LtsP LtsE}

  (p1 p2 : P) (e : E) : 
  must p1 e -> p1 ⟶ p2 -> must p2 e.
Proof. by inversion 1; eauto with mdb. Qed.

Lemma must_preserved_by_lts_tau_clt `{
  LtsP : Lts P A, 
  LtsE : ! Lts E A, ! LtsEq E A, !Good E A good}
  
  `{@Prop_of_Inter P E A parallel_inter H LtsP LtsE}
  
  (p : P) (e1 e2 : E) : 
  must p e1 -> ¬ good e1 -> e1 ⟶ e2 -> must p e2.
Proof. by inversion 1; eauto with mdb. Qed.

Lemma must_terminate_ungood `{
  LtsP : Lts P A, 
  LtsE : ! Lts E A, ! LtsEq E A, !Good E A good}
  
  `{@Prop_of_Inter P E A parallel_inter H LtsP LtsE}
  
  (p : P) (e : E) : must p e -> ¬ good e -> p ⤓.
Proof. intros hm. dependent induction hm; eauto with mdb. contradiction. Qed.

Lemma must_mu_either_good_cnv `{
  LtsP : Lts P A, 
  LtsE : ! Lts E A, ! LtsEq E A, !Good E A good}
  
  `{@Prop_of_Inter P E A parallel_inter H LtsP LtsE}
  (p : P) (e e': E)  : 
  must p e 
    -> forall μ μ',
      parallel_inter μ μ'
        -> e ⟶[μ'] e' 
          -> ¬ good e -> ¬ good e'
             -> p ⇓ [μ].
Proof.
  intros hmx μ μ' inter l not_happy not_happy'.
  dependent induction hmx.
  + contradiction.
  + eapply cnv_act; eauto. 
    ++ eapply tstep. intros p'' tr.
       eapply must_terminate_ungood; eauto.
    ++ intros p'' tr.
       admit.
Admitted.

(** Must sets. *)

Section must_sets.

  (* https://arxiv.org/pdf/1612.03191.pdf *)

  Local Open Scope positive.

  Definition MUST `{Lts P A} 
    (p : P) (G : gset A) :=
    forall p', p ⟹ p' -> exists μ p0, μ ∈ G /\ p' ⟹{μ} p0.

  Definition MUST__s `{FiniteImageLts P A} 
    (ps : gset P) (G : gset A) := 
    forall p, p ∈ ps -> MUST p G.

  (* Residuals of a process p AFTER the execution of s. *)

  Definition AFTER `{FiniteImageLts P A} 
    (p : P) (s : trace A) (hcnv : p ⇓ s) := 
    wt_set p s hcnv. 

  Definition bhv_pre_ms_cond2 `{@FiniteImageLts P A H LtsP, @FiniteImageLts Q A H LtsQ} 
    (p : P) (q : Q) :=
    forall s h1 h2 G, MUST__s (AFTER p s h1) G -> MUST__s (AFTER q s h2) G.

  Definition bhv_pre_ms `{@FiniteImageLts P A H LtsP, @FiniteImageLts Q A H LtsQ} 
    (p : P) (q : Q) :=
    p ≼₁ q /\ bhv_pre_ms_cond2 p q.
End must_sets.

Global Hint Unfold bhv_pre_ms:mdb. 

Notation "p ≾₂ q" := (bhv_pre_ms_cond2 p q) (at level 70).

Notation "p ≾ q" := (bhv_pre_ms p q) (at level 70).

Section failure.

(* Meme ExtAction ? *)

  Definition Failure `{FiniteImageLts P A} 
    (p : P) (s : trace A) (G : gset A) :=
    p ⇓ s -> exists p', p ⟹[s] p' /\ forall μ, μ ∈ G -> ¬ exists p0, p' ⟹{μ} p0.

  Definition fail_pre_ms_cond2 `{@FiniteImageLts P A HA LtsP, @FiniteImageLts Q A HA LtsQ} 
    (p : P) (q : Q) :=
    forall s G, Failure q s G -> Failure p s G.

  Definition fail_pre_ms `{@FiniteImageLts P A HA LtsP, @FiniteImageLts Q A HA LtsQ} 
    (p : P) (q : Q) :=
    p ≼₁ q /\ fail_pre_ms_cond2 p q.

End failure.

Notation "p ⋖ q" := (fail_pre_ms p q) (at level 70).
