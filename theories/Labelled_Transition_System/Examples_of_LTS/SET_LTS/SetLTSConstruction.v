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
From Coq.Wellfounded Require Import Inverse_Image.
From Coq.Logic Require Import JMeq ProofIrrelevance.
From Coq.Program Require Import Wf Equality.
From stdpp Require Import base list countable decidable finite gmap gmultiset.
From Must Require Import MultisetHelper gLts FiniteImageLTS ActTau Bisimulation.
(* From Must Require Import MultisetHelper  Lts_OBA Lts_FW Lts_OBA_FB 
    InListPropHelper CodePurification InteractionBetweenLts MultisetLTSConstruction ActTau. *)

(**************************************** Forwarder LTS *************************************)


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

#[global] Program Instance SET_LTS `(gLtsP : @gLts P A H) `{!FiniteImagegLts P A} : @gLts (gset P) A H.
Next Obligation.
  intros. destruct X.
  + exact (H1 = lts_extaction_set_from_pset H0 μ /\ H1 ≠ ∅).
  + exact (H1 = lts_tau_set_from_pset H0 /\ H1 ≠ ∅).
Defined.
Next Obligation.
  intros; simpl in *. unfold SET_LTS_obligation_1.
  destruct α.
  - destruct (decide (b = lts_extaction_set_from_pset a μ /\ b ≠ ∅)).
    + left. eauto.
    + right. eauto.
  - destruct (decide (b = lts_tau_set_from_pset a /\ b ≠ ∅)).
    + left. eauto.
    + right. eauto.
Qed.
Next Obligation.
  intros. exact (forall p, p ∈ H0 -> lts_refuses p X).
Defined.
Next Obligation.
  intros. simpl in *. unfold SET_LTS_obligation_3.
  destruct α.
  - assert (forall p', p' ∈ p -> (¬ lts_refuses p' (ActExt μ) \/ lts_refuses p' (ActExt μ))) as Hyp.
    { intros. destruct (decide (p' ↛[μ])); [right|left];eauto. }
    (* destruct (exists_forall_in_gset p _ _ Hyp). *) admit.
  - assert (forall p', p' ∈ p -> (¬ lts_refuses p' τ \/ lts_refuses p' τ)) as Hyp.
    { intros. destruct (decide (p' ↛)); [right|left];eauto. }
    (* destruct (exists_forall_in_gset p _ _ Hyp). *) admit.
Admitted.
Next Obligation.
  unfold SET_LTS_obligation_3.
  unfold SET_LTS_obligation_1. intros. destruct α.
  - assert (forall p', p' ∈ p -> (¬ lts_refuses p' (ActExt μ) \/ lts_refuses p' (ActExt μ))) as Hyp.
    { intros. destruct (decide (p' ↛[μ])); [right|left];eauto. }
    exists (lts_extaction_set_from_pset p μ). split; eauto.
    destruct (exists_forall_in_gset p _ _ Hyp).
    + destruct H1 as (p' & Hyp' & Hyp'').
      intro. eapply lts_refuses_spec1 in Hyp'' as (p'' & Hyp''').
      assert (p'' ∈ lts_extaction_set_from_pset p μ).
      { destruct (lts_extaction_set_from_pset_ispec p μ). eauto. }
      rewrite H1 in H2. inversion H2.
    + contradiction.
  - assert (forall p', p' ∈ p -> (¬ lts_refuses p' τ \/ lts_refuses p' τ)) as Hyp.
    { intros. destruct (decide (p' ↛)); [right|left];eauto. }
    exists (lts_tau_set_from_pset p). split; eauto.
    destruct (exists_forall_in_gset p _ _ Hyp).
    + destruct H1 as (p' & Hyp' & Hyp'').
      intro. eapply lts_refuses_spec1 in Hyp'' as (p'' & Hyp''').
      assert (p'' ∈ lts_tau_set_from_pset p).
      { destruct (lts_tau_set_from_pset_ispec p). eauto. }
      rewrite H1 in H2. inversion H2.
    + contradiction.
Qed.
Next Obligation.
  unfold SET_LTS_obligation_3.
  unfold SET_LTS_obligation_1. intros.
  destruct α.
  - intro. destruct H0 as (p' & Hyp1 & Hyp2). subst.
    remember (lts_extaction_set_from_pset p μ).
    induction g using set_ind_L.
    + eapply Hyp2. reflexivity.
    + assert (x ∈ lts_extaction_set_from_pset p μ) as Hyp by set_solver.
      destruct (lts_extaction_set_from_pset_ispec p μ) as (Hyp'1 & Hyp'2).
      unfold lts_extaction_set_from_pset_spec1 in Hyp'1.
      unfold lts_extaction_set_from_pset_spec2 in Hyp'2.
      eapply Hyp'1 in Hyp as (p'0 & in_Set & Tr).
      eapply H1 in in_Set. eapply lts_refuses_spec2; eauto.
  - intro. destruct H0 as (p' & Hyp1 & Hyp2). subst.
    remember (lts_tau_set_from_pset p).
    induction g using set_ind_L.
    + eapply Hyp2. reflexivity.
    + assert (x ∈ lts_tau_set_from_pset p) as Hyp by set_solver.
      destruct (lts_tau_set_from_pset_ispec p) as (Hyp'1 & Hyp'2).
      unfold lts_tau_set_from_pset_spec1 in Hyp'1.
      unfold lts_tau_set_from_pset_spec2 in Hyp'2.
      eapply Hyp'1 in Hyp as (p'0 & in_Set & Tr).
      eapply H1 in in_Set. eapply lts_refuses_spec2 ; eauto.
Qed.

Definition set_eq `(gLtsEqP : @LtsEq P A H gLtsP) `{!FiniteImagegLts P A} (ps : gset P) (qs : gset P) :=
  (forall p', p' ∈ ps -> exists q', q' ∈ qs /\ p' ⋍ q') /\ (forall q', q' ∈ qs -> exists p', p' ∈ ps /\ p' ⋍ q').

Infix "⋍ₛₑₜ" := set_eq (at level 70).

#[global] Program Instance SET_LTS_eq `(gLtsP : @gLts P A H) `{!FiniteImagegLts P A} : @gLtsEq (gset P) A H (SET_LTS gLtsP) :=
  {| eq_rel := fw_eq |}.
Next Obligation.
  `{M : @gLtsObaFB P A H gLtsP gLtsEqP gLtsObaP}  
  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}
  : gLtsEq (gset P) A :=
  {| eq_rel := fw_eq |}.
Next Obligation. intros. split.
  + eapply fw_eq_refl.
  + eapply fw_eq_symm.
  + eapply fw_eq_trans.
Qed.
Next Obligation.
  intros ? ? ? ? ? ? ? ? (p, mp) (q, mq) α ((t, mt) & heq & hl).
  eapply lts_fw_eq_spec; eauto.
Qed.

#[global] Program Instance FW_gLtsOba
  `{M : @gLtsObaFB P A H gLtsP gLtsEqP gLtsObaP}  
  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}
  : gLtsOba (P * mb A) A :=
  {| lts_oba_mo p := lts_oba_mo p.1 ⊎ mb_without_not_nb p.2 |}.
Next Obligation.
  intros ? ? ? ? ? ? ? ? p1 η p2 nb Hstep; simpl in *.
  inversion Hstep; subst; simpl in *.
  + apply (lts_oba_mo_spec_bis1 a1 η a2) in nb; eauto. set_solver.
  + apply (non_blocking_action_in_ms b1 η b2) in nb as eq ; subst;  eauto. 
    assert (η ∈ mb_without_not_nb ({[+ η +]} ⊎ b2)).
    eapply lts_mb_nb_with_nb_spec2; eauto; try multiset_solver.
    set_solver.
Qed.
Next Obligation.
  intros ? ? ? ? ? ? ? ? (p , mem) η mem_non_blocking; simpl in *.
  rewrite gmultiset_elem_of_disj_union in mem_non_blocking. 
  destruct (decide (η ∈ lts_oba_mo p)) as [non_blocking_in_p | non_blocking_not_in_p].
  + eapply lts_oba_mo_spec_bis2 in non_blocking_in_p as (p' & nb & Hstep).
    exists (p', mem). split.
    ++ exact nb.
    ++ eauto with mdb.
  + destruct (decide (η ∈ mb_without_not_nb mem)) as [non_blocking_in_mem | non_blocking_not_in_mem].
    eapply lts_mb_nb_with_nb_spec1 in non_blocking_in_mem as (nb & mem').
    * exists (p , mem ∖ {[+ η +]}). split.
      ++ exact nb.
      ++ eapply ParRight. assert (mem = {[+ η +]} ⊎ mem ∖ {[+ η +]}) as eq. multiset_solver.
         rewrite eq at 1. eapply lts_multiset_minus. exact nb. 
    * exfalso. destruct mem_non_blocking; contradiction.
Qed.
Next Obligation.
  intros ? ? ? ? ? ? ? ? ? ? ? nb Hstep ; simpl in *.
  inversion Hstep; subst; simpl in *.
  - apply (lts_oba_mo_spec2 a1 η a2) in nb; eauto. multiset_solver.
  - apply (non_blocking_action_in_ms b1 η b2) in nb as eq; eauto; subst.
    rewrite gmultiset_disj_union_assoc. 
    assert ({[+ η +]} ⊎ lts_oba_mo a ⊎ mb_without_not_nb b2 = 
    lts_oba_mo a ⊎ ({[+ η +]} ⊎ mb_without_not_nb b2)) as eq. multiset_solver.
    rewrite eq.
    erewrite gmultiset_eq_pop_l; eauto.
    eapply lts_mb_nb_spec1;eauto.
Qed.
Next Obligation.
intros ? ? ? ? ? ? ? ? ? ? ? ? ? nb Hstep_nb Hstep. destruct p as (p, mp), q as (q, mq), r as (r, mr).
  inversion Hstep_nb (* as [a b c d e f| a b c d e f| a b c d e f] *) ; inversion Hstep; subst.
  - destruct (lts_oba_non_blocking_action_delay nb l l0) as (t & hlt0 & (r0 & hlr0 & heqr0)).
    exists (t, mr). split; simpl in *. eauto with mdb.
    exists (r0, mr). split. simpl in *. eauto with mdb.
    now eapply fw_eq_id_mb.
  - exists (p, mr). split; simpl in *. eauto with mdb.
    exists (r, mr). split. simpl in *. eauto with mdb. reflexivity.
  - destruct (lts_oba_non_blocking_action_delay nb l l1) as (t & hlt0 & (r0 & hlr0 & heqr0)).
    exists (t, mr). split. simpl in *. eauto with mdb.
    exists (r0, mr). split. simpl in *. eauto with mdb.
    now eapply fw_eq_id_mb.
  - apply (non_blocking_action_in_ms mp η mr) in nb as eq; subst; eauto.
    exists (r, {[+ η +]} ⊎ mr).
    split. simpl in *. eauto with mdb.
    exists (r, mr). split. simpl in *. eauto with mdb. reflexivity.
  - destruct α as [μ |]. 
    + apply (non_blocking_action_in_ms mp η mq) in nb as eq; subst; eauto.
      destruct ((decide (non_blocking μ))) as [nb' | not_nb'].
      ++ apply (non_blocking_action_in_ms mq μ mr) in nb' as eq; subst; eauto.
         replace ({[+ η +]} ⊎ ({[+ μ +]} ⊎ mr))
         with ({[+ μ +]} ⊎ ({[+ η +]} ⊎ mr)) by multiset_solver.
         exists (r, {[+ η +]} ⊎ mr). split.
         * eapply ParRight. eapply lts_multiset_minus. exact nb'.
         * exists (r, mr). split. eapply ParRight. eapply lts_multiset_minus. exact nb. reflexivity.
      ++ apply (blocking_action_in_ms mq μ mr) in not_nb' as (eq & duo & nb'); subst; eauto.
         exists (r, {[+ co μ +]} ⊎ ({[+ η +]} ⊎ mq)).
         split.
         * eapply ParRight. eapply lts_multiset_add; eauto.
         * replace ({[+ co μ +]} ⊎ ({[+ η +]} ⊎ mq))
           with ({[+ η +]} ⊎ ({[+ co μ +]} ⊎ mq)) by multiset_solver.
           exists (r ▷ {[+ co μ +]} ⊎ mq). split. eapply ParRight. eapply lts_multiset_minus. exact nb. reflexivity.
    + inversion l0.
  - destruct eq as (duo & nb').
    apply (non_blocking_action_in_ms mp η mq) in nb as eq_mem; subst; eauto.
    apply (non_blocking_action_in_ms mq μ2 mr) in nb' as eq_mem; subst; eauto.
    replace ({[+ η +]} ⊎ ({[+ μ2 +]} ⊎ mr))
    with ({[+ μ2 +]} ⊎ ({[+ η +]} ⊎ mr)) by multiset_solver.
    exists (r, ({[+ η +]} ⊎ mr)). split. eapply (ParSync μ1 μ2); eauto.
    + split; eauto.
    + apply lts_multiset_minus. exact nb'.
    + exists (r ▷ mr). split. eapply ParRight. apply lts_multiset_minus; exact nb. reflexivity.
Qed.
Next Obligation.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? nb not_eq Hstep_nb Hstep. 
  destruct p as (p, mp), q1 as (q, mq), q2 as (r, mr).
  inversion Hstep_nb; subst.
  - inversion Hstep; subst.
    + edestruct (lts_oba_non_blocking_action_confluence nb not_eq l l0) as (t & hlt0 & (r0 & hlr0 & heqr0)).
      exists (t, mr). split; simpl in *. eauto with mdb.
      exists (r0, mr). split. simpl in *. eauto with mdb.
      now eapply fw_eq_id_mb.
    + exists (q, mr). split. simpl in *. eauto with mdb.
      exists (q, mr). split. simpl in *. eauto with mdb. reflexivity.
  - inversion Hstep; subst.
    + exists (r, mq). split; simpl in *. eauto with mdb.
      exists (r, mq). split. simpl in *. eauto with mdb. reflexivity.
    + eapply (non_blocking_action_in_ms mp η mq) in nb as eq; eauto ; subst.
      destruct (decide (non_blocking μ)) as [nb' | not_nb'].
      * eapply (non_blocking_action_in_ms ({[+ η +]} ⊎ mq) μ mr) in nb' as eq; eauto ; subst.
        assert (neq : η ≠ μ) by naive_solver.
        assert (μ ∈ mq) as mem. multiset_solver.
        assert (μ ∈ {[+ η +]} ⊎ mq) as mem'. multiset_solver.
        eapply gmultiset_disj_union_difference' in mem. rewrite mem.
        exists (r, mq ∖ {[+ μ +]}). split.
        ++ eapply ParRight. eapply lts_multiset_minus; eauto.
        ++ assert (η ∈ mr) as mem''. multiset_solver. 
           assert (mr = {[+ η +]} ⊎ (mq ∖ {[+ μ +]})) as mem'''. multiset_solver.
           rewrite mem'''. exists (r ▷ mq ∖ {[+ μ +]}). split. 
           eapply ParRight. eapply lts_multiset_minus; eauto. reflexivity.
      * eapply (blocking_action_in_ms ({[+ η +]} ⊎ mq) μ mr) in not_nb' as (eq & duo & nb'); eauto ; subst.
        exists (r ▷ {[+ co μ +]} ⊎ mq). split.
        ++ eapply ParRight. eapply lts_multiset_add; eauto.
        ++ assert ({[+ co μ +]} ⊎ ({[+ η +]} ⊎ mq) = {[+ η +]} ⊎ ({[+ co μ +]} ⊎ mq)) as eq. multiset_solver.
           rewrite eq. exists (r ▷ {[+ co μ +]} ⊎ mq). split. 
           eapply ParRight. eapply lts_multiset_minus; eauto. reflexivity.
Qed.
Next Obligation.
Proof.
  intros ? ? ? ? ? ? ? ? (p1, m1) (p2, m2) (p3, m3) η nb Hstep_nb Hstep.
  inversion Hstep_nb ;subst.
  - inversion Hstep ; subst.
    + edestruct (lts_oba_non_blocking_action_tau nb l l0) as
        [(t & hl1 & (t0 & hl0 & heq0)) | (μ & duo & t0 & hl0 & heq0)].
      left. exists (t, m3).
      split. simpl. eauto with mdb.
      exists (t0, m3). split. simpl. eauto with mdb.
      now eapply fw_eq_id_mb.
      right. exists μ. split.  exact duo. exists (t0, m3). split. simpl. eauto with mdb.
      now eapply fw_eq_id_mb.
    + inversion l0.
    + destruct eq as (duo' & nb').
      assert (blocking μ1). eapply dual_blocks; eauto.
      assert (neq : μ1 ≠ η). intro. subst. contradiction. 
      edestruct (lts_oba_non_blocking_action_confluence nb neq l l1)
        as (t & hl1 & (t1 & hl2 & heq1)).
      left. exists (t, m3). split. eapply ParSync; eauto. split; eauto.
      exists (t1, m3). split. simpl. eauto with mdb.
      now eapply fw_eq_id_mb.
  - eapply (non_blocking_action_in_ms m1 η m2) in nb as eq; subst; eauto. 
    inversion Hstep ; subst.
    + left. exists (p3, m2).
      split. simpl. eauto with mdb.
      exists (p3, m2). split. eapply ParRight; eassumption. reflexivity.
    + inversion l0.
    + destruct eq as (duo & nb').
      eapply (non_blocking_action_in_ms ({[+ η +]} ⊎ m2) μ2 m3) in nb' as eq'; subst; eauto. 
      destruct (decide (μ2 = η)) as [eq | not_eq]; subst.
      ++ right. assert (m2 = m3) as eq_mem. multiset_solver. rewrite <-eq_mem in l2.  
         exists μ1. split; eauto. exists (p3, m2). split. simpl. eauto with mdb. rewrite eq_mem. reflexivity.
      ++ left. eapply (non_blocking_action_in_ms ({[+ η +]} ⊎ m2) μ2 m3) in nb' as eq; subst; eauto.
         assert (η ∈ m3). multiset_solver.
         assert (η ∈ {[+ μ2 +]} ⊎ m3). multiset_solver.
         assert (μ2 ∈ m2). multiset_solver.
         assert (μ2 ∈ {[+ η +]} ⊎ m2). multiset_solver.
         exists (p3, m2 ∖ {[+ μ2 +]}). split. eapply (ParSync μ1 μ2); eauto.
         split; eauto. assert (m2 = {[+ μ2 +]} ⊎ (m2 ∖ {[+ μ2 +]})) as eq_mem. multiset_solver.
         rewrite eq_mem at 1. eapply lts_multiset_minus; eauto.
         assert (m3 = ({[+ η +]} ⊎ (m2 ∖ {[+ μ2 +]}))) as eq_mem'. multiset_solver.
         rewrite eq_mem'. exists (p3 ▷ m2 ∖ {[+ μ2 +]}). split.
         eapply ParRight. eapply lts_multiset_minus; eauto. reflexivity.
Qed.
Next Obligation.
  intros ? ? ? ? ? ? ? ? (p1, m1) (p2, m2) (p3, m3) η nb Hstep_nb Hstep_nb'.
  intros p2' p3' hwp2 hwp3; simpl in *.
  inversion Hstep_nb ; subst.
  - inversion Hstep_nb' ; subst.
    + eapply fw_eq_id_mb; eauto.
      eapply lts_oba_non_blocking_action_deter; eauto.
    + eapply (non_blocking_action_in_ms m2 η m3) in nb as eq; subst; eauto.
      set (he1 := lts_oba_mo_spec2 _ _ _ nb l).
      rewrite he1 in hwp3.
      eapply strip_eq_step in hwp3 as (p0 & hw0 & heq0); eauto. split.
      etrans. eapply strip_m_deter; eauto. eassumption.
      assert (mb_without_not_nb ({[+ η +]} ⊎ m3) = {[+ η +]} ⊎ mb_without_not_nb m3) as eq.
      eapply lts_mb_nb_spec1;eauto. rewrite eq.
      rewrite he1.
      rewrite gmultiset_disj_union_comm at 1.
      rewrite <- 2 gmultiset_disj_union_assoc.
      eapply gmultiset_eq_pop_l. multiset_solver.
  - inversion Hstep_nb' ; subst.
    + eapply (non_blocking_action_in_ms m3 η m2) in nb as eq; subst; eauto.
      set (he1 := lts_oba_mo_spec2 _ _ _ nb l0).
      rewrite he1 in hwp2.
      eapply strip_eq_step in hwp2 as (p0 & hw0 & heq0); eauto. split.
      etrans. symmetry. eassumption.
      eapply strip_m_deter; eauto.
      assert (mb_without_not_nb ({[+ η +]} ⊎ m2) = {[+ η +]} ⊎ mb_without_not_nb m2) as eq.
      eapply lts_mb_nb_spec1;eauto. rewrite eq.
      symmetry. rewrite he1.
      rewrite gmultiset_disj_union_comm at 1.
      rewrite <- 2 gmultiset_disj_union_assoc.
      eapply gmultiset_eq_pop_l. multiset_solver.
    + eapply (non_blocking_action_in_ms m1 η m2) in nb as eq; subst; eauto.
      eapply (non_blocking_action_in_ms ({[+ η +]} ⊎ m2) η m3) in nb as eq; subst; eauto.
      assert (m3 = m2) by multiset_solver; subst.
      split.  eapply strip_m_deter; eauto. multiset_solver.
Qed.
Next Obligation.
  intros ? ? ? ? ? ? ? ? (p1, mp1) (p2, mp2) (q1, mq1) (q2, mq2) η nb Hstep_nb Hstep_nb' equiv.
  inversion Hstep_nb; subst;  intros p1' p2' hwp1 hwp2; simpl in *.
  - eapply lts_oba_mo_spec2 in l as hd1; eauto.
    edestruct (lts_oba_mo_strip q1) as (q1' & hwq1).
    inversion Hstep_nb'; subst.
    + edestruct (lts_oba_mo_strip q2) as (q2' & hwq2).
      edestruct (equiv q1' q2'); eauto; simpl in *.
      eapply lts_oba_mo_spec2 in l0 as hd2; eauto.
      split.
      ++ rewrite hd1 in hwp1. rewrite hd2 in hwp2.
         eapply strip_eq_step in hwp1, hwp2; eauto.
         destruct hwp1 as (t1 & hwq1' & heq1').
         destruct hwp2 as (t2 & hwq2' & heq2').
         set (heq1 := strip_m_deter hwq1 hwq1').
         set (heq2 := strip_m_deter hwq2 hwq2').
         transitivity t1. now symmetry.
         transitivity q1'. now symmetry.
         transitivity q2'. now symmetry.
         transitivity t2. now symmetry. eassumption.
      ++ multiset_solver.
    + edestruct (equiv q1' p2'); eauto; simpl in *.
      split.
      ++ rewrite hd1 in hwp1.
         eapply strip_eq_step in hwp1; eauto.
         destruct hwp1 as (t1 & hwq1' & heq1').
         set (heq1 := strip_m_deter hwq1 hwq1').
         transitivity t1. naive_solver.
         transitivity q1'; naive_solver.
      ++ rewrite hd1. symmetry.
         rewrite gmultiset_disj_union_comm at 1.
         eapply (non_blocking_action_in_ms mp2 η mq2) in nb as eq; eauto ; subst.
         assert (mb_without_not_nb ({[+ η +]} ⊎ mq2) = {[+ η +]} ⊎ mb_without_not_nb mq2) as eq.
         eapply lts_mb_nb_spec1;eauto. rewrite eq.
         rewrite <- 2 gmultiset_disj_union_assoc.
         eapply gmultiset_eq_pop_l. multiset_solver.
  - inversion Hstep_nb'; subst.
    + eapply lts_oba_mo_spec2 in l0 as hd1; eauto.
      edestruct (lts_oba_mo_strip q2) as (q2' & hwq2).
      edestruct (equiv p1' q2'); eauto; simpl in *.
      split.
      ++ rewrite hd1 in hwp2.
         eapply strip_eq_step in hwp2; eauto.
         destruct hwp2 as (t2 & hwq2' & heq2').
         set (heq1 := strip_m_deter hwq2 hwq2').
         transitivity q2'. naive_solver.
         transitivity t2; naive_solver.
      ++ rewrite hd1.
         rewrite gmultiset_disj_union_comm at 1.
         eapply (non_blocking_action_in_ms mp1 η mq1) in nb as eq; eauto; subst.
         assert (mb_without_not_nb ({[+ η +]} ⊎ mq1) = {[+ η +]} ⊎ mb_without_not_nb mq1) as eq.
         eapply lts_mb_nb_spec1;eauto. rewrite eq.
         rewrite <- 2 gmultiset_disj_union_assoc.
         eapply gmultiset_eq_pop_l. multiset_solver.
    + eapply (non_blocking_action_in_ms mp1 η mq1) in nb as eq; subst; eauto.
      assert (mb_without_not_nb ({[+ η +]} ⊎ mq1) = {[+ η +]} ⊎ mb_without_not_nb mq1) as eq.
      eapply lts_mb_nb_spec1;eauto. rewrite eq.
      edestruct (equiv p1' p2'); eauto; simpl in *.
      eapply (non_blocking_action_in_ms mp2 η mq2) in nb as eq'; subst; eauto.
      split. assumption.
      assert (mb_without_not_nb ({[+ η +]} ⊎ mq2) = {[+ η +]} ⊎ mb_without_not_nb mq2) as eq''.
      eapply lts_mb_nb_spec1;eauto. rewrite eq''.
      multiset_solver.
Qed.

(* Forwarder of a LTS with OBA axioms respects FW axioms *)

#[global] Program Instance FW_gLtsObaFW
  `{M : @gLtsObaFB P A H gLtsP gLtsEqP gLtsObaP}
  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}
  : gLtsObaFW (P * mb A) A.
Next Obligation.
  intros ? ? ? ? ? ? ? ? (p, m) η μ.
  exists (p, {[+ η +]} ⊎ m). split; eauto with mdb.
  eapply ParRight. eapply lts_multiset_add; eauto.
  eapply ParRight. eapply lts_multiset_minus; eauto.
Qed.
Next Obligation.
  intros ? ? ? ? ? ? ? ? (p1, m1) (p2, m2) (p3, m3) η μ nb duo Hstep_nb Hstep.
  inversion Hstep_nb; subst.
  + inversion Hstep; subst.
    ++ left. destruct (lts_oba_fb_feedback nb duo l l0) as (t & l1 & heq).
       exists (t, m3). split. eapply ParLeft; assumption.
       now eapply fw_eq_id_mb.
    ++ right. simpl. unfold fw_eq.
       intros p' q' strip_p strip_q. simpl in *.
       assert ( blocking μ) as not_nb. eapply dual_blocks; eauto.
       eapply (blocking_action_in_ms m2 μ m3) in not_nb as (eq & duo' & nb'); subst.
       set (heq := lts_oba_mo_spec2 _ _ _ nb l).
       rewrite heq in strip_p. rewrite heq. split.
       +++ destruct (strip_mem_ex strip_p) as (e & l' & nb'').
           destruct (strip_eq_step strip_p e l') as (t & hwo & heq'); eauto.
           set (h := lts_oba_non_blocking_action_deter nb'' l l').
           etrans. symmetry. eassumption.
           symmetry. eapply strip_eq_sim; eassumption.
       +++ assert (mb_without_not_nb ({[+ co μ +]} ⊎ m2) 
              = {[+ co μ +]} ⊎ mb_without_not_nb m2) as eq''.
           eapply lts_mb_nb_spec1;eauto. rewrite eq''.
           rewrite <- gmultiset_disj_union_assoc.
           rewrite gmultiset_disj_union_comm.
           rewrite <- gmultiset_disj_union_assoc.
           eapply gmultiset_eq_pop_l.
           assert (η = co μ) as eq_nb. eapply unique_nb; eauto; subst. subst.
           now rewrite gmultiset_disj_union_comm.
       +++ assumption.
  + inversion Hstep; subst.
    ++ left. exists (p3, m3). split. eapply ParSync; eauto. split; eauto. reflexivity.
    ++ right. 
       eapply (non_blocking_action_in_ms m1 η m2) in nb as eq; subst; eauto.
       assert (blocking μ) as not_nb. eapply dual_blocks; eauto.
       eapply (blocking_action_in_ms m2 μ m3) in not_nb as (eq & duo' & nb'); subst; eauto.
       assert (η = co μ) as eq_nb. eapply unique_nb; eauto. subst.
       reflexivity.
Qed.

(**********************************Forwarder Construction is a Finite Image LTS ************************)

Definition lts_fw_not_non_blocking_action_set `{FiniteImagegLts P A} 
  (p : P) (m : mb A) μ :=
  if (decide (dual (co μ) μ /\ non_blocking (co μ))) 
  then (p, {[+ (co μ) +]} ⊎ m) :: map (fun p => (proj1_sig p, m)) (enum $ dsig (lts_step p (ActExt $ μ)))
  else map (fun p => (proj1_sig p, m)) (enum $ dsig (lts_step p (ActExt $ μ))).

Definition lts_fw_non_blocking_action_set `{FiniteImagegLts P A} 
  (p : P) (m : mb A) η :=
  let ps := map (fun p => (proj1_sig p, m)) (enum $ dsig (lts_step p (ActExt $ η))) in
  if (decide (η ∈ m)) then (p, m ∖ {[+ η +]}) :: ps else ps.


Definition lts_fw_co_fin `{@FiniteImagegLts P A H M}
  `{@Prop_of_Inter P (mb A) A fw_inter H M MbgLts}
  (p : P) (η : A) (* : list (A * list P) *) :=
  map (fun μ => (η, map proj1_sig (enum $ dsig (lts_step p (ActExt $ μ))))) 
    (elements (lts_co_inter_action_left η p) ++ elements (lts_essential_actions_left p)).

Definition lts_fw_com_fin `{@FiniteImagegLts P A H M}
  `{@Prop_of_Inter P (mb A) A fw_inter H M MbgLts}
  (p : P) (m : list A) : list (A * list P) :=
  concat (map (fun η => (lts_fw_co_fin p η)) m). (* flat_map (fun η => (lts_fw_co_fin p η)) m. *)

Definition lts_fw_tau_set `{@FiniteImagegLts P A H M} 
  `{@Prop_of_Inter P (mb A) A fw_inter H M MbgLts}
  (p : P) (m : mb A) : list (P * mb A) :=
  let xs := map (fun p' => (proj1_sig p', m)) (enum $ dsig (fun q => p ⟶ q)) in
  let ys :=
    concat (map
              (fun '(a, ps) => map (fun p => (p, m ∖ {[+ a +]})) ps)
              (lts_fw_com_fin p (elements m) ))
    in xs ++ ys.

Lemma lts_fw_tau_set_spec1 
  `{gLtsP : @gLts P A H}
  `{@FiniteImagegLts P A H gLtsP} 
  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}
  p1 m1 p2 m2 :
  (p1, m1) ⟶ (p2, m2) ->
  (p2, m2) ∈ lts_fw_tau_set p1 m1.
Proof.
  intros l.
  inversion l; subst.
  + eapply elem_of_app. left.
    eapply elem_of_list_fmap.
    exists (dexist p2 l0). split. reflexivity. eapply elem_of_enum.
  + inversion l0.
  + assert (inter : fw_inter μ1 μ2). eauto.
    destruct eq as (duo & nb).
    eapply elem_of_app. right.
    eapply elem_of_list_In.
    eapply in_concat.
    exists (map (fun p => (p, m2))
         (map proj1_sig (enum $ dsig (lts_step p1 (ActExt $ μ1))))
      ).
    split.
    eapply elem_of_list_In.
    eapply elem_of_list_fmap.
    exists (co μ1, map proj1_sig (enum $ dsig (lts_step p1 (ActExt $ μ1)))).
    eapply (non_blocking_action_in_ms m1 μ2 m2) in nb as eq; subst; eauto.
    assert (μ2 = co μ1) as eq. eapply unique_nb; eauto. subst.
    split.
    now replace (({[+ co μ1 +]} ⊎ m2) ∖ {[+ co μ1 +]}) with m2 by multiset_solver.
    assert (elements ({[+ co μ1 +]} ⊎ m2) ≡ₚ 
    elements (gmultiset_singleton (co μ1)) ++ elements (m2)) as equiv.
    unfold singletonMS. eapply gmultiset_elements_disj_union.
    assert (map (λ η : A, lts_fw_co_fin p1 η) (elements ({[+ co μ1 +]} ⊎ m2)) ≡ₚ 
    map (λ η : A, lts_fw_co_fin p1 η) (elements ({[+(co μ1)+]} : gmultiset A) ++ elements m2))
    as equiv2.
    eapply Permutation_map. eauto.
    erewrite gmultiset_elements_singleton in equiv2.
    simpl in equiv2. 
    assert (eq : co μ1 ▷ map proj1_sig (enum (dsig (lts_step p1 (ActExt μ1)))) ∈ 
    lts_fw_co_fin p1 (co μ1)).
    unfold lts_fw_co_fin.
    edestruct (lts_essential_actions_spec_interact _ _ _ _ _ _ l1 l2 inter) 
      as [ess_act | not_ess_act].
    ++ rewrite map_app.  eapply elem_of_app. right. 
       eapply elem_of_list_In. 
       assert (lts_essential_actions_left p1 = 
       {[μ1]} ∪ lts_essential_actions_left p1 ∖ {[μ1]}) as eq''.
        eapply union_difference_singleton_L;eauto.
       rewrite eq''.
       assert (elements ({[μ1]} ∪ (lts_essential_actions_left p1) ∖ {[μ1]}) ≡ₚ
        μ1 :: elements ((lts_essential_actions_left p1) ∖ {[μ1]})) as eq'''.
        eapply elements_union_singleton. set_solver. symmetry in eq'''.
       eapply Permutation_in. eapply Permutation_map. exact eq'''. simpl. left. eauto.
    ++ assert (μ1 ∈ lts_co_inter_action_left (co μ1) p1). eauto.
       eapply lts_co_inter_action_spec_left ; eauto.
       rewrite map_app. 
       eapply elem_of_app. left. 
       eapply elem_of_list_In. 
       assert (lts_co_inter_action_left (co μ1) p1 = 
       {[μ1]} ∪ lts_co_inter_action_left (co μ1) p1 ∖ {[μ1]}) as eq''.
        eapply union_difference_singleton_L;eauto.
       rewrite eq''.
       assert (elements ({[μ1]} ∪ (lts_co_inter_action_left (co μ1) p1) ∖ {[μ1]}) ≡ₚ
        μ1 :: elements ((lts_co_inter_action_left (co μ1) p1) ∖ {[μ1]})) as eq'''.
       eapply elements_union_singleton. set_solver. symmetry in eq'''.
       eapply Permutation_in. eapply Permutation_map. exact eq'''. simpl. left. eauto.
    ++ unfold lts_fw_com_fin. 
    rewrite<- flat_map_concat_map.
    assert (eq' : flat_map (λ η : A, lts_fw_co_fin p1 η) (elements ({[+ co μ1 +]} ⊎ m2))
    ≡ₚ flat_map (λ η : A, lts_fw_co_fin p1 η) (elements ({[+ co μ1 +]} : gmultiset A) 
      ++ (elements m2))).
    eapply Permutation_flat_map. eauto.
    erewrite gmultiset_elements_singleton in eq'.
    simpl in *.
    eapply elem_of_Permutation_proper; eauto. 
    eapply elem_of_list_In. 
    eapply in_or_app. left. eapply elem_of_list_In in eq. eauto.
    ++ eapply elem_of_list_In.
    eapply elem_of_list_fmap.
    eexists.  split. reflexivity.
    eapply elem_of_list_fmap.
    exists (dexist p2 l1). split. reflexivity. eapply elem_of_enum.
Qed.

Lemma lts_fw_input_set_spec1 `{@FiniteImagegLts P A H gLtsP}
  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}
  p1 m1 p2 m2 μ :
  (p1, m1) ⟶[μ] (p2, m2) -> blocking μ -> 
    (p2, m2) ∈ lts_fw_not_non_blocking_action_set p1 m1 μ.
Proof.
  intros l not_nb.
  inversion l; subst.
  + unfold lts_fw_not_non_blocking_action_set.
    destruct (decide (dual (co μ) μ /\ non_blocking (co μ))) as [(duo & nb) | case2].
    - right. eapply elem_of_list_fmap.
      exists (dexist p2 l0). split. reflexivity. eapply elem_of_enum.
    - eapply elem_of_list_fmap.
      exists (dexist p2 l0). split. reflexivity. eapply elem_of_enum.
  + eapply (blocking_action_in_ms m1 μ m2) in not_nb as (eq & duo & nb); eauto; subst.
    unfold lts_fw_not_non_blocking_action_set.
    destruct (decide (dual (co μ) μ /\ non_blocking (co μ))) as [toto | impossible].
    ++ left.
    ++ assert (dual (co μ) μ ∧ non_blocking (co μ)); eauto. contradiction.
Qed. 

Lemma lts_fw_non_blocking_action_set_spec1 `{@FiniteImagegLts P A H gLtsP}
  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}
  p1 m1 p2 m2 η :
  (p1, m1) ⟶[η] (p2, m2) -> non_blocking η -> 
    (p2, m2) ∈ lts_fw_non_blocking_action_set p1 m1 η.
Proof.
  intros l nb.
  inversion l; subst.
  + unfold lts_fw_non_blocking_action_set.
    destruct (decide (η ∈ m2)) as [in_mem | not_in_mem].
    right. eapply elem_of_list_fmap. 
    exists (dexist p2 l0). split. reflexivity. eapply elem_of_enum. 
    eapply elem_of_list_fmap.
    exists (dexist p2 l0). split. reflexivity. eapply elem_of_enum. 
  + unfold lts_fw_non_blocking_action_set.
    eapply (non_blocking_action_in_ms m1 η m2) in nb as eq; subst ; eauto.
    destruct (decide (η ∈ {[+ η +]} ⊎ m2)).
    ++ replace (({[+ η +]} ⊎ m2) ∖ {[+ η +]}) with m2 by multiset_solver.
       left.
    ++ multiset_solver.
Qed.

#[global] Program Instance gLtsMBFinite `{@FiniteImagegLts P A H gLtsP} 
  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}
  : FiniteImagegLts (P * mb A) A.
Next Obligation. 
  intros ? ? ? ? ? ? (p, m) α.
  destruct α as [η | ].
  + destruct (decide (non_blocking η)) as [nb | not_nb].
    - eapply (in_list_finite (lts_fw_non_blocking_action_set p m η));
      intros (p0, m0) h%bool_decide_unpack.
      now eapply lts_fw_non_blocking_action_set_spec1.
    - rename η into μ. 
      eapply (in_list_finite (lts_fw_not_non_blocking_action_set p m μ)). simpl in *.
      intros (p0, m0) h%bool_decide_unpack.
      now eapply lts_fw_input_set_spec1. 
  + eapply (in_list_finite (lts_fw_tau_set p m)).
      intros (p0, m0) h%bool_decide_unpack.
      now eapply lts_fw_tau_set_spec1.
Qed.
