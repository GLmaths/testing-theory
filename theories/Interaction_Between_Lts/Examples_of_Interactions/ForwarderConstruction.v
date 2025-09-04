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
From stdpp Require Import base countable list decidable finite gmap gmultiset.
From Must Require Import MultisetHelper gLts Bisimulation Lts_OBA Lts_FW Lts_OBA_FB FiniteImageLTS
    InListPropHelper CodePurification InteractionBetweenLts MultisetLTSConstruction ActTau.

(**************************************** Forwarder LTS *************************************)

Definition fw_inter `{ExtAction A} μ2 μ1 := dual μ1 μ2 /\ non_blocking μ1.

#[global] Program Instance FW_gLts {P A : Type} `{H : ExtAction A} (M: gLts P A) 
  `{@Prop_of_Inter P (mb A) A fw_inter H M MbgLts}
    : gLts (P * mb A) A := inter_lts fw_inter.

(* Properties on the Forwarder Construction *)

Lemma add_in_mb_fw_tau `{
  @Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}

  (m : mb A) (p : P) (mp : mb A) (p' : P) (mp' : mb A) :
  (p ▷ mp) ⟶ (p' ▷ mp') -> (p ▷ m ⊎ mp) ⟶ (p' ▷ m ⊎ mp').
Proof.
  intro Hstep.
  inversion Hstep; subst.
  + eapply ParLeft; assumption.
  + inversion l.
  + eapply ParSync; eauto.
    destruct (decide (non_blocking μ2)) as [nb | not_nb].
    ++ eapply non_blocking_action_in_ms in nb as eq'; eauto; subst.
       assert (m ⊎ ({[+ μ2 +]} ⊎ mp') 
       = {[+ μ2 +]} ⊎ (m ⊎ mp')) as eqm by multiset_solver.
       rewrite eqm.
       assert (m ⊎ mp' = mp' ⊎ m) as eqm' by multiset_solver.
       rewrite eqm'. eapply lts_multiset_minus; eauto.
    ++ eapply blocking_action_in_ms in not_nb as (eq' & duo & nb); eauto; subst.
       assert (m ⊎ ({[+ co μ2 +]} ⊎ mp) = {[+ co μ2 +]} ⊎ (m ⊎ mp))
       as eqm' by multiset_solver.
       rewrite eqm'. eapply lts_multiset_add; eauto.
Qed.

Lemma add_in_mb_fw_action `{
  @Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}

  (m : mb A) (p : P) (mp : mb A) (p' : P) (mp' : mb A) (μ : A):
  (p ▷ mp) ⟶[μ] (p' ▷ mp') -> (p ▷ m ⊎ mp) ⟶[μ] (p' ▷ m ⊎ mp').
Proof.
  intro Hstep.
  inversion Hstep; subst.
  + eapply ParLeft; assumption.
  + inversion l; subst.
    ++ eapply ParRight.
       assert ({[+ η +]} ⊎ (m ⊎ mp) = m ⊎ ({[+ η +]} ⊎ mp)) as eq.
       multiset_solver. rewrite<- eq. eapply lts_multiset_add; eauto.
    ++ eapply ParRight.
       assert (m ⊎ ({[+ μ +]} ⊎ mp') = {[+ μ +]} ⊎ (m ⊎ mp')) as eq.
       multiset_solver. rewrite eq. eapply lts_multiset_minus; eauto.
Qed.

(** Definining an Forwarder Equivalence ≐ , between forwarders, using code purification *)

Definition fw_eq `{gLtsOba P A} (p : P * mb A) (q : P * mb A) :=
  forall (p' q' : P),
    p.1 ⟿{lts_oba_mo p.1} p' ->
    q.1 ⟿{lts_oba_mo q.1} q' ->
    p' ⋍ q' /\ lts_oba_mo p.1 ⊎ (mb_without_not_nb p.2) = 
        lts_oba_mo q.1 ⊎ (mb_without_not_nb q.2).

Infix "≐" := fw_eq (at level 70).

(** ≐ is reflexive. **)

Lemma fw_eq_refl `{gLtsOba P A} : Reflexive fw_eq.
Proof.
  intros p p1 q2 hw1 hw2. split; [eapply strip_m_deter|]; eauto.
Qed.

Global Hint Resolve fw_eq_refl:mdb.

(** ≐ is symmetric. **)

Lemma fw_eq_symm `{gLtsOba P A} : Symmetric fw_eq.
Proof.
  intros p q heq.
  intros q2 p2 hw1 hw2.
  destruct (heq p2 q2 hw2 hw1) as (heq2 & hmo2). naive_solver.
Qed.

Global Hint Resolve fw_eq_symm:mdb.

(** ≐ is transitive. **)

Lemma fw_eq_trans `{gLtsOba P A} : Transitive fw_eq.
Proof.
  intros p q t.
  intros heq1 heq2 p2 t2 hwp hwt.
  edestruct (lts_oba_mo_strip q.1) as (q2 & hwq).
  destruct (heq1 p2 q2 hwp hwq) as (heq3 & heq4).
  destruct (heq2 q2 t2 hwq hwt) as (heq5 & heq6).
  split. etrans; naive_solver. multiset_solver.
Qed.

Global Hint Resolve fw_eq_trans:mdb.

(** Congruence is an Equivalence. *)

Lemma fw_eq_equiv `{gLtsOba P A} : Equivalence fw_eq.
Proof. constructor; eauto with mdb. Qed.

Global Hint Resolve fw_eq_equiv:mdb.

(* Properties on our FW Equivalence *)

Lemma fw_eq_id_mb `{gLtsOba P A} p q m : p ⋍ q -> fw_eq (p, m) (q, m).
Proof.
  intros heq p' q' hwp hwq. simpl in *.
  set (h := lts_oba_mo_eq heq).
  split. rewrite <- h in hwq. eapply (strip_eq_sim heq hwp hwq).
  multiset_solver.
Qed.

Definition lts_fw_sc
  `{M1 : @gLtsOba P A H gLtsP gLtsEqP}
  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}
  (p : P * mb A) α (q : P * mb A) :=
  exists r, ((FW_gLts gLtsP).(lts_step) p α r) /\ r ≐ q.

Notation "p ⟶≐ q" := (lts_fw_sc p τ q) (at level 90, format "p  ⟶≐  q").
Notation "p ⟶≐{ α } q" := (lts_fw_sc p α q) (at level 90, format "p  ⟶≐{ α }  q").
Notation "p ⟶≐[ μ ] q" := (lts_fw_sc p (ActExt μ) q) (at level 90, format "p  ⟶≐[ μ ]  q").

(* Properties on our FW Equivalence, to assert it is a simulation. *)

Lemma fw_eq_blocking_action_simulation `{gLtsOba P A} {p q mp mq μ q'} :
  p ▷ mp ≐ q ▷ mq -> blocking μ  -> q ⟶[μ] q'
    -> exists p', p ⟶[μ] p' /\ p' ▷ mp ≐ q' ▷ mq.
Proof.
  intros heq not_nb hlq. 
  edestruct (lts_oba_mo_strip p) as (p0 & hwp).
  edestruct (lts_oba_mo_strip q) as (q0 & hwq).
  edestruct (heq p0 q0) as (heqp0 & heqm); eauto. simpl in *.
  eapply lts_oba_mo_non_blocking_contra in not_nb as not_in. instantiate (1 := q) in not_in.
  edestruct (strip_delay_m not_in hwq hlq) as (q1 & hwq').
  edestruct (strip_delay_inp4 not_nb hlq hwq') as (q2 & hwq2 & hlq2).
  assert (q0 ⋍ q2) by (eapply strip_m_deter; eauto).
  destruct hlq2 as (r & hlr & heqr).
  edestruct (eq_spec p0 r (ActExt $ μ)) as (p0' & hlp0' & heqp0').
  exists q2. split; eauto. transitivity q0; eauto.
  edestruct (strip_retract_act hwp hlp0' ) as (p' & wp' & p1 & hwp' & heqp').
  exists p'. split. eassumption.
  intros pt qt hwpt hwqt. simpl in *.
  assert (heq1 : lts_oba_mo p' = lts_oba_mo p ⊎ lts_oba_mo p1).
  eapply strip_after; eauto.
  assert (heq2 : lts_oba_mo q' = lts_oba_mo q ⊎ lts_oba_mo q1).
  eapply strip_after; eauto.
  assert (heq3 : lts_oba_mo p1 = lts_oba_mo q1).
  eapply lts_oba_mo_eq. transitivity p0'. now symmetry. transitivity r; eauto.
  split.
  - rewrite heq1 in hwpt.
    rewrite heq2 in hwqt.
    eapply strip_aux1 in hwpt as (pt' & hwp1 & heqpt'); eauto.
    eapply strip_aux1 in hwqt as (qt' & hwq1 & heqqt'); eauto.
    transitivity pt'. now symmetry.
    transitivity qt'.
    assert (heq0 : p1 ⋍ q1).
    transitivity p0'. now symmetry. transitivity r; eauto.
    eapply (strip_eq_sim heq0); eauto.
    now rewrite heq3. assumption.
  - multiset_solver.
Qed.

Lemma lts_fw_eq_spec_left_blocking_action `{
   M : @gLtsObaFB P A H gLtsP gLtsEqP gLtsObaP}
   `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}
   p q q' mp mq μ :
   p ▷ mp ≐ q ▷ mq -> blocking μ -> q ⟶[μ] q'
    -> p ▷ mp ⟶≐[μ] q' ▷ mq.
Proof.
  intros not_nb heq l.
  edestruct (fw_eq_blocking_action_simulation not_nb heq l) as (p' & hl' & heq').
  exists (p' ▷ mp). split.
  + eapply ParLeft. eauto with mdb.
  + eauto with mdb.
Qed.

Lemma lts_fw_eq_spec_left_non_blocking_action `{
  M : @gLtsObaFB P A H gLtsP gLtsEqP gLtsObaP}
  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}
  p q q' mp mq η :
  p ▷ mp ≐ q ▷ mq -> non_blocking η -> q ⟶[η] q' -> p ▷ mp ⟶≐[η] q' ▷ mq.
Proof.
  intros heq nb l.
  edestruct (lts_oba_mo_strip p) as (p0 & hwp).
  edestruct (lts_oba_mo_strip q) as (q0 & hwq).
  assert (η ∈ lts_oba_mo q) as h0. eapply lts_oba_mo_spec_bis1; eauto.
  edestruct (heq p0 q0) as (heq0 & heqm0); eauto. simpl in *.
  assert (h1 : η ∈ lts_oba_mo p ⊎ mb_without_not_nb mp) by multiset_solver.
  eapply gmultiset_elem_of_disj_union in h1 as [hleft|hright].
  ++ eapply gmultiset_disj_union_difference' in hleft as heqmop.
     eapply lts_oba_mo_spec_bis2 in hleft as (p' & nb1 & hl').
     rewrite heqmop in hwp.
     eapply strip_eq_step in hwp as (p0' & hwop0' & heqp0'); eauto.
     assert (η ∈ lts_oba_mo q) as h2. eapply (lts_oba_mo_spec_bis1 _ _ _ nb l).
     eapply gmultiset_disj_union_difference' in h2 as heqmoq.
     rewrite heqmoq in hwq.
     eapply strip_eq_step in hwq as (q0' & hwoq0' & heqq0'); eauto.
     exists (p', mp). 
     split. eapply ParLeft. eauto with mdb.
     intros pt qt hwopt hwoqt. simpl in *.
     eapply lts_oba_mo_spec2 in hl', l; eauto.
     assert (heq1 : lts_oba_mo q' = lts_oba_mo q ∖ {[+ η +]})
       by multiset_solver.
     assert (heq2 : lts_oba_mo p' = lts_oba_mo p ∖ {[+ η +]})
       by multiset_solver.
     rewrite heq1 in hwoqt. rewrite heq2 in hwopt.
     split.
     +++ transitivity p0'. eapply strip_m_deter; eauto.
         transitivity p0. assumption.
         transitivity q0. assumption.
         transitivity q0'. now symmetry.
         eapply strip_m_deter; eauto.
     +++ multiset_solver.
  ++ assert (η ∈ mp) as hright'. eapply lts_mb_nb_with_nb_spec1; eauto.
     eapply gmultiset_disj_union_difference' in hright'.
     rewrite hright'.
     eexists. split.
     eapply (ParRight (ActExt η) p ({[+ η +]} ⊎ mp ∖ {[+ η +]}) (mp ∖ {[+ η +]})).
     eapply lts_multiset_minus. eauto with mdb.
     intros pt qt hwopt hwoqt. simpl in *.
     split.
     +++ edestruct (heq pt q0) as (heq1 & heqm1); eauto. simpl in *.
         transitivity q0. assumption.
         eapply gmultiset_disj_union_difference' in h0 as heqmoq.
         rewrite heqmoq in hwq.
         eapply strip_eq_step in hwq as (q0' & hwoq0' & heqq0'); eauto.
         transitivity q0'. now symmetry.
         eapply lts_oba_mo_spec2 in l; eauto.
         assert (heq2 : lts_oba_mo q' = lts_oba_mo q ∖ {[+ η +]})
           by multiset_solver.
         rewrite heq2 in hwoqt. eapply strip_m_deter; eauto.
     +++ eapply lts_oba_mo_spec2 in l; eauto.
         assert (η ∈ mb_without_not_nb mp). eauto.
         eapply lts_mb_nb_with_nb_spec1 in hright as (nb'' & mem'').
         rewrite lts_mb_nb_with_nb_diff;eauto. multiset_solver.
Qed.

Lemma lts_fw_eq_spec_left_tau
  `{M : @gLtsObaFB P A H gLtsP gLtsEqP gLtsObaP}
  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}
  (p : P) (q : P) q' (mp : mb A) (mq : mb A) :
  p ▷ mp ≐ q ▷ mq -> q ⟶ q'
    -> p ▷ mp ⟶≐ q' ▷ mq.
Proof.
  intros heq l.
  edestruct (lts_oba_mo_strip q) as (q0 & hwq).
  edestruct (lts_oba_mo_strip p) as (p0 & hwp).
  edestruct (heq p0 q0) as (heq0 & heqm0); eauto. simpl in *.
  destruct (strip_delay_tau hwq l) as
    [(a & b & q1 & duo & nb  & l1 & l2) | (qt & q1 & hltqt & hwq1 & heq1)].
  - destruct l2 as (q'' & hlq1 & heq'').
    edestruct (lts_oba_non_blocking_action_delay nb l1 hlq1) as (q2 & hlq & hlq2).
    assert (blocking b) as not_nb. eapply dual_blocks; eauto.
    edestruct (fw_eq_blocking_action_simulation heq not_nb hlq) as (p2 & hlp_inp & heqp2).
    assert (mem : a ∈ lts_oba_mo p ⊎ (mb_without_not_nb mp))
      by (eapply lts_oba_mo_spec_bis1 in l1; multiset_solver).
    eapply gmultiset_elem_of_disj_union in mem as [hleft | hright].
    + assert {p1 | non_blocking a /\ p ⟶[a] p1} as (p1 & nb1 & tr1)
          by now eapply lts_oba_mo_spec_bis2.
      assert (neq : b ≠ a). now eapply BlockingAction_are_not_non_blocking. 
      edestruct (lts_oba_non_blocking_action_confluence nb neq tr1 hlp_inp)
        as (p'' & hlp1 & hlp2).
      destruct (lts_oba_fb_feedback nb duo tr1 hlp1)
        as (p' & hlp_tau & heqp').
      exists (p', mp). split. 
      eapply ParLeft. eauto with mdb.
      intros pt qt hwpt hwqt. simpl in *.
      edestruct (lts_oba_mo_strip p2) as (pt' & hwpt').
      edestruct (lts_oba_mo_strip q2) as (qt' & hwqt').
      edestruct heqp2 as (heqpqt' & heqmpt'); eauto; simpl in *.
      destruct hlp2 as (p''' & hlp2 & heqp'').
      assert (heqm1 : lts_oba_mo p2 = {[+ a +]} ⊎ lts_oba_mo p').
      replace (lts_oba_mo p') with (lts_oba_mo p''').
      now eapply lts_oba_mo_spec2.
      eapply lts_oba_mo_eq. etrans. eapply heqp''. now symmetry.
      destruct hlq2 as (q''' & hlq2 & heqq'').
      assert (heqm2 : lts_oba_mo q2 = {[+ a +]} ⊎ lts_oba_mo q').
      replace (lts_oba_mo q') with (lts_oba_mo q''').
      now eapply lts_oba_mo_spec2.
      eapply lts_oba_mo_eq. etrans. eapply heqq''. now symmetry.
      split.
      ++ rewrite heqm1 in hwpt'. rewrite heqm2 in hwqt'.
         eapply strip_eq_step in hwpt' as (pr & hwpr & heqpr); eauto.
         eapply strip_eq_step in hwqt' as (qr & hwqr & heqqr); eauto.
         etrans. eapply strip_eq_sim.
         etrans. eapply heqp'. symmetry.
         eapply heqp''. eassumption. eassumption.
         symmetry.
         etrans. eapply strip_eq_sim.
         etrans. symmetry. eapply heq''. symmetry.
         eapply heqq''. eassumption. eassumption.
         symmetry. etrans. apply heqpr. etrans. apply heqpqt'. now symmetry.
      ++ multiset_solver.
    + eapply lts_mb_nb_with_nb_spec1 in hright as (nb' & hright).
      exists (p2, mp ∖ {[+ a +]}). split.
      ++ eapply gmultiset_disj_union_difference' in hright.
         rewrite hright at 1. 
         eapply ParSync; eauto. unfold fw_inter.  
         split; eauto.
         eapply lts_multiset_minus; eauto.
      ++ destruct hlq2 as (q''' & hlq2 & heqq'').
         assert (heqm2 : lts_oba_mo q2 = {[+ a +]} ⊎ lts_oba_mo q').
         replace (lts_oba_mo q') with (lts_oba_mo q''').
         now eapply lts_oba_mo_spec2.
         eapply lts_oba_mo_eq. etrans. eapply heqq''. now symmetry.
         intros pt qt hwpt hwqt. simpl in *.
         assert (heq' : q''' ⋍ q') by (etrans; eassumption).
         edestruct (strip_eq hwqt _ heq') as (qt' & hwqt' & heqqt').
         edestruct heqp2 as (heqpqt' & heqmpt'); eauto; simpl in *.
         rewrite heqm2. eapply strip_step; eassumption.
         split.
         symmetry. etrans. symmetry. eapply heqqt'. now symmetry.
         eapply (gmultiset_disj_union_inj_1 {[+ a +]}).
         replace ({[+ a +]} ⊎ (lts_oba_mo q' ⊎ (mb_without_not_nb mq))) with
           ({[+ a +]} ⊎ lts_oba_mo q' ⊎ (mb_without_not_nb mq)) by multiset_solver.
         rewrite <- heqm2.
         rewrite <- heqmpt'.
         rewrite gmultiset_disj_union_assoc.
         replace ({[+ a +]} ⊎ lts_oba_mo p2) with (lts_oba_mo p2 ⊎ {[+ a +]}) 
         by multiset_solver.
         rewrite <- gmultiset_disj_union_assoc.
         eapply gmultiset_eq_pop_l.
         apply lts_mb_nb_with_nb_spec2 in hright; eauto.
         assert (mb_without_not_nb (mp ∖ {[+ a +]}) = (mb_without_not_nb mp) ∖ {[+ a +]}) as eq.
         eapply lts_mb_nb_with_nb_diff; eauto.
         eapply lts_mb_nb_with_nb_spec1 in hright as (nb'' & mem'').
         eauto.
         rewrite eq. multiset_solver.
  - edestruct (eq_spec p0 qt τ) as (pt & hlpt & heqpt); eauto.
    edestruct (strip_retract_act hwp hlpt )
      as (p' & wp' & p1 & hwp' & heqpr0).
    exists (p', mp). split.
    eapply ParLeft. eauto with mdb.
    intros pr qr hwpr hwqr. simpl in *.
    assert (heqr1 : lts_oba_mo p' = lts_oba_mo p ⊎ lts_oba_mo p1).
    eapply strip_after; eauto.
    assert (heqr2 : lts_oba_mo q' = lts_oba_mo q ⊎ lts_oba_mo q1).
    eapply strip_after; eauto.
    assert (heqr3 : lts_oba_mo p1 = lts_oba_mo q1).
    eapply lts_oba_mo_eq.
    transitivity pt. now symmetry. transitivity qt; eauto. now symmetry.
    split.
    + rewrite heqr1 in hwpr. rewrite heqr2 in hwqr.
      eapply strip_aux1 in hwpr as (pt' & hwp1' & heqpt'); eauto.
      eapply strip_aux1 in hwqr as (qt' & hwq1' & heqqt'); eauto.
      transitivity pt'. now symmetry. transitivity qt'.
      assert (heqr0 : p1 ⋍ q1).
      transitivity pt. now symmetry.
      transitivity qt; eauto. now symmetry.
      eapply (strip_eq_sim heqr0); eauto.
      now rewrite heqr3. assumption.
    + multiset_solver.
Qed.

Lemma lts_fw_eq_spec_left `{
  M : @gLtsObaFB P A H gLtsP gLtsEqP gLtsObaP}
  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}
  p q q' α mp mq :
  p ▷ mp ≐ q ▷ mq -> q ⟶{α} q'
    -> p ▷ mp ⟶≐{α} q' ▷ mq.
Proof.
  intros heq l. destruct α as [μ | ].
  + destruct (decide (non_blocking μ)).
   ++ eapply lts_fw_eq_spec_left_non_blocking_action; eauto.
   ++ eapply lts_fw_eq_spec_left_blocking_action; eauto.
  + eapply lts_fw_eq_spec_left_tau; eauto.
Qed.

Lemma lts_fw_eq_spec_right_non_blocking_action `{
  M : @gLtsObaFB P A H gLtsP gLtsEqP gLtsObaP}
  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}
  p q mp mq η :
  non_blocking η -> p ▷ mp ≐ q ▷ {[+ η +]} ⊎ mq
    -> p ▷ mp ⟶≐[η] q ▷ mq.
Proof.
  intros nb heq.
  destruct (decide (η ∈ mp)) as [eq | not_eq].
  + assert (η ∈ mb_without_not_nb mp). eapply lts_mb_nb_with_nb_spec2;eauto.
    assert (η ∈ lts_oba_mo p ⊎ mb_without_not_nb mp) as eq'. multiset_solver.
    exists (p, mp ∖ {[+ η +]}). split.
    eapply gmultiset_disj_union_difference' in eq as eq''. rewrite eq'' at 1. 
    eapply ParRight. eapply lts_multiset_minus. eauto with mdb.
    intros p' q' hw1 hw2. simpl in *.
    edestruct (heq p' q') as (equiv & same_mb) ; eauto; simpl in *.
    split. eassumption.
    eapply gmultiset_disj_union_difference' in eq as eq''.
    eapply (gmultiset_disj_union_inj_1 {[+ η +]}).
    symmetry.
    transitivity (lts_oba_mo q ⊎ ({[+ η +]} ⊎ mb_without_not_nb mq)).
    multiset_solver. rewrite lts_mb_nb_with_nb_diff;eauto.
    unfold mb.
    erewrite<- lts_mb_nb_spec1;eauto. unfold mb in same_mb. rewrite<- same_mb.
    multiset_solver.
  + edestruct (lts_oba_mo_strip p) as (p' & hwp).
    assert (η ∈ lts_oba_mo p) as Hyp.
    edestruct (lts_oba_mo_strip q) as (q' & hwq).
    destruct (heq p' q' hwp hwq) as (heq' & heqmo). simpl in *.
    assert (η ∈ lts_oba_mo p ⊎ mb_without_not_nb mp) as Hyp'. rewrite heqmo.
    unfold mb.
    erewrite lts_mb_nb_spec1;eauto.  multiset_solver.
    eapply gmultiset_elem_of_disj_union in Hyp' as [hleft | hright].
    ++ multiset_solver.
    ++ eapply lts_mb_nb_with_nb_spec1 in hright as (nb' & mem'). multiset_solver.
    ++ eapply lts_oba_mo_spec_bis2 in Hyp as (p0 & nb1 & hl0).
    exists (p0, mp). split.
    eapply ParLeft. eauto with mdb.
    intros p1 q1 hw1 hw2. simpl in *. split.
    edestruct (heq p' q1); eauto; simpl in *.
    set (heqmo := lts_oba_mo_spec2 _ _ _ nb1 hl0).
    rewrite heqmo in hwp.
    eapply strip_eq_step in hwp as (p4 & hwo4 & heq4); eauto.
    set (h := strip_m_deter hw1 hwo4).
    etrans. eassumption. etrans; eassumption.
    set (heqmo := lts_oba_mo_spec2 _ _ _ nb1 hl0).
    edestruct (heq p' q1) as (equiv & mb_equal); eauto; simpl in *.
    rewrite heqmo in mb_equal.
    assert (mb_without_not_nb ({[+ η +]} ⊎ mq) = {[+ η +]} ⊎ mb_without_not_nb mq) as eq.
    eapply lts_mb_nb_spec1; eauto. rewrite eq in mb_equal.
    replace (lts_oba_mo q ⊎ ({[+ η +]} ⊎ (mb_without_not_nb mq)))
      with ({[+ η +]} ⊎ lts_oba_mo q ⊎ mb_without_not_nb mq) in mb_equal.
    eapply (gmultiset_disj_union_inj_1 ({[+ η +]})). multiset_solver.
    rewrite <- gmultiset_disj_union_assoc.
    rewrite gmultiset_disj_union_comm.
    rewrite <- gmultiset_disj_union_assoc.
    eapply gmultiset_eq_pop_l.
    now rewrite gmultiset_disj_union_comm.
Qed.

Lemma lts_fw_eq_spec_right_blocking_action `{
  M : @gLtsObaFB P A H gLtsP gLtsEqP gLtsObaP}
  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}
   p q mp mq η μ:
  non_blocking η -> dual η μ -> p ▷ mp ≐ q ▷ mq 
    -> p ▷ mp ⟶≐[μ] q ▷ {[+ η +]} ⊎ mq.
Proof.
  intros nb duo heq.
  exists (p ▷ ({[+ η +]} ⊎ mp)). split.
  + eapply ParRight. eapply lts_multiset_add; eauto.
  + constructor; simpl in *. 
    - edestruct heq; simpl in *; eauto.
    - edestruct heq; simpl in *; eauto.
      unfold mb.
      rewrite (lts_mb_nb_spec1 η mp nb).
      rewrite (lts_mb_nb_spec1 η mq nb). multiset_solver.
Qed.

Lemma lts_fw_com_eq_spec `{
  M : @gLtsObaFB P A H gLtsP gLtsEqP gLtsObaP}
  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}
  p q q' mp mq μ η:
  blocking μ -> dual η μ -> non_blocking η -> p ▷ mp ≐ q ▷ {[+ η +]} ⊎ mq -> q ⟶[μ] q' 
    -> p ▷ mp ⟶≐ q' ▷ mq.
Proof.
  intros not_nb duo nb' heq hl.
  edestruct (fw_eq_blocking_action_simulation heq not_nb hl) as (p' & hl' & heq').
  edestruct (lts_oba_mo_strip p) as (p0 & hwp).
  edestruct (lts_oba_mo_strip q) as (q0 & hwq).
  edestruct (heq p0 q0) as (heqp0 & heqm); eauto. simpl in *.
  assert (mb_without_not_nb ({[+ η +]} ⊎ mq) = {[+ η +]} ⊎ mb_without_not_nb mq) as eq;eauto.
  eapply (lts_mb_nb_spec1 η mq nb'). rewrite eq in heqm.
  assert (mem : η ∈ lts_oba_mo p ⊎ (mb_without_not_nb mp)) 
    by (now rewrite heqm; multiset_solver).
  eapply gmultiset_elem_of_disj_union in mem as [hleft | hright].
  - eapply lts_oba_mo_spec_bis2 in hleft as (p1 & nb & hl1).
    assert (neq : μ ≠ η). eapply BlockingAction_are_not_non_blocking; eauto.
    edestruct (lts_oba_non_blocking_action_confluence nb neq hl1 hl') as (p2 & hlp1 & hlp').
    edestruct (lts_oba_fb_feedback nb duo hl1 hlp1) as (p3 & hlp & heqp3).
    exists (p3, mp). split.
    + eapply ParLeft. eauto with mdb.
    + intros ph qh hsph hsqh. simpl in *.
      destruct hlp' as (p2' & hlp2' & heqp2').
      destruct (lts_oba_mo_strip p') as (ph' & hsph').
      destruct (heq' ph' qh) as (heqt0 & heqmt); eauto. simpl in *.
      eapply lts_oba_mo_spec2 in hlp2' as hmeqp2'; eauto.
      assert (heqmu : lts_oba_mo p2' = lts_oba_mo p' ∖ {[+ η +]}) by multiset_solver.
      split.
      ++ eapply lts_oba_mo_spec_bis1 in hlp2' as hmem; eauto.
         eapply gmultiset_disj_union_difference' in hmem.
         rewrite hmem in hsph'.
         eapply strip_eq_step in hsph' as h1; eauto.
         destruct h1 as (p4 & hsu & heqp4).
         symmetry. transitivity ph'. now symmetry. transitivity p4. now symmetry.
         eapply (@strip_eq_sim _ _ _ _ _ _ p2' p3). transitivity p2. assumption. now symmetry.
         eassumption.
         replace (lts_oba_mo p' ∖ {[+ η +]}) with (lts_oba_mo p3). assumption.
         rewrite <- heqmu. eapply lts_oba_mo_eq. transitivity p2. assumption. now symmetry.
      ++ eapply (gmultiset_disj_union_inj_1 {[+ η +]}).
         replace (lts_oba_mo p3) with (lts_oba_mo p2'). rewrite heqmu.
         replace ({[+ η +]} ⊎ (lts_oba_mo q' ⊎ (mb_without_not_nb mq))) with (lts_oba_mo q' ⊎ ({[+ η +]} ⊎ (mb_without_not_nb mq))).
         rewrite <- heqmu. multiset_solver.
         rewrite 2 gmultiset_disj_union_assoc.
         replace (lts_oba_mo q' ⊎ {[+ η +]}) with ({[+ η +]} ⊎ lts_oba_mo q')
           by multiset_solver.
         reflexivity. eapply lts_oba_mo_eq.
         transitivity p2. assumption. now symmetry.
  - eapply lts_mb_nb_with_nb_spec1 in hright as (nb'' & hright);eauto.
    assert (mem : η ∈ mp); eauto.
    eapply gmultiset_disj_union_difference' in hright.
    exists (p' ▷ mp ∖ {[+ η +]}).
    split. rewrite hright at 1.
    eapply ParSync. split; eauto. eauto with mdb. eapply lts_multiset_minus; eauto.
    intros pt qt hw1 hw2. simpl in *.
    edestruct (heq' pt qt) as (heqt0 & heqmt); eauto.
    split; simpl in *; eauto.
    eapply (gmultiset_disj_union_inj_1 {[+ η +]}).
    symmetry.
    assert (mb_without_not_nb ({[+ η +]} ⊎ mq) = {[+ η +]} ⊎ mb_without_not_nb mq) as eq'. 
    eapply lts_mb_nb_spec1;eauto. rewrite eq' in heqmt.
    transitivity (({[+ η +]} ⊎ lts_oba_mo q') ⊎ mb_without_not_nb mq). multiset_solver.
    transitivity ((lts_oba_mo q' ⊎ {[+ η +]}) ⊎ mb_without_not_nb mq). multiset_solver.
    transitivity (lts_oba_mo p' ⊎ mb_without_not_nb mp).
    by now rewrite <- gmultiset_disj_union_assoc.
    symmetry.
    transitivity (lts_oba_mo p' ⊎ {[+ η +]} ⊎  (mb_without_not_nb mp) ∖ {[+ η +]}).
    assert (mb_without_not_nb (mp ∖ {[+ η +]}) = (mb_without_not_nb mp) ∖ {[+ η +]}) as eq''.
    eapply lts_mb_nb_with_nb_diff; eauto.
    rewrite eq''.
    multiset_solver.
    rewrite <- gmultiset_disj_union_assoc.
    f_equal. assert (η ∈ mb_without_not_nb mp). eapply lts_mb_nb_with_nb_spec2; eauto.
    multiset_solver.
Qed.

Lemma lts_fw_eq_spec  `{
  M : @gLtsObaFB P A H gLtsP gLtsEqP gLtsObaP}
  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}
  (p : P) (q : P) (t : P) (mp : mb A) (mq : mb A) (mt : mb A) (α : Act A) :
  (p ▷ mp) ≐ (t ▷ mt) -> (t ▷ mt) ⟶{α} (q ▷ mq)
    -> p ▷ mp ⟶≐{α} q ▷ mq.
Proof.
  intros heq hl. inversion hl as [ | ? ? ? ? Hstep | ] ; subst.
  - eapply lts_fw_eq_spec_left; eauto.
  - destruct α. 
    + destruct (decide (non_blocking μ)) as [nb | not_nb]. 
      ++ eapply (non_blocking_action_in_ms mt μ mq) in nb as equal_mb; eauto.
         eapply lts_fw_eq_spec_right_non_blocking_action; eauto. rewrite equal_mb. eauto. 
      ++ assert (blocking μ) as not_nb'. assumption.
         eapply (blocking_action_in_ms mt μ mq) in not_nb' as (equal_mb & duo & nb); eauto.
         rewrite <-equal_mb.
         eapply lts_fw_eq_spec_right_blocking_action; eauto.
    + inversion Hstep.
  - destruct eq as (duo & nb).
    assert ({[+ μ2 +]} ⊎ mq = mt) as equal_mb.
    apply non_blocking_action_in_ms; eauto.
    eapply lts_fw_com_eq_spec; eauto. eapply dual_blocks; eauto.
    rewrite equal_mb. eauto.
Qed.

(* Our FW Equivalence ≐ is a bissimulation *)

#[global] Program Instance FW_gLtsEq 
  `{M : @gLtsObaFB P A H gLtsP gLtsEqP gLtsObaP}  
  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}
  : gLtsEq (P * mb A) A :=
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
