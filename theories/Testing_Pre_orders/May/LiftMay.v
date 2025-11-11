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

From Coq.Program Require Import Equality.
From stdpp Require Import base countable finite gmap list 
                        finite base decidable finite gmap gmultiset.
From Must Require Import ForAllHelper gLts Bisimulation Lts_OBA Lts_OBA_FB Lts_FW Testing_Predicate 
  May CodePurification Termination 
  InteractionBetweenLts MultisetLTSConstruction ParallelLTSConstruction ForwarderConstruction FiniteImageLTS.
From Must Require Import ActTau.

Lemma may_non_blocking_action_swap_l_fw_eq `{
  @gLtsObaFW P A H gLtsP gLtsEqP gLtsObaP, 
  @gLtsObaFB T A H gLtsT gLtsEqT gLtsObaT, !Testing_Predicate T A outcome}

  `{@Prop_of_Inter P T A parallel_inter H gLtsP gLtsT}

  (p1 p2 : P) (t1 t2 : T) (η : A) :
  non_blocking η -> p1 ⟶⋍[η] p2 -> t1 ⟶⋍[η] t2 -> p1 may_pass t2
    -> p2 may_pass t1.
Proof.
  intros nb tr_server tr_client hmay.
Admitted.

Lemma may_non_blocking_action_swap_r_fw_eq`{
  @gLtsObaFW P A H gLtsP gLtsEqP gLtsObaP, 
  @gLtsObaFB T A H gLtsT gLtsEqT gLtsObaT, !Testing_Predicate T A outcome}

  `{@Prop_of_Inter P T A parallel_inter H gLtsP gLtsT}

  (p1 p2 : P) (t1 t2 : T) (η : A) :
  non_blocking η -> p1 ⟶⋍[η] p2 -> t1 ⟶⋍[η] t2 -> p2 may_pass t1
    -> p1 may_pass t2.
Proof.
  intros nb tr_server tr_client hmay.
Admitted.

Lemma may_non_blocking_action_swap_l_fw `{
  @gLtsObaFW P A H gLtsP gLtsEqP gLtsObaP, 
  @gLtsObaFB T A H gLtsT gLtsEqT gLtsObaT, !Testing_Predicate T A outcome}

  `{@Prop_of_Inter P T A parallel_inter H gLtsP gLtsT}

  (p1 p2 : P) (t1 t2 : T) (η : A) :
  non_blocking η -> p1 ⟶[η] p2 -> t1 ⟶[η] t2 -> p1 may_pass t2 
    -> p2 may_pass t1.
Proof.
  intros. eapply may_non_blocking_action_swap_l_fw_eq; eauto; eexists; split; eauto; reflexivity.
Qed.

Lemma may_non_blocking_action_swap_r_fw `{
  @gLtsObaFW P A H gLtsP gLtsEqP gLtsObaP, 
  @gLtsObaFB T A H gLtsT gLtsEqT gLtsObaT, !Testing_Predicate T A outcome}

  `{@Prop_of_Inter P T A parallel_inter H gLtsP gLtsT}

  (p1 p2 : P) (t1 t2 : T) (η : A) :
  non_blocking η -> p1 ⟶[η] p2 -> t1 ⟶[η] t2 -> may p2 t1
    -> may p1 t2.
Proof.
  intros.
  eapply may_non_blocking_action_swap_r_fw_eq; eauto; eexists; split; eauto; reflexivity.
Qed.

Lemma nf_may_fw_l `{
  @gLtsObaFB P A H gLtsP gLtsEqP gLtsObaP, !FiniteImagegLts P A,
  @gLtsObaFB T A H gLtsT gLtsEqT gLtsObaT, !Testing_Predicate T A outcome}

  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}
  `{@Prop_of_Inter (P * mb A) T A parallel_inter H (inter_lts fw_inter) gLtsT}

  m1 m2 (p : P) (t t' : T) : t ⟿{m1} t' -> (p, m1 ⊎ m2) may_pass t' -> (p, m2) may_pass t.
Proof.
  revert p t t' m2.
  induction m1 using gmultiset_ind; intros p t t' m2 hmo hm.
  - inversion hmo; subst.
    rewrite gmultiset_disj_union_left_id in hm.
    symmetry in eq. eapply may_eq_client; eauto.
    multiset_solver.
  - assert (non_blocking x) as nb. eapply nb_with_strip; eauto. multiset_solver.
    assert (x ∈ {[+ x +]} ⊎ m1) as mem by multiset_solver.
    eapply aux0 in mem as (e0 & l0); eauto.
    eapply (aux3_) in hmo as (t'' & hwo & heq); eauto.
    eapply (may_non_blocking_action_swap_l_fw_eq ).
    exact nb. exists (p ▷ m2). split. 
    apply (ParRight (ActExt x) p ({[+ x +]} ⊎ m2) (m2)).
    unfold lts_step;simpl.
    eapply lts_multiset_minus; eauto. 
    reflexivity. exists e0. split. eassumption. reflexivity.
    eapply IHm1. eassumption. eapply may_eq_client. symmetry. eassumption.
    now replace (m1 ⊎ ({[+ x +]} ⊎ m2)) with ({[+ x +]} ⊎ m1 ⊎ m2) by multiset_solver.
Qed.

Lemma nf_may_fw_r `{
  @gLtsObaFB P A H gLtsP gLtsEqP gLtsObaP, !FiniteImagegLts P A ,
  @gLtsObaFB T A H gLtsT gLtsEqT gLtsObaT, !Testing_Predicate T A outcome}

  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}
  `{@Prop_of_Inter (P * mb A) T A parallel_inter H (inter_lts fw_inter) gLtsT}

  (p : P) (t t' : T) m1 m2 : 
  t ⟿{m1} t' -> (p, m2) may_pass t -> (p, m1 ⊎ m2) may_pass t'.
Proof.
  intro hwo. revert p m2.
  dependent induction hwo; intros q m2 hm.
  rename p into e, q into p.
  - rewrite gmultiset_disj_union_left_id. eapply may_eq_client; eauto.
  - assert (may (q, {[+ η +]} ⊎ m2) p2).
    { admit. }
    replace ({[+ η +]} ⊎ m ⊎ m2) with (m ⊎ ({[+ η +]} ⊎ m2)) by multiset_solver.
    eapply IHhwo. eassumption.
Admitted.

Lemma nf_may_fw `{
  @gLtsObaFB P A H gLtsP gLtsEqP gLtsObaP, !FiniteImagegLts P A ,
  @gLtsObaFB T A H gLtsT gLtsEqT gLtsObaT, !Testing_Predicate T A outcome}

  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}
  `{@Prop_of_Inter (P * mb A) T A parallel_inter H (inter_lts fw_inter) gLtsT}

  (p : P) (t t' : T) m : 
  t ⟿{m} t' -> (p, m) may_pass t' <-> (p, ∅) may_pass t.
Proof.
  intros. split; intro hm.
  - eapply nf_may_fw_l; eauto. now rewrite gmultiset_disj_union_right_id.
  - rewrite <- gmultiset_disj_union_right_id. eapply nf_may_fw_r; eassumption.
Qed.

Lemma may_to_may_fw `{
  @gLtsObaFB P A H gLtsP gLtsEqP gLtsObaP, !FiniteImagegLts P A,
  @gLtsObaFB T A H gLtsT gLtsEqT gLtsObaT, !Testing_Predicate T A outcome}

  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}
  `{@Prop_of_Inter (P * mb A) T A parallel_inter H (inter_lts fw_inter) gLtsT}
  `{@Prop_of_Inter P T A parallel_inter H gLtsP gLtsT}

  (p : P) (t : T) (m : mb A) :
  p may_pass t -> m = lts_oba_mo t -> forall t', t ⟿{m} t' 
    -> (p, m) may_pass t'.
Proof.
  intros hm. revert m.
  dependent induction hm.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Lemma may_fw_to_may `{
  @gLtsObaFB P A H gLtsP gLtsEqP gLtsObaP, !FiniteImagegLts P A,
  @gLtsObaFB T A H gLtsT gLtsEqT gLtsObaT, !Testing_Predicate T A outcome}

  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}
  `{@Prop_of_Inter (P * mb A) T A parallel_inter H (inter_lts fw_inter) gLtsT}
  `{@Prop_of_Inter P T A parallel_inter H gLtsP gLtsT}

  (p : P) (t : T) :
  (p, ∅) may_pass t -> p may_pass t.
Proof.
  intro hm. dependent induction hm.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Lemma may_iff_may_fw `{
  @gLtsObaFB P A H gLtsP gLtsEqP gLtsObaP, !FiniteImagegLts P A,
  @gLtsObaFB T A H gLtsT gLtsEqT gLtsObaT, !Testing_Predicate T A outcome}

  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}
  `{@Prop_of_Inter (P * mb A) T A parallel_inter H (inter_lts fw_inter) gLtsT}
  `{@Prop_of_Inter P T A parallel_inter H gLtsP gLtsT}

  (p : P) (t : T) :
  p may_pass t <-> (p, ∅) may_pass t.
Proof.
  split; intro hm.
  - edestruct (lts_oba_mo_strip t) as (t' & hmo).
    eapply nf_may_fw_l. eassumption.
    rewrite gmultiset_disj_union_right_id.
    eapply may_to_may_fw. eassumption. reflexivity. eassumption.
  - eapply may_fw_to_may; eauto.
Qed.

Lemma lift_fw_ctx_pre `{
    @gLtsObaFB P A H gLtsP gLtsEqP gLtsObaP, !FiniteImagegLts P A,
    @gLtsObaFB Q A H gLtsQ gLtsEqQ gLtsObaQ, !FiniteImagegLts Q A,
    @gLtsObaFB T A H gLtsT gLtsEqT gLtsObaT, !Testing_Predicate T A outcome}

  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}

  `{@Prop_of_Inter (P * mb A) T A parallel_inter H (inter_lts fw_inter) gLtsT}

  `{@Prop_of_Inter P T A parallel_inter H gLtsP gLtsT}

  `{@Prop_of_Inter Q (mb A) A fw_inter H gLtsQ MbgLts}

  `{@Prop_of_Inter (Q * mb A) T A parallel_inter H (inter_lts fw_inter) gLtsT}

  `{@Prop_of_Inter Q T A parallel_inter H gLtsQ gLtsT}

  (p : P) (q : Q) : p ⊑ₘₐᵧ q <-> (p, ∅) ⊑ₘₐᵧ (q, ∅).
Proof.
  split; intros hctx e hm%may_iff_may_fw. 
  - rewrite <- may_iff_may_fw. eauto.
  - rewrite may_iff_may_fw. eauto.
Qed.
