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

From Stdlib.Program Require Import Equality.
From stdpp Require Import gmultiset.
From TestingTheory Require Import gLts Bisimulation Lts_OBA Lts_OBA_FB Lts_FW Testing_Predicate May CodePurification InteractionBetweenLts MultisetLTSConstruction ForwarderConstruction FiniteImageLTS ActTau Lts_Finite_Output_Chain.

Lemma may_non_blocking_action_swap_l_fw_eq `{
   @gLtsObaFW P A H gLtsEqP gLtsObaP, 
  !@gLtsObaFB T A H gLtsEqT gLtsObaT, !Testing_Predicate outcome _}

  {_ : Prop_of_Inter P T A dual}

  (p1 p2 : P) (t1 t2 : T) (η : A) :
  non_blocking η -> p1 ⟶⋍[η] p2 -> t1 ⟶⋍[η] t2 -> p1 may_pass t2
    -> p2 may_pass t1.
Proof.
  intros nb tr_server tr_client hmay.
  revert  t1 p2 η nb tr_server tr_client.
  induction hmay as [p t happy | p t p' nh pt hmay IH | p t t' nh et hmay IH
                     | p t p' μ1 t' μ2 nh inter trS trC hmay IH]; intros t1 p2 η nb tr_server tr_client.
  + eapply may_now. destruct tr_client as (t'1 & tr & equiv).
    eapply outcome_preserved_by_lts_non_blocking_action_converse;eauto.
    eapply outcome_preserved_by_eq; eauto. now symmetry.
  + assert (nh1 : ¬ outcome t1).
    { intro h. destruct tr_client as (t1' & trc & eqc).
      apply nh. eapply outcome_preserved_by_eq.
      eapply outcome_preserved_by_lts_non_blocking_action; eauto.
      eassumption. }
    destruct tr_server as (p'2  & tr_server & equiv).
    edestruct (nb_tau nb tr_server pt)
      as [(w & trw & r2 & trr2 & eqr2) |(β & duo & w & trw & eqw)].
    * edestruct (eq_spec p2 w τ) as (q2 & trq2 & eqq2).
      { exists p'2. split. now symmetry. eassumption. }
      eapply (may_server_step _ _ q2); eauto.
      eapply may_eq_server. etransitivity. eapply eqr2. symmetry. eapply eqq2.
      eapply IH; eauto. exists r2. split. eassumption. reflexivity.
    * edestruct (eq_spec p2 w (ActExt β)) as (w2 & trw2 & eqw2).
      { exists p'2. split. now symmetry. eassumption. }
      destruct tr_client as (t1' & hlt1' & heqt1').
      eapply (may_com_step _ _ w2 β t1' η nh1 duo trw2 hlt1').
      assert (heqp' : p' ⋍ w2) by (symmetry; etransitivity; [eapply eqw2 | eapply eqw]).
      eapply may_eq_server. eapply heqp'.
      eapply may_eq_client. symmetry. eapply heqt1'.
      eassumption.
  + assert (nh1 : ¬ outcome t1).
    { intro h. destruct tr_client as (t1' & trc & eqc).
      apply nh. eapply outcome_preserved_by_eq.
      eapply outcome_preserved_by_lts_non_blocking_action; eauto.
      eassumption. }
    destruct tr_client as (t1' & hlt1' & heqt1').
    edestruct (eq_spec t1' t' τ) as (w & trw & eqw).
    { exists t. split. now symmetry. eassumption. }
    edestruct (nb_delay nb hlt1' trw) as (s & news & sw).
    destruct sw as (w2 & sw2 & eqw2).
    eapply (may_client_step _ _ s); eauto.
    eapply IH; eauto. exists w2. split. eassumption. etransitivity. eassumption. eassumption.
  + assert (nh1 : ¬ outcome t1).
    { intro h. destruct tr_client as (t1' & trc & eqc).
      apply nh. eapply outcome_preserved_by_eq.
      eapply outcome_preserved_by_lts_non_blocking_action; eauto.
      eassumption. }
    destruct tr_server as (p'2 & hlp'2 & heqp'2).
    destruct tr_client as (t1' & hlt1' & heqt1').
    destruct (decide (μ1 = η)) as [eq | neq]; subst.
    * assert (eqp' : p'2 ⋍ p') by (eapply nb_determinacy; eauto).
      assert (duo' : dual μ2 η) by (symmetry; eauto).
      edestruct (eq_spec t1' t' (ActExt μ2)) as (t1'' & hlt1'' & heqt1'').
      { exists t. split. now symmetry. eassumption. }
      edestruct (feedback nb duo' hlt1' hlt1'') as (w & tauw & eqw).
      eapply (may_client_step _ _ w); eauto.
      assert (heqp'p2 : p' ⋍ p2) by (etransitivity; [symmetry; eapply eqp' | eapply heqp'2]).
      assert (heqt'w : t' ⋍ w) by (symmetry; etransitivity; [eapply eqw | eapply heqt1'']).
      eapply may_eq_server. eapply heqp'p2.
      eapply may_eq_client. eapply heqt'w.
      eassumption.
    * edestruct (nb_confluence nb neq hlp'2 trS) as (r & trR & rest).
      destruct rest as (r2 & trR2' & eqR2r).
      edestruct (eq_spec p2 r (ActExt μ1)) as (r3 & trR3 & eqR3).
      { exists p'2. split. now symmetry. eassumption. }
      edestruct (eq_spec t1' t' (ActExt μ2)) as (t1'' & hlt1'' & heqt1'').
      { exists t. split. now symmetry. eassumption. }
      edestruct (nb_delay nb hlt1' hlt1'') as (w & trW & ww).
      destruct ww as (w2 & trW2 & eqW2).
      eapply (may_com_step _ _ r3 μ1 w μ2 nh1 inter trR3 trW).
      assert (heqr2r3 : r2 ⋍ r3) by (etransitivity; [eapply eqR2r | symmetry; eapply eqR3]).
      eapply (may_eq_server r2 r3 w heqr2r3).
      eapply (IH w r2 η nb).
      - exists r2. split. exact trR2'. reflexivity.
      - exists w2. split. exact trW2. etransitivity. exact eqW2. exact heqt1''.
Qed.

Lemma may_non_blocking_action_swap_r_fw_eq`{
  @gLtsObaFW P A H gLtsEqP gLtsObaP, 
  @gLtsObaFB T A H gLtsEqT gLtsObaT, !Testing_Predicate outcome _}

  {_ : Prop_of_Inter P T A dual}

  (p1 p2 : P) (t1 t2 : T) (η : A) :
  non_blocking η -> p1 ⟶⋍[η] p2 -> t1 ⟶⋍[η] t2 -> p2 may_pass t1
    -> p1 may_pass t2.
Proof.
  intros nb tr_server tr_client hmay.
  revert t2 p1 η nb tr_server tr_client.
  induction hmay as [p t happy | p t p' nh pt hmay IH | p t t' nh et hmay IH
                     | p t p' μ1 t' μ2 nh inter trS trC hmay IH]; intros t2 p1 η nb tr_server tr_client.
  + eapply may_now. destruct tr_client as (t2' & hlt2' & heqt2').
    eapply outcome_preserved_by_eq.
    eapply outcome_preserved_by_lts_non_blocking_action; eauto.
    eassumption.
  + assert (nh1 : ¬ outcome t2).
    { intro h. destruct tr_client as (t2' & trc & eqc).
      apply nh.
      eapply outcome_preserved_by_lts_non_blocking_action_converse.
      eassumption. eassumption.
      eapply outcome_preserved_by_eq.
      eassumption. symmetry. eassumption. }
    destruct tr_server as (p0 & hlp0 & heqp0).
    edestruct (eq_spec p0 p' τ) as (w & trw & eqw).
    { exists p. split. now symmetry. eassumption. }
    edestruct (nb_delay nb hlp0 trw) as (s & news & sw).
    destruct sw as (s2 & trs2 & eqs2).
    eapply (may_server_step _ _ s nh1 news).
    eapply (IH t2 s η nb).
    - exists s2. split. exact trs2. etransitivity. exact eqs2. exact eqw.
    - eassumption.
  + assert (nh1 : ¬ outcome t2).
    { intro h. destruct tr_client as (t2' & trc & eqc).
      apply nh.
      eapply outcome_preserved_by_lts_non_blocking_action_converse.
      eassumption. eassumption.
      eapply outcome_preserved_by_eq.
      eassumption. symmetry. eassumption. }
    destruct tr_client as (t2' & hlt2' & heqt2').
    edestruct (nb_tau nb hlt2' et) as [(w & trw & r2 & trr2 & eqr2) | (β & duo & w & trw & eqw)].
    * edestruct (eq_spec t2 w τ) as (q2 & trq2 & eqq2).
      { exists t2'. split. now symmetry. eassumption. }
      eapply (may_client_step _ _ q2 nh1 trq2).
      eapply (IH q2 p1 η nb tr_server).
      exists r2. split. exact trr2. etransitivity. eapply eqr2. symmetry. eapply eqq2.
    * edestruct (eq_spec t2 w (ActExt β)) as (w2 & trw2 & eqw2).
      { exists t2'. split. now symmetry. eassumption. }
      destruct tr_server as (p0 & hlp0 & heqp0).
      eapply (may_com_step _ _ p0 η w2 β nh1).
      - now symmetry.
      - exact hlp0.
      - exact trw2.
      - assert (heqw2t' : w2 ⋍ t') by (etransitivity; [eapply eqw2 | eapply eqw]).
        eapply may_eq_server. symmetry. eapply heqp0.
        eapply may_eq_client. symmetry. eapply heqw2t'.
        eassumption.
  + assert (nh1 : ¬ outcome t2).
    { intro h. destruct tr_client as (t2' & trc & eqc).
      apply nh.
      eapply outcome_preserved_by_lts_non_blocking_action_converse.
      eassumption. eassumption.
      eapply outcome_preserved_by_eq.
      eassumption. symmetry. eassumption. }
    destruct tr_server as (p0 & hlp0 & heqp0).
    destruct tr_client as (t2' & hlt2' & heqt2').
    destruct (decide (μ2 = η)) as [eq | neq]; subst.
    * pose proof (nb_determinacy nb hlt2' trC) as eqt'.
      edestruct (eq_spec p0 p' (ActExt μ1)) as (p0'' & hlp0'' & heqp0'').
      { exists p. split. now symmetry. eassumption. }
      destruct (fwd_feedback nb inter hlp0 hlp0'') as [(p3 & hlp3 & heqp3) | heqdirect].
      -- assert (heqp3p' : p3 ⋍ p') by (etransitivity; [eapply heqp3 | eapply heqp0'']).
         assert (heqt'2t2 : t' ⋍ t2) by (etransitivity; [symmetry; eapply eqt' | eapply heqt2']).
         eapply (may_server_step _ _ p3 nh1 hlp3).
         eapply may_eq_server. symmetry. eapply heqp3p'.
         eapply may_eq_client. eapply heqt'2t2.
         eassumption.
      -- assert (heqp1p' : p1 ⋍ p') by (etransitivity; [eapply heqdirect | eapply heqp0'']).
         assert (heqt'2t2 : t' ⋍ t2) by (etransitivity; [symmetry; eapply eqt' | eapply heqt2']).
         eapply may_eq_server. symmetry. eapply heqp1p'.
         eapply may_eq_client. eapply heqt'2t2.
         eassumption.
    * edestruct (nb_confluence nb neq hlt2' trC) as (r & trR & rest).
      destruct rest as (r2 & trr2 & eqr2r).
      edestruct (eq_spec t2 r (ActExt μ2)) as (r3 & trR3 & eqR3).
      { exists t2'. split. now symmetry. eassumption. }
      edestruct (eq_spec p0 p' (ActExt μ1)) as (w & trw & eqw).
      { exists p. split. now symmetry. eassumption. }
      edestruct (nb_delay nb hlp0 trw) as (s2 & trS2 & ss).
      destruct ss as (w2 & trW2 & eqW2).
      eapply (may_com_step _ _ s2 μ1 r3 μ2 nh1 inter trS2 trR3).
      assert (heqr2r3 : r2 ⋍ r3) by (etransitivity; [eapply eqr2r | symmetry; eapply eqR3]).
      assert (heqs2p' : s2 ⟶⋍[η] p').
      { exists w2. split. exact trW2. etransitivity. eapply eqW2. eapply eqw. }
      eapply (IH r3 s2 η nb heqs2p').
      exists r2. split. exact trr2. exact heqr2r3.
Qed.

Lemma may_non_blocking_action_swap_l_fw `{
  @gLtsObaFW P A H gLtsEqP gLtsObaP, 
  @gLtsObaFB T A H gLtsEqT gLtsObaT, !Testing_Predicate outcome _}

  {_ : Prop_of_Inter P T A dual}

  (p1 p2 : P) (t1 t2 : T) (η : A) :
  non_blocking η -> p1 ⟶[η] p2 -> t1 ⟶[η] t2 -> p1 may_pass t2 
    -> p2 may_pass t1.
Proof.
  intros. eapply may_non_blocking_action_swap_l_fw_eq; eauto; eexists; split; eauto; reflexivity.
Qed.

Lemma may_non_blocking_action_swap_r_fw `{
  @gLtsObaFW P A H gLtsEqP gLtsObaP, 
  @gLtsObaFB T A H gLtsEqT gLtsObaT, !Testing_Predicate outcome _}

  {_ : Prop_of_Inter P T A dual}

  (p1 p2 : P) (t1 t2 : T) (η : A) :
  non_blocking η -> p1 ⟶[η] p2 -> t1 ⟶[η] t2 -> may p2 t1
    -> may p1 t2.
Proof.
  intros.
  eapply may_non_blocking_action_swap_r_fw_eq; eauto; eexists; split; eauto; reflexivity.
Qed.

Lemma nf_may_fw_l `{
  @gLtsObaFB P A H gLtsEqP gLtsObaP, !FiniteOutputChain_LtsOba P, !FiniteImagegLts P A,
  @gLtsObaFB T A H gLtsEqT gLtsObaT, !Testing_Predicate outcome _}

  {_ : Prop_of_Inter P (MO A) A fw_inter}
  {_ : Prop_of_Inter (P * MO A) T A dual}

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
  @gLtsObaFB P A H gLtsEqP gLtsObaP, !FiniteImagegLts P A ,
  @gLtsObaFB T A H gLtsEqT gLtsObaT, !Testing_Predicate outcome _}

  {_ : Prop_of_Inter P (MO A) A fw_inter}
  {_ : Prop_of_Inter (P * MO A) T A dual}

  (p : P) (t t' : T) m1 m2 : 
  t ⟿{m1} t' -> (p, m2) may_pass t -> (p, m1 ⊎ m2) may_pass t'.
Proof.
  intro hwo. revert p m2.
  dependent induction hwo; intros q m2 hm.
  rename p into e, q into p.
  - rewrite gmultiset_disj_union_left_id. eapply may_eq_client; eauto.
  - assert (step2 : q ▷ ({[+ η +]} ⊎ m2) may_pass p2).
    { assert (Hgen: forall (rp : P * MO A) (t1 t2 : T),
        non_blocking η -> t1 ⟶[η] t2 -> rp may_pass t1 -> (fst rp, {[+ η +]} ⊎ snd rp) may_pass t2).
      { intros rp t1 t2 Hnb Htr hm2.
        revert t2 Hnb Htr.
        induction hm2 as [rp t0 Hout | rp t1' rp' nh pt hm2 IH | rp t1' t1'' nh et hm2 IH
                          | rp t1' rp' μ1 t1'' μ2 nh inter trS trC hm2 IH]; intros t2 Hnb Htr.
        - eapply may_now.
          eapply outcome_preserved_by_lts_non_blocking_action; eassumption.
        - destruct rp as [r mr].
          destruct rp' as [r' mr'].
          simpl in *.
          eapply (may_server_step _ _ (r', {[+ η +]} ⊎ mr')).
          + eapply unoutcome_preserved_by_lts_non_blocking_action; eassumption.
          + eapply add_in_MO_fw_tau.
            exact pt.
          + apply IH; assumption.
        - assert (nh2 : ¬ outcome t2) by (eapply unoutcome_preserved_by_lts_non_blocking_action; [exact Hnb | exact Htr | exact nh]).
          destruct rp as [r mr].
          simpl in *.
          edestruct (nb_tau (p:=t1') (q1:=t2) (q2:=t1'') (η:=η) Hnb Htr et) as [(w & trw & w0 & trw0 & eqw0) | (β & duo & w & trw & eqw)].
          eapply (may_client_step _ _ w).
          exact nh2.
          exact trw.
          eapply may_eq_client.
          exact eqw0.
          apply IH; [exact Hnb | exact trw0].
          eapply (may_com_step _ _ (r, mr) η w β).
          exact nh2.
          symmetry; exact duo.
          eapply (ParRight (ActExt η) r ({[+ η +]} ⊎ mr) mr).
          unfold lts_step; simpl.
          eapply lts_multiset_minus; eauto.
          exact trw.
          eapply may_eq_client.
          symmetry; exact eqw.
          exact hm2.
        - destruct (decide (μ2 = η)) as [eq | neq]; subst.
          assert (heq_t : t1'' ⋍ t2) by (eapply nb_determinacy; [exact Hnb | exact trC | exact Htr]).
          assert (nh2 : ¬ outcome t2) by (eapply unoutcome_preserved_by_lts_non_blocking_action; [exact Hnb | exact Htr | exact nh]).
          destruct rp as [r mr].
          destruct rp' as [r' mr'].
          simpl in *.
          inversion trS as [a a1 a2 b l Heq1 Heq2 | a a1 b1 b2 l Heq1 Heq2 | μa μb a1 a2 b1 b2 fwi l1 l2 Heq1 Heq2]; subst.
          + eapply (may_server_step _ _ (r' ▷ mr')).
            exact nh2.
            eapply ParSync.
            exact (conj inter Hnb).
            exact l.
            eapply lts_multiset_minus; eauto.
            eapply may_eq_client.
            exact heq_t.
            exact hm2.
          + inversion l as [mm ζ μc duo' nb' Heq3 Heq4 | mm ζ nb' Heq3 Heq4]; subst.
            assert (Hextra: forall (rp0 : P * MO A) (t0 : T) (extra : MO A), rp0 may_pass t0 -> (fst rp0, extra ⊎ snd rp0) may_pass t0).
            intros rp0 t0 extra hm3.
            revert extra.
            induction hm3 as [rp0 t0 Hout | rp0 t0 rp0' nh0 pt0 hm3 IH0 | rp0 t0 t0' nh0 et0 hm3 IH0
                              | rp0 t0 rp0' μ1' t0' μ2' nh0 inter0 trS0 trC0 hm3 IH0]; intro extra.
            eapply may_now; exact Hout.
            destruct rp0 as [r0 mr0].
            destruct rp0' as [r0' mr0'].
            simpl in *.
            eapply (may_server_step _ _ (r0', extra ⊎ mr0')).
            exact nh0.
            eapply add_in_MO_fw_tau.
            exact pt0.
            apply IH0.
            eapply (may_client_step _ _ t0').
            exact nh0.
            exact et0.
            apply IH0.
            destruct rp0 as [r0 mr0].
            destruct rp0' as [r0' mr0'].
            simpl in *.
            eapply (may_com_step _ _ (r0', extra ⊎ mr0') μ1' t0' μ2').
            exact nh0.
            exact inter0.
            eapply add_in_MO_fw_action.
            exact trS0.
            exact trC0.
            apply IH0.
            assert (Heqz : ζ = η) by (rewrite (unique_nb ζ μ1 duo'); rewrite (unique_nb η μ1 inter); reflexivity).
            subst ζ.
            eapply may_eq_client.
            exact heq_t.
            exact hm2.
            assert (Hextra: forall (rp0 : P * MO A) (t0 : T) (extra : MO A), rp0 may_pass t0 -> (fst rp0, extra ⊎ snd rp0) may_pass t0).
            intros rp0 t0 extra hm3.
            revert extra.
            induction hm3 as [rp0 t0 Hout | rp0 t0 rp0' nh0 pt0 hm3 IH0 | rp0 t0 t0' nh0 et0 hm3 IH0
                              | rp0 t0 rp0' μ1' t0' μ2' nh0 inter0 trS0 trC0 hm3 IH0]; intro extra.
            eapply may_now; exact Hout.
            destruct rp0 as [r0 mr0].
            destruct rp0' as [r0' mr0'].
            simpl in *.
            eapply (may_server_step _ _ (r0', extra ⊎ mr0')).
            exact nh0.
            eapply add_in_MO_fw_tau.
            exact pt0.
            apply IH0.
            eapply (may_client_step _ _ t0').
            exact nh0.
            exact et0.
            apply IH0.
            destruct rp0 as [r0 mr0].
            destruct rp0' as [r0' mr0'].
            simpl in *.
            eapply (may_com_step _ _ (r0', extra ⊎ mr0') μ1' t0' μ2').
            exact nh0.
            exact inter0.
            eapply add_in_MO_fw_action.
            exact trS0.
            exact trC0.
            apply IH0.
            assert (hm2' : r' ▷ mr' may_pass t2) by (eapply may_eq_client; [exact heq_t | exact hm2]).
            pose proof (Hextra (r', mr') t2 ({[+ η +]} ⊎ {[+ μ1 +]}) hm2') as Hres.
            simpl in Hres.
            replace ({[+ η +]} ⊎ {[+ μ1 +]} ⊎ mr') with ({[+ η +]} ⊎ ({[+ μ1 +]} ⊎ mr')) in Hres by multiset_solver.
            exact Hres.
          + assert (nh2 : ¬ outcome t2) by (eapply unoutcome_preserved_by_lts_non_blocking_action; [exact Hnb | exact Htr | exact nh]).
            destruct rp as [r mr].
            destruct rp' as [r' mr'].
            simpl in *.
            edestruct (nb_confluence (p:=t1') (q1:=t2) (q2:=t1'') (η:=η) (μ:=μ2) Hnb neq Htr trC) as (w & trW & w2 & trW2 & eqW2).
            eapply (may_com_step _ _ (r', {[+ η +]} ⊎ mr') μ1 w μ2).
            exact nh2.
            exact inter.
            eapply add_in_MO_fw_action.
            exact trS.
            exact trW.
            eapply may_eq_client.
            exact eqW2.
            apply IH.
            exact Hnb.
            exact trW2.
      }
      apply (Hgen (q, m2) p1 p2 H2 H3 hm). }
    replace ({[+ η +]} ⊎ m ⊎ m2) with (m ⊎ ({[+ η +]} ⊎ m2)) by multiset_solver.
    eapply IHhwo. eassumption.
Qed.

Lemma nf_may_fw `{
  @gLtsObaFB P A H gLtsEqP gLtsObaP, !FiniteOutputChain_LtsOba P, !FiniteImagegLts P A ,
  @gLtsObaFB T A H gLtsEqT gLtsObaT, !Testing_Predicate outcome _}

  {_ : Prop_of_Inter P (MO A) A fw_inter}
  {_ : Prop_of_Inter (P * MO A) T A dual}

  (p : P) (t t' : T) m : 
  t ⟿{m} t' -> (p, m) may_pass t' <-> (p, ∅) may_pass t.
Proof.
  intros. split; intro hm.
  - eapply nf_may_fw_l; eauto. now rewrite gmultiset_disj_union_right_id.
  - rewrite <- gmultiset_disj_union_right_id. eapply nf_may_fw_r; eassumption.
Qed.

Lemma may_to_may_fw `{
  @gLtsObaFB P A H gLtsEqP gLtsObaP, !FiniteOutputChain_LtsOba P, !FiniteImagegLts P A,
  @gLtsObaFB T A H gLtsEqT gLtsObaT, !FiniteOutputChain_LtsOba T, !Testing_Predicate outcome _}

  {_ : Prop_of_Inter P (MO A) A fw_inter}
  {_ : Prop_of_Inter (P * MO A) T A dual}
  {_ : Prop_of_Inter P T A dual}

  (p : P) (t : T) (m : MO A) :
  p may_pass t -> m = lts_oba_mo t -> forall t', t ⟿{m} t' 
    -> (p, m) may_pass t'.
Proof.
  intros hm. revert m.
  dependent induction hm.
  - intros m heq t' hmo.
    eapply may_now.
    eapply woutpout_preserves_outcome; eauto.
  - intros m heq t' hmo.
    eapply (may_server_step _ _ (p' ▷ m)).
    intro hh.
    eapply nh.
    eapply woutpout_preserves_outcome_converse; eauto.
    pose proof (add_in_MO_fw_tau m p ∅ p' ∅ (ParLeft τ p p' ∅ pt)) as l1.
    replace (m ⊎ ∅) with m in l1 by multiset_solver.
    exact l1.
    apply IHhm; auto.
  - intros m heq t'0 hmo.
    subst m.
    destruct (lts_oba_mo_strip t') as (t'' & hwo'').
    pose proof (IHhm (lts_oba_mo t') eq_refl t'' hwo'') as hm1.
    assert (hm_fw : p ▷ ∅ may_pass t').
    { pose proof (nf_may_fw_l (lts_oba_mo t') ∅ p t' t'' hwo'') as hstep.
      rewrite gmultiset_disj_union_right_id in hstep.
      apply hstep.
      exact hm1. }
    destruct (decide (outcome t'0)) as [hgood | hbad].
    eapply may_now; exact hgood.
    edestruct (strip_delay_tau hmo et) as [(η & μ & r & duo & nb & l1 & l2) | (r & w & l1 & hwo & heqw)].
    pose proof (lts_oba_mo_spec2 t η r nb l1) as heqmo.
    rewrite heqmo.
    rewrite heqmo in hmo.
    destruct l2 as (r' & trR & heqR).
    assert (nhr : ¬ outcome r) by (eapply unoutcome_preserved_by_lts_non_blocking_action; [exact nb | exact l1 | exact nh]).
    assert (hstep0' : (p, {[+ η +]} ⊎ ∅) may_pass r).
    { eapply (may_com_step _ _ (p, ∅) η r' μ).
      exact nhr.
      symmetry; exact duo.
      eapply ParRight.
      eapply lts_multiset_minus; eauto.
      exact trR.
      eapply may_eq_client.
      symmetry; exact heqR.
      exact hm_fw. }
    destruct (aux3_ hmo r l1) as (s & hwos & heqs).
    pose proof (nf_may_fw_r p r s (lts_oba_mo r) ({[+ η +]} ⊎ ∅) hwos hstep0') as hfinal.
    replace (lts_oba_mo r ⊎ ({[+ η +]} ⊎ ∅)) with ({[+ η +]} ⊎ lts_oba_mo r) in hfinal by multiset_solver.
    eapply may_eq_client.
    exact heqs.
    exact hfinal.
    pose proof (nf_may_fw_r p t' w (lts_oba_mo t) ∅ hwo hm_fw) as hfinal2.
    rewrite gmultiset_disj_union_right_id in hfinal2.
    eapply (may_client_step _ _ r).
    exact hbad.
    exact l1.
    eapply may_eq_client.
    exact heqw.
    exact hfinal2.
  - intros m heq t'0 hmo.
    subst m.
    destruct (decide (non_blocking μ2)) as [nb | nnb].
    pose proof (lts_oba_mo_spec2 t μ2 t' nb trC) as heqmo.
    rewrite heqmo.
    rewrite heqmo in hmo.
    destruct (aux3_ hmo t' trC) as (s & hwos & heqs).
    pose proof (IHhm (lts_oba_mo t') eq_refl s hwos) as hm2.
    assert (nht' : ¬ outcome t') by (eapply unoutcome_preserved_by_lts_non_blocking_action; [exact nb | exact trC | exact nh]).
    assert (nhs : ¬ outcome s) by (intro hcontra; apply nht'; eapply woutpout_preserves_outcome_converse; [exact hcontra | exact hwos]).
    assert (hnh : ¬ outcome t'0) by (eapply unoutcome_preserved_by_eq; [exact nhs | symmetry; exact heqs]).
    eapply (may_server_step _ _ (p', lts_oba_mo t')).
    exact hnh.
    eapply ParSync.
    exact (conj inter nb).
    exact trS.
    eapply lts_multiset_minus; eauto.
    eapply may_eq_client.
    exact heqs.
    exact hm2.
    destruct (decide (non_blocking μ1)) as [nb1 | nnb1].
    assert (mem : μ2 ∉ lts_oba_mo t) by (eapply lts_oba_mo_non_blocking_contra; exact nnb).
    destruct (strip_delay_m mem hmo trC) as (r' & hwor').
    destruct (strip_delay_inp4 nnb trC hwor') as (r & hwor & hr).
    pose proof (strip_m_deter hmo hwor) as heqr.
    destruct hr as (r2 & trR2 & heqR2).
    edestruct (eq_spec t'0 r2 (ActExt μ2)) as (r3 & trR3 & heqR3).
    exists r.
    split; [exact heqr | exact trR2].
    assert (heqR3' : r3 ⋍ r') by (etransitivity; [exact heqR3 | exact heqR2]).
    destruct (lts_oba_mo_strip t') as (t'' & hwo'').
    pose proof (IHhm (lts_oba_mo t') eq_refl t'' hwo'') as hm1.
    assert (hm_fw : p' ▷ ∅ may_pass t').
    { pose proof (nf_may_fw_l (lts_oba_mo t') ∅ p' t' t'' hwo'') as hstep.
      rewrite gmultiset_disj_union_right_id in hstep.
      apply hstep.
      exact hm1. }
    pose proof (nf_may_fw_r p' t' r' (lts_oba_mo t) ∅ hwor' hm_fw) as hstep2.
    rewrite gmultiset_disj_union_right_id in hstep2.
    assert (nht'0 : ¬ outcome t'0) by (intro hcontra; apply nh; eapply woutpout_preserves_outcome_converse; [exact hcontra | exact hmo]).
    assert (trSlift : (p, lts_oba_mo t ⊎ ∅) ⟶[μ1] (p', lts_oba_mo t ⊎ ∅)) by (eapply add_in_MO_fw_action; eapply ParLeft; exact trS).
    rewrite gmultiset_disj_union_right_id in trSlift.
    eapply (may_com_step _ _ (p', lts_oba_mo t) μ1 r3 μ2).
    exact nht'0.
    exact inter.
    exact trSlift.
    exact trR3.
    eapply may_eq_client.
    symmetry; exact heqR3'.
    exact hstep2.
    assert (mem : μ2 ∉ lts_oba_mo t) by (eapply lts_oba_mo_non_blocking_contra; exact nnb).
    destruct (strip_delay_m mem hmo trC) as (r' & hwor').
    destruct (strip_delay_inp4 nnb trC hwor') as (r & hwor & hr).
    pose proof (strip_m_deter hmo hwor) as heqr.
    destruct hr as (r2 & trR2 & heqR2).
    edestruct (eq_spec t'0 r2 (ActExt μ2)) as (r3 & trR3 & heqR3).
    exists r.
    split; [exact heqr | exact trR2].
    assert (heqR3' : r3 ⋍ r') by (etransitivity; [exact heqR3 | exact heqR2]).
    destruct (lts_oba_mo_strip t') as (t'' & hwo'').
    pose proof (IHhm (lts_oba_mo t') eq_refl t'' hwo'') as hm1.
    assert (hm_fw : p' ▷ ∅ may_pass t').
    { pose proof (nf_may_fw_l (lts_oba_mo t') ∅ p' t' t'' hwo'') as hstep.
      rewrite gmultiset_disj_union_right_id in hstep.
      apply hstep.
      exact hm1. }
    pose proof (nf_may_fw_r p' t' r' (lts_oba_mo t) ∅ hwor' hm_fw) as hstep2.
    rewrite gmultiset_disj_union_right_id in hstep2.
    assert (nht'0 : ¬ outcome t'0) by (intro hcontra; apply nh; eapply woutpout_preserves_outcome_converse; [exact hcontra | exact hmo]).
    assert (trSlift : (p, lts_oba_mo t ⊎ ∅) ⟶[μ1] (p', lts_oba_mo t ⊎ ∅)) by (eapply add_in_MO_fw_action; eapply ParLeft; exact trS).
    rewrite gmultiset_disj_union_right_id in trSlift.
    eapply (may_com_step _ _ (p', lts_oba_mo t) μ1 r3 μ2).
    exact nht'0.
    exact inter.
    exact trSlift.
    exact trR3.
    eapply may_eq_client.
    symmetry; exact heqR3'.
    exact hstep2.
Qed.

Lemma may_fw_to_may_gen `{
  @gLtsObaFB P A H gLtsEqP gLtsObaP, !FiniteImagegLts P A,
  @gLtsObaFB T A H gLtsEqT gLtsObaT, !Testing_Predicate outcome _}

  {_ : Prop_of_Inter P (MO A) A fw_inter}
  {_ : Prop_of_Inter (P * MO A) T A dual}
  {_ : Prop_of_Inter P T A dual}

  (p : P) (m : gmultiset A) (t0 t : T) :
  t0 ⟿{m} t -> (p, m) may_pass t -> p may_pass t0.
Proof.
  intros hstrip hm.
  remember (p, m) as q eqn:Heqq.
  revert p m Heqq t0 hstrip.
  induction hm as [q t Hout | q t q' nh pt hmay IH | q t t' nh et hmay IH | q t q' μ1 t' μ2 nh inter trS trC hmay IH];
    intros p m Heqq t0 hstrip.
  apply may_now.
  eapply woutpout_preserves_outcome_converse; eauto.
  subst q.
  inversion pt as [α a1 a2 b l Heq1 Heq2 | α a b1 b2 l Heq1 Heq2 | μa μb a1 a2 b1 b2 eqfw l1 l2 Heq1 Heq2]; subst.
  2: inversion l.
  eapply may_server_step.
  + intro hc. apply nh. eapply woutpout_preserves_outcome; eauto.
  + exact l.
  + eapply IH; eauto.
  + destruct eqfw as [duo nb].
    assert (heqm : {[+ μb +]} ⊎ b2 = m) by (eapply non_blocking_action_in_ms; eauto).
    assert (mem : μb ∈ m) by (rewrite <- heqm; multiset_solver).
    edestruct (aux0 μb mem hstrip) as (e0 & hte0).
    rewrite <- heqm in hstrip.
    edestruct (aux3_ hstrip e0 hte0) as (t'' & hstrip'' & heqt'').
    assert (hstrip3 : e0 ⟿{b2} t) by (eapply mo_stripped_equiv; eauto).
    assert (nh0 : ¬ outcome t0).
    { intro hc. apply nh. eapply woutpout_preserves_outcome; eauto. }
    eapply may_com_step.
    - exact nh0.
    - exact duo.
    - exact l1.
    - exact hte0.
    - eapply IH; eauto.
  + subst q.
    edestruct (strip_retract_act hstrip et) as (r & htr & w & hstripw & heqw).
    assert (nh0 : ¬ outcome t0).
    { intro hc. apply nh. eapply woutpout_preserves_outcome; eauto. }
    eapply may_client_step.
    - exact nh0.
    - exact htr.
    - eapply IH; eauto. eapply mo_stripped_equiv; eauto.
  + subst q.
    inversion trS as [α a1 a2 b l Heq1 Heq2 Heq3 | α a b1 b2 l Heq1 Heq2 Heq3 | μa μb a1 a2 b1 b2 eqfw l1 l2 Heq1 Heq2]; subst.
    edestruct (strip_retract_act hstrip trC) as (r & htr & w & hstripw & heqw).
    assert (nh0 : ¬ outcome t0).
    { intro hc. apply nh. eapply woutpout_preserves_outcome; eauto. }
    eapply may_com_step.
    - exact nh0.
    - exact inter.
    - exact l.
    - exact htr.
    - eapply IH; eauto. eapply mo_stripped_equiv; eauto.
    - inversion l; subst.
      assert (heqmu : μ2 = η).
      { transitivity (co μ1). exact (unique_nb μ2 μ1 inter). symmetry. exact (unique_nb η μ1 duo). }
      subst μ2.
      assert (hstep1 : t ⟿{{[+ η +]} ⊎ (∅ : gmultiset A)} t').
      { eapply strip_step. exact nb. exact trC. constructor. reflexivity. }
      rewrite gmultiset_disj_union_right_id in hstep1.
      assert (hstripfull : t0 ⟿{m ⊎ {[+ η +]}} t') by (eapply strip_union; eauto).
      assert (heqcomm : m ⊎ {[+ η +]} = {[+ η +]} ⊎ m) by multiset_solver.
      rewrite heqcomm in hstripfull.
      exact (IH p ({[+ η +]} ⊎ m) eq_refl t0 hstripfull).
      assert (mem : μ1 ∈ {[+ μ1 +]} ⊎ b2) by multiset_solver.
      edestruct (aux0 μ1 mem hstrip) as (e0 & hte0).
      edestruct (aux3_ hstrip e0 hte0) as (t'' & hstrip'' & heqt'').
      edestruct (eq_spec t'' t' (ActExt μ2)) as (t3 & htr3 & heqt3).
      { exists t. split. exact heqt''. exact trC. }
      edestruct (strip_retract_act hstrip'' htr3) as (r & htr & t5 & hstrip5 & heqt5).
      assert (duo2 : dual μ2 μ1) by (symmetry; exact inter).
      destruct (feedback nb duo2 hte0 htr) as (r' & htr' & heqr').
      assert (hstrip6 : r' ⟿⋍{b2} t5) by (eapply strip_eq; eauto).
      destruct hstrip6 as (t6 & hstrip6 & heqt6).
      assert (heqt6t3 : t6 ⋍ t3) by (transitivity t5; [exact heqt6 | exact heqt5]).
      assert (heqt6t' : t6 ⋍ t') by (transitivity t3; [exact heqt6t3 | exact heqt3]).
      assert (hstripfinal : r' ⟿{b2} t') by (eapply mo_stripped_equiv; [exact hstrip6 | exact heqt6t']).
      assert (nh0 : ¬ outcome t0).
      { intro hc. apply nh. eapply woutpout_preserves_outcome; eauto. }
      eapply may_client_step.
      exact nh0.
      exact htr'.
      exact (IH p b2 eq_refl r' hstripfinal).
Qed.

Lemma may_fw_to_may `{
  @gLtsObaFB P A H gLtsEqP gLtsObaP, !FiniteImagegLts P A,
  @gLtsObaFB T A H gLtsEqT gLtsObaT, !Testing_Predicate outcome _}

  {_ : Prop_of_Inter P (MO A) A fw_inter}
  {_ : Prop_of_Inter (P * MO A) T A dual}
  {_ : Prop_of_Inter P T A dual}

  (p : P) (t : T) :
  (p, ∅ : gmultiset A) may_pass t -> p may_pass t.
Proof.
  intro hm. eapply may_fw_to_may_gen; eauto. constructor. reflexivity.
Qed.

Lemma may_iff_may_fw `{
  @gLtsObaFB P A H gLtsEqP gLtsObaP, !FiniteOutputChain_LtsOba P, !FiniteImagegLts P A,
  @gLtsObaFB T A H gLtsEqT gLtsObaT, !FiniteOutputChain_LtsOba T, !Testing_Predicate outcome _}

  {_ : Prop_of_Inter P (MO A) A fw_inter}
  {_ : Prop_of_Inter (P * MO A) T A dual}
  {_ : Prop_of_Inter P T A dual}

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
    @gLtsObaFB P A H gLtsEqP gLtsObaP, !FiniteOutputChain_LtsOba P, !FiniteImagegLts P A,
    @gLtsObaFB Q A H gLtsEqQ gLtsObaQ, !FiniteOutputChain_LtsOba Q, !FiniteImagegLts Q A,
    @gLtsObaFB T A H gLtsEqT gLtsObaT, !FiniteOutputChain_LtsOba T, !Testing_Predicate outcome _}

  {_ : Prop_of_Inter P (MO A) A fw_inter}
  {_ : Prop_of_Inter (P * MO A) T A dual}

  {_ : Prop_of_Inter P T A dual}

  {_ : Prop_of_Inter Q (MO A) A fw_inter}
  {_ : Prop_of_Inter (Q * MO A) T A dual}

  {_ : Prop_of_Inter Q T A dual}

  (p : P) (q : Q) : p ⊑ₘₐᵧ q <-> (p, ∅) ⊑ₘₐᵧ (q, ∅).
Proof.
  split; intros hctx e hm%may_iff_may_fw. 
  - rewrite <- may_iff_may_fw. eauto.
  - rewrite may_iff_may_fw. eauto.
Qed.
