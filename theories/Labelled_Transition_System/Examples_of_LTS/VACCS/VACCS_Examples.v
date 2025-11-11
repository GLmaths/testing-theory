(*
   Copyright (c) 2024 Gaëtan Lopez <gaetanlopez.maths@gmail.com>

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
From Coq.Strings Require Import String.
From Coq Require Import Relations.
From Coq.Wellfounded Require Import Inverse_Image.

From stdpp Require Import base countable finite gmap list gmultiset strings.
From Must Require Import InputOutputActions ActTau OldTransitionSystems Must VACCS_Instance VACCS_Good
gLts Bisimulation Lts_OBA Lts_FW Lts_OBA_FB GeneralizeLtsOutputs ParallelLTSConstruction ForwarderConstruction
InteractionBetweenLts Testing_Predicate.
(************************************* Examples for VACCS *************************************)
Parameter c : Channel.
Parameter O : Value.
Parameter I : Value.
Parameter (neq : O ≠ I).

Definition p : proc := c ? x • (c ! O • 𝟘).

Definition q : proc := c ? x • (c ! (bvar 0) • 𝟘).

Lemma q_is_above_NIL : 
  (@ctx_pre _ _ _ _ _ _ proc _ _ _ _ _ _ _ (g 𝟘) q). (* 𝟘 ⊑ₘᵤₛₜᵢ q *)
Proof.
  intros e Hyp.
  dependent induction Hyp.
  - eapply m_now. eauto.
  - eapply m_step; eauto.
    + inversion ex; subst. inversion H2; subst.
      * inversion l.
      * exists (q ▷ b2). eapply ParRight. eauto.
      * inversion l1.
    + intros. eauto. inversion H2.
    + intros. destruct μ1 as [ (*Input*) a | (*Output*) a ].
      * inversion H3. subst. simpl in *. symmetry in H2.
        eapply simplify_match_input in H2. subst.
        destruct (decide (good_VACCS e')).
        -- eapply m_now. eauto.
        -- eapply m_step; eauto.
           ++ inversion ex. inversion H2; subst.
              ** inversion l.
              ** unfold lts_step in l; simpl in *.
                 assert (lts e ((c ⋉ v) !) e') as HypTr; eauto.
                 eapply OBA_with_FB_Fifth_Axiom in HypTr 
                    as [(e'' & HypTr' & e'0 & HypTr'0 & equiv')|(e'' & HypTr' & equiv'')]; eauto.
                 --- exists (c ! v • 𝟘 ▷ e''). eapply ParRight. eauto.
                 --- assert (lts (c ! v • 𝟘) ((c ⋉ v) !) (g 𝟘)).
                     { eauto with ccs. }
                      exists ((g 𝟘) ▷ e''). eapply ParSync; eauto.
                     simpl; eauto.
              ** inversion l1.
           ++ intros. inversion H2.
           ++ intros. unfold lts_step in H2; simpl in *.
              destruct (decide (good_VACCS e'0)) as [happy | not_happy].
              ** now eapply m_now.
              ** eapply (OBA_with_FB_First_Axiom e e' e'0) in H4 
                    as (e1 & HypTr1 & e'1 & HypTr'1 & equiv); eauto.
                 eapply must_eq_client; eauto. assert (¬ good_VACCS e'1) as not_happy'.
                 { eapply unoutcome_preserved_by_eq; eauto. }
                 assert (¬ good_VACCS e1) as not_happy''.
                 { eapply unoutcome_preserved_by_lts_non_blocking_action_converse; eauto.
                   unfold non_blocking; simpl. exists (c ⋉ v); eauto. }
                 assert (must q e1); eauto.
                 eapply must_preserved_by_synch_if_notoutcome; eauto.
                 simpl; eauto.
           ++ intros. inversion H5; subst. simpl in *. symmetry in H2.
              eapply simplify_match_output in H2. subst. 
              eapply OBA_with_FB_Fourth_Axiom in H4 as (e'1 & HypTr'1 & equiv1); eauto.
              eapply must_eq_client; eauto.
      * inversion H3.
Qed.

Lemma NIL_is_above_q : 
  (@ctx_pre _ _ _ _ _ _ proc _ _ _ _ _ _ _ q (g 𝟘)). (* q ⊑ₘᵤₛₜᵢ 𝟘 *)
Proof.
  intros e Hyp.
  assert (must q e) as Mq; eauto.
  dependent induction Hyp.
  - now eapply m_now.
  - inversion ex. inversion H2; subst.
    + inversion l.
    + eapply m_step.
      * eauto. 
      * exists ((g 𝟘) ▷ b2). eapply ParRight; eauto.
      * intros. inversion H3.
      * intros. eapply H0. eauto. eauto. eapply et. eauto.
      * intros. inversion H4.
    + inversion l1; subst.
      symmetry in eq. eapply simplify_match_input in eq. subst.
      assert (must ((c ! (bvar 0) • 𝟘) ^ v) b2) as Mq'.
      { eapply must_preserved_by_synch_if_notoutcome ; eauto. simpl; eauto. }
      inversion Mq'.
      * assert (good_VACCS e).
        { eapply outcome_preserved_by_lts_non_blocking_action_converse; eauto.
          eexists; eauto. } contradiction.
      * inversion ex0; subst. inversion H3; subst.
        -- inversion l.
        -- eapply (OBA_with_FB_First_Axiom e b2 b0) in l2 
              as (e'' & HypTr'' & p'1 & HypTr'1 & equiv'1); eauto.
           eapply m_step; eauto.
           ++ exists ((g 𝟘) ▷ e''). eapply ParRight. eauto.
           ++ intros. inversion H4.
           ++ intros. inversion H5.
        -- inversion l0; subst.
           symmetry in eq. eapply simplify_match_output in eq. subst.
           eapply OBA_with_FB_Fourth_Axiom in l2 as (e''1 & HypTr''1 & equiv''1) ; eauto.
           eapply must_preserved_by_lts_tau_clt in Mq; eauto.
           eapply m_step; eauto.
           ++ exists ((g 𝟘) ▷ e''1). eapply ParRight. eauto.
           ++ intros. inversion H4.
           ++ intros. inversion H5.
Qed.

Lemma q_is_above_p : 
  (@ctx_pre _ _ _ _ _ _ proc _ _ _ _ _ _ _ p q). (* p ⊑ₘᵤₛₜᵢ q *)
Proof.
  intros e HypMust.
  dependent induction HypMust.
  - now apply m_now.
  - eapply m_step; eauto.
    + inversion ex; subst. inversion H2; subst.
      * inversion l.
      * exists (q ▷ b2). eapply ParRight. eauto.
      * inversion l1; subst. symmetry in eq.
        eapply simplify_match_input in eq as eq'; subst.
        symmetry in eq. eexists. eapply ParSync; eauto.
        unfold q. eapply lts_input; eauto.
    + intros. eauto. inversion H2.
    + intros. inversion H3; subst. symmetry in H2.
      eapply simplify_match_input in H2 as eq;subst.
      assert (¬ good_VACCS e') as not_happy'.
      { eapply unoutcome_preserved_by_lts_non_blocking_action; eauto.
        exists (c ⋉ v); eauto. }
      eapply m_step; eauto.
      * symmetry in H2. assert (must ((c ! O • 𝟘) ^ v) e') as Mp'.
        { eapply (must_preserved_by_synch_if_notoutcome p _ e _) ; eauto.
          eapply m_step; eauto. eapply lts_input. }
        inversion Mp'. contradiction.
        inversion ex0. inversion H5; subst.
        -- inversion l.
        -- exists ((c ! 0 • 𝟘) ^ v ▷ b2). eapply ParRight; eauto.
        -- inversion l1; subst. symmetry in eq. eapply simplify_match_output in eq as eq'; subst.
           assert (e' ⟶[ActIn (c ⋉ O)] b2) as l'2; eauto.
           eapply TransitionShapeForInput in l2 as (p1 & g1 & r1 & n & equiv1 & equiv2 & eq1).
           edestruct (Congruence_Respects_Transition e') as (e'1 & Tr'1 & equiv'1). 
           { exists (Ѵ n (((gpr_input c p1 + g1) ‖ r1))). split; eauto. eapply lts_res_ext_n. eapply lts_parL.
             eapply lts_choiceL. instantiate (2 := ActIn (c ⋉ v)). simpl. eapply lts_input. }
           simpl. exists (g 𝟘 , e'1). eapply ParSync.
           ++ symmetry in H2. exact H2.
           ++ eapply lts_output.
           ++ eauto.
      * intros. inversion H5.
      * intros. destruct (decide (good_VACCS e'0)) as [happy | not_happy].
        -- now eapply m_now.
        -- eapply (OBA_with_FB_First_Axiom e e' e'0) in H4 
                    as (e1 & HypTr1 & e'1 & HypTr'1 & equiv); eauto.
           eapply must_eq_client; eauto. assert (¬ good_VACCS e'1) as not_happy''.
           { eapply unoutcome_preserved_by_eq; eauto. }
           assert (¬ good_VACCS e1) as not_happy'''.
           { eapply unoutcome_preserved_by_lts_non_blocking_action_converse; eauto.
             unfold non_blocking; simpl. exists (c ⋉ v); eauto. }
           assert (must q e1); eauto. symmetry in H2.
           eapply must_preserved_by_synch_if_notoutcome; eauto.
      * intros. inversion H6; subst. symmetry in H5.
        eapply simplify_match_output in H5 as eq; subst.
        assert (lts e ((c ⋉ v) !) e') as l2; eauto.
        eapply OBA_with_FB_Fourth_Axiom in l2 as (e'1 & HypTr'1 & equiv1); eauto.
        eapply must_eq_client; eauto. assert (must p e) as Mp. eapply m_step; eauto.
        assert (must p e'1) as Mp';eauto.
        assert (must q e'1); eauto. eapply NIL_is_above_q. eauto.
Qed.


Lemma NIL_is_above_p : 
  (@ctx_pre _ _ _ _ _ _ proc _ _ _ _ _ _ _ p (g 𝟘)). (* p ⊑ₘᵤₛₜᵢ 𝟘 *)
Proof.
  intros e Hyp. eapply NIL_is_above_q. eapply q_is_above_p. exact Hyp.
Qed.

Definition Test := (c ! I • 𝟘) ‖ (c ? x • (If (bvar 0 == I) Then ① Else (g 𝟘))).

Lemma this_Test_is_not_good : ¬ good_VACCS Test.
Proof.
  intro imp. inversion imp; subst. inversion H0; subst.
  - inversion H.
  - inversion H.
Qed.

Lemma NIL_must_this_TEST :  (g 𝟘) must_pass Test.
Proof.
  eapply m_step.
  - eapply this_Test_is_not_good.
  - exists (g 𝟘 ▷ (g 𝟘 ‖ ((If (bvar 0 == I) Then ① Else (g 𝟘))^I))).
    eapply ParRight. eapply lts_comL; eauto with ccs.
  - intros ? imp. inversion imp.
  - intros. inversion H; subst.
    + inversion H3; subst. simpl. inversion H2; subst.
      constructor. constructor. right. constructor. constructor. simpl.
      eapply decide_True; eauto.
    + inversion H3.
    + inversion H4.
    + inversion H4.
  - intros. inversion H0. 
Qed.


Lemma p_is_not_above_NIL : 
¬ (@ctx_pre _ _ _ _ _ _ proc _ _ _ _ _ _ _ (g 𝟘) p). (* ¬ 𝟘 ⊑ₘᵤₛₜᵢ p *)
Proof.
  intro imp.
  assert (must p Test).
  { eapply imp. eapply NIL_must_this_TEST. }
  inversion H.
  + eapply this_Test_is_not_good; eauto.
  + assert (must ((c ! O • 𝟘)^I) ((g 𝟘) ‖ (c ? x • (If (bvar 0 == I) Then ① Else (g 𝟘))))) as Mp.
    { eapply com; eauto. 2: { eapply lts_input. } 2: { eapply lts_parL. eapply lts_output. }
    simpl; eauto. }
    simpl in Mp.
    assert (must (g 𝟘) ((g 𝟘) ‖ ((If ((bvar 0) == I)
                                           Then ① 
                                           Else 𝟘)^O))) as Mp'.
    { eapply must_preserved_by_synch_if_notoutcome; eauto. intro imp'.
      inversion imp'; subst. inversion H1. inversion H0. inversion H0.
      2 : { eapply lts_output. } 2 : { eapply lts_parR. eapply lts_input. }
      simpl; eauto. } simpl in Mp'. inversion Mp'.
    ++ inversion H0; subst. inversion H2.
       * inversion H1.
       * inversion H1; subst.
         - simpl in H7. rewrite decide_False in H7. inversion H7.
           eapply neq.
         - inversion H5.
    ++ inversion ex0. inversion H0; subst.
       * inversion l.
       * inversion l; subst.
         - inversion H3.
         - inversion H4.
         - inversion H5.
         - inversion H5; subst. inversion H8. inversion H8.
       * inversion l1.
Qed.

Lemma p_is_not_above_q : 
  ¬ (@ctx_pre _ _ _ _ _ _ proc _ _ _ _ _ _ _ q p). (* ¬ q ⊑ₘᵤₛₜᵢ p *)
Proof.
  intros imp. assert (@ctx_pre _ _ _ _ _ _ proc _ _ _ _ _ _ _ (g 𝟘) q) as HypMust.
  { eapply q_is_above_NIL; eauto. }
  assert (@ctx_pre _ _ _ _ _ _ proc _ _ _ _ _ _ _ (g 𝟘) p) as imp'.
  { intros e HM. eapply imp. eapply HypMust. eauto. }
  assert (¬ (@ctx_pre _ _ _ _ _ _ proc _ _ _ _ _ _ _ (g 𝟘) p)). { eapply p_is_not_above_NIL. }
  contradiction.
Qed.
