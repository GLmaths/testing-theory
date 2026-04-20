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


From Stdlib.Program Require Import Equality.
From Stdlib.Strings Require Import String.
From Stdlib Require Import Relations.
From Stdlib.Wellfounded Require Import Inverse_Image.

From stdpp Require Import base countable finite gmap list gmultiset strings.
From Must Require Import InputOutputActions ActTau OldTransitionSystems Must VACCS_Instance VACCS_Good
gLts Bisimulation Lts_OBA Lts_FW Lts_OBA_FB GeneralizeLtsOutputs ParallelLTSConstruction
InteractionBetweenLts Testing_Predicate DefinitionAS.
(************************************* Examples for VACCS *************************************)
Parameter a : Channel.
Parameter O : Value.
Parameter I : Value.
Parameter (neq : O ≠ I).

Definition cst : proc := a ? x • (a ! O • 𝟘).

Definition ccat : proc := a ? x • (a ! (bvar 0) • 𝟘).

(* Set Typeclasses Debug.
Set Typeclasses Depth 1. (* to be remove *)*)
(* Example of Proof *)
(*
Goal (g 𝟘 ≼ₐₛ ccat).
constructor.
- intros s Hs. *)

Lemma q_is_above_NIL : g 𝟘 ⊑ₘᵤₛₜᵢ ccat.
Proof.
  intros e Hyp.
  dependent induction Hyp.
  - eapply m_now. eauto.
  - eapply m_step; eauto.
    + inversion ex; subst. inversion H2; subst.
      * inversion l.
      * exists (ccat ▷ b2). eapply ParRight. eauto.
      * inversion l1.
    + intros. eauto. inversion H2.
    + intros. destruct μ1 as [ (*Input*) a | (*Output*) a ].
      * inversion H3. subst. simpl in *.
        eapply simplify_match_input in H2. subst.
        destruct (decide (good_VACCS t')).
        -- eapply m_now. eauto.
        -- eapply m_step; eauto.
           ++ inversion ex. inversion H2; subst.
              ** inversion l.
              ** unfold lts_step in l; simpl in *.
                 assert (lts e ((a ⋉ v) !) e') as HypTr; eauto.
                 eapply OBA_with_FB_Fifth_Axiom in HypTr 
                    as [(e'' & HypTr' & e'0 & HypTr'0 & equiv')|(e'' & HypTr' & equiv'')]; eauto.
                 --- exists (a ! v • 𝟘 ▷ e''). eapply ParRight. eauto.
                 --- assert (lts (a ! v • 𝟘) ((a ⋉ v) !) (g 𝟘)).
                     { eauto with cgr. }
                      exists ((g 𝟘) ▷ e''). eapply ParSync; eauto.
                     simpl; eauto.
              ** inversion l1.
           ++ intros. inversion H2.
           ++ intros. unfold lts_step in H2; simpl in *.
              destruct (decide (good_VACCS t'0)) as [happy | not_happy].
              ** now eapply m_now.
              ** eapply (OBA_with_FB_First_Axiom t t' t'0) in H4 
                    as (e1 & HypTr1 & e'1 & HypTr'1 & equiv); eauto.
                 eapply (@must_eq_client proc); eauto. assert (¬ good_VACCS e'1) as not_happy'.
                 { eapply unoutcome_preserved_by_eq; eauto. }
                 assert (¬ good_VACCS e1) as not_happy''.
                 { eapply unoutcome_preserved_by_lts_non_blocking_action_converse; eauto.
                   unfold non_blocking; simpl. exists (a ⋉ v); eauto. }
                 assert (must ccat e1); eauto.
                 eapply must_preserved_by_synch_if_notoutcome; eauto.
                 simpl; eauto.
           ++ intros. inversion H5; subst. simpl in *.
              eapply simplify_match_output in H2. subst. 
              eapply OBA_with_FB_Fourth_Axiom in H4 as (e'1 & HypTr'1 & equiv1); eauto.
              eapply (@must_eq_client proc); eauto.
      * inversion H3.
Qed.

Lemma NIL_is_above_ccat : ccat ⊑ₘᵤₛₜᵢ (g 𝟘).
Proof.
  intros t Hyp.
  assert (must ccat t) as Mq; eauto.
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
      eapply simplify_match_input in eq. subst.
      assert (must ((a ! (bvar 0) • 𝟘) ^ v) b2) as Mq'.
      { eapply must_preserved_by_synch_if_notoutcome ; eauto. simpl; eauto. }
      inversion Mq'.
      * assert (good_VACCS t).
        { eapply outcome_preserved_by_lts_non_blocking_action_converse; eauto.
          eexists; eauto. } contradiction.
      * inversion ex0; subst. inversion H3; subst.
        -- inversion l.
        -- eapply (OBA_with_FB_First_Axiom t b2 b0) in l2 
              as (e'' & HypTr'' & p'1 & HypTr'1 & equiv'1); eauto.
           eapply m_step; eauto.
           ++ exists ((g 𝟘) ▷ e''). eapply ParRight. eauto.
           ++ intros. inversion H4.
           ++ intros. inversion H5.
        -- inversion l0; subst.
           eapply simplify_match_output in eq. subst.
           eapply OBA_with_FB_Fourth_Axiom in l2 as (e''1 & HypTr''1 & equiv''1) ; eauto.
           eapply (@must_preserved_by_lts_tau_clt proc) in Mq; eauto.
           eapply m_step; eauto.
           ++ exists ((g 𝟘) ▷ e''1). eapply ParRight. eauto.
           ++ intros. inversion H4.
           ++ intros. inversion H5.
Qed.

Lemma copycat_is_above_constant : cst ⊑ₘᵤₛₜᵢ ccat.
Proof.
  intros e HypMust.
  dependent induction HypMust.
  - now apply m_now.
  - eapply m_step; eauto.
    + inversion ex; subst. inversion H2; subst.
      * inversion l.
      * exists (ccat ▷ b2). eapply ParRight. eauto.
      * inversion l1; subst.
        eapply simplify_match_input in eq as eq'; subst.
        eexists. eapply ParSync; eauto.
        unfold ccat. eapply lts_input; eauto.
    + intros. eauto. inversion H2.
    + intros. inversion H3; subst.
      eapply simplify_match_input in H2 as eq;subst.
      assert (¬ good_VACCS t') as not_happy'.
      { eapply unoutcome_preserved_by_lts_non_blocking_action; eauto.
        exists (a ⋉ v); eauto. }
      eapply m_step; eauto.
      (* * assert (must ((a ! O • 𝟘) ^ v) e') as Mp'.
        { eapply (must_preserved_by_synch_if_notoutcome cst _ e _) ; eauto.
          eapply m_step; eauto. eapply lts_input. } *)
      * pose proof H4 as Mp'.
        eapply (must_preserved_by_synch_if_notoutcome p ((a ! O • 𝟘) ^ v) t t' (ActIn (a ⋉ v))) in Mp'; eauto.
        inversion Mp'. contradiction.
        inversion ex0. inversion H5; subst.
        -- inversion l.
        -- exists ((a ! 0 • 𝟘) ^ v ▷ b2). eapply ParRight; eauto.
        -- inversion l1; subst. eapply simplify_match_output in eq as eq'; subst.
           assert (t' ⟶[ActIn (a ⋉ O)] b2) as l'2; eauto.
           eapply TransitionShapeForInput in l2 as (p1 & g1 & r1 & n & equiv1 & equiv2 & eq1).
           edestruct (Congruence_Respects_Transition t') as (e'1 & Tr'1 & equiv'1). 
           { exists (Ѵ n (((gpr_input a p1 + g1) ‖ r1))). split; eauto. eapply lts_res_ext_n. eapply lts_parL.
             eapply lts_choiceL. instantiate (2 := ActIn (a ⋉ v)). simpl. eapply lts_input. }
           simpl. exists (g 𝟘 , e'1). eapply ParSync.
           ++ symmetry in H2. exact H2.
           ++ eapply lts_output.
           ++ eauto.
        -- eapply m_step; eauto.
        -- eapply lts_input.
      * intros p' tr_tau. inversion tr_tau.
      * intros. destruct (decide (good_VACCS t'0)) as [happy | not_happy].
        -- now eapply m_now.
        -- eapply (OBA_with_FB_First_Axiom t t' t'0) in H4 
                    as (t1 & HypTr1 & t'1 & HypTr'1 & equiv); eauto.
           eapply (@must_eq_client proc); eauto. assert (¬ good_VACCS t'1) as not_happy''.
           { eapply unoutcome_preserved_by_eq; eauto. }
           assert (¬ good_VACCS t1) as not_happy'''.
           { eapply unoutcome_preserved_by_lts_non_blocking_action_converse; eauto.
             unfold non_blocking; simpl. exists (a ⋉ v); eauto. }
           assert (must q t1); eauto.
           eapply must_preserved_by_synch_if_notoutcome; eauto.
      * intros. inversion H6; subst.
        eapply simplify_match_output in H5 as eq; subst.
        assert (lts t ((a ⋉ v) !) t') as l2; eauto.
        eapply OBA_with_FB_Fourth_Axiom in l2 as (e'1 & HypTr'1 & equiv1); eauto.
        eapply (@must_eq_client proc); eauto. assert (must p t) as Mp. eapply m_step; eauto.
        assert (must p e'1) as Mp';eauto.
        assert (must q e'1); eauto. eapply NIL_is_above_q. eauto.
Qed.

Lemma NIL_is_above_copycat : ccat ⊑ₘᵤₛₜᵢ (g 𝟘).
Proof.
  intros e Hyp. eapply NIL_is_above_copycat. eapply copycat_is_above_constant. exact Hyp.
Qed.

Definition Test := (a ! I • 𝟘) ‖ (a ? x • (If (bvar 0 == I) Then ① Else (g 𝟘))).

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
    eapply ParRight. eapply lts_comL; eauto with cgr.
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


Lemma constant_is_not_above_NIL : (g 𝟘) ⋢ₘᵤₛₜᵢ cst.
Proof.
  intro imp.
  assert (must cst Test).
  { eapply imp. eapply NIL_must_this_TEST. }
  inversion H.
  + eapply this_Test_is_not_good; eauto.
  + assert (must ((a ! O • 𝟘)^I) ((g 𝟘) ‖ (a ? x • (If (bvar 0 == I) Then ① Else (g 𝟘))))) as Mp.
    { eapply com; eauto. 2: { eapply lts_input. } 2: { eapply lts_parL. eapply lts_output. }
    simpl; eauto. }
    simpl in Mp.
    assert (must (g 𝟘) ((g 𝟘) ‖ ((If ((bvar 0) == I)
                                           Then ① 
                                           Else 𝟘)^O))) as Mp'.
    { eapply (@must_preserved_by_synch_if_notoutcome proc); eauto. intro imp'.
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

Lemma constant_is_not_above_copycat : ccat ⋢ₘᵤₛₜᵢ cst.
Proof.
  intros imp. assert ((g 𝟘) ⊑ₘᵤₛₜᵢ ccat) as HypMust.
  { eapply q_is_above_NIL; eauto. }
  assert ((g 𝟘) ⊑ₘᵤₛₜᵢ cst) as imp'.
  { intros e HM. eapply imp. eapply HypMust. eauto. }
  assert (¬ (g 𝟘) ⊑ₘᵤₛₜᵢ cst). { eapply p_is_not_above_NIL. }
  contradiction.
Qed.
