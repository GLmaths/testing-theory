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
From TestingTheory Require Import InputOutputActions ActTau Must VACCS_Must_Characterization
gLts Bisimulation Lts_OBA Lts_FW Lts_OBA_FB ParallelLTSConstruction
InteractionBetweenLts Testing_Predicate DefinitionAS VACCS VACCS_Good VACCS_Instance
Convergence WeakTransitions Subset_Act MultisetLTSConstruction Termination.

(* Local Coercion in VACCS.v does not propagate across files; redeclared here. *)
Local Coercion bvar : nat >-> Data.
Local Coercion cst_channel : Channel >-> ChannelData.
Local Coercion cst_value : Value >-> ValueData.

(** ** VACCS **)
(** *** Applications *)

Section VACCS_examples.

Context `{VP : VACCS_Parameters}.

(* We assume that there is at least one channel and two values *)
Context {a : Channel} {O : Value} {I : Value} {neq : O ≠ I}.

Definition const : proc := a ? (a ! O • 𝟘).

Definition ccat : proc := a ? (a ! (0) • 𝟘).

Example copycat_is_above_NIL : g 𝟘 ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ccat.
Proof.
  intros e Hyp.
  dependent induction Hyp.
  - eapply m_now. eauto.
  - clear H2.
    eapply m_step; eauto.
    + inversion ex; subst. inversion H; subst.
      * lts_inversion lts.
      * exists (ccat ▷ b2). eapply ParRight. eauto.
      * inversion l1.
    + intros. eauto. inversion H.
    + intros. destruct μ1 as [ (*Input*) b | (*Output*) b ].
      * inversion H2. subst. simpl in *.
        eapply simplify_match_input in H. subst.
        destruct (decide (good_VACCS t')).
        -- eapply m_now. eauto.
        -- eapply m_step; eauto.
           ++ inversion ex. inversion H; subst.
              ** inversion l.
              ** unfold lts_step in l; simpl in *.
                 assert (lts e ((cst a , v) !) t') as HypTr; eauto.
                 eapply OBA_with_FB_Fifth_Axiom in HypTr 
                    as [(t'' & HypTr' & t'0 & HypTr'0 & equiv')|(t'' & HypTr' & equiv'')]; eauto.
                 --- exists (a ! v • 𝟘 ▷ t''). eapply ParRight. eauto.
                 --- assert (lts (a ! v • 𝟘) ((cst a , v) !) (g 𝟘)).
                     { eauto with cgr. }
                      exists ((g 𝟘) ▷ t''). eapply ParSync; eauto.
                     simpl; eauto.
              ** inversion l1.
           ++ intros. lts_inversion lts.
           ++ intros. unfold lts_step in H2; simpl in *.
              destruct (decide (good_VACCS t'0)) as [happy | not_happy].
              ** now eapply m_now.
              ** eapply (OBA_with_FB_First_Axiom e t' t'0) in H3
                    as (e1 & HypTr1 & e'1 & HypTr'1 & equiv); eauto.
                 eapply (@must_eq_client proc); eauto. assert (¬ good_VACCS e'1) as not_happy'.
                 { eapply unoutcome_preserved_by_eq; eauto. }
                 assert (¬ good_VACCS e1) as not_happy''.
                 { eapply unoutcome_preserved_by_lts_non_blocking_action_converse; eauto.
                   unfold non_blocking; simpl. exists (cst a , v); eauto. }
                 assert (must ccat e1); eauto.
                 eapply must_preserved_by_synch_if_notoutcome; eauto.
                 simpl; eauto.
           ++ intros. inversion H4; subst. simpl in *.
              eapply simplify_match_output in H. subst. 
              eapply OBA_with_FB_Fourth_Axiom in H3 as (e'1 & HypTr'1 & equiv1); eauto.
              eapply (@must_eq_client proc); eauto.
      * lts_inversion lts.
Qed.

Example NIL_is_above_copycat : ccat ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (g 𝟘).
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
      * intros. lts_inversion lts.
      * intros. eapply H0. eauto. eauto. eapply et. eauto.
      * intros. lts_inversion lts.
    + inversion l1; subst.
      eapply simplify_match_input in eq. subst.
      assert (must ((cst a ! (bvar 0) • 𝟘) ^ v) b2) as Mq'.
      { eapply must_preserved_by_synch_if_notoutcome ; eauto. simpl; eauto. }
      inversion Mq'.
      * assert (good_VACCS t).
        { eapply outcome_preserved_by_lts_non_blocking_action_converse; eauto.
          eexists; eauto. } contradiction.
      * inversion ex0; subst. lts_inversion lts.
        -- lts_inversion lts.
        -- eapply (OBA_with_FB_First_Axiom t b2 b0) in l2 
              as (t'' & HypTr'' & p'1 & HypTr'1 & equiv'1); eauto.
           eapply m_step; eauto.
           ++ exists ((g 𝟘) ▷ t''). eapply ParRight. eauto.
           ++ intros. lts_inversion lts.
           ++ intros. lts_inversion lts.
        -- inversion l0; subst.
           eapply simplify_match_output in eq. subst.
           eapply OBA_with_FB_Fourth_Axiom in l2 as (t''1 & HypTr''1 & equiv''1) ; eauto.
           eapply (@must_preserved_by_lts_tau_clt proc) in Mq; eauto.
           eapply m_step; eauto.
           ++ exists ((g 𝟘) ▷ t''1). eapply ParRight. eauto.
           ++ intros. lts_inversion lts.
           ++ intros. lts_inversion lts.
Qed.

Example copycat_is_above_constant : const ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ccat.
Proof.
  intros t HypMust.
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
        exists (cst a , v); eauto. }
      eapply m_step; eauto.
      * pose proof H4 as Mp'.
        eapply (must_preserved_by_synch_if_notoutcome const ((cst a ! cst O • 𝟘) ^ v) t t' (ActIn (cst a , v))) in Mp'; eauto.
        inversion Mp'. contradiction.
        inversion ex0. inversion H5; subst.
        -- inversion l.
        -- exists ((cst a ! (bvar 0) • 𝟘) ^ v ▷ b2). eapply ParRight; eauto.
        -- inversion l1; subst. eapply simplify_match_output in eq as eq'; subst.
           assert (t' ⟶[ActIn (cst a , cst O)] b2) as l'2; eauto.
           eapply TransitionShapeForInput in l2 as (p1 & g1 & r1 & n & equiv1 & equiv2 & eq1).
           edestruct (Congruence_Respects_Transition t') as (t'1 & Tr'1 & equiv'1). 
           { exists (Ѵ n (((gpr_input (a) p1 + g1) ‖ r1))). split; eauto. eapply lts_res_ext_n. eapply lts_parL.
             eapply lts_choiceL. instantiate (2 := ActIn (cst a , v)). simpl. eapply lts_input. }
           simpl. exists (g 𝟘 , t'1). eapply ParSync.
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
             unfold non_blocking; simpl. exists (cst a , v); eauto. }
           assert (must ccat t1); eauto.
           eapply must_preserved_by_synch_if_notoutcome; eauto.
      * intros. inversion H6; subst.
        eapply simplify_match_output in H5 as eq; subst.
        assert (lts t ((cst a , v) !) t') as l2; eauto.
        eapply OBA_with_FB_Fourth_Axiom in l2 as (t'1 & HypTr'1 & equiv1); eauto.
        eapply (@must_eq_client proc); eauto. assert (must const t) as Mp. eapply m_step; eauto.
        assert (must const t'1) as Mp';eauto.
        assert (must ccat t'1); eauto. eapply NIL_is_above_copycat. eauto.
Qed.

Example NIL_is_above_constant : const ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (g 𝟘).
Proof.
  intros e Hyp. eapply NIL_is_above_copycat. eapply copycat_is_above_constant. exact Hyp.
Qed.

Definition Test := (cst a ! cst I • 𝟘) ‖ (cst a ? (If (bvar 0 == cst I) Then ① Else (g 𝟘))).

Lemma this_Test_is_not_good : ¬ good_VACCS Test.
Proof. intro imp. inversion imp; subst. inversion H0; subst; inversion H. Qed.

Lemma NIL_must_this_TEST :  (g 𝟘) must_pass Test.
Proof.
  eapply m_step.
  - eapply this_Test_is_not_good.
  - exists (g 𝟘 ▷ (g 𝟘 ‖ ((If (bvar 0 == cst I) Then ① Else (g 𝟘))^(cst I)))).
    eapply ParRight. eapply lts_comL; eauto with cgr.
  - intros ? imp. inversion imp.
  - intros. inversion H; subst; repeat lts_inversion lts.
    constructor. constructor. right. constructor. constructor. simpl.
    eapply decide_True; eauto.
  - intros. lts_inversion lts.
Qed.


Example constant_is_not_above_NIL : (g 𝟘) ⋢ₘᵤₛₜᵢ const.
Proof.
  intro imp.
  assert (must const Test).
  { eapply imp. eapply NIL_must_this_TEST. }
  inversion H.
  + eapply this_Test_is_not_good; eauto.
  + assert (must ((cst a ! cst O • 𝟘)^(cst I)) ((g 𝟘) ‖ (cst a ? (If (bvar 0 == cst I) Then ① Else (g 𝟘))))) as Mp.
    { eapply com; eauto. 2: { eapply lts_input. } 2: { eapply lts_parL. eapply lts_output. }
    simpl; eauto. }
    simpl in Mp.
    assert ((g 𝟘) must_pass ((g 𝟘) ‖ ((If ((bvar 0) == cst I)
                                           Then ① 
                                           Else 𝟘)^(cst O)))) as Mp'.
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
    ++ inversion ex0. repeat lts_inversion lts.
Qed.

Example NIL_is_equivalent_to_ccat : ccat ≂ₘᵤₛₜᵢ (g 𝟘).
Proof.
  split.
  + eapply copycat_is_above_NIL.
  + eapply NIL_is_above_copycat.
Qed.

End VACCS_examples.
