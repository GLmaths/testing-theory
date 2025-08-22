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
InteractionBetweenLts.
(************************************* Examples for VACCS *************************************)
Parameter c : Channel.

Definition q : proc := c ? x • (c ! (bvar 0) • 𝟘).

Lemma q_is_above_NIL : 
  (@ctx_pre _ _ _ _ _ _ proc _ _ _ _ _ _ _ (g 𝟘) q). (* 𝟘 ⊑ q *)
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
                 { eapply ungood_preserved_by_eq; eauto. }
                 assert (¬ good_VACCS e1) as not_happy''.
                 { eapply ungood_preserved_by_lts_non_blocking_action_converse; eauto.
                   unfold non_blocking; simpl. exists (c ⋉ v); eauto. }
                 assert (must q e1); eauto.
                 eapply must_preserved_by_synch_if_notgood; eauto.
                 simpl; eauto.
           ++ intros. inversion H5; subst. simpl in *. symmetry in H2.
              eapply simplify_match_output in H2. subst. 
              eapply OBA_with_FB_Fourth_Axiom in H4 as (e'1 & HypTr'1 & equiv1); eauto.
              eapply must_eq_client; eauto.
      * inversion H3.
Qed.

Lemma NIL_is_above_q : 
  (@ctx_pre _ _ _ _ _ _ proc _ _ _ _ _ _ _ q (g 𝟘)). (* q ⊑ 𝟘 *)
Proof.
  intros e Hyp.
  assert (must q e) as Mq; eauto.
  dependent induction Hyp.
  - now eapply m_now.
  - inversion ex. inversion H2; subst.
    + inversion l.
    + eapply m_step; eauto.
      * exists ((g 𝟘) ▷ b2). eapply ParRight; eauto.
      * intros. inversion H3.
      * intros. inversion H4.
    + inversion l1; subst.
      symmetry in eq. eapply simplify_match_input in eq. subst.
      assert (must ((c ! (bvar 0) • 𝟘) ^ v) b2) as Mq'.
      { eapply must_preserved_by_synch_if_notgood ; eauto. simpl; eauto. }
      inversion Mq'.
      * assert (good_VACCS e).
        { eapply good_preserved_by_lts_non_blocking_action_converse; eauto.
          eexists; eauto. }
        now eapply m_now.
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




