   (*
   Copyright (c) 2026 Gaëtan Lopez <gaetanlopez.maths@gmail.com>

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
From TestingTheory Require Import InputOutputActions ActTau Must VCCS_Must_Characterization
gLts Bisimulation Lts_OBA Lts_FW Lts_OBA_FB ParallelLTSConstruction
InteractionBetweenLts Testing_Predicate DefinitionAS Convergence Termination
MultisetLTSConstruction ForwarderConstruction InputOutputActions WeakTransitions Subset_Act VCCS_Instance
VCCS_Good.

(** ** VCCS **)
(** *** Applications *)
Section VCCS_examples.

Context `{VP : VCCS_Parameters}.

Parameter a : Channel.
Parameter I : Value.
Parameter (neq : O ≠ I).

Definition all_out := g ((cst a ! cst O • 𝟘) + (cst a ! cst I • 𝟘)).

Definition one_out := g (cst a ! cst O • 𝟘).

Lemma NIL_converges : (g 𝟘) ⤓.
Proof.
  constructor.
  intros p Imp. inversion Imp.
Qed.

Lemma NIL_wt_to_NIL s p : g 𝟘 ⟹[s] p -> p = g 𝟘.
Proof.
  intros Hyp. inversion Hyp;subst.
  + reflexivity.
  + inversion l.
  + inversion l.
Qed.

Lemma NIL_converges_forall s : (g 𝟘) ⇓ s.
Proof.
  induction s.
  + constructor. eapply NIL_converges.
  + constructor.
    * eapply NIL_converges.
    * intros. eapply NIL_wt_to_NIL in H; subst; eauto.
Qed.

Lemma one_out_converges : one_out ⤓.
Proof.
  constructor. intros p Imp. inversion Imp.
Qed.

Lemma all_out_converges : all_out ⤓.
Proof.
  constructor. intros p Imp. repeat lts_inversion lts.
Qed.

Lemma one_out_wt_inv p : one_out ⟹ p -> p = one_out.
Proof.
  intros Hyp.
  inversion Hyp;subst; eauto. inversion l.
Qed.

Lemma all_out_wt_inv p : all_out ⟹ p -> p = all_out.
Proof.
  intros Hyp.
  dependent induction Hyp;subst; eauto. inversion l;subst;inversion H3.
Qed.

Lemma one_out_wt_inv_s a p : one_out ⟹{a} p -> p = g 𝟘.
Proof.
  intros Hyp.
  inversion Hyp;subst.
  + inversion l.
  + inversion l; subst.
    eapply NIL_wt_to_NIL in w ; subst ; eauto.
Qed.

Lemma all_out_wt_inv_s a p : all_out ⟹{a} p -> p = g 𝟘.
Proof.
  intros Hyp.
  inversion Hyp;subst.
  + inversion l; subst.
    * inversion H3.
    * inversion H3.
  + inversion l; subst.
    * inversion H3;subst.
      eapply NIL_wt_to_NIL in w ;subst; eauto.
    * inversion H3;subst.
      eapply NIL_wt_to_NIL in w ;subst; eauto.
Qed.

Lemma all_out_converges_for_all s : all_out ⇓ s.
Proof.
  induction s.
  + constructor. eapply all_out_converges.
  + constructor.
    * eapply all_out_converges.
    * intros p wk_tr.
      eapply all_out_wt_inv_s in wk_tr;subst.
      eapply NIL_converges_forall; eauto.
Qed.

Lemma one_out_converges_for_all s : one_out ⇓ s.
Proof.
  induction s.
  + constructor. eapply one_out_converges.
  + constructor.
    * eapply one_out_converges.
    * intros p wk_tr.
      eapply one_out_wt_inv_s in wk_tr;subst.
      eapply NIL_converges_forall; eauto.
Qed.

Lemma one_out_inv_wt s q : one_out ⟹[s] q -> s = [] \/ s = [ActOut (cst a , cst O)] \/ False.
Proof.
  intros H.
  inversion H; subst.
  + left; eauto.
  + inversion l.
  + lts_inversion lts.
    inversion w; subst.
    * right. left; eauto.
    * inversion l.
    * inversion l.
Qed.

Ltac compute_coR mem :=
  eapply coR_abs_spec2 in mem;
  eapply coR_abs_spec1;
  unfold all_out in mem;
  simpl in *;
  unfold PreCoAct_of in *;
  eapply gmultiset_elem_of_dom;
  eapply gmultiset_elem_of_dom in mem;
  simpl in *.

Ltac only_two_cases s q wt_tr H :=
  edestruct (one_out_inv_wt s q wt_tr);
  [| destruct H; [| inversion H]];
  subst;
  [ eapply one_out_wt_inv in wt_tr as eq; subst
  | eapply one_out_wt_inv_s in wt_tr as eq; subst ].

Lemma one_output_is_above_all_output_conv : all_out ⊑ₘᵤₛₜᵢ one_out.
Proof.
  apply must_iff_acceptance_set_VCCS_without_toFW.
  split.
  + intros s Hyp_conv.
    eapply one_out_converges_for_all.
  + intros s q Hyp_conv wt_tr ostable.
    only_two_cases s q wt_tr H.
    - exists all_out.
      repeat split.
      ++ constructor.
      ++ intros i mem.
         compute_coR mem.
         multiset_solver.
   - exists (g 𝟘).
      repeat split.
      ++ eapply lts_to_wt. constructor. constructor.
      ++ intros i mem.
         compute_coR mem.
         multiset_solver.
Qed.

Definition const : proc := g (cst a ? (cst a ! cst O • 𝟘)).

Definition ccat : proc := g (cst a ? (cst a ! (bvar 0) • 𝟘)).

Definition MyTest := g (cst a ! cst I • ①).

Lemma MyTest_is_not_good : ¬ good_VCCS MyTest.
Proof.
  intro imp. inversion imp; subst.
Qed.

Lemma constant_must_MyTest : const must_pass MyTest.
Proof.
  eapply m_step.
  - eapply MyTest_is_not_good.
  - exists ((cst a ! cst O • 𝟘)^(cst I) ▷ (g ①)).
    eapply ParSync.
    3 : { eapply lts_output. }
    2 : { eapply lts_input. }
    simpl; eauto.
  - intros ? Imp. inversion Imp.
  - intros ? Imp. inversion Imp.
  - intros ? ? ? ? ? tr_proc tr_test.
    inversion tr_proc; inversion tr_test; subst.
    eapply m_now. constructor.
Qed.

Lemma copycat_must_MyTest : ccat must_pass MyTest.
Proof.
  eapply m_step.
  - eapply MyTest_is_not_good.
  - exists ((cst a ! bvar 0 • 𝟘)^(cst I) ▷ (g ①)).
    eapply ParSync.
    3 : { eapply lts_output. }
    2 : { eapply lts_input. }
    simpl; eauto.
  - intros ? Imp. inversion Imp.
  - intros ? Imp. inversion Imp.
  - intros ? ? ? ? ? tr_proc tr_test.
    inversion tr_proc; inversion tr_test; subst.
    eapply m_now. constructor.
Qed.

Lemma NIL_must_not_pass_MyTest : ¬ ((g 𝟘) must_pass MyTest).
Proof.
  intro. inversion H.
  + eapply MyTest_is_not_good; eauto.
  + destruct ex as ((p',t') & tr_par).
    inversion tr_par;subst.
    * inversion l.
    * inversion l.
    * inversion l1.
Qed.

Lemma NIL_is_not_above_copycat : ccat ⋢ₘᵤₛₜᵢ g 𝟘.
Proof.
  intros Hyp.
  eapply NIL_must_not_pass_MyTest.
  eapply Hyp.
  eapply copycat_must_MyTest.
Qed.

Lemma NIL_is_not_above_constant : const ⋢ₘᵤₛₜᵢ g 𝟘.
Proof.
  intros Hyp.
  eapply NIL_must_not_pass_MyTest.
  eapply Hyp.
  eapply constant_must_MyTest.
Qed.

Definition MySynchTest := g (cst a ! cst I • g (cst a ? (If (bvar 0 == cst O) Then (g ①) Else (g 𝟘)))).

Lemma MySynchTest_is_not_good : ¬ good_VCCS MySynchTest.
Proof.
  intro imp. inversion imp; subst.
Qed.

Lemma MySubTest_is_not_good : ¬ good_VCCS (cst a ? (If bvar 0 == cst O
                                                    Then ① 
                                                    Else 𝟘)).
Proof.
  intro imp. inversion imp; subst.
Qed.

Lemma copycat_must_not_pass_MySynchTest : ¬ ccat must_pass MySynchTest.
Proof.
  intro Hyp. inversion Hyp; subst.
  + now eapply MySynchTest_is_not_good.
  + assert (g (cst a ! (bvar 0) • 𝟘)^(cst I) must_pass g (cst a ? (If (bvar 0 == cst O) Then (g ①) Else (g 𝟘)))) as Imp.
    { eapply com. 3 : { constructor. } 2 : { constructor. } simpl; eauto. }
    simpl in Imp. inversion Imp;subst.
    * now eapply MySubTest_is_not_good.
    * assert (g 𝟘 must_pass (If bvar 0 == cst O
                                  Then ① 
                                  Else 𝟘)^(cst I)) as Imp'.
      { eapply com0; try constructor. simpl; eauto. }
      assert (¬ g 𝟘 must_pass (If bvar 0 == cst O
                                  Then ① 
                                  Else 𝟘)^(cst I)) as Hyp'.
      { simpl. intro. eapply must_eq_client in H.
        2 : { eapply cgr_if_false. simpl. rewrite decide_False; eauto.
              intro H'. eapply neq; subst; eauto. }
      inversion H.
      - inversion H0.
      - inversion ex1. inversion H0;subst.
        ++ inversion l.
        ++ inversion l.
        ++ inversion l1. }
      contradiction.
Qed.

Lemma constant_must_MySynchTest : const must_pass MySynchTest.
Proof.
  eapply m_step.
  + now eapply MySynchTest_is_not_good.
  + eexists. eapply ParSync; try constructor. simpl; eauto.
  + intros ? Imp. inversion Imp.
  + intros ? Imp. inversion Imp.
  + intros ? ? ? ? ? tr_proc tr_test.
    inversion tr_proc. inversion tr_test. subst.
    simpl. eapply m_step.
    * eapply MySubTest_is_not_good.
    * eexists. eapply ParSync; try constructor. simpl; eauto.
    * intros ? Imp. inversion Imp.
    * intros ? Imp. inversion Imp.
    * intros ? ? ? ? duo tr_proc' tr_test'.
      inversion tr_proc'; subst.
      eapply simplify_match_output in duo; subst.
      inversion tr_test'; subst. simpl in *.
      eapply must_eq_client. eapply cgr_if_true_rev.
      - simpl. rewrite decide_True; eauto.
      - eapply m_now. constructor.
Qed.

Lemma copycat_is_not_above_const : const ⋢ₘᵤₛₜᵢ ccat.
Proof.
  intros Hyp.
  eapply copycat_must_not_pass_MySynchTest.
  eapply Hyp.
  eapply constant_must_MySynchTest.
Qed.

Definition MySynchTest2 := g (cst a ! cst I • g (cst a ? (If (bvar 0 == cst I) Then ① Else (g 𝟘)))).

Lemma MySynchTest2_is_not_good : ¬ good_VCCS MySynchTest2.
Proof.
  intro imp. inversion imp; subst.
Qed.

Lemma MySubTest2_is_not_good : ¬ good_VCCS (cst a ? (If bvar 0 == cst I
                                                    Then ① 
                                                    Else 𝟘)).
Proof.
  intro imp. inversion imp; subst.
Qed.

Lemma copycat_must_MySynchTest2 : ccat must_pass MySynchTest2.
Proof.
  eapply m_step.
  + now eapply MySynchTest2_is_not_good.
  + eexists. eapply ParSync; try constructor. simpl; eauto.
  + intros ? Imp. inversion Imp.
  + intros ? Imp. inversion Imp.
  + intros ? ? ? ? ? tr_proc tr_test.
    inversion tr_proc. inversion tr_test. subst.
    simpl. eapply m_step.
    * eapply MySubTest2_is_not_good.
    * eexists. eapply ParSync; try constructor. simpl; eauto.
    * intros ? Imp. inversion Imp.
    * intros ? Imp. inversion Imp.
    * intros ? ? ? ? duo tr_proc' tr_test'.
      inversion tr_proc'; subst.
      eapply simplify_match_output in duo; subst.
      inversion tr_test'; subst. simpl in *. inversion H;subst.
      eapply must_eq_client. eapply cgr_if_true_rev.
      - simpl. rewrite decide_True; eauto.
      - eapply m_now. constructor.
Qed.

Lemma constant_must_not_pass_MySynchTest2 : ¬ const must_pass MySynchTest2.
Proof.
  intro Hyp. inversion Hyp; subst.
  + now eapply MySynchTest_is_not_good.
  + assert (g (cst a ! cst O • 𝟘)^(cst I) must_pass g (cst a ? (If (bvar 0 == cst I) Then (g ①) Else (g 𝟘)))) as Imp.
    { eapply com. 3 : { constructor. } 2 : { constructor. } simpl; eauto. }
    simpl in Imp. inversion Imp;subst.
    * now eapply MySubTest_is_not_good.
    * assert (g 𝟘 must_pass (If bvar 0 == cst I
                                  Then ① 
                                  Else 𝟘)^(cst O)) as Imp'.
      { eapply com0; try constructor. simpl; eauto. }
      assert (¬ g 𝟘 must_pass (If bvar 0 == cst I
                                  Then ① 
                                  Else 𝟘)^(cst O)) as Hyp'.
      { simpl. intro. eapply must_eq_client in H. 
        2 : { eapply cgr_if_false. simpl. rewrite decide_False; eauto. exact neq. }
      inversion H.
      - inversion H0.
      - inversion ex1. inversion H0;subst.
        ++ inversion l.
        ++ inversion l.
        ++ inversion l1. }
      contradiction.
Qed.

Lemma const_is_not_above_copycat : ccat ⋢ₘᵤₛₜᵢ const.
Proof.
  intros Hyp.
  eapply constant_must_not_pass_MySynchTest2.
  eapply Hyp.
  eapply copycat_must_MySynchTest2.
Qed.

Definition MySynchTest3 := g ((cst a ! cst O • 𝟘) + (𝛕 • ①)).

Lemma MySynchTest3_is_not_good : ¬ good_VCCS MySynchTest3.
Proof.
  intro imp. inversion imp; subst.
  destruct H0; inversion H.
Qed.

Lemma NIL_must_MySynchTest3 : g 𝟘 must_pass MySynchTest3.
Proof.
  eapply m_step.
  + now eapply MySynchTest3_is_not_good.
  + eexists. eapply ParRight.
    eapply lts_choiceR. constructor.
  + intros ? Imp. inversion Imp.
  + intros ? tr_test. inversion tr_test;subst.
    * inversion H3.
    * inversion H3;subst. eapply m_now. constructor.
  + intros ? ? ? ? ? tr_proc tr_test.
    inversion tr_proc.
Qed.

Lemma copycat_must_not_pass_MySynchTest3 : ¬ ccat must_pass MySynchTest3.
Proof.
  intro Imp. inversion Imp; subst.
  + now eapply MySynchTest3_is_not_good.
  + assert (g (cst a ! (bvar 0) • 𝟘)^(cst O) must_pass (g 𝟘)).
    { eapply com; try constructor. 2 : { constructor. }
    simpl. eauto. }
    simpl in *.
    assert (¬ g (cst a ! cst O • 𝟘) must_pass g 𝟘).
    { intro Imp'; inversion Imp'; subst.
      * inversion H0.
      * inversion ex0. inversion H0;subst. inversion l. inversion l. inversion l2. }
    contradiction.
Qed.

Lemma copycat_is_not_NIL : g 𝟘 ⋢ₘᵤₛₜᵢ ccat.
Proof.
  intros Hyp.
  eapply copycat_must_not_pass_MySynchTest3.
  eapply Hyp.
  eapply NIL_must_MySynchTest3.
Qed.

Lemma constant_must_not_pass_MySynchTest3 : ¬ const must_pass MySynchTest3.
Proof.
  intro Imp. inversion Imp; subst.
  + now eapply MySynchTest3_is_not_good.
  + assert (g (cst a ! cst O • 𝟘)^(cst O) must_pass (g 𝟘)).
    { eapply com; try constructor. 2 : { constructor. }
    simpl. eauto. }
    simpl in *.
    assert (¬ g (cst a ! cst O • 𝟘) must_pass g 𝟘).
    { intro Imp'; inversion Imp'; subst.
      * inversion H0.
      * inversion ex0. inversion H0;subst. inversion l. inversion l. inversion l2. }
    contradiction.
Qed.

Lemma constant_is_not_NIL : g 𝟘 ⋢ₘᵤₛₜᵢ const.
Proof.
  intros Hyp.
  eapply constant_must_not_pass_MySynchTest3.
  eapply Hyp.
  eapply NIL_must_MySynchTest3.
Qed.

End VCCS_examples.
