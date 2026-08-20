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

(** * The copycat law, for an arbitrary channel

        [ccat c := c ? (c ! x • 𝟘)]        [ccat c ≂ₘᵤₛₜᵢ 𝟘]

    A one-shot forwarder is invisible: whatever a test sends it, it sends
    straight back, so no test can tell it apart from a process that never
    listened at all.  This is the process-level shadow of the *buffer*'s
    [lts_multiset_add] rule ([MultisetLTSConstruction.v]) — "accept any
    input at any time, storing the dual output" — which is what makes the
    forwarder construction able to absorb every input, and hence what
    makes VACCS's must-preorder coarser than VCCS's.

    [VACCS_Examples.v] proves this for a *constant* channel [cst a] (with
    a spurious two-distinct-values hypothesis inherited from its section).
    Both directions are generalised here to an arbitrary
    [c : ChannelData], which is what the axiom system needs: a [Static]
    process may perfectly well listen on a de Bruijn channel under a [ν].
    The proofs are the repository's own, with [cst a] replaced by [c]
    throughout — they never used anything about the channel.

    ** Why this has to be a *rule*

    No other rule can put a bare input guard on the right of [⊑] without
    one already being on the left: [ax_input] and [ax_choice_input]
    preserve the guard, [ax_int_glb] needs a [𝛕], and [ax_share_in] needs
    the left-hand side to be an internal choice of two sums each already
    offering [c].  So [⊢ g 𝟘 ⊑ ccat c] is underivable without it, while
    being semantically true — the system would be incomplete. *)

From Stdlib.Program Require Import Equality.
From stdpp Require Import base.
From TestingTheory Require Import InputOutputActions ActTau Must VACCS_Must_Characterization
  gLts Bisimulation Lts_OBA Lts_FW Lts_OBA_FB ParallelLTSConstruction
  InteractionBetweenLts Testing_Predicate DefinitionAS VACCS VACCS_Good VACCS_Instance
  Convergence WeakTransitions Subset_Act MultisetLTSConstruction Termination
  VACCS_Static VACCS_Erasure VACCS_Precongruence.

Section VACCS_Copycat.

Context `{VP : VACCS_Parameters}.

(** The one-shot forwarder on channel [c]. *)
Definition ccat (c : ChannelData) : proc := c ? (c ! (bvar 0) • 𝟘).

Lemma ccat_gStatic : forall c, gStatic (c ? (c ! (bvar 0) • 𝟘)).
Proof. intros c. constructor. constructor. Qed.

Lemma must_i_ccat_r : forall c, g 𝟘 ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (ccat c).
Proof.
  intros c e Hyp.
  dependent induction Hyp.
  - eapply m_now. eauto.
  - clear H2.
    eapply m_step; eauto.
    + inversion ex; subst. inversion H; subst.
      * lts_inversion lts.
      * exists (ccat c ▷ b2). eapply ParRight. eauto.
      * inversion l1.
    + intros. eauto. inversion H.
    + intros. destruct μ1 as [ b | b ].
      * inversion H2. subst. simpl in *.
        eapply simplify_match_input in H. subst.
        destruct (decide (good_VACCS t')).
        -- eapply m_now. eauto.
        -- eapply m_step; eauto.
           ++ inversion ex. inversion H; subst.
              ** inversion l.
              ** unfold lts_step in l; simpl in *.
                 assert (lts e ((c , v) !) t') as HypTr; eauto.
                 eapply OBA_with_FB_Fifth_Axiom in HypTr
                    as [(t'' & HypTr' & t'0 & HypTr'0 & equiv')|(t'' & HypTr' & equiv'')]; eauto.
                 --- exists (c ! v • 𝟘 ▷ t''). eapply ParRight. eauto.
                 --- assert (lts (c ! v • 𝟘) ((c , v) !) (g 𝟘)).
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
                   unfold non_blocking; simpl. exists (c , v); eauto. }
                 assert (must (ccat c) e1); eauto.
                 eapply must_preserved_by_synch_if_notoutcome; eauto.
                 simpl; eauto.
           ++ intros. inversion H4; subst. simpl in *.
              eapply simplify_match_output in H. subst.
              eapply OBA_with_FB_Fourth_Axiom in H3 as (e'1 & HypTr'1 & equiv1); eauto.
              eapply (@must_eq_client proc); eauto.
      * lts_inversion lts.
Qed.

Lemma must_i_ccat_l : forall c, (ccat c) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (g 𝟘).
Proof.
  intros c t Hyp.
  assert (must (ccat c) t) as Mq; eauto.
  dependent induction Hyp.
  - now eapply m_now.
  - inversion ex. inversion H2; subst.
    + inversion l.
    + eapply m_step.
      * eauto.
      * exists ((g 𝟘) ▷ b2). eapply ParRight; eauto.
      * intros. lts_inversion lts.
      * intros. eapply H0; [ exact H3 | reflexivity | apply et; exact H3 ].
      * intros. lts_inversion lts.
    + inversion l1; subst.
      eapply simplify_match_input in eq. subst.
      assert (must ((c ! (bvar 0) • 𝟘) ^ v) b2) as Mq'.
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

(** ** A *responder* is only below the copycat, never equal to it

    [resp a V := a ? (a ! V • 𝟘)] answers on the same channel but with a
    value of its own choosing.  It is **not** a forwarder: the buffer's
    [lts_multiset_add] stores the *dual of what it absorbed*, faithfully,
    and that fidelity is exactly what buys the *equation* [ccat c ≂ 𝟘].
    An unfaithful responder only gets the *inequation*, and the repository
    already records the separating test for [V := cst O]
    ([VACCS_Examples.v]): a test that sends [I] and checks it gets [I]
    back is passed by [𝟘] — which self-synchronises — and failed by
    [resp a O], which answers [O].

    The asymmetry shows up *inside the proofs*, which is the point:

    - [must_i_ccat_l] discharges its hard case with the **feedback** axiom
      [OBA_with_FB_Fourth_Axiom]: the test's own output-then-input round
      trip can be reassembled into a single [τ] precisely because the
      value comes back unchanged.
    - here that step is unavailable, and the proof must instead
      *reconstruct* the test's ability to receive a **different** value,
      via [TransitionShapeForInput] and [Congruence_Respects_Transition].
      That reconstruction needs [VarC_add n c = c], so it only works for a
      **constant** channel — which is why this law, unlike the copycat
      law, is stated for [cst a] and not for an arbitrary [ChannelData].

    So the forwarder does not merely suggest the laws, it grades them:
    faithful re-emission gives an equation at any channel, unfaithful
    re-emission gives an inequation at constant channels only. *)

Section Responder.

Variable a : Channel.
Variable V : ValueData.

Definition resp : proc := (cst a) ? ((cst a) ! V • 𝟘).

Lemma must_i_resp_below_ccat : resp ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (ccat (cst a)).
Proof.
  intros t HypMust.
  dependent induction HypMust.
  - now apply m_now.
  - eapply m_step; eauto.
    + inversion ex; subst. inversion H2; subst.
      * inversion l.
      * exists (ccat (cst a) ▷ b2). eapply ParRight. eauto.
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
        eapply (must_preserved_by_synch_if_notoutcome resp ((cst a ! V • 𝟘) ^ v) t t'
                  (ActIn (cst a , v))) in Mp'; eauto.
        inversion Mp'. contradiction.
        inversion ex0. inversion H5; subst.
        -- inversion l.
        -- exists ((cst a ! (bvar 0) • 𝟘) ^ v ▷ b2). eapply ParRight; eauto.
        -- inversion l1; subst. eapply simplify_match_output in eq as eq'; subst.
           assert (t' ⟶[ActIn (cst a , subst_Data 0 v V)] b2) as l'2; eauto.
           eapply TransitionShapeForInput in l2 as (p1 & g1 & r1 & n & equiv1 & equiv2 & eq1).
           edestruct (Congruence_Respects_Transition t') as (t'1 & Tr'1 & equiv'1).
           { exists (Ѵ n (((gpr_input (a) p1 + g1) ‖ r1))). split; eauto.
             eapply lts_res_ext_n. eapply lts_parL.
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
           eapply (@must_eq_client proc); eauto. assert (¬ good_VACCS t'1) as not_happyA.
           { eapply unoutcome_preserved_by_eq; eauto. }
           assert (¬ good_VACCS t1) as not_happyB.
           { eapply unoutcome_preserved_by_lts_non_blocking_action_converse; eauto.
             unfold non_blocking; simpl. exists (cst a , v); eauto. }
           assert (must (ccat (cst a)) t1); eauto.
           eapply must_preserved_by_synch_if_notoutcome; eauto.
      * intros. inversion H6; subst.
        eapply simplify_match_output in H5 as eq; subst.
        assert (lts t ((cst a , v) !) t') as l2; eauto.
        eapply OBA_with_FB_Fourth_Axiom in l2 as (t'1 & HypTr'1 & equiv1); eauto.
        eapply (@must_eq_client proc); eauto.
        assert (must resp t) as Mp. eapply m_step; eauto.
        assert (must resp t'1) as Mp';eauto.
        assert (must (ccat (cst a)) t'1); eauto.
        apply (must_i_ccat_l (cst a)). exact H8.
Qed.

(** …and hence below [𝟘], by the copycat law. *)
Corollary must_i_resp_l : resp ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (g 𝟘).
Proof. intros t Hm. apply (must_i_ccat_l (cst a)). apply must_i_resp_below_ccat. exact Hm. Qed.

End Responder.

(** * A whole SUM of copycats is invisible too

    Guarded choice commits, so a sum of copycats can absorb a message on
    one channel and thereby lose the ability to absorb on the others —
    and yet it is still below [𝟘], because *every* branch is a no-op:
    whichever one is taken, the message comes straight back.

    This generalises [must_i_ccat_r] and is what makes the multi-channel
    mirror reachable: [ax_expansion_l] applied to [g M ‖ g CC], with [CC]
    the sum of copycat guards on all the right-hand side's channels,
    produces one mirror summand per channel in a single step.

    The proof is the one-copycat proof unchanged in shape.  Its only
    interesting field is [com]: the sum's guard absorbs [(c,v)], the
    client emitted it, so [TransitionShapeForOutputSimplified] gives
    [t ≡* (c!v•𝟘) ‖ t'], and [par_bridge_rev] moves the message from the
    *client* side back to the *server* side — which is exactly the state
    the copycat is in after absorbing.  So the asynchronous bridge of
    [VACCS_Precongruence.v] is doing the real work here. *)

Fixpoint gCopycats (M : gproc) : Prop :=
  match M with
  | gpr_success => True
  | gpr_nil => True
  | gpr_input c p => p = (c ! (bvar 0) • 𝟘)
  | gpr_tau _ => False
  | gpr_choice M1 M2 => gCopycats M1 /\ gCopycats M2
  end.

Lemma gCopycats_no_tau : forall M, gCopycats M -> forall p, ~ lts (g M) τ p.
Proof.
  induction M as [ | | c q | q | M1 IH1 M2 IH2 ]; intros Hc p Hl; simpl in *;
    inversion Hl; subst.
  - contradiction.
  - destruct Hc as [Hc1 Hc2]. eapply IH1; eassumption.
  - destruct Hc as [Hc1 Hc2]. eapply IH2; eassumption.
Qed.

Lemma gCopycats_lts : forall M, gCopycats M ->
  forall mu p, lts (g M) (ActExt mu) p ->
  exists c v, mu = ActIn (c,v) /\ p = (c ! v • 𝟘).
Proof.
  induction M as [ | | c q | q | M1 IH1 M2 IH2 ]; intros Hc mu p Hl; simpl in *;
    inversion Hl; subst.
  - exists c, v. split; reflexivity.
  - destruct Hc as [Hc1 Hc2]. eapply IH1; eassumption.
  - destruct Hc as [Hc1 Hc2]. eapply IH2; eassumption.
Qed.

Theorem must_i_nil_below_copycats : forall (M : gproc), gCopycats M ->
  (g 𝟘) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (g M).
Proof.
  intros M Hcop t Hm. remember (g 𝟘) as p0 eqn:Heq.
  induction Hm; subst.
  - apply m_now. assumption.
  - apply m_step.
    + assumption.
    + destruct ex as (u & Hu). inversion Hu; subst; unfold lts_step in *; simpl in *.
      * inversion l.
      * eexists. eapply ParRight. eassumption.
      * inversion l1.
    + intros p' Hp'. exfalso. eapply gCopycats_no_tau; eassumption.
    + intros t' Ht'. eapply H0; [ exact Ht' | reflexivity ].
    + intros p' t' mu1 mu2 Hd Hl1 Hl2.
      destruct (gCopycats_lts M Hcop mu1 p' Hl1) as (c & v & Hmu & Hp). subst.
      destruct mu2 as [[c2 v2]|[c2 v2]]; simpl in Hd; try (exfalso; exact Hd).
      inversion Hd; subst.
      assert (Horig : (g 𝟘) must_pass t) by (apply m_step; assumption).
      assert (Hsh : t ≡* ((c2 ! v2 • 𝟘) ‖ t'))
        by (eapply TransitionShapeForOutputSimplified; exact Hl2).
      assert (Hpar : (g 𝟘) must_pass ((c2 ! v2 • 𝟘) ‖ t'))
        by (eapply must_eq_client; [ exact Hsh | exact Horig ]).
      assert (Hres : ((g 𝟘) ‖ (c2 ! v2 • 𝟘)) must_pass t').
      { apply (par_bridge_rev (g 𝟘) ((c2 ! v2 • 𝟘) ‖ t') Hpar (c2 ! v2 • 𝟘) t').
        reflexivity. }
      assert (Hc : ((g 𝟘) ‖ (c2 ! v2 • 𝟘)) ≂ₘᵤₛₜᵢ (c2 ! v2 • 𝟘)).
      { apply must_i_cgr. etransitivity; [ apply cgr_par_com | apply cgr_par_nil ]. }
      destruct Hc as [Hc1 Hc2]. apply Hc2. exact Hres.
Qed.

End VACCS_Copycat.
