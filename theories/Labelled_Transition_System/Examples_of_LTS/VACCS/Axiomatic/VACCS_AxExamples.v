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

(** * The VACCS proof system, exercised — and exactly what completeness still needs

    Two things here.

    First, a regression against [VACCS_Examples.v]: the two facts that file
    proves by long [must]-inductions using the OBA-with-feedback axioms are
    recovered from the proof system in **one and two rule applications**.

    Second, [completeness_from_NF]: soundness and the normal form together
    reduce completeness to a single statement about *normal forms*, i.e.
    about forwarder states.  That reduction is proved; the statement it
    reduces to is what remains to be done. *)

From Stdlib Require Import List PeanoNat Lia.
From stdpp Require Import base gmultiset.
From TestingTheory Require Import MultisetLTSConstruction.
From TestingTheory Require Import VACCS VACCS_Instance Must ActTau InputOutputActions
  gLts Bisimulation InteractionBetweenLts Testing_Predicate VACCS_Good WeakTransitions
  Subset_Act DefinitionAS Convergence VACCS_Static VACCS_Must_Characterization
  VACCS_Erasure VACCS_Shift VACCS_Precongruence VACCS_Expansion VACCS_ResNormalize
  VACCS_Copycat VACCS_Absorb VACCS_DefinitionAxiomatic VACCS_SoundnessAx VACCS_NormalForm
  VACCS_Forwarder VACCS_Cond2 VACCS_ReadySet VACCS_Canonical VACCS_Descent VACCS_Matching
  VACCS_Bad.
Import ListNotations.

Section VACCS_AxExamples.

Context `{VP : VACCS_Parameters}.

(** ** The copycat, from the system

    [VACCS_Examples.v] proves [ccat ≂ₘᵤₛₜᵢ 𝟘] with two ~40-line [must]
    inductions leaning on [OBA_with_FB_First/Fourth/Fifth_Axiom].  Here
    each direction is one rule. *)

Section Copycat.
Variable a : Channel.

Example ax_ccat_eq : ax_pre (ccat (cst a)) (g 𝟘) /\ ax_pre (g 𝟘) (ccat (cst a)).
Proof. split; [ apply ax_ccat_l | apply ax_ccat_r; reflexivity ]. Qed.

Example ccat_eq_nil : (ccat (cst a)) ≂ₘᵤₛₜᵢ (g 𝟘).
Proof. apply soundness_ax_eq; [ apply ax_ccat_l | apply ax_ccat_r; reflexivity ]. Qed.

(** ** The constant responder

    [VACCS_Examples.NIL_is_above_constant] chains two long lemmas.  Here it
    is [ax_resp] followed by [ax_ccat_l] — and the *converse* is false, as
    that file's separating test shows, which is exactly why [ax_resp] is an
    inequation and [ax_ccat] an equation. *)

Variable O : Value.

Example ax_const_below_nil : ax_pre (resp a (cst O)) (g 𝟘).
Proof. eapply ax_trans; [ apply ax_resp | apply ax_ccat_l ]. Qed.

Example const_below_nil : (resp a (cst O)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (g 𝟘).
Proof. apply soundness_ax. apply ax_const_below_nil. Qed.

(** A copycat in parallel with anything is invisible — the general
    forwarder law, by [ax_par] and the unit law for [‖]. *)
Example ax_ccat_par : forall p, ax_pre (p ‖ (ccat (cst a))) p.
Proof.
  intro p. eapply ax_trans; [ apply ax_par; [ apply ax_refl | apply ax_ccat_l ] | ].
  apply ax_cgr. apply cgr_par_nil.
Qed.

End Copycat.

(** ** The absorbing input, from the system

    A server that swallows a message and does nothing with it is invisible
    too — but for the opposite reason to the copycat, and by a different
    rule ([ax_input_drop], [VACCS_Absorb.v]).  Neither rule derives the
    other: [ax_ccat_l]'s guard re-emits, this one's does not. *)

Example ax_swallow_nil : forall c, ax_pre (g (c ? (g 𝟘))) (g 𝟘).
Proof.
  intro c.
  eapply ax_trans; [ apply ax_cgr; apply cgr_choice_nil_rev | ].
  apply ax_input_drop. intro v. simpl. apply bad_nil_any.
Qed.

Example swallow_nil : forall c, (g (c ? (g 𝟘))) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (g 𝟘).
Proof. intro c. apply soundness_ax. apply ax_swallow_nil. Qed.

(** ** What completeness reduces to

    Soundness plus the normal form turn completeness into a statement
    about normal forms only: it suffices to compare two
    [Ѵⁿ (msgs l ‖ g M)], i.e. two *forwarder states*.  Every process is
    [⊢]-equal to one, and [⊑ₘᵤₛₜᵢ] transports across those equalities by
    soundness. *)

Theorem completeness_from_NF :
  (forall n1 l1 M1 n2 l2 M2, gStatic M1 -> gStatic M2 ->
     (NF n1 l1 M1) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (NF n2 l2 M2) ->
     ax_pre (NF n1 l1 M1) (NF n2 l2 M2)) ->
  forall p q, Static p -> Static q -> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> ax_pre p q.
Proof.
  intros HNF p q Hp Hq Hpq.
  destruct (normal_form p Hp) as (n1 & l1 & M1 & HM1 & Ha1 & Hb1).
  destruct (normal_form q Hq) as (n2 & l2 & M2 & HM2 & Ha2 & Hb2).
  eapply ax_trans; [ exact Ha1 | ].
  eapply ax_trans; [ | exact Hb2 ].
  apply HNF; [ exact HM1 | exact HM2 | ].
  intros t Hm.
  apply (soundness_ax _ _ Ha2). apply Hpq. apply (soundness_ax _ _ Hb1). exact Hm.
Qed.

(** And the half of the characterisation that *is* available: soundness,
    in the shape [VACCS_Must_Characterization.v] states its corollaries. *)

Theorem ax_pre_sound : forall (p q : proc), ax_pre p q -> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q.
Proof. apply soundness_ax. Qed.


(** * REGRESSION: the whole new chain, on a configuration with an UNSTABLE left

    [VACCS_Bad.unstable_delivery_below_nil] machine-checks, by a direct
    [must] argument, that a pending message beside a guard that swallows
    it is below [𝟘].  Here the *same* inequation is obtained through the
    entire configuration-level apparatus built for completeness, which
    exercises it end to end:

      [ax_below_split_from_certificate]   (different bags, surplus on the left)
        → [ax_below_stable_split_bag]     ([msgs_app], surplus into the process)
        → [ax_below_stable_sum_cfg]       (Phase B at a bag)
        → [ax_phaseA_direct]              (Phase A by a settling simulation)
        → [ax_settle_sim]                 (the rule)

    and the only hypothesis it leaves — the certificate — is discharged
    here by exhibiting the settling run: the guard swallows the message
    and the residue emits nothing.

    Note the left configuration is **unstable** (the delivery is an
    internal step), which is exactly the case
    [ax_below_stable_NF_bag] cannot reach. *)

Section SplitRegression.
Context {c : Channel} {v : Value}.

Definition Swallow : gproc := (cst c) ? (g 𝟘).
Definition dm : list TypeOfActions := [((cst c) ▷ (cst v))].

Lemma swallow_settles : forall K : MO (ExtAct TypeOfActions),
  Settles (chans K) (((g Swallow) : proc) ▷ (bag dm ⊎ K)).
Proof.
  intro K.
  assert (EB : bag dm ⊎ K = {[+ ActOut ((cst c) ▷ (cst v)) +]} ⊎ K).
  { simpl. f_equal. apply (right_id_L (∅ : MO (ExtAct TypeOfActions))
                            (@disj_union (MO (ExtAct TypeOfActions)) _)). }
  rewrite EB.
  exists (((g 𝟘) : proc) ▷ K). split.
  - eapply wt_tau; [ | apply wt_nil ].
    apply fw_tau_deliver. unfold Swallow.
    assert (E : (g 𝟘 : proc) = ((g 𝟘) ^ (cst v))) by reflexivity.
    rewrite E at 2. apply lts_input.
  - split.
    + apply stable_of_no_step. apply fw_stable_iff. split.
      * intros z Hz. inversion Hz.
      * intros a Hin z Hz. inversion Hz.
    + intros d w r Hr. eapply emits_gsum_chans. exists w, r. exact Hr.
Qed.

Theorem ax_swallow_split : ax_pre (msgs (dm ++ []) ‖ g Swallow) (msgs [] ‖ g 𝟘).
Proof.
  apply ax_below_split_from_certificate with (N := 𝟘).
  - unfold Swallow. repeat constructor.
  - constructor.
  - intros p Hp. inversion Hp.
  - intros K Hout Hst. apply swallow_settles.
  - intros c0 v0 Q' l' Hs Hl. inversion Hl.
Qed.

Corollary ax_swallow_split_sound :
  (msgs (dm ++ []) ‖ g Swallow) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs [] ‖ g 𝟘).
Proof. apply soundness_ax. apply ax_swallow_split. Qed.

End SplitRegression.

(** ** Regression on the two drop laws, at concrete channels

    Both of these are derivations the system did **not** license before
    the two clauses were corrected, and they exercise different parts of
    it:

    - the first drops a guard whose continuation is a *nested* sum with a
      **sibling** dead guard.  [must]'s [com] field owes all the residues
      at a channel at once, so one failing sibling suffices — which is
      what [bad_stuck]'s [exists] clause now says and its universal
      predecessor could not.  Note the continuation [d ! y • 𝟘] is a live
      message on a third channel, so no per-branch certificate exists for
      it ([VACCS_Bad.msg_not_Bad]).

    - the second drops **two** guards in a row using only the presence of
      a [𝛕]-summand ([ax_sub_tau], through [ax_drop_tau]), with no
      condition whatsoever on the discarded continuations — [ax_input_drop]
      would need a certificate for [K1], and [ax_restrict] would need the
      sum to be stable, which it is not.  The reassociation between the
      two steps is plain [ax_cgr]. *)

Section DropRegression2.
Context {c d : Channel} {y : Value}.

Example ax_nested_drop_nil :
  ax_pre ((g ((cst c) ? ((g ((((cst d) ? (((cst d) ! (cst y) • 𝟘) : proc)) : gproc)
                          + ((cst d) ? ((g 𝟘) : proc)))) : proc))) : proc)
         ((g 𝟘) : proc).
Proof.
  eapply ax_trans; [ apply ax_cgr; apply cgr_choice_nil_rev | ].
  apply ax_nested_sibling_drop.
Qed.

Corollary nested_drop_nil_sound :
  ((g ((cst c) ? ((g ((((cst d) ? (((cst d) ! (cst y) • 𝟘) : proc)) : gproc)
                   + ((cst d) ? ((g 𝟘) : proc)))) : proc))) : proc)
  ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc).
Proof. apply soundness_ax. apply ax_nested_drop_nil. Qed.

Example ax_double_tau_drop : forall (K1 : proc),
  ax_pre ((g (((((cst c) ? K1) + ((cst c) ? ((g 𝟘) : proc)))) + (𝛕 • ((g 𝟘) : proc)))) : proc)
         ((g (𝛕 • ((g 𝟘) : proc))) : proc).
Proof.
  intro K1.
  eapply ax_trans;
    [ apply ax_cgr with
        (q := (g (((cst c) ? K1) + (((cst c) ? ((g 𝟘) : proc)) + (𝛕 • ((g 𝟘) : proc))))) : proc);
      apply cgr_choice_assoc | ].
  eapply ax_trans;
    [ apply ax_drop_tau; exists ((g 𝟘) : proc); apply lts_choiceR; apply lts_tau | ].
  apply ax_drop_tau. exists ((g 𝟘) : proc). apply lts_tau.
Qed.

Corollary double_tau_drop_sound : forall (K1 : proc),
  ((g (((((cst c) ? K1) + ((cst c) ? ((g 𝟘) : proc)))) + (𝛕 • ((g 𝟘) : proc)))) : proc)
  ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g (𝛕 • ((g 𝟘) : proc))) : proc).
Proof. intro K1. apply soundness_ax. apply ax_double_tau_drop. Qed.

End DropRegression2.


(** * REGRESSION: THE UNEQUAL-BAG CHAIN, END TO END

    [VACCS_Bad.unstable_delivery_below_nil] machine-checks, by a direct
    [must] argument, that a one-message bag sits below the empty one when
    the guard *swallows* the message.  Here the **same** inequation comes
    out of the whole unequal-bag apparatus:

        bag_incl_of_below_disj  (the two bags, by draining the right one)
      → msgs_cancel_surplus_disj (the common part cancelled, surplus left)
      → cert_of_split           (the certificate at the shifted buffer)
      → ax_below_split_from_certificate   (Phase A, Phase B, bag restored)

    and the recursive premise is **vacuous** here, [g 𝟘] having no input
    transition — which is why the chain can be exercised without the
    outer induction. *)

Section SplitChainRegression.
Variable c : ChannelData.
Variable v : ValueData.

Definition Sink : gproc := c ? ((g 𝟘) : proc).

Lemma sink_cfg_sem :
  (msgs [(c, v)] ‖ ((g Sink) : proc))
    ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs [] ‖ ((g (𝟘 : gproc)) : proc)).
Proof.
  assert (Hc : ((g (𝟘 : gproc)) : proc) ≡* (msgs [] ‖ ((g (𝟘 : gproc)) : proc))).
  { simpl. symmetry. etransitivity; [ apply cgr_par_com | apply cgr_par_nil ]. }
  intros t Ht.
  apply (proj2 (must_i_cgr _ _ Hc)).
  apply (unstable_delivery_below_nil c v). exact Ht.
Qed.

Theorem ax_sink_split :
  ax_pre (msgs [(c, v)] ‖ ((g Sink) : proc))
         (msgs [] ‖ ((g (𝟘 : gproc)) : proc)).
Proof.
  apply completeness_cfg_split_no_output.
  - repeat constructor.
  - constructor.
  - intros cc uu Hin. inversion Hin.
  - intros z Hz. inversion Hz.
  - apply sink_cfg_sem.
  - intros d Hperm cc vv Q' l' Hsub Hin. inversion Hin.
Qed.

End SplitChainRegression.


(** * REGRESSION: THE STEP ITSELF, WITH A VACUOUS INDUCTION HYPOTHESIS

    [completeness_step_of_mute_nf] is the head result of the
    configuration chain, and it takes an induction hypothesis it cannot
    normally be exercised without.  There is one place where that
    hypothesis is **vacuous**: [gsize 𝟘 = 0], so [size (g 𝟘) = 0] and no
    process is strictly smaller.

    So at [q := 𝟘] the whole step runs on its own, and it re-derives —
    through [normal_form_nores_sim], [DomOk], Phase A, Phase B and the
    bag machinery — the inequation [VACCS_Bad.unstable_delivery_below_nil]
    establishes by a direct [must] argument.  That is the non-vacuity
    control the head result was missing. *)

Section StepRegression.
Variable c : ChannelData.
Variable v : ValueData.

Theorem ax_sink_step :
  ax_pre (msgs [(c, v)] ‖ ((g (c ? ((g 𝟘) : proc))) : proc))
         ((g (𝟘 : gproc)) : proc).
Proof.
  apply completeness_step_of_mute_nf.
  - repeat constructor.
  - simpl. exact I.
  - apply MuteNF_cfg; [ repeat constructor | reflexivity ].
  - apply unstable_delivery_below_nil.
  - intros p' q' _ _ Hlt _. simpl in Hlt. lia.
Qed.


(** …and the same fact from the **restricted recursion**, which needs no
    induction hypothesis supplied by hand: [completeness_deep_cfg] is a
    closed theorem.  [VACCS_Bad.unstable_delivery_below_nil] establishes
    the inequation independently, so this is a control, not a definition. *)

Theorem ax_sink_deep :
  ax_pre (msgs [(c, v)] ‖ ((g (c ? ((g 𝟘) : proc))) : proc))
         ((g (𝟘 : gproc)) : proc).
Proof.
  apply completeness_deep_cfg.
  - repeat constructor.
  - simpl. exact I.
  - repeat constructor.
  - reflexivity.
  - apply unstable_delivery_below_nil.
Qed.

(** A second control, where the recursion is **not** vacuous: the right
    has an input transition, so the theorem really descends through
    [completeness_step_deep]'s recursive premise. *)

Theorem ax_guard_deep :
  ax_pre (msgs [] ‖ ((g (c ? ((g 𝟘) : proc))) : proc))
         ((g (c ? ((g 𝟘) : proc))) : proc).
Proof.
  assert (Hc : (msgs [] ‖ ((g (c ? ((g 𝟘) : proc))) : proc))
                 ≡* ((g (c ? ((g 𝟘) : proc))) : proc)).
  { simpl. etransitivity; [ apply cgr_par_com | apply cgr_par_nil ]. }
  apply completeness_deep_cfg.
  - repeat constructor.
  - simpl. exact I.
  - repeat constructor.
  - reflexivity.
  - exact (proj2 (must_i_cgr _ _ Hc)).
Qed.

End StepRegression.


(* ------------------------------------------------------------------ *)
(*  A SUM OF COPYCATS IS DERIVABLY BELOW [𝟘]                           *)
(*                                                                     *)
(*  The mute peeling criterion cannot say this: a copycat's            *)
(*  continuation *emits*, precisely on the channel of its own guard,   *)
(*  so [ochans] of the sum is not empty.  The [DropOk] criterion of    *)
(*  [VACCS_Matching.ax_gsum_drop_ochans] asks only that a              *)
(*  continuation emit **nowhere but on its own guard's channel**, and  *)
(*  that is exactly what a copycat does.                               *)
(*                                                                     *)
(*  This is the non-vacuity control for that criterion: the statement  *)
(*  is true independently (a copycat is invisible), and the new        *)
(*  peeling derives it — for a *sum*, which no single-guard rule       *)
(*  reaches.                                                           *)
(* ------------------------------------------------------------------ *)

Section CopycatSumRegression.
Context {ka kb : Channel}.

Lemma two_ccats_gStatic : gStatic ((ccatg (cst ka)) + (ccatg (cst kb))).
Proof. constructor; apply ccatg_gStatic. Qed.

Lemma two_ccats_copycats : gCopycats ((ccatg (cst ka)) + (ccatg (cst kb))).
Proof. simpl. split; reflexivity. Qed.

Lemma ax_two_ccats_below_nil :
  ax_pre ((g ((ccatg (cst ka)) + (ccatg (cst kb)))) : proc) ((g (𝟘 : gproc)) : proc).
Proof.
  apply ax_copycats_below_nil;
    [ apply two_ccats_gStatic | apply two_ccats_copycats ].
Qed.

(** …et le critère muet ne peut pas le dire. *)

Lemma two_ccats_not_mute :
  ochans ((g ((ccatg (cst ka)) + (ccatg (cst kb)))) : proc) <> [].
Proof. simpl. discriminate. Qed.

Lemma two_ccats_below_nil_sound :
  ((g ((ccatg (cst ka)) + (ccatg (cst kb)))) : proc)
    ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g (𝟘 : gproc)) : proc).
Proof. apply soundness_ax. apply ax_two_ccats_below_nil. Qed.

End CopycatSumRegression.

(* ------------------------------------------------------------------ *)
(*  A RETURNING GUARD WITH A NON-TRIVIAL RESIDUE                       *)
(*                                                                     *)
(*  [cfg_return_below_residue] does not need the guard to be a         *)
(*  copycat: it is enough that the continuation *returns* the bag      *)
(*  message.  Here the continuation returns it **and keeps a guard on  *)
(*  another channel**, so the residue is not [𝟘] and                   *)
(*  [cfg_copycat_guard_below_bag] does not apply.                      *)
(*                                                                     *)
(*  Noter que la somme entière disparaît malgré tout — le choix gardé  *)
(*  s'engage — et qu'il ne reste que ce que la garde choisie a laissé. *)
(* ------------------------------------------------------------------ *)

Lemma ax_return_residue_example :
  forall (c d : ChannelData) (u : ValueData),
  ax_pre ((msgs [(c,u)])
            ‖ ((g (c ? (((c ! (bvar 0) • 𝟘)) ‖ ((g (d ? ((g 𝟘) : proc))) : proc)))) : proc))
         ((msgs [(c,u)])
            ‖ ((((g (𝟘 : gproc)) : proc)) ‖ ((g (d ? ((g 𝟘) : proc))) : proc))).
Proof.
  intros c d u.
  eapply (cfg_return_below_residue _ [] c u _
            (((c ! u • 𝟘)) ‖ ((g (d ? ((g 𝟘) : proc))) : proc))).
  - reflexivity.
  - assert (E : subst_in_proc 0 u
                  ((((c ! (bvar 0) • 𝟘)) ‖ ((g (d ? ((g 𝟘) : proc))) : proc)) : proc)
                = ((((c ! u • 𝟘)) ‖ ((g (d ? ((g 𝟘) : proc))) : proc)) : proc))
      by reflexivity.
    rewrite <- E. apply lts_input.
  - apply lts_parL. apply lts_output.
Qed.

(* ------------------------------------------------------------------ *)
(*  …ET LE RENVOI PEUT ÊTRE DIFFÉRÉ                                     *)
(*                                                                     *)
(*  [cfg_return_below_residue_w] n'exige pas que la garde rende le      *)
(*  message *immédiatement* : elle peut travailler d'abord.  Ici la     *)
(*  continuation prend un [𝛕] avant de renvoyer, donc                   *)
(*  [cfg_return_below_residue] ne s'applique pas —                      *)
(*  [delayed_return_is_not_immediate] le machine-vérifie, une somme     *)
(*  gardée n'émettant jamais ([gsum_no_out]).                          *)
(* ------------------------------------------------------------------ *)

Lemma ax_delayed_return_example :
  forall (c : ChannelData) (u : ValueData),
  ax_pre ((msgs [(c,u)])
            ‖ ((g (c ? ((g (𝛕 • ((c ! (bvar 0) • 𝟘) : proc))) : proc))) : proc))
         ((msgs [(c,u)]) ‖ ((g (𝟘 : gproc)) : proc)).
Proof.
  intros c u.
  eapply (cfg_return_below_residue_w _ [] c u _
            ((g (𝛕 • ((c ! u • 𝟘) : proc))) : proc)
            ((c ! u • 𝟘) : proc)).
  - reflexivity.
  - assert (E : subst_in_proc 0 u ((g (𝛕 • ((c ! (bvar 0) • 𝟘) : proc))) : proc)
                = ((g (𝛕 • ((c ! u • 𝟘) : proc))) : proc)) by reflexivity.
    rewrite <- E. apply lts_input.
  - eapply wt_tau; [ apply lts_tau | apply wt_nil ].
  - apply lts_output.
Qed.

Lemma delayed_return_is_not_immediate :
  forall (c : ChannelData) (u : ValueData) K,
    ~ lts ((g (𝛕 • ((c ! u • 𝟘) : proc))) : proc) (ActExt (ActOut (c,u))) K.
Proof. intros c u K H. eapply gsum_no_out. exact H. Qed.

(* ------------------------------------------------------------------ *)
(*  …ET LE REJEU COUVRE UN RENVOI PRÉCÉDÉ D'UNE AUTRE DÉLIVRANCE        *)
(*                                                                     *)
(*  C'était l'écart nommé : le run consomme DEUX messages du sac avant  *)
(*  de les rendre.  Aucune des deux descentes ne l'atteint — elles ne   *)
(*  traitent qu'un message, rendu après des pas internes seulement.     *)
(*  [ax_cfg_replay_balanced] le fait, le sac servant les deux entrées   *)
(*  puis absorbant les deux sorties.                                   *)
(*                                                                     *)
(*  Les valeurs sont prises constantes pour que les continuations       *)
(*  soient closes : la substitution de l'entrée y est alors l'identité, *)
(*  ce qui évite toute comptabilité de de Bruijn.                       *)
(* ------------------------------------------------------------------ *)

Lemma ax_replay_two_messages :
  forall (a b : ChannelData) (UU WW : Value),
  ax_pre (msgs [(a, cst UU); (b, cst WW)]
            ‖ ((g (a ? ((g (b ? ((((a ! (cst UU) • 𝟘)) ‖ ((b ! (cst WW) • 𝟘))) : proc)))
                          : proc))) : proc))
         (msgs [(a, cst UU); (b, cst WW)]
            ‖ ((((g (𝟘 : gproc)) : proc)) ‖ (((g (𝟘 : gproc)) : proc)))).
Proof.
  intros a b UU WW.
  eapply (ax_cfg_replay_balanced
            [ActIn (a, cst UU); ActIn (b, cst WW);
             ActOut (a, cst UU); ActOut (b, cst WW)]).
  - eapply wt_act.
    { assert (E : subst_in_proc 0 (cst UU)
                    ((g (b ? ((((a ! (cst UU) • 𝟘)) ‖ ((b ! (cst WW) • 𝟘))) : proc)))
                       : proc)
                  = ((g (b ? ((((a ! (cst UU) • 𝟘)) ‖ ((b ! (cst WW) • 𝟘))) : proc)))
                       : proc))
        by reflexivity.
      rewrite <- E. apply lts_input. }
    eapply wt_act.
    { assert (E : subst_in_proc 0 (cst WW)
                    ((((a ! (cst UU) • 𝟘)) ‖ ((b ! (cst WW) • 𝟘))) : proc)
                  = ((((a ! (cst UU) • 𝟘)) ‖ ((b ! (cst WW) • 𝟘))) : proc))
        by reflexivity.
      rewrite <- E. apply lts_input. }
    simpl.
    eapply (wt_act _ _ _ (((g (𝟘 : gproc)) : proc) ‖ ((b ! (cst WW) • 𝟘) : proc)) _);
      [ apply lts_parL; apply lts_output | ].
    eapply (wt_act _ _ _ (((g (𝟘 : gproc)) : proc) ‖ ((g (𝟘 : gproc)) : proc)) _);
      [ apply lts_parR; apply lts_output | ].
    apply wt_nil.
  - simpl. multiset_solver.
  - simpl. multiset_solver.
Qed.

End VACCS_AxExamples.

(* ===================================================================== *)
(** * CONTROL: the derivations now come from the SEMANTICS alone

    [VACCS_Bad.ax_unstable_delivery_below_nil] derives its inequation by
    a hand-picked [ax_tau_step]; [ax_sink_split] above derives the same
    one by running the whole different-bags machinery.  With
    [must_iff_ax_below_nil] neither is needed: the semantic fact — which
    [VACCS_Bad.unstable_delivery_below_nil] establishes by a direct
    [must] argument — *is* the derivation.

    This is the point of the theorem, and the reason it is worth having
    even though it does not close the residue: below [𝟘] there is no gap
    between the preorder and the system, for **any** [Static] left-hand
    side. *)

Section CompletenessBelowNil.

Context `{VP : VACCS_Parameters}.
Context {ca : Channel} {va : Value}.

Corollary ax_sink_from_semantics :
  ax_pre ((((cst ca) ! (cst va) • 𝟘) ‖ ((g 𝟘) : proc))
            ‖ ((g ((cst ca) ? ((g 𝟘) : proc))) : proc))
         ((g 𝟘) : proc).
Proof.
  apply ax_of_below_nil.
  - repeat constructor.
  - apply unstable_delivery_below_nil.
Qed.

(** The copycat too: [ax_ccat_l] is a *rule*, and here the same
    inequation falls out of its semantic content instead. *)
Corollary ax_ccat_from_semantics : ax_pre (ccat (cst ca)) ((g 𝟘) : proc).
Proof.
  apply ax_of_below_nil;
    [ unfold ccat; apply static_g; apply ccat_gStatic | apply must_i_ccat_l ].
Qed.

End CompletenessBelowNil.
