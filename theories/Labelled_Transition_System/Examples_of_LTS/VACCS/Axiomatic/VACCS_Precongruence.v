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

(** * Precongruence lemmas for [⊑ₘᵤₛₜᵢ] on VACCS

    Building blocks for a Hennessy-Ingólfsdóttir-style inequational proof
    system for the must-preorder on VACCS. This file collects the lemmas
    that don't require case-splitting on the parallel operator. *)

From Stdlib.Program Require Import Equality.
From stdpp Require Import base.
From TestingTheory Require Import VACCS VACCS_Instance Must ActTau InputOutputActions
  gLts Bisimulation InteractionBetweenLts Testing_Predicate VACCS_Good WeakTransitions
  Subset_Act DefinitionAS Convergence VACCS_Static VACCS_Must_Characterization VACCS_Erasure VACCS_Shift.

Section VACCS_Precongruence.

Context `{VP : VACCS_Parameters}.

(** ** Internal-choice inequations

    [⊕] is not primitive in this VACCS syntax; it is definable as [𝛕•X + 𝛕•Y].
    The key Hennessy-Ingólfsdóttir inequation [X⊕Y ⊑ X] (resp. [⊑ Y]) holds
    here because [must]'s [m_step] constructor's [pt] field already forces
    every τ-successor of the client to must-pass — [𝛕•X + 𝛕•Y] has exactly
    two τ-successors, [X] and [Y], so weakening to just one of them is free. *)

Lemma must_i_int_choice_l (X Y : proc) : g ((𝛕 • X) + (𝛕 • Y)) ⊑ₘᵤₛₜᵢ X.
Proof.
  intros t Hm.
  destruct Hm as [Ho | Ho Hex Hpt Het Hcom].
  - now apply m_now.
  - apply Hpt.
    eapply lts_choiceL.
    eapply lts_tau.
Qed.

Lemma must_i_int_choice_r (X Y : proc) : g ((𝛕 • X) + (𝛕 • Y)) ⊑ₘᵤₛₜᵢ Y.
Proof.
  intros t Hm.
  destruct Hm as [Ho | Ho Hex Hpt Het Hcom].
  - now apply m_now.
  - apply Hpt.
    eapply lts_choiceR.
    eapply lts_tau.
Qed.

(** ** Internal choice is the greatest lower bound, not merely a lower bound

    [must_i_int_choice_l]/[_r] above say [𝛕X + 𝛕Y] is *below* each of [X]
    and [Y] — glb *elimination*. The matching *introduction* rule is
    [must_i_int_glb_pre] below: anything below both is below the internal
    choice. Both directions are needed; without the introduction rule
    there is no way at all to establish [_ ⊑ 𝛕q₁ + 𝛕q₂], since an
    internal choice is not stable and so [must_i_choice_stable_compat]
    ([VACCS_ReadySet.v]) does not apply to it either. (Found while
    analysing what [CompletenessAx.v] needs; [DefinitionAxiomatic.v]
    gained the corresponding [ax_int_glb].)

    Proved by induction on *one* of the two given [must]-facts with the
    other [revert]-ed first, so that it is carried into every generated
    IH — the same idiom as the merge equations' "join" direction
    ([must_i_input_join_branches] etc.) further down this file. Two
    details worth noting: the [pt] field needs the original
    [q1 must_pass t] back, which is recovered from the destructured
    fields by [apply m_step; assumption] (a direct term application
    fails to elaborate here); and the [com] field is *vacuous* because a
    [𝛕]-guarded sum has no external transitions at all. *)

Lemma must_i_int_glb : forall (q1 q2 : proc) t,
  q1 must_pass t -> q2 must_pass t -> (g ((𝛕 • q1) + (𝛕 • q2))) must_pass t.
Proof.
  intros q1 q2 t Hm1 Hm2.
  revert Hm2. revert q2.
  induction Hm1 as [t Hout | p t nh ex pt IHpt et IHet com IHcom]; intros q2 Hm2.
  - now apply m_now.
  - assert (Hp : p must_pass t) by (apply m_step; assumption).
    apply m_step.
    + exact nh.
    + exists (p, t). eapply ParLeft. apply lts_choiceL. apply lts_tau.
    + intros p' Hp'. inversion Hp'; subst.
      * inversion H3; subst. exact Hp.
      * inversion H3; subst. exact Hm2.
    + intros t' Ht'. apply IHet; [exact Ht' |].
      inversion Hm2; subst.
      * exfalso. apply nh. assumption.
      * eapply et0. exact Ht'.
    + intros p' t' μ1 μ2 Hdual Hp' Ht'. inversion Hp'; subst; inversion H3.
Qed.

Lemma must_i_int_glb_pre : forall (p q1 q2 : proc),
  p ⊑ₘᵤₛₜᵢ q1 -> p ⊑ₘᵤₛₜᵢ q2 -> p ⊑ₘᵤₛₜᵢ (g ((𝛕 • q1) + (𝛕 • q2))).
Proof.
  intros p q1 q2 H1 H2 t Ht.
  apply must_i_int_glb; [apply H1 | apply H2]; exact Ht.
Qed.

(** ** Separating [𝛕] from a mixed sum

    [X + 𝛕•(g Y) ≂ₘᵤₛₜᵢ 𝛕•(g (X + Y)) ⊕ 𝛕•(g Y)] — the law that turns a
    *mixed* sum (external guards sitting beside a [𝛕]-guard) into an
    internal choice of sums that are one [𝛕]-guard closer to being
    stable. Iterating it is what produces the [⊕]-of-stable-sums shape
    that [CompletenessAx.v]'s matching argument needs;
    [VACCS_Canonical.v]'s [canonical] alone does not deliver it, because
    it says nothing about [𝛕]-guards.

    Note what the law is **not**: it does *not* say the [𝛕]-guard's
    external siblings can be turned into a second internal branch on
    their own. [VACCS_MixedSumProbes.v] refutes that, machine-checked —
    [X] has to be carried along *into the first branch* ([X + Y]), which
    is exactly what keeps [X]'s offers available to satisfy the [ex]
    field there. Dropping [X] would strengthen the requirement and
    change the semantics.

    The crux is [must_i_tau_sep_aux]: the left-hand side's obligations
    plus [g Y]'s own obligations suffice for [g (X + Y)]. Its [ex] field
    is the interesting one — it is discharged from *[Y]'s* interaction,
    lifted through [lts_choiceR], precisely because the mixed sum's own
    [ex] may have been satisfied by the [𝛕] alone and so says nothing
    about [X]. *)

Lemma must_i_tau_sep_aux : forall (X Y : gproc) t,
  g (X + (𝛕 • (g Y))) must_pass t -> g Y must_pass t -> g (X + Y) must_pass t.
Proof.
  intros X Y t HL HY.
  remember (g (X + (𝛕 • (g Y)))) as L eqn:EL.
  revert EL HY.
  induction HL as [t Hout | u t nh ex pt IHpt et IHet com IHcom]; intros EL HY.
  - now apply m_now.
  - subst u.
    apply m_step.
    + exact nh.
    + inversion HY; subst; [exfalso; apply nh; assumption |].
      destruct ex0 as ((a2,b2) & Hstep). inversion Hstep; subst.
      * exists (a2,b2). eapply ParLeft. apply lts_choiceR. exact l.
      * exists (g (X + Y), b2). eapply ParRight. exact l.
      * exists (a2,b2). eapply (ParSync μ1 μ2); [exact eq | apply lts_choiceR; exact l1 | exact l2].
    + intros p' Hp'. inversion Hp'; subst.
      * apply pt. apply lts_choiceL. exact H3.
      * inversion HY; subst; [exfalso; apply nh; assumption | apply pt0; exact H3].
    + intros t' Ht'. apply IHet; [exact Ht' | reflexivity |].
      inversion HY; subst; [exfalso; apply nh; assumption | eapply et0; exact Ht'].
    + intros p' t' μ1 μ2 Hdual Hp' Ht'. inversion Hp'; subst.
      * eapply com; [exact Hdual | apply lts_choiceL; exact H3 | exact Ht'].
      * inversion HY; subst; [exfalso; apply nh; assumption |].
        eapply com0; [exact Hdual | exact H3 | exact Ht'].
Qed.

Lemma must_i_tau_sep_l : forall (X Y : gproc) t,
  g (X + (𝛕 • (g Y))) must_pass t ->
  g ((𝛕 • (g (X + Y))) + (𝛕 • (g Y))) must_pass t.
Proof.
  intros X Y t HL.
  inversion HL; subst.
  - now apply m_now.
  - assert (HY : g Y must_pass t) by (apply pt; apply lts_choiceR; apply lts_tau).
    apply must_i_int_glb.
    + apply must_i_tau_sep_aux; assumption.
    + exact HY.
Qed.

Lemma must_i_tau_sep_r : forall (X Y : gproc) t,
  g ((𝛕 • (g (X + Y))) + (𝛕 • (g Y))) must_pass t ->
  g (X + (𝛕 • (g Y))) must_pass t.
Proof.
  intros X Y t HR.
  remember (g ((𝛕 • (g (X + Y))) + (𝛕 • (g Y)))) as R eqn:ER.
  revert ER.
  induction HR as [t Hout | u t nh ex pt IHpt et IHet com IHcom]; intro ER.
  - now apply m_now.
  - subst u.
    assert (HXY : g (X + Y) must_pass t) by (apply pt; apply lts_choiceL; apply lts_tau).
    assert (HY : g Y must_pass t) by (apply pt; apply lts_choiceR; apply lts_tau).
    apply m_step.
    + exact nh.
    + eexists. eapply ParLeft. apply lts_choiceR. apply lts_tau.
    + intros p' Hp'. inversion Hp'; subst.
      * inversion HXY; subst; [exfalso; apply nh; assumption |].
        apply pt0. apply lts_choiceL. exact H3.
      * inversion H3; subst. exact HY.
    + intros t' Ht'. apply IHet; [exact Ht' | reflexivity].
    + intros p' t' μ1 μ2 Hdual Hp' Ht'. inversion Hp'; subst.
      * inversion HXY; subst; [exfalso; apply nh; assumption |].
        eapply com0; [exact Hdual | apply lts_choiceL; exact H3 | exact Ht'].
      * inversion H3.
Qed.

Corollary must_i_tau_sep_pre_l : forall (X Y : gproc),
  g (X + (𝛕 • (g Y))) ⊑ₘᵤₛₜᵢ g ((𝛕 • (g (X + Y))) + (𝛕 • (g Y))).
Proof. intros X Y t H. apply must_i_tau_sep_l. exact H. Qed.

Corollary must_i_tau_sep_pre_r : forall (X Y : gproc),
  g ((𝛕 • (g (X + Y))) + (𝛕 • (g Y))) ⊑ₘᵤₛₜᵢ g (X + (𝛕 • (g Y))).
Proof. intros X Y t H. apply must_i_tau_sep_r. exact H. Qed.

(** ** Convexity of acceptance sets

    [g X ⊕ g ((X+Y)+Z) ⊑ₘᵤₛₜᵢ g (X+Y)] — the internal choice between a
    sum and a *larger* sum lies below every sum in between. This is the
    convex-closure condition of acceptance-tree semantics, and
    [DefinitionAxiomatic.v]'s [ax_convex] is exactly this rule; the
    comment there records the counterexample showing it is not derivable
    from the others, i.e. that completeness genuinely needs it.

    The whole content is [must_i_convex_aux]: [X+Y] discharges each of
    its obligations from *one* of the two hypotheses, chosen by which
    side of the sum the transition came from — [X]'s from [g X]'s own
    fact, [Y]'s from [g ((X+Y)+Z)]'s (where [Y] sits as
    [lts_choiceL ∘ lts_choiceR]). [Z] is never inspected, which is why
    it may be arbitrary; and no stability is needed anywhere, since even
    a [𝛕] inside [X] or [Y] is covered by the corresponding hypothesis's
    own [pt] field. *)

Lemma must_i_convex_aux : forall (X Y Z : gproc) t,
  g X must_pass t -> g ((X + Y) + Z) must_pass t -> g (X + Y) must_pass t.
Proof.
  intros X Y Z t HX HW.
  remember (g X) as L eqn:EL.
  revert EL HW.
  induction HX as [t Hout | u t nh ex pt IHpt et IHet com IHcom]; intros EL HW.
  - now apply m_now.
  - subst u.
    apply m_step.
    + exact nh.
    + destruct ex as ((a2,b2) & Hstep). inversion Hstep; subst.
      * exists (a2,b2). eapply ParLeft. apply lts_choiceL. exact l.
      * exists (g (X + Y), b2). eapply ParRight. exact l.
      * exists (a2,b2). eapply (ParSync μ1 μ2); [exact eq | apply lts_choiceL; exact l1 | exact l2].
    + intros p' Hp'. inversion Hp'; subst.
      * apply pt. exact H3.
      * inversion HW; subst; [exfalso; apply nh; assumption |].
        apply pt0. apply lts_choiceL. apply lts_choiceR. exact H3.
    + intros t' Ht'. apply IHet; [exact Ht' | reflexivity |].
      inversion HW; subst; [exfalso; apply nh; assumption | eapply et0; exact Ht'].
    + intros p' t' μ1 μ2 Hdual Hp' Ht'. inversion Hp'; subst.
      * eapply com; [exact Hdual | exact H3 | exact Ht'].
      * inversion HW; subst; [exfalso; apply nh; assumption |].
        eapply com0; [exact Hdual | apply lts_choiceL; apply lts_choiceR; exact H3 | exact Ht'].
Qed.

Lemma must_i_convex : forall (X Y Z : gproc) t,
  g ((𝛕 • (g X)) + (𝛕 • (g ((X + Y) + Z)))) must_pass t -> g (X + Y) must_pass t.
Proof.
  intros X Y Z t H.
  inversion H; subst.
  - now apply m_now.
  - apply must_i_convex_aux with (Z := Z).
    + apply pt. apply lts_choiceL. apply lts_tau.
    + apply pt. apply lts_choiceR. apply lts_tau.
Qed.

Corollary must_i_convex_pre : forall (X Y Z : gproc),
  g ((𝛕 • (g X)) + (𝛕 • (g ((X + Y) + Z)))) ⊑ₘᵤₛₜᵢ g (X + Y).
Proof. intros X Y Z t Ht. apply must_i_convex with (Z := Z). exact Ht. Qed.

(** ** Continuation sharing

    Two branches of an internal choice that offer the *same* action may
    pool their continuations there, keeping the first branch's ready set:

      [(k•P + X') ⊕ (k•Q + Y')  ⊑ₘᵤₛₜᵢ  k•(P ⊕ Q) + X']

    This is the *uniformity* condition of acceptance-tree normal forms —
    the continuation function is shared by every acceptance set — and it
    is what lets a derivation use one leaf for the ready set and another
    for the continuation. Nothing else in the system does that:
    [ax_int_l]/[_r] reach only a whole branch, the merge and
    distributivity laws reduce the goal to itself, and [ax_convex]
    *transfers* a restricted target but cannot introduce one (with its
    [Y] empty it reduces, through [ax_int_glb], to its own conclusion).
    [DefinitionAxiomatic.v] gains [ax_share_in]/[ax_share_out].

    The proof is the file's usual [remember] + induct-on-one-fact idiom.
    The [com] field is where the two hypotheses meet: a synchronisation
    on [k] takes the target to [P ⊕ Q], and the two branches supply
    [P]'s and [Q]'s obligations separately — [must_i_int_glb] assembles
    them. Every other field comes from the first branch alone, which is
    why the first branch's residue [X'] is the one that survives.

    **No side conditions.** Neither stability nor [Static]-ness of
    [X']/[Y'] is needed: a [𝛕] inside [X'] is handled by the first
    branch's own [pt] field, and [Y'] is only ever consulted through the
    second branch's [com]. *)

Lemma must_i_share_in_aux : forall c P Q X' Y' t,
  g ((c ? P) + X') must_pass t -> g ((c ? Q) + Y') must_pass t ->
  g ((c ? (g ((𝛕 • P) + (𝛕 • Q)))) + X') must_pass t.
Proof.
  intros c P Q X' Y' t H1 H2.
  remember (g ((c ? P) + X')) as L eqn:EL.
  revert EL H2.
  induction H1 as [t Hout | u t nh ex pt IHpt et IHet com IHcom]; intros EL H2.
  - now apply m_now.
  - subst u.
    apply m_step.
    + exact nh.
    + destruct ex as ((a2,b2) & Hstep). inversion Hstep; subst.
      * inversion l; subst.
        { inversion H4. }
        { exists (a2, b2). eapply ParLeft. apply lts_choiceR. exact H4. }
      * exists (g ((c ? (g ((𝛕 • P) + (𝛕 • Q)))) + X'), b2).
        eapply ParRight. exact l.
      * inversion l1; subst.
        { inversion H4; subst. eexists.
          eapply ParSync; [exact eq | apply lts_choiceL; apply lts_input | exact l2]. }
        { exists (a2,b2). eapply ParSync;
            [exact eq | apply lts_choiceR; exact H4 | exact l2]. }
    + intros p' Hp'. inversion Hp'; subst.
      * inversion H4.
      * apply pt. apply lts_choiceR. exact H4.
    + intros t' Ht'. apply IHet; [exact Ht' | reflexivity |].
      inversion H2; subst; [exfalso; apply nh; assumption | eapply et0; exact Ht'].
    + intros p' t' μ1 μ2 Hdual Hp' Ht'. inversion Hp'; subst.
      * inversion H4; subst. simpl.
        apply must_i_int_glb.
        { eapply com; [exact Hdual | apply lts_choiceL; apply lts_input | exact Ht']. }
        { inversion H2; subst; [exfalso; apply nh; assumption |].
          eapply com0; [exact Hdual | apply lts_choiceL; apply lts_input | exact Ht']. }
      * eapply com; [exact Hdual | apply lts_choiceR; exact H4 | exact Ht'].
Qed.

Corollary must_i_share_in_pre : forall c P Q X' Y',
  g ((𝛕 • (g ((c ? P) + X'))) + (𝛕 • (g ((c ? Q) + Y'))))
    ⊑ₘᵤₛₜᵢ g ((c ? (g ((𝛕 • P) + (𝛕 • Q)))) + X').
Proof.
  intros c P Q X' Y' t H. inversion H; subst.
  - now apply m_now.
  - apply must_i_share_in_aux with (Y' := Y') (Q := Q).
    + apply pt. apply lts_choiceL. apply lts_tau.
    + apply pt. apply lts_choiceR. apply lts_tau.
Qed.

Fixpoint gAllTau (M : gproc) : Prop :=
match M with
| 𝛕 • _ => True
| M1 + M2 => gAllTau M1 /\ gAllTau M2
| _ => False
end.

Lemma gAllTau_has_tau : forall Y, gAllTau Y -> exists r, lts (g Y) τ r.
Proof.
  induction Y; intro H; simpl in H; try contradiction.
  - exists p. apply lts_tau.
  - destruct H as (H1 & H2). destruct (IHY1 H1) as (r & Hr).
    exists r. apply lts_choiceL. exact Hr.
Qed.

Lemma gAllTau_no_ext : forall Y, gAllTau Y -> forall mu r, ~ lts (g Y) (ActExt mu) r.
Proof.
  induction Y; intros H mu r Hl; simpl in H; try contradiction.
  - inversion Hl.
  - destruct H as (H1 & H2). inversion Hl; subst.
    + eapply IHY1; eassumption.
    + eapply IHY2; eassumption.
Qed.

(** An all-[𝛕] part of a sum inherits the whole sum's obligations: it
    supplies its own [ex] (it always has a [𝛕]) and owes no [com] (it has
    no external transitions). *)
Lemma must_i_alltau_part : forall (X Y : gproc) t, gAllTau Y ->
  g (X + Y) must_pass t -> g Y must_pass t.
Proof.
  intros X Y t HY Hm.
  remember (g (X + Y)) as L eqn:EL.
  revert EL.
  induction Hm as [t Hout | u t nh ex pt IHpt et IHet com IHcom]; intro EL.
  - now apply m_now.
  - subst u.
    apply m_step.
    + exact nh.
    + destruct (gAllTau_has_tau Y HY) as (r & Hr).
      exists (r, t). eapply ParLeft. exact Hr.
    + intros r Hr. apply pt. apply lts_choiceR. exact Hr.
    + intros t' Ht'. apply IHet; [exact Ht' | reflexivity].
    + intros r t' μ1 μ2 Hdual Hr Ht'.
      exfalso. eapply gAllTau_no_ext; [exact HY | exact Hr].
Qed.

Lemma must_i_tau_flatten_l : forall (X Y : gproc) t, gAllTau Y ->
  g (X + (𝛕 • (g Y))) must_pass t -> g (X + Y) must_pass t.
Proof.
  intros X Y t HY Hm.
  remember (g (X + (𝛕 • (g Y)))) as L eqn:EL.
  revert EL.
  induction Hm as [t Hout | u t nh ex pt IHpt et IHet com IHcom]; intro EL.
  - now apply m_now.
  - subst u.
    assert (HgY : g Y must_pass t) by (apply pt; apply lts_choiceR; apply lts_tau).
    apply m_step.
    + exact nh.
    + destruct (gAllTau_has_tau Y HY) as (r & Hr).
      exists (r, t). eapply ParLeft. apply lts_choiceR. exact Hr.
    + intros r Hr. inversion Hr; subst.
      * apply pt. apply lts_choiceL. exact H3.
      * inversion HgY; subst; [exfalso; apply nh; assumption | apply pt0; exact H3].
    + intros t' Ht'. apply IHet; [exact Ht' | reflexivity].
    + intros r t' μ1 μ2 Hdual Hr Ht'. inversion Hr; subst.
      * eapply com; [exact Hdual | apply lts_choiceL; exact H3 | exact Ht'].
      * exfalso. eapply gAllTau_no_ext; [exact HY | exact H3].
Qed.

Lemma must_i_tau_flatten_r : forall (X Y : gproc) t, gAllTau Y ->
  g (X + Y) must_pass t -> g (X + (𝛕 • (g Y))) must_pass t.
Proof.
  intros X Y t HY Hm.
  remember (g (X + Y)) as L eqn:EL.
  revert EL.
  induction Hm as [t Hout | u t nh ex pt IHpt et IHet com IHcom]; intro EL.
  - now apply m_now.
  - assert (HgY : g Y must_pass t)
      by (apply (must_i_alltau_part X Y t HY); rewrite <- EL; apply m_step; assumption).
    subst u.
    apply m_step.
    + exact nh.
    + eexists. eapply ParLeft. apply lts_choiceR. apply lts_tau.
    + intros r Hr. inversion Hr; subst.
      * apply pt. apply lts_choiceL. exact H3.
      * inversion H3; subst. exact HgY.
    + intros t' Ht'. apply IHet; [exact Ht' | reflexivity].
    + intros r t' μ1 μ2 Hdual Hr Ht'. inversion Hr; subst.
      * eapply com; [exact Hdual | apply lts_choiceL; exact H3 | exact Ht'].
      * inversion H3.
Qed.

Corollary must_i_tau_flatten_pre_l : forall (X Y : gproc), gAllTau Y ->
  g (X + (𝛕 • (g Y))) ⊑ₘᵤₛₜᵢ g (X + Y).
Proof. intros X Y HY t H. apply must_i_tau_flatten_l; assumption. Qed.

Corollary must_i_tau_flatten_pre_r : forall (X Y : gproc), gAllTau Y ->
  g (X + Y) ⊑ₘᵤₛₜᵢ g (X + (𝛕 • (g Y))).
Proof. intros X Y HY t H. apply must_i_tau_flatten_r; assumption. Qed.

Lemma must_i_choice_tau_compat : forall (p p' : proc) (gq : gproc),
  p ⊑ₘᵤₛₜᵢ p' -> g ((𝛕 • p) + gq) ⊑ₘᵤₛₜᵢ g ((𝛕 • p') + gq).
Proof.
  intros p p' gq Hpre t Hm.
  remember (g ((𝛕 • p) + gq)) as L eqn:EL.
  revert EL.
  induction Hm as [t Hout | u t nh ex pt IHpt et IHet com IHcom]; intro EL.
  - now apply m_now.
  - subst u.
    apply m_step.
    + exact nh.
    + eexists. eapply ParLeft. apply lts_choiceL. apply lts_tau.
    + intros r Hr. inversion Hr; subst.
      * inversion H3; subst. apply Hpre. apply pt. apply lts_choiceL. apply lts_tau.
      * apply pt. apply lts_choiceR. exact H3.
    + intros t' Ht'. apply IHet; [exact Ht' | reflexivity].
    + intros r t' μ1 μ2 Hdual Hr Ht'. inversion Hr; subst.
      * inversion H3.
      * eapply com; [exact Hdual | apply lts_choiceR; exact H3 | exact Ht'].
Qed.

(** ** Structural congruence is a (near-)free source of equations

    Since VACCS's [gLtsEq] instance takes [⋍ := ≡*] (structural congruence),
    every axiom of [cgr_step] (commutativity/associativity of [‖]/[+],
    unit laws, scope extrusion, [If]-reduction, [rec]-unfolding, ...) gives
    a sound equation for [⊑ₘᵤₛₜᵢ] via [must_eq_server]/[must_eq_client]. *)

Lemma must_i_cgr (p q : proc) : p ≡* q -> p ≂ₘᵤₛₜᵢ q.
Proof.
  intros Hcgr. split.
  - intros t Hm. eapply must_eq_server; [symmetry; exact Hcgr | exact Hm].
  - intros t Hm. eapply must_eq_server; [exact Hcgr | exact Hm].
Qed.

(** ** Precongruence for the output prefix

    [must_eq_client]/[must_eq_server]'s technique (transferring transitions
    one-for-one via [eq_spec]) does NOT apply here: [⊑ₘᵤₛₜᵢ] is an
    asymmetric preorder, not a bisimulation, so it gives no operational
    correspondence between [p]'s and [q]'s individual steps. Instead we
    induct directly on the [must] derivation (via [remember], to avoid the
    dependent-type/JMeq mess of [dependent induction] on this heavily
    indexed type), using [Hpq] as a black box exactly where [p]'s own
    behaviour becomes externally observable (the [com] field), and the
    automatically-generated induction hypothesis everywhere the recursion
    is on the *test*'s structure (the [et] field). *)

Lemma must_i_tau_compat (p q : proc) : p ⊑ₘᵤₛₜᵢ q -> g (𝛕 • p) ⊑ₘᵤₛₜᵢ g (𝛕 • q).
Proof.
  intros Hpq t Hm.
  remember (g (𝛕 • p)) as P eqn:HP.
  induction Hm.
  - now apply m_now.
  - subst.
    apply m_step.
    + exact nh.
    + destruct ex as ((a2, b2) & Hstep).
      inversion Hstep; subst.
      * inversion l; subst.
        exists (q, b2).
        eapply ParLeft.
        eapply lts_tau.
      * exists (g (𝛕 • q), b2).
        eapply ParRight.
        exact l.
      * inversion l1.
    + intros p' Hp'.
      inversion Hp'; subst.
      eapply Hpq.
      eapply pt.
      eapply lts_tau.
    + intros t' Ht'.
      eapply H0; [exact Ht' | reflexivity].
    + intros p' t' μ1 μ2 Hdual Hp' Ht'.
      inversion Hp'.
Qed.

(** ** Weak transitions and stability under restriction

    Building blocks toward a [ν]-precongruence for the acceptance-set
    characterisation [≼ₐₛ] (routed through since, unlike the output/τ
    prefixes, [ν]'s transition target is a *descendant* of its argument,
    not the argument itself — see the [VACCS_Precongruence] module
    docstring in the plan/session notes for why direct [must]-induction
    doesn't apply here). *)

Lemma res_wt_forward : forall p s0 q,
  p ⟹[s0] q -> forall sx, s0 = List.map (VarC_action_add 1) sx -> (ν p) ⟹[sx] (ν q).
Proof.
  intros p s0 q Hw.
  induction Hw; intros sx Heq.
  - destruct sx; [| simpl in Heq; discriminate].
    constructor.
  - eapply wt_tau; [eapply lts_res_tau; exact l | eapply IHHw; exact Heq].
  - destruct sx as [|μ_ext sx']; simpl in Heq; [discriminate|].
    inversion Heq; subst.
    eapply wt_act; [eapply lts_res_ext; exact l | eapply IHHw; reflexivity].
Qed.

Lemma res_wt_backward : forall p s q,
  (ν p) ⟹[s] q -> exists q', q = ν q' /\ p ⟹[List.map (VarC_action_add 1) s] q'.
Proof.
  intros p s q Hw.
  remember (ν p) as P eqn:HP.
  revert p HP.
  induction Hw; intros p0 HP; subst.
  - exists p0.
    split; [reflexivity | constructor].
  - inversion l; subst.
    edestruct IHHw as (q' & Hq' & Hw'); [reflexivity|].
    exists q'.
    split; [exact Hq' | eapply wt_tau; [exact H0 | exact Hw']].
  - inversion l; subst.
    edestruct IHHw as (q' & Hq' & Hw'); [reflexivity|].
    exists q'.
    split; [exact Hq' |].
    simpl.
    eapply wt_act; [exact H1 | exact Hw'].
Qed.

Lemma res_stable_iff : forall q, (ν q) ↛ <-> q ↛.
Proof.
  intros q. split.
  - intros Hst. destruct (decide (q ↛)) as [Hd|Hd]; [exact Hd|].
    exfalso. eapply lts_refuses_spec1 in Hd as (r & Hl).
    eapply lts_refuses_spec2 in Hst. apply Hst. exists (ν r). eapply lts_res_tau. exact Hl.
  - intros Hst. destruct (decide ((ν q) ↛)) as [Hd|Hd]; [exact Hd|].
    exfalso. eapply lts_refuses_spec1 in Hd as (r & Hl).
    inversion Hl; subst.
    eapply lts_refuses_spec2 in Hst. apply Hst. exists p'. exact H0.
Qed.

Lemma res_ext_stable_iff : forall p mu, (ν p) ↛[mu] <-> p ↛[VarC_action_add 1 mu].
Proof.
  intros p mu. split.
  - intros Hst. destruct (decide (p ↛[VarC_action_add 1 mu])) as [Hd|Hd]; [exact Hd|].
    exfalso. eapply lts_refuses_spec1 in Hd as (r & Hl).
    eapply lts_refuses_spec2 in Hst. apply Hst. exists (ν r). eapply lts_res_ext. exact Hl.
  - intros Hst. destruct (decide ((ν p) ↛[mu])) as [Hd|Hd]; [exact Hd|].
    exfalso. eapply lts_refuses_spec1 in Hd as (r & Hl).
    inversion Hl; subst.
    eapply lts_refuses_spec2 in Hst. apply Hst. exists p'. exact H1.
Qed.

(** ** The abstracted co-refusal set [coR] under restriction

    [coR p := fun μ1 => ∃μ2, ¬p↛[μ2] ∧ dual μ2 μ1 ∧ blocking μ1]
    (Subset_Act.v). Since [dual] (= [ext_act_match]) forces μ2 to be
    exactly the complementary action of μ1 on the same channel/value,
    and [res_ext_stable_iff] transports refusal of a *single* label
    faithfully across [ν], the whole set transports too — in *both*
    directions, giving a clean iff (not just the "outward" direction
    [VarC_action_add_co_rev]/[VarC_action_add_co_rev_map] already proved
    in [VACCS_Instance.v]). Monotonicity (all that
    [must_i_res_compat]/[≼ₐₛ]-precongruence actually needs) is then a
    one-line corollary. *)

Lemma res_coR_iff : forall p mu1, mu1 ∈ coR (ν p) <-> (VarC_action_add 1 mu1) ∈ coR p.
Proof.
  intros p mu1.
  unfold coR, elem_of, subset_of in *.
  simpl.
  split.
  - intros (mu2 & Hnr & Hd & Hb).
    exists (VarC_action_add 1 mu2).
    repeat split.
    + intro Hc. apply Hnr. apply res_ext_stable_iff. exact Hc.
    + destruct mu2 as [x|x]; destruct mu1 as [y|y].
      1: simpl in Hd |- *; exact (match Hd with end).
      1: destruct x as [c v]; destruct y as [c' v']; simpl in Hd |- *; inversion Hd; subst; reflexivity.
      1: destruct x as [c v]; destruct y as [c' v']; simpl in Hd |- *; inversion Hd; subst; reflexivity.
      1: exact (match Hd with end).
    + (* Unlike VCCS, [blocking] is not vacuous here: [non_blocking] is
         [is_output], so [coR] only ever contains *inputs*.  Both sides of
         the shift are inputs, so the condition transports; on the output
         side the hypothesis is already contradictory. *)
      unfold non_blocking_output, is_output in *.
      destruct mu1 as [[c v]|[c v]].
      * intros (a & Ha); discriminate.
      * exfalso; apply Hb; eexists; reflexivity.
  - intros (mu2 & Hnr & Hd & Hb).
    unfold elem_of, subset_of in *.
    destruct mu1 as [[c1 v1]|[c1 v1]]; destruct mu2 as [[c2 v2]|[c2 v2]]; simpl in Hd, Hb |- *;
      try (exact (match Hd with end)); inversion Hd; subst.
    + exists (ActOut (c1,v1)). repeat split.
      all: [> (intro Hc; apply Hnr; apply res_ext_stable_iff in Hc; simpl in Hc; exact Hc)
            | (unfold non_blocking_output, is_output in *; intros (a & Ha); discriminate) ].
    + exists (ActIn (c1,v1)). repeat split.
      all: [> (intro Hc; apply Hnr; apply res_ext_stable_iff in Hc; simpl in Hc; exact Hc)
            | (unfold non_blocking_output, is_output in *;
               exfalso; apply Hb; eexists; reflexivity) ].
Qed.

Lemma res_coR_mono : forall p q,
  (forall x, x ∈ coR p -> x ∈ coR q) -> forall y, y ∈ coR (ν p) -> y ∈ coR (ν q).
Proof.
  intros p q Hsub y Hy.
  apply res_coR_iff. apply Hsub. apply res_coR_iff. exact Hy.
Qed.

(** ** Lifting [res_coR_iff] through VACCS's label abstraction [𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ]

    [≼ₐₛ]'s [bhv_pre_cond2] (DefinitionAS.v) is stated over the *image*
    [⌈𝝳∘Φ⌉(coR p')], not raw [coR p'] — abstracted-set inclusion does not
    in general imply raw-set inclusion, so [res_coR_mono] alone isn't
    enough. The fix: [𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ] commutes with the channel shift
    ([VarC_action_add]/[VarC_preaction_add]) by direct computation — both
    sides just extract-and-rewrap the channel component — so
    [res_coR_iff] lifts through the abstraction essentially for free. *)

Lemma Phi_delta_shift_commute : forall mu,
  𝝳ᴠᴀᴄᴄꜱ (Φᴠᴀᴄᴄꜱ (VarC_action_add 1 mu)) = VarC_preaction_add 1 (𝝳ᴠᴀᴄᴄꜱ (Φᴠᴀᴄᴄꜱ mu)).
Proof.
  intros [[c v]|[c v]]; reflexivity.
Qed.

Lemma res_coR_abs_iff : forall p x,
  x ∈ ⌈ 𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ ⌉ (coR (ν p)) <-> (VarC_preaction_add 1 x) ∈ ⌈ 𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ ⌉ (coR p).
Proof.
  intros p x. unfold elem_of, subset_of, map_set in *. simpl.
  split.
  - intros (mu1 & Hmu1 & Hx).
    exists (VarC_action_add 1 mu1). split.
    + apply res_coR_iff. exact Hmu1.
    + rewrite Hx. symmetry. apply Phi_delta_shift_commute.
  - intros (mu2 & Hmu2 & Heq).
    (* VACCS's [FinA] has the single constructor [Inputs c]: the abstraction
       erases the value *and* the polarity, keeping only the channel. *)
    destruct x as [cx]; destruct mu2 as [[c2 v2]|[c2 v2]]; simpl in Heq; inversion Heq; subst.
    + exists (ActIn (cx, v2)). split.
      * apply res_coR_iff. simpl. exact Hmu2.
      * reflexivity.
    + (* an output is never in [coR] here: [blocking] means "is an input" *)
      exfalso. unfold elem_of, subset_of, coR in Hmu2.
      destruct Hmu2 as (? & _ & _ & Hb).
      unfold non_blocking_output, is_output in Hb.
      apply Hb. eexists; reflexivity.
Qed.

Lemma res_coR_abs_mono : forall p q,
  (forall x, x ∈ ⌈ 𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ ⌉ (coR p) -> x ∈ ⌈ 𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ ⌉ (coR q)) ->
  forall y, y ∈ ⌈ 𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ ⌉ (coR (ν p)) -> y ∈ ⌈ 𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ ⌉ (coR (ν q)).
Proof.
  intros p q Hsub y Hy.
  apply res_coR_abs_iff. apply Hsub. apply res_coR_abs_iff. exact Hy.
Qed.

(** ** [ν]-precongruence for [≼ₐₛ], and the [⊑ₘᵤₛₜᵢ] corollary

    Assembles [Static_converge] (cond1, trivial on the [Static] fragment),
    [res_wt_backward]/[res_wt_forward] (relate [(ν _) ⟹[s] _] to the
    underlying process's own weak transitions), [res_stable_iff]
    (transfer stability), and [res_coR_abs_mono] (transfer the
    acceptance-set inclusion) into the full [≼ₐₛ]-precongruence for [ν],
    then bridges to [⊑ₘᵤₛₜᵢ] via [must_iff_acceptance_set_VACCS_without_toFW]
    (`VACCS_Must_Characterization.v`). *)

Lemma must_i_res_bhv_pre : forall p q, Static p -> Static q -> p ≼ₐₛ q -> (ν p) ≼ₐₛ (ν q).
Proof.
  intros p q Hsp Hsq (Hc1 & Hc2).
  split.
  - intros s _. apply Static_converge. apply static_res. exact Hsq.
  - intros s q'' _ Hwq Hstq.
    destruct (res_wt_backward q s q'' Hwq) as (q''' & Hq'' & Hwq').
    subst q''.
    rewrite res_stable_iff in Hstq.
    destruct (Hc2 (List.map (VarC_action_add 1) s) q''' (Static_converge _ p Hsp) Hwq' Hstq) as (p''' & Hwp' & Hstp & Hincl).
    exists (ν p''').
    repeat split.
    + apply res_wt_forward with (s0 := List.map (VarC_action_add 1) s); [exact Hwp' | reflexivity].
    + apply res_stable_iff. exact Hstp.
    + intros x Hx.
      eapply (res_coR_abs_mono p''' q'''); [exact Hincl | exact Hx].
Qed.

(** ** [ν]-precongruence, via the restriction bridge

    The [≼ₐₛ] toolkit just above cannot be cashed in: unlike VCCS, VACCS
    has no [must_iff_acceptance_set_VACCS_without_toFW] — every alternative
    characterisation of [⊑ₘᵤₛₜᵢ] here goes through the forwarder [p ▷ ∅],
    because asynchrony makes the bare-process acceptance-set preorder too
    fine.  So [must_i_res_bhv_pre] above, though proved, is unusable.

    Instead, the same move as for [‖]: put the context into the test.
    [(ν p) | t] and [p | t↑] are *the same system*.  [lts_res_tau] and
    [lts_res_ext] already characterise [ν]'s transitions in both
    directions by inversion, and a shifted test [t↑] can only ever act on
    shifted channels, so it can never synchronise on the restricted one —
    which is exactly what [ν] hides.  [VACCS_Shift.v] supplies the
    transport of transitions along [NewVarC] in both directions, and
    [NewVarC_respects_good] ([VACCS_Good.v]) says the outcome predicate
    does not see the shift at all. *)

Lemma NewVar_in_action_at_zero : forall mu, NewVar_in_action 0 mu = VarC_action_add 1 mu.
Proof. intros [[c v]|[c v]]; simpl; f_equal; f_equal; apply NewVarC_at_zero. Qed.

Lemma NewVarC_act_at_zero : forall mu, NewVarC_act 0 (ActExt mu) = ActExt (VarC_action_add 1 mu).
Proof. intros mu. rewrite NewVarC_act_ext. f_equal. apply NewVar_in_action_at_zero. Qed.

Lemma dual_shift : forall (mu1 mu2 : ExtAct TypeOfActions), dual mu1 mu2 ->
  dual (VarC_action_add 1 mu1) (VarC_action_add 1 mu2).
Proof.
  intros [[c v]|[c v]] [[d w]|[d w]] Hd; simpl in *;
    try (exact (match Hd with end)); inversion Hd; subst; reflexivity.
Qed.

(** The inverse: a label dual to a shifted one is itself a shift.  This is
    what lets the [com] field pull the *server*'s action back through [ν]. *)
Lemma dual_shift_inv : forall (nu1 : ExtAct TypeOfActions) (mu2 : ExtAct TypeOfActions),
  dual nu1 (VarC_action_add 1 mu2) -> exists mu1, nu1 = VarC_action_add 1 mu1 /\ dual mu1 mu2.
Proof.
  intros nu1 [[c v]|[c v]] Hd; destruct nu1 as [[d w]|[d w]]; simpl in Hd;
    try (exact (match Hd with end)); inversion Hd; subst.
  - exists (ActOut (c, v)). split; reflexivity.
  - exists (ActIn (c, v)). split; reflexivity.
Qed.

Lemma res_bridge_fwd : forall (P t : proc), P must_pass t ->
  forall p, P = ν p -> p must_pass (NewVarC 0 t).
Proof.
  intros P t Hm. induction Hm as [ P t Ho | P t Ho Hex Hpt IHpt Het IHet Hcom IHcom ];
    intros p Heq; subst.
  - apply m_now. apply NewVarC_respects_good. exact Ho.
  - apply m_step.
    + intro Hg. apply Ho. apply (NewVarC_respects_good 0). exact Hg.
    + destruct Hex as ((x1,x2) & Hs). inversion Hs; subst.
      * inversion l; subst. exists (p' ▷ NewVarC 0 x2). eapply ParLeft. eassumption.
      * exists (p ▷ NewVarC 0 x2). eapply ParRight. apply (lts_NewVarC _ _ _ l 0).
      * inversion l1; subst.
        exists (p' ▷ NewVarC 0 x2).
        eapply ParSync; [ apply dual_shift; exact eq | eassumption | ].
        pose proof (lts_NewVarC _ _ _ l2 0) as Hl2.
        rewrite NewVarC_act_at_zero in Hl2. exact Hl2.
    + intros p' Hp'. eapply (IHpt (ν p')); [ apply lts_res_tau; exact Hp' | reflexivity ].
    + intros u Hu. destruct (lts_NewVarC_inv _ _ _ _ Hu) as (a0 & t' & Ha & Hu' & Hlt).
      destruct a0 as [mu0|]; [ rewrite NewVarC_act_ext in Ha; discriminate Ha | ].
      subst. eapply IHet; [ exact Hlt | reflexivity ].
    + intros p' u nu1 nu2 Hd Hp' Hu.
      destruct (lts_NewVarC_inv _ _ _ _ Hu) as (a0 & t' & Ha & Hu' & Hlt).
      destruct a0 as [mu2|]; [ | simpl in Ha; discriminate Ha ].
      rewrite NewVarC_act_at_zero in Ha. inversion Ha as [Ha']. clear Ha. subst.
      destruct (dual_shift_inv nu1 mu2 Hd) as (mu1 & Hmu1 & Hdm). subst.
      eapply (IHcom (ν p') t' mu1 mu2);
        [ exact Hdm | apply lts_res_ext; exact Hp' | exact Hlt | reflexivity ].
Qed.

Lemma res_bridge_rev : forall (p T : proc), p must_pass T ->
  forall t, T = NewVarC 0 t -> (ν p) must_pass t.
Proof.
  intros p T Hm. induction Hm as [ p T Ho | p T Ho Hex Hpt IHpt Het IHet Hcom IHcom ];
    intros t Heq; subst.
  - apply m_now. apply (NewVarC_respects_good 0). exact Ho.
  - apply m_step.
    + intro Hg. apply Ho. apply NewVarC_respects_good. exact Hg.
    + destruct Hex as ((x1,x2) & Hs). inversion Hs; subst.
      * exists ((ν x1) ▷ t). eapply ParLeft. apply lts_res_tau. eassumption.
      * destruct (lts_NewVarC_inv _ _ _ _ l) as (a0 & t' & Ha & Hu' & Hlt).
        destruct a0 as [mu0|]; [ rewrite NewVarC_act_ext in Ha; discriminate Ha | ].
        exists ((ν x1) ▷ t'). eapply ParRight. exact Hlt.
      * destruct (lts_NewVarC_inv _ _ _ _ l2) as (a0 & t' & Ha & Hu' & Hlt).
        destruct a0 as [mu2|]; [ | simpl in Ha; discriminate Ha ].
        rewrite NewVarC_act_at_zero in Ha. inversion Ha as [Ha']. clear Ha. subst.
        destruct (dual_shift_inv μ1 mu2 eq) as (mu1 & Hmu1 & Hdm). subst.
        exists ((ν x1) ▷ t').
        eapply ParSync; [ exact Hdm | apply lts_res_ext; exact l1 | exact Hlt ].
    + intros x Hx. inversion Hx; subst. eapply IHpt; [ eassumption | reflexivity ].
    + intros t' Ht'. eapply (IHet (NewVarC 0 t'));
        [ apply (lts_NewVarC _ _ _ Ht' 0) | reflexivity ].
    + intros x t' mu1 mu2 Hd Hx Ht'. inversion Hx; subst.
      eapply (IHcom p' (NewVarC 0 t') (VarC_action_add 1 mu1) (VarC_action_add 1 mu2));
        [ apply dual_shift; exact Hd | eassumption | | reflexivity ].
      pose proof (lts_NewVarC _ _ _ Ht' 0) as Hl.
      rewrite NewVarC_act_at_zero in Hl. exact Hl.
Qed.

(** Again, no [Static] side condition — VCCS's version needed two. *)
Lemma must_i_res_compat : forall (p q : proc), p ⊑ₘᵤₛₜᵢ q -> (ν p) ⊑ₘᵤₛₜᵢ (ν q).
Proof.
  intros p q Hpq t Hm.
  eapply res_bridge_rev; [ | reflexivity ].
  apply Hpq. eapply res_bridge_fwd; [ exact Hm | reflexivity ].
Qed.

(** ** Precongruence for [If]

    [lts_ifOne]/[lts_ifZero] (VACCS.v) only ever evaluate [Eval_Eq 0 E]
    (depth 0). At depth 0, [Eval_Eq]'s [None] branches (used to represent
    an equation between two still-unresolved bound variables at some
    positive depth) are unreachable — [0 <= i] holds unconditionally for
    any [i : nat] — so [Eval_Eq 0 E] is always [Some true] or [Some
    false] in practice. Consequently [If E Then p Else q] is *always*
    structurally congruent to either [p] or [q] ([cgr_if_true_step]/
    [cgr_if_false_step]), and precongruence for [If] reduces entirely to
    [must_i_cgr] plus transitivity — no acceptance-set argument needed. *)

Lemma Eval_Eq_0_not_none : forall E, Eval_Eq 0 E <> None.
Proof.
  intros [d1 d2]. destruct d1 as [t|i]; destruct d2 as [t'|i']; simpl.
  - destruct (decide (t=t')); discriminate.
  - destruct (decide (0<=i')); discriminate.
  - destruct (decide (0<=i)); discriminate.
  - destruct (decide (i=i')); [discriminate|].
    destruct (decide (0<=i)); [destruct (decide (0<=i')); discriminate|].
    discriminate.
Qed.

Lemma must_i_if_compat : forall E p p' q q', p ⊑ₘᵤₛₜᵢ p' -> q ⊑ₘᵤₛₜᵢ q' ->
  (If E Then p Else q) ⊑ₘᵤₛₜᵢ (If E Then p' Else q').
Proof.
  intros E p p' q q' Hpp' Hqq'.
  destruct (Eval_Eq 0 E) as [[|]|] eqn:Heval.
  - assert (H1 : (If E Then p Else q) ≡* p) by (constructor; eapply cgr_if_true_step; exact Heval).
    assert (H2 : (If E Then p' Else q') ≡* p') by (constructor; eapply cgr_if_true_step; exact Heval).
    apply must_i_cgr in H1 as (H1a & H1b).
    apply must_i_cgr in H2 as (H2a & H2b).
    intros t Ht. apply H2a. apply Hpp'. apply H1b. exact Ht.
  - assert (H1 : (If E Then p Else q) ≡* q) by (constructor; eapply cgr_if_false_step; exact Heval).
    assert (H2 : (If E Then p' Else q') ≡* q') by (constructor; eapply cgr_if_false_step; exact Heval).
    apply must_i_cgr in H1 as (H1a & H1b).
    apply must_i_cgr in H2 as (H2a & H2b).
    intros t Ht. apply H2a. apply Hqq'. apply H1b. exact Ht.
  - exfalso. eapply Eval_Eq_0_not_none. exact Heval.
Qed.

(** ** Toolkit for guarded-choice [+] precongruence

    Unlike [ν] (single argument, shifting), guarded choice has *two*
    arguments and no depth shift, but introduces a genuine branching
    subtlety: a weak transition of [g (gp+gq)] either (a) takes zero
    steps (still at the choice itself), or (b)/(c) commits to [gp]'s or
    [gq]'s own transition system after exactly one step (via
    [lts_choiceL]/[lts_choiceR]) — never both. [choice_wt_decomp']
    captures this trichotomy precisely (case (a) forces [s = []], via
    the [wt_nil] shape). *)

Lemma choice_wt_decomp' : forall gp gq s r, (g (gp + gq)) ⟹[s] r ->
  (s = [] /\ r = g (gp + gq)) \/ (g gp) ⟹[s] r \/ (g gq) ⟹[s] r.
Proof.
  intros gp gq s r Hw.
  remember (g (gp + gq)) as P eqn:HP.
  destruct Hw.
  - left. split; reflexivity.
  - subst p. inversion l; subst.
    + right. left. eapply wt_tau; [exact H3 | exact Hw].
    + right. right. eapply wt_tau; [exact H3 | exact Hw].
  - subst p. inversion l; subst.
    + right. left. eapply wt_act; [exact H3 | exact Hw].
    + right. right. eapply wt_act; [exact H3 | exact Hw].
Qed.

Lemma choice_ext_stable_iff : forall gp gq mu, (g (gp+gq)) ↛[mu] <-> (g gp) ↛[mu] /\ (g gq) ↛[mu].
Proof.
  intros gp gq mu. split.
  - intros Hst. split.
    + destruct (decide ((g gp) ↛[mu])) as [Hd|Hd]; [exact Hd|].
      exfalso. eapply lts_refuses_spec1 in Hd as (r & Hl).
      eapply lts_refuses_spec2 in Hst. apply Hst. exists r. eapply lts_choiceL. exact Hl.
    + destruct (decide ((g gq) ↛[mu])) as [Hd|Hd]; [exact Hd|].
      exfalso. eapply lts_refuses_spec1 in Hd as (r & Hl).
      eapply lts_refuses_spec2 in Hst. apply Hst. exists r. eapply lts_choiceR. exact Hl.
  - intros (Hst1 & Hst2). destruct (decide ((g(gp+gq)) ↛[mu])) as [Hd|Hd]; [exact Hd|].
    exfalso. eapply lts_refuses_spec1 in Hd as (r & Hl).
    inversion Hl; subst.
    + eapply lts_refuses_spec2 in Hst1. apply Hst1. exists r. exact H3.
    + eapply lts_refuses_spec2 in Hst2. apply Hst2. exists r. exact H3.
Qed.

Lemma choice_stable_iff : forall gp gq, (g (gp+gq)) ↛ <-> (g gp) ↛ /\ (g gq) ↛.
Proof.
  intros gp gq. split.
  - intros Hst. split.
    + destruct (decide ((g gp) ↛)) as [Hd|Hd]; [exact Hd|].
      exfalso. eapply lts_refuses_spec1 in Hd as (r & Hl).
      eapply lts_refuses_spec2 in Hst. apply Hst. exists r. eapply lts_choiceL. exact Hl.
    + destruct (decide ((g gq) ↛)) as [Hd|Hd]; [exact Hd|].
      exfalso. eapply lts_refuses_spec1 in Hd as (r & Hl).
      eapply lts_refuses_spec2 in Hst. apply Hst. exists r. eapply lts_choiceR. exact Hl.
  - intros (Hst1 & Hst2). destruct (decide ((g(gp+gq)) ↛)) as [Hd|Hd]; [exact Hd|].
    exfalso. eapply lts_refuses_spec1 in Hd as (r & Hl).
    inversion Hl; subst.
    + eapply lts_refuses_spec2 in Hst1. apply Hst1. exists r. exact H3.
    + eapply lts_refuses_spec2 in Hst2. apply Hst2. exists r. exact H3.
Qed.

Lemma choice_coR_union : forall gp gq mu1, mu1 ∈ coR (g (gp+gq)) <-> mu1 ∈ coR (g gp) \/ mu1 ∈ coR (g gq).
Proof.
  intros gp gq mu1. unfold coR, elem_of, subset_of in *. simpl.
  split.
  - intros (mu2 & Hnr & Hd & Hb).
    destruct (decide ((g gp) ↛[mu2])) as [Hd1|Hd1].
    + right. exists mu2. repeat split; try assumption.
      intro Hc. apply Hnr. apply choice_ext_stable_iff. split; assumption.
    + left. exists mu2. repeat split; try assumption.
  - intros [(mu2 & Hnr & Hd & Hb) | (mu2 & Hnr & Hd & Hb)].
    + exists mu2. repeat split; try assumption.
      intro Hc. apply Hnr. apply choice_ext_stable_iff in Hc. destruct Hc as (Hc1 & Hc2). exact Hc1.
    + exists mu2. repeat split; try assumption.
      intro Hc. apply Hnr. apply choice_ext_stable_iff in Hc. destruct Hc as (Hc1 & Hc2). exact Hc2.
Qed.

(** Lifting a single first step of [gp] (resp. [gq]) through [lts_choiceL]
    (resp. [lts_choiceR]), then continuing with an *already-given* weak
    transition of the successor state unchanged — deliberately not by
    induction on the whole [gp ⟹[s] r] derivation, since that fails
    exactly on its degenerate zero-step case (there is no way to reach
    the bare state [g gp] from [g (gp+gq)] with zero steps — they are
    different terms, and a commit through [gp]'s own first step is
    unavoidable). Composing these lemmas with a case split on whether
    [gp]/[gq]'s own weak transition needed zero steps or not is the
    intended usage pattern (see the session notes in the plan file for
    the full case analysis this feeds into). *)

Lemma choice_wt_liftL_step : forall gp gq q r s, (g gp) ⟶ q -> q ⟹[s] r -> (g (gp+gq)) ⟹[s] r.
Proof. intros gp gq q r s l w. eapply wt_tau; [eapply lts_choiceL; exact l | exact w]. Qed.

Lemma choice_wt_liftL_step_act : forall gp gq q r mu s, (g gp) ⟶[mu] q -> q ⟹[s] r -> (g (gp+gq)) ⟹[mu::s] r.
Proof. intros gp gq q r mu s l w. eapply wt_act; [eapply lts_choiceL; exact l | exact w]. Qed.

Lemma choice_wt_liftR_step : forall gp gq q r s, (g gq) ⟶ q -> q ⟹[s] r -> (g (gp+gq)) ⟹[s] r.
Proof. intros gp gq q r s l w. eapply wt_tau; [eapply lts_choiceR; exact l | exact w]. Qed.

Lemma choice_wt_liftR_step_act : forall gp gq q r mu s, (g gq) ⟶[mu] q -> q ⟹[s] r -> (g (gp+gq)) ⟹[mu::s] r.
Proof. intros gp gq q r mu s l w. eapply wt_act; [eapply lts_choiceR; exact l | exact w]. Qed.

(** ** Precongruence for the input prefix

    Unlike the guarded-choice case, the input's transition target
    [p^v]/[q^v] is *exactly* what the (necessarily [∀v]-quantified,
    Hennessy's classical "omega rule") hypothesis is about, for whichever
    concrete [v] the interaction actually uses — so the direct
    [must]-induction technique (as for the output/τ prefixes) applies
    immediately, no acceptance-set detour needed. Confirms the earlier
    correction to the plan: the single Coq binder in [c?p] doesn't make
    this rule non-quantified "for free" (it's still genuinely
    [∀v]-indexed in the hypothesis), but it *does* mean no separate
    substitution-respects-⊑ lemma is needed beyond this. *)

Lemma must_i_input_compat (c : ChannelData) (p q : proc) :
  (forall v, p^v ⊑ₘᵤₛₜᵢ q^v) -> g (c ? p) ⊑ₘᵤₛₜᵢ g (c ? q).
Proof.
  intros Hpq t Hm.
  remember (g (c ? p)) as P eqn:HP.
  induction Hm.
  - now apply m_now.
  - subst.
    apply m_step.
    + exact nh.
    + destruct ex as ((a2, b2) & Hstep).
      inversion Hstep; subst.
      * inversion l.
      * exists (g (c ? q), b2). eapply ParRight. exact l.
      * inversion l1; subst. exists (q^v, b2). eapply ParSync; [exact eq | eapply lts_input | exact l2].
    + intros p' Hp'. inversion Hp'.
    + intros t' Ht'. eapply H0; [exact Ht' | reflexivity].
    + intros p' t' μ1 μ2 Hdual Hp' Ht'. inversion Hp'; subst.
      apply (Hpq v). eapply com; [exact Hdual | eapply lts_input | exact Ht'].
Qed.

(** ** Toolkit for parallel [‖] precongruence

    The hardest operator (two-sided synchronisation), attempted last on
    purpose. Unlike guarded choice, taking a step in one component does
    *not* discard the other — [q ⟶ q1] gives [p‖q ⟶ p‖q1], with [p]
    still fully present — so the specific obstacle that stalled the
    guarded-choice case (a branch's contribution becoming permanently
    unreachable) should not arise here; the price is a genuinely two-
    sided stability/synchronisation condition instead.

    Tactic note: [p ⟶[mu] p'] for a *bare* label literal (e.g.
    [(c,v)!]) fails to elaborate in isolation — typeclass search can't
    pin down the [ExtAction (ExtAct TypeOfActions)] instance without an
    anchor. Binding [mu : ExtAct TypeOfActions] as an explicit top-level
    variable first (mirroring how [μ1]/[μ2] are always bound in [must]'s
    own [com] field) fixes it — this is *the* idiom to use for any
    labelled-transition statement on bare (non-[g]-wrapped) [proc]
    arguments in this file. *)

(** ** Output-merge equation (Hennessy's "c!v•P + c!v'•Q ≡ (c!v•P)⊕(c!v'•Q)")

    Unlike the other prefix-precongruences above, this is a genuine
    two-premise combinatorial argument, not a one-line unfolding. Key
    fact this relies on: VACCS's input transitions are inherently
    [∀v]-quantified ([lts_input : lts (c?P) ((c,v)?) (P^v)] holds for
    *every* [v], not just one chosen by the test) so a test's ability to
    synchronise on channel [c] never depends on the specific value being
    sent — only on whether the test offers *some* input on [c] at all.
    [lts_in_value_swap] makes this precise: any transition labelled
    [(c,v')?] can be "re-derived" at any other value [v] from the very
    same underlying test structure, by structural induction on the
    transition (the only real case is the [lts_input] base case; every
    other constructor is a transparent pass-through, including
    [lts_res_ext] since [VarC_action_add] only ever shifts the channel
    component, never the value — confirmed directly from its
    definition). *)

Lemma lts_in_value_swap : forall (p : proc) (mu : ExtAct TypeOfActions) (q : proc),
  lts p (ActExt mu) q ->
  forall (c : ChannelData) (v v' : ValueData), mu = ActIn (c, v) ->
  exists q', lts p (ActExt (ActIn (c, v'))) q'.
Proof.
  intros p mu q Ht.
  dependent induction Ht; intros c0 v0 v0' Heq; try discriminate Heq.
  - injection Heq as -> ->.
    exists (P ^ v0').
    apply lts_input.
  - destruct (IHHt mu JMeq_refl c0 v0 v0' Heq) as (q' & Hq').
    exists q'.
    eapply lts_ifOne; eauto.
  - destruct (IHHt mu JMeq_refl c0 v0 v0' Heq) as (q'0 & Hq').
    exists q'0.
    eapply lts_ifZero; eauto.
  - assert (Heq' : VarC_action_add 1 mu = ActIn (VarC_add 1 c0, v0)) by (subst mu; reflexivity).
    destruct (IHHt (VarC_action_add 1 mu) JMeq_refl (VarC_add 1 c0) v0 v0' Heq') as (p'' & Hp'').
    exists (ν p'').
    eapply lts_res_ext.
    replace (VarC_action_add 1 (ActIn (c0, v0'))) with (ActIn (VarC_add 1 c0, v0')) by reflexivity.
    exact Hp''.
  - destruct (IHHt mu JMeq_refl c0 v0 v0' Heq) as (p2' & Hp2').
    exists (p2' ‖ q).
    eapply lts_parL.
    exact Hp2'.
  - destruct (IHHt mu JMeq_refl c0 v0 v0' Heq) as (q2' & Hq2').
    exists (p ‖ q2').
    eapply lts_parR.
    exact Hq2'.
  - destruct (IHHt mu JMeq_refl c0 v0 v0' Heq) as (q' & Hq').
    exists q'.
    eapply lts_choiceL.
    exact Hq'.
  - destruct (IHHt mu JMeq_refl c0 v0 v0' Heq) as (q' & Hq').
    exists q'.
    eapply lts_choiceR.
    exact Hq'.
Qed.

(** Whenever the choice of two same-channel outputs passes a test, *each*
    branch alone (as a bare output-guard process, no alternative) also
    passes it — this is the semantic content that lets the choice be
    replaced by an internal (τ-guarded) commitment to either branch.
    The "wrong branch" case (the choice's own transition commits via the
    *other* output) is where [lts_in_value_swap] is needed: the
    synchronising test transition is only known at the other branch's
    value, and has to be re-derived at this branch's value instead. *)
Lemma must_i_input_branch_must : forall (c : ChannelData) (P Q t : proc),
  (g ((c ? P) + (c ? Q))) must_pass t ->
  (g (c ? P)) must_pass t /\ (g (c ? Q)) must_pass t.
Proof.
  intros c P Q t Hm.
  remember (g ((c ? P) + (c ? Q))) as R eqn:HR.
  induction Hm.
  - split; now apply m_now.
  - subst.
    split.
    + apply m_step.
      * exact nh.
      * destruct ex as ((a2,b2) & Hstep).
        inversion Hstep; subst.
        -- inversion l; subst; solve[inversion H6].
        -- exists (g (c ? P), b2). eapply ParRight. exact l.
        -- inversion l1; subst.
           ++ inversion H6; subst.
              exists (P ^ v, b2). eapply ParSync; [exact eq | exact H6 | exact l2].
           ++ inversion H6; subst.
              exists (P ^ v, b2). eapply ParSync; [exact eq | eapply lts_input | exact l2].
      * intros p' Hp'. inversion Hp'.
      * intros t' Ht'. apply (proj1 (H0 t' Ht' eq_refl)).
      * intros p' t' μ1 μ2 Hdual Hp' Ht'.
        inversion Hp'; subst.
        eapply com; [exact Hdual | eapply lts_choiceL; eapply lts_input | exact Ht'].
    + apply m_step.
      * exact nh.
      * destruct ex as ((a2,b2) & Hstep).
        inversion Hstep; subst.
        -- inversion l; subst; solve[inversion H6].
        -- exists (g (c ? Q), b2). eapply ParRight. exact l.
        -- inversion l1; subst.
           ++ inversion H6; subst.
              exists (Q ^ v, b2). eapply ParSync; [exact eq | eapply lts_input | exact l2].
           ++ inversion H6; subst.
              exists (Q ^ v, b2). eapply ParSync; [exact eq | exact H6 | exact l2].
      * intros p' Hp'. inversion Hp'.
      * intros t' Ht'. apply (proj2 (H0 t' Ht' eq_refl)).
      * intros p' t' μ1 μ2 Hdual Hp' Ht'.
        inversion Hp'; subst.
        eapply com; [exact Hdual | eapply lts_choiceR; eapply lts_input | exact Ht'].
Qed.

Lemma must_i_input_merge_l : forall (c : ChannelData) (P Q : proc),
  g ((c ? P) + (c ? Q)) ⊑ₘᵤₛₜᵢ g ((𝛕 • (g (c ? P))) + (𝛕 • (g (c ? Q)))).
Proof.
  intros c P Q t Hm.
  remember (g ((c ? P) + (c ? Q))) as LHS eqn:HLHS.
  induction Hm.
  - now apply m_now.
  - subst.
    assert (Hbranch : (g (c ? P)) must_pass t /\ (g (c ? Q)) must_pass t).
    { apply must_i_input_branch_must. apply m_step; assumption. }
    apply m_step.
    + exact nh.
    + destruct ex as ((a2,b2) & Hstep).
      inversion Hstep; subst.
      * inversion l; subst; solve[inversion H6].
      * exists (g ((𝛕 • (g (c ? P))) + (𝛕 • (g (c ? Q)))), b2).
        eapply ParRight. exact l.
      * inversion l1; subst.
        -- exists (g (c ? P), t). eapply ParLeft. eapply lts_choiceL. eapply lts_tau.
        -- exists (g (c ? P), t). eapply ParLeft. eapply lts_choiceL. eapply lts_tau.
    + intros p' Hp'.
      inversion Hp'; subst.
      * inversion H6; subst. exact (proj1 Hbranch).
      * inversion H6; subst. exact (proj2 Hbranch).
    + intros t' Ht'.
      eapply H0; [exact Ht' | reflexivity].
    + intros p' t' μ1 μ2 Hdual Hp' Ht'.
      inversion Hp'; subst.
      inversion H6.
      inversion H6.
Qed.

(** ** Reverse direction of the merge equations

    [must_i_int_choice_l]/[_r] already give, for free, that the internal-
    choice form's own [pt] field forces *both* branches to individually
    pass any test the whole thing passes. What remains is a "gluing"
    lemma: given both branches individually pass a test, does their
    external union also pass it? Proved by inducting on *one* of the two
    given facts while [revert]-ing the other first, so it reappears as
    an extra hypothesis in every generated induction hypothesis — this
    is what lets the [et] field recurse correctly on both facts at once
    without needing genuine mutual induction. For output specifically,
    no value-swap is needed here either (unlike the forward direction):
    each case of the [com] field dispatches on which literal branch's
    syntax the transition matches, and every case has a *direct* match
    to the corresponding given hypothesis's own [com] field. *)

Lemma must_i_input_join_branches : forall (c : ChannelData) (P Q t : proc),
  (g (c ? P)) must_pass t -> (g (c ? Q)) must_pass t -> (g ((c ? P) + (c ? Q))) must_pass t.
Proof.
  intros c P Q t Hm1 Hm2.
  remember (g (c ? P)) as X eqn:HX.
  revert Hm2.
  induction Hm1; intros Hm2.
  - now apply m_now.
  - subst.
    apply m_step.
    + exact nh.
    + destruct ex as ((a2,b2) & Hstep).
      inversion Hstep; subst.
      * inversion l.
      * exists (g ((c ? P) + (c ? Q)), b2). eapply ParRight. exact l.
      * inversion l1; subst.
        exists (P ^ v, b2). eapply ParSync; [exact eq | eapply lts_choiceL; eapply lts_input | exact l2].
    + intros p' Hp'. inversion Hp'; subst.
      inversion H6.
      inversion H6.
    + intros t' Ht'.
      eapply H0; [exact Ht' | reflexivity | ].
      inversion Hm2 as [Hout | nh2 ex2 pt2 et2 com2].
      * now apply m_now.
      * apply et2. exact Ht'.
    + intros p' t' μ1 μ2 Hdual Hp' Ht'.
      inversion Hp'; subst.
      * inversion H6; subst.
        eapply com; [exact Hdual | exact H6 | exact Ht'].
      * inversion H6; subst.
        inversion Hm2 as [Hout | nh2 ex2 pt2 et2 com2].
        -- exfalso. apply nh. exact Hout.
        -- eapply com2; [exact Hdual | exact H6 | exact Ht'].
Qed.

Lemma must_i_input_merge_r : forall (c : ChannelData) (P Q : proc),
  g ((𝛕 • (g (c ? P))) + (𝛕 • (g (c ? Q)))) ⊑ₘᵤₛₜᵢ g ((c ? P) + (c ? Q)).
Proof.
  intros c P Q t Hm.
  apply must_i_input_join_branches.
  - eapply must_i_int_choice_l. exact Hm.
  - eapply must_i_int_choice_r. exact Hm.
Qed.

Lemma par_stable_iff : forall (p q : proc), (p‖q) ↛ <->
  p ↛ /\ q ↛ /\ (forall (mu : ExtAct TypeOfActions) p' q', ~ (p ⟶[mu] p' /\ q ⟶[co mu] q')).
Proof.
  intros p q. split.
  - intros Hst. repeat split.
    + destruct (decide (p ↛)) as [Hd|Hd]; [exact Hd|].
      exfalso. eapply lts_refuses_spec1 in Hd as (r & Hl).
      eapply lts_refuses_spec2 in Hst. apply Hst. exists (r‖q). eapply lts_parL. exact Hl.
    + destruct (decide (q ↛)) as [Hd|Hd]; [exact Hd|].
      exfalso. eapply lts_refuses_spec1 in Hd as (r & Hl).
      eapply lts_refuses_spec2 in Hst. apply Hst. exists (p‖r). eapply lts_parR. exact Hl.
    + intros mu p' q' (Hl1 & Hl2).
      destruct mu as [[c v]|[c v]]; simpl in Hl2.
      * eapply lts_refuses_spec2 in Hst. apply Hst. exists (p'‖q'). eapply lts_comR; [exact Hl2 | exact Hl1].
      * eapply lts_refuses_spec2 in Hst. apply Hst. exists (p'‖q'). eapply lts_comL; [exact Hl1 | exact Hl2].
  - intros (Hp & Hq & Hc). destruct (decide ((p‖q) ↛)) as [Hd|Hd]; [exact Hd|].
    exfalso. eapply lts_refuses_spec1 in Hd as (r & Hl).
    inversion Hl; subst.
    + eapply (Hc (ActOut (c,v)) p2 q2). split; assumption.
    + eapply (Hc (ActIn (c,v)) q2 p2). split; assumption.
    + eapply lts_refuses_spec2 in Hp. apply Hp. exists p2. exact H3.
    + eapply lts_refuses_spec2 in Hq. apply Hq. exists q2. exact H3.
Qed.

(** Labelled refusal and [coR] compose for [‖] exactly as they did for
    guarded choice — synchronisation only ever produces [τ], never an
    external action, so it's invisible to [↛[mu]] for external [mu]; the
    difference between [‖] and [+] is entirely in [τ]-stability
    ([par_stable_iff] above vs [choice_stable_iff]), not in [coR]. *)

Lemma par_ext_stable_iff : forall (p q : proc) (mu : ExtAct TypeOfActions), (p‖q) ↛[mu] <-> p ↛[mu] /\ q ↛[mu].
Proof.
  intros p q mu. split.
  - intros Hst. split.
    + destruct (decide (p ↛[mu])) as [Hd|Hd]; [exact Hd|].
      exfalso. eapply lts_refuses_spec1 in Hd as (r & Hl).
      eapply lts_refuses_spec2 in Hst. apply Hst. exists (r‖q). eapply lts_parL. exact Hl.
    + destruct (decide (q ↛[mu])) as [Hd|Hd]; [exact Hd|].
      exfalso. eapply lts_refuses_spec1 in Hd as (r & Hl).
      eapply lts_refuses_spec2 in Hst. apply Hst. exists (p‖r). eapply lts_parR. exact Hl.
  - intros (Hp & Hq). destruct (decide ((p‖q) ↛[mu])) as [Hd|Hd]; [exact Hd|].
    exfalso. eapply lts_refuses_spec1 in Hd as (r & Hl).
    inversion Hl; subst.
    + eapply lts_refuses_spec2 in Hp. apply Hp. exists p2. exact H3.
    + eapply lts_refuses_spec2 in Hq. apply Hq. exists q2. exact H3.
Qed.

Lemma par_coR_union : forall p q mu1, mu1 ∈ coR (p‖q) <-> mu1 ∈ coR p \/ mu1 ∈ coR q.
Proof.
  intros p q mu1. unfold coR, elem_of, subset_of in *. simpl.
  split.
  - intros (mu2 & Hnr & Hd & Hb).
    destruct (decide (p ↛[mu2])) as [Hd1|Hd1].
    + right. exists mu2. repeat split; try assumption.
      intro Hc. apply Hnr. apply par_ext_stable_iff. split; assumption.
    + left. exists mu2. repeat split; try assumption.
  - intros [(mu2 & Hnr & Hd & Hb) | (mu2 & Hnr & Hd & Hb)].
    + exists mu2. repeat split; try assumption.
      intro Hc. apply Hnr. apply par_ext_stable_iff in Hc. destruct Hc as (Hc1 & Hc2). exact Hc1.
    + exists mu2. repeat split; try assumption.
      intro Hc. apply Hnr. apply par_ext_stable_iff in Hc. destruct Hc as (Hc1 & Hc2). exact Hc2.
Qed.

(** ** Trace-interleaving toolkit for [‖]'s weak transitions

    The combinatorial core needed for [‖]-precongruence's [cond2]: a
    weak transition of [q‖r] decomposes into a trace [s_q] for [q] and
    [s_r] for [r] (synchronised pairs cancelling out of the combined
    trace, exactly as in a shuffle-with-cancellation), *and* — this is
    the part that actually gets used — whatever process realises [q]'s
    own trace [s_q] can be substituted for [q] and recombined with [r]
    the same way, no matter how unrelated its internal derivation is to
    [q]'s. This substitution property is what lets an acceptance-set
    comparison of [p] against [q] (which only ever talks about full
    traces, never individual steps) be turned into a fact about [p‖r]
    versus [q‖r]. *)

Lemma par_wt_liftL : forall (r p p' : proc) (s : trace (ExtAct TypeOfActions)),
  p ⟹[s] p' -> (p ‖ r) ⟹[s] (p' ‖ r).
Proof.
  intros r p p' s Hwt.
  induction Hwt.
  - apply wt_nil.
  - eapply wt_tau; [eapply lts_parL; exact l | exact IHHwt].
  - eapply wt_act; [eapply lts_parL; exact l | exact IHHwt].
Qed.

Lemma par_wt_liftR : forall (p r r' : proc) (s : trace (ExtAct TypeOfActions)),
  r ⟹[s] r' -> (p ‖ r) ⟹[s] (p ‖ r').
Proof.
  intros p r r' s Hwt.
  induction Hwt.
  - apply wt_nil.
  - eapply wt_tau; [eapply lts_parR; exact l | exact IHHwt].
  - eapply wt_act; [eapply lts_parR; exact l | exact IHHwt].
Qed.

Lemma par_wt_transfer : forall (s : trace (ExtAct TypeOfActions)) (qr t2 : proc),
  qr ⟹[s] t2 ->
  forall q r, qr = q ‖ r ->
  exists q'' r'' s_q s_r,
    t2 = q'' ‖ r'' /\ q ⟹[s_q] q'' /\ r ⟹[s_r] r'' /\
    (forall p p'', p ⟹[s_q] p'' -> (p ‖ r) ⟹[s] (p'' ‖ r'')).
Proof.
  intros s qr t2 Hwt.
  induction Hwt as [ x | s0 x y z l Hwt IH | mu0 s0 x y z l Hwt IH ]; intros q r Heq.
  - subst. exists q, r, [], [].
    repeat split; eauto with mdb.
    intros p p'' Hp. eapply par_wt_liftL. exact Hp.
  - subst. inversion l; subst.
    destruct (IH p2 q2 eq_refl) as (q'' & r'' & s_q & s_r & Ht2 & Hq'' & Hr'' & Hsub).
    exists q'', r'', (ActOut (c,v) :: s_q), (ActIn (c,v) :: s_r).
    repeat split.
    exact Ht2.
    eapply wt_act; [exact H1 | exact Hq''].
    eapply wt_act; [exact H2 | exact Hr''].
    intros p pf Hp.
    eapply wt_pop in Hp as (mid & Hp1 & Hp2).
    eapply wt_decomp_one in Hp1 as (p1 & p2b & Hpp1 & Hpp2 & Hpp3).
    eapply wt_push_nil_left; [eapply par_wt_liftL; exact Hpp1 | ].
    eapply wt_push_nil_left; [eapply lts_to_wt_tau; eapply lts_comL; [exact Hpp2 | exact H2] | ].
    eapply wt_push_nil_left; [eapply par_wt_liftL; exact Hpp3 | ].
    eapply Hsub. exact Hp2.
    destruct (IH q2 p2 eq_refl) as (q'' & r'' & s_q & s_r & Ht2 & Hq'' & Hr'' & Hsub).
    exists q'', r'', (ActIn (c,v) :: s_q), (ActOut (c,v) :: s_r).
    repeat split.
    exact Ht2.
    eapply wt_act; [exact H2 | exact Hq''].
    eapply wt_act; [exact H1 | exact Hr''].
    intros p pf Hp.
    eapply wt_pop in Hp as (mid & Hp1 & Hp2).
    eapply wt_decomp_one in Hp1 as (p1 & p2b & Hpp1 & Hpp2 & Hpp3).
    eapply wt_push_nil_left; [eapply par_wt_liftL; exact Hpp1 | ].
    eapply wt_push_nil_left; [eapply lts_to_wt_tau; eapply lts_comR; [exact H1 | exact Hpp2] | ].
    eapply wt_push_nil_left; [eapply par_wt_liftL; exact Hpp3 | ].
    eapply Hsub. exact Hp2.
    destruct (IH p2 r eq_refl) as (q'' & r'' & s_q & s_r & Ht2 & Hq'' & Hr'' & Hsub).
    exists q'', r'', s_q, s_r.
    repeat split.
    exact Ht2.
    eapply wt_tau; [exact H3 | exact Hq''].
    exact Hr''.
    exact Hsub.
    destruct (IH q q2 eq_refl) as (q'' & r'' & s_q & s_r & Ht2 & Hq'' & Hr'' & Hsub).
    exists q'', r'', s_q, s_r.
    repeat split.
    exact Ht2.
    exact Hq''.
    eapply wt_tau; [exact H3 | exact Hr''].
    intros p pf Hp.
    eapply wt_push_nil_left; [eapply par_wt_liftR; eapply lts_to_wt_tau; exact H3 | ].
    eapply Hsub. exact Hp.
  - inversion l; subst.
    discriminate H.
    discriminate H.
    discriminate H1.
    discriminate H1.
    discriminate H0.
    injection H0 as -> ->.
    destruct (IH p2 r eq_refl) as (q'' & r'' & s_q & s_r & Ht2 & Hq'' & Hr'' & Hsub).
    exists q'', r'', (mu0 :: s_q), s_r.
    repeat split.
    exact Ht2.
    eapply wt_act; [exact H | exact Hq''].
    exact Hr''.
    intros p pf Hp.
    eapply wt_pop in Hp as (mid & Hp1 & Hp2).
    eapply wt_decomp_one in Hp1 as (p1 & p2b & Hpp1 & Hpp2 & Hpp3).
    eapply wt_push_nil_left; [eapply par_wt_liftL; exact Hpp1 | ].
    eapply wt_push_left.
    + eapply lts_to_wt. eapply lts_parL. exact Hpp2.
    + eapply wt_push_nil_left; [eapply par_wt_liftL; exact Hpp3 | ].
      eapply Hsub. exact Hp2.
    + injection H0 as -> ->.
      destruct (IH q q2 eq_refl) as (q'' & r'' & s_q & s_r & Ht2 & Hq'' & Hr'' & Hsub).
      exists q'', r'', s_q, (mu0 :: s_r).
      repeat split.
      exact Ht2.
      exact Hq''.
      eapply wt_act; [exact H | exact Hr''].
      intros p pf Hp.
      eapply wt_push_left.
      * eapply lts_to_wt. eapply lts_parR. exact H.
      * eapply Hsub. exact Hp.
    + discriminate H0.
    + discriminate H0.
Qed.

(** ** Bridging the acceptance-set abstraction through [‖]

    [cond2] only ever gives coR inclusion at the *abstracted* level
    (dropping values, keeping channel+polarity — [Φᴠᴀᴄᴄꜱ]/[𝝳ᴠᴀᴄᴄꜱ], same
    maps as for [ν]). To show a reconstructed pair is itself stable, a
    raw "no synchronisation possible" fact has to be derived from that
    abstracted bound. This is sound for the same reason the output-merge
    equation (checkpoint 3) was sound: [lts_in_value_swap] shows a
    process's ability to synchronise on a channel never depends on the
    specific value, so losing the value when abstracting loses no real
    distinguishing power for the "can these synchronise at all" question
    — only for what happens in the continuation afterwards, which is
    handled separately (recursively) by the acceptance-set comparison
    itself, not by [coR]. *)

Lemma lts_in_refuse_channel_indep : forall (r : proc) (c : ChannelData) (v v' : ValueData),
  r ↛[ActIn (c,v)] -> r ↛[ActIn (c,v')].
Proof.
  intros r c v v' Hr.
  destruct (decide (r ↛[ActIn (c,v')])) as [?|Hnr]; [assumption|].
  exfalso.
  eapply lts_refuses_spec1 in Hnr as (r' & Hl).
  destruct (lts_in_value_swap r (ActIn (c,v')) r' Hl c v' v eq_refl) as (r'' & Hl').
  eapply lts_refuses_spec2 in Hr. apply Hr. exists r''. exact Hl'.
Qed.

(** The [coR]-level half of the [≼ₐₛ] route stops here for VACCS.
    [par_nosync_transfer] (the VCCS bridging lemma turning an *abstracted*
    [coR] inclusion into a raw synchronisation-freedom fact) does not port:
    VCCS's [blocking] is unconditionally true, so its [coR p] is "the
    co-actions of everything [p] can do", whereas VACCS's [non_blocking] is
    [is_output], so [coR p] holds *inputs only*.  Since VACCS has no
    [_without_toFW] bridge either, none of this could be cashed in anyway —
    [‖]-precongruence is obtained below by a different and cheaper route. *)

(** ** [‖]-precongruence, via the erasure bridge

    The [≼ₐₛ] toolkit above cannot be cashed in (no
    [_without_toFW] bridge for VACCS), so [‖]-precongruence is obtained
    another way, and the result is *stronger* than VCCS's: no [Static]
    side conditions at all.

    The observation is that [must]'s pair LTS does not care how the
    system [p | r | t] is bracketed — only the *outcome* predicate does,
    since [good (r ‖ t)] holds as soon as [good r] does.  Erase the
    server's [①]s ([VACCS_Erasure.v]) and that obstruction disappears:
    [noone r] can never become [good], so [r] may be moved from the
    server side to the client side and back.  Then [p ⊑ₘᵤₛₜᵢ q] is applied
    at the single test [noone r ‖ t]. *)

Lemma par_bridge_fwd : forall (P t : proc), P must_pass t ->
  forall p r, P = p ‖ (noone r) -> p must_pass ((noone r) ‖ t).
Proof.
  intros P t Hm. induction Hm as [ P t Ho | P t Ho Hex Hpt IHpt Het IHet Hcom IHcom ];
    intros p r Heq; subst.
  - apply m_now. apply good_par. right. exact Ho.
  - apply m_step.
    + intro Hg. inversion Hg; subst. destruct H0 as [H|H].
      * eapply noone_not_good; exact H.
      * apply Ho; exact H.
    + destruct Hex as ((x1,x2) & Hs). inversion Hs; subst.
      * inversion l; subst.
        -- exists (p2 ▷ (q2 ‖ x2)).
           eapply ParSync; [ apply dual_out_in | eassumption | apply lts_parL; eassumption ].
        -- exists (q2 ▷ (p2 ‖ x2)).
           eapply ParSync; [ apply dual_in_out | eassumption | apply lts_parL; eassumption ].
        -- exists (p2 ▷ (noone r ‖ x2)). eapply ParLeft. eassumption.
        -- exists (p ▷ (q2 ‖ x2)). eapply ParRight. apply lts_parL. eassumption.
      * exists (p ▷ (noone r ‖ x2)). eapply ParRight. apply lts_parR. eassumption.
      * inversion l1; subst.
        -- exists (p2 ▷ (noone r ‖ x2)).
           eapply ParSync; [ exact eq | eassumption | apply lts_parR; eassumption ].
        -- exists (p ▷ (q2 ‖ x2)). eapply ParRight.
           destruct (dual_shape _ _ eq) as [(a & Ha1 & Ha2)|(a & Ha1 & Ha2)]; subst;
             destruct a as (c0,v0).
           ++ eapply lts_comL; eassumption.
           ++ eapply lts_comR; eassumption.
    + intros p' Hp'. eapply (IHpt (p' ‖ noone r)); [ apply lts_parL; exact Hp' | reflexivity ].
    + intros u Hu. inversion Hu; subst.
      * destruct (lts_noone_inv _ _ _ H1) as (r1 & Hr1 & Hlr1). subst.
        eapply (IHcom (p ‖ noone r1) _ (ActOut (c,v)) (ActIn (c,v)));
          [ apply dual_out_in | apply lts_parR; apply lts_noone; exact Hlr1
          | eassumption | reflexivity ].
      * destruct (lts_noone_inv _ _ _ H2) as (r1 & Hr1 & Hlr1). subst.
        eapply (IHcom (p ‖ noone r1) _ (ActIn (c,v)) (ActOut (c,v)));
          [ apply dual_in_out | apply lts_parR; apply lts_noone; exact Hlr1
          | eassumption | reflexivity ].
      * destruct (lts_noone_inv _ _ _ H3) as (r1 & Hr1 & Hlr1). subst.
        eapply (IHpt (p ‖ noone r1)); [ apply lts_parR; apply lts_noone; exact Hlr1 | reflexivity ].
      * eapply IHet; [ eassumption | reflexivity ].
    + intros p' u mu1 mu2 Hd Hp' Hu. inversion Hu; subst.
      * destruct (lts_noone_inv _ _ _ H3) as (r1 & Hr1 & Hlr1). subst.
        destruct (dual_shape _ _ Hd) as [(a & Ha1 & Ha2)|(a & Ha1 & Ha2)]; subst.
        -- destruct a as (c0,v0).
           eapply (IHpt (p' ‖ noone r1));
             [ eapply lts_comL; [ exact Hp' | apply lts_noone; exact Hlr1 ] | reflexivity ].
        -- destruct a as (c0,v0).
           eapply (IHpt (p' ‖ noone r1));
             [ eapply lts_comR; [ apply lts_noone; exact Hlr1 | exact Hp' ] | reflexivity ].
      * eapply (IHcom (p' ‖ noone r) _ mu1 mu2);
          [ exact Hd | apply lts_parL; exact Hp' | eassumption | reflexivity ].
Qed.

Lemma par_bridge_rev : forall (p T : proc), p must_pass T ->
  forall r t, T = (noone r) ‖ t -> (p ‖ (noone r)) must_pass t.
Proof.
  intros p T Hm. induction Hm as [ p T Ho | p T Ho Hex Hpt IHpt Het IHet Hcom IHcom ];
    intros r t Heq; subst.
  - apply m_now. inversion Ho; subst. destruct H0 as [H|H].
    + exfalso. eapply noone_not_good; exact H.
    + exact H.
  - apply m_step.
    + intro Hg. apply Ho. apply good_par. right. exact Hg.
    + destruct Hex as ((x1,x2) & Hs). inversion Hs; subst.
      * exists ((x1 ‖ noone r) ▷ t). eapply ParLeft. apply lts_parL. eassumption.
      * inversion l; subst.
        -- exists ((x1 ‖ p2) ▷ q2).
           eapply ParSync; [ apply dual_out_in | apply lts_parR; eassumption | eassumption ].
        -- exists ((x1 ‖ q2) ▷ p2).
           eapply ParSync; [ apply dual_in_out | apply lts_parR; eassumption | eassumption ].
        -- exists ((x1 ‖ p2) ▷ t). eapply ParLeft. apply lts_parR. eassumption.
        -- exists ((x1 ‖ noone r) ▷ q2). eapply ParRight. eassumption.
      * inversion l2; subst.
        -- exists ((x1 ‖ p2) ▷ t). eapply ParLeft.
           destruct (dual_shape _ _ eq) as [(a & Ha1 & Ha2)|(a & Ha1 & Ha2)]; subst;
             destruct a as (c0,v0).
           ++ eapply lts_comL; eassumption.
           ++ eapply lts_comR; eassumption.
        -- exists ((x1 ‖ noone r) ▷ q2).
           eapply ParSync; [ exact eq | apply lts_parL; eassumption | eassumption ].
    + intros y Hy. inversion Hy; subst.
      * destruct (lts_noone_inv _ _ _ H2) as (r1 & Hr1 & Hlr1). subst.
        eapply (IHcom p2 (noone r1 ‖ t) (ActOut (c,v)) (ActIn (c,v)));
          [ apply dual_out_in | eassumption | apply lts_parL; apply lts_noone; exact Hlr1
          | reflexivity ].
      * destruct (lts_noone_inv _ _ _ H1) as (r1 & Hr1 & Hlr1). subst.
        eapply (IHcom q2 (noone r1 ‖ t) (ActIn (c,v)) (ActOut (c,v)));
          [ apply dual_in_out | eassumption | apply lts_parL; apply lts_noone; exact Hlr1
          | reflexivity ].
      * eapply (IHpt p2); [ exact H3 | reflexivity ].
      * destruct (lts_noone_inv _ _ _ H3) as (r1 & Hr1 & Hlr1). subst.
        eapply (IHet (noone r1 ‖ t)); [ apply lts_parL; apply lts_noone; exact Hlr1 | reflexivity ].
    + intros t' Ht'. eapply (IHet (noone r ‖ t')); [ apply lts_parR; exact Ht' | reflexivity ].
    + intros y t' mu1 mu2 Hd Hy Ht'. inversion Hy; subst.
      * eapply (IHcom p2 (noone r ‖ t') mu1 mu2);
          [ exact Hd | eassumption | apply lts_parR; exact Ht' | reflexivity ].
      * destruct (lts_noone_inv _ _ _ H3) as (r1 & Hr1 & Hlr1). subst.
        eapply (IHet (noone r1 ‖ t')); [ | reflexivity ].
        destruct (dual_shape _ _ Hd) as [(a & Ha1 & Ha2)|(a & Ha1 & Ha2)]; subst;
          destruct a as (c0,v0).
        -- eapply lts_comL; [ apply lts_noone; exact Hlr1 | exact Ht' ].
        -- eapply lts_comR; [ exact Ht' | apply lts_noone; exact Hlr1 ].
Qed.

(** A pending message may sit on EITHER side of the barrier: moving it
    from the server to the client changes nothing.  This is the [noone]
    bridge at [r := c ! v • 𝟘], which needs no erasure at all — an atomic
    message contains no [①], so [noone] is the identity on it.

    It is the message-layer counterpart of the two bridges that made [‖]
    and [ν] precongruence cheap: a pending output is not part of a
    process's behaviour, it is part of the *configuration*, and the
    configuration may be split anywhere. *)

Lemma must_msg_swap : forall (c : ChannelData) (v : ValueData) (p e : proc),
  ((p ‖ (c ! v • 𝟘)) must_pass e) <-> (p must_pass ((c ! v • 𝟘) ‖ e)).
Proof.
  intros c v p e.
  assert (Hn : noone ((c ! v • 𝟘) : proc) = ((c ! v • 𝟘) : proc)) by reflexivity.
  split; intro Hm.
  - assert (Hx : p must_pass (noone ((c ! v • 𝟘) : proc) ‖ e)).
    { eapply (par_bridge_fwd _ e Hm p ((c ! v • 𝟘) : proc)).
      rewrite Hn. reflexivity. }
    rewrite Hn in Hx. exact Hx.
  - assert (Hx : (p ‖ noone ((c ! v • 𝟘) : proc)) must_pass e).
    { eapply (par_bridge_rev p _ Hm ((c ! v • 𝟘) : proc) e).
      rewrite Hn. reflexivity. }
    rewrite Hn in Hx. exact Hx.
Qed.

(** The precongruence itself.  Note the absence of any [Static] side
    condition — the argument never inspects the shape of [p], [q] or [r]. *)

Lemma must_i_par_compat : forall (p q r : proc), p ⊑ₘᵤₛₜᵢ q -> (p ‖ r) ⊑ₘᵤₛₜᵢ (q ‖ r).
Proof.
  intros p q r Hpq t Hm.
  apply (must_noone_rev (q ‖ r)).
  simpl. eapply par_bridge_rev; [ | reflexivity ].
  apply must_noone. apply Hpq.
  apply (must_noone_rev p).
  eapply par_bridge_fwd; [ | reflexivity ].
  apply (must_noone (p ‖ r)) in Hm. exact Hm.
Qed.

Lemma must_i_par_compat_r : forall (p q q' : proc), q ⊑ₘᵤₛₜᵢ q' -> (p ‖ q) ⊑ₘᵤₛₜᵢ (p ‖ q').
Proof.
  intros p q q' Hqq'.
  assert (Hcomm1 : (p ‖ q) ≡* (q ‖ p)) by (constructor; constructor).
  assert (Hcomm2 : (q' ‖ p) ≡* (p ‖ q')) by (constructor; constructor).
  apply must_i_cgr in Hcomm1 as (Hd1a & Hd1b).
  apply must_i_cgr in Hcomm2 as (Hd2a & Hd2b).
  intros t Hm. apply Hd2b. apply (must_i_par_compat q q' p Hqq'). apply Hd1b. exact Hm.
Qed.

Lemma must_i_par_compat2 : forall (p p' q q' : proc),
  p ⊑ₘᵤₛₜᵢ p' -> q ⊑ₘᵤₛₜᵢ q' -> (p ‖ q) ⊑ₘᵤₛₜᵢ (p' ‖ q').
Proof.
  intros p p' q q' Hpp' Hqq' t Hm.
  apply (must_i_par_compat_r p' q q' Hqq').
  apply (must_i_par_compat p p' q Hpp'). exact Hm.
Qed.

(** ** [①] is a [𝟘] on the server side

    [must]'s outcome field inspects only the *test*, and [①] has no [lts]
    rule at all, so a server's [①] is indistinguishable from [𝟘].  A
    one-line instance of [VACCS_Erasure.v]'s [must_noone]. *)

Lemma must_i_success_nil : (g ①) ≂ₘᵤₛₜᵢ (g 𝟘).
Proof.
  split.
  - intros t Hm. exact (must_noone_rev (g ①) t Hm).
  - intros t Hm. exact (must_noone (g ①) t Hm).
Qed.

(** ** Guard-preserving congruence inside a sum

    This is what replaces VCCS's [ax_choice_stable] — which is **unsound**
    for VACCS: see [VACCS_ChoiceProbes.v] for the counterexample, whose
    engine is the copycat [a ? (a!x•𝟘) ≂ₘᵤₛₜᵢ 𝟘].  A copycat is invisible
    standalone, but guarded choice *commits*, so putting one beside another
    summand lets the sum swallow a message, discard the alternative, and
    deadlock.  Replacing a stable summand by another stable one is
    therefore not sound here, however stable both are.

    What survives is congruence that leaves the *guard* alone, so the sum's
    ready set is untouched and no new commitment becomes available.  For a
    [𝛕] summand that is [must_i_choice_tau_compat] above; for an input
    summand it is the lemma below.  Between them they cover every guard
    shape VACCS has ([①] and [𝟘] carry no continuation, and there is no
    output guard at all).

    The proof is the input-prefix argument ([must_i_input_compat]) carried
    through a context: the two sums have literally the same transitions
    except at the rewritten guard, where the hypothesis is applied at
    exactly the value the synchronisation fired on. *)

Lemma must_i_choice_input_compat : forall (c : ChannelData) (P Q : proc) (G : gproc),
  (forall v, (P ^ v) ⊑ₘᵤₛₜᵢ (Q ^ v)) ->
  g ((c ? P) + G) ⊑ₘᵤₛₜᵢ g ((c ? Q) + G).
Proof.
  intros c P Q G HPQ t Hm.
  remember (g ((c ? P) + G)) as S eqn:HS.
  revert HS. revert G. induction Hm as [ S t Ho | S t Ho Hex Hpt IHpt Het IHet Hcom IHcom ];
    intros G HS; subst.
  - now apply m_now.
  - apply m_step.
    + exact Ho.
    + destruct Hex as ((x1,x2) & Hs). inversion Hs; subst.
      * inversion l; subst.
        -- inversion H3.
        -- exists (x1 ▷ x2). eapply ParLeft. apply lts_choiceR. exact H3.
      * exists (g ((c ? Q) + G) ▷ x2). eapply ParRight. exact l.
      * inversion l1; subst.
        -- inversion H3; subst.
           exists ((Q ^ v) ▷ x2). eapply ParSync;
             [ exact eq | apply lts_choiceL; apply lts_input | exact l2 ].
        -- exists (x1 ▷ x2). eapply ParSync;
             [ exact eq | apply lts_choiceR; exact H3 | exact l2 ].
    + intros x Hx. inversion Hx; subst.
      * inversion H3.
      * eapply Hpt. apply lts_choiceR. exact H3.
    + intros t' Ht'. eapply IHet; [ exact Ht' | reflexivity ].
    + intros x t' mu1 mu2 Hd Hx Ht'. inversion Hx; subst.
      * inversion H3; subst.
        apply HPQ. eapply Hcom; [ exact Hd | apply lts_choiceL; apply lts_input | exact Ht' ].
      * eapply Hcom; [ exact Hd | apply lts_choiceR; exact H3 | exact Ht' ].
Qed.

(** ** Prefix distributes over guarded choice: [a.P + a.Q ≂ a.(P ⊕ Q)]

    The law that makes a guarded-sum normal form *canonical* — with a
    *unique* continuation per action — which is what
    [CompletenessAx.v]'s completeness argument needs. Without it, two
    same-action summands ([c?P + c?Q]) leave the correspondence between
    the two sides' continuations underdetermined: [⊑ₘᵤₛₜᵢ] only ever
    supplies an *existential* "some matching configuration exists",
    never a fixed pairing, so no [ax_pre] derivation can be built
    branch-by-branch. Collapsing same-action summands into one removes
    the choice entirely. This is exactly the role the analogous law
    plays in Hennessy's acceptance-tree normal forms, where a canonical
    form is [⊕ᵢ Σ_{a ∈ Aᵢ} a.p(a)] with [p(a)] a *function of the
    action alone*.

    Both directions hold, and both bottom out on the same observation:
    [c?P + c?Q] forces a test to survive *both* continuations (via its
    two possible synchronisation targets, [must]'s [com] field), while
    [c?(P ⊕ Q)] forces the same thing via [must]'s [pt] field after the
    internal choice's own [𝛕] — the very same requirement, reached
    through a different field. [must_i_tau_choice_join] below is the
    reusable half of that observation, and is the mirror image of
    [must_i_int_choice_l]/[_r] (which project *out* of an internal
    choice; this one builds *into* one). *)

Lemma must_i_tau_choice_join : forall (X Y t : proc),
  X must_pass t -> Y must_pass t -> g ((𝛕 • X) + (𝛕 • Y)) must_pass t.
Proof.
  intros X Y t Hm1.
  revert Y.
  induction Hm1 as [p t Ho | p t nh ex pt et IH com]; intros Y Hm2.
  - now apply m_now.
  - apply m_step.
    + exact nh.
    + exists (p, t). eapply ParLeft. apply lts_choiceL. apply lts_tau.
    + intros p' Hp'. inversion Hp'; subst.
      * inversion H4; subst.
        apply m_step; [exact nh | exact ex | exact pt | exact IH | exact com0].
      * inversion H4; subst. exact Hm2.
    + intros t' Ht'.
      apply com; [exact Ht' |].
      inversion Hm2; subst.
      * exfalso. apply nh. assumption.
      * eapply et0. exact Ht'.
    + intros p' t' μ1 μ2 Hdual Hp' Ht'.
      inversion Hp'; subst; inversion H4.
Qed.

Lemma must_i_input_distrib_l : forall (c : ChannelData) (P Q : proc),
  g ((c ? P) + (c ? Q)) ⊑ₘᵤₛₜᵢ g (c ? (g ((𝛕 • P) + (𝛕 • Q)))).
Proof.
  intros c P Q t Hm.
  remember (g ((c ? P) + (c ? Q))) as p0 eqn:Heq.
  revert c P Q Heq.
  induction Hm; intros c0 P0 Q0 Heq.
  - now apply m_now.
  - subst p.
    apply m_step.
    + exact nh.
    + destruct ex as ((a2,b2) & Hstep). inversion Hstep; subst.
      * exfalso. inversion l; subst; inversion H6.
      * exists (g (c0 ? (g ((𝛕 • P0) + (𝛕 • Q0)))), b2). eapply ParRight. exact l.
      * inversion l1; subst; inversion H6; subst;
          (eexists; eapply ParSync; [exact eq | apply lts_input | exact l2]).
    + intros p' Hp'. inversion Hp'.
    + intros t' Ht'. eapply H0; [exact Ht' | reflexivity].
    + intros p' t' μ1 μ2 Hdual Hp' Ht'.
      inversion Hp'; subst.
      apply must_i_tau_choice_join.
      * eapply com; [exact Hdual | apply lts_choiceL; apply lts_input | exact Ht'].
      * eapply com; [exact Hdual | apply lts_choiceR; apply lts_input | exact Ht'].
Qed.

Lemma must_i_input_distrib_r : forall (c : ChannelData) (P Q : proc),
  g (c ? (g ((𝛕 • P) + (𝛕 • Q)))) ⊑ₘᵤₛₜᵢ g ((c ? P) + (c ? Q)).
Proof.
  intros c P Q t Hm.
  apply must_i_input_join_branches.
  - apply (must_i_input_compat c (g ((𝛕 • P) + (𝛕 • Q))) P).
    + intro v. simpl. apply must_i_int_choice_l.
    + exact Hm.
  - apply (must_i_input_compat c (g ((𝛕 • P) + (𝛕 • Q))) Q).
    + intro v. simpl. apply must_i_int_choice_r.
    + exact Hm.
Qed.

(** The same merge, but **in an arbitrary context** — two same-channel
    input summands collapse into one over the internal choice of their
    continuations, whatever else the sum contains.

    This has to be proved directly.  VCCS derives its context versions
    from [ax_choice_stable], which is unsound here
    ([VACCS_ChoiceProbes.v]) — and rightly so, since that rule may change
    a summand's guard.  This rewrite does not: the sum's guard *set* is
    the same on both sides, which is exactly why it escapes the
    counterexample.

    Only one field has content, [com] at the merged guard: the right-hand
    side's continuation is [P^v ⊕ Q^v], so *both* branches must survive,
    and the left-hand side supplies them from its two summands, assembled
    by [must_i_int_glb].  Everything else transfers through
    [lts_choiceR]. *)

Lemma must_i_input_distrib_ctx_l :
  forall (c : ChannelData) (P Q : proc) (R : gproc) (t : proc),
  (g ((c ? P + (c ? Q)) + R)) must_pass t ->
  (g ((c ? (𝛕 • P + (𝛕 • Q))) + R)) must_pass t.
Proof.
  intros c P Q R t Hm. remember (g ((c ? P + (c ? Q)) + R)) as p0 eqn:Heq.
  induction Hm; subst.
  - apply m_now. assumption.
  - apply m_step.
    + assumption.
    + destruct ex as (u & Hu). inversion Hu; subst; unfold lts_step in *; simpl in *.
      * inversion l; subst.
        -- inversion H6; subst; inversion H7.
        -- eexists. eapply ParLeft. apply lts_choiceR. eassumption.
      * eexists. eapply ParRight. eassumption.
      * inversion l1; subst.
        -- inversion H6; subst;
             (inversion H7; subst; eexists; eapply ParSync;
               [ exact eq | apply lts_choiceL; apply lts_input | exact l2 ]).
        -- eexists. eapply ParSync; [ exact eq | apply lts_choiceR; eassumption | exact l2 ].
    + intros p' Hp'. inversion Hp'; subst.
      * inversion H6.
      * apply pt. apply lts_choiceR. assumption.
    + intros t' Ht'. eapply H0; [ exact Ht' | reflexivity ].
    + intros p' t' mu1 mu2 Hd Hl1 Hl2. inversion Hl1; subst.
      * inversion H6; subst. simpl. apply must_i_int_glb.
        -- eapply com;
             [ exact Hd | apply lts_choiceL; apply lts_choiceL; apply lts_input | exact Hl2 ].
        -- eapply com;
             [ exact Hd | apply lts_choiceL; apply lts_choiceR; apply lts_input | exact Hl2 ].
      * eapply com; [ exact Hd | apply lts_choiceR; eassumption | exact Hl2 ].
Qed.

(** ** A server's own internal step only decreases

    [p ⟶ p'] gives [p ⊑ₘᵤₛₜᵢ p'] outright — [must]'s [pt] field hands the
    obligation straight to every τ-successor.  Free from the generic
    [must_preserved_by_lts_tau_srv], and it is the semantic content of
    the [ax_tau_step] rule. *)

Lemma must_i_tau_below : forall p p', lts p τ p' -> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ p'.
Proof.
  intros p p' Hl t Hm. eapply must_preserved_by_lts_tau_srv; eassumption.
Qed.

(** The **reverse** direction, also in context — so the merge is a
    semantic *equivalence*, not just an inequation.

    That is what lets canonicalisation ([VACCS_Canonical.canonicalize])
    be inserted into a completeness chain: the rule
    [ax_input_distrib_l] only goes one way, but if the semantics goes
    both ways then a hypothesis [g M ⊑ₘᵤₛₜᵢ g N] transfers to the
    canonical form, which is exactly what the chain needs.

    Canonicity matters to [BadK] specifically: [bk_kill] demands **every**
    continuation on the killed channel be bad, whereas [must] only needs
    *one* of two same-channel guards to fail.  With at most one guard per
    channel the two coincide. *)

Lemma must_i_input_distrib_ctx_r :
  forall (c : ChannelData) (P Q : proc) (R : gproc) (t : proc),
  (g ((c ? (g ((𝛕 • P) + (𝛕 • Q)))) + R)) must_pass t ->
  (g (((c ? P) + (c ? Q)) + R)) must_pass t.
Proof.
  intros c P Q R t Hm. remember (g ((c ? (g ((𝛕 • P) + (𝛕 • Q)))) + R)) as p0 eqn:Heq.
  induction Hm; subst.
  - apply m_now. assumption.
  - apply m_step.
    + assumption.
    + destruct ex as (u & Hu). inversion Hu; subst; unfold lts_step in *; simpl in *.
      * inversion l; subst.
        -- inversion H6.
        -- eexists. eapply ParLeft. apply lts_choiceR. eassumption.
      * eexists. eapply ParRight. eassumption.
      * inversion l1; subst.
        -- inversion H6; subst. eexists. eapply ParSync;
             [ exact eq | apply lts_choiceL; apply lts_choiceL; apply lts_input | exact l2 ].
        -- eexists. eapply ParSync; [ exact eq | apply lts_choiceR; eassumption | exact l2 ].
    + intros p' Hp'. inversion Hp'; subst.
      * inversion H6. all: inversion H7.
      * apply pt. apply lts_choiceR. assumption.
    + intros t' Ht'. eapply H0; [ exact Ht' | reflexivity ].
    + intros p' t' mu1 mu2 Hd Hl1 Hl2. inversion Hl1; subst.
      * inversion H6; subst.
        -- inversion H7; subst.
           assert (Hobl : ((g ((𝛕 • P) + (𝛕 • Q))) ^ v) must_pass t')
             by (eapply com; [ exact Hd | apply lts_choiceL; apply lts_input | exact Hl2 ]).
           simpl in Hobl. eapply must_i_int_choice_l. exact Hobl.
        -- inversion H7; subst.
           assert (Hobl : ((g ((𝛕 • P) + (𝛕 • Q))) ^ v) must_pass t')
             by (eapply com; [ exact Hd | apply lts_choiceL; apply lts_input | exact Hl2 ]).
           simpl in Hobl. eapply must_i_int_choice_r. exact Hobl.
      * eapply com; [ exact Hd | apply lts_choiceR; eassumption | exact Hl2 ].
Qed.

(** ** Input congruence AT A CONFIGURATION

    The matching's innermost step, [ax_fwd_match], is an instance of
    [ax_input]: the mirror summand [fwdg c M] and the right-hand guard
    [c ? Q] have the *same* guard, only different continuations.  Its
    premise is therefore about the **bare** continuations, while the
    recursion's measure only ever bounds the *wrapped* configuration
    [Ѵⁿ (msgs l ‖ ·)] — and the wrapper cannot be moved inside a guard
    (a guard commits, a pending message bag does not).

    So what is needed is input congruence stated *with the context
    already in place*.  It holds, and the context need not be a message
    bag: any process that is **inert** — no [τ] and no input of its own,
    so its only moves are outputs — will do, provided the family of such
    contexts is closed under those outputs.  [R] is that family.

    Note what the three structural hypotheses buy: with [B] inert, the
    only [τ] of [B ‖ g (c ? P)] is [B] handing a message to the guard,
    and the only visible actions are [B]'s outputs and the guard's own
    input.  Every one of them has a [Q]-counterpart with the *same*
    label, which is why all five [must] fields transfer. *)

Lemma must_i_input_ctx : forall (R : proc -> Prop) (c : ChannelData) (P Q : proc),
  (forall B, R B -> (forall q, ~ lts B τ q)) ->
  (forall B, R B -> (forall a q, ~ lts B (ActExt (ActIn a)) q)) ->
  (forall B, R B -> forall mu B', lts B (ActExt mu) B' -> R B') ->
  (forall B, R B -> forall v,
     (B ‖ (subst_in_proc 0 v P)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (B ‖ (subst_in_proc 0 v Q))) ->
  forall B, R B -> (B ‖ g (c ? P)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (B ‖ g (c ? Q)).
Proof.
  intros R c P Q Hnt Hni Hcl HPQ B HB t Hm.
  remember (B ‖ g (c ? P)) as S eqn:HS.
  revert HS. revert B HB. induction Hm as [ S t Ho | S t Ho Hex Hpt IHpt Het IHet Hcom IHcom ];
    intros B HB HS; subst.
  - now apply m_now.
  - apply m_step.
    + exact Ho.
    + destruct Hex as ((x1,x2) & Hs). inversion Hs; subst.
      * inversion l; subst.
        -- match goal with HH : lts (g (c ? P)) (ActExt (ActIn _)) _ |- _ =>
             inversion HH; subst end.
           match goal with HB' : lts B (ActExt (ActOut _)) _ |- _ =>
             eexists; eapply ParLeft; eapply lts_comL; [ exact HB' | apply lts_input ] end.
        -- exfalso.
           match goal with HH : lts B (ActExt (ActIn _)) _ |- _ =>
             eapply Hni; [ exact HB | exact HH ] end.
        -- exfalso.
           match goal with HH : lts B τ _ |- _ => eapply Hnt; [ exact HB | exact HH ] end.
        -- match goal with HH : lts (g (c ? P)) τ _ |- _ => inversion HH end.
      * exists (B ‖ (g (c ? Q)) ▷ x2). eapply ParRight. eassumption.
      * inversion l1; subst.
        -- match goal with HB' : lts B (ActExt μ1) ?p2 |- _ =>
             exists ((p2 ‖ (g (c ? Q))) ▷ x2);
             eapply ParSync; [ exact eq | apply lts_parL; exact HB' | exact l2 ] end.
        -- match goal with HH : lts (g (c ? P)) (ActExt μ1) _ |- _ =>
             inversion HH; subst end.
           exists ((B ‖ (subst_in_proc 0 v Q)) ▷ x2).
           eapply ParSync; [ exact eq | apply lts_parR; apply lts_input | exact l2 ].
    + intros x Hx. inversion Hx; subst.
      * match goal with HH : lts (g (c ? Q)) (ActExt (ActIn _)) _ |- _ =>
          inversion HH; subst end.
        match goal with HB' : lts B (ActExt (ActOut _)) ?B2 |- _ =>
          apply (HPQ B2 (Hcl B HB _ B2 HB'));
          apply Hpt; eapply lts_comL; [ exact HB' | apply lts_input ] end.
      * exfalso.
        match goal with HH : lts B (ActExt (ActIn _)) _ |- _ =>
          eapply Hni; [ exact HB | exact HH ] end.
      * exfalso.
        match goal with HH : lts B τ _ |- _ => eapply Hnt; [ exact HB | exact HH ] end.
      * match goal with HH : lts (g (c ? Q)) τ _ |- _ => inversion HH end.
    + intros t' Ht'. eapply IHet; [ exact Ht' | exact HB | reflexivity ].
    + intros x t' mu1 mu2 Hd Hx Ht'. inversion Hx; subst.
      * match goal with HB' : lts B (ActExt mu1) ?B2 |- _ =>
          eapply (IHcom (B2 ‖ (g (c ? P))) t' mu1 mu2 Hd (lts_parL HB') Ht' B2
                   (Hcl B HB _ B2 HB') eq_refl) end.
      * match goal with HH : lts (g (c ? Q)) (ActExt mu1) _ |- _ =>
          inversion HH; subst end.
        apply (HPQ B HB v).
        eapply Hcom; [ exact Hd | apply lts_parR; apply lts_input | exact Ht' ].
Qed.

(** The same with a context [G] beside the guard — the configuration-level
    counterpart of [must_i_choice_input_compat].  [G]'s own transitions
    reach *literally the same* state on both sides, so they are discharged
    by the given [must] fact directly; only the guard's own input consults
    the premise.  Between them, [must_i_input_ctx] and this cover both
    places the matching needs an omega step: [ax_fwd_match] (no context)
    and [ax_choice_input] (with one). *)
Lemma must_i_choice_input_ctx :
  forall (R : proc -> Prop) (c : ChannelData) (P Q : proc) (G : gproc),
  (forall B, R B -> (forall q, ~ lts B τ q)) ->
  (forall B, R B -> (forall a q, ~ lts B (ActExt (ActIn a)) q)) ->
  (forall B, R B -> forall mu B', lts B (ActExt mu) B' -> R B') ->
  (forall B, R B -> forall v,
     (B ‖ (subst_in_proc 0 v P)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (B ‖ (subst_in_proc 0 v Q))) ->
  forall B, R B -> (B ‖ g ((c ? P) + G)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (B ‖ g ((c ? Q) + G)).
Proof.
  intros R c P Q G Hnt Hni Hcl HPQ B HB t Hm.
  remember (B ‖ g ((c ? P) + G)) as S eqn:HS.
  revert HS. revert B HB. induction Hm as [ S t Ho | S t Ho Hex Hpt IHpt Het IHet Hcom IHcom ];
    intros B HB HS; subst.
  - now apply m_now.
  - apply m_step.
    + exact Ho.
    + destruct Hex as ((x1,x2) & Hs). inversion Hs; subst.
      * inversion l; subst.
        -- match goal with HH : lts (g ((c ? P) + G)) (ActExt (ActIn _)) _ |- _ =>
             inversion HH; subst end.
           ++ match goal with HH : lts (g (c ? P)) (ActExt (ActIn _)) _ |- _ =>
                inversion HH; subst end.
              match goal with HB' : lts B (ActExt (ActOut _)) ?p2 |- _ =>
                exists ((p2 ‖ (subst_in_proc 0 v Q)) ▷ x2); eapply ParLeft;
                eapply lts_comL; [ exact HB' | apply lts_choiceL; apply lts_input ] end.
           ++ match goal with HB' : lts B (ActExt (ActOut _)) ?p2 |- _ =>
                match goal with HG : lts (g G) (ActExt (ActIn _)) ?q2 |- _ =>
                  exists ((p2 ‖ q2) ▷ x2); eapply ParLeft;
                  eapply lts_comL; [ exact HB' | apply lts_choiceR; exact HG ] end end.
        -- exfalso.
           match goal with HH : lts B (ActExt (ActIn _)) _ |- _ =>
             eapply Hni; [ exact HB | exact HH ] end.
        -- exfalso.
           match goal with HH : lts B τ _ |- _ => eapply Hnt; [ exact HB | exact HH ] end.
        -- match goal with HH : lts (g ((c ? P) + G)) τ _ |- _ => inversion HH; subst end.
           ++ match goal with HH : lts (g (c ? P)) τ _ |- _ => inversion HH end.
           ++ match goal with HG : lts (g G) τ ?q2 |- _ =>
                exists ((B ‖ q2) ▷ x2); eapply ParLeft; apply lts_parR;
                apply lts_choiceR; exact HG end.
      * exists (B ‖ (g ((c ? Q) + G)) ▷ x2). eapply ParRight. eassumption.
      * inversion l1; subst.
        -- match goal with HB' : lts B (ActExt μ1) ?p2 |- _ =>
             exists ((p2 ‖ (g ((c ? Q) + G))) ▷ x2);
             eapply ParSync; [ exact eq | apply lts_parL; exact HB' | exact l2 ] end.
        -- match goal with HH : lts (g ((c ? P) + G)) (ActExt μ1) _ |- _ =>
             inversion HH; subst end.
           ++ match goal with HH : lts (g (c ? P)) (ActExt μ1) _ |- _ =>
                inversion HH; subst end.
              exists ((B ‖ (subst_in_proc 0 v Q)) ▷ x2).
              eapply ParSync;
                [ exact eq | apply lts_parR; apply lts_choiceL; apply lts_input | exact l2 ].
           ++ match goal with HG : lts (g G) (ActExt μ1) ?q2 |- _ =>
                exists ((B ‖ q2) ▷ x2);
                eapply ParSync;
                  [ exact eq | apply lts_parR; apply lts_choiceR; exact HG | exact l2 ] end.
    + intros x Hx. inversion Hx; subst.
      * match goal with HH : lts (g ((c ? Q) + G)) (ActExt (ActIn _)) _ |- _ =>
          inversion HH; subst end.
        -- match goal with HH : lts (g (c ? Q)) (ActExt (ActIn _)) _ |- _ =>
             inversion HH; subst end.
           match goal with HB' : lts B (ActExt (ActOut _)) ?B2 |- _ =>
             apply (HPQ B2 (Hcl B HB _ B2 HB'));
             apply Hpt; eapply lts_comL;
               [ exact HB' | apply lts_choiceL; apply lts_input ] end.
        -- match goal with HB' : lts B (ActExt (ActOut _)) _ |- _ =>
             match goal with HG : lts (g G) (ActExt (ActIn _)) _ |- _ =>
               apply Hpt; eapply lts_comL;
                 [ exact HB' | apply lts_choiceR; exact HG ] end end.
      * exfalso.
        match goal with HH : lts B (ActExt (ActIn _)) _ |- _ =>
          eapply Hni; [ exact HB | exact HH ] end.
      * exfalso.
        match goal with HH : lts B τ _ |- _ => eapply Hnt; [ exact HB | exact HH ] end.
      * match goal with HH : lts (g ((c ? Q) + G)) τ _ |- _ => inversion HH; subst end.
        -- match goal with HH : lts (g (c ? Q)) τ _ |- _ => inversion HH end.
        -- match goal with HG : lts (g G) τ _ |- _ =>
             apply Hpt; apply lts_parR; apply lts_choiceR; exact HG end.
    + intros t' Ht'. eapply IHet; [ exact Ht' | exact HB | reflexivity ].
    + intros x t' mu1 mu2 Hd Hx Ht'. inversion Hx; subst.
      * match goal with HB' : lts B (ActExt mu1) ?B2 |- _ =>
          eapply (IHcom (B2 ‖ (g ((c ? P) + G))) t' mu1 mu2 Hd (lts_parL HB') Ht' B2
                   (Hcl B HB _ B2 HB') eq_refl) end.
      * match goal with HH : lts (g ((c ? Q) + G)) (ActExt mu1) _ |- _ =>
          inversion HH; subst end.
        -- match goal with HH : lts (g (c ? Q)) (ActExt mu1) _ |- _ =>
             inversion HH; subst end.
           apply (HPQ B HB v).
           eapply Hcom;
             [ exact Hd | apply lts_parR; apply lts_choiceL; apply lts_input | exact Ht' ].
        -- match goal with HG : lts (g G) (ActExt mu1) _ |- _ =>
             eapply Hcom;
               [ exact Hd | apply lts_parR; apply lts_choiceR; exact HG | exact Ht' ] end.
Qed.

(** The greatest-lower-bound law, likewise with an inert context in place.

    Only [com] needs the context's own moves: an internal choice has no
    external transition of its own, so the *only* way the pair can act
    visibly is [B] emitting — and that lands on the same statement at
    [B'], which the [must] induction supplies.  [ex] is unconditional
    (the internal choice always has its own [τ]) and [pt] is the two
    premises. *)
Lemma must_i_int_glb_ctx : forall (R : proc -> Prop) (p q1 q2 : proc),
  (forall B, R B -> (forall z, ~ lts B τ z)) ->
  (forall B, R B -> (forall a z, ~ lts B (ActExt (ActIn a)) z)) ->
  (forall B, R B -> forall mu B', lts B (ActExt mu) B' -> R B') ->
  (forall B, R B -> (B ‖ p) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (B ‖ q1)) ->
  (forall B, R B -> (B ‖ p) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (B ‖ q2)) ->
  forall B, R B -> (B ‖ p) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (B ‖ g ((𝛕 • q1) + (𝛕 • q2))).
Proof.
  intros R p q1 q2 Hnt Hni Hcl H1 H2 B HB t Hm.
  remember (B ‖ p) as S eqn:HS.
  revert HS. revert B HB. induction Hm as [ S t Ho | S t Ho Hex Hpt IHpt Het IHet Hcom IHcom ];
    intros B HB HS; subst.
  - now apply m_now.
  - apply m_step.
    + exact Ho.
    + exists ((B ‖ q1) ▷ t). eapply ParLeft. apply lts_parR.
      apply lts_choiceL. apply lts_tau.
    + intros x Hx. inversion Hx; subst.
      * match goal with HH : lts (g ((𝛕 • q1) + (𝛕 • q2))) (ActExt (ActIn _)) _ |- _ =>
          inversion HH; subst end;
        match goal with HH : lts (g (𝛕 • _)) (ActExt (ActIn _)) _ |- _ => inversion HH end.
      * exfalso.
        match goal with HH : lts B (ActExt (ActIn _)) _ |- _ =>
          eapply Hni; [ exact HB | exact HH ] end.
      * exfalso.
        match goal with HH : lts B τ _ |- _ => eapply Hnt; [ exact HB | exact HH ] end.
      * match goal with HH : lts (g ((𝛕 • q1) + (𝛕 • q2))) τ _ |- _ =>
          inversion HH; subst end;
        match goal with HH : lts (g (𝛕 • _)) τ _ |- _ => inversion HH; subst end.
        -- apply (H1 B HB). apply m_step; assumption.
        -- apply (H2 B HB). apply m_step; assumption.
    + intros t' Ht'. eapply IHet; [ exact Ht' | exact HB | reflexivity ].
    + intros x t' mu1 mu2 Hd Hx Ht'. inversion Hx; subst.
      * match goal with HB' : lts B (ActExt mu1) ?B2 |- _ =>
          eapply (IHcom (B2 ‖ p) t' mu1 mu2 Hd (lts_parL HB') Ht' B2
                   (Hcl B HB _ B2 HB') eq_refl) end.
      * match goal with HH : lts (g ((𝛕 • q1) + (𝛕 • q2))) (ActExt mu1) _ |- _ =>
          inversion HH; subst end;
        match goal with HH : lts (g (𝛕 • _)) (ActExt mu1) _ |- _ => inversion HH end.
Qed.


(** ** An unstable right-hand side, WITHOUT separating it

    The τ-layer built by porting VCCS's separation laws needs every
    τ-continuation to be a guarded sum ([tau_cont_nf], see the caveat at
    [VACCS_Matching.ax_below_tau_peel]) — an invariant VACCS normal forms
    do not have, because a continuation normalises to a *configuration*.

    This law removes the need for it.  It reads [must]'s own structure as
    a rule: if [q] can move internally, then [q must_pass t] is settled
    by its [pt] and [com] fields, so it suffices that

    - **every τ-successor of [q] is above [p]** — that is [pt], and it is
      where the recursion descends, on strictly smaller reducts;
    - **every input of [q] is answered by [p] holding the message** —
      that is [com], in its *asynchronous* reading.

    The second premise is the one that makes the law usable at all.  A
    synchronous formulation would demand [p ⟶[μ] p'] with [p' ⊑ q''],
    and the left need not offer the channel ([c ? 𝟘 ⊑ₘᵤₛₜᵢ 𝟘]).  Here it
    is enough that [(c!v•𝟘) ‖ p] be above the reduct — and that is
    exactly what the recursion produces
    ([VACCS_Matching.must_i_feed_below]).  The proof of the [com] case is
    where asynchrony does the work: the client emitted, so
    [TransitionShapeForOutputSimplified] splits it as [(c!v•𝟘) ‖ t'], and
    [must_msg_swap] moves that message from the client to the server.

    [q] is required not to emit — true of every guarded sum
    ([gsum_no_out]) — because an emission of [q] would have to be
    answered by an emission of [p], which nothing provides. *)

Lemma must_i_glb_tau : forall (p q : proc),
  (exists q0, lts q τ q0) ->
  (forall a q'', ~ lts q (ActExt (ActOut a)) q'') ->
  (forall q', lts q τ q' -> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q') ->
  (forall c v q'', lts q (ActExt (ActIn (c,v))) q'' ->
     ((c ! v • 𝟘) ‖ p) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q'') ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q.
Proof.
  intros p q (q0 & Hq0) Hnoout Htau Hin t Hm.
  induction Hm as [p0 t0 Hg | p0 t0 Hnh Hex Hpt IHpt Het IHet Hcom IHcom].
  - apply m_now. exact Hg.
  - assert (Hmpt : p0 must_pass t0) by (apply m_step; assumption).
    apply m_step.
    + exact Hnh.
    + exists (q0, t0). apply ParLeft. exact Hq0.
    + intros q' Hq'. apply (Htau q' Hq'). exact Hmpt.
    + intros t' Ht'. apply IHet; assumption.
    + intros q'' t' mu1 mu2 Hdual Hq'' Ht'.
      destruct mu1 as [(c,v)|(c,v)]; [ | exfalso; eapply Hnoout; exact Hq'' ].
      destruct mu2 as [(d,w)|(d,w)]; simpl in Hdual; [ inversion Hdual | ].
      injection Hdual as E1 E2. subst d w.
      apply (Hin c v q'' Hq'').
      apply TransitionShapeForOutputSimplified in Ht' as Hcgr.
      assert (Hm2 : p0 must_pass ((c ! v • 𝟘) ‖ t')).
      { eapply must_eq_client; [ exact Hcgr | exact Hmpt ]. }
      apply must_msg_swap in Hm2.
      assert (Hc2 : (p0 ‖ (c ! v • 𝟘)) ≡* ((c ! v • 𝟘) ‖ p0)) by (apply cgr_par_com).
      eapply (proj2 (must_i_cgr _ _ Hc2)). exact Hm2.
Qed.


(** The same law with **emissions allowed** on the right, at the price of
    the obvious premise: an emission of [q] must be answered by one of
    [p] whose target is again above.  [must_i_glb_tau] is the case where
    [q] never emits, which makes that premise vacuous — true of every
    guarded sum, false of a configuration carrying a bag.  With this
    version the law applies to a *configuration* on the right as well:
    the bag's own emissions are matched by the left's, at a strictly
    smaller bag. *)

Lemma must_i_glb_gen : forall (p q : proc),
  (exists q0, lts q τ q0) ->
  (forall q', lts q τ q' -> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q') ->
  (forall c v q'', lts q (ActExt (ActIn (c,v))) q'' ->
     ((c ! v • 𝟘) ‖ p) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q'') ->
  (forall c v q'', lts q (ActExt (ActOut (c,v))) q'' ->
     exists p'', lts p (ActExt (ActOut (c,v))) p'' /\ p'' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q'') ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q.
Proof.
  intros p q (q0 & Hq0) Htau Hin Hout t Hm.
  induction Hm as [p0 t0 Hg | p0 t0 Hnh Hex Hpt IHpt Het IHet Hcom IHcom].
  - apply m_now. exact Hg.
  - assert (Hmpt : p0 must_pass t0) by (apply m_step; assumption).
    apply m_step.
    + exact Hnh.
    + exists (q0, t0). apply ParLeft. exact Hq0.
    + intros q' Hq'. apply (Htau q' Hq'). exact Hmpt.
    + intros t' Ht'. apply IHet; assumption.
    + intros q'' t' mu1 mu2 Hdual Hq'' Ht'.
      destruct mu1 as [(c,v)|(c,v)].
      * destruct mu2 as [(d,w)|(d,w)]; simpl in Hdual; [ inversion Hdual | ].
        injection Hdual as E1 E2. subst d w.
        apply (Hin c v q'' Hq'').
        apply TransitionShapeForOutputSimplified in Ht' as Hcgr.
        assert (Hm2 : p0 must_pass ((c ! v • 𝟘) ‖ t')).
        { eapply must_eq_client; [ exact Hcgr | exact Hmpt ]. }
        apply must_msg_swap in Hm2.
        assert (Hc2 : (p0 ‖ (c ! v • 𝟘)) ≡* ((c ! v • 𝟘) ‖ p0)) by (apply cgr_par_com).
        eapply (proj2 (must_i_cgr _ _ Hc2)). exact Hm2.
      * destruct mu2 as [(d,w)|(d,w)]; simpl in Hdual; [ | inversion Hdual ].
        injection Hdual as E1 E2. subst d w.
        destruct (Hout c v q'' Hq'') as (p'' & Hp'' & Hsub).
        apply Hsub. eapply Hcom; [ | exact Hp'' | exact Ht' ]. reflexivity.
Qed.

(** ** …and the same law with the emissions matched only WEAKLY

    [must_i_glb_gen]'s output premise asks [p] to emit [(c,v)] *itself*,
    and that premise is **not** a semantic consequence of [p ⊑ q]
    ([VACCS_Matching.glb_output_premise_not_semantic]: a server [τ] only
    ever weakens, so [g (𝛕 • (c!v•𝟘))] sits below [c!v•𝟘] while offering
    no emission at all).  What *is* a consequence is the weak form —
    [VACCS_Matching.weak_out_of_below].

    The price is that the weak residues cannot be compared one by one:
    [must (W c v) t] has to follow from *all* of them passing [t]
    ([Hcollect]), which is why the intended [W c v] is the **internal
    choice** of the residues at [(c,v)]
    ([VACCS_Matching.ichoice_residues_below]).

    Only the [com]-output case differs from [must_i_glb_gen], and it is
    where the weak step is spent: [must_preserved_by_weak_nil_srv] carries
    [must p0 t0] along the server's own [τ]s to the state that actually
    emits, and *that* state's [com] field discharges the residue.  The
    [m_now] branch of its inversion is impossible, [t0] not being good. *)

Lemma must_i_glb_weak : forall (p q : proc) (W : ChannelData -> ValueData -> proc),
  (exists q0, lts q τ q0) ->
  (forall q', lts q τ q' -> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q') ->
  (forall c v q'', lts q (ActExt (ActIn (c,v))) q'' ->
     ((c ! v • 𝟘) ‖ p) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q'') ->
  (forall c v q'' t, lts q (ActExt (ActOut (c,v))) q'' ->
     (forall p1 p'', p ⟹[[]] p1 ->
        lts p1 (ActExt (ActOut (c,v))) p'' -> p'' must_pass t) ->
     (W c v) must_pass t) ->
  (forall c v q'', lts q (ActExt (ActOut (c,v))) q'' ->
     (W c v) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q'') ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q.
Proof.
  intros p q W (q0 & Hq0) Htau Hin Hcollect Hout t Hm.
  induction Hm as [p0 t0 Hg | p0 t0 Hnh Hex Hpt IHpt Het IHet Hcom IHcom].
  - apply m_now. exact Hg.
  - assert (Hmpt : p0 must_pass t0) by (apply m_step; assumption).
    apply m_step.
    + exact Hnh.
    + exists (q0, t0). apply ParLeft. exact Hq0.
    + intros q' Hq'. apply (Htau q' Hq'). exact Hmpt.
    + intros t' Ht'. apply IHet; assumption.
    + intros q'' t' mu1 mu2 Hdual Hq'' Ht'.
      destruct mu1 as [(c,v)|(c,v)].
      * destruct mu2 as [(d,w)|(d,w)]; simpl in Hdual; [ inversion Hdual | ].
        injection Hdual as E1 E2. subst d w.
        apply (Hin c v q'' Hq'').
        apply TransitionShapeForOutputSimplified in Ht' as Hcgr.
        assert (Hm2 : p0 must_pass ((c ! v • 𝟘) ‖ t')).
        { eapply must_eq_client; [ exact Hcgr | exact Hmpt ]. }
        apply must_msg_swap in Hm2.
        assert (Hc2 : (p0 ‖ (c ! v • 𝟘)) ≡* ((c ! v • 𝟘) ‖ p0)) by (apply cgr_par_com).
        eapply (proj2 (must_i_cgr _ _ Hc2)). exact Hm2.
      * destruct mu2 as [(d,w)|(d,w)]; simpl in Hdual; [ | inversion Hdual ].
        injection Hdual as E1 E2. subst d w.
        apply (Hout c v q'' Hq'').
        apply (Hcollect c v q'' t' Hq'').
        intros p1 p'' Hp1 Ho.
        assert (Hm1 : p1 must_pass t0)
          by (eapply must_preserved_by_weak_nil_srv; [ exact Hmpt | exact Hp1 ]).
        inversion Hm1; subst.
        { exfalso. apply Hnh. assumption. }
        { eapply com; [ | exact Ho | exact Ht' ]. reflexivity. }
Qed.

(** ** τ MAKES YOU SAFE: fewer transitions plus one [τ] puts you above

    A general law, and much stronger than it looks.  Every field of
    [must] except [ex] is *contravariant* in the process's transitions —
    [pt] and [com] are obligations, so having fewer of them can only
    help — and [ex] is the one field that needs a transition to exist.
    So a process with a subset of another's transitions is above it as
    soon as it can move **internally**, whatever the discarded branches
    were doing:

    a state that can always move on its own owes the client nothing. *)

Lemma must_i_sub_tau : forall (p q : proc),
  (forall al z, lts q al z -> lts p al z) ->
  (exists z, lts q τ z) ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q.
Proof.
  intros p q Hsub Htau t Hm.
  induction Hm as [p0 t0 Hgood | p0 t0 nh ex pt IHpt et IHet com IHcom].
  - apply m_now. exact Hgood.
  - apply m_step.
    + exact nh.
    + destruct Htau as (z & Hz). exists (z ▷ t0). apply ParLeft. exact Hz.
    + intros p' Hp'. apply pt. apply Hsub. exact Hp'.
    + intros t' Ht'. apply IHet; [ exact Ht' | exact Hsub ].
    + intros p' t' mu1 mu2 Hd Hp' Ht'.
      eapply com; [ exact Hd | apply Hsub; exact Hp' | exact Ht' ].
Qed.

(** Hence a drop rule whose premise is **purely syntactic** and which says
    nothing at all about the discarded continuation — strictly outside the
    reach of [Harmless]/[Bad]/[BadK], all of which constrain it:

    an input guard sitting beside a [𝛕]-summand may always be discarded. *)

Lemma must_i_drop_tau : forall (c : ChannelData) (P : proc) (G : gproc),
  (exists z, lts (g G) τ z) ->
  (g ((c ? P) + G)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (g G).
Proof.
  intros c P G Htau. apply must_i_sub_tau; [ | exact Htau ].
  intros al z Hz. apply lts_choiceR. exact Hz.
Qed.


(** ** THE MESSAGE-LAYER POOLING LAW

    [ax_share_in] pools two branches of an internal choice at a shared
    **input guard**.  Its message-layer counterpart is this: two branches
    that carry the **same pending message** pool their residues, and the
    message factors out of the choice —

      (c!v•𝟘 ‖ X) ⊕ (c!v•𝟘 ‖ Y)  ⊑ₘᵤₛₜᵢ  c!v•𝟘 ‖ (X ⊕ Y)

    Both sides have the same [pt] obligation (the two members) and the
    same free [ex] (an internal choice always has a τ).  The right-hand
    side has one obligation the left-hand side does not — the [com] at
    its own emission — and that is exactly what makes the law non-trivial
    **and** what makes it provable: each member of the left carries the
    very same message, so each has that [com] too, and
    [must_i_nil_choice_join] recombines the two residues.

    The converse direction is derivable ([ax_int_glb] over
    [ax_par]+[ax_int_l]/[ax_int_r]), so the two are must-equivalent; it is
    this direction that is new.  Note that no rule of the system can
    produce it: the left-hand side is a **guarded sum** and the right a
    **parallel composition**, [≡*] does not distribute [‖] over [+], and
    the expansion law does not apply because a message is not a [gproc]. *)

Lemma cgr_nil_par_l : forall (p : proc), ((g (𝟘 : gproc)) : proc) ‖ p ≡* p.
Proof.
  intro p. etransitivity; [ apply cgr_par_com | apply cgr_par_nil ].
Qed.

Lemma must_i_nil_choice_join : forall (X Y t : proc),
  (((g (𝟘 : gproc)) : proc) ‖ X) must_pass t ->
  (((g (𝟘 : gproc)) : proc) ‖ Y) must_pass t ->
  (((g (𝟘 : gproc)) : proc) ‖ ((g ((𝛕 • X) + (𝛕 • Y))) : proc)) must_pass t.
Proof.
  intros X Y t H1 H2.
  apply (proj1 (must_i_cgr _ _ (cgr_nil_par_l ((g ((𝛕 • X) + (𝛕 • Y))) : proc)))).
  apply must_i_tau_choice_join.
  - apply (proj2 (must_i_cgr _ _ (cgr_nil_par_l X))). exact H1.
  - apply (proj2 (must_i_cgr _ _ (cgr_nil_par_l Y))). exact H2.
Qed.

(** A message beside an all-[𝛕] sum has exactly two kinds of move: the
    sum's own τ, and the message's emission.  There is no
    synchronisation, the sum having no external transition at all. *)

Lemma msg_alltau_tau_inv : forall (c : ChannelData) (v : ValueData) (Y : gproc) (p' : proc),
  gAllTau Y ->
  lts (((c ! v • 𝟘) : proc) ‖ ((g Y) : proc)) τ p' ->
  exists q', lts ((g Y) : proc) τ q' /\ p' = (((c ! v • 𝟘) : proc) ‖ q').
Proof.
  intros c v Y p' HAT Hl. inversion Hl; subst;
    try (exfalso; eapply gAllTau_no_ext; [ exact HAT | eassumption ]);
    try (exfalso; match goal with H : lts (c ! v • 𝟘) τ _ |- _ => inversion H end);
    try (eexists; split; [ eassumption | reflexivity ]).
Qed.

Lemma msg_alltau_ext_inv : forall (c : ChannelData) (v : ValueData) (Y : gproc)
    (mu : ExtAct TypeOfActions) (p' : proc),
  gAllTau Y ->
  lts (((c ! v • 𝟘) : proc) ‖ ((g Y) : proc)) (ActExt mu) p' ->
  mu = ActOut (c,v) /\ p' = (((g (𝟘 : gproc)) : proc) ‖ ((g Y) : proc)).
Proof.
  intros c v Y mu p' HAT Hl. inversion Hl; subst.
  - match goal with H : lts (c ! v • 𝟘) (ActExt _) _ |- _ => inversion H; subst end.
    split; reflexivity.
  - exfalso. eapply gAllTau_no_ext; [ exact HAT | eassumption ].
Qed.

Lemma must_i_share_msg_aux : forall (c : ChannelData) (v : ValueData) (X Y t : proc),
  (((c ! v • 𝟘) : proc) ‖ X) must_pass t ->
  (((c ! v • 𝟘) : proc) ‖ Y) must_pass t ->
  (((c ! v • 𝟘) : proc) ‖ ((g ((𝛕 • X) + (𝛕 • Y))) : proc)) must_pass t.
Proof.
  intros c v X Y t H1 H2.
  assert (HAT : gAllTau ((𝛕 • X) + (𝛕 • Y))) by (simpl; split; exact I).
  remember (((c ! v • 𝟘) : proc) ‖ X) as L eqn:EL.
  revert EL H2.
  induction H1 as [t Hout | u t nh ex pt IHpt et IHet com IHcom]; intros EL H2.
  - now apply m_now.
  - subst u.
    apply m_step.
    + exact nh.
    + exists ((((c ! v • 𝟘) : proc) ‖ X), t).
      eapply ParLeft. apply lts_parR. apply lts_choiceL. apply lts_tau.
    + intros p' Hp'.
      destruct (msg_alltau_tau_inv c v _ p' HAT Hp') as (q' & Hq' & ->).
      inversion Hq'; subst.
      * inversion H4; subst. apply m_step; assumption.
      * inversion H4; subst. exact H2.
    + intros t' Ht'. apply IHet; [exact Ht' | reflexivity |].
      inversion H2; subst; [exfalso; apply nh; assumption | eapply et0; exact Ht'].
    + intros p' t' μ1 μ2 Hdual Hp' Ht'.
      destruct (msg_alltau_ext_inv c v _ μ1 p' HAT Hp') as (Hmu & ->).
      subst μ1. apply must_i_nil_choice_join.
      * eapply com; [exact Hdual | apply lts_parL; apply lts_output | exact Ht'].
      * inversion H2; subst; [exfalso; apply nh; assumption |].
        eapply com0; [exact Hdual | apply lts_parL; apply lts_output | exact Ht'].
Qed.

Corollary must_i_share_msg_pre : forall (c : ChannelData) (v : ValueData) (X Y : proc),
  (g ((𝛕 • (((c ! v • 𝟘) : proc) ‖ X)) + (𝛕 • (((c ! v • 𝟘) : proc) ‖ Y))))
    ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (((c ! v • 𝟘) : proc) ‖ ((g ((𝛕 • X) + (𝛕 • Y))) : proc)).
Proof.
  intros c v X Y t H. inversion H; subst.
  - now apply m_now.
  - apply must_i_share_msg_aux.
    + apply pt. apply lts_choiceL. apply lts_tau.
    + apply pt. apply lts_choiceR. apply lts_tau.
Qed.

End VACCS_Precongruence.
