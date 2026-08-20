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

(** * Precongruence lemmas for [⊑ₘᵤₛₜᵢ] on VCCS

    Building blocks for a Hennessy-Ingólfsdóttir-style inequational proof
    system for the must-preorder on VCCS. This file collects the lemmas
    that don't require case-splitting on the parallel operator. *)

From Stdlib.Program Require Import Equality.
From stdpp Require Import base.
From TestingTheory Require Import VCCS VCCS_Instance Must ActTau InputOutputActions
  gLts Bisimulation InteractionBetweenLts Testing_Predicate VCCS_Good WeakTransitions
  Subset_Act DefinitionAS Convergence VCCS_Static VCCS_Must_Characterization VCCS_Erasure.

Section VCCS_Precongruence.

Context `{VP : VCCS_Parameters}.

(** ** Internal-choice inequations

    [⊕] is not primitive in this VCCS syntax; it is definable as [𝛕•X + 𝛕•Y].
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
    ([VCCS_ReadySet.v]) does not apply to it either. (Found while
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
    [VCCS_Canonical.v]'s [canonical] alone does not deliver it, because
    it says nothing about [𝛕]-guards.

    Note what the law is **not**: it does *not* say the [𝛕]-guard's
    external siblings can be turned into a second internal branch on
    their own. [VCCS_MixedSumProbes.v] refutes that, machine-checked —
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

Lemma must_i_share_out_aux : forall c v P Q X' Y' t,
  g ((c ! v • P) + X') must_pass t -> g ((c ! v • Q) + Y') must_pass t ->
  g ((c ! v • (g ((𝛕 • P) + (𝛕 • Q)))) + X') must_pass t.
Proof.
  intros c v P Q X' Y' t H1 H2.
  remember (g ((c ! v • P) + X')) as L eqn:EL.
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
      * exists (g ((c ! v • (g ((𝛕 • P) + (𝛕 • Q)))) + X'), b2).
        eapply ParRight. exact l.
      * inversion l1; subst.
        { inversion H4; subst. eexists.
          eapply ParSync; [exact eq | apply lts_choiceL; apply lts_output | exact l2]. }
        { exists (a2,b2). eapply ParSync;
            [exact eq | apply lts_choiceR; exact H4 | exact l2]. }
    + intros p' Hp'. inversion Hp'; subst.
      * inversion H4.
      * apply pt. apply lts_choiceR. exact H4.
    + intros t' Ht'. apply IHet; [exact Ht' | reflexivity |].
      inversion H2; subst; [exfalso; apply nh; assumption | eapply et0; exact Ht'].
    + intros p' t' μ1 μ2 Hdual Hp' Ht'. inversion Hp'; subst.
      * inversion H4; subst.
        apply must_i_int_glb.
        { eapply com; [exact Hdual | apply lts_choiceL; apply lts_output | exact Ht']. }
        { inversion H2; subst; [exfalso; apply nh; assumption |].
          eapply com0; [exact Hdual | apply lts_choiceL; apply lts_output | exact Ht']. }
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

Corollary must_i_share_out_pre : forall c v P Q X' Y',
  g ((𝛕 • (g ((c ! v • P) + X'))) + (𝛕 • (g ((c ! v • Q) + Y'))))
    ⊑ₘᵤₛₜᵢ g ((c ! v • (g ((𝛕 • P) + (𝛕 • Q)))) + X').
Proof.
  intros c v P Q X' Y' t H. inversion H; subst.
  - now apply m_now.
  - apply must_i_share_out_aux with (Y' := Y') (Q := Q).
    + apply pt. apply lts_choiceL. apply lts_tau.
    + apply pt. apply lts_choiceR. apply lts_tau.
Qed.

(** ** Rewriting a [𝛕]-summand's continuation inside a sum

    The exact complement of [must_i_choice_stable_compat]
    ([VCCS_ReadySet.v]). Between them, *every* guard shape can have its
    continuation rewritten in place inside a larger sum:
    - [①]/[𝟘]/input/output summands are [gStable], so
      [must_i_choice_stable_compat] applies (combined with
      [must_i_input_compat]/[must_i_output_compat] to rewrite the
      continuation itself);
    - [𝛕]-summands are handled here.

    Both stay clear of the [ax_choice] counterexample for the same
    reason, from opposite sides: neither changes whether the rewritten
    summand is *initially stable*. There the rewrite replaced a stable
    summand by an unstable one, letting a fresh [𝛕] pre-empt the sibling
    branch; here the summand is [𝛕]-guarded before *and* after, so the
    sum's own stability is untouched and the sibling [gq] keeps exactly
    the role it had.

    Proof is a direct induction on the [must] derivation — no
    acceptance-set machinery needed, unlike the stable case. The only
    field doing real work is [pt]: the [𝛕]-reduct is [p'], recovered by
    feeding the left-hand side's own [pt] (which yields [p must_pass t])
    through the hypothesis [p ⊑ₘᵤₛₜᵢ p']. The [com] field never sees the
    [𝛕]-summand at all, since a [𝛕]-guard has no external transitions. *)

(** ** Flattening a nested internal choice

    [gAllTau Y] says every summand of [Y] is [𝛕]-guarded — so [g Y] is a
    pure internal choice, with no external offers of its own. In that
    case a [𝛕] leading to it is redundant:

      [gAllTau Y -> g (X + 𝛕•(g Y)) ≂ₘᵤₛₜᵢ g (X + Y)]

    Note the side condition is essential and is exactly what
    distinguishes this law from the τ-separation law above: if [Y] had
    *external* summands, moving it up would expose them at top level,
    which changes behaviour (that is precisely the content of
    [must_i_tau_sep_*] and of [VCCS_MixedSumProbes.v]). Note also that
    [𝟘] must **not** count as all-[𝛕]: [X + 𝛕•(g 𝟘)] has a [𝛕] into a
    deadlock, whereas [X + 𝟘] does not, and the two differ.

    This is what makes the normal-form construction *terminate*. After
    separating a mixed sum with [must_i_tau_sep_l] one recurses into
    [X + Y]; if [Y] could itself be a pure internal choice, its
    [𝛕]-summands would re-enter the count and the obvious measure
    (number of top-level [𝛕]-summands) would not decrease. Flattening
    first ensures every [𝛕]-summand's continuation is *stable*, and then
    separation strictly decreases that measure. *)

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

    Since VCCS's [gLtsEq] instance takes [⋍ := ≡*] (structural congruence),
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

Lemma must_i_output_compat (c : ChannelData) (v : ValueData) (p q : proc) :
  p ⊑ₘᵤₛₜᵢ q -> g (c ! v • p) ⊑ₘᵤₛₜᵢ g (c ! v • q).
Proof.
  intros Hpq t Hm.
  remember (g (c ! v • p)) as P eqn:HP.
  induction Hm.
  - now apply m_now.
  - subst.
    apply m_step.
    + exact nh.
    + destruct ex as ((a2, b2) & Hstep).
      inversion Hstep; subst.
      * inversion l.
      * exists (g (c ! v • q), b2).
        eapply ParRight.
        exact l.
      * inversion l1; subst.
        exists (q, b2).
        eapply ParSync; [exact eq | eapply lts_output | exact l2].
    + intros p' Hp'.
      inversion Hp'.
    + intros t' Ht'.
      eapply H0; [exact Ht' | reflexivity].
    + intros p' t' μ1 μ2 Hdual Hp' Ht'.
      inversion Hp'; subst.
      eapply Hpq.
      eapply com; [exact Hdual | eapply lts_output | exact Ht'].
Qed.

(** ** Precongruence for the τ prefix

    Unlike the output prefix, [𝛕•p] has a τ-successor ([p] itself), so
    here it is the [pt] field (not [com]) that uses [Hpq] directly; [com]
    is vacuous instead (no external transitions to synchronise on). *)

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
    not the argument itself — see the [VCCS_Precongruence] module
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
    in [VCCS_Instance.v]). Monotonicity (all that
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
    + destruct mu1 as [z|z]; simpl in *; exact Hb.
  - intros (mu2 & Hnr & Hd & Hb).
    unfold elem_of, subset_of in *.
    destruct mu1 as [[c1 v1]|[c1 v1]]; destruct mu2 as [[c2 v2]|[c2 v2]]; simpl in Hd, Hb |- *;
      try (exact (match Hd with end)); inversion Hd; subst.
    + exists (ActOut (c1,v1)). repeat split.
      all: [> (intro Hc; apply Hnr; apply res_ext_stable_iff in Hc; simpl in Hc; exact Hc) | exact Hb].
    + exists (ActIn (c1,v1)). repeat split.
      all: [> (intro Hc; apply Hnr; apply res_ext_stable_iff in Hc; simpl in Hc; exact Hc) | exact Hb].
Qed.

Lemma res_coR_mono : forall p q,
  (forall x, x ∈ coR p -> x ∈ coR q) -> forall y, y ∈ coR (ν p) -> y ∈ coR (ν q).
Proof.
  intros p q Hsub y Hy.
  apply res_coR_iff. apply Hsub. apply res_coR_iff. exact Hy.
Qed.

(** ** Lifting [res_coR_iff] through VCCS's label abstraction [𝝳ᴠᴄᴄꜱ ∘ Φᴠᴄᴄꜱ]

    [≼ₐₛ]'s [bhv_pre_cond2] (DefinitionAS.v) is stated over the *image*
    [⌈𝝳∘Φ⌉(coR p')], not raw [coR p'] — abstracted-set inclusion does not
    in general imply raw-set inclusion, so [res_coR_mono] alone isn't
    enough. The fix: [𝝳ᴠᴄᴄꜱ ∘ Φᴠᴄᴄꜱ] commutes with the channel shift
    ([VarC_action_add]/[VarC_preaction_add]) by direct computation — both
    sides just extract-and-rewrap the channel component — so
    [res_coR_iff] lifts through the abstraction essentially for free. *)

Lemma Phi_delta_shift_commute : forall mu,
  𝝳ᴠᴄᴄꜱ (Φᴠᴄᴄꜱ (VarC_action_add 1 mu)) = VarC_preaction_add 1 (𝝳ᴠᴄᴄꜱ (Φᴠᴄᴄꜱ mu)).
Proof.
  intros [[c v]|[c v]]; reflexivity.
Qed.

Lemma res_coR_abs_iff : forall p x,
  x ∈ ⌈ 𝝳ᴠᴄᴄꜱ ∘ Φᴠᴄᴄꜱ ⌉ (coR (ν p)) <-> (VarC_preaction_add 1 x) ∈ ⌈ 𝝳ᴠᴄᴄꜱ ∘ Φᴠᴄᴄꜱ ⌉ (coR p).
Proof.
  intros p x. unfold elem_of, subset_of, map_set in *. simpl.
  split.
  - intros (mu1 & Hmu1 & Hx).
    exists (VarC_action_add 1 mu1). split.
    + apply res_coR_iff. exact Hmu1.
    + rewrite Hx. symmetry. apply Phi_delta_shift_commute.
  - intros (mu2 & Hmu2 & Heq).
    destruct x as [cx|cx]; destruct mu2 as [[c2 v2]|[c2 v2]]; simpl in Heq; try discriminate; inversion Heq; subst.
    + exists (ActIn (cx, v2)). split.
      * apply res_coR_iff. simpl. exact Hmu2.
      * reflexivity.
    + exists (ActOut (cx, v2)). split.
      * apply res_coR_iff. simpl. exact Hmu2.
      * reflexivity.
Qed.

Lemma res_coR_abs_mono : forall p q,
  (forall x, x ∈ ⌈ 𝝳ᴠᴄᴄꜱ ∘ Φᴠᴄᴄꜱ ⌉ (coR p) -> x ∈ ⌈ 𝝳ᴠᴄᴄꜱ ∘ Φᴠᴄᴄꜱ ⌉ (coR q)) ->
  forall y, y ∈ ⌈ 𝝳ᴠᴄᴄꜱ ∘ Φᴠᴄᴄꜱ ⌉ (coR (ν p)) -> y ∈ ⌈ 𝝳ᴠᴄᴄꜱ ∘ Φᴠᴄᴄꜱ ⌉ (coR (ν q)).
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
    then bridges to [⊑ₘᵤₛₜᵢ] via [must_iff_acceptance_set_VCCS_without_toFW]
    (`VCCS_Must_Characterization.v`). *)

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

Lemma must_i_res_compat : forall p q, Static p -> Static q -> p ⊑ₘᵤₛₜᵢ q -> (ν p) ⊑ₘᵤₛₜᵢ (ν q).
Proof.
  intros p q Hsp Hsq Hpq.
  apply must_iff_acceptance_set_VCCS_without_toFW.
  apply must_i_res_bhv_pre; [exact Hsp | exact Hsq |].
  apply must_iff_acceptance_set_VCCS_without_toFW. exact Hpq.
Qed.

(** ** Precongruence for [If]

    [lts_ifOne]/[lts_ifZero] (VCCS.v) only ever evaluate [Eval_Eq 0 E]
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
    fact this relies on: VCCS's input transitions are inherently
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
Lemma must_i_output_branch_must : forall (c : ChannelData) (v v' : ValueData) (P Q t : proc),
  (g ((c ! v • P) + (c ! v' • Q))) must_pass t ->
  (g (c ! v • P)) must_pass t /\ (g (c ! v' • Q)) must_pass t.
Proof.
  intros c v v' P Q t Hm.
  remember (g ((c ! v • P) + (c ! v' • Q))) as R eqn:HR.
  induction Hm.
  - split; now apply m_now.
  - subst.
    split.
    + apply m_step.
      * exact nh.
      * destruct ex as ((a2,b2) & Hstep).
        inversion Hstep; subst.
        -- inversion l; subst; solve[inversion H6].
        -- exists (g (c ! v • P), b2). eapply ParRight. exact l.
        -- inversion l1; subst.
           ++ exists (P, b2).
              inversion H6; subst.
              eapply ParSync; [exact eq | exact H6 | exact l2].
           ++ inversion H6; subst.
              unfold dual in eq; simpl in eq.
              destruct μ2 as [[c2 v2]|[c2 v2]]; simpl in eq; [| exfalso; exact eq].
              inversion eq; subst.
              destruct (lts_in_value_swap t (ActIn (c2,v2)) b2 l2 c2 v2 v eq_refl) as (b2' & Hb2').
              exists (P, b2'). eapply ParSync; [ | eapply lts_output | exact Hb2'].
              reflexivity.
      * intros p' Hp'. inversion Hp'.
      * intros t' Ht'. apply (proj1 (H0 t' Ht' eq_refl)).
      * intros p' t' μ1 μ2 Hdual Hp' Ht'.
        inversion Hp'; subst.
        eapply com; [exact Hdual | eapply lts_choiceL; eapply lts_output | exact Ht'].
    + apply m_step.
      * exact nh.
      * destruct ex as ((a2,b2) & Hstep).
        inversion Hstep; subst.
        -- inversion l; subst; solve[inversion H6].
        -- exists (g (c ! v' • Q), b2). eapply ParRight. exact l.
        -- inversion l1; subst.
           ++ inversion H6; subst.
              unfold dual in eq; simpl in eq.
              destruct μ2 as [[c2 v2]|[c2 v2]]; simpl in eq; [| exfalso; exact eq].
              inversion eq; subst.
              destruct (lts_in_value_swap t (ActIn (c2,v2)) b2 l2 c2 v2 v' eq_refl) as (b2' & Hb2').
              exists (Q, b2'). eapply ParSync; [ | eapply lts_output | exact Hb2'].
              reflexivity.
           ++ inversion H6; subst.
              exists (a2, b2). eapply ParSync; [exact eq | exact H6 | exact l2].
      * intros p' Hp'. inversion Hp'.
      * intros t' Ht'. apply (proj2 (H0 t' Ht' eq_refl)).
      * intros p' t' μ1 μ2 Hdual Hp' Ht'.
        inversion Hp'; subst.
        eapply com; [exact Hdual | eapply lts_choiceR; eapply lts_output | exact Ht'].
Qed.

Lemma must_i_output_merge_l : forall (c : ChannelData) (v v' : ValueData) (P Q : proc),
  g ((c ! v • P) + (c ! v' • Q)) ⊑ₘᵤₛₜᵢ g ((𝛕 • (g (c ! v • P))) + (𝛕 • (g (c ! v' • Q)))).
Proof.
  intros c v v' P Q t Hm.
  remember (g ((c ! v • P) + (c ! v' • Q))) as LHS eqn:HLHS.
  induction Hm.
  - now apply m_now.
  - subst.
    assert (Hbranch : (g (c ! v • P)) must_pass t /\ (g (c ! v' • Q)) must_pass t).
    { apply must_i_output_branch_must. apply m_step; assumption. }
    apply m_step.
    + exact nh.
    + destruct ex as ((a2,b2) & Hstep).
      inversion Hstep; subst.
      * inversion l; subst; solve[inversion H6].
      * exists (g ((𝛕 • (g (c ! v • P))) + (𝛕 • (g (c ! v' • Q)))), b2).
        eapply ParRight. exact l.
      * inversion l1; subst.
        -- exists (g (c ! v • P), t). eapply ParLeft. eapply lts_choiceL. eapply lts_tau.
        -- exists (g (c ! v • P), t). eapply ParLeft. eapply lts_choiceL. eapply lts_tau.
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

(** ** Input-merge equation

    Simpler than the output case: since [lts_input] is already
    [∀v]-quantified in the LTS itself, both branches of [c?P + c?Q] are
    *always* simultaneously synchronisable at the same value, whichever
    branch a given transition of the choice happens to commit to — no
    value-swap lemma is needed at all here. *)

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

Lemma must_i_output_join_branches : forall (c : ChannelData) (v v' : ValueData) (P Q t : proc),
  (g (c ! v • P)) must_pass t -> (g (c ! v' • Q)) must_pass t -> (g ((c ! v • P) + (c ! v' • Q))) must_pass t.
Proof.
  intros c v v' P Q t Hm1 Hm2.
  remember (g (c ! v • P)) as X eqn:HX.
  revert Hm2.
  induction Hm1; intros Hm2.
  - now apply m_now.
  - subst.
    apply m_step.
    + exact nh.
    + destruct ex as ((a2,b2) & Hstep).
      inversion Hstep; subst.
      * inversion l.
      * exists (g ((c ! v • P) + (c ! v' • Q)), b2). eapply ParRight. exact l.
      * inversion l1; subst.
        exists (a2, b2). eapply ParSync; [exact eq | eapply lts_choiceL; eapply lts_output | exact l2].
    + intros p' Hp'. inversion Hp'; subst.
      * inversion H6.
      * inversion H6.
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

Lemma must_i_output_merge_r : forall (c : ChannelData) (v v' : ValueData) (P Q : proc),
  g ((𝛕 • (g (c ! v • P))) + (𝛕 • (g (c ! v' • Q)))) ⊑ₘᵤₛₜᵢ g ((c ! v • P) + (c ! v' • Q)).
Proof.
  intros c v v' P Q t Hm.
  apply must_i_output_join_branches.
  - eapply must_i_int_choice_l. exact Hm.
  - eapply must_i_int_choice_r. exact Hm.
Qed.

(** ** [‖]-precongruence — via the erasure bridge

    The original route to this went through the acceptance-set
    characterisation: [par_stable_iff], [par_ext_stable_iff],
    [par_coR_union], [par_wt_liftL]/[_R], [par_wt_transfer] (a full
    trace-interleaving construction), [lts_in_refuse_channel_indep],
    [par_nosync_transfer] (the raw/abstracted bridging lemma),
    [par_coR_abs_mono] and [must_i_par_bhv_pre] — a checkpoint's worth of
    lemmas, and three [Static] side conditions.

    All of it is superseded by [VCCS_Erasure.v]: a **contextual**
    preorder is better attacked by moving the context into the *test*
    than by re-deriving the context's effect on a behavioural
    characterisation.  The only obstruction is the outcome predicate, and
    erasing the server's [①]s removes it.  The result is also *stronger*
    — no [Static] anywhere. *)

Lemma must_i_par_compat : forall p p' r, p ⊑ₘᵤₛₜᵢ p' -> (p‖r) ⊑ₘᵤₛₜᵢ (p'‖r).
Proof. exact must_i_par_compat_erasure. Qed.

Lemma must_i_par_compat_r : forall p q q', q ⊑ₘᵤₛₜᵢ q' -> (p‖q) ⊑ₘᵤₛₜᵢ (p‖q').
Proof. exact must_i_par_compat_r_erasure. Qed.

Lemma must_i_par_compat2 : forall p p' q q',
  p ⊑ₘᵤₛₜᵢ p' -> q ⊑ₘᵤₛₜᵢ q' -> (p‖q) ⊑ₘᵤₛₜᵢ (p'‖q').
Proof. exact must_i_par_compat2_erasure. Qed.

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

Lemma must_i_output_distrib_l : forall (c : ChannelData) (v : ValueData) (P Q : proc),
  g ((c ! v • P) + (c ! v • Q)) ⊑ₘᵤₛₜᵢ g (c ! v • (g ((𝛕 • P) + (𝛕 • Q)))).
Proof.
  intros c v P Q t Hm.
  remember (g ((c ! v • P) + (c ! v • Q))) as p0 eqn:Heq.
  revert c v P Q Heq.
  induction Hm; intros c0 v0 P0 Q0 Heq.
  - now apply m_now.
  - subst p.
    apply m_step.
    + exact nh.
    + destruct ex as ((a2,b2) & Hstep). inversion Hstep; subst.
      * exfalso. inversion l; subst; inversion H6.
      * exists (g (c0 ! v0 • (g ((𝛕 • P0) + (𝛕 • Q0)))), b2). eapply ParRight. exact l.
      * inversion l1; subst; inversion H6; subst;
          (eexists; eapply ParSync; [exact eq | apply lts_output | exact l2]).
    + intros p' Hp'. inversion Hp'.
    + intros t' Ht'. eapply H0; [exact Ht' | reflexivity].
    + intros p' t' μ1 μ2 Hdual Hp' Ht'.
      inversion Hp'; subst.
      apply must_i_tau_choice_join.
      * eapply com; [exact Hdual | apply lts_choiceL; apply lts_output | exact Ht'].
      * eapply com; [exact Hdual | apply lts_choiceR; apply lts_output | exact Ht'].
Qed.

Lemma must_i_output_distrib_r : forall (c : ChannelData) (v : ValueData) (P Q : proc),
  g (c ! v • (g ((𝛕 • P) + (𝛕 • Q)))) ⊑ₘᵤₛₜᵢ g ((c ! v • P) + (c ! v • Q)).
Proof.
  intros c v P Q t Hm.
  apply must_i_output_join_branches.
  - apply (must_i_output_compat c v (g ((𝛕 • P) + (𝛕 • Q))) P); [apply must_i_int_choice_l | exact Hm].
  - apply (must_i_output_compat c v (g ((𝛕 • P) + (𝛕 • Q))) Q); [apply must_i_int_choice_r | exact Hm].
Qed.

(** ** Cross-value swapping: taking a guard from one branch and the
       residue from the other

    [must_i_share_out_*] pools two branches' continuations at a guard
    they *share*, i.e. at the same channel AND the same value.  That is
    not enough for completeness, because VCCS's ready-set abstraction
    ([coR_abs_incl_iff], [VCCS_ReadySet.v]) erases the value: a leaf may
    offer [c!v] where the target offers only [c!v'].  Witness (all
    continuations [𝟘], [v ≠ v'], [w ≠ w']):

      M := (c!v•𝟘 + d!w'•𝟘) ⊕ (c!v'•𝟘 + d!w•𝟘)     N := c!v'•𝟘 + d!w'•𝟘

    [M ⊑ₘᵤₛₜᵢ N] holds — [N]'s ready set is a *transversal*, one summand
    taken from each leaf — yet no leaf of [M] has its key set inside
    [N]'s, so neither [ax_int_l]/[_r], [ax_convex] nor [ax_share_out]
    reaches it.  (The merge equations do relate same-channel
    different-value pairs, but only when the pair is the whole sum:
    merging turns a stable summand into an unstable one, so it cannot be
    applied in a context without reintroducing the unsound [ax_choice].)

    The law below closes exactly that gap.  Note the asymmetry: the
    guard comes from the *second* branch, the residue from the *first*.
    Pooling at different values ([c!v'•(P ⊕ Q) + X']) would be
    **unsound** — after emitting [v'] the test sits in a state only [Q]
    was ever required to survive.

    The input analogue needs no rule: [ax_share_in] already gives
    [c?(P ⊕ Q) + X'], which [ax_input] + [ax_int_r] weakens to
    [c?Q + X']. *)

Lemma must_i_swap_out_aux : forall c v v' P Q X' Y' t,
  g ((c ! v • P) + X') must_pass t -> g ((c ! v' • Q) + Y') must_pass t ->
  g ((c ! v' • Q) + X') must_pass t.
Proof.
  intros c v v' P Q X' Y' t H1 H2.
  remember (g ((c ! v • P) + X')) as L eqn:EL.
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
      * exists (g ((c ! v' • Q) + X'), b2). eapply ParRight. exact l.
      * inversion l1; subst.
        { (* the moving branch is the [c!v] guard: the test must be
             offering *some* input on [c], hence (value-genericity) the
             one at [v'] too. *)
          inversion H4; subst.
          destruct μ2 as [a|a]; simpl in eq; [| contradiction]. subst a.
          destruct (lts_in_value_swap t _ b2 l2 c v v' eq_refl) as (b2' & Hb2').
          exists (Q, b2'). eapply ParSync;
            [| apply lts_choiceL; apply lts_output | exact Hb2'].
          simpl. reflexivity. }
        { exists (a2,b2). eapply ParSync;
            [exact eq | apply lts_choiceR; exact H4 | exact l2]. }
    + intros p' Hp'. inversion Hp'; subst.
      * inversion H4.
      * apply pt. apply lts_choiceR. exact H4.
    + intros t' Ht'. apply IHet; [exact Ht' | reflexivity |].
      inversion H2; subst; [exfalso; apply nh; assumption | eapply et0; exact Ht'].
    + intros p' t' μ1 μ2 Hdual Hp' Ht'. inversion Hp'; subst.
      * inversion H4; subst.
        inversion H2; subst; [exfalso; apply nh; assumption |].
        eapply com0; [exact Hdual | apply lts_choiceL; apply lts_output | exact Ht'].
      * eapply com; [exact Hdual | apply lts_choiceR; exact H4 | exact Ht'].
Qed.

Corollary must_i_swap_out_pre : forall c v v' P Q X' Y',
  g ((𝛕 • (g ((c ! v • P) + X'))) + (𝛕 • (g ((c ! v' • Q) + Y'))))
    ⊑ₘᵤₛₜᵢ g ((c ! v' • Q) + X').
Proof.
  intros c v v' P Q X' Y' t H. inversion H; subst.
  - now apply m_now.
  - apply must_i_swap_out_aux with (v := v) (P := P) (Y' := Y').
    + apply pt. apply lts_choiceL. apply lts_tau.
    + apply pt. apply lts_choiceR. apply lts_tau.
Qed.

End VCCS_Precongruence.
