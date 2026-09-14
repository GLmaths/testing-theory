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

(** * A mixed [𝛕]/external sum is not an internal choice

    A *negative* result, recorded because it constrains the design of
    [CompletenessAx.v]'s normal form and would otherwise be easy to
    assume away.

    [VCCS_Canonical.v]'s [canonical] guarantees at most one summand per
    action, which is what makes summand-to-summand matching possible.
    It does **not** separate [𝛕]-guards from external guards, so it still
    admits *mixed* sums such as [𝛕•P + Q] with [Q] external. One might
    hope those could be normalised into an internal choice
    [𝛕•P + 𝛕•(g Q)] and thereby reduced to the [⊕]-of-stable-sums shape
    that Hennessy's completeness argument uses. **They cannot**: the two
    are not even must-equivalent.

    The witness below is as small as it gets. With [c ≠ d]:
      [P := c!v•𝟘]   [Q := d!w•𝟘]   [t := c?①]
    - [g (𝛕•P + Q)] passes [t] ([probe_mixed_passes]): the [ex] field is
      satisfied by the [𝛕] itself, [pt] reduces to [P must_pass t] which
      holds, and [com] is vacuous because [t] never offers [d?].
    - [g (𝛕•P + 𝛕•(g Q))] fails [t] ([probe_intchoice_fails]): its [pt]
      field now *also* demands [g Q must_pass t], and that fails at its
      own [ex] field — a stable [Q] and a stable [t] with no common
      channel simply deadlock ([probe_Q_fails]).

    So turning the external siblings of a [𝛕] into a second internal
    branch **strengthens** the requirement, by making the sibling
    responsible for offering an interaction on its own. Consequences for
    the normal form:

    - Reaching the [⊕]-of-stable-sums shape needs a genuinely new law,
      not just the rules currently in [DefinitionAxiomatic.v]. The
      standard candidate from testing theory is
      [x + 𝛕•y ≂ 𝛕•(x + y) ⊕ 𝛕•y]; both probes here are consistent with
      it, and it remains to be proved.
    - Discarding the siblings outright is also wrong: a companion
      hand-calculation (with [t' := g (d?𝟘 + c?①)], where the [com] field
      forces the unprovable [𝟘 must_pass 𝟘]) shows
      [𝛕•P + Q ⊑ₘᵤₛₜᵢ 𝛕•P] holds **strictly**. Only the [⊑] direction is
      available, so [Q] carries real information.
    - Finally, a warning about reading the acceptance-set
      characterisation too quickly: these two processes have the *same*
      stable reducts after the empty trace. What separates them is
      [bhv_pre_cond2] at a *longer* trace ([s = [(d,w)!]]) — [cond2]
      quantifies over all traces, not just [[]]. *)

From stdpp Require Import base sets gmap.
From TestingTheory Require Import VCCS VCCS_Instance Must ActTau InputOutputActions
  gLts Bisimulation InteractionBetweenLts Testing_Predicate VCCS_Good WeakTransitions
  Convergence VCCS_Static VCCS_Precongruence.

Section VCCS_MixedSumProbes.

Context `{VP : VCCS_Parameters}.

Section MixedSumProbe.
Variables (c d : ChannelData) (v w : ValueData).
Hypothesis Hcd : c <> d.

Let P : proc := g (c ! v • (g 𝟘)).
Let Q : gproc := d ! w • (g 𝟘).
Let t : proc := g (c ? (g ①)).

Lemma probe_t_not_good : ~ good_VCCS t.
Proof. intro H. inversion H. Qed.

Lemma probe_P_passes : P must_pass t.
Proof.
  apply m_step.
  - apply probe_t_not_good.
  - eexists. eapply ParSync; [| apply lts_output | eapply lts_input]. simpl. reflexivity.
  - intros p' Hp'. inversion Hp'.
  - intros t' Ht'. inversion Ht'.
  - intros p' t' μ1 μ2 Hdual Hp' Ht'.
    inversion Hp'; subst. inversion Ht'; subst.
    apply m_now. simpl. constructor.
Qed.

(** The mixed sum passes: the [𝛕] alone satisfies [ex], and [Q] is never
    called upon to interact. *)
Lemma probe_mixed_passes : g ((𝛕 • P) + Q) must_pass t.
Proof.
  apply m_step.
  - apply probe_t_not_good.
  - eexists. eapply ParLeft. apply lts_choiceL. apply lts_tau.
  - intros p' Hp'. inversion Hp'; subst.
    + inversion H3; subst. apply probe_P_passes.
    + inversion H3.
  - intros t' Ht'. inversion Ht'.
  - intros p' t' μ1 μ2 Hdual Hp' Ht'.
    exfalso.
    inversion Hp'; subst.
    + inversion H3.
    + inversion H3; subst.
      inversion Ht'; subst.
      simpl in Hdual.
      injection Hdual as Hd1 Hd2. apply Hcd. symmetry. exact Hd1.
Qed.

(** [Q] on its own deadlocks against [t]: both stable, no shared channel. *)
Lemma probe_Q_fails : ~ (g Q must_pass t).
Proof.
  intro Hm. inversion Hm; subst.
  - apply probe_t_not_good. assumption.
  - destruct ex as ((a2,b2) & Hstep). inversion Hstep; subst.
    + inversion l.
    + inversion l.
    + inversion l1; subst. inversion l2; subst.
      simpl in eq. injection eq as Hd1 Hd2. apply Hcd. symmetry. exact Hd1.
Qed.

(** Hence the internal choice fails where the mixed sum succeeded: making
    [Q] a [𝛕]-branch puts it under [pt], which demands it interact. *)
Lemma probe_intchoice_fails : ~ (g ((𝛕 • P) + (𝛕 • (g Q))) must_pass t).
Proof.
  intro Hm. inversion Hm; subst.
  - apply probe_t_not_good. assumption.
  - apply probe_Q_fails. apply pt. apply lts_choiceR. apply lts_tau.
Qed.

(** The two are therefore not must-equivalent — indeed incomparable in
    the direction that a normalisation step would need. *)
Corollary probe_mixed_not_below_intchoice :
  ~ (g ((𝛕 • P) + Q) ⊑ₘᵤₛₜᵢ g ((𝛕 • P) + (𝛕 • (g Q)))).
Proof.
  intro Hpre. apply probe_intchoice_fails. apply Hpre. apply probe_mixed_passes.
Qed.

End MixedSumProbe.

End VCCS_MixedSumProbes.
