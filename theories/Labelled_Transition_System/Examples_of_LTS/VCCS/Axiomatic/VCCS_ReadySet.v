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

(** * A guarded sum's own stability and (abstracted) ready set, computed structurally

    Groundwork for [CompletenessAx.v]: completeness of [ax_pre] w.r.t.
    [⊑ₘᵤₛₜᵢ] needs, at its core, to compare two guarded sums' own
    top-level behaviour — [≼ₐₛ]'s [bhv_pre_cond2] states this via the
    general (and, for a single guarded sum, needlessly heavy) abstracted
    [coR]/[AbsAction] machinery. This file computes, directly from a
    guarded sum's own syntax, exactly the same information [cond2]
    would extract via that machinery, with no abstraction plumbing left
    in the final statements:
    - [gStable_iff]: [(g M) ↛] (top-level stability, i.e. no available
      [𝛕]) iff [gStable M], a trivial structural recursion over [M]'s
      own summands.
    - [has_input_iff]/[has_output_iff]: [g M] can offer *some* input
      (resp. output) on channel [c] iff [has_input c M] (resp.
      [has_output c M]), again read directly off [M]'s summands.
    - [coR_abs_incl_iff]: the abstracted [coR] inclusion [≼ₐₛ]'s
      [cond2] actually demands between two stable configurations is
      *equivalent* to a plain implication between [has_input]/
      [has_output] facts — no residual abstraction-inclusion reasoning
      needed once stated this way.

    Worked out by hand from the primitives: [coR p := fun μ1 => ∃μ2,
    ¬p↛[μ2] ∧ dual μ2 μ1 ∧ blocking μ1] ([Subset_Act.v]), VCCS's
    [dual := ext_act_match] and [non_blocking := all_blocking_action :=
    False] (so [blocking] is unconditionally [True],
    [VCCS_Instance.v]), and VCCS's label abstraction [Φᴠᴄᴄꜱ]/[𝝳ᴠᴄᴄꜱ]
    ([VCCS_Instance.v] ~line 3113/3165), which together discard a
    label's *value* component entirely, keeping only channel+polarity
    ([Inputs_on c]/[Outputs_on c] in [PreAct]). Concretely this gives,
    for *any* [proc] (no [gStable]/[Static] needed): [Outputs_on c ∈
    ⌈𝝳∘Φ⌉(coR p) <-> ∃v, ¬p↛[ActIn (c,v)]] (dual of "[p] can input on
    [c]") and symmetrically for [Inputs_on c]/output — i.e. the
    abstracted ready set of *any* process is exactly a pair of
    (channel-indexed) input/output capability predicates, with the
    value entirely erased. For a guarded sum specifically, "[p] can
    input on [c] at some value" reduces further, structurally, to
    [has_input c M]. *)

From stdpp Require Import base sets gmap.
From TestingTheory Require Import VCCS VCCS_Instance Must ActTau InputOutputActions
  gLts Bisimulation WeakTransitions Convergence VCCS_Static
  VCCS_Precongruence Subset_Act DefinitionAS VCCS_Must_Characterization.

Section VCCS_ReadySet.

Context `{VP : VCCS_Parameters}.

(** ** Stability *)

Fixpoint gStable (M : gproc) : Prop :=
match M with
| ① => True
| 𝟘 => True
| c ? p => True
| c ! v • p => True
| 𝛕 • p => False
| M1 + M2 => gStable M1 /\ gStable M2
end.

Lemma gStable_iff : forall M, (g M) ↛ <-> gStable M.
Proof.
  induction M; simpl.
  - split.
    + intros _. exact I.
    + intros _. destruct (decide ((g ①) ↛)) as [Hd|Hd].
      * exact Hd.
      * exfalso. apply lts_refuses_spec1 in Hd as (r & Hl). inversion Hl.
  - split.
    + intros _. exact I.
    + intros _. destruct (decide ((g 𝟘) ↛)) as [Hd|Hd].
      * exact Hd.
      * exfalso. apply lts_refuses_spec1 in Hd as (r & Hl). inversion Hl.
  - split.
    + intros _. exact I.
    + intros _. destruct (decide ((g (c ? p)) ↛)) as [Hd|Hd].
      * exact Hd.
      * exfalso. apply lts_refuses_spec1 in Hd as (r & Hl). inversion Hl.
  - split.
    + intros _. exact I.
    + intros _. destruct (decide ((g (c ! v • p)) ↛)) as [Hd|Hd].
      * exact Hd.
      * exfalso. apply lts_refuses_spec1 in Hd as (r & Hl). inversion Hl.
  - split.
    + intro H. exfalso. pose proof (lts_set_spec1 (𝛕 • p) τ p lts_tau) as Hmem. rewrite H in Hmem. set_solver.
    + intro H. destruct H.
  - split; intro H.
    + apply choice_stable_iff in H as (H1 & H2). split; [apply IHM1 | apply IHM2]; assumption.
    + destruct H as (H1 & H2). apply choice_stable_iff. split; [apply IHM1 | apply IHM2]; assumption.
Qed.

(** ** The abstracted ready set of an arbitrary process, value-erased *)

Lemma coR_abs_Outputs_on_iff : forall (p : proc) c,
  Outputs_on c ∈ ⌈ 𝝳ᴠᴄᴄꜱ ∘ Φᴠᴄᴄꜱ ⌉ (coR p) <-> exists v, ~ p ↛[ActIn (c,v)].
Proof.
  intros p c. unfold coR, elem_of, subset_of, map_set in *; simpl.
  split.
  - intros (mu1 & (mu2 & Hnr & Hd & _) & Heq).
    destruct mu2 as [[c1 v1]|[c1 v1]]; simpl in Hd.
    + apply simplify_match_input in Hd. subst mu1. simpl in Heq. inversion Heq; subst. exists v1. exact Hnr.
    + apply simplify_match_output in Hd. subst mu1. simpl in Heq. discriminate Heq.
  - intros (v & Hnr).
    exists (ActOut (c,v)). split; [| reflexivity].
    exists (ActIn (c,v)). split; [exact Hnr | split; [apply simplify_match_input; reflexivity | exact (fun H => H)]].
Qed.

Lemma coR_abs_Inputs_on_iff : forall (p : proc) c,
  Inputs_on c ∈ ⌈ 𝝳ᴠᴄᴄꜱ ∘ Φᴠᴄᴄꜱ ⌉ (coR p) <-> exists v, ~ p ↛[ActOut (c,v)].
Proof.
  intros p c. unfold coR, elem_of, subset_of, map_set in *; simpl.
  split.
  - intros (mu1 & (mu2 & Hnr & Hd & _) & Heq).
    destruct mu2 as [[c1 v1]|[c1 v1]]; simpl in Hd.
    + apply simplify_match_input in Hd. subst mu1. simpl in Heq. discriminate Heq.
    + apply simplify_match_output in Hd. subst mu1. simpl in Heq. inversion Heq; subst. exists v1. exact Hnr.
  - intros (v & Hnr).
    exists (ActIn (c,v)). split; [| reflexivity].
    exists (ActOut (c,v)). split; [exact Hnr | split; [apply simplify_match_output; reflexivity | exact (fun H => H)]].
Qed.

(** ** A process's ability to fire an action, restated via the finite [lts_set] *)

Lemma no_lts_empty : forall (p : proc) a, (forall q, ~ lts p a q) -> lts_set p a = ∅.
Proof.
  intros p a Hno.
  apply set_eq. intro q. split.
  - intro Hq. apply lts_set_spec0 in Hq. exfalso. eapply Hno. exact Hq.
  - intro Hq. exfalso. eapply not_elem_of_empty. exact Hq.
Unshelve.
  all: typeclasses eauto.
Qed.

(** ** A guarded sum's own input/output offers, read off its syntax *)

Fixpoint has_input (c : ChannelData) (M : gproc) : Prop :=
match M with
| c' ? p => c = c'
| M1 + M2 => has_input c M1 \/ has_input c M2
| _ => False
end.

Fixpoint has_output (c : ChannelData) (M : gproc) : Prop :=
match M with
| c' ! v • p => c = c'
| M1 + M2 => has_output c M1 \/ has_output c M2
| _ => False
end.

Lemma has_input_iff : forall M c, (exists v, ~ (g M) ↛[ActIn (c,v)]) <-> has_input c M.
Proof.
  induction M; intro c0; simpl.
  - split.
    + intros (v & Hnr). exfalso. apply Hnr. apply no_lts_empty. intros q Hl. inversion Hl.
    + intros [].
  - split.
    + intros (v & Hnr). exfalso. apply Hnr. apply no_lts_empty. intros q Hl. inversion Hl.
    + intros [].
  - split.
    + intros (v & Hnr). destruct (decide (c0 = c)) as [Heq|Hneq]; [exact Heq|]. exfalso. apply Hnr. apply no_lts_empty. intros q Hl. inversion Hl; subst. apply Hneq. reflexivity.
    + intro Heq. subst c0. exists (cst VP.(O)). intro Hd. pose proof (lts_set_spec1 (c ? p) (ActExt (ActIn (c, cst VP.(O)))) (p ^ (cst VP.(O))) lts_input) as Hmem. rewrite Hd in Hmem. set_solver.
  - split.
    + intros (v0 & Hnr). exfalso. apply Hnr. apply no_lts_empty. intros q Hl. inversion Hl.
    + intros [].
  - split.
    + intros (v & Hnr). exfalso. apply Hnr. apply no_lts_empty. intros q Hl. inversion Hl.
    + intros [].
  - split.
    + intros (v & Hnr).
      destruct (decide ((g M1) ↛[ActIn (c0,v)])) as [Hd1|Hd1].
      * right. apply IHM2. exists v. intro Hd2. apply Hnr. apply choice_ext_stable_iff. split; assumption.
      * left. apply IHM1. exists v. exact Hd1.
    + intros [H1|H2].
      * apply IHM1 in H1 as (v & Hnr). exists v. intro Hc. apply choice_ext_stable_iff in Hc as (Hc1 & Hc2). apply Hnr. exact Hc1.
      * apply IHM2 in H2 as (v & Hnr). exists v. intro Hc. apply choice_ext_stable_iff in Hc as (Hc1 & Hc2). apply Hnr. exact Hc2.
Qed.

Lemma has_output_iff : forall M c, (exists v, ~ (g M) ↛[ActOut (c,v)]) <-> has_output c M.
Proof.
  induction M; intro c0; simpl.
  - split.
    + intros (v & Hnr). exfalso. apply Hnr. apply no_lts_empty. intros q Hl. inversion Hl.
    + intros [].
  - split.
    + intros (v & Hnr). exfalso. apply Hnr. apply no_lts_empty. intros q Hl. inversion Hl.
    + intros [].
  - split.
    + intros (v0 & Hnr). exfalso. apply Hnr. apply no_lts_empty. intros q Hl. inversion Hl.
    + intros [].
  - split.
    + intros (v0 & Hnr). destruct (decide (c0 = c)) as [Heq|Hneq]; [exact Heq|]. exfalso. apply Hnr. apply no_lts_empty. intros q Hl. inversion Hl; subst. apply Hneq. reflexivity.
    + intro Heq. subst c0. exists v. intro Hd. pose proof (lts_set_spec1 (c ! v • p) (ActExt (ActOut (c, v))) p lts_output) as Hmem. rewrite Hd in Hmem. set_solver.
  - split.
    + intros (v & Hnr). exfalso. apply Hnr. apply no_lts_empty. intros q Hl. inversion Hl.
    + intros [].
  - split.
    + intros (v & Hnr).
      destruct (decide ((g M1) ↛[ActOut (c0,v)])) as [Hd1|Hd1].
      * right. apply IHM2. exists v. intro Hd2. apply Hnr. apply choice_ext_stable_iff. split; assumption.
      * left. apply IHM1. exists v. exact Hd1.
    + intros [H1|H2].
      * apply IHM1 in H1 as (v & Hnr). exists v. intro Hc. apply choice_ext_stable_iff in Hc as (Hc1 & Hc2). apply Hnr. exact Hc1.
      * apply IHM2 in H2 as (v & Hnr). exists v. intro Hc. apply choice_ext_stable_iff in Hc as (Hc1 & Hc2). apply Hnr. exact Hc2.
Qed.

(** ** The [≼ₐₛ]-level ready-set inclusion, restated structurally *)

Lemma coR_abs_incl_iff : forall M N,
  (⌈ 𝝳ᴠᴄᴄꜱ ∘ Φᴠᴄᴄꜱ ⌉ (coR (g M)) ⊆ ⌈ 𝝳ᴠᴄᴄꜱ ∘ Φᴠᴄᴄꜱ ⌉ (coR (g N)))
  <-> (forall c, has_input c M -> has_input c N) /\ (forall c, has_output c M -> has_output c N).
Proof.
  intros M N. split.
  - intro Hincl. split.
    + intros c Hin. apply has_input_iff. apply has_input_iff in Hin as (v & Hnr).
      assert (Hmem : Outputs_on c ∈ ⌈ 𝝳ᴠᴄᴄꜱ ∘ Φᴠᴄᴄꜱ ⌉ (coR (g M))) by (apply coR_abs_Outputs_on_iff; exists v; exact Hnr).
      apply Hincl in Hmem. apply coR_abs_Outputs_on_iff in Hmem. exact Hmem.
    + intros c Hin. apply has_output_iff. apply has_output_iff in Hin as (v & Hnr).
      assert (Hmem : Inputs_on c ∈ ⌈ 𝝳ᴠᴄᴄꜱ ∘ Φᴠᴄᴄꜱ ⌉ (coR (g M))) by (apply coR_abs_Inputs_on_iff; exists v; exact Hnr).
      apply Hincl in Hmem. apply coR_abs_Inputs_on_iff in Hmem. exact Hmem.
  - intros (Hi & Ho) pre_mu Hmem.
    destruct pre_mu as [c|c].
    + apply coR_abs_Inputs_on_iff. apply coR_abs_Inputs_on_iff in Hmem.
      apply has_output_iff in Hmem. apply Ho in Hmem. apply has_output_iff in Hmem. exact Hmem.
    + apply coR_abs_Outputs_on_iff. apply coR_abs_Outputs_on_iff in Hmem.
      apply has_input_iff in Hmem. apply Hi in Hmem. apply has_input_iff in Hmem. exact Hmem.
Qed.

(** ** Guarded-choice precongruence, restricted to *stable* summands

    [must_i_choice_stable_compat] below closes what sessions 3-6 of this
    development treated as a hard blocker. The unrestricted rule
    ([ax_choice], removed from [DefinitionAxiomatic.v]) is *unsound*:
    replacing a stable summand by an unstable one lets a fresh [𝛕]
    pre-empt the sibling branch, permanently discarding it. Requiring
    [gStable] on *both* sides blocks exactly that move — and it turns
    out to be enough to make the whole acceptance-set argument go
    through.

    Two distinct facts do the work, and both need the stability
    hypotheses:
    - [gp'] stable ⟹ no [𝛕] is available on the [gp']-side at all, so
      any [𝛕] taken by [g (gp' + gq)] commits through [gq]. Every run
      that commits to [gq] can be mimicked *step for step* by
      [g (gp + gq)], so those cases are discharged with the **identical**
      witness ([p' := r], [coR]-inclusion by reflexivity) — nothing
      about [gp]/[gp'] is needed there.
    - [gp] stable ⟹ a matching run of [g gp] realising a trace
      [μ :: s'] must *start* with its [μ]-step ([wt_cons_stable]), which
      is exactly the shape [choice_wt_liftL_step_act] needs in order to
      lift it back up through [lts_choiceL].

    The session-3 obstacle ("[g (gp+gq)] can never reach the bare state
    [g gp] via any weak transition", which is what made the
    unrestricted assembly stall) is sidestepped rather than solved: in
    the zero-step case the witness taken is [g (gp + gq)] *itself*, not
    [g gp], and its [coR] is handled by [choice_coR_union] lifted to the
    abstracted level via [coR_abs_incl_iff] ([choice_coR_abs_mono_l]).
    This is also why the sharper [choice_wt_decomp_sharp] below is
    needed in place of [VCCS_Precongruence.v]'s [choice_wt_decomp']:
    the latter is a weaker implication that admits *spurious* cases
    (e.g. a zero-step run [g gp ⟹[[]] g gp]) which do not correspond to
    any real run of the choice, and in which no witness can be built. *)

Lemma wt_nil_stable : forall (p q : proc), p ↛ -> p ⟹[[]] q -> q = p.
Proof.
  intros p q Hst Hwt. inversion Hwt; subst.
  - reflexivity.
  - exfalso. pose proof (lts_set_spec1 p τ q0 l) as Hmem. rewrite Hst in Hmem. set_solver.
Qed.

Lemma wt_cons_stable : forall (p r : proc) mu s, p ↛ -> p ⟹[mu :: s] r ->
  exists q, p ⟶[mu] q /\ q ⟹[s] r.
Proof.
  intros p r mu s Hst Hwt. inversion Hwt; subst.
  - exfalso. pose proof (lts_set_spec1 p τ q l) as Hmem. rewrite Hst in Hmem. set_solver.
  - exists q. split; [exact l | exact w].
Qed.

(** Every weak transition of a guarded choice either takes no step at
    all, or takes a genuine *first committing step* from one of the two
    branches — unlike [choice_wt_decomp'], this records that first step,
    which is what makes the run liftable back onto another choice. *)

Lemma choice_wt_decomp_sharp : forall gp gq s r, (g (gp + gq)) ⟹[s] r ->
  (s = [] /\ r = g (gp + gq))
  \/ (exists q1, (g gp) ⟶ q1 /\ q1 ⟹[s] r)
  \/ (exists q1 mu s', s = mu :: s' /\ (g gp) ⟶[mu] q1 /\ q1 ⟹[s'] r)
  \/ (exists q1, (g gq) ⟶ q1 /\ q1 ⟹[s] r)
  \/ (exists q1 mu s', s = mu :: s' /\ (g gq) ⟶[mu] q1 /\ q1 ⟹[s'] r).
Proof.
  intros gp gq s r Hwt. inversion Hwt; subst.
  - left. split; reflexivity.
  - inversion l; subst.
    + right. left. exists q. split; [exact H3 | exact w].
    + right. right. right. left. exists q. split; [exact H3 | exact w].
  - inversion l; subst.
    + right. right. left. exists q, μ, s0. split; [reflexivity | split; [exact H3 | exact w]].
    + right. right. right. right. exists q, μ, s0. split; [reflexivity | split; [exact H3 | exact w]].
Qed.

Lemma choice_coR_abs_mono_l : forall gp gp' gq,
  (⌈ 𝝳ᴠᴄᴄꜱ ∘ Φᴠᴄᴄꜱ ⌉ (coR (g gp)) ⊆ ⌈ 𝝳ᴠᴄᴄꜱ ∘ Φᴠᴄᴄꜱ ⌉ (coR (g gp'))) ->
  (⌈ 𝝳ᴠᴄᴄꜱ ∘ Φᴠᴄᴄꜱ ⌉ (coR (g (gp + gq))) ⊆ ⌈ 𝝳ᴠᴄᴄꜱ ∘ Φᴠᴄᴄꜱ ⌉ (coR (g (gp' + gq)))).
Proof.
  intros gp gp' gq Hincl.
  apply coR_abs_incl_iff in Hincl as (Hi & Ho).
  apply coR_abs_incl_iff. split.
  - intros c [H1|H2]; simpl; [left; apply Hi; exact H1 | right; exact H2].
  - intros c [H1|H2]; simpl; [left; apply Ho; exact H1 | right; exact H2].
Qed.

Lemma must_i_choice_stable_bhv_pre : forall gp gp' gq,
  gStable gp -> gStable gp' ->
  Static (g gp) -> Static (g gp') -> Static (g gq) ->
  (g gp) ≼ₐₛ (g gp') -> (g (gp + gq)) ≼ₐₛ (g (gp' + gq)).
Proof.
  intros gp gp' gq Hstp Hstp' Hsp Hsp' Hsq (Hc1 & Hc2).
  split.
  - intros s _. apply Static_converge. constructor.
    constructor; [inversion Hsp' | inversion Hsq]; assumption.
  - intros s r Hconv Hwt Hstable.
    apply choice_wt_decomp_sharp in Hwt
      as [(Hs & Hr) | [(q1 & Hl & Hw) | [(q1 & mu & s' & Hs & Hl & Hw)
        | [(q1 & Hl & Hw) | (q1 & mu & s' & Hs & Hl & Hw)]]]].
    + (* no step taken: the choice itself is the witness, on both sides *)
      subst s r. exists (g (gp + gq)). repeat split.
      * apply wt_nil.
      * apply choice_stable_iff. split; [apply gStable_iff; exact Hstp |].
        apply choice_stable_iff in Hstable as (_ & Hsq2). exact Hsq2.
      * apply choice_coR_abs_mono_l.
        destruct (Hc2 [] (g gp') (Static_converge [] (g gp) Hsp) (wt_nil _)
          (proj2 (gStable_iff gp') Hstp')) as (p0 & Hw0 & Hst0 & Hincl0).
        rewrite (wt_nil_stable (g gp) p0 (proj2 (gStable_iff gp) Hstp) Hw0) in Hincl0.
        exact Hincl0.
    + (* [gp'] takes a [𝛕]: impossible, [gp'] is stable *)
      exfalso. pose proof (lts_set_spec1 (g gp') τ q1 Hl) as Hmem.
      rewrite (proj2 (gStable_iff gp') Hstp') in Hmem. set_solver.
    + (* [gp'] takes the first visible step: appeal to the hypothesis at [mu :: s'] *)
      subst s.
      assert (Hwp' : (g gp') ⟹[mu :: s'] r) by (eapply wt_act; [exact Hl | exact Hw]).
      destruct (Hc2 (mu :: s') r (Static_converge (mu :: s') (g gp) Hsp) Hwp' Hstable)
        as (r0 & Hw0 & Hst0 & Hincl0).
      destruct (wt_cons_stable (g gp) r0 mu s' (proj2 (gStable_iff gp) Hstp) Hw0)
        as (q0 & Hl0 & Hw0').
      exists r0. repeat split.
      * eapply choice_wt_liftL_step_act; [exact Hl0 | exact Hw0'].
      * exact Hst0.
      * exact Hincl0.
    + (* [gq] takes a [𝛕]: mimic exactly, same witness *)
      exists r. repeat split.
      * eapply choice_wt_liftR_step; [exact Hl | exact Hw].
      * exact Hstable.
      * reflexivity.
    + (* [gq] takes the first visible step: mimic exactly, same witness *)
      subst s. exists r. repeat split.
      * eapply choice_wt_liftR_step_act; [exact Hl | exact Hw].
      * exact Hstable.
      * reflexivity.
Qed.

Lemma must_i_choice_stable_compat : forall gp gp' gq,
  gStable gp -> gStable gp' ->
  Static (g gp) -> Static (g gp') -> Static (g gq) ->
  (g gp) ⊑ₘᵤₛₜᵢ (g gp') -> (g (gp + gq)) ⊑ₘᵤₛₜᵢ (g (gp' + gq)).
Proof.
  intros gp gp' gq Hstp Hstp' Hsp Hsp' Hsq Hpre.
  apply must_iff_acceptance_set_VCCS_without_toFW.
  apply must_i_choice_stable_bhv_pre; try assumption.
  apply must_iff_acceptance_set_VCCS_without_toFW.
  exact Hpre.
Qed.

End VCCS_ReadySet.
