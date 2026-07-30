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
  Subset_Act DefinitionAS Convergence VCCS_Static VCCS_Must_Characterization.

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
    (dropping values, keeping channel+polarity — [Φᴠᴄᴄꜱ]/[𝝳ᴠᴄᴄꜱ], same
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

Lemma par_nosync_transfer : forall (p1 pp rr : proc),
  (forall mu p' q', ~ (pp ⟶[mu] p' /\ rr ⟶[co mu] q')) ->
  (forall x, x ∈ ⌈ 𝝳ᴠᴄᴄꜱ ∘ Φᴠᴄᴄꜱ ⌉ (coR p1) -> x ∈ ⌈ 𝝳ᴠᴄᴄꜱ ∘ Φᴠᴄᴄꜱ ⌉ (coR pp)) ->
  (forall mu p' q', ~ (p1 ⟶[mu] p' /\ rr ⟶[co mu] q')).
Proof.
  intros p1 pp rr Hns Hincl mu p' q' (Hp1 & Hrr).
  unfold elem_of, subset_of, map_set in Hincl.
  destruct mu as [[c v]|[c v]]; simpl in Hrr.
  - assert (Hmem : ActOut (c,v) ∈ coR p1).
    { unfold coR, elem_of, subset_of.
      exists (ActIn (c,v)). repeat split.
      - intro Hr. eapply lts_refuses_spec2 in Hr. apply Hr. exists p'. exact Hp1.
      - intro F; exact F. }
    destruct (Hincl (𝝳ᴠᴄᴄꜱ (Φᴠᴄᴄꜱ (ActOut (c,v)))) (ex_intro _ (ActOut (c,v)) (conj Hmem eq_refl)))
      as (nu & Hnu & Heq).
    destruct nu as [[c2 v2]|[c2 v2]]; simpl in Heq; try discriminate.
    inversion Heq; subst.
    unfold coR, elem_of, subset_of in Hnu.
    destruct Hnu as (mu2 & Hnr & Hd & Hb).
    destruct mu2 as [[c3 v3]|[c3 v3]]; simpl in Hd; try (exfalso; exact Hd).
    inversion Hd; subst.
    eapply lts_refuses_spec1 in Hnr as (p2 & Hl).
    destruct (lts_in_value_swap pp (ActIn (c2,v2)) p2 Hl c2 v2 v eq_refl) as (p3 & Hl').
    eapply (Hns (ActIn (c2,v)) p3 q').
    split; [exact Hl' | simpl; exact Hrr].
  - assert (Hmem : ActIn (c,v) ∈ coR p1).
    { unfold coR, elem_of, subset_of.
      exists (ActOut (c,v)). repeat split.
      - intro Hr. eapply lts_refuses_spec2 in Hr. apply Hr. exists p'. exact Hp1.
      - intro F; exact F. }
    destruct (Hincl (𝝳ᴠᴄᴄꜱ (Φᴠᴄᴄꜱ (ActIn (c,v)))) (ex_intro _ (ActIn (c,v)) (conj Hmem eq_refl)))
      as (nu & Hnu & Heq).
    destruct nu as [[c2 v2]|[c2 v2]]; simpl in Heq; try discriminate.
    inversion Heq; subst.
    unfold coR, elem_of, subset_of in Hnu.
    destruct Hnu as (mu2 & Hnr & Hd & Hb).
    destruct mu2 as [[c3 v3]|[c3 v3]]; simpl in Hd; try (exfalso; exact Hd).
    inversion Hd; subst.
    assert (Hindep : rr ↛[ActIn (c2,v2)]).
    { destruct (decide (rr ↛[ActIn (c2,v2)])) as [?|Hnr2]; [assumption|].
      exfalso.
      eapply lts_refuses_spec1 in Hnr2 as (q2 & Hl2).
      eapply lts_refuses_spec1 in Hnr as (p2 & Hlp2).
      eapply (Hns (ActOut (c2,v2)) p2 q2).
      split; [exact Hlp2 | simpl; exact Hl2]. }
    pose proof (lts_in_refuse_channel_indep rr c2 v2 v Hindep) as Hindep'.
    eapply lts_refuses_spec2 in Hindep'. apply Hindep'. exists q'. exact Hrr.
Qed.

Lemma par_coR_abs_mono : forall (p1 pp rr : proc),
  (forall x, x ∈ ⌈ 𝝳ᴠᴄᴄꜱ ∘ Φᴠᴄᴄꜱ ⌉ (coR p1) -> x ∈ ⌈ 𝝳ᴠᴄᴄꜱ ∘ Φᴠᴄᴄꜱ ⌉ (coR pp)) ->
  forall x, x ∈ ⌈ 𝝳ᴠᴄᴄꜱ ∘ Φᴠᴄᴄꜱ ⌉ (coR (p1 ‖ rr)) -> x ∈ ⌈ 𝝳ᴠᴄᴄꜱ ∘ Φᴠᴄᴄꜱ ⌉ (coR (pp ‖ rr)).
Proof.
  intros p1 pp rr Hincl x Hx.
  unfold elem_of, subset_of, map_set in *.
  destruct Hx as (nu & Hnu & Heq).
  apply par_coR_union in Hnu.
  destruct Hnu as [Hnu | Hnu].
  - assert (Hx1 : x ∈ ⌈ 𝝳ᴠᴄᴄꜱ ∘ Φᴠᴄᴄꜱ ⌉ (coR p1)).
    { exists nu. split; assumption. }
    apply Hincl in Hx1. unfold elem_of, subset_of, map_set in Hx1.
    destruct Hx1 as (nu' & Hnu' & Heq').
    exists nu'. split; [apply par_coR_union; left; exact Hnu' | exact Heq'].
  - exists nu. split; [apply par_coR_union; right; exact Hnu | exact Heq].
Qed.

(** ** [‖]-precongruence for [≼ₐₛ], and the [⊑ₘᵤₛₜᵢ] corollaries

    Assembles [par_wt_transfer] (turn the given trace of the RHS into
    matching traces of its two components, plus the substitution
    property), [par_stable_iff] (transfer/reconstruct stability),
    [par_nosync_transfer] (transfer the "no synchronisation possible"
    side of stability across the acceptance-set comparison), and
    [par_coR_abs_mono] (transfer the coR inclusion itself) into the full
    [≼ₐₛ]-precongruence for one argument of [‖], then the other by
    commutativity, then both together by transitivity. *)

Lemma must_i_par_bhv_pre : forall p p' r, Static p -> Static p' -> Static r -> p ≼ₐₛ p' -> (p‖r) ≼ₐₛ (p'‖r).
Proof.
  intros p p' r Hsp Hsp' Hsr (Hc1 & Hc2).
  split.
  - intros s _. apply Static_converge. apply static_par; [exact Hsp' | exact Hsr].
  - intros s t2 _ Hwt Hst.
    destruct (par_wt_transfer s (p'‖r) t2 Hwt p' r eq_refl) as (q'' & r'' & s_q & s_r & Ht2 & Hq'' & Hr'' & Hsub).
    subst t2.
    apply par_stable_iff in Hst as (Hstq & Hstr & Hnosync).
    destruct (Hc2 s_q q'' (Static_converge _ p Hsp) Hq'' Hstq) as (p1 & Hwp1 & Hstp1 & Hinclp1).
    exists (p1 ‖ r'').
    repeat split.
    + apply Hsub. exact Hwp1.
    + apply par_stable_iff. repeat split.
      * exact Hstp1.
      * exact Hstr.
      * eapply par_nosync_transfer; [exact Hnosync | exact Hinclp1].
    + intros x Hx. eapply par_coR_abs_mono; [exact Hinclp1 | exact Hx].
Qed.

Lemma must_i_par_compat : forall p p' r, Static p -> Static p' -> Static r -> p ⊑ₘᵤₛₜᵢ p' -> (p‖r) ⊑ₘᵤₛₜᵢ (p'‖r).
Proof.
  intros p p' r Hsp Hsp' Hsr Hpq.
  apply must_iff_acceptance_set_VCCS_without_toFW.
  apply must_i_par_bhv_pre; [exact Hsp | exact Hsp' | exact Hsr |].
  apply must_iff_acceptance_set_VCCS_without_toFW. exact Hpq.
Qed.

Lemma must_i_par_compat_r : forall p q q', Static p -> Static q -> Static q' -> q ⊑ₘᵤₛₜᵢ q' -> (p‖q) ⊑ₘᵤₛₜᵢ (p‖q').
Proof.
  intros p q q' Hsp Hsq Hsq' Hqq'.
  assert (Hcomm1 : (p‖q) ≡* (q‖p)) by (constructor; constructor).
  assert (Hcomm2 : (q'‖p) ≡* (p‖q')) by (constructor; constructor).
  apply must_i_cgr in Hcomm1 as (Hd1a & Hd1b).
  apply must_i_cgr in Hcomm2 as (Hd2a & Hd2b).
  intros t Hm.
  apply Hd2b.
  apply (must_i_par_compat q q' p Hsq Hsq' Hsp Hqq').
  apply Hd1b. exact Hm.
Qed.

Lemma must_i_par_compat2 : forall p p' q q', Static p -> Static p' -> Static q -> Static q' ->
  p ⊑ₘᵤₛₜᵢ p' -> q ⊑ₘᵤₛₜᵢ q' -> (p‖q) ⊑ₘᵤₛₜᵢ (p'‖q').
Proof.
  intros p p' q q' Hsp Hsp' Hsq Hsq' Hpp' Hqq' t Hm.
  apply (must_i_par_compat_r p' q q' Hsp' Hsq Hsq' Hqq').
  apply (must_i_par_compat p p' q Hsp Hsp' Hsq Hpp').
  exact Hm.
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

End VCCS_Precongruence.
