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

(** * The guarded-sum normal-form theorem

    Every [Static] process is [⊢]-derivably equal to some guarded sum
    [g M] — the top-level shape [CompletenessAx.v]'s completeness proof
    needs in order to compare two [Static] processes structurally.

    Proved by well-founded induction on [size p], one case per [proc]
    constructor:
    - [p ‖ q]: normalize [p]/[q] individually (IH), combine via
      [ax_par], then flatten [g M1 ‖ g M2] via [ax_expansion_l]/[_r]
      (the expansion law, [VCCS_Expansion.v]).
    - [If E Then p Else q]: normalize [p]/[q] individually (IH), then
      pick whichever one [Eval_Eq 0 E] selects via [ax_cgr] +
      [cgr_if_true_step]/[cgr_if_false_step] — [Eval_Eq 0 E] is never
      [None] ([Eval_Eq_0_not_none], [VCCS_Precongruence.v]), so this
      covers every case; no separate "[If] over a guarded sum" rule is
      needed at all.
    - [ν p]: normalize [p] (IH), wrap via [ax_res], then eliminate the
      resulting [ν (g M)] via [ax_res_normalize_l]/[_r]
      ([VCCS_ResNormalize.v]).
    - [g M]: already a guarded sum — [ax_refl] both directions.
    - [pr_var _]/[rec _ • _]: excluded by [Static]. *)

From Stdlib.Wellfounded Require Import Inverse_Image.
From Stdlib Require Import List Permutation PeanoNat Lia.
From stdpp Require Import base sets gmap.
From TestingTheory Require Import VCCS VCCS_Instance Must VCCS_Static
  VCCS_Expansion VCCS_ResNormalize VCCS_Precongruence VCCS_ReadySet
  DefinitionAxiomatic VCCS_Canonical.

Section VCCS_NormalForm.

Context `{VP : VCCS_Parameters}.

Theorem normal_form : forall p, Static p -> exists M, gStatic M /\ ax_pre p (g M) /\ ax_pre (g M) p.
Proof.
  induction p as (p & IH) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intro Hsp.
  destruct p; simpl in *.
  - (* p1 ‖ p2 *)
    inversion Hsp; subst.
    destruct (IH p1) as (M1 & HM1 & Hf1 & Hb1); [simpl; lia | assumption |].
    destruct (IH p2) as (M2 & HM2 & Hf2 & Hb2); [simpl; lia | assumption |].
    exists ((ext M1 M2 + ext_r M2 M1) + int M1 M2).
    repeat split.
    + constructor.
      * constructor; [apply ext_gStatic | apply ext_r_gStatic]; assumption.
      * apply int_gStatic; assumption.
    + eapply ax_trans; [apply ax_par; eassumption | apply ax_expansion_l; assumption].
    + eapply ax_trans; [apply ax_expansion_r; assumption | apply ax_par; eassumption].
  - (* pr_var *)
    inversion Hsp.
  - (* rec x • p *)
    inversion Hsp.
  - (* If E Then p1 Else p2 *)
    inversion Hsp; subst.
    destruct (IH p1) as (M1 & HM1 & Hf1 & Hb1); [simpl; lia | assumption |].
    destruct (IH p2) as (M2 & HM2 & Hf2 & Hb2); [simpl; lia | assumption |].
    destruct (Eval_Eq 0 e) as [[|]|] eqn:Heval.
    + exists M1. repeat split; [assumption | | ].
      * eapply ax_trans; [| exact Hf1].
        apply ax_cgr; [assumption | constructor; eapply cgr_if_true_step; exact Heval].
      * eapply ax_trans; [exact Hb1 |].
        apply ax_cgr; [assumption | apply cgr_symm; constructor; eapply cgr_if_true_step; exact Heval].
    + exists M2. repeat split; [assumption | | ].
      * eapply ax_trans; [| exact Hf2].
        apply ax_cgr; [assumption | constructor; eapply cgr_if_false_step; exact Heval].
      * eapply ax_trans; [exact Hb2 |].
        apply ax_cgr; [assumption | apply cgr_symm; constructor; eapply cgr_if_false_step; exact Heval].
    + exfalso. eapply Eval_Eq_0_not_none. exact Heval.
  - (* ν p *)
    inversion Hsp; subst.
    destruct (IH p) as (M0 & HM0 & Hf0 & Hb0); [simpl; lia | assumption |].
    exists (resg M0).
    repeat split.
    + apply resg_gStatic. assumption.
    + eapply ax_trans; [apply ax_res; eassumption | apply ax_res_normalize_l; assumption].
    + eapply ax_trans; [apply ax_res_normalize_r; assumption | apply ax_res; eassumption].
  - (* g g, already a guarded sum — the constructor's own field is auto-named [g], shadowing the [g] coercion locally (harmless: not referenced here) *)
    inversion Hsp; subst.
    exists g. repeat split; [assumption | apply ax_refl | apply ax_refl].
Qed.

(** ** The canonical normal form

    [normal_form] followed by [VCCS_Canonical.v]'s [canonicalize]: every
    [Static] process is [⊢]-provably equal, in both directions, to a
    guarded sum that is additionally **canonical** — at most one summand
    per action. This is the form [CompletenessAx.v] consumes; see
    [DefinitionAxiomatic.v]'s [ax_input_distrib_l] comment for why
    completeness needs canonicity and not merely guarded-sum shape. *)

(** ** Normalisation is one-step dominated by the original process

    [normal_form] alone is not enough to drive the [𝛕]-normalisation of
    [VCCS_Canonical.v]: that recursion has to descend into the
    *continuations* of the normal form, and needs them to be smaller
    than the input in some well-founded order. Plain [size] does not
    work — normalisation can *grow* a process (the expansion law turns
    [p ‖ q] into a sum over all interleavings), so continuations of
    [g M] are not subterms of [p] and carry no size bound.

    [step_dominated] supplies what is actually needed, and is strictly
    weaker than a bisimulation: every one-step transition of the normal
    form is matched by a one-step transition of the *original* process,
    with [⊢]-equal targets. Since a matched target is a genuine reduct
    of [p], [Static_lts_decrease] ([VCCS_Static.v]) makes it strictly
    smaller — so the caller can recurse on it by [size] and then
    transport the result back along the [⊢]-equality.

    Only one step is ever needed, which is why no coinduction and no
    bisimulation infrastructure is required. The property composes
    through every case:
    - [‖] — via [expansion_lts_iff] plus [ax_par] to rebuild the
      [⊢]-equalities on both components;
    - [ν] — via [resg_lts_iff] plus [ax_res];
    - [If] — directly from [lts_ifOne]/[lts_ifZero];
    - a guarded sum is already normal, so it matches itself. *)

(** [step_dominated] itself is defined in [VCCS_Canonical.v], which this
    file imports — it is consumed there, by [tau_summand_reduct]. *)

Lemma nf_if_case : forall (e : Equation ValueData) (p1 p2 : proc) M1 M2,
  Static p1 -> Static p2 ->
  gStatic M1 -> ax_pre p1 (g M1) -> ax_pre (g M1) p1 -> step_dominated p1 M1 ->
  gStatic M2 -> ax_pre p2 (g M2) -> ax_pre (g M2) p2 -> step_dominated p2 M2 ->
  exists M, gStatic M /\ ax_pre (If e Then p1 Else p2) (g M)
            /\ ax_pre (g M) (If e Then p1 Else p2)
            /\ step_dominated (If e Then p1 Else p2) M.
Proof.
  intros e p1 p2 M1 M2 Hs1 Hs2 HM1 Hf1 Hb1 Hd1 HM2 Hf2 Hb2 Hd2.
  assert (Hsif : Static (If e Then p1 Else p2)) by (constructor; assumption).
  destruct (Eval_Eq 0 e) as [[|]|] eqn:Heval.
  - exists M1. repeat split; [assumption | | |].
    + eapply ax_trans; [| exact Hf1].
      apply ax_cgr; [exact Hs1 | apply cgr_if_true; exact Heval].
    + eapply ax_trans; [exact Hb1 |].
      apply ax_cgr; [exact Hsif | apply cgr_if_true_rev; exact Heval].
    + intros a q Hl. destruct (Hd1 _ _ Hl) as (r & Hlr & Hqr & Hrq).
      exists r. repeat split; [| exact Hqr | exact Hrq].
      eapply lts_ifOne; [exact Heval | exact Hlr].
  - exists M2. repeat split; [assumption | | |].
    + eapply ax_trans; [| exact Hf2].
      apply ax_cgr; [exact Hs2 | apply cgr_if_false; exact Heval].
    + eapply ax_trans; [exact Hb2 |].
      apply ax_cgr; [exact Hsif | apply cgr_if_false_rev; exact Heval].
    + intros a q Hl. destruct (Hd2 _ _ Hl) as (r & Hlr & Hqr & Hrq).
      exists r. repeat split; [| exact Hqr | exact Hrq].
      eapply lts_ifZero; [exact Heval | exact Hlr].
  - exfalso. eapply Eval_Eq_0_not_none. exact Heval.
Qed.

Lemma nf_par_case : forall (p1 p2 : proc) M1 M2,
  Static p1 -> Static p2 ->
  gStatic M1 -> ax_pre p1 (g M1) -> ax_pre (g M1) p1 -> step_dominated p1 M1 ->
  gStatic M2 -> ax_pre p2 (g M2) -> ax_pre (g M2) p2 -> step_dominated p2 M2 ->
  step_dominated (p1 ‖ p2) ((ext M1 M2 + ext_r M2 M1) + int M1 M2).
Proof.
  intros p1 p2 M1 M2 Hs1 Hs2 HM1 Hf1 Hb1 Hd1 HM2 Hf2 Hb2 Hd2.
  intros a q Hl.
  assert (Hpar : lts (g M1 ‖ g M2) a q).
  { apply expansion_lts_iff. apply lts_choice3_iff in Hl as [H|[H|H]]; auto.
    right. right.
    destruct a; [exfalso; eapply int_no_ext; exact H | split; [reflexivity | exact H]]. }
  clear Hl. inversion Hpar; subst.
  - match goal with HA : lts (g M1) _ _ |- _ => destruct (Hd1 _ _ HA) as (r1 & Hl1 & Hq1 & Hr1) end.
    match goal with HB : lts (g M2) _ _ |- _ => destruct (Hd2 _ _ HB) as (r2 & Hl2 & Hq2 & Hr2) end.
    exists (r1 ‖ r2). repeat split.
    + eapply lts_comL; [exact Hl1 | exact Hl2].
    + apply ax_par; assumption.
    + apply ax_par; assumption.
  - match goal with HA : lts (g M1) _ _ |- _ => destruct (Hd1 _ _ HA) as (r1 & Hl1 & Hq1 & Hr1) end.
    match goal with HB : lts (g M2) _ _ |- _ => destruct (Hd2 _ _ HB) as (r2 & Hl2 & Hq2 & Hr2) end.
    exists (r1 ‖ r2). repeat split.
    + eapply lts_comR; [exact Hl2 | exact Hl1].
    + apply ax_par; assumption.
    + apply ax_par; assumption.
  - match goal with HA : lts (g M1) _ _ |- _ => destruct (Hd1 _ _ HA) as (r1 & Hl1 & Hq1 & Hr1) end.
    exists (r1 ‖ p2). repeat split.
    + apply lts_parL. exact Hl1.
    + apply ax_par; assumption.
    + apply ax_par; assumption.
  - match goal with HB : lts (g M2) _ _ |- _ => destruct (Hd2 _ _ HB) as (r2 & Hl2 & Hq2 & Hr2) end.
    exists (p1 ‖ r2). repeat split.
    + apply lts_parR. exact Hl2.
    + apply ax_par; assumption.
    + apply ax_par; assumption.
Qed.

Theorem normal_form_strong : forall p, Static p ->
  exists M, gStatic M /\ ax_pre p (g M) /\ ax_pre (g M) p /\ step_dominated p M.
Proof.
  induction p as (p & IH) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intro Hsp.
  destruct p; simpl in *.
  - inversion Hsp; subst.
    destruct (IH p1) as (M1 & HM1 & Hf1 & Hb1 & Hd1); [simpl; lia | assumption |].
    destruct (IH p2) as (M2 & HM2 & Hf2 & Hb2 & Hd2); [simpl; lia | assumption |].
    exists ((ext M1 M2 + ext_r M2 M1) + int M1 M2). repeat split.
    + constructor; [constructor; [apply ext_gStatic | apply ext_r_gStatic] | apply int_gStatic]; assumption.
    + eapply ax_trans; [apply ax_par; eassumption | apply ax_expansion_l; assumption].
    + eapply ax_trans; [apply ax_expansion_r; assumption | apply ax_par; eassumption].
    + apply nf_par_case; assumption.
  - inversion Hsp.
  - inversion Hsp.
  - inversion Hsp; subst.
    destruct (IH p1) as (M1 & HM1 & Hf1 & Hb1 & Hd1); [simpl; lia | assumption |].
    destruct (IH p2) as (M2 & HM2 & Hf2 & Hb2 & Hd2); [simpl; lia | assumption |].
    apply nf_if_case with (M1 := M1) (M2 := M2); assumption.
  - inversion Hsp; subst.
    destruct (IH p) as (M0 & HM0 & Hf0 & Hb0 & Hd0); [simpl; lia | assumption |].
    exists (resg M0). repeat split.
    + apply resg_gStatic. assumption.
    + eapply ax_trans; [apply ax_res; eassumption | apply ax_res_normalize_l; assumption].
    + eapply ax_trans; [apply ax_res_normalize_r; assumption | apply ax_res; eassumption].
    + intros a q Hl. apply resg_lts_iff in Hl. inversion Hl; subst.
      * destruct (Hd0 _ _ H1) as (r & Hlr & Hqr & Hrq).
        exists (ν r). repeat split;
          [apply lts_res_ext; exact Hlr | apply ax_res; exact Hqr | apply ax_res; exact Hrq].
      * destruct (Hd0 _ _ H1) as (r & Hlr & Hqr & Hrq).
        exists (ν r). repeat split;
          [apply lts_res_tau; exact Hlr | apply ax_res; exact Hqr | apply ax_res; exact Hrq].
  - inversion Hsp; subst.
    exists g. repeat split; [assumption | apply ax_refl | apply ax_refl |].
    intros a q Hl. exists q. repeat split; [exact Hl | apply ax_refl | apply ax_refl].
Qed.

Theorem canonical_normal_form : forall p, Static p ->
  exists M, gStatic M /\ canonical M /\ ax_pre p (g M) /\ ax_pre (g M) p.
Proof.
  intros p Hp.
  destruct (normal_form p Hp) as (M & HMst & Hf & Hb).
  destruct (canonicalize M HMst) as (M' & HM'st & HM'can & Hf' & Hb').
  exists M'. repeat split; [exact HM'st | exact HM'can | | ].
  - eapply ax_trans; [exact Hf | exact Hf'].
  - eapply ax_trans; [exact Hb' | exact Hb].
Qed.

(** ** The full normal form: Hennessy's [⊕]-of-stable-sums

    [tau_nf M] ([VCCS_Canonical.v]) is the shape the completeness proof
    consumes: a binary tree of internal choices whose leaves are
    [gStable] guarded sums — i.e. [⊕ᵢ (Σ_{a ∈ Aᵢ} a.p(a))], with [𝛕]
    occurring *only* as the internal-choice combinator and never beside
    an external guard. ([VCCS_MixedSumProbes.v] records why mixed sums
    genuinely have to be eliminated rather than reinterpreted.)

    Four stages, each with its own measure, chained here:

    - **0.** [normal_form_strong] — reach a guarded sum at all, *and*
      obtain [step_dominated], which is what makes stage 1 possible.
    - **1.** [tau_normalize_conts] — normalise every [𝛕]-continuation.
      This is the only stage that recurses on the *outer* measure
      ([size p]), via the [Forall tau_cont_norm] hypothesis established
      just below: for each [𝛕]-summand, [tau_summand_reduct] converts
      [step_dominated] into a strictly smaller [Static] reduct [u], the
      outer induction hypothesis normalises [u], and the result
      transports back along [⊢]. Normalisation itself is *not*
      size-decreasing (the expansion law blows terms up), which is
      exactly why the detour through a genuine reduct is needed.
    - **2.** [tau_flatten_all] — collapse nested internal choices, so
      every [𝛕]-continuation becomes [gStable] ([tau_cont_nf] ⟶
      [tau_cont_ok]). Measure: [tau_weight].
    - **3.** [tau_separate] — split mixed sums until only [tau_nf]
      remains. Measure: [ntaus], which decreases *because of* stage 2's
      invariant.

    The stages cannot be merged: stage 3 increases [tau_weight] and
    stage 2 increases the count of outstanding [𝛕]-summands, so no
    lexicographic combination survives both. *)

Theorem full_normalize : forall p, Static p ->
  exists M, gStatic M /\ tau_nf M /\ ax_pre p (g M) /\ ax_pre (g M) p.
Proof.
  induction p as (p & IH) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intro Hsp.
  destruct (normal_form_strong p Hsp) as (M0 & HM0 & Hf0 & Hb0 & Hd0).
  (* Stage 1's hypothesis: every [𝛕]-continuation of [M0] is [⊢]-equal
     to some [tau_nf] guarded sum. This is where [step_dominated] and
     the outer size-recursion meet. *)
  assert (HnormA : Forall tau_cont_norm (summands M0)).
  { apply Forall_forall. intros a Ha.
    destruct a as [ | | c pa | c v pa | pa | N1 N2 ]; try exact I.
    simpl.
    apply elem_of_Permutation in Ha. destruct Ha as (r & Hperm).
    destruct (tau_summand_reduct p M0 pa r Hsp HM0 Hd0 Hperm)
      as (u & Hqu & Huq & Hust & Hsz).
    destruct (IH u Hsz Hust) as (Y & HY & HYnf & Hfu & Hbu).
    exists Y. repeat split; [exact HY | exact HYnf | | ].
    - eapply ax_trans; [exact Hqu | exact Hfu].
    - eapply ax_trans; [exact Hbu | exact Huq]. }
  destruct (tau_normalize_conts (ntodo (summands M0)) M0 HM0 (le_n _) HnormA)
    as (M1 & HM1 & Hnf1 & Hf1 & Hb1).
  destruct (tau_flatten_all (tau_weight (summands M1)) M1 HM1 (le_n _) Hnf1)
    as (M2 & HM2 & Hok2 & Hf2 & Hb2).
  destruct (tau_separate (ntaus (summands M2)) M2 HM2 (le_n _) Hok2)
    as (M3 & HM3 & Hnf3 & Hf3 & Hb3).
  exists M3. repeat split; [exact HM3 | exact Hnf3 | | ].
  - eapply ax_trans; [exact Hf0 |].
    eapply ax_trans; [exact Hf1 |].
    eapply ax_trans; [exact Hf2 | exact Hf3].
  - eapply ax_trans; [exact Hb3 |].
    eapply ax_trans; [exact Hb2 |].
    eapply ax_trans; [exact Hb1 | exact Hb0].
Qed.

End VCCS_NormalForm.
