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
From Stdlib Require Import PeanoNat Lia.
From TestingTheory Require Import VCCS VCCS_Instance Must VCCS_Static
  VCCS_Expansion VCCS_ResNormalize VCCS_Precongruence DefinitionAxiomatic.

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

End VCCS_NormalForm.
