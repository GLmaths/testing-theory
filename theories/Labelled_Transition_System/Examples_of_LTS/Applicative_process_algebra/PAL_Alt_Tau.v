(*
   Copyright (c) 2026 Gaëtan Lopez <glopez@irif.fr>

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

From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base tactics countable.
From TestingTheory Require Import ActTau InputOutputActions PAL_Syntax
  Applicative_process_algebra PAL_Alt_LTS.

(* * The alternative LTS of PAL has the τ-transitions of PAL

   [Applicative_process_algebra.lts_step] labels an input with the received
   tuple only; [PAL_Alt_LTS.lts_step_a] also records the template of the
   pattern. Outputs have the same labels in both. *)

Section PAL_Alt_Tau.
  Context (Val : Type) `{Countable Val}.

  Notation old := (Applicative_process_algebra.lts_step Val).
  Notation new := (lts_step_a Val).

  (** From the new LTS to the old one: forget the templates. *)
  Lemma new_old p α q :
    new p α q →
    match α with
    | τ => old p τ q
    | ActExt (AIn _ l) => old p (ActExt (ActIn (ltuple Val l))) q
    | ActExt (AOut _ ot) => old p (ActExt (ActOut ot)) q
    end.
  Proof.
    induction 1; simpl in *.
    - eapply ar1; [eassumption | by apply template_tuple_match].
    - eapply ar2; [eassumption | by apply template_tuple_match].
    - by apply ar3.
    - destruct mu; by eapply ar4_l.
    - destruct mu; by eapply ar4_r.
    - destruct mu; by eapply ar5_l.
    - destruct mu; by eapply ar5_r.
    - destruct mu; by eapply ar6.
    - destruct mu; by eapply ar7.
    - destruct mu; by eapply ar8.
    - apply ir1.
    - apply ir2.
    - by eapply ir3.
    - by eapply ir4.
    - by apply ir5.
    - apply ir6.
    - apply ir7_l.
    - apply ir7_r.
    - by apply ir8_l.
    - by apply ir8_r.
    - by apply ir9_l.
    - by apply ir9_r.
    - by apply ir10_l.
    - by apply ir10_r.
    - by apply ir11.
    - destruct mu1 as [l1|a1], mu2 as [l2|a2]; simpl in *; try contradiction; subst.
      + by eapply (ir12 _ _ _ (ActIn (ltuple Val l1))).
      + by eapply (ir12 _ _ _ (ActOut (ltuple Val l2))).
    - destruct mu1 as [l1|a1], mu2 as [l2|a2]; simpl in *; try contradiction; subst.
      + by eapply (ir13 _ _ _ (ActIn (ltuple Val l1))).
      + by eapply (ir13 _ _ _ (ActOut (ltuple Val l2))).
  Qed.

  (** From the old LTS to the new one: an input gains the template of its pattern. *)
  Lemma old_new p α q :
    old p α q →
    match α with
    | τ => new p τ q
    | ActExt (ActIn ot) => ∃ l, ltuple Val l = ot ∧ new p (ActExt (AIn _ l)) q
    | ActExt (ActOut ot) => new p (ActExt (AOut _ ot)) q
    end.
  Proof.
    induction 1; simpl in *.
    - match goal with hm : tuple_match ?it ?ot |- _ =>
        destruct (label_of_spec Val it ot hm) as [ht ho];
        exists (label_of Val it ot); split; [exact ho |];
        rewrite <- ho at 2; apply aar1; [done | by rewrite ht] end.
    - match goal with hm : tuple_match ?it ?ot |- _ =>
        destruct (label_of_spec Val it ot hm) as [ht ho];
        exists (label_of Val it ot); split; [exact ho |];
        rewrite <- ho at 2 3; apply aar2; [done | by rewrite ht] end.
    - by apply aar3.
    - destruct mu; simpl in *; [destruct IHlts_step as (l & hl & h'); exists l; split; [done |] |]; by eapply aar4_l.
    - destruct mu; simpl in *; [destruct IHlts_step as (l & hl & h'); exists l; split; [done |] |]; by eapply aar4_r.
    - destruct mu; simpl in *; [destruct IHlts_step as (l & hl & h'); exists l; split; [done |] |]; by eapply aar5_l.
    - destruct mu; simpl in *; [destruct IHlts_step as (l & hl & h'); exists l; split; [done |] |]; by eapply aar5_r.
    - destruct mu; simpl in *; [destruct IHlts_step as (l & hl & h'); exists l; split; [done |] |]; by eapply aar6.
    - destruct mu; simpl in *; [destruct IHlts_step as (l & hl & h'); exists l; split; [done |] |]; by eapply aar7.
    - destruct mu; simpl in *; [destruct IHlts_step as (l & hl & h'); exists l; split; [done |] |]; by eapply aar8.
    - apply air1.
    - apply air2.
    - by eapply air3.
    - by eapply air4.
    - by apply air5.
    - apply air6.
    - apply air7_l.
    - apply air7_r.
    - by apply air8_l.
    - by apply air8_r.
    - by apply air9_l.
    - by apply air9_r.
    - by apply air10_l.
    - by apply air10_r.
    - by apply air11.
    - destruct mu as [ot|ot]; simpl in *.
      + destruct IHlts_step1 as (l & hl & h1'). eapply air12; [exact h1' | exact IHlts_step2 | exact hl].
      + destruct IHlts_step2 as (l & hl & h2'). eapply air12; [exact IHlts_step1 | exact h2' | exact hl].
    - destruct mu as [ot|ot]; simpl in *.
      + destruct IHlts_step1 as (l & hl & h1'). eapply air13; [exact h1' | exact IHlts_step2 | exact hl].
      + destruct IHlts_step2 as (l & hl & h2'). eapply air13; [exact IHlts_step1 | exact h2' | exact hl].
  Qed.

  (** The τ-transitions coincide. *)
  Theorem tau_iff p q : new p τ q ↔ old p τ q.
  Proof. split; [apply (new_old p τ q) | apply (old_new p τ q)]. Qed.

  (** Visible transitions: inputs refine the labels of the old LTS, outputs are unchanged. *)
  Lemma in_iff p ot q : (∃ l, ltuple Val l = ot ∧ new p (ActExt (AIn _ l)) q) ↔ old p (ActExt (ActIn ot)) q.
  Proof.
    split.
    - intros (l & <- & h). exact (new_old _ (ActExt (AIn _ l)) _ h).
    - apply (old_new p (ActExt (ActIn ot)) q).
  Qed.

  Lemma out_iff p ot q : new p (ActExt (AOut _ ot)) q ↔ old p (ActExt (ActOut ot)) q.
  Proof. split; [apply (new_old p (ActExt (AOut _ ot)) q) | apply (old_new p (ActExt (ActOut ot)) q)]. Qed.
End PAL_Alt_Tau.
