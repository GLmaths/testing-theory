(* begin hide *)
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
From stdpp Require Import base tactics decidable.
From TestingTheory Require Import ActTau gLts SyncActions Subset_Act InteractionUnion.

Section Sum_LTS.
  Context {P Q A1 A2 : Type} {H1 : ExtAction A1} {H2 : ExtAction A2}
    {gLtsP : gLts P H1} {gLtsQ : gLts Q H2}.

  Definition sum_step (s : P + Q) (𝜆 : Labels (A1 + A2)) (s' : P + Q) : Prop :=
    match s, s' with
    | inl p, inl p' => lift_left_step p 𝜆 p'
    | inr q, inr q' => lift_right_step q 𝜆 q'
    | _, _ => False
    end.

  Definition sum_performs (s : P + Q) (𝜆 : Labels (A1 + A2)) : Prop :=
    match s with
    | inl p => lift_left_performs p 𝜆
    | inr q => lift_right_performs q 𝜆
    end.

  Definition gLts_sum : gLts (P + Q) (@ExtAction_sum A1 A2 H1 H2).
  Proof.
    refine {| lts_step := sum_step; lts_performs := sum_performs |}.
    - intros [p | q] 𝜆 [p' | q']; simpl;
        [apply decide_lift_left_step | apply _ | apply _ | apply decide_lift_right_step].
    - intros [p | q] 𝜆; simpl; [apply decide_lift_left_performs | apply decide_lift_right_performs].
    - intros [p | q] 𝜆 h; simpl in h.
      + destruct (lift_left_performs_spec1 p 𝜆 h) as (p' & tr). by exists (inl p').
      + destruct (lift_right_performs_spec1 q 𝜆 h) as (q' & tr). by exists (inr q').
    - intros [p | q] 𝜆 ([p' | q'] & tr); simpl in *; try done.
      + apply lift_left_performs_spec2. by exists p'.
      + apply lift_right_performs_spec2. by exists q'.
  Defined.

  Context {At : Type} {Ht : ExtAction At} {SA1 : SyncAction A1 At} {SA2 : SyncAction A2 At}.

  Definition sync_sum (a : A1 + A2) (β : At) : Prop :=
    match a with
    | inl a1 => sync a1 β
    | inr a2 => sync a2 β
    end.

  Definition SyncAction_sum : @SyncAction (A1 + A2) At ExtAction_sum Ht.
  Proof. refine {| sync := sync_sum |}. intros [a1 | a2] β; simpl; apply _. Defined.

  #[local] Hint Extern 0 (ExtAction (A1 + A2)) => exact ExtAction_sum : typeclass_instances.
  #[local] Existing Instance gLts_sum.
  #[local] Existing Instance SyncAction_sum.

  Lemma sum_step_inl (p p' : P) (μ : A1) : (inl p : P + Q) ⟶[inl μ : A1 + A2] inl p' ↔ p ⟶[μ] p'.
  Proof. done. Qed.

  Lemma sum_step_inr (q q' : Q) (μ : A2) : (inr q : P + Q) ⟶[inr μ : A1 + A2] inr q' ↔ q ⟶[μ] q'.
  Proof. done. Qed.

  Lemma coR_inl (p : P) (β : At) : β ∈ coR (H := gLts_sum) (SA := SyncAction_sum) (inl p) ↔ β ∈ coR p.
  Proof.
    split.
    - intros ([μ | μ] & acc & hs & b); [by exists μ | done].
    - intros (μ & acc & hs & b). by exists (inl μ).
  Qed.

  Lemma coR_inr (q : Q) (β : At) : β ∈ coR (H := gLts_sum) (SA := SyncAction_sum) (inr q) ↔ β ∈ coR q.
  Proof.
    split.
    - intros ([μ | μ] & acc & hs & b); [done | by exists μ].
    - intros (μ & acc & hs & b). by exists (inr μ).
  Qed.

  Lemma map_coR_inl {PreA : Type} (Γ : At → PreA) (p : P) x :
    x ∈ ⌈ Γ ⌉ (coR (H := gLts_sum) (SA := SyncAction_sum) (inl p)) ↔ x ∈ ⌈ Γ ⌉ (coR p).
  Proof.
    split; intros (β & hβ & ->); exists β; split; [by apply coR_inl | done | by apply coR_inl | done].
  Qed.

  Lemma map_coR_inr {PreA : Type} (Γ : At → PreA) (q : Q) x :
    x ∈ ⌈ Γ ⌉ (coR (H := gLts_sum) (SA := SyncAction_sum) (inr q)) ↔ x ∈ ⌈ Γ ⌉ (coR q).
  Proof.
    split; intros (β & hβ & ->); exists β; split; [by apply coR_inr | done | by apply coR_inr | done].
  Qed.
End Sum_LTS.
(* end hide *)
