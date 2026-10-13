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
From Stdlib Require Import Relations.Relation_Definitions Classes.RelationClasses.
From stdpp Require Import base tactics decidable countable gmap.
From TestingTheory Require Import ActTau gLts SyncActions Subset_Act LabelAbstraction RelationKernel.

Section Admissible.
  Context {P T Aproc A : Type} {Hp : ExtAction Aproc} {H : ExtAction A} {SA : SyncAction Aproc A}
    {gLtsP : gLts P Hp} {gLtsT : gLts T H}.

  Lemma LA_admissible_sub (R R' : relation A) :
    (∀ μ μ', R' μ μ' → R μ μ') → LA_admissible P T R → LA_admissible P T R'.
  Proof. intros hsub adm p β β'' b h mem. exact (adm p β β'' b (hsub β β'' h) mem). Qed.

  Lemma LA_admissible_inter_l (R1 R2 : relation A) :
    LA_admissible P T R1 → LA_admissible P T (λ μ μ', R1 μ μ' ∧ R2 μ μ').
  Proof. apply LA_admissible_sub. by intros μ μ' [h _]. Qed.

  Lemma LA_admissible_inter_r (R1 R2 : relation A) :
    LA_admissible P T R2 → LA_admissible P T (λ μ μ', R1 μ μ' ∧ R2 μ μ').
  Proof. apply LA_admissible_sub. by intros μ μ' [_ h]. Qed.

  Lemma LA_admissible_of_pre (Rt Rp R : relation A) :
    (∀ μ μ', Rt μ μ' → (𝐄 μ : subset_of T) ⊆ 𝐄 μ') →
    (∀ μ μ', Rp μ μ' → (co𝐄 μ' : subset_of P) ⊆ co𝐄 μ) →
    (∀ μ μ', R μ μ' → ∃ u, Rt μ u ∧ Rp u μ') →
    LA_admissible P T R.
  Proof.
    intros ht hp hr p β β'' b h mem.
    destruct (hr β β'' h) as (u & h1 & h2).
    exists u. split; [exact (hp u β'' h2 p mem) | exact (ht β u h1)].
  Qed.
End Admissible.

Section Kernel_admissible.
  Context {P Q T Aproc A : Type} {Hp : ExtAction Aproc} {H : ExtAction A} {SA : SyncAction Aproc A}
    {gLtsP : gLts P Hp} {gLtsQ : gLts Q Hp} {gLtsT : gLts T H}.
  Context (Rt RpP RpQ : relation A) `{!PreOrder Rt, !PreOrder RpP, !PreOrder RpQ}.
  Context (ht : ∀ μ μ', Rt μ μ' → (𝐄 μ : subset_of T) ⊆ 𝐄 μ').

  Lemma LA_K_admissible_l :
    (∀ μ μ', RpP μ μ' → (co𝐄 μ' : subset_of P) ⊆ co𝐄 μ) →
    LA_admissible P T (LA_K Rt RpP RpQ).
  Proof.
    intros hp. apply (LA_admissible_of_pre Rt RpP); [exact ht | exact hp |].
    intros μ μ' h. destruct (proj1 (LA_K_sub Rt RpP RpQ μ μ' h)) as (u & [hu _] & hpu).
    by exists u.
  Qed.

  Lemma LA_K_admissible_r :
    (∀ μ μ', RpQ μ μ' → (co𝐄 μ' : subset_of Q) ⊆ co𝐄 μ) →
    LA_admissible Q T (LA_K Rt RpP RpQ).
  Proof.
    intros hq. apply (LA_admissible_of_pre Rt RpQ); [exact ht | exact hq |].
    intros μ μ' h. destruct (proj2 (LA_K_sub Rt RpP RpQ μ μ' h)) as (u & [hu _] & hqu).
    by exists u.
  Qed.
End Kernel_admissible.

Lemma rel_inter_equivalence {A : Type} (R1 R2 : relation A) `{!Equivalence R1, !Equivalence R2} :
  Equivalence (λ μ μ', R1 μ μ' ∧ R2 μ μ').
Proof.
  split.
  - intros μ. split; reflexivity.
  - intros μ μ' [h1 h2]. split; by symmetry.
  - intros μ μ' μ'' [h1 h2] [h3 h4]. split; by etransitivity.
Qed.

Lemma rel_inter_dec {A : Type} (R1 R2 : relation A) `{!RelDecision R1, !RelDecision R2} :
  RelDecision (λ μ μ', R1 μ μ' ∧ R2 μ μ').
Proof. intros μ μ'. apply _. Defined.

Section Finitary_of_rep.
  Context {P Aproc A : Type} {Hp : ExtAction Aproc} {H : ExtAction A} {SA : SyncAction Aproc A}
    {gLtsP : gLts P Hp} (R : relation A) `{!Equivalence R} `{!RelDecision R}.

  Definition FinitaryLA_of_rep (coR_rep : P → list A)
    (hsub : ∀ p β, β ∈ coR_rep p → β ∈ coR p)
    (hcov : ∀ p β, β ∈ coR p → ∃ x, x ∈ coR_rep p ∧ R β x) : FinitaryLA P R.
  Proof.
    refine {| coR_absR p := list_to_set (LA_class R <$> coR_rep p) |}.
    intros p x. rewrite elem_of_list_to_set, list_elem_of_fmap. split.
    - intros (r & -> & hr). exists r. split; [by apply hsub | reflexivity].
    - intros (β & hβ & <-). destruct (hcov p β hβ) as (r & hr & hR).
      exists r. split; [by apply (LA_class_proj R) | exact hr].
  Defined.
End Finitary_of_rep.
(* end hide *)
