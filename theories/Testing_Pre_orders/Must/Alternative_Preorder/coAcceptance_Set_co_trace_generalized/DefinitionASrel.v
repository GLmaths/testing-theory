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
(* end hide *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib Require Import Relations.Relation_Definitions Classes.RelationClasses.
From stdpp Require Import base tactics decidable countable gmap.
From TestingTheory Require Import ActTau gLts SyncActions Bisimulation Subset_Act
  coWeakTransition coConvergence Label_Abstraction.LabelAbstraction LabelAdmissible.
(* begin hide *)
Class AbsActionG (P T : Type) {PreAct A : Type} {H : ExtAction A} (Γ : A → PreAct)
  {Aproc : Type} {Hp : ExtAction Aproc} {gLtsP : gLts P Hp} {gLtsT : gLtsEq T H}
  {SA : SyncAction Aproc A} :=
  abstraction_step (p : P) β β'' :
    blocking β → Γ β = Γ β'' → β'' ∈ coR p → ∃ u, u ∈ coR p ∧ (𝐏 β : subset_of T) ⊆ 𝐏 u.

Class FinitaryAbsActionG (P T : Type) {PreAct A : Type} {H : ExtAction A} (Γ : A → PreAct)
  {Aproc : Type} {Hp : ExtAction Aproc} {gLtsP : gLts P Hp} {gLtsT : gLtsEq T H}
  {SA : SyncAction Aproc A} `{Countable PreAct} :=
  MkFinitaryAbsActionG {
    FinitaryAbsActionG_Abs :: AbsActionG P T Γ;
    coR_abs : P → gset PreAct;
    coR_abs_spec1 (p : P) (x : PreAct) : x ∈ coR_abs p → x ∈ ⌈ Γ ⌉ (coR p);
    coR_abs_spec2 (p : P) (x : PreAct) : x ∈ ⌈ Γ ⌉ (coR p) → x ∈ coR_abs p;
  }.

Section Abstraction_step.
  Context {P T PreAct Aproc A : Type} {Hp : ExtAction Aproc} {H : ExtAction A}
    {SA : SyncAction Aproc A} {gLtsP : gLts P Hp} {gLtsT : gLtsEq T H}
    (Γ : A → PreAct) `{!AbsActionG P T Γ}.

  Lemma abstraction_step_test (p : P) (t : T) β β'' :
    blocking β → Γ β = Γ β'' → β'' ∈ coR p → t ⟶[β] → ∃ u, u ∈ coR p ∧ t ⟶[u].
  Proof.
    intros b e mem acc. destruct (abstraction_step p β β'' b e mem) as (u & hu & hP).
    exists u. split; [exact hu | exact (hP t acc)].
  Qed.
End Abstraction_step.

Section Of_relation.
  Context {P T Aproc A : Type} {Hp : ExtAction Aproc} {H : ExtAction A} {SA : SyncAction Aproc A}
    {gLtsP : gLts P Hp} {gLtsT : gLtsEq T H}.
  Context (R : relation A) `{!Equivalence R} `{!RelDecision R}.

  Definition AbsActionG_of_LA :
    LA_admissible P T R → AbsActionG P T (LA_class R).
  Proof.
    intros adm p β β'' b e mem.
    exact (adm p β β'' b (proj1 (LA_class_proj R β β'') e) mem).
  Defined.

  Definition FinitaryAbsActionG_of_LA :
    LA_admissible P T R → FinitaryLA P R → FinitaryAbsActionG P T (LA_class R).
  Proof.
    intros adm fin.
    refine {| FinitaryAbsActionG_Abs := AbsActionG_of_LA adm; coR_abs := coR_absR |}.
    - intros p x hx. apply coR_absR_spec in hx as (β & hβ & <-). by exists β.
    - intros p x (β & hβ & ->). apply coR_absR_spec. by exists β.
  Defined.
End Of_relation.

Definition bhv_pre_g_cond1 `{gLtsP : @gLts P Aproc Hp} `{gLtsQ : !@gLts Q Aproc Hp}
  `{Ht : ExtAction A} `{SA : !SyncAction Aproc A}
  (p : P) (q : Q) := ∀ (s : trace A), p ⇓ᶜᵒ s → q ⇓ᶜᵒ s.

Definition bhv_pre_g_cond2 `{gLtsP : @gLts P Aproc Hp} `{gLtsQ : !@gLts Q Aproc Hp}
  `{Ht : ExtAction A} `{SA : !SyncAction Aproc A} {PreAct : Type} (Γ : A → PreAct)
  (p : P) (q : Q) :=
  ∀ (s : trace A) q',
    p ⇓ᶜᵒ s → q ⟹ᶜᵒ[s] q' → q' ↛ →
    ∃ p', p ⟹ᶜᵒ[s] p' ∧ p' ↛ ∧ ⌈ Γ ⌉ (coR p') ⊆ ⌈ Γ ⌉ (coR q').

Definition bhv_pre_g `{gLtsP : @gLts P Aproc Hp} `{gLtsQ : !@gLts Q Aproc Hp}
  `{Ht : ExtAction A} `{SA : !SyncAction Aproc A} {PreAct : Type} (Γ : A → PreAct)
  (p : P) (q : Q) :=
  bhv_pre_g_cond1 (A := A) p q ∧ bhv_pre_g_cond2 Γ p q.

Notation "p ≼ᴳ[ Γ ] q" := (bhv_pre_g Γ p q) (at level 70).

Definition bhv_pre_r_cond2 `{gLtsP : @gLts P Aproc Hp} `{gLtsQ : !@gLts Q Aproc Hp}
  `{Ht : ExtAction A} `{SA : !SyncAction Aproc A} (R : relation A)
  (p : P) (q : Q) :=
  ∀ (s : trace A) q',
    p ⇓ᶜᵒ s → q ⟹ᶜᵒ[s] q' → q' ↛ →
    ∃ p', p ⟹ᶜᵒ[s] p' ∧ p' ↛ ∧ ∀ β, β ∈ coR p' → ∃ β', β' ∈ coR q' ∧ R β β'.

Definition bhv_pre_r `{gLtsP : @gLts P Aproc Hp} `{gLtsQ : !@gLts Q Aproc Hp}
  `{Ht : ExtAction A} `{SA : !SyncAction Aproc A} (R : relation A)
  (p : P) (q : Q) :=
  bhv_pre_g_cond1 (A := A) p q ∧ bhv_pre_r_cond2 R p q.

Notation "p ≼ᴿ[ R ] q" := (bhv_pre_r R p q) (at level 70).

Section Relational.
  Context {P Q Aproc A : Type} {Hp : ExtAction Aproc} {H : ExtAction A} {SA : SyncAction Aproc A}
    {gLtsP : gLts P Hp} {gLtsQ : gLts Q Hp}.
  Context (R : relation A) `{!Equivalence R} `{!RelDecision R}.

  Lemma map_class_subseteq_iff (X Y : subset_of A) :
    ⌈ LA_class R ⌉ X ⊆ ⌈ LA_class R ⌉ Y ↔ ∀ β, β ∈ X → ∃ β', β' ∈ Y ∧ R β β'.
  Proof.
    split.
    - intros sub β hβ.
      destruct (sub (LA_class R β) (map_gamma_of_action _ _ β hβ)) as (β' & hβ' & e).
      exists β'. split; [exact hβ' | exact (proj1 (LA_class_proj R β β') e)].
    - intros h x (β & hβ & ->). destruct (h β hβ) as (β' & hβ' & hR).
      exists β'. split; [exact hβ' | exact (proj2 (LA_class_proj R β β') hR)].
  Qed.

  Lemma bhv_pre_r_iff_g (p : P) (q : Q) : p ≼ᴿ[ R ] q ↔ p ≼ᴳ[ LA_class R ] q.
  Proof.
    split; intros [h1 h2]; split; [exact h1 | | exact h1 |].
    - intros s q' hc w st. destruct (h2 s q' hc w st) as (p' & wp & stp & sub).
      exists p'. split_and!; [exact wp | exact stp |]. by apply map_class_subseteq_iff.
    - intros s q' hc w st. destruct (h2 s q' hc w st) as (p' & wp & stp & sub).
      exists p'. split_and!; [exact wp | exact stp |]. by apply map_class_subseteq_iff.
  Qed.
End Relational.
(* end hide *)
