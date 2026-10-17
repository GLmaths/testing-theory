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
  coWeakTransition coConvergence Label_Abstraction.LabelAbstraction.
(* begin hide *)
Class AbsActionG (P T : Type) {PreAct A : Type} {H : ExtAction A} (Γ : A → PreAct)
  {Aproc : Type} {Hp : ExtAction Aproc} {gLtsP : gLts P Hp} {gLtsT : gLtsEq T H}
  {SA : SyncAction Aproc A} :=
  abstraction_step (p : P) β β'' :
    blocking β → Γ β = Γ β'' → β'' ∈ coR p → ∃ u, u ∈ coR p ∧ (𝐄 β : subset_of T) ⊆ 𝐄 u.

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

Section Of_label_abstraction.
  Context {P T Ap At : Type} {Hp : ExtAction Ap} {Ht : ExtAction At} {SA : SyncAction Ap At}
    {gLtsP : gLts P Hp} {gLtsT : gLtsEq T Ht}.

  Definition AbsActionG_of_LA (𝔸 : Label_abstraction P T) : AbsActionG P T ρ[𝔸].
  Proof.
    intros p β β'' b e mem.
    apply (LA_class_proj (label_ker 𝔸)) in e.
    apply rel_ker_sub in e as (u & hu & hu''); [| intros μ; exists μ; split; reflexivity].
    exists u. split.
    - exact (coR_reverse_inclusion u β'' hu'' p mem).
    - exact (Ready_set_inclusion β u hu).
  Defined.

  Definition FinitaryAbsActionG_of_FLA (F : Finitary_Label_abstraction P T) :
    FinitaryAbsActionG P T ρ[𝔸 (Finitary_Label_abstraction := F)].
  Proof.
    refine {| FinitaryAbsActionG_Abs := AbsActionG_of_LA _; coR_abs := coRₐ |}.
    - intros p x. apply coRₐ_spec.
    - intros p x. apply coRₐ_spec.
  Defined.
End Of_label_abstraction.

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

Definition bhv_pre_LA_cond2 `{gLtsP : @gLts P Ap Hp} `{gLtsQ : !@gLts Q Ap Hp}
  `{gLtsT : @gLts T At Ht} `{SA : !SyncAction Ap At} (𝔸 : Label_abstraction P T)
  (p : P) (q : Q) :=
  ∀ (s : trace At) q',
    p ⇓ᶜᵒ s → q ⟹ᶜᵒ[s] q' → q' ↛ →
    ∃ p', p ⟹ᶜᵒ[s] p' ∧ p' ↛ ∧ ⌈ ρ[𝔸] ⌉ (coR p') ⊆ ⌈ ρ[𝔸] ⌉ (coR q').

Notation "p ₂≼꜀ₒ₋ₐₛ[ 𝔸 ] q" := (bhv_pre_LA_cond2 𝔸 p q) (at level 70, format "p  ₂≼꜀ₒ₋ₐₛ[ 𝔸 ]  q").

Definition bhv_pre_LA `{gLtsP : @gLts P Ap Hp} `{gLtsQ : !@gLts Q Ap Hp}
  `{gLtsT : @gLts T At Ht} `{SA : !SyncAction Ap At} (𝔸 : Label_abstraction P T)
  (p : P) (q : Q) :=
  bhv_pre_g_cond1 (A := At) p q ∧ p ₂≼꜀ₒ₋ₐₛ[𝔸] q.

Notation "p ≼꜀ₒ₋ₐₛ[ 𝔸 ] q" := (bhv_pre_LA 𝔸 p q) (at level 70, format "p  ≼꜀ₒ₋ₐₛ[ 𝔸 ]  q").

Section Label_abstraction_preorder.
  Context {P Q T Ap At : Type} {Hp : ExtAction Ap} {Ht : ExtAction At} {SA : SyncAction Ap At}
    {gLtsP : gLts P Hp} {gLtsQ : gLts Q Hp} {gLtsT : gLts T Ht}.

  Lemma map_class_subseteq_iff (R : relation At) `{!Equivalence R} `{!RelDecision R}
    (X Y : subset_of At) :
    ⌈ ρ[R] ⌉ X ⊆ ⌈ ρ[R] ⌉ Y ↔ ∀ β, β ∈ X → ∃ β', β' ∈ Y ∧ R β β'.
  Proof.
    split.
    - intros sub β hβ.
      destruct (sub (LA_class R β) (map_gamma_of_action _ _ β hβ)) as (β' & hβ' & e).
      exists β'. split; [exact hβ' | exact (proj1 (LA_class_proj R β β') e)].
    - intros h x (β & hβ & ->). destruct (h β hβ) as (β' & hβ' & hR).
      exists β'. split; [exact hβ' | exact (proj2 (LA_class_proj R β β') hR)].
  Qed.

  Lemma bhv_pre_LA_iff_g (𝔸 : Label_abstraction P T) (p : P) (q : Q) :
    p ≼꜀ₒ₋ₐₛ[𝔸] q ↔ p ≼ᴳ[ ρ[𝔸] ] q.
  Proof. done. Qed.
End Label_abstraction_preorder.
(* end hide *)
