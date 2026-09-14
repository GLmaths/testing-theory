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
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base decidable.
From TestingTheory Require Import ActTau gLts Bisimulation Lts_OBA Subset_Act
     WeakTransitions coWeakTransition Termination Convergence coConvergence
     StateTransitionSystems InteractionBetweenLts Testing_Predicate
     NormalForm Normalisation
     DefinitionTI DefinitionTIco DefinitionAS DefinitionASco.

(** * The alternative preorders restricted to the feedback-free traces

    Each of the four alternative preorders of the development quantifies over
    *all* the traces, resp. co-traces, of the processes.  Restricting that
    quantification to the traces that carry no feedback -- [has_fb] of
    [Normalisation.v] -- gives in each case a weaker relation, written with the
    superscript [ⁿᶠᵇ] ("no feedback"):

      [≼ₜᵢⁿᶠᵇ]      [≼꜀ₒ₋ₜᵢⁿᶠᵇ]      [≼ₐₛⁿᶠᵇ]      [≼꜀ₒ₋ₐₛⁿᶠᵇ]

    That the weakening is *strict* -- that none of the four implies its
    unrestricted counterpart -- is what [FeedbackNotReversible.v] proves, with
    one explicit pair of VACCS processes for each. *)

(** ** May, on traces: trace inclusion *)

Definition bhv_pre_ti_nfb `{gLtsP : @gLts P A H, gLtsQ : !gLts Q H} (p : P) (q : Q) :=
  ∀ s : trace A, ¬ has_fb s -> traces p s -> traces q s.

Global Hint Unfold bhv_pre_ti_nfb : mdb.

Notation "p ≼ₜᵢⁿᶠᵇ q" := (bhv_pre_ti_nfb p q) (at level 70).
Notation "p ⋠ₜᵢⁿᶠᵇ q" := (¬ bhv_pre_ti_nfb p q) (at level 70).

(** ** May, on co-traces: co-trace inclusion *)

Definition bhv_pre_ti_co_nfb `{gLtsP : @gLts P A H, gLtsQ : !gLts Q H} (p : P) (q : Q) :=
  ∀ s : trace A, ¬ has_fb s -> traces_co p s -> traces_co q s.

Global Hint Unfold bhv_pre_ti_co_nfb : mdb.

Notation "p ≼꜀ₒ₋ₜᵢⁿᶠᵇ q" := (bhv_pre_ti_co_nfb p q) (at level 70).
Notation "p ⋠꜀ₒ₋ₜᵢⁿᶠᵇ q" := (¬ bhv_pre_ti_co_nfb p q) (at level 70).

(** ** Must, on traces: convergence and acceptance sets *)

Definition bhv_pre_cond1_nfb `{gLts P A, gLts Q A} (p : P) (q : Q) :=
  ∀ s, ¬ has_fb s -> p ⇓ s -> q ⇓ s.

Notation "p ₁≼ₐₛⁿᶠᵇ q" := (bhv_pre_cond1_nfb p q) (at level 70).

Definition bhv_pre_cond2_nfb `{
  gLtsP : @gLts P A H, AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳P _ gLtsT,
  gLtsQ : @gLts Q A H, AbsQT : @AbsAction Q T FinA PreAct A H Φ 𝝳Q _ gLtsT}
  (p : P) (q : Q) :=
  ∀ (s : trace A) q',
    ¬ has_fb s -> p ⇓ s -> q ⟹[s] q' -> q' ↛ ->
    ∃ p', p ⟹[s] p' /\ p' ↛ /\ (⌈ (𝝳P ∘ Φ) ⌉ (coR p') ⊆ ⌈ (𝝳Q ∘ Φ) ⌉ (coR q')).

Notation "p ₂≼ₐₛⁿᶠᵇ q" := (bhv_pre_cond2_nfb p q) (at level 70).

Definition bhv_pre_nfb `{
  gLtsP : @gLts P A H, AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳P _ gLtsT,
  gLtsQ : @gLts Q A H, AbsQT : @AbsAction Q T FinA PreAct A H Φ 𝝳Q _ gLtsT}
  (p : P) (q : Q) :=
  p ₁≼ₐₛⁿᶠᵇ q /\ p ₂≼ₐₛⁿᶠᵇ q.

Notation "p ≼ₐₛⁿᶠᵇ q" := (bhv_pre_nfb p q) (at level 70).

(** ** Must, on co-traces *)

Definition bhv_pre_co_cond1_nfb `{gLts P A, gLts Q A} (p : P) (q : Q) :=
  ∀ s, ¬ has_fb s -> p ⇓ᶜᵒ s -> q ⇓ᶜᵒ s.

Notation "p ₁≼꜀ₒ₋ₐₛⁿᶠᵇ q" := (bhv_pre_co_cond1_nfb p q) (at level 70).

Definition bhv_pre_co_cond2_nfb `{
  gLtsP : @gLts P A H, AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳P _ gLtsT,
  gLtsQ : @gLts Q A H, AbsQT : @AbsAction Q T FinA PreAct A H Φ 𝝳Q _ gLtsT}
  (p : P) (q : Q) :=
  ∀ (s : trace A) q',
    ¬ has_fb s -> p ⇓ᶜᵒ s -> q ⟹ᶜᵒ[s] q' -> q' ↛ ->
    ∃ p', p ⟹ᶜᵒ[s] p' /\ p' ↛ /\ (⌈ (𝝳P ∘ Φ) ⌉ (coR p') ⊆ ⌈ (𝝳Q ∘ Φ) ⌉ (coR q')).

Notation "p ₂≼꜀ₒ₋ₐₛⁿᶠᵇ q" := (bhv_pre_co_cond2_nfb p q) (at level 70).

Definition bhv_pre_co_nfb `{
  gLtsP : @gLts P A H, AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳P _ gLtsT,
  gLtsQ : @gLts Q A H, AbsQT : @AbsAction Q T FinA PreAct A H Φ 𝝳Q _ gLtsT}
  (p : P) (q : Q) :=
  p ₁≼꜀ₒ₋ₐₛⁿᶠᵇ q /\ p ₂≼꜀ₒ₋ₐₛⁿᶠᵇ q.

Notation "p ≼꜀ₒ₋ₐₛⁿᶠᵇ q" := (bhv_pre_co_nfb p q) (at level 70).

(** * The easy direction: restricting can only weaken

    Each unrestricted preorder implies its feedback-free restriction, simply by
    dropping the extra hypothesis.  The converse is what fails, and the four
    counterexamples of [FeedbackNotReversible.v] refute it separately for each
    of the four preorders. *)

Lemma bhv_pre_ti_nfb_of_ti `{gLtsP : @gLts P A H, gLtsQ : !gLts Q H} (p : P) (q : Q) :
  p ≼ₜᵢ q -> p ≼ₜᵢⁿᶠᵇ q.
Proof. intros h s _ hs. eapply h, hs. Qed.

Lemma bhv_pre_ti_co_nfb_of_ti_co `{gLtsP : @gLts P A H, gLtsQ : !gLts Q H} (p : P) (q : Q) :
  p ≼꜀ₒ₋ₜᵢ q -> p ≼꜀ₒ₋ₜᵢⁿᶠᵇ q.
Proof. intros h s _ hs. eapply h, hs. Qed.

Lemma bhv_pre_cond1_nfb_of_cond1 `{gLts P A, gLts Q A} (p : P) (q : Q) :
  p ₁≼ₐₛ q -> p ₁≼ₐₛⁿᶠᵇ q.
Proof. intros h s _ hs. eapply h, hs. Qed.

Lemma bhv_pre_co_cond1_nfb_of_co_cond1 `{gLts P A, gLts Q A} (p : P) (q : Q) :
  p ₁≼꜀ₒ₋ₐₛ q -> p ₁≼꜀ₒ₋ₐₛⁿᶠᵇ q.
Proof. intros h s _ hs. eapply h, hs. Qed.

Section WeakerMust.

  Context `{
    gLtsP : @gLts P A H, AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳P _ gLtsT,
    gLtsQ : @gLts Q A H, AbsQT : @AbsAction Q T FinA PreAct A H Φ 𝝳Q _ gLtsT}.

  Lemma bhv_pre_cond2_nfb_of_cond2 (p : P) (q : Q) : p ₂≼ₐₛ q -> p ₂≼ₐₛⁿᶠᵇ q.
  Proof. intros h s q' _ hc w hst. eapply h; eassumption. Qed.

  Lemma bhv_pre_nfb_of_pre (p : P) (q : Q) : p ≼ₐₛ q -> p ≼ₐₛⁿᶠᵇ q.
  Proof.
    intros (h1 & h2). split;
      [eapply bhv_pre_cond1_nfb_of_cond1, h1 | eapply bhv_pre_cond2_nfb_of_cond2, h2].
  Qed.

  Lemma bhv_pre_co_cond2_nfb_of_co_cond2 (p : P) (q : Q) : p ₂≼꜀ₒ₋ₐₛ q -> p ₂≼꜀ₒ₋ₐₛⁿᶠᵇ q.
  Proof. intros h s q' _ hc w hst. eapply h; eassumption. Qed.

  Lemma bhv_pre_co_nfb_of_pre_co (p : P) (q : Q) : p ≼꜀ₒ₋ₐₛ q -> p ≼꜀ₒ₋ₐₛⁿᶠᵇ q.
  Proof.
    intros (h1 & h2). split;
      [eapply bhv_pre_co_cond1_nfb_of_co_cond1, h1
      | eapply bhv_pre_co_cond2_nfb_of_co_cond2, h2].
  Qed.

End WeakerMust.

(** * The restricted relations are preorders *)

#[global] Instance bhv_pre_ti_nfb_refl `{gLtsP : @gLts P A H} : Reflexive bhv_pre_ti_nfb.
Proof. intros p s _ hs. exact hs. Qed.

#[global] Instance bhv_pre_ti_nfb_transitive `{gLtsP : @gLts P A H} : Transitive bhv_pre_ti_nfb.
Proof. intros p q r hpq hqr s hfb hs. eapply hqr, hpq; eassumption. Qed.

#[global] Instance bhv_pre_ti_nfb_preorder `{gLtsP : @gLts P A H} : PreOrder bhv_pre_ti_nfb.
Proof. split; [exact bhv_pre_ti_nfb_refl | exact bhv_pre_ti_nfb_transitive]. Qed.

#[global] Instance bhv_pre_ti_co_nfb_refl `{gLtsP : @gLts P A H} : Reflexive bhv_pre_ti_co_nfb.
Proof. intros p s _ hs. exact hs. Qed.

#[global] Instance bhv_pre_ti_co_nfb_transitive `{gLtsP : @gLts P A H} :
  Transitive bhv_pre_ti_co_nfb.
Proof. intros p q r hpq hqr s hfb hs. eapply hqr, hpq; eassumption. Qed.

#[global] Instance bhv_pre_ti_co_nfb_preorder `{gLtsP : @gLts P A H} :
  PreOrder bhv_pre_ti_co_nfb.
Proof. split; [exact bhv_pre_ti_co_nfb_refl | exact bhv_pre_ti_co_nfb_transitive]. Qed.
