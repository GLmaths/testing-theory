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
From Stdlib.Program Require Import Equality Basics.
From stdpp Require Import base countable list decidable finite gmap gmultiset.
From TestingTheory Require Import ActTau gLts Bisimulation Lts_OBA Lts_FW Subset_Act
    WeakTransitions Convergence coWeakTransition coConvergence Termination
    FiniteImageLTS Testing_Predicate StateTransitionSystems InteractionBetweenLts
    DefinitionAS DefinitionASco NormalForm Normalisation NormalisationCo.

(** * The must preorders on traces in normal form

    The alternative characterisations of [must] in this development are based
    on acceptance sets: [≼ₐₛ] on traces ([DefinitionAS.v]) and [≼꜀ₒ₋ₐₛ] on
    co-traces ([DefinitionASco.v]).  Both only have to be checked on traces in
    normal form.

    The counterpart for [may] is in [NormalisationMay.v]. *)

(** ** The alternative preorder restricted to traces in normal form *)

(** Abstracted co-ready-sets are invariant under the bisimulation. *)
Lemma coR_map_preserved_by_eq `{gLtsEq P A} {PreAct : Type} {Γ : A -> PreAct}
  (p p' : P) (x : PreAct) : p ⋍ p' -> x ∈ ⌈ Γ ⌉ (coR p) -> x ∈ ⌈ Γ ⌉ (coR p').
Proof.
  intros heq hmem. destruct hmem as (μ & hmemμ & hx). subst x.
  destruct hmemμ as (μ' & acc & duo & b).
  eapply map_gamma_of_action. exists μ'. repeat split; [| exact duo | exact b].
  eapply accepts_preserved_by_eq; eassumption.
Qed.

(** ** Termination condition, on normalised traces *)
Definition bhv_pre_nf_cond1 `{gLts P A, gLts Q A}
  (p : P) (q : Q) := forall σ : ntrace A, p ⇓ nlin σ -> q ⇓ nlin σ.

Notation "p ₁≼ₙ_ₐₛ q" := (bhv_pre_nf_cond1 p q) (at level 70).

(** ** Smyth preorder on acceptance sets, on normalised traces *)
Definition bhv_pre_nf_cond2 `{
  gLtsP : @gLts P A H, AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳P _ gLtsT,
  gLtsQ : @gLts Q A H, AbsQT : @AbsAction Q T FinA PreAct A H Φ 𝝳Q _ gLtsT}
  (p : P) (q : Q) :=
  forall (σ : ntrace A) q',
    p ⇓ nlin σ -> q ⟹[nlin σ] q' -> q' ↛ ->
    ∃ p', p ⟹[nlin σ] p' /\ p' ↛ /\ (⌈ (𝝳P ∘ Φ) ⌉ (coR p') ⊆ ⌈ (𝝳Q ∘ Φ) ⌉ (coR q')).

Notation "p ₂≼ₙ_ₐₛ q" := (bhv_pre_nf_cond2 p q) (at level 70).

(** ** The alternative preorder on normalised traces *)
Definition bhv_pre_nf `{
  gLtsP : @gLts P A H, AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳P _ gLtsT,
  gLtsQ : @gLts Q A H, AbsQT : @AbsAction Q T FinA PreAct A H Φ 𝝳Q _ gLtsT}
    (p : P) (q : Q) :=
      p ₁≼ₙ_ₐₛ q /\ p ₂≼ₙ_ₐₛ q.

Notation "p ≼ₙ_ₐₛ q" := (bhv_pre_nf p q) (at level 70).

Section Normalised_preorder.

  Context `{H : !ExtAction A}.
  Context `{@gLtsOba P A H gLtsEqP, !gLtsObaFW P A}.
  Context `{@gLtsOba Q A H gLtsEqQ, !gLtsObaFW Q A}.
  Context `{gLtsT : !gLtsEq T H}.
  Context `{@AbsAction P T FinA PreAct A H Φ 𝝳P _ gLtsT}.
  Context `{@AbsAction Q T FinA PreAct A H Φ 𝝳Q _ gLtsT}.

  (** Every trace can be replaced by its normal form. *)
  Lemma bhv_pre_cond1_nf (p : P) (q : Q) : p ₁≼ₙ_ₐₛ q <-> p ₁≼ₐₛ q.
  Proof.
    split.
    - intros hpre s hcnv.
      eapply cnv_norm_rev, (hpre (nform cls_tr s)), cnv_norm, hcnv.
    - intros hpre σ hcnv. now eapply hpre.
  Qed.

  Lemma bhv_pre_cond2_nf (p : P) (q : Q) : p ₂≼ₙ_ₐₛ q <-> p ₂≼ₐₛ q.
  Proof.
    split.
    - intros hpre s q' hcnv w hst.
      eapply wt_norm in w as (q'' & w' & heq'').
      assert (hst'' : q'' ↛) by (eapply stable_preserved_by_eq; [exact hst | now symmetry]).
      destruct (hpre (nform cls_tr s) q'' (cnv_norm p s hcnv) w' hst'')
        as (p'' & w'' & hstp'' & hsub).
      eapply wt_norm_rev in w'' as (p' & w''' & heqp').
      exists p'. repeat split.
      + exact w'''.
      + eapply stable_preserved_by_eq; [exact hstp'' | now symmetry].
      + intros pre_μ hmem.
        eapply (coR_map_preserved_by_eq p' p'' pre_μ heqp') in hmem.
        eapply hsub in hmem.
        eapply (coR_map_preserved_by_eq q'' q' pre_μ heq''), hmem.
    - intros hpre σ q' hcnv w hst. now eapply hpre.
  Qed.

  (** ** The alternative preorder on normalised traces coincides with the
      alternative preorder on traces *)
  Theorem bhv_pre_nf_iff (p : P) (q : Q) : p ≼ₙ_ₐₛ q <-> p ≼ₐₛ q.
  Proof.
    split; intros (h1 & h2); split.
    - now eapply bhv_pre_cond1_nf.
    - now eapply bhv_pre_cond2_nf.
    - now eapply bhv_pre_cond1_nf.
    - now eapply bhv_pre_cond2_nf.
  Qed.

End Normalised_preorder.

(** ** The co-acceptance-set preorder restricted to co-traces in normal form *)

(** ** Termination condition, on normalised co-traces *)
Definition bhv_pre_co_nf_cond1 `{gLts P A, gLts Q A}
  (p : P) (q : Q) := forall σ : ntrace A, p ⇓ᶜᵒ nlin σ -> q ⇓ᶜᵒ nlin σ.

Notation "p ₁≼ₙ_꜀ₒ₋ₐₛ q" := (bhv_pre_co_nf_cond1 p q) (at level 70).

(** ** Smyth preorder on co-acceptance sets, on normalised co-traces *)
Definition bhv_pre_co_nf_cond2 `{
  gLtsP : @gLts P A H, AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳P _ gLtsT,
  gLtsQ : @gLts Q A H, AbsQT : @AbsAction Q T FinA PreAct A H Φ 𝝳Q _ gLtsT}
  (p : P) (q : Q) :=
  forall (σ : ntrace A) q',
    p ⇓ᶜᵒ nlin σ -> q ⟹ᶜᵒ[nlin σ] q' -> q' ↛ ->
    ∃ p', p ⟹ᶜᵒ[nlin σ] p' /\ p' ↛ /\ (⌈ (𝝳P ∘ Φ) ⌉ (coR p') ⊆ ⌈ (𝝳Q ∘ Φ) ⌉ (coR q')).

Notation "p ₂≼ₙ_꜀ₒ₋ₐₛ q" := (bhv_pre_co_nf_cond2 p q) (at level 70).

(** ** The alternative co-preorder on normalised co-traces *)
Definition bhv_pre_co_nf `{
  gLtsP : @gLts P A H, AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳P _ gLtsT,
  gLtsQ : @gLts Q A H, AbsQT : @AbsAction Q T FinA PreAct A H Φ 𝝳Q _ gLtsT}
    (p : P) (q : Q) :=
      p ₁≼ₙ_꜀ₒ₋ₐₛ q /\ p ₂≼ₙ_꜀ₒ₋ₐₛ q.

Notation "p ≼ₙ_꜀ₒ₋ₐₛ q" := (bhv_pre_co_nf p q) (at level 70).

Section Normalised_co_preorder.

  Context `{H : !ExtAction A}.
  Context `{@gLtsOba P A H gLtsEqP, !gLtsObaFW P A}.
  Context `{@gLtsOba Q A H gLtsEqQ, !gLtsObaFW Q A}.
  Context `{gLtsT : !gLtsEq T H}.
  Context `{@AbsAction P T FinA PreAct A H Φ 𝝳P _ gLtsT}.
  Context `{@AbsAction Q T FinA PreAct A H Φ 𝝳Q _ gLtsT}.
  Context (cls : A -> act_class) `{!CoClassifier cls}.

  Lemma bhv_pre_co_cond1_nf (p : P) (q : Q) : p ₁≼ₙ_꜀ₒ₋ₐₛ q <-> p ₁≼꜀ₒ₋ₐₛ q.
  Proof.
    split.
    - intros hpre s hcnv.
      eapply (cocnv_norm_rev cls), (hpre (nform cls s)), (cocnv_norm cls), hcnv.
    - intros hpre σ hcnv. now eapply hpre.
  Qed.

  Lemma bhv_pre_co_cond2_nf (p : P) (q : Q) : p ₂≼ₙ_꜀ₒ₋ₐₛ q <-> p ₂≼꜀ₒ₋ₐₛ q.
  Proof.
    split.
    - intros hpre s q' hcnv w hst.
      eapply (cowt_norm cls) in w as (q'' & w' & heq'').
      assert (hst'' : q'' ↛) by (eapply stable_preserved_by_eq; [exact hst | now symmetry]).
      destruct (hpre (nform cls s) q'' ((cocnv_norm cls) p s hcnv) w' hst'')
        as (p'' & w'' & hstp'' & hsub).
      eapply (cowt_norm_rev cls) in w'' as (p' & w''' & heqp').
      exists p'. repeat split.
      + exact w'''.
      + eapply stable_preserved_by_eq; [exact hstp'' | now symmetry].
      + intros pre_μ hmem.
        eapply (coR_map_preserved_by_eq p' p'' pre_μ heqp') in hmem.
        eapply hsub in hmem.
        eapply (coR_map_preserved_by_eq q'' q' pre_μ heq''), hmem.
    - intros hpre σ q' hcnv w hst. now eapply hpre.
  Qed.

  (** ** The alternative co-preorder on normalised co-traces coincides with the
      alternative co-preorder on co-traces *)
  Theorem bhv_pre_co_nf_iff (p : P) (q : Q) : p ≼ₙ_꜀ₒ₋ₐₛ q <-> p ≼꜀ₒ₋ₐₛ q.
  Proof.
    split; intros (h1 & h2); split.
    - now eapply bhv_pre_co_cond1_nf.
    - now eapply bhv_pre_co_cond2_nf.
    - now eapply bhv_pre_co_cond1_nf.
    - now eapply bhv_pre_co_cond2_nf.
  Qed.

End Normalised_co_preorder.
