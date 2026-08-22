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
From stdpp Require Import base countable list decidable gmultiset.
From TestingTheory Require Import ActTau gLts Bisimulation Lts_OBA Lts_FW
    WeakTransitions coWeakTransition DefinitionTI DefinitionTIco
    NormalForm Normalisation NormalisationCo.

(** * The may preorders on traces in normal form

    The alternative characterisations of [may] in this development are plain
    trace inclusion ([≼ₜᵢ]) and plain co-trace inclusion ([≼꜀ₒ₋ₜᵢ]): the
    asynchrony is already absorbed by the forwarder lifting of the LTS, so it
    does not have to be absorbed by a preorder on traces, contrary to Boreale,
    De Nicola and Pugliese, whose [≪ₘ] (Definition 3.2) asks for a [≼]-smaller
    trace on the right-hand side.

    Both inclusions only have to be checked on traces in normal form. *)

(** ** Trace inclusion on normalised traces *)

Definition bhv_pre_ti_nf `{gLtsP : @gLts P A H, gLtsQ : !gLts Q H} (p : P) (q : Q) :=
  ∀ σ : ntrace A, traces p (nlin σ) -> traces q (nlin σ).

Notation "p ≼ₙ_ₜᵢ q" := (bhv_pre_ti_nf p q) (at level 70).

Definition bhv_pre_ti_co_nf `{gLtsP : @gLts P A H, gLtsQ : !gLts Q H} (p : P) (q : Q) :=
  ∀ σ : ntrace A, traces_co p (nlin σ) -> traces_co q (nlin σ).

Notation "p ≼ₙ_꜀ₒ₋ₜᵢ q" := (bhv_pre_ti_co_nf p q) (at level 70).

Section OneProcess.

  Context `{H : !ExtAction A}.
  Context `{@gLtsOba P A H gLtsEqP, !gLtsObaFW P A}.

  (** *** Traces *)

  (** Two traces with the same normal form are traces of the same processes. *)
  Lemma traces_of_nform (p : P) s t :
    nform cls_tr s = nform cls_tr t -> traces p s -> traces p t.
  Proof.
    intros heq (p' & w).
    eapply (wt_of_nform p p' s t heq) in w as (p'' & w' & _).
    exists p''. exact w'.
  Qed.

  Corollary traces_norm (p : P) s : traces p s <-> traces p (nlin (nform cls_tr s)).
  Proof.
    split; intro h.
    - eapply traces_of_nform; [| exact h]. symmetry. eapply nform_nlin_nform.
    - eapply traces_of_nform; [| exact h]. eapply nform_nlin_nform.
  Qed.

  (** *** Co-traces *)

  Context (cls : A -> act_class) `{!CoClassifier cls}.

  Lemma traces_co_of_nform (p : P) s t :
    nform cls s = nform cls t -> traces_co p s -> traces_co p t.
  Proof.
    intros heq (p' & w).
    eapply (cowt_of_nform cls p p' s t heq) in w as (p'' & w' & _).
    exists p''. exact w'.
  Qed.

  Corollary traces_co_norm (p : P) s :
    traces_co p s <-> traces_co p (nlin (nform cls s)).
  Proof.
    split; intro h.
    - eapply traces_co_of_nform; [| exact h]. symmetry. eapply nform_nlin_nform.
    - eapply traces_co_of_nform; [| exact h]. eapply nform_nlin_nform.
  Qed.

  (** *** The preorder on traces, read on [may]

      On the may side the preorder has a direct reading: performing a trace
      implies performing every trace above it, in particular the one where a
      feedback has been consumed. *)

  Lemma traces_trace_pre (p : P) s t : s ≼ₜ t -> traces p s -> traces p t.
  Proof. intros hle (p' & w). eapply wt_trace_pre; eassumption. Qed.

  Lemma traces_co_cotrace_pre (p : P) s t : s ≼ᶜᵒₜ t -> traces_co p s -> traces_co p t.
  Proof. intros hle (p' & w). eapply cowt_cotrace_pre; eassumption. Qed.

End OneProcess.

Section MayNormalForm.

  Context `{H : !ExtAction A}.
  Context `{@gLtsOba P A H gLtsEqP, !gLtsObaFW P A}.
  Context `{@gLtsOba Q A H gLtsEqQ, !gLtsObaFW Q A}.

  Theorem bhv_pre_ti_nf_iff (p : P) (q : Q) : p ≼ₙ_ₜᵢ q <-> p ≼ₜᵢ q.
  Proof.
    split.
    - intros hpre s hs.
      eapply (proj2 (traces_norm q s)).
      eapply (hpre (nform cls_tr s)).
      eapply (proj1 (traces_norm p s)), hs.
    - intros hpre σ hs. now eapply hpre.
  Qed.

  Context (cls : A -> act_class) `{!CoClassifier cls}.

  Theorem bhv_pre_ti_co_nf_iff (p : P) (q : Q) : p ≼ₙ_꜀ₒ₋ₜᵢ q <-> p ≼꜀ₒ₋ₜᵢ q.
  Proof.
    split.
    - intros hpre s hs.
      eapply (proj2 (traces_co_norm cls q s)).
      eapply (hpre (nform cls s)).
      eapply (proj1 (traces_co_norm cls p s)), hs.
    - intros hpre σ hs. now eapply hpre.
  Qed.

End MayNormalForm.

(** ** Trace inclusion on simplified traces

    The preorder of [FeedbackNotReversible.v]: like [bhv_pre_ti_nf], it
    quantifies over normalised traces on *both* sides, the difference being
    that the feedbacks have been consumed as well.

    The two readings one may give it coincide -- quantifying over the
    normalised traces on both sides, or over all traces on the left and their
    normal form on the right.  One direction is [wt_fnf], the traces being
    closed under simplification; the other is the idempotence of the normal
    form ([fnf_idem]). *)

Definition bhv_pre_ti_fnf `{gLtsP : @gLts P A H, gLtsQ : !gLts Q H} (p : P) (q : Q) :=
  ∀ s : trace A, traces p (nlin (fnf s)) -> traces q (nlin (fnf s)).

Notation "p ≼ₛ_ₜᵢ q" := (bhv_pre_ti_fnf p q) (at level 70).

Section MaySimplified.

  Context `{H : !ExtAction A}.
  Context `{@gLtsOba P A H gLtsEqP, !gLtsObaFW P A}.
  Context `{@gLtsOba Q A H gLtsEqQ, !gLtsObaFW Q A}.

  Theorem bhv_pre_ti_fnf_iff (p : P) (q : Q) :
    p ≼ₛ_ₜᵢ q <-> (forall s, traces p s -> traces q (nlin (fnf s))).
  Proof.
    split.
    - intros hpre s (r & w). eapply wt_fnf in w as (r' & w' & _).
      eapply hpre. exists r'. exact w'.
    - intros hpre s hs.
      specialize (hpre (nlin (fnf s)) hs). rewrite fnf_idem in hpre. exact hpre.
  Qed.

End MaySimplified.
