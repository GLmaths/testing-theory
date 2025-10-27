(*
   Copyright (c) 2024 Nomadic Labs
   Copyright (c) 2024 Paul Laforgue <paul.laforgue@nomadic-labs.com>
   Copyright (c) 2024 Léo Stefanesco <leo.stefanesco@mpi-sws.org>
   Copyright (c) 2025 Gaëtan Lopez <glopez@irif.fr>

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

From stdpp Require Import base decidable gmap finite.
From Coq Require Import ssreflect.
From Coq.Program Require Import Equality.
From Must Require Import gLts Bisimulation Lts_OBA Lts_FW Lts_OBA_FB StateTransitionSystems Termination
    Must Bar CompletenessAS SoundnessAS Lift Subset_Act FiniteImageLTS WeakTransitions Convergence
    InteractionBetweenLts MultisetLTSConstruction ForwarderConstruction  ParallelLTSConstruction ActTau
    Testing_Predicate DefinitionAS DefinitionMS DefinitionFMS EquivalenceMS.

Section failure_must_set.

  Context `{P : Type}.
  Context `{Q : Type}.
  Context `{A : Type}.
  Context `{H : !ExtAction A}.
  Context `{gLtsP : !gLts P A, !FiniteImagegLts P A}.
  Context `{gLtsQ : !gLts Q A, !FiniteImagegLts Q A}.

  Context `{@gLtsObaFB P A H gLtsP gLtsEqP gLtsObaP}.
  Context `{@gLtsObaFB Q A H gLtsQ gLtsEqQ gLtsObaQ}.

  Context `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}.
  Context `{@Prop_of_Inter Q (mb A) A fw_inter H gLtsQ MbgLts}.

  Lemma equivalence_must_set_nfailure
    (p : P) (s : trace A) h1 (G : gset A) :
    MUST__s (AFTER (p, ∅) s h1) G
      <-> ¬ Failure (p, ∅) s G.
  Proof.
    split.
    - intros hm (e & hw & hf). eassumption.
      edestruct (hm e) as (μ & p' & mem' & hw'). eapply wt_set_spec2. eauto. eapply wt_nil.
      edestruct (hf μ mem'). eauto.
    - intros hnf.
      assert (∀ p0 : P * mb A, p0 ∈ AFTER (p ▷ ∅) s h1 → p0 ⇓ []).
      intros p0 mem0. eapply cnv_nil, cnv_wt_s_terminate; eauto.
      eapply (wt_set_spec1 _ _ _ _ mem0).
      destruct (either_MUST__s (AFTER (p, ∅) s h1) G) as [Hyp | Hyp]; eauto.
      + eapply nMusts_ex in Hyp as (p0 & mem & hnm).
        exfalso. eapply hnf.
        eapply nMust_ex in hnm as (p1 & hw1 & hnp).
        exists p1. split.
        eapply wt_push_nil_right.
        eapply (wt_set_spec1 _ _ _ _ mem). eassumption.
        intros μ mem0 (p' & hw'). eapply hnp. eassumption.
        eassumption.
        eapply cnv_nil, cnv_wt_s_terminate; eauto.
        eapply (wt_set_spec1 _ _ _ _ mem). eauto.
  Qed.

  Lemma equivalence_nmust_set_failure
    (p : P) (s : trace A) h1 (G : gset A) :
    ¬ MUST__s (AFTER (p ▷ ∅) s h1) G
      <-> Failure (p ▷ ∅) s G.
  Proof.
    split.
    - intro hm.
      eapply nMusts_ex in hm as (p0 & mem & hnm).
      eapply nMust_ex in hnm as (p1 & hw1 & hnp).
      exists p1. split.
      eapply wt_push_nil_right.
      eapply (wt_set_spec1 _ _ _ _ mem). eassumption.
      intros μ mem0 (p' & hw'). eapply hnp. eassumption.
      eassumption.
      eapply cnv_nil, cnv_wt_s_terminate; eauto.
      eapply (wt_set_spec1 _ _ _ _ mem).
      intros p0 mem0. eapply cnv_nil, cnv_wt_s_terminate; eauto.
      eapply (wt_set_spec1 _ _ _ _ mem0).
    - intros (e & hmem & hf) hm. eassumption.
      unfold MUST__s in hm.
      unfold MUST in hm.
      edestruct (hm e) as (μ & p1 & mem1 & hw1).
      eapply (wt_set_spec2 _ _ _ _ hmem). eapply wt_nil.
      eapply (hf μ mem1). eauto.
  Qed.

End failure_must_set.

Section failure_must_set_pre.
  Context `{P : Type}.
  Context `{Q : Type}.
  Context `{A : Type}.
  Context `{H : !ExtAction A}.
  Context `{gLtsP : !gLts P A, !FiniteImagegLts P A}.
  Context `{gLtsQ : !gLts Q A, !FiniteImagegLts Q A}.

  Context `{@gLtsObaFB P A H gLtsP gLtsEqP gLtsObaP}.
  Context `{@gLtsObaFB Q A H gLtsQ gLtsEqQ gLtsObaQ}.

  Context `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}.
  Context `{@Prop_of_Inter Q (mb A) A fw_inter H gLtsQ MbgLts}.

  Theorem equivalence_pre_failure_must_set

  (p : P) (q : Q) : (p ▷ ∅) ≾ (q ▷ ∅) <-> (p ▷ ∅) ⋖ (q ▷ ∅).
  Proof.
    split.
    - intros (hpre1 & hpre2). split.
      + exact hpre1.
      + intros s G hf hcnv.
        eapply (equivalence_nmust_set_failure p s hcnv).
        intros hm. eapply (hpre2 s hcnv (hpre1 s hcnv)) in hm.
        eapply (equivalence_must_set_nfailure q s (hpre1 s hcnv) G) in hm. contradiction. eassumption.
    - intros (hpre1 & hpre2). split. 
      + exact hpre1. 
      + intros s h1 h2 G hm%equivalence_must_set_nfailure.
        eapply (equivalence_must_set_nfailure q).
        intros hf%hpre2. contradiction.
  Qed.

End failure_must_set_pre.

