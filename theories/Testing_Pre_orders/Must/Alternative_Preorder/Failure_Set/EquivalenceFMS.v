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

From Stdlib Require Import ssreflect.
From Stdlib.Program Require Import Equality.

From stdpp Require Import base decidable gmap finite.

From TestingTheory Require Import ActTau gLts Bisimulation Lts_OBA Subset_Act WeakTransitions Testing_Predicate
    StateTransitionSystems InteractionBetweenLts Convergence Termination FiniteImageLTS
    DefinitionAS DefinitionFMS DefinitionMS EquivalenceMS.


Lemma equivalence_must_set_nfailure `{
  gLtsP : @gLts P A H, !FiniteImagegLts P A, CC : Countable PreAct,
  @FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 _ gLtsEqT _ _}
  (p : P) (s : trace A) h1 (G : gset PreAct) : MUST__s (AFTER p s h1) G <->  ¬ Failure p s G.
Proof.
  split.
  - intros hm (e & hw & hf). eassumption.
    edestruct (hm e) as (β & μ & p' & mem' & hw' & duo & b). eapply wt_set_spec2. eauto. eapply wt_nil.
    edestruct (hf β μ mem' duo b). eauto.
  - intros hnf.
    assert (∀ p0 : P, p0 ∈ AFTER p s h1 → p0 ⇓ []).
    { intros p0 mem0. eapply cnv_nil, cnv_wt_s_terminate; eauto.
      eapply (wt_set_spec1 _ _ _ _ mem0). }
    destruct (either_MUST__s (AFTER p s h1) G) as [Hyp | Hyp]; eauto.
    + eapply nMusts_ex in Hyp as (p0 & mem & hnm).
      * exfalso. eapply hnf.
        eapply nMust_ex in hnm as (p1 & hw1 & hnp).
        exists p1. split.
        eapply wt_push_nil_right.
        eapply (wt_set_spec1 _ _ _ _ mem). eassumption.
        intros β μ mem0 duo b (p' & hw'). eapply hnp. eassumption.
        eassumption. eassumption. eassumption.
        eapply cnv_nil, cnv_wt_s_terminate; eauto.
        eapply (wt_set_spec1 _ _ _ _ mem).
      * eauto.
Qed.

Lemma equivalence_nmust_set_failure `{
  gLtsP : @gLts P A H, !FiniteImagegLts P A, CC : Countable PreAct,
  @FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 _ gLtsEqT _ _}
  (p : P) (s : trace A) h1 (G : gset PreAct) :
  ¬ MUST__s (AFTER p s h1) G
    <-> Failure p s G.
Proof.
  split.
  - intro hm.
    eapply nMusts_ex in hm as (p0 & mem & hnm).
    eapply nMust_ex in hnm as (p1 & hw1 & hnp).
    exists p1. split.
    eapply wt_push_nil_right.
    eapply (wt_set_spec1 _ _ _ _ mem). eassumption.
    intros β μ mem0 duo b (p' & hw'). eapply hnp. eassumption.
    eassumption. eassumption. eassumption.
    eapply cnv_nil, cnv_wt_s_terminate; eauto.
    eapply (wt_set_spec1 _ _ _ _ mem).
    intros p0 mem0. eapply cnv_nil, cnv_wt_s_terminate; eauto.
    eapply (wt_set_spec1 _ _ _ _ mem0).
  - intros (e & hmem & hf) hm. eassumption.
    unfold MUST__s in hm.
    edestruct (hm e) as (β & μ & p1 & mem1 & hw1 & duo & b).
    eapply (wt_set_spec2 _ _ _ _ hmem). eapply wt_nil.
    eapply (hf β μ mem1 duo b). eauto.
Qed.

Theorem equivalence_failure_set_must_set `{ CC : Countable PreAct,
  gLtsP : @gLts P A H, !FiniteImagegLts P A,
  @FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 _ gLtsEqT _ _,
  gLtsQ : @gLts Q A H, !FiniteImagegLts Q A,
  @FinitaryAbsAction Q T FinA PreAct A H Φ 𝝳 _ gLtsEqT _ _
  }
  (p : P) (q : Q) : p ≾ₘᵤₛₜ q <-> p ⋖ꜰᴀɪʟ q.
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


From stdpp Require Import base decidable gmap finite.
From Stdlib Require Import ssreflect.
From Stdlib.Program Require Import Equality.
From TestingTheory Require Import gLts Bisimulation Lts_OBA Lts_FW Lts_OBA_FB StateTransitionSystems Termination
    Must Bar Completeness Soundness Lift Subset_Act FiniteImageLTS WeakTransitions Convergence
    InteractionBetweenLts MultisetLTSConstruction ForwarderConstruction ParallelLTSConstruction ActTau
    Testing_Predicate DefinitionAS MustE Lts_Finite_Output_Chain Equivalence Soundness Completeness.

Section failure_set_preorder.
  Context `{outcome : T -> Prop}.
  Context `{outcome_dec : forall t, Decision (outcome t)}.
  Context `{P : Type}.
  Context `{Q : Type}.
  Context `{H : !ExtAction A}.

  Context `{@gLtsOba P A H gLtsEqP, !FiniteImagegLts P A}.
  Context `{@gLtsOba Q A H gLtsEqQ, !FiniteImagegLts Q A}.
  Context `{@gLtsOba T A H gLtsEqT, !FiniteImagegLts T A, !Testing_Predicate outcome _}.

  Context `{!Prop_of_Inter P T A dual}.
  Context `{!Prop_of_Inter Q T A dual}.

  Context `{!Prop_of_Inter P (MO A) A fw_inter}.
  Context `{!Prop_of_Inter (P * MO A) T A dual}.
  Context `{!Prop_of_Inter Q (MO A) A fw_inter}.
  Context `{!Prop_of_Inter (Q * MO A) T A dual}.


  Context `{CC : Countable PreAct}.
  Context `{@FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 _ _ _ _ }.
  Context `{@FinitaryAbsAction Q T FinA PreAct A H Φ 𝝳 _ _ _ _ }.

  Context `{tc_spec : @test_convergence_spec T _ _ _ outcome _ t_conv}.
  Context `{ta_spec : @test_co_acceptance_set_spec PreAct _ _ T _ _ _ outcome Testing_Predicate0 ta (fun x => 𝝳 (Φ x))}.

  (** * Main equivalence theorems *)

  Section FWⁿ.

  Context `{!gLtsObaFW P A}.
  Context `{!gLtsObaFW Q A}.
  Context `{!gLtsObaFB T A}.

  (** ** The failure divergence refinement is equivalent to the extensional must preorder on FWⁿ*)
  Corollary equivalence_fw_failure_set_and_must_e (p : P) (q : Q) :
    p ⋖ꜰᴀɪʟ q <-> pre_extensional outcome p q.
  Proof.
    erewrite<- equivalence_failure_set_must_set.
    rewrite equivalence_fw_must_set_and_must_e;eauto.
  Qed.

  (** ** The failure divergence refinement is equivalent to the inductive must preorder on FWⁿ*)
  Corollary equivalence_fw_failure_set_and_must_i (p : P) (q : Q) :
     p ⋖ꜰᴀɪʟ q <-> p ⊑ₘᵤₛₜᵢ q .
  Proof.
    erewrite<- equivalence_failure_set_must_set.
    rewrite equivalence_fw_must_set_and_must_i;eauto.
  Qed.

  End FWⁿ.
  (** ---- *)
  Section Lⁿ.

  Context `{!gLtsObaFB P A, !FiniteOutputChain_LtsOba P}.
  Context `{!gLtsObaFB Q A, !FiniteOutputChain_LtsOba Q}.
  Context `{!gLtsObaFB T A, !FiniteOutputChain_LtsOba T}.

  (** ** The failure divergence refinement is equivalent to the inductive must preorder *)
  Corollary equivalence_failure_set_and_must_i (p : P) (q : Q) :
    p ⊑ₘᵤₛₜᵢ q <-> (p, ∅) ⋖ꜰᴀɪʟ (q, ∅).
  Proof.
    erewrite<- equivalence_failure_set_must_set.
    rewrite equivalence_must_set_and_must_i; eauto.
  Qed.

  (** ---- *)

  (** ** The failure divergence refinement is equivalent to the extensional must preorder *)
  Corollary equivalence_failure_set_and_must_e (p : P) (q : Q) :
    pre_extensional outcome p q <-> (p, ∅) ⋖ꜰᴀɪʟ (q, ∅).
  Proof.
    rewrite pre_extensional_eq. apply equivalence_failure_set_and_must_i.
  Qed.

  End Lⁿ.

End failure_set_preorder.

