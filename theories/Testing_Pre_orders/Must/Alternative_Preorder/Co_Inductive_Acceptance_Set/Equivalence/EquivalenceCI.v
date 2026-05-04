(*
   Copyright (c) 2024 Nomadic Labs
   Copyright (c) 2024 Paul Laforgue <paul.laforgue@nomadic-labs.com>
   Copyright (c) 2024 Léo Stefanesco <leo.stefanesco@mpi-sws.org>

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

From Stdlib Require ssreflect.
From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From Stdlib.Program Require Import Equality Wf.
From Stdlib.Wellfounded Require Import Inverse_Image.
From Stdlib Require Import Setoid.
From Stdlib .Logic Require Import ProofIrrelevance.

From stdpp Require Import base countable finite gmap list finite base decidable finite gmap.

From TestingTheory Require Import
  ActTau Subset_Act gLts Bisimulation Lts_OBA Lts_Finite_Output_Chain Lts_OBA_FB Lts_FW FiniteImageLTS
  Termination WeakTransitions Convergence
  InteractionBetweenLts MultisetLTSConstruction ForwarderConstruction ParallelLTSConstruction SetLTSConstruction
  Must MustE Lift Testing_Predicate StateTransitionSystems
  DefinitionAS Soundness Completeness Equivalence
  DefinitionCI SoundnessCI CompletenessCI.

Theorem equivalence_co_inductive_acc_set_and_acc_set `{
  gLtsP : @gLts P A H, !FiniteImagegLts P A, AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳 gLtsP gLtsT,
  gLtsQ : @gLts Q A H, !FiniteImagegLts Q A, AbsQT : @AbsAction Q T FinA PreAct A H Φ 𝝳 gLtsQ gLtsT}
  (X : gset P) (Y : gset Q) :
  X ≼ₛₑₜ_ₐₛ Y <-> X ⩽ Y.
Proof.
  split.
  - eapply copre_if_prex.
  - intros hco. split. now eapply prex1_if_copre. now eapply prex2_if_copre.
Qed.

Section eq_contextual.
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

  Context `{!Prop_of_Inter P (mb A) A fw_inter}.
  Context `{!Prop_of_Inter (P * mb A) T A dual}.
  Context `{!Prop_of_Inter Q (mb A) A fw_inter}.
  Context `{!Prop_of_Inter (Q * mb A) T A dual}.

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

  Theorem equivalence_fw_co_inductive_acc_set_and_must_i (p : P) (q : Q) :
    p ⊑ₘᵤₛₜᵢ q <-> ({[ p ]} : gset P)  ⩽ ({[ q ]} : gset Q).
  Proof.
    split.
    - intros hpre. eapply equivalence_co_inductive_acc_set_and_acc_set.
      eapply alt_set_singleton_iff.
      eapply equivalence_fw_acc_set_and_must_i. exact hpre.
    - intros hpre. eapply equivalence_fw_acc_set_and_must_i.
      eapply alt_set_singleton_iff. eapply equivalence_co_inductive_acc_set_and_acc_set. exact hpre.
  Qed.

  (** ---- *)

  (** ** The inductive characterisation on FW is equivalent to the extensional must preorder *)
  Theorem equivalence_fw_co_inductive_acc_set_and_must (p : P) (q : Q) :
    pre_extensional outcome p q <-> ({[ p ]} : gset P)  ⩽ ({[ q ]} : gset Q).
  Proof.
    rewrite pre_extensional_eq. eapply equivalence_fw_co_inductive_acc_set_and_must_i.
  Qed.

  End FWⁿ.
  (** ---- *)
  Section Lⁿ.

  Context `{!gLtsObaFB P A, !FiniteOutputChain_LtsOba P}.
  Context `{!gLtsObaFB Q A, !FiniteOutputChain_LtsOba Q}.
  Context `{!gLtsObaFB T A, !FiniteOutputChain_LtsOba T}.

  (** ** The inductive characterisation on toFW is equivalent to the inductive must preorder *)
  Theorem equivalence_co_inductive_acc_set_and_must_i (p : P) (q : Q) :
    p ⊑ₘᵤₛₜᵢ q <-> ({[ (p, ∅) ]} : gset (P * mb A)) ⩽ ({[ (q, ∅) ]}  : gset (Q * mb A)).
  Proof.
    split.
    - intros hpre. eapply equivalence_co_inductive_acc_set_and_acc_set.
      eapply alt_set_singleton_iff.
      eapply equivalence_fw_acc_set_and_must_i.
      destruct (lift_fw_ctx_pre p q) as (Hyp1 & Hyp2).
      eapply Hyp1. exact hpre.
    - intros hpre. eapply equivalence_co_inductive_acc_set_and_acc_set in hpre. eapply alt_set_singleton_iff in hpre.
      eapply lift_fw_ctx_pre. eapply equivalence_fw_acc_set_and_must_i;eauto.
  Qed.

  (** ---- *)

  (** ** The inductive characterisation on toFW is equivalent to the extensional must preorder *)
  Theorem equivalence_co_inductive_acc_set_and_must (p : P) (q : Q) :
    pre_extensional outcome p q <-> ({[ (p, ∅) ]} : gset (P * mb A)) ⩽ ({[ (q, ∅) ]}  : gset (Q * mb A)).
  Proof.
    rewrite pre_extensional_eq. apply equivalence_co_inductive_acc_set_and_must_i.
  Qed.

  End Lⁿ.

End eq_contextual.
