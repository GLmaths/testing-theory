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
From Stdlib Require Import ssreflect.
From Stdlib.Program Require Import Equality.
From TestingTheory Require Import gLts Bisimulation Lts_OBA Lts_FW Lts_OBA_FB StateTransitionSystems Termination
    Must Bar CompletenessAS SoundnessAS Lift Subset_Act FiniteImageLTS WeakTransitions Convergence
    InteractionBetweenLts MultisetLTSConstruction ForwarderConstruction ParallelLTSConstruction ActTau
    Testing_Predicate DefinitionAS MustE.

Section preorder.
  Context `{outcome : T -> Prop}.
  Context `{outcome_dec : forall t, Decision (outcome t)}.
  Context `{P : Type}.
  Context `{Q : Type}.
  Context `{H : !ExtAction A}.

  Context `{@gLtsObaFB P A H gLtsEqP gLtsObaP, !FiniteImagegLts P A}.
  Context `{@gLtsObaFB Q A H gLtsEqQ gLtsObaQ, !FiniteImagegLts Q A}.
  Context `{@gLtsObaFB T A H gLtsEqT gLtsObaT, !FiniteImagegLts T A, !Testing_Predicate outcome _}.

  Context `{!Prop_of_Inter P T A dual}.
  Context `{!Prop_of_Inter Q T A dual}.

  Context `{!Prop_of_Inter P (mb A) A fw_inter}.
  Context `{!Prop_of_Inter (P * mb A) T A dual}.
  Context `{!Prop_of_Inter Q (mb A) A fw_inter}.
  Context `{!Prop_of_Inter (Q * mb A) T A dual}.

  Context `{@PreExtAction P A H FinA PreA PreA_eq PreA_countable 𝝳 Φ _}.
  Context `{@PreExtAction Q A H FinA PreA PreA_eq PreA_countable 𝝳 Φ _}.
  Context `{@AbsAction A H T FinA _ Φ}.
  Context `{tc_spec : @test_convergence_spec T _ _ _ outcome _ t_conv}.
  Context `{ta_spec : @test_co_acceptance_set_spec PreA _ _ T _ _ _ outcome Testing_Predicate0 ta (fun x => 𝝳 (Φ x))}.

  (** * Main equivalence theorems *)
  (** ** The inductive characterisation is equivalent to the extensional must preorder *)
  Theorem equivalence_acc_set_and_must_i (p : P) (q : Q) :
    p ⊑ₘᵤₛₜᵢ q <-> (p, ∅) ≼ₐₛ (q, ∅).
  Proof.
    split.
    - intros hpre. now eapply lift_fw_ctx_pre, completeness_fw in hpre.
    - intros hpre%soundness_fw.
      now eapply lift_fw_ctx_pre.
  Qed.

  (** ---- *)

  (** ** The inductive characterisation is equivalent to the inductive must preorder *)
  Theorem equivalence_bhv_acc_ctx (p : P) (q : Q) :
    pre_extensional outcome p q <-> (p, ∅) ≼ₐₛ (q, ∅).
  Proof.
    rewrite pre_extensional_eq. apply equivalence_acc_set_and_must_i.
  Qed.

End preorder.
