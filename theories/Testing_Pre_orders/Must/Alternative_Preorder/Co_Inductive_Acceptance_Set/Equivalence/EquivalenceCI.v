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

From TestingTheory Require Import ActTau InputOutputActions gLts Bisimulation Lts_OBA Lts_OBA_FB Lts_FW FiniteImageLTS
            Subset_Act Must Soundness Completeness Equivalence StateTransitionSystems
              Termination WeakTransitions Convergence 
              InteractionBetweenLts MultisetLTSConstruction ForwarderConstruction ParallelLTSConstruction
               Testing_Predicate DefinitionAS DefinitionCI SoundnessCI CompletenessCI MustE Lts_Finite_Output_Chain.



(*
Theorem eqx `{@FiniteImagegLts P A H gLtsP, @FiniteImagegLts Q A H gLtsQ} 
  `{PreAP : @PreExtAction P A H FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP}
  `{PreAQ : @PreExtAction Q A H FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsQ}
  (X : gset P) (q : Q) :
  X ≼ₓ q <-> X ⩽ q.
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

  Context `{@gLtsObaFB P A H gLtsEqP gLtsObaP, !FiniteOutputChain_LtsOba P, !FiniteImagegLts P A}.
  Context `{@gLtsObaFB Q A H gLtsEqQ gLtsObaQ, !FiniteOutputChain_LtsOba Q, !FiniteImagegLts Q A}.
  Context `{@gLtsObaFB T A H gLtsEqT gLtsObaT, !FiniteOutputChain_LtsOba T, !FiniteImagegLts T A, !Testing_Predicate outcome _}.

  Context `{!Prop_of_Inter P T A dual}.
  Context `{!Prop_of_Inter Q T A dual}.

  Context `{!Prop_of_Inter P (mb A) A fw_inter}.
  Context `{!Prop_of_Inter (P * mb A) T A dual}.
  Context `{!Prop_of_Inter Q (mb A) A fw_inter}.
  Context `{!Prop_of_Inter (Q * mb A) T A dual}.

  Context `{@PreExtAction P A H FinA PreA PreA_eq PreA_countable 𝝳 Φ _}.
  Context `{@PreExtAction Q A H FinA PreA PreA_eq PreA_countable 𝝳 Φ _}.
  Context `{@AbsAction A H T FinA _ Φ}.
  Context `{it_conv : @test_convergence_spec T _ _ _ outcome Testing_Predicate0 t_conv}.
  Context `{ita : @test_co_acceptance_set_spec PreA _ _ T _ _ _ outcome Testing_Predicate0 ta (fun x => 𝝳 (Φ x))}.

  Theorem eq_ctx (p : P) (q : Q) :
  pre_extensional outcome p q <-> {[ p ▷ (∅ : mb A)]} ⩽ q ▷ (∅ : mb A).
  Proof.
    rewrite <- eqx, <- alt_set_singleton_iff.
    now rewrite equivalence_bhv_acc_ctx.
  Qed.
End eq_contextual.

*)
