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

Require ssreflect.
Require Import Coq.Unicode.Utf8.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Program.Equality.
Require Import Coq.Wellfounded.Inverse_Image.
Require Import Coq.Logic.JMeq.
Require Import Coq.Program.Wf Setoid.
Require Import Coq.Program.Equality.
From Coq.Logic Require Import ProofIrrelevance.
From stdpp Require Import base countable finite gmap list finite base decidable finite gmap.
From Must Require Import gLts Lts_OBA_FB FiniteImageLTS
            Must SoundnessAS CompletenessAS EquivalenceAS StateTransitionSystems
              Termination WeakTransitions Convergence  
               InteractionBetweenLts MultisetLTSConstruction ForwarderConstruction ParallelLTSConstruction
               Testing_Predicate DefinitionAS DefinitionCI SoundnessCI CompletenessCI MustE.

Theorem eqx `{@FiniteImagegLts A L HL LtsP, @FiniteImagegLts B L HL LtsQ} 
  `{PreAP : @PreExtAction L HL A FinA PreA PreA_eq PreA_countable 𝝳 Φ LtsP}
  `{PreAQ : @PreExtAction L HL B FinA PreA PreA_eq PreA_countable 𝝳 Φ LtsQ}
  (X : gset A) (q : B) :
  X ≼ₓ q <-> X ⩽ q.
Proof.
  split.
  - eapply copre_if_prex.
  - intros hco. split. now eapply prex1_if_copre. now eapply prex2_if_copre.
Qed.

Section eq_contextual.

  Context `{H : ExtAction A}.
  Context `{gLtsP : !gLts P A, !FiniteImagegLts P A}.
  Context `{gLtsQ : !gLts Q A, !FiniteImagegLts Q A}.
  Context `{gLtsT : !gLts T A, !FiniteImagegLts T A}.

  Context `{@gLtsObaFB P A H gLtsP gLtsEqP gLtsObaP}.
  Context `{@gLtsObaFB Q A H gLtsQ gLtsEqQ gLtsObaQ}.
  Context `{@gLtsObaFB T A H gLtsT gLtsEqT gLtsObaT}.

  Context `{outcome : T -> Prop}.
  Context `{outcome_dec : forall t, Decision (outcome t)}.
  Context `{TA_instance : !Testing_Predicate T A outcome}.

  (* ************************************************** *)
  Context `{@Prop_of_Inter P T A parallel_inter H gLtsP gLtsT}.
  Context `{@Prop_of_Inter Q T A parallel_inter H gLtsQ gLtsT}.
  Context `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}.
  Context `{@Prop_of_Inter (P * mb A) T A parallel_inter H (inter_lts fw_inter) gLtsT}.
  Context `{@Prop_of_Inter Q (mb A) A fw_inter H gLtsQ MbgLts}.
  Context `{@Prop_of_Inter (Q * mb A) T A parallel_inter H (inter_lts fw_inter) gLtsT}.

  Context `{@PreExtAction A H P FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP}.
  Context `{@PreExtAction A H Q FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsQ}.
  Context `{@AbsAction A H T FinA gLtsT Φ}.

  Context `{igen_conv : @test_convergence_spec T _ _ _ _ outcome TA_instance gen_conv}.
  Context `{igen_acc : @test_co_acceptance_set_spec PreA _ _ T _ _ _ _ outcome TA_instance gen_acc (fun x => 𝝳 (Φ x))}.

  Theorem eq_ctx (p : P) (q : Q) :
    @pre_extensional P Q _ _ _ outcome _ p q <-> {[ p ▷ (∅ : mb A) ]} ⩽ q ▷ (∅ : mb A).
  Proof.
    rewrite <- eqx, <- alt_set_singleton_iff.
    now rewrite equivalence_bhv_acc_ctx.
  Qed.
End eq_contextual.
