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
    InteractionBetweenLts MultisetLTSConstruction ForwarderConstruction ParallelLTSConstruction ActTau
    Testing_Predicate DefinitionAS MustE.

Section preorder.
  Context `{outcome : T -> Prop}.
  Context `{outcome_dec : forall t, Decision (outcome t)}.
  Context `{P : Type}.
  Context `{Q : Type}.
  Context `{H : !ExtAction A}.
  Context `{gLtsP : !gLts P A, !FiniteImagegLts P A}.
  Context `{gLtsQ : !gLts Q A, !FiniteImagegLts Q A}.
  Context `{gLtsT : !gLts T A, !FiniteImagegLts T A, gLtsEqT: !gLtsEq T A, !Testing_Predicate T A outcome}.
  Context `{@Prop_of_Inter P T A parallel_inter H gLtsP gLtsT}.
  Context `{@Prop_of_Inter Q T A parallel_inter H gLtsQ gLtsT}.

  Context `{@gLtsObaFB P A H gLtsP gLtsEqP gLtsObaP}.
  Context `{@gLtsObaFB Q A H gLtsQ gLtsEqQ gLtsObaQ}.
  Context `{@gLtsObaFB T A H gLtsT gLtsEqT gLtsObaT}.

  Context `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}.
  Context `{@Prop_of_Inter (P * mb A) T A parallel_inter H (inter_lts fw_inter) gLtsT}.
  Context `{@Prop_of_Inter Q (mb A) A fw_inter H gLtsQ MbgLts}.
  Context `{@Prop_of_Inter (Q * mb A) T A parallel_inter H (inter_lts fw_inter) gLtsT}.

  Context `{@PreExtAction A H P FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP}.
  Context `{@PreExtAction A H Q FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsQ}.
  Context `{@AbsAction A H T FinA gLtsT Φ}.
  Context `{it_conv : @test_convergence_spec T _ _ _ _ outcome Testing_Predicate0 t_conv}.
  Context `{ita : @test_co_acceptance_set_spec PreA _ _ T _ _ _ _ outcome Testing_Predicate0 ta (fun x => 𝝳 (Φ x))}.

  (* ************************************************** *)

  (** Equivalence between the extensional definition of the contextual preorder and
      the alternative, inductive characterisation. *)
  Theorem equivalence_bhv_acc_ctx (p : P) (q : Q) :
    @pre_extensional P Q _ _ _ outcome _ p q <-> (p, ∅) ≼ₐₛ (q, ∅).
  Proof.
    split.
    - intros hpre%pre_extensional_eq.
      now eapply lift_fw_ctx_pre, completeness_fw in hpre.
    - intros hpre%soundness_fw.
      now eapply pre_extensional_eq, lift_fw_ctx_pre.
  Qed.

End preorder.