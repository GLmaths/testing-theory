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
From Must Require Import ActTau InputOutputActions gLts Bisimulation Lts_OBA Lts_OBA_FB Lts_FW FiniteImageLTS
            Subset_Act Must SoundnessAS CompletenessAS EquivalenceAS StateTransitionSystems
              GeneralizeLtsOutputs Termination WeakTransitions Convergence  
               InteractionBetweenLts MultisetLTSConstruction ForwarderConstruction ParallelLTSConstruction
               Testing_Predicate DefinitionAS DefinitionCI SoundnessCI CompletenessCI.

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
  Context `{gLtsE : !gLts E A, !FiniteImagegLts E A}.

  Context `{@gLtsObaFB P A H gLtsP gLtsEqP gLtsObaP}.
  Context `{@gLtsObaFB Q A H gLtsQ gLtsEqQ gLtsObaQ}.
  Context `{@gLtsObaFB E A H gLtsE gLtsEqE gLtsObaE}.

  Context `{attaboy : E -> Prop}.
  Context `{attaboy_dec : forall e, Decision (attaboy e)}.
  Context `{!Testing_Predicate E A attaboy}.

  (* ************************************************** *)
  Context `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}.
  Context `{@Prop_of_Inter Q E A parallel_inter H gLtsQ gLtsE}.
  Context `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}.
  Context `{@Prop_of_Inter (P * mb A) E A parallel_inter H (inter_lts fw_inter) gLtsE}.
  Context `{@Prop_of_Inter Q (mb A) A fw_inter H gLtsQ MbgLts}.
  Context `{@Prop_of_Inter (Q * mb A) E A parallel_inter H (inter_lts fw_inter) gLtsE}.

  Context `{@PreExtAction A H (P * mb A) FinA PreA PreA_eq PreA_countable 𝝳 Φ (FW_gLts gLtsP)}.
  Context `{@PreExtAction A H (Q * mb A) FinA PreA PreA_eq PreA_countable 𝝳 Φ (FW_gLts gLtsQ)}.
  Context `{@AbsAction A H E FinA gLtsE Φ}.

  Context `{igen_conv : @gen_spec_conv E _ _ _ _ attaboy Testing_Predicate0 co_of gen_conv}.
  Context `{igen_acc : @gen_spec_acc PreA _ _ E _ _ _ _ attaboy Testing_Predicate0 co_of gen_acc (fun x => 𝝳 (Φ x))}.

  Theorem eq_ctx (p : P) (q : Q) :
    @pre_extensional P Q _ _ _ attaboy _ p q <-> {[ p ▷ (∅ : mb A) ]} ⩽ q ▷ (∅ : mb A).
  Proof.
    rewrite <- eqx, <- alt_set_singleton_iff.
    now rewrite equivalence_bhv_acc_ctx.
  Qed.
End eq_contextual.
