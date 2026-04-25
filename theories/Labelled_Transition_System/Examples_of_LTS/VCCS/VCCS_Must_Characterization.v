(*
   Copyright (c) 2024 Gaëtan Lopez <gaetanlopez.maths@gmail.com>

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

From stdpp Require Import gmap gmultiset.
From Stdlib.Program Require Import Equality.
From Stdlib.Strings Require Import String.
From Stdlib Require Import Relations.
From Stdlib.Wellfounded Require Import Inverse_Image.

From TestingTheory Require Import InputOutputActions OldTransitionSystems ActTau .
From TestingTheory Require Export 
  VCCS_ta_tc_gen DefinitionAS Must ForwarderConstruction ParallelLTSConstruction
  InteractionBetweenLts GeneralizeLtsOutputs Completeness Equivalence Soundness
  Testing_Predicate Bisimulation gLts Lts_OBA VCCS_Instance FiniteImageLTS Lts_FW Lts_OBA.


Module Type VCCS_Must_Alt_Corollary.
Include VCCS_ta_tc.

Corollary bhv_iff_ctx_VCCS (p q : proc) : p ⊑ₘᵤₛₜᵢ q <-> p ▷ ∅ ≼ₐₛ q ▷ ∅.
Proof.
  split.
  - intro Hyp. eapply @equivalence_acc_set_and_must_i; eauto.

    exact VCCS_gLtsFiniteImage. exact VCCS_gLtsFiniteImage. exact VCCS_gLtsFiniteImage.
    exact Interaction_between_FW_VCCS_and_VCCS. exact Interaction_between_FW_VCCS_and_VCCS.
    (* exact gen_conv_gen_spec_conv_inst. *) admit.
    (* exact gen_acc_gen_spec_acc_inst.*) admit.
    exact VCCS_gLtsOBAFB. exact VCCS_gFiniteOutputChain_LtsOba.

  - intro Hyp. eapply @equivalence_acc_set_and_must_i in Hyp; eauto.

    exact VCCS_gLtsFiniteImage. exact VCCS_gLtsFiniteImage. exact VCCS_gLtsFiniteImage.
    exact Interaction_between_FW_VCCS_and_VCCS. exact Interaction_between_FW_VCCS_and_VCCS.
    exact FinitaryAbsVCCS. exact FinitaryAbsVCCS.
    (* exact gen_conv_gen_spec_conv_inst. *) admit.
    (* exact gen_acc_gen_spec_acc_inst.*) admit.
     exact VCCS_gLtsOBAFB. exact VCCS_gFiniteOutputChain_LtsOba.
Admitted.

End VCCS_Must_Alt_Corollary.

