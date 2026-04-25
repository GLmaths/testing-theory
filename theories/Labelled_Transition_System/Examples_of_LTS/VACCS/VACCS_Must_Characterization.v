From stdpp Require Import gmap gmultiset.
From Stdlib.Program Require Import Equality.
From Stdlib.Wellfounded Require Import Inverse_Image.
From TestingTheory Require Import InputOutputActions OldTransitionSystems ActTau .
From TestingTheory Require Import
  VACCS_ta_tc_gen DefinitionAS Must ForwarderConstruction ParallelLTSConstruction
  InteractionBetweenLts GeneralizeLtsOutputs Completeness Equivalence Soundness
  Testing_Predicate Bisimulation Lts_OBA.


Module Type VACCS_Must_Alt_Corollary.
Include VACCS_ta_tc.

Corollary bhv_iff_ctx_VACCS (p q : proc) : p ⊑ₘᵤₛₜᵢ q <-> p ▷ ∅ ≼ₐₛ q ▷ ∅.
Proof.
  split.
  - intro Hyp. eapply @equivalence_acc_set_and_must_i; eauto.

    exact VACCS_gLtsFiniteImage. exact VACCS_gLtsFiniteImage. exact VACCS_gLtsFiniteImage.
    exact Interaction_between_FW_VACCS_and_VACCS. exact Interaction_between_FW_VACCS_and_VACCS.
    (* exact gen_conv_gen_spec_conv_inst. *) admit.
    (* exact gen_acc_gen_spec_acc_inst.*) admit.
    exact VACCS_gLtsOBAFB. exact VACCS_gFiniteOutputChain_LtsOba.


  - intro Hyp. eapply @equivalence_acc_set_and_must_i in Hyp; eauto.

    exact VACCS_gLtsFiniteImage. exact VACCS_gLtsFiniteImage. exact VACCS_gLtsFiniteImage.
    exact Interaction_between_FW_VACCS_and_VACCS. exact Interaction_between_FW_VACCS_and_VACCS.
    exact FinitaryAbsVACCS. exact FinitaryAbsVACCS.
    (* exact gen_conv_gen_spec_conv_inst. *) admit.
    (* exact gen_acc_gen_spec_acc_inst.*) admit.
    exact VACCS_gLtsOBAFB. exact VACCS_gFiniteOutputChain_LtsOba.
Admitted.

End VACCS_Must_Alt_Corollary.