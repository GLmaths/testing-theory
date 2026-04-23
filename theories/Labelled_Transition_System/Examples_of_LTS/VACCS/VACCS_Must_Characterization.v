From stdpp Require Import gmap gmultiset.
From Stdlib.Program Require Import Equality.
From Stdlib.Wellfounded Require Import Inverse_Image.
From TestingTheory Require Import InputOutputActions OldTransitionSystems ActTau .
From TestingTheory Require Export VACCS VACCS.Congruence VACCS_Instance
  VACCS_ta VACCS_tc DefinitionAS Must ForwarderConstruction ParallelLTSConstruction
  InteractionBetweenLts GeneralizeLtsOutputs Completeness Equivalence Soundness
  Testing_Predicate Bisimulation Lts_OBA.


Corollary bhv_iff_ctx_VACCS (p q : proc) : p ⊑ₘᵤₛₜᵢ q <-> p ▷ ∅ ≼ₐₛ q ▷ ∅.
Proof.
  split.
  - intro Hyp. eapply @equivalence_acc_set_and_must_i; eauto.



    exact VACCS_gLtsFiniteImage. exact VACCS_gLtsFiniteImage. exact VACCS_gLtsOBAFB. exact VACCS_gLtsFiniteImage.
    exact Interaction_between_FW_ACCS_and_ACCS. exact Interaction_between_FW_ACCS_and_ACCS.
    exact (@gAbsAction (ExtAct TypeOfActions)).
    (* exact (gen_conv_gen_spec_conv_inst _).*) admit.
    (* exact gen_acc_gen_spec_acc_inst. *) admit.

  - intro Hyp. eapply @equivalence_acc_set_and_must_i in Hyp; eauto.

    exact VACCS_gLtsFiniteImage. exact VACCS_gLtsFiniteImage. exact VACCS_gLtsOBAFB. exact VACCS_gLtsFiniteImage.
    exact Interaction_between_FW_ACCS_and_ACCS. exact Interaction_between_FW_ACCS_and_ACCS.
    exact (@gAbsAction (ExtAct TypeOfActions)).
    (* exact (gen_conv_gen_spec_conv_inst _).*) admit.
    (* exact gen_acc_gen_spec_acc_inst. *) admit.
Admitted.


