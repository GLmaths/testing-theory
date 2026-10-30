(* begin hide *)
From Stdlib Require Import Lia.
From stdpp Require Import sets gmap gmultiset countable numbers list.
From TestingTheory Require Import VACCS.Testing.ta_tc_gen DefinitionAS Equivalence Must Lift
  ParallelLTSConstruction InteractionBetweenLts Bisimulation
  ActTau InputOutputActions Convergence InListPropHelper
  gLts Lts_OBA FiniteImageLTS Testing_Predicate Completeness Lts_FW Lts_OBA_FB MultisetLTSConstruction
  SetLTSConstruction ForwarderConstruction.
From TestingTheory Require Import coFiniteImage coConvergence coWeakTransition DefinitionASrel
  CompletenessASco EquivalenceASco TestSpecBridge SyncActions
  VACCS.Language.LTS VACCS.Language.gLts_Instance VACCS.Language.Label_Abstraction
  VACCS.Characterisations.Must_Characterisation VACCS.Helper.Atom_Swap
  Label_Abstraction.LabelAbstraction Label_Abstraction.Decidable_dichotomic Subset_Act
  Decision.Tools_in_construction.Inductive.Generic.Helpers Decision.Tools_in_construction.Inductive.Generic.Acceptance_Tests_Gamma
  Decision.Tools_in_construction.Inductive.VACCS.Tests Decision.Tools_in_construction.Inductive.Generic.Interface Decision.Tools_in_construction.Inductive.Generic.Sets Decision.Tools_in_construction.Inductive.Generic.Graph Decision.Tools_in_construction.Inductive.Generic.Swaps Decision.Tools_in_construction.Inductive.Generic.Adequacy Decision.Tools_in_construction.Inductive.Generic.Verdict Decision.Tools_in_construction.Inductive.Generic.Forwarders
  Decision.Tools_in_construction.Inductive.VACCS.Instance.
Import ListNotations.


Section Examples.

#[local] Instance VACCS_nat : VACCS_Parameters := {| Channel := nat; Value := nat; O := 0 |}.

Definition p1 : proc := cst 0 ! cst 0 • 𝟘.
Definition q1 : proc := g ((𝛕 • (cst 0 ! cst 0 • 𝟘)) + (𝛕 • g 𝟘)).

Example p1_q1_verdict : ∃ s t, vaccs_verdict (VP := VACCS_nat) 0 5 1 p1 q1 = R_fails s t.
Proof. vm_compute. eexists _, _. reflexivity. Qed.

Lemma p1_not_below_q1 : p1 ⋢ₘᵤₛₜᵢ q1.
Proof. destruct p1_q1_verdict as (s & t & e). exact (vaccs_verdict_refutes _ _ _ _ _ _ _ e). Qed.

Example q1_p1_verdict : vaccs_verdict (VP := VACCS_nat) 0 5 1 q1 p1 = R_unknown.
Proof. vm_compute. reflexivity. Qed.

Definition p3 : proc := g (cst 2 ? • (cst 0 ! cst 0 • 𝟘)).
Definition q3 : proc := g (cst 2 ? • g ((𝛕 • (cst 0 ! cst 0 • 𝟘)) + (𝛕 • g 𝟘))).

Example p3_q3_verdict : ∃ s t, vaccs_verdict (VP := VACCS_nat) 0 5 1 p3 q3 = R_fails s t.
Proof. vm_compute. eexists _, _. reflexivity. Qed.

Lemma p3_not_below_q3 : p3 ⋢ₘᵤₛₜᵢ q3.
Proof. destruct p3_q3_verdict as (s & t & e). exact (vaccs_verdict_refutes _ _ _ _ _ _ _ e). Qed.

Definition ω : proc := rec 0 • (pr_var 0).

Lemma ω_below_p1 : ω ⊑ₘᵤₛₜᵢ p1.
Proof. apply (vaccs_verdict_holds (VP := VACCS_nat) 2 5 0). vm_compute. reflexivity. Qed.

Example p1_ω_verdict : ∃ s t, vaccs_verdict (VP := VACCS_nat) 0 5 1 p1 ω = R_fails s t.
Proof. vm_compute. eexists _, _. reflexivity. Qed.

Definition ω_par : proc := rec 0 • (pr_var 0 ‖ (cst 0 ! cst 0 • 𝟘)).

Example p1_ω_par_verdict : ∃ s t, vaccs_verdict (VP := VACCS_nat) 0 5 1 p1 ω_par = R_fails s t.
Proof. vm_compute. eexists _, _. reflexivity. Qed.

Lemma ω_par_below_p1 : ω_par ⊑ₘᵤₛₜᵢ p1.
Proof. apply (vaccs_verdict_holds (VP := VACCS_nat) 2 5 0). vm_compute. reflexivity. Qed.

End Examples.
(* end hide *)
