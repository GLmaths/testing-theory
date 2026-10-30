(* begin hide *)
From Stdlib Require Import Lia.
From stdpp Require Import sets gmap gmultiset countable numbers list sorting.
From TestingTheory Require Import VCCS.Testing.ta_tc_gen DefinitionAS Equivalence Must
  ParallelLTSConstruction InteractionBetweenLts Bisimulation
  ActTau InputOutputActions Convergence Termination InListPropHelper
  gLts Lts_OBA FiniteImageLTS Testing_Predicate Completeness Lts_FW Lts_OBA_FB MultisetLTSConstruction
  SetLTSConstruction ForwarderConstruction.
From TestingTheory Require Import coFiniteImage coConvergence coWeakTransition DefinitionASrel
  CompletenessASco EquivalenceASco TestSpecBridge SyncActions
  VCCS.Language.LTS VCCS.Language.gLts_Instance VCCS.Language.Label_Abstraction
  Label_Abstraction.LabelAbstraction Label_Abstraction.Decidable_dichotomic Subset_Act
  Decision.Tools_in_construction.Inductive.Generic.Helpers Decision.Tools_in_construction.Inductive.Generic.Acceptance_Tests_Gamma
  Decision.Tools_in_construction.Inductive.VCCS.Tests VCCS.Helper.Value_Swap VCCS.Characterisations.Must_Characterisation
  Decision.Tools_in_construction.Inductive.Generic.Bisim Decision.Tools_in_construction.Inductive.Generic.Interface Decision.Tools_in_construction.Inductive.Generic.Sets Decision.Tools_in_construction.Inductive.Generic.Graph Decision.Tools_in_construction.Inductive.Generic.Swaps Decision.Tools_in_construction.Inductive.Generic.Adequacy Decision.Tools_in_construction.Inductive.Generic.Verdict
  Decision.Tools_in_construction.Inductive.VCCS.Instance Coin_tower_co Decision.Tools_in_construction.CoInductive.Generic.Certificate Decision.Tools_in_construction.CoInductive.Generic.Antichain Decision.Tools_in_construction.CoInductive.Generic.Normalised Decision.Tools_in_construction.CoInductive.Generic.Auto
  Decision.Tools_in_construction.CoInductive.VCCS.Must_Co.
Import ListNotations.
From TestingTheory Require Export VCCS.Testing.ta_tc_gen DefinitionAS Equivalence Must ParallelLTSConstruction InteractionBetweenLts Bisimulation ActTau InputOutputActions Convergence Termination InListPropHelper gLts Lts_OBA FiniteImageLTS Testing_Predicate Completeness Lts_FW Lts_OBA_FB MultisetLTSConstruction SetLTSConstruction ForwarderConstruction coFiniteImage coConvergence coWeakTransition DefinitionASrel CompletenessASco EquivalenceASco TestSpecBridge SyncActions VCCS.Language.LTS VCCS.Language.gLts_Instance VCCS.Language.Label_Abstraction Label_Abstraction.LabelAbstraction Label_Abstraction.Decidable_dichotomic Subset_Act Decision.Tools_in_construction.Inductive.Generic.Helpers Decision.Tools_in_construction.Inductive.Generic.Acceptance_Tests_Gamma Decision.Tools_in_construction.Inductive.VCCS.Tests VCCS.Helper.Value_Swap VCCS.Characterisations.Must_Characterisation Decision.Tools_in_construction.Inductive.Generic.Interface Decision.Tools_in_construction.Inductive.Generic.Sets Decision.Tools_in_construction.Inductive.Generic.Graph Decision.Tools_in_construction.Inductive.Generic.Swaps Decision.Tools_in_construction.Inductive.Generic.Adequacy Decision.Tools_in_construction.Inductive.Generic.Verdict Decision.Tools_in_construction.Inductive.VCCS.Instance.


#[global] Instance VCCS_nat : VCCS_Parameters := {| Channel := nat; Value := nat; O := 0 |}.

Definition vccsnat_exact (m : nat) (k : nat) (n : nat) (p q : proc) : result := vccs_verdict m k n p q.

Theorem vccsnat_exact_holds (m : nat) (k : nat) (n : nat) (p q : proc) : vccsnat_exact m k n p q = R_holds → p ⊑ₘᵤₛₜᵢ q.
Proof. exact (vccs_verdict_holds m k n p q). Qed.

Theorem vccsnat_exact_refutes (m : nat) (k : nat) (n : nat) (p q : proc) s t : vccsnat_exact m k n p q = R_fails s t → p ⋢ₘᵤₛₜᵢ q.
Proof. exact (vccs_verdict_refutes m k n p q s t). Qed.

Definition vccsnat_ac (m : nat) (k : nat) (n : nat) (p q : proc) : result := vccs_verdict_ac m k n p q.

Theorem vccsnat_ac_holds (m : nat) (k : nat) (n : nat) (p q : proc) : vccsnat_ac m k n p q = R_holds → p ⊑ₘᵤₛₜᵢ q.
Proof. exact (vccs_verdict_ac_holds m k n p q). Qed.

Theorem vccsnat_ac_refutes (m : nat) (k : nat) (n : nat) (p q : proc) s t : vccsnat_ac m k n p q = R_fails s t → p ⋢ₘᵤₛₜᵢ q.
Proof. exact (vccs_verdict_ac_refutes m k n p q s t). Qed.

Definition vccsnat_xa (m : nat) (k : nat) (n : nat) (p q : proc) : result := vccs_verdict_xa m k n p q.

Theorem vccsnat_xa_holds (m : nat) (k : nat) (n : nat) (p q : proc) : vccsnat_xa m k n p q = R_holds → p ⊑ₘᵤₛₜᵢ q.
Proof. exact (vccs_verdict_xa_holds m k n p q). Qed.

Theorem vccsnat_xa_refutes (m : nat) (k : nat) (n : nat) (p q : proc) s t : vccsnat_xa m k n p q = R_fails s t → p ⋢ₘᵤₛₜᵢ q.
Proof. exact (vccs_verdict_xa_refutes m k n p q s t). Qed.

Definition vccsnat_norm (m : nat) (k : nat) (n : nat) (p q : proc) : result := vccs_verdict_n m k n p q.

Theorem vccsnat_norm_holds (m : nat) (k : nat) (n : nat) (p q : proc) : vccsnat_norm m k n p q = R_holds → p ⊑ₘᵤₛₜᵢ q.
Proof. exact (vccs_verdict_n_holds m k n p q). Qed.

Theorem vccsnat_norm_refutes (m : nat) (k : nat) (n : nat) (p q : proc) s t : vccsnat_norm m k n p q = R_fails s t → p ⋢ₘᵤₛₜᵢ q.
Proof. exact (vccs_verdict_n_refutes m k n p q s t). Qed.

Definition vccsnat_auto (j : nat) (m : nat) (k : nat) (n : nat) (p q : proc) : result := vccs_verdict_auto j m k n p q.

Theorem vccsnat_auto_holds (j : nat) (m : nat) (k : nat) (n : nat) (p q : proc) : vccsnat_auto j m k n p q = R_holds → p ⊑ₘᵤₛₜᵢ q.
Proof. exact (vccs_verdict_auto_holds j m k n p q). Qed.

Theorem vccsnat_auto_refutes (j : nat) (m : nat) (k : nat) (n : nat) (p q : proc) s t : vccsnat_auto j m k n p q = R_fails s t → p ⋢ₘᵤₛₜᵢ q.
Proof. exact (vccs_verdict_auto_refutes j m k n p q s t). Qed.
(* end hide *)
