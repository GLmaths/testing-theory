(* begin hide *)
From Stdlib Require Import Lia.
From stdpp Require Import sets gmap gmultiset countable numbers list sorting finite.
From TestingTheory Require Import Termination VACCS.Testing.ta_tc_gen DefinitionAS Equivalence Must Lift
  ParallelLTSConstruction InteractionBetweenLts Bisimulation
  ActTau InputOutputActions Convergence InListPropHelper
  gLts Lts_OBA FiniteImageLTS Testing_Predicate Completeness Lts_FW Lts_OBA_FB MultisetLTSConstruction
  SetLTSConstruction ForwarderConstruction.
From TestingTheory Require Import coFiniteImage coConvergence coWeakTransition DefinitionASrel
  CompletenessASco EquivalenceASco TestSpecBridge SyncActions
  VACCS.Language.LTS VACCS.Language.gLts_Instance VACCS.Language.Label_Abstraction
  VACCS.Characterisations.Must_Characterisation VACCS.Helper.Atom_Swap VACCS.Helper.Divergence
  Label_Abstraction.LabelAbstraction Label_Abstraction.Decidable_dichotomic Subset_Act
  Decision.Tools_in_construction.Inductive.Generic.Helpers Decision.Tools_in_construction.Inductive.Generic.Acceptance_Tests_Gamma
  Decision.Tools_in_construction.Inductive.VACCS.Tests Decision.Tools_in_construction.Inductive.Generic.Bisim Decision.Tools_in_construction.Inductive.Generic.Interface Decision.Tools_in_construction.Inductive.Generic.Sets Decision.Tools_in_construction.Inductive.Generic.Graph Decision.Tools_in_construction.Inductive.Generic.Swaps Decision.Tools_in_construction.Inductive.Generic.Adequacy Decision.Tools_in_construction.Inductive.Generic.Verdict Decision.Tools_in_construction.Inductive.Generic.Forwarders
  Decision.Tools_in_construction.Inductive.VACCS.Instance Coin_tower_co Decision.Tools_in_construction.CoInductive.Generic.Certificate Decision.Tools_in_construction.CoInductive.Generic.Antichain Decision.Tools_in_construction.CoInductive.Generic.Normalised Decision.Tools_in_construction.CoInductive.Generic.Auto
  Decision.Tools_in_construction.CoInductive.VACCS.Must_Co.
Import ListNotations.
From TestingTheory Require Export VACCS.Testing.ta_tc_gen DefinitionAS Equivalence Must Lift ParallelLTSConstruction InteractionBetweenLts Bisimulation ActTau InputOutputActions Convergence InListPropHelper gLts Lts_OBA FiniteImageLTS Testing_Predicate Completeness Lts_FW Lts_OBA_FB MultisetLTSConstruction SetLTSConstruction ForwarderConstruction coFiniteImage coConvergence coWeakTransition DefinitionASrel CompletenessASco EquivalenceASco TestSpecBridge SyncActions VACCS.Language.LTS VACCS.Language.gLts_Instance VACCS.Language.Label_Abstraction VACCS.Characterisations.Must_Characterisation VACCS.Helper.Atom_Swap Label_Abstraction.LabelAbstraction Label_Abstraction.Decidable_dichotomic Subset_Act Decision.Tools_in_construction.Inductive.Generic.Helpers Decision.Tools_in_construction.Inductive.Generic.Acceptance_Tests_Gamma Decision.Tools_in_construction.Inductive.VACCS.Tests Decision.Tools_in_construction.Inductive.Generic.Interface Decision.Tools_in_construction.Inductive.Generic.Sets Decision.Tools_in_construction.Inductive.Generic.Graph Decision.Tools_in_construction.Inductive.Generic.Swaps Decision.Tools_in_construction.Inductive.Generic.Adequacy Decision.Tools_in_construction.Inductive.Generic.Verdict Decision.Tools_in_construction.Inductive.Generic.Forwarders Decision.Tools_in_construction.Inductive.VACCS.Instance.


#[global] Instance VACCS_nat : VACCS_Parameters := {| Channel := nat; Value := nat; O := 0 |}.

Definition vaccsnat_exact (m : nat) (k : nat) (n : nat) (p q : proc) : result := vaccs_verdict m k n p q.

Theorem vaccsnat_exact_holds (m : nat) (k : nat) (n : nat) (p q : proc) : vaccsnat_exact m k n p q = R_holds → p ⊑ₘᵤₛₜᵢ q.
Proof. exact (vaccs_verdict_holds m k n p q). Qed.

Theorem vaccsnat_exact_refutes (m : nat) (k : nat) (n : nat) (p q : proc) s t : vaccsnat_exact m k n p q = R_fails s t → p ⋢ₘᵤₛₜᵢ q.
Proof. exact (vaccs_verdict_refutes m k n p q s t). Qed.

Definition vaccsnat_ac (m : nat) (k : nat) (n : nat) (p q : proc) : result := vaccs_verdict_ac m k n p q.

Theorem vaccsnat_ac_holds (m : nat) (k : nat) (n : nat) (p q : proc) : vaccsnat_ac m k n p q = R_holds → p ⊑ₘᵤₛₜᵢ q.
Proof. exact (vaccs_verdict_ac_holds m k n p q). Qed.

Theorem vaccsnat_ac_refutes (m : nat) (k : nat) (n : nat) (p q : proc) s t : vaccsnat_ac m k n p q = R_fails s t → p ⋢ₘᵤₛₜᵢ q.
Proof. exact (vaccs_verdict_ac_refutes m k n p q s t). Qed.

Definition vaccsnat_xa (m : nat) (k : nat) (n : nat) (p q : proc) : result := vaccs_verdict_xa m k n p q.

Theorem vaccsnat_xa_holds (m : nat) (k : nat) (n : nat) (p q : proc) : vaccsnat_xa m k n p q = R_holds → p ⊑ₘᵤₛₜᵢ q.
Proof. exact (vaccs_verdict_xa_holds m k n p q). Qed.

Theorem vaccsnat_xa_refutes (m : nat) (k : nat) (n : nat) (p q : proc) s t : vaccsnat_xa m k n p q = R_fails s t → p ⋢ₘᵤₛₜᵢ q.
Proof. exact (vaccs_verdict_xa_refutes m k n p q s t). Qed.

Definition vaccsnat_norm (m : nat) (k : nat) (n : nat) (p q : proc) : result := vaccs_verdict_n m k n p q.

Theorem vaccsnat_norm_holds (m : nat) (k : nat) (n : nat) (p q : proc) : vaccsnat_norm m k n p q = R_holds → p ⊑ₘᵤₛₜᵢ q.
Proof. exact (vaccs_verdict_n_holds m k n p q). Qed.

Theorem vaccsnat_norm_refutes (m : nat) (k : nat) (n : nat) (p q : proc) s t : vaccsnat_norm m k n p q = R_fails s t → p ⋢ₘᵤₛₜᵢ q.
Proof. exact (vaccs_verdict_n_refutes m k n p q s t). Qed.

Definition vaccsnat_auto (j : nat) (m : nat) (k : nat) (n : nat) (p q : proc) : result := vaccs_verdict_auto j m k n p q.

Theorem vaccsnat_auto_holds (j : nat) (m : nat) (k : nat) (n : nat) (p q : proc) : vaccsnat_auto j m k n p q = R_holds → p ⊑ₘᵤₛₜᵢ q.
Proof. exact (vaccs_verdict_auto_holds j m k n p q). Qed.

Theorem vaccsnat_auto_refutes (j : nat) (m : nat) (k : nat) (n : nat) (p q : proc) s t : vaccsnat_auto j m k n p q = R_fails s t → p ⋢ₘᵤₛₜᵢ q.
Proof. exact (vaccs_verdict_auto_refutes j m k n p q s t). Qed.
(* end hide *)
