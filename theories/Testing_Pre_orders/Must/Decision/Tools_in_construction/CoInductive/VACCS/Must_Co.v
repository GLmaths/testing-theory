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
  Decision.Tools_in_construction.Inductive.VACCS.Instance Coin_tower_co Decision.Tools_in_construction.CoInductive.Generic.Certificate Decision.Tools_in_construction.CoInductive.Generic.Antichain Decision.Tools_in_construction.CoInductive.Generic.Normalised Decision.Tools_in_construction.CoInductive.Generic.Auto.
Import ListNotations.

Section VACCS_Verdict_Co.

Context `{VP : VACCS_Parameters}.

#[local] Existing Instance SyncAction_VACCS.

Theorem vaccs_verdict_holds_co (m k n : nat) (p q : proc) : vaccs_verdict m k n p q = R_holds → p ⊑ₘᵤₛₜᵢ q.
Proof.
  intros h. destruct (verdict_holds_co m k n _ _ h) as [h1 h2].
  apply must_iff_co_acceptance_set_VACCS. split; [exact h1 |].
  intros s q' hp w st. destruct (h2 s q' hp w st) as (p' & w' & st' & sub).
  exists p'. split_and!; [exact w' | exact st' | exact (ρ_incl_of_Γ_incl _ _ sub)].
Qed.

Definition vaccs_verdict_ac (m k n : nat) (p q : proc) : result := verdict_ac m k n (p ▷ ∅) (q ▷ ∅).

Theorem vaccs_verdict_ac_holds (m k n : nat) (p q : proc) : vaccs_verdict_ac m k n p q = R_holds → p ⊑ₘᵤₛₜᵢ q.
Proof.
  intros h. destruct (verdict_ac_holds m k n _ _ h) as [h1 h2].
  apply must_iff_co_acceptance_set_VACCS. split; [exact h1 |].
  intros s q' hp w st. destruct (h2 s q' hp w st) as (p' & w' & st' & sub).
  exists p'. split_and!; [exact w' | exact st' | exact (ρ_incl_of_Γ_incl _ _ sub)].
Qed.

Theorem vaccs_verdict_ac_refutes (m k n : nat) (p q : proc) s t : vaccs_verdict_ac m k n p q = R_fails s t → p ⋢ₘᵤₛₜᵢ q.
Proof.
  intros h. destruct (verdict_ac_fails m k n _ _ s t h) as [h1 h2].
  exact (distinguishing_test_refutes p q t h1 h2).
Qed.

Definition vaccs_verdict_n (m k n : nat) (p q : proc) : result := verdict_n m k n (p ▷ ∅) (q ▷ ∅).

Theorem vaccs_verdict_n_holds (m k n : nat) (p q : proc) : vaccs_verdict_n m k n p q = R_holds → p ⊑ₘᵤₛₜᵢ q.
Proof.
  intros h. destruct (verdict_n_holds m k n _ _ h) as [h1 h2].
  apply must_iff_co_acceptance_set_VACCS. split; [exact h1 |].
  intros s q' hp w st. destruct (h2 s q' hp w st) as (p' & w' & st' & sub).
  exists p'. split_and!; [exact w' | exact st' | exact (ρ_incl_of_Γ_incl _ _ sub)].
Qed.

Theorem vaccs_verdict_n_refutes (m k n : nat) (p q : proc) s t : vaccs_verdict_n m k n p q = R_fails s t → p ⋢ₘᵤₛₜᵢ q.
Proof.
  intros h. destruct (verdict_n_fails m k n _ _ s t h) as [h1 h2].
  exact (distinguishing_test_refutes p q t h1 h2).
Qed.

Definition vaccs_verdict_auto (j m k n : nat) (p q : proc) : result := verdict_auto j m k n (p ▷ ∅) (q ▷ ∅).

Theorem vaccs_verdict_auto_holds (j m k n : nat) (p q : proc) : vaccs_verdict_auto j m k n p q = R_holds → p ⊑ₘᵤₛₜᵢ q.
Proof.
  intros h. destruct (verdict_auto_holds j m k n _ _ h) as [h1 h2].
  apply must_iff_co_acceptance_set_VACCS. split; [exact h1 |].
  intros s q' hp w st. destruct (h2 s q' hp w st) as (p' & w' & st' & sub).
  exists p'. split_and!; [exact w' | exact st' | exact (ρ_incl_of_Γ_incl _ _ sub)].
Qed.

Theorem vaccs_verdict_auto_refutes (j m k n : nat) (p q : proc) s t : vaccs_verdict_auto j m k n p q = R_fails s t → p ⋢ₘᵤₛₜᵢ q.
Proof.
  intros h. destruct (verdict_auto_fails j m k n _ _ s t h) as [h1 h2].
  exact (distinguishing_test_refutes p q t h1 h2).
Qed.

Definition vaccs_verdict_xa (m k n : nat) (p q : proc) : result := verdict_xa m k n (p ▷ ∅) (q ▷ ∅).

Theorem vaccs_verdict_xa_holds (m k n : nat) (p q : proc) : vaccs_verdict_xa m k n p q = R_holds → p ⊑ₘᵤₛₜᵢ q.
Proof.
  intros h. destruct (verdict_xa_holds m k n _ _ h) as [h1 h2].
  apply must_iff_co_acceptance_set_VACCS. split; [exact h1 |].
  intros s q' hp w st. destruct (h2 s q' hp w st) as (p' & w' & st' & sub).
  exists p'. split_and!; [exact w' | exact st' | exact (ρ_incl_of_Γ_incl _ _ sub)].
Qed.

Theorem vaccs_verdict_xa_refutes (m k n : nat) (p q : proc) s t : vaccs_verdict_xa m k n p q = R_fails s t → p ⋢ₘᵤₛₜᵢ q.
Proof.
  intros h. destruct (verdict_xa_fails m k n _ _ s t h) as [h1 h2].
  exact (distinguishing_test_refutes p q t h1 h2).
Qed.

End VACCS_Verdict_Co.
(* end hide *)
