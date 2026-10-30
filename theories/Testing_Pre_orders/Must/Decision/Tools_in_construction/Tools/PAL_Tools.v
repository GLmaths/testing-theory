(* begin hide *)
From Stdlib.Unicode Require Import Utf8.
From Stdlib Require Import Lia.
From stdpp Require Import base countable gmap list sets sorting.
From TestingTheory Require Import Termination ActTau gLts Bisimulation SyncActions Must RelationKernel Subset_Act
  Lts_OBA Lts_FW Lts_OBA_FB LtsFW InteractionBetweenLts Testing_Predicate InListPropHelper
  coFiniteImage coConvergence coWeakTransition DefinitionASrel CompletenessASco
  Label_Abstraction.LabelAbstraction
  PAL.Language.Syntax PAL.Language.LTS PAL.Language.Phi PAL.Language.AbsAction PAL.Language.Congruence
  PAL.Language.Dichotomy PAL.Language.Label_Abstraction PAL.Language.Value_Swap PAL.Language.Divergence PAL_Good PAL.Testing.Must_Preorder
  PAL.Testing.Tests PAL.Testing.Test_Spec PAL.Testing.CoTrace_Hypotheses PAL.Characterisations.Must_Characterisation
  Decision.Tools_in_construction.Inductive.Generic.Helpers Decision.Tools_in_construction.Inductive.Generic.Acceptance_Tests_Gamma
  Decision.Tools_in_construction.Inductive.PAL.Tests Decision.Tools_in_construction.Inductive.Generic.Bisim Decision.Tools_in_construction.Inductive.Generic.Interface Decision.Tools_in_construction.Inductive.Generic.Sets Decision.Tools_in_construction.Inductive.Generic.Graph Decision.Tools_in_construction.Inductive.Generic.Swaps Decision.Tools_in_construction.Inductive.Generic.Adequacy Decision.Tools_in_construction.Inductive.Generic.Verdict
  Decision.Tools_in_construction.Inductive.PAL.Instance Coin_tower_co Decision.Tools_in_construction.CoInductive.Generic.Certificate Decision.Tools_in_construction.CoInductive.Generic.Antichain Decision.Tools_in_construction.CoInductive.Generic.Normalised Decision.Tools_in_construction.CoInductive.Generic.Auto
  Decision.Tools_in_construction.CoInductive.PAL.Must_Co.
Import ListNotations.
From TestingTheory Require Export ActTau gLts Bisimulation SyncActions Must RelationKernel Subset_Act Lts_OBA Lts_FW Lts_OBA_FB LtsFW InteractionBetweenLts Testing_Predicate InListPropHelper coFiniteImage coConvergence coWeakTransition DefinitionASrel CompletenessASco Label_Abstraction.LabelAbstraction PAL.Language.Syntax PAL.Language.LTS PAL.Language.Phi PAL.Language.AbsAction PAL.Language.Congruence PAL.Language.Dichotomy PAL.Language.Label_Abstraction PAL.Language.Value_Swap PAL_Good PAL.Testing.Must_Preorder PAL.Testing.Tests PAL.Testing.Test_Spec PAL.Testing.CoTrace_Hypotheses PAL.Characterisations.Must_Characterisation Decision.Tools_in_construction.Inductive.Generic.Helpers Decision.Tools_in_construction.Inductive.Generic.Acceptance_Tests_Gamma Decision.Tools_in_construction.Inductive.PAL.Tests Decision.Tools_in_construction.Inductive.Generic.Interface Decision.Tools_in_construction.Inductive.Generic.Sets Decision.Tools_in_construction.Inductive.Generic.Graph Decision.Tools_in_construction.Inductive.Generic.Swaps Decision.Tools_in_construction.Inductive.Generic.Adequacy Decision.Tools_in_construction.Inductive.Generic.Verdict Decision.Tools_in_construction.Inductive.PAL.Instance.

#[local] Hint Mode ExtAction ! : typeclass_instances.

Definition palnat_exact (m : nat) (k : nat) (n : nat) (p q : term nat) : result := pal_verdict m k n p q.

Theorem palnat_exact_holds (m : nat) (k : nat) (n : nat) (p q : term nat) : palnat_exact m k n p q = R_holds → p ᴘᴀʟ⊑ₘᵤₛₜᵢ q.
Proof. exact (pal_verdict_holds m k n p q). Qed.

Theorem palnat_exact_refutes (m : nat) (k : nat) (n : nat) (p q : term nat) s t : palnat_exact m k n p q = R_fails s t → ¬ p ᴘᴀʟ⊑ₘᵤₛₜᵢ q.
Proof. exact (pal_verdict_refutes m k n p q s t). Qed.

Definition palnat_ac (m : nat) (k : nat) (n : nat) (p q : term nat) : result := pal_verdict_ac m k n p q.

Theorem palnat_ac_holds (m : nat) (k : nat) (n : nat) (p q : term nat) : palnat_ac m k n p q = R_holds → p ᴘᴀʟ⊑ₘᵤₛₜᵢ q.
Proof. exact (pal_verdict_ac_holds m k n p q). Qed.

Theorem palnat_ac_refutes (m : nat) (k : nat) (n : nat) (p q : term nat) s t : palnat_ac m k n p q = R_fails s t → ¬ p ᴘᴀʟ⊑ₘᵤₛₜᵢ q.
Proof. exact (pal_verdict_ac_refutes m k n p q s t). Qed.

Definition palnat_xa (m : nat) (k : nat) (n : nat) (p q : term nat) : result := pal_verdict_xa m k n p q.

Theorem palnat_xa_holds (m : nat) (k : nat) (n : nat) (p q : term nat) : palnat_xa m k n p q = R_holds → p ᴘᴀʟ⊑ₘᵤₛₜᵢ q.
Proof. exact (pal_verdict_xa_holds m k n p q). Qed.

Theorem palnat_xa_refutes (m : nat) (k : nat) (n : nat) (p q : term nat) s t : palnat_xa m k n p q = R_fails s t → ¬ p ᴘᴀʟ⊑ₘᵤₛₜᵢ q.
Proof. exact (pal_verdict_xa_refutes m k n p q s t). Qed.

Definition palnat_norm (m : nat) (k : nat) (n : nat) (p q : term nat) : result := pal_verdict_n m k n p q.

Theorem palnat_norm_holds (m : nat) (k : nat) (n : nat) (p q : term nat) : palnat_norm m k n p q = R_holds → p ᴘᴀʟ⊑ₘᵤₛₜᵢ q.
Proof. exact (pal_verdict_n_holds m k n p q). Qed.

Theorem palnat_norm_refutes (m : nat) (k : nat) (n : nat) (p q : term nat) s t : palnat_norm m k n p q = R_fails s t → ¬ p ᴘᴀʟ⊑ₘᵤₛₜᵢ q.
Proof. exact (pal_verdict_n_refutes m k n p q s t). Qed.

Definition palnat_auto (j : nat) (m : nat) (k : nat) (n : nat) (p q : term nat) : result := pal_verdict_auto j m k n p q.

Theorem palnat_auto_holds (j : nat) (m : nat) (k : nat) (n : nat) (p q : term nat) : palnat_auto j m k n p q = R_holds → p ᴘᴀʟ⊑ₘᵤₛₜᵢ q.
Proof. exact (pal_verdict_auto_holds j m k n p q). Qed.

Theorem palnat_auto_refutes (j : nat) (m : nat) (k : nat) (n : nat) (p q : term nat) s t : palnat_auto j m k n p q = R_fails s t → ¬ p ᴘᴀʟ⊑ₘᵤₛₜᵢ q.
Proof. exact (pal_verdict_auto_refutes j m k n p q s t). Qed.
(* end hide *)
