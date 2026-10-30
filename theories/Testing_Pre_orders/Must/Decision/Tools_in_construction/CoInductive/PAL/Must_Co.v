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
  Decision.Tools_in_construction.Inductive.PAL.Instance Coin_tower_co Decision.Tools_in_construction.CoInductive.Generic.Certificate Decision.Tools_in_construction.CoInductive.Generic.Antichain Decision.Tools_in_construction.CoInductive.Generic.Normalised Decision.Tools_in_construction.CoInductive.Generic.Auto.
Import ListNotations.

#[local] Hint Mode ExtAction ! : typeclass_instances.

Section PAL_Verdict_Co.



#[local] Existing Instance SyncAction_PAL.

Theorem pal_verdict_holds_co (m k n : nat) (p q : term nat) : pal_verdict m k n p q = R_holds → p ᴘᴀʟ⊑ₘᵤₛₜᵢ q.
Proof.
  intros h. destruct (verdict_holds_co m k n p q h) as [h1 h2].
  apply PAL_Alt_equivalence. split; [exact h1 |].
  intros s q' hp w st. destruct (h2 s q' hp w st) as (p' & w' & st' & sub).
  exists p'. split_and!; [exact w' | exact st' | exact (ρ_incl_of_Γ_incl _ _ sub)].
Qed.

Definition pal_verdict_ac (m k n : nat) (p q : term nat) : result := verdict_ac m k n p q.

Theorem pal_verdict_ac_holds (m k n : nat) (p q : term nat) : pal_verdict_ac m k n p q = R_holds → p ᴘᴀʟ⊑ₘᵤₛₜᵢ q.
Proof.
  intros h. destruct (verdict_ac_holds m k n p q h) as [h1 h2].
  apply PAL_Alt_equivalence. split; [exact h1 |].
  intros s q' hp w st. destruct (h2 s q' hp w st) as (p' & w' & st' & sub).
  exists p'. split_and!; [exact w' | exact st' | exact (ρ_incl_of_Γ_incl _ _ sub)].
Qed.

Theorem pal_verdict_ac_refutes (m k n : nat) (p q : term nat) s t : pal_verdict_ac m k n p q = R_fails s t → ¬ p ᴘᴀʟ⊑ₘᵤₛₜᵢ q.
Proof.
  intros h. destruct (verdict_ac_fails m k n p q s t h) as [h1 h2].
  exact (distinguishing_test_refutes p q t h1 h2).
Qed.

Definition pal_verdict_n (m k n : nat) (p q : term nat) : result := verdict_n m k n p q.

Theorem pal_verdict_n_holds (m k n : nat) (p q : term nat) : pal_verdict_n m k n p q = R_holds → p ᴘᴀʟ⊑ₘᵤₛₜᵢ q.
Proof.
  intros h. destruct (verdict_n_holds m k n p q h) as [h1 h2].
  apply PAL_Alt_equivalence. split; [exact h1 |].
  intros s q' hp w st. destruct (h2 s q' hp w st) as (p' & w' & st' & sub).
  exists p'. split_and!; [exact w' | exact st' | exact (ρ_incl_of_Γ_incl _ _ sub)].
Qed.

Theorem pal_verdict_n_refutes (m k n : nat) (p q : term nat) s t : pal_verdict_n m k n p q = R_fails s t → ¬ p ᴘᴀʟ⊑ₘᵤₛₜᵢ q.
Proof.
  intros h. destruct (verdict_n_fails m k n p q s t h) as [h1 h2].
  exact (distinguishing_test_refutes p q t h1 h2).
Qed.

Definition pal_verdict_auto (j m k n : nat) (p q : term nat) : result := verdict_auto j m k n p q.

Theorem pal_verdict_auto_holds (j m k n : nat) (p q : term nat) : pal_verdict_auto j m k n p q = R_holds → p ᴘᴀʟ⊑ₘᵤₛₜᵢ q.
Proof.
  intros h. destruct (verdict_auto_holds j m k n p q h) as [h1 h2].
  apply PAL_Alt_equivalence. split; [exact h1 |].
  intros s q' hp w st. destruct (h2 s q' hp w st) as (p' & w' & st' & sub).
  exists p'. split_and!; [exact w' | exact st' | exact (ρ_incl_of_Γ_incl _ _ sub)].
Qed.

Theorem pal_verdict_auto_refutes (j m k n : nat) (p q : term nat) s t : pal_verdict_auto j m k n p q = R_fails s t → ¬ p ᴘᴀʟ⊑ₘᵤₛₜᵢ q.
Proof.
  intros h. destruct (verdict_auto_fails j m k n p q s t h) as [h1 h2].
  exact (distinguishing_test_refutes p q t h1 h2).
Qed.

Definition pal_verdict_xa (m k n : nat) (p q : term nat) : result := verdict_xa m k n p q.

Theorem pal_verdict_xa_holds (m k n : nat) (p q : term nat) : pal_verdict_xa m k n p q = R_holds → p ᴘᴀʟ⊑ₘᵤₛₜᵢ q.
Proof.
  intros h. destruct (verdict_xa_holds m k n p q h) as [h1 h2].
  apply PAL_Alt_equivalence. split; [exact h1 |].
  intros s q' hp w st. destruct (h2 s q' hp w st) as (p' & w' & st' & sub).
  exists p'. split_and!; [exact w' | exact st' | exact (ρ_incl_of_Γ_incl _ _ sub)].
Qed.

Theorem pal_verdict_xa_refutes (m k n : nat) (p q : term nat) s t : pal_verdict_xa m k n p q = R_fails s t → ¬ p ᴘᴀʟ⊑ₘᵤₛₜᵢ q.
Proof.
  intros h. destruct (verdict_xa_fails m k n p q s t h) as [h1 h2].
  exact (distinguishing_test_refutes p q t h1 h2).
Qed.

End PAL_Verdict_Co.
(* end hide *)
