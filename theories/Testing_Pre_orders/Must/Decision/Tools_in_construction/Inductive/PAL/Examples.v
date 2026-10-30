(* begin hide *)
From Stdlib.Unicode Require Import Utf8.
From Stdlib Require Import Lia.
From stdpp Require Import base countable gmap list sets.
From TestingTheory Require Import ActTau gLts Bisimulation SyncActions Must RelationKernel Subset_Act
  Lts_OBA Lts_FW Lts_OBA_FB LtsFW InteractionBetweenLts Testing_Predicate InListPropHelper
  coFiniteImage coConvergence coWeakTransition DefinitionASrel CompletenessASco
  Label_Abstraction.LabelAbstraction
  PAL.Language.Syntax PAL.Language.LTS PAL.Language.Phi PAL.Language.AbsAction PAL.Language.Congruence
  PAL.Language.Dichotomy PAL.Language.Label_Abstraction PAL.Language.Value_Swap PAL_Good PAL.Testing.Must_Preorder
  PAL.Testing.Tests PAL.Testing.Test_Spec PAL.Testing.CoTrace_Hypotheses PAL.Characterisations.Must_Characterisation
  Decision.Tools_in_construction.Inductive.Generic.Helpers Decision.Tools_in_construction.Inductive.Generic.Acceptance_Tests_Gamma
  Decision.Tools_in_construction.Inductive.PAL.Tests Decision.Tools_in_construction.Inductive.Generic.Interface Decision.Tools_in_construction.Inductive.Generic.Sets Decision.Tools_in_construction.Inductive.Generic.Graph Decision.Tools_in_construction.Inductive.Generic.Swaps Decision.Tools_in_construction.Inductive.Generic.Adequacy Decision.Tools_in_construction.Inductive.Generic.Verdict Decision.Tools_in_construction.Inductive.PAL.Instance.
Import ListNotations.

#[local] Hint Mode ExtAction ! : typeclass_instances.

Section Examples.

#[local] Open Scope pal_scope.

Definition p1 : term nat := t_out [f_actual (ve_val 1)] t_nil.
Definition q1 : term nat := t_ichoice p1 t_nil.
Definition ω : term nat := t_undef.
Definition p3 : term nat := t_in [f_formal 0] p1.
Definition q3 : term nat := t_in [f_formal 0] q1.

Example p1_q1_verdict : ∃ s t, pal_verdict 20 5 1 p1 q1 = R_fails s t.
Proof. vm_compute. eexists _, _. reflexivity. Qed.

Lemma p1_not_below_q1 : ¬ p1 ᴘᴀʟ⊑ₘᵤₛₜᵢ q1.
Proof. destruct p1_q1_verdict as (s & t & e). exact (pal_verdict_refutes _ _ _ _ _ _ _ e). Qed.

Lemma q1_below_p1 : q1 ᴘᴀʟ⊑ₘᵤₛₜᵢ p1.
Proof. apply (pal_verdict_holds 20 5 1). vm_compute. reflexivity. Qed.

Lemma ω_below_p1 : ω ᴘᴀʟ⊑ₘᵤₛₜᵢ p1.
Proof. apply (pal_verdict_holds 20 5 1). vm_compute. reflexivity. Qed.

Example p3_q3_verdict : ∃ s t, pal_verdict 20 5 2 p3 q3 = R_fails s t.
Proof. vm_compute. eexists _, _. reflexivity. Qed.

Lemma p3_not_below_q3 : ¬ p3 ᴘᴀʟ⊑ₘᵤₛₜᵢ q3.
Proof. destruct p3_q3_verdict as (s & t & e). exact (pal_verdict_refutes _ _ _ _ _ _ _ e). Qed.

Lemma q3_below_p3 : q3 ᴘᴀʟ⊑ₘᵤₛₜᵢ p3.
Proof. apply (pal_verdict_holds 20 5 2). vm_compute. reflexivity. Qed.

Definition ω_par : term nat := t_rec 0 (t_par (t_pvar 0) p1).

Example p1_ω_par_verdict : ∃ s t, pal_verdict 20 5 1 p1 ω_par = R_fails s t.
Proof. vm_compute. eexists _, _. reflexivity. Qed.

Lemma ω_par_below_q1 : ω_par ᴘᴀʟ⊑ₘᵤₛₜᵢ q1.
Proof. apply (pal_verdict_holds 20 5 1). vm_compute. reflexivity. Qed.

End Examples.
(* end hide *)
