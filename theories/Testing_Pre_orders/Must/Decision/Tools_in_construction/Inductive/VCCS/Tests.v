(* begin hide *)
From stdpp Require Import sets gmap gmultiset countable numbers.

From TestingTheory Require Import VCCS.Testing.ta_tc_gen DefinitionAS Equivalence Must
  ParallelLTSConstruction InteractionBetweenLts Bisimulation
  ActTau InputOutputActions Convergence
  gLts Lts_OBA FiniteImageLTS Testing_Predicate Completeness Lts_FW Lts_OBA_FB MultisetLTSConstruction
  SetLTSConstruction ForwarderConstruction.
From TestingTheory Require Import coFiniteImage coConvergence coWeakTransition DefinitionASrel
  CompletenessASco EquivalenceASco TestSpecBridge SyncActions
  VCCS.Language.gLts_Instance VCCS.Language.Label_Abstraction
  Label_Abstraction.LabelAbstraction Label_Abstraction.Decidable_dichotomic Subset_Act
  Decision.Tools_in_construction.Inductive.Generic.Acceptance_Tests_Gamma.

(* Computing a test that distinguishes two VCCS processes. *)

Section VCCS_Distinguishing_Test.

Context `{VP : VCCS_Parameters}.

#[local] Instance SyncAction_VCCS : SyncAction (ExtAct TypeOfActions) (ExtAct TypeOfActions) :=
  SyncAction_of_dual.

Notation A := (ExtAct TypeOfActions).

(* The projection of an action onto its channel and direction. *)
Notation Γᴠᴄᴄꜱ := (λ μ : A, αᴘᴠᴄᴄꜱ (αᴛᴠᴄᴄꜱ μ)).

(* A test passed by [p] and failed by [q] refutes [p ⊑ₘᵤₛₜᵢ q]. *)
Lemma distinguishing_test_refutes (p q t : proc) :
  p must_pass t → ¬ q must_pass t → p ⋢ₘᵤₛₜᵢ q.
Proof. intros hp hq hpre. exact (hq (hpre t hp)). Qed.

Lemma PreCoAct_of_spec (p : proc) x : x ∈ PreCoAct_of p ↔ x ∈ ⌈ Γᴠᴄᴄꜱ ⌉ (coR p).
Proof.
  split.
  - apply (coR_abs_spec1 (FinitaryAbsAction := FinitaryAbsVCCS)).
  - apply (coR_abs_spec2 (FinitaryAbsAction := FinitaryAbsVCCS)).
Qed.

(* Compares the co-actions offered by two states. *)
(* Each pre-action is the projection of an action. *)
#[local] Instance LA_surj_VCCS : LA_surj Γᴠᴄᴄꜱ :=
  {| LA_repr := repr_pre_vccs; LA_repr_spec := ρᴠᴄᴄꜱ_repr |}.

(* Second case: the acceptance test. *)
Lemma gen_acc_distinguishes (p q q' : proc) (s : trace A) (hp : p ⇓ᶜᵒ s) (X : gset PreAct) :
  q ⟹ᶜᵒ[s] q' → q' ↛ →
  (∀ x, x ∈ X → x ∉ ⌈ Γᴠᴄᴄꜱ ⌉ (coR q')) →
  (∀ p', p ⟹ᶜᵒ[s] p' → p' ↛ → ∃ x, x ∈ X ∧ x ∈ ⌈ Γᴠᴄᴄꜱ ⌉ (coR p')) →
  p must_pass (gen_acc X s) ∧ ¬ q must_pass (gen_acc X s).
Proof.
  intros w st hXC hXS. split.
  - exact (must_ta_for_all_trace_co_Γ 𝔸ᴠᴄᴄꜱ Γᴠᴄᴄꜱ (ta := gen_acc) s p hp X hXS).
  - exact (not_must_ta_without_required_acc_set q q' s X w st hXC).
Qed.

End VCCS_Distinguishing_Test.
(* end hide *)
