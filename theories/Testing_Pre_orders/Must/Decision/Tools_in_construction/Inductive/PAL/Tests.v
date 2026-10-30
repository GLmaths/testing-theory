(* begin hide *)
From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base countable gmap list sets.
From TestingTheory Require Import ActTau gLts Bisimulation SyncActions Must RelationKernel Subset_Act
  Lts_OBA Lts_FW Lts_OBA_FB LtsFW InteractionBetweenLts Testing_Predicate
  coFiniteImage coConvergence coWeakTransition DefinitionASrel CompletenessASco
  Label_Abstraction.LabelAbstraction
  PAL.Language.Syntax PAL.Language.LTS PAL.Language.Phi PAL.Language.AbsAction PAL.Language.Congruence
  PAL.Language.Dichotomy PAL.Language.Label_Abstraction PAL_Good PAL.Testing.Must_Preorder
  PAL.Testing.Tests PAL.Testing.Test_Spec PAL.Testing.CoTrace_Hypotheses
  Decision.Tools_in_construction.Inductive.Generic.Acceptance_Tests_Gamma.
Import ListNotations.

(* Computing a test that distinguishes two processes of the alternative LTS of PAL. *)
#[local] Hint Mode ExtAction ! : typeclass_instances.

Section PAL_Distinguishing_Test.

Notation proc := (term nat).
Notation A := (PALA_Act nat).

(* The event of a label. *)
Notation Γᴘᴀʟ := (λ μ : A, αᴘᴇᴠ nat (αᴛᴀᴘᴀʟ nat μ)).

#[local] Instance LtsFW_PAL : LtsFW proc A := LtsFW_of_gLtsObaFW (H0 := hyp_gLtsObaFW nat).
#[local] Instance t_conv_PAL : CompletenessASco.test_convergence_spec (t_conv nat) :=
  hyp_test_convergence_spec nat.
#[local] Instance ta_PAL : CompletenessASco.test_co_acceptance_set_spec (ta nat) Γᴘᴀʟ :=
  hyp_test_co_acceptance_set_spec nat.

#[local] Existing Instance LA_class_proj.

(* [Γᴘᴀʟ] identifies the same labels as [ρ[𝔸ᴘᴀʟ]]. *)
#[local] Instance LA_proj_PAL : LA_proj (label_ker 𝔸ᴘᴀʟ) Γᴘᴀʟ.
Proof.
  intros μ μ'. transitivity (ρ[𝔸ᴘᴀʟ] μ = ρ[𝔸ᴘᴀʟ] μ').
  - symmetry. apply ρᴘᴀʟ_eq.
  - apply (LA_proj_spec (R := label_ker 𝔸ᴘᴀʟ) (f := ρ[𝔸ᴘᴀʟ])).
Qed.

(* Each event is the event of a label. *)
#[local] Instance LA_surj_PAL : LA_surj Γᴘᴀʟ :=
  {| LA_repr := repr_ev; LA_repr_spec := repr_ev_spec |}.

(* A test passed by [p] and failed by [q] refutes [p ᴘᴀʟ⊑ₘᵤₛₜᵢ q]. *)
Lemma distinguishing_test_refutes (p q t : proc) :
  p must_pass t → ¬ q must_pass t → ¬ p ᴘᴀʟ⊑ₘᵤₛₜᵢ q.
Proof. intros hp hq hpre. exact (hq (hpre t hp)). Qed.

(* [must_iff_cocnv] for PAL, with the instances given explicitly (as in
   [PAL_Alt_equivalence]): left to instance search, they make it diverge. *)
Lemma must_iff_cocnv_PAL (p : proc) (s : trace A) : p must_pass (t_conv nat s) ↔ p ⇓ᶜᵒ s.
Proof.
  exact (must_iff_cocnv (gLtsEqP := PALA_gLtsEq nat) (LtsFW0 := LtsFW_PAL)
           (gLtsEqT := PALA_gLtsEq nat) (gLtsObaT := hyp_gLtsOba nat) (outcome := good_PAL nat)
           (Testing_Predicate0 := hyp_Testing_Predicate nat) (tconv := t_conv nat)
           (test_convergence_spec0 := t_conv_PAL) (Prop_of_Inter0 := hyp_Prop_of_Inter nat) p s).
Qed.

(* Second case: the acceptance test of the paper. *)
Lemma ta_distinguishes (p q q' : proc) (s : trace A) (hp : p ⇓ᶜᵒ s) (X : gset (Event nat)) :
  q ⟹ᶜᵒ[s] q' → q' ↛ →
  (∀ x, x ∈ X → x ∉ ⌈ Γᴘᴀʟ ⌉ (coR q')) →
  (∀ p', p ⟹ᶜᵒ[s] p' → p' ↛ → ∃ x, x ∈ X ∧ x ∈ ⌈ Γᴘᴀʟ ⌉ (coR p')) →
  p must_pass (ta nat X s) ∧ ¬ q must_pass (ta nat X s).
Proof.
  intros w st hXC hXS. split.
  - exact (must_ta_for_all_trace_co_Γ (gLtsEqP := PALA_gLtsEq nat) (LtsFW0 := LtsFW_PAL)
             (gLtsEqT := PALA_gLtsEq nat) (gLtsObaT := hyp_gLtsOba nat)
             (Prop_of_Inter0 := hyp_Prop_of_Inter nat) 𝔸ᴘᴀʟ Γᴘᴀʟ
             (LA_proj0 := LA_proj_PAL) (LA_surj0 := LA_surj_PAL) (outcome := good_PAL nat)
             (Testing_Predicate0 := hyp_Testing_Predicate nat) (ta := ta nat)
             (test_co_acceptance_set_spec0 := ta_PAL) s p hp X hXS).
  - exact (not_must_ta_without_required_acc_set (gLtsQ := PALA_gLts nat)
             (gLtsEqT := PALA_gLtsEq nat) (gLtsObaT := hyp_gLtsOba nat) (outcome := good_PAL nat)
             (Testing_Predicate0 := hyp_Testing_Predicate nat) (Γ := Γᴘᴀʟ) (ta := ta nat)
             (test_co_acceptance_set_spec0 := ta_PAL) q q' s X w st hXC).
Qed.

End PAL_Distinguishing_Test.
(* end hide *)
