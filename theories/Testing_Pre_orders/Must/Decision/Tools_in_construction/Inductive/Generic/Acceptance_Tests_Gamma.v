(* begin hide *)
From Stdlib Require ssreflect Setoid.
From Stdlib Require Import Unicode.Utf8 List.
From Stdlib.Program Require Import Wf Equality.
From stdpp Require Import sets base countable finite gmap list decidable.
From stdpp Require gmultiset.
From TestingTheory Require Import ActTau SyncActions gLts Bisimulation Lts_OBA
  WeakTransitions Lts_OBA_FB Lts_FW FiniteImageLTS
  InteractionBetweenLts MultisetLTSConstruction
  ParallelLTSConstruction ForwarderConstruction
  Must Lift Subset_Act Convergence Termination
  Testing_Predicate DefinitionAS Lts_Finite_Non_Blocking_Chain
  coWeakTransition coConvergence coFiniteImage DefinitionASrel LtsFW
  Label_Abstraction.LabelAbstraction Label_Abstraction.Decidable_dichotomic
  CompletenessASco.
Import ListNotations.

(* Acceptance tests indexed by a projection [Γ] with the kernel of [𝔸] *)

Section Acceptance_Tests_Γ.

Context {P : Type}.
Context `{gLtsEqP : @gLtsEq P A H} `{!LtsFW P A}.
Context `{gLtsObaT : @gLtsOba T A H gLtsEqT}.
Context `{!Prop_of_Inter P T A A dual}.
Context (𝔸 : Label_abstraction P T).
Context {PreAct : Type} `{CC : Countable PreAct} (Γ : A → PreAct).
Context `{!LA_proj (label_ker 𝔸) Γ} `{!LA_surj Γ}.
Context `{!Testing_Predicate outcome _}.
Context `{!test_co_acceptance_set_spec ta Γ}.

#[local] Existing Instance LA_class_proj.

(* The representative of a class and any of its elements have the same [Γ]-value. *)
Lemma Γ_repr_class μ : Γ (proj1_sig (ρ[𝔸] μ)) = Γ μ.
Proof.
  apply (LA_proj_spec (R := label_ker 𝔸) (f := Γ)).
  apply (LA_proj_spec (R := label_ker 𝔸) (f := ρ[𝔸])).
  exact (LA_repr_spec (LA_surj := LA_class_surj (label_ker 𝔸)) (ρ[𝔸] μ)).
Qed.

Lemma ρ_of_Γ_eq μ μ' : Γ μ = Γ μ' → ρ[𝔸] μ = ρ[𝔸] μ'.
Proof.
  intros h. apply (LA_proj_spec (R := label_ker 𝔸) (f := ρ[𝔸])).
  by apply (LA_proj_spec (R := label_ker 𝔸) (f := Γ)).
Qed.

Lemma class_repr (y : A / 𝔸) : ρ[𝔸] (`y) = y.
Proof. exact (LA_repr_spec (LA_surj := LA_class_surj (label_ker 𝔸)) y). Qed.

(* The class of a [Γ]-value. *)
Definition class_of_pre (x : PreAct) : A / 𝔸 := ρ[𝔸] (LA_repr x).

Lemma Γ_class_of_pre x : Γ (proj1_sig (class_of_pre x)) = x.
Proof. unfold class_of_pre. rewrite Γ_repr_class. apply LA_repr_spec. Qed.

(* The test indexed by classes, through the [Γ]-values of their representatives. *)
Definition ta_ρ (E : gset (A / 𝔸)) (s : trace A) : T :=
  ta (set_map (λ y : A / 𝔸, Γ (`y)) E) s.

#[local] Instance ta_ρ_spec : test_co_acceptance_set_spec ta_ρ ρ[𝔸].
Proof.
  split; unfold ta_ρ.
  - intros E. apply ta_test_spec.
  - intros E. apply ta_does_no_tau.
  - intros E η nb. by apply ta_does_no_non_blocking_actions.
  - intros E β e b h.
    apply (ta_actions_are_in_its_gamma_set _ β e b), elem_of_map in h as (y & hy & hyE).
    rewrite (ρ_of_Γ_eq β (`y) hy), class_repr. exact hyE.
  - intros E pβ hpβ (β & b & hβ).
    destruct (ta_has_a_representative_transition_for_its_gamma_set
                (set_map (λ y : A / 𝔸, Γ (`y)) E) (Γ (`pβ))) as (r & β' & tr & e).
    + apply elem_of_map. by exists pβ.
    + exists β. split; [exact b |]. rewrite <- hβ. symmetry. apply Γ_repr_class.
    + exists r, β'. split; [exact tr |].
      rewrite (ρ_of_Γ_eq β' (`pβ) e). apply class_repr.
  - intros β e' E b h. exact (ta_transition_to_good β e' _ b h).
Qed.

(* [must_ta_for_all_trace_co] of [CompletenessASco], for tests indexed by [Γ]-values. *)
Lemma must_ta_for_all_trace_co_Γ s (p : P) (hcocnv : p ⇓ᶜᵒ s) (X : gset PreAct) :
  (∀ p', p ⟹ᶜᵒ[s] p' → p' ↛ → ∃ x, x ∈ X ∧ x ∈ ⌈ Γ ⌉ (coR p')) →
  p must_pass (ta X s).
Proof.
  intros hX.
  assert (set_map (λ y : A / 𝔸, Γ (`y)) (set_map class_of_pre X : gset (A / 𝔸)) = X) as heq.
  { apply leibniz_equiv, set_equiv. intros x. rewrite !elem_of_map. split.
    - intros (y & -> & hy). apply elem_of_map in hy as (x' & -> & hx').
      by rewrite Γ_class_of_pre.
    - intros hx. exists (class_of_pre x).
      split; [symmetry; apply Γ_class_of_pre | apply elem_of_map; by exists x]. }
  rewrite <- heq. change (p must_pass (ta_ρ (set_map class_of_pre X) s)).
  apply (must_ta_for_all_trace_co 𝔸 s p hcocnv).
  intros p' w st. destruct (hX p' w st) as (x & hx & (μ & hμ & ->)).
  exists (class_of_pre (Γ μ)). split; [apply elem_of_map; by exists (Γ μ) |].
  exists μ. split; [exact hμ |].
  unfold class_of_pre. apply ρ_of_Γ_eq, LA_repr_spec.
Qed.

End Acceptance_Tests_Γ.
(* end hide *)
