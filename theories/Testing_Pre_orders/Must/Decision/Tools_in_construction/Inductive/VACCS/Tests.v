(* begin hide *)
From stdpp Require Import sets gmap gmultiset countable numbers.

From TestingTheory Require Import VACCS.Testing.ta_tc_gen DefinitionAS Equivalence Must Lift
  ParallelLTSConstruction InteractionBetweenLts Bisimulation
  ActTau InputOutputActions Convergence
  gLts Lts_OBA FiniteImageLTS Testing_Predicate Completeness Lts_FW Lts_OBA_FB MultisetLTSConstruction
  SetLTSConstruction ForwarderConstruction.
From TestingTheory Require Import coFiniteImage coConvergence coWeakTransition DefinitionASrel
  CompletenessASco EquivalenceASco TestSpecBridge SyncActions
  VACCS.Language.gLts_Instance VACCS.Language.Label_Abstraction VACCS.Characterisations.Must_Characterisation
  Label_Abstraction.LabelAbstraction Label_Abstraction.Decidable_dichotomic Subset_Act
  Decision.Tools_in_construction.Inductive.Generic.Acceptance_Tests_Gamma.

(* Computing a test that distinguishes two VACCS processes.  *)

Section VACCS_Distinguishing_Test.

Context `{VP : VACCS_Parameters}.

#[local] Instance SyncAction_VACCS : SyncAction (ExtAct TypeOfActions) (ExtAct TypeOfActions) :=
  SyncAction_of_dual.

Notation A := (ExtAct TypeOfActions).
Notation FW := (proc * MO A)%type.

(* The channel and direction of an action. *)
Definition Γᴠᴀᴄᴄꜱ (μ : A) : ChannelData + ChannelData :=
  match μ with
  | ActIn (c , _) => inl c
  | ActOut (c , _) => inr c
  end.

#[local] Existing Instance LA_class_proj.

#[local] Instance LA_proj_VACCS : LA_proj (label_ker 𝔸ᴠᴀᴄᴄꜱ) Γᴠᴀᴄᴄꜱ.
Proof.
  intros μ μ'. transitivity (ρ[𝔸ᴠᴀᴄᴄꜱ] μ = ρ[𝔸ᴠᴀᴄᴄꜱ] μ');
    [| apply (LA_proj_spec (R := label_ker 𝔸ᴠᴀᴄᴄꜱ) (f := ρ[𝔸ᴠᴀᴄᴄꜱ]))].
  split.
  - intros h. apply class_eq_vaccs.
    destruct μ as [[c v]|[c v]], μ' as [[c' v']|[c' v']]; simpl in *; congruence.
  - intros h%class_eq_vaccs_inv.
    destruct μ as [[c v]|[c v]], μ' as [[c' v']|[c' v']]; simpl in *;
      first [contradiction | by subst].
Qed.

#[local] Instance LA_surj_VACCS : LA_surj Γᴠᴀᴄᴄꜱ.
Proof.
  refine {| LA_repr x := match x with inl c => ActIn (c , cst O) | inr c => ActOut (c , cst O) end |}.
  by intros [c|c].
Defined.

(* The acceptance test indexed by channels and directions: only the inputs count, as
   they are the blocking actions of VACCS. *)
Definition pre_of (X : gset (ChannelData + ChannelData)) : gset PreAct :=
  list_to_set (omap (λ x, match x with inl c => Some (Inputs c) | inr _ => None end) (elements X)).

Lemma elem_of_pre_of X c : Inputs c ∈ pre_of X ↔ inl c ∈ X.
Proof.
  unfold pre_of. rewrite elem_of_list_to_set, list_elem_of_omap. split.
  - intros ([c'|c'] & hx & e); [| discriminate]. injection e as ->. by apply elem_of_elements.
  - intros hx. exists (inl c). split; [by apply elem_of_elements | done].
Qed.

Definition ta_Γ (X : gset (ChannelData + ChannelData)) (s : trace A) : proc := gen_acc (pre_of X) s.

#[local] Instance ta_Γ_spec : CompletenessASco.test_co_acceptance_set_spec ta_Γ Γᴠᴀᴄᴄꜱ.
Proof.
  split; unfold ta_Γ.
  - intros E. apply ta_test_spec.
  - intros E. apply ta_does_no_tau.
  - intros E η nb. by apply ta_does_no_non_blocking_actions.
  - intros E β e b h.
    pose proof (ta_actions_are_in_its_gamma_set (Γ := λ x, αᴘᴠᴀᴄᴄꜱ (αᴛᴠᴀᴄᴄꜱ x)) _ β e b h) as hm.
    destruct (blocking_is_input β b) as ([c v] & ->). simpl in hm |- *.
    by apply elem_of_pre_of.
  - intros E pβ hpβ (β & b & hβ).
    destruct (blocking_is_input β b) as ([c v] & ->). simpl in hβ. subst pβ.
    destruct (ta_has_a_representative_transition_for_its_gamma_set (Γ := λ x, αᴘᴠᴀᴄᴄꜱ (αᴛᴠᴀᴄᴄꜱ x))
                (pre_of E) (Inputs c)) as (r & β' & tr & e).
    + by apply elem_of_pre_of.
    + exists (ActIn (c , v)). split; [exact b | reflexivity].
    + exists r, β'. split; [exact tr |].
      assert (blocking β') as b'.
      { intros nb. eapply (ta_does_no_non_blocking_actions (Γ := λ x, αᴘᴠᴀᴄᴄꜱ (αᴛᴠᴀᴄᴄꜱ x))
                             (pre_of E) β' nb).
        apply lts_may_perform_spec2. by exists r. }
      destruct (blocking_is_input β' b') as ([c' v'] & ->). simpl in e |- *.
      by injection e as ->.
  - intros β e' E b h. exact (ta_transition_to_good (Γ := λ x, αᴘᴠᴀᴄᴄꜱ (αᴛᴠᴀᴄᴄꜱ x)) β e' _ b h).
Qed.

(* The co-actions of a forwarder state, as channels and directions. *)
Definition sum_of_pre (x : PreAct) : ChannelData + ChannelData :=
  match x with Inputs c => inl c end.

Definition coR_Γ (pm : FW) : gset (ChannelData + ChannelData) :=
  set_map sum_of_pre (PreCoAct_of pm.1)
  ∪ set_map (λ η, Γᴠᴀᴄᴄꜱ (co η)) (dom (MO_without_not_nb pm.2)).

Lemma coR_Γ_spec (pm : FW) x : x ∈ coR_Γ pm ↔ x ∈ ⌈ Γᴠᴀᴄᴄꜱ ⌉ (coR pm).
Proof.
  destruct pm as (p, m). unfold coR_Γ. simpl. rewrite elem_of_union, !elem_of_map. split.
  - intros [(pre & -> & hpre) | (η & -> & hη)].
    + apply (coR_abs_spec1 (FinitaryAbsAction := FinitaryAbsVACCS)) in hpre as (μ & hμ & ->).
      exists μ. split.
      * apply coR_fw. by left.
      * destruct hμ as (? & ? & ? & b). by destruct (blocking_is_input μ b) as ([c v] & ->).
    + apply gmultiset_elem_of_dom in hη.
      assert (hη' : η ∈ (MO_without_not_nb (m : MO A) : MO A)) by exact hη.
      apply lts_MO_nb_with_nb_spec1 in hη' as (nb & hη').
      exists (co η). split; [| done]. apply coR_fw. right. by exists η.
  - intros (μ & hμ & ->). pose proof (coR_blocking _ _ hμ) as b.
    apply coR_fw in hμ as [hμ | (η & nb & hη & ->)].
    + left. exists (αᴘᴠᴀᴄᴄꜱ (αᴛᴠᴀᴄᴄꜱ μ)). split.
      * by destruct (blocking_is_input μ b) as ([c v] & ->).
      * apply (coR_abs_spec2 (FinitaryAbsAction := FinitaryAbsVACCS)). by exists μ.
    + right. exists η. split; [done |].
      apply gmultiset_elem_of_dom.
      assert (h' : η ∈ (MO_without_not_nb (m : MO A) : MO A)) by (by apply lts_MO_nb_with_nb_spec2).
      exact h'.
Qed.

(* A test passed by [p ▷ ∅] and failed by [q ▷ ∅] refutes [p ⊑ₘᵤₛₜᵢ q]. *)
Lemma distinguishing_test_refutes (p q t : proc) :
  (p ▷ ∅) must_pass t → ¬ (q ▷ ∅) must_pass t → p ⋢ₘᵤₛₜᵢ q.
Proof. intros hp hq hpre%lift_fw_ctx_pre. exact (hq (hpre t hp)). Qed.

(* Second case: the acceptance test. *)
Lemma ta_distinguishes (p q q' : FW) (s : trace A) (hp : p ⇓ᶜᵒ s) (X : gset (ChannelData + ChannelData)) :
  q ⟹ᶜᵒ[s] q' → q' ↛ →
  (∀ x, x ∈ X → x ∉ ⌈ Γᴠᴀᴄᴄꜱ ⌉ (coR q')) →
  (∀ p', p ⟹ᶜᵒ[s] p' → p' ↛ → ∃ x, x ∈ X ∧ x ∈ ⌈ Γᴠᴀᴄᴄꜱ ⌉ (coR p')) →
  p must_pass (ta_Γ X s) ∧ ¬ q must_pass (ta_Γ X s).
Proof.
  intros w st hXC hXS. split.
  - exact (must_ta_for_all_trace_co_Γ 𝔸ᴠᴀᴄᴄꜱ Γᴠᴀᴄᴄꜱ (ta := ta_Γ) s p hp X hXS).
  - exact (not_must_ta_without_required_acc_set q q' s X w st hXC).
Qed.

End VACCS_Distinguishing_Test.
(* end hide *)
