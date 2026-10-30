(* begin hide *)
From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import sets gmap gmultiset countable numbers list.
From TestingTheory Require Import VACCS.Testing.ta_tc_gen DefinitionAS Equivalence Must Lift
  ParallelLTSConstruction InteractionBetweenLts Bisimulation
  ActTau InputOutputActions Convergence
  gLts Lts_OBA FiniteImageLTS Testing_Predicate Completeness Lts_FW Lts_OBA_FB MultisetLTSConstruction
  SetLTSConstruction ForwarderConstruction.
From TestingTheory Require Import coFiniteImage coConvergence coWeakTransition DefinitionASrel
  CompletenessASco EquivalenceASco TestSpecBridge SyncActions
  VACCS.Language.LTS VACCS.Language.gLts_Instance VACCS.Language.Label_Abstraction
  VACCS.Characterisations.Must_Characterisation
  Label_Abstraction.LabelAbstraction Label_Abstraction.Decidable_dichotomic Subset_Act
  Decision.Computing_Tools.Bounded_Search.
Import ListNotations.

Section VACCS_Bounded.

Context `{VP : VACCS_Parameters}.

#[local] Instance SyncAction_VACCS : SyncAction (ExtAct TypeOfActions) (ExtAct TypeOfActions) :=
  SyncAction_of_dual.

Notation A := (ExtAct TypeOfActions).
Notation FW := (proc * MO A)%type.

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

Definition coR_dichotomy_Γ (p' q' : FW) :
  (⌈ Γᴠᴀᴄᴄꜱ ⌉ (coR p') ⊆ ⌈ Γᴠᴀᴄᴄꜱ ⌉ (coR q'))
  + { x | x ∈ ⌈ Γᴠᴀᴄᴄꜱ ⌉ (coR p') ∧ x ∉ ⌈ Γᴠᴀᴄᴄꜱ ⌉ (coR q') }.
Proof.
  destruct (elements (coR_Γ p' ∖ coR_Γ q')) as [|x l] eqn:e.
  - left. intros x hx%coR_Γ_spec. apply coR_Γ_spec.
    destruct (decide (x ∈ coR_Γ q')) as [h | h]; [exact h |].
    assert (x ∈ elements (coR_Γ p' ∖ coR_Γ q')) as mem
      by (apply elem_of_elements; set_solver).
    rewrite e in mem. inversion mem.
  - right. exists x.
    assert (x ∈ coR_Γ p' ∖ coR_Γ q') as hx
      by (apply elem_of_elements; rewrite e; apply list_elem_of_here).
    split.
    + apply coR_Γ_spec. set_solver.
    + intros h%coR_Γ_spec. set_solver.
Defined.


#[local] Instance Dichotomic_Γᴠᴀᴄᴄꜱ : Dichotomic FW Γᴠᴀᴄᴄꜱ := λ p' q' _ _, coR_dichotomy_Γ p' q'.

Definition vaccs_bounded_preorder (alphabet : list A) (n : nat) (p q : proc) : Prop :=
  bounded_co_preorder Γᴠᴀᴄᴄꜱ alphabet n (p ▷ ∅) (q ▷ ∅).

Definition vaccs_bounded (alphabet : list A) (n k : nat) (p q : proc) :=
  bounded_verdict Γᴠᴀᴄᴄꜱ alphabet n k (p ▷ ∅) (q ▷ ∅).

Theorem vaccs_bounded_holds alphabet n k (p q : proc) :
  vaccs_bounded alphabet n k p q = B_holds → vaccs_bounded_preorder alphabet n p q.
Proof. exact (bounded_verdict_holds Γᴠᴀᴄᴄꜱ alphabet n k (p ▷ ∅) (q ▷ ∅)). Qed.

Theorem vaccs_bounded_test alphabet n k (p q : proc) s E :
  vaccs_bounded alphabet n k p q = B_distinguished s E →
  (p ▷ ∅) must_pass (ta_Γ E s) ∧ ¬ (q ▷ ∅) must_pass (ta_Γ E s).
Proof. exact (bounded_verdict_distinguishes 𝔸ᴠᴀᴄᴄꜱ Γᴠᴀᴄᴄꜱ (ta := ta_Γ) alphabet n k (p ▷ ∅) (q ▷ ∅) s E). Qed.

Corollary vaccs_bounded_refutes alphabet n k (p q : proc) s E :
  vaccs_bounded alphabet n k p q = B_distinguished s E → p ⋢ₘᵤₛₜᵢ q.
Proof.
  intros e hpre%lift_fw_ctx_pre. destruct (vaccs_bounded_test alphabet n k p q s E e) as [hp hq].
  exact (hq (hpre _ hp)).
Qed.

Definition vaccs_holds_b (alphabet : list A) (n k : nat) (p q : proc) : bool :=
  bounded_holds_b Γᴠᴀᴄᴄꜱ alphabet n k (p ▷ ∅) (q ▷ ∅).

Theorem vaccs_holds_b_spec alphabet n k (p q : proc) :
  vaccs_holds_b alphabet n k p q = true → vaccs_bounded_preorder alphabet n p q.
Proof. exact (bounded_holds_b_spec Γᴠᴀᴄᴄꜱ alphabet n k (p ▷ ∅) (q ▷ ∅)). Qed.

Definition vaccs_refuted_b (alphabet : list A) (n k : nat) (p q : proc) : bool :=
  bounded_refuted_b Γᴠᴀᴄᴄꜱ alphabet n k (p ▷ ∅) (q ▷ ∅).

Corollary vaccs_refuted_b_spec alphabet n k (p q : proc) :
  vaccs_refuted_b alphabet n k p q = true → p ⋢ₘᵤₛₜᵢ q.
Proof.
  unfold vaccs_refuted_b, bounded_refuted_b. fold (vaccs_bounded alphabet n k p q).
  destruct (vaccs_bounded alphabet n k p q) as [| s E |] eqn:e; try discriminate.
  intros _. exact (vaccs_bounded_refutes alphabet n k p q s E e).
Qed.

Corollary vaccs_bounded_of_must alphabet n (p q : proc) :
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q → vaccs_bounded_preorder alphabet n p q.
Proof.
  intros h%must_iff_co_acceptance_set_VACCS.
  exact (bounded_of_co_preorder 𝔸ᴠᴀᴄᴄꜱ Γᴠᴀᴄᴄꜱ alphabet n (p ▷ ∅) (q ▷ ∅) h).
Qed.

Definition vaccs_test_of_not_bounded (alphabet : list A) (n k : nat) (p q : proc) (hn : ¬ vaccs_bounded_preorder alphabet n p q) :=
  bounded_test_of_not 𝔸ᴠᴀᴄᴄꜱ Γᴠᴀᴄᴄꜱ (ta := ta_Γ) alphabet n k (p ▷ ∅) (q ▷ ∅) hn.

End VACCS_Bounded.

#[global] Instance VACCS_nat : VACCS_Parameters := {| Channel := nat; Value := nat; O := 0 |}.

Section VACCS_Bounded_nat.

Notation A := (ExtAct (@TypeOfActions VACCS_nat)).

Definition chan_of (c : ChannelData) : list nat := match c with cst c => [c] | bvar _ => [] end.

Fixpoint chans (p : proc) : list nat :=
  match p with
  | pr_par p1 p2 => chans p1 ++ chans p2
  | pr_var _ => []
  | pr_rec _ p => chans p
  | pr_if_then_else _ p1 p2 => chans p1 ++ chans p2
  | pr_output c _ => chan_of c
  | pr_restrict p => chans p
  | g gp => gchans gp
  end
with gchans (gp : gproc) : list nat :=
  match gp with
  | gpr_success | gpr_nil => []
  | gpr_input c p => chan_of c ++ chans p
  | gpr_tau p => chans p
  | gpr_choice g1 g2 => gchans g1 ++ gchans g2
  end.

Definition vaccs_alphabet (b : nat) (q : proc) : list A :=
  flat_map (λ c, flat_map (λ v, [ActIn (cst c, cst v); ActOut (cst c, cst v)]) (seq 0 (2 ^ b)))
    (remove_dups (chans q)).

Definition vaccs_bounded_preorder_nat (b n : nat) (p q : proc) : Prop :=
  vaccs_bounded_preorder (vaccs_alphabet b q) n p q.

Definition vaccs_bounded_nat (b n k : nat) (p q : proc) :=
  vaccs_bounded (vaccs_alphabet b q) n k p q.

Definition vaccs_holds_nat (b n k : nat) (p q : proc) : bool :=
  vaccs_holds_b (vaccs_alphabet b q) n k p q.

Theorem vaccs_holds_nat_spec b n k (p q : proc) :
  vaccs_holds_nat b n k p q = true → vaccs_bounded_preorder_nat b n p q.
Proof. exact (vaccs_holds_b_spec (vaccs_alphabet b q) n k p q). Qed.

Definition vaccs_refuted_nat (b n k : nat) (p q : proc) : bool :=
  vaccs_refuted_b (vaccs_alphabet b q) n k p q.

Theorem vaccs_refuted_nat_spec b n k (p q : proc) :
  vaccs_refuted_nat b n k p q = true → p ⋢ₘᵤₛₜᵢ q.
Proof. exact (vaccs_refuted_b_spec (vaccs_alphabet b q) n k p q). Qed.

Theorem vaccs_bounded_nat_test b n k (p q : proc) s E :
  vaccs_bounded_nat b n k p q = B_distinguished s E →
  (p ▷ ∅) must_pass (ta_Γ E s) ∧ ¬ (q ▷ ∅) must_pass (ta_Γ E s).
Proof. exact (vaccs_bounded_test (vaccs_alphabet b q) n k p q s E). Qed.

Corollary vaccs_bounded_nat_of_must b n (p q : proc) :
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q → vaccs_bounded_preorder_nat b n p q.
Proof. exact (vaccs_bounded_of_must (vaccs_alphabet b q) n p q). Qed.

Definition vaccs_test_of_not_bounded_nat (b n k : nat) (p q : proc) (hn : ¬ vaccs_bounded_preorder_nat b n p q) :=
  vaccs_test_of_not_bounded (vaccs_alphabet b q) n k p q hn.

End VACCS_Bounded_nat.

Section Examples.

Definition p1 : proc := cst 0 ! cst 0 • 𝟘.
Definition q1 : proc := g ((𝛕 • (cst 0 ! cst 0 • 𝟘)) + (𝛕 • g 𝟘)).

Example p1_q1_verdict :
  match vaccs_bounded_nat 0 0 5 p1 q1 with B_distinguished s E => Some (s, elements E) | _ => None end
  = Some ([], [inl (cst 0)]).
Proof. vm_compute. reflexivity. Qed.

Theorem p1_not_below_q1 : p1 ⋢ₘᵤₛₜᵢ q1.
Proof. apply (vaccs_refuted_nat_spec 0 0 5). vm_compute. reflexivity. Qed.

Lemma q1_below_p1_bounded : vaccs_bounded_preorder_nat 0 0 q1 p1.
Proof. apply (vaccs_holds_nat_spec 0 0 5). vm_compute. reflexivity. Qed.

End Examples.
(* end hide *)
