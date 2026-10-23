(* begin hide *)
From stdpp Require Import sets gmap gmultiset countable numbers.
From Stdlib Require Uint63.

From TestingTheory Require Import VACCS.Testing.ta_tc_gen DefinitionAS Equivalence Must Lift
  ParallelLTSConstruction InteractionBetweenLts Bisimulation
  ActTau InputOutputActions Convergence
  gLts Lts_OBA FiniteImageLTS Testing_Predicate Completeness Lts_FW Lts_OBA_FB MultisetLTSConstruction
  SetLTSConstruction ForwarderConstruction.
From TestingTheory Require Import coFiniteImage coConvergence coWeakTransition DefinitionASrel
  CompletenessASco EquivalenceASco TestSpecBridge SyncActions
  VACCS.Language.gLts_Instance VACCS.Language.Label_Abstraction VACCS.Characterisations.Must_Characterisation
  Label_Abstraction.LabelAbstraction Label_Abstraction.Decidable_dichotomic Subset_Act
  Computing_Tools.Search_Helpers Computing_Tools.Acceptance_Tests_Gamma Computing_Tools.Bounded_Convergence.

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
        apply lts_performs_spec2. by exists r. }
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

(* Compares the co-actions offered by two forwarder states. *)
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

(* A test passed by [p ▷ ∅] and failed by [q ▷ ∅] refutes [p ⊑ₘᵤₛₜᵢ q]. *)
Lemma distinguishing_test_refutes (p q t : proc) :
  (p ▷ ∅) must_pass t → ¬ (q ▷ ∅) must_pass t → p ⋢ₘᵤₛₜᵢ q.
Proof. intros hp hq hpre%lift_fw_ctx_pre. exact (hq (hpre t hp)). Qed.

(* First case: the convergence test. *)
Lemma gen_conv_distinguishes (p q : FW) (s : trace A) :
  p ⇓ᶜᵒ s → ¬ q ⇓ᶜᵒ s → p must_pass (gen_conv s) ∧ ¬ q must_pass (gen_conv s).
Proof.
  intros hp hq. split.
  - by apply must_iff_cocnv.
  - intros hm. by apply hq, must_iff_cocnv.
Qed.

(* For a stable state [q'] of [q] after [s]: either a stable state of [p] after [s]
   offers no more co-actions than [q'], or a set [X] of co-actions refused by [q'] meets
   every stable state of [p] after [s]. *)
Definition acc_witness (p : FW) (s : trace A) (hp : p ⇓ᶜᵒ s) (q' : FW) (st : q' ↛) :
  { p' | p ⟹ᶜᵒ[s] p' ∧ p' ↛ ∧ ⌈ Γᴠᴀᴄᴄꜱ ⌉ (coR p') ⊆ ⌈ Γᴠᴀᴄᴄꜱ ⌉ (coR q') }
  + { X : gset (ChannelData + ChannelData) | (∀ x, x ∈ X → x ∉ ⌈ Γᴠᴀᴄᴄꜱ ⌉ (coR q'))
        ∧ (∀ p', p ⟹ᶜᵒ[s] p' → p' ↛ → ∃ x, x ∈ X ∧ x ∈ ⌈ Γᴠᴀᴄᴄꜱ ⌉ (coR p')) }.
Proof.
  destruct (included_or_witnesses (elements (cowaiting_states p s hp))
              (λ p', ⌈ Γᴠᴀᴄᴄꜱ ⌉ (coR p')) (⌈ Γᴠᴀᴄᴄꜱ ⌉ (coR q')))
    as [(p' & mem & sub) | (X & hXC & hXS)].
  - intros p' mem. exact (coR_dichotomy_Γ p' q').
  - left. exists p'.
    destruct (cowaiting_states_spec1 _ _ _ _ (proj1 (elem_of_elements _ _) mem)) as [w' st'].
    split_and!; [exact w' | exact st' | exact sub].
  - right. exists X. split; [exact hXC |].
    intros p' w' st'. apply hXS, elem_of_elements, cowaiting_states_spec2. split; [exact w' | exact st'].
Defined.

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

(* An acceptance test passed by [p] and failed by [q], with its co-trace. *)
Definition distinguishing_pair (p q : FW) : Type :=
  { sX : trace A * gset (ChannelData + ChannelData) |
    p must_pass (ta_Γ sX.2 sX.1) ∧ ¬ q must_pass (ta_Γ sX.2 sX.1) }.

(* Looks for an acceptance test among the stable states [l] of [q] after [s]. *)
Fixpoint distinguish_in (p q : FW) (s : trace A) (hp : p ⇓ᶜᵒ s) (l : list FW) :
  (∀ q', q' ∈ l → q ⟹ᶜᵒ[s] q' ∧ q' ↛) →
  option { X : gset (ChannelData + ChannelData) | p must_pass (ta_Γ X s) ∧ ¬ q must_pass (ta_Γ X s) } :=
  match l with
  | [] => λ _, None
  | q' :: l' => λ hl,
      match acc_witness p s hp q' (proj2 (hl q' (list_elem_of_here q' l'))) with
      | inl _ => distinguish_in p q s hp l' (λ x m, hl x (list_elem_of_further x q' l' m))
      | inr (exist _ X hX) =>
          Some (exist _ X (ta_distinguishes p q q' s hp X
                             (proj1 (hl q' (list_elem_of_here q' l')))
                             (proj2 (hl q' (list_elem_of_here q' l')))
                             (proj1 hX) (proj2 hX)))
      end
  end.

(* Looks for an acceptance test along a given co-trace [s]. *)
Definition distinguish_at (p q : FW) (s : trace A) (hp : p ⇓ᶜᵒ s) (hq : q ⇓ᶜᵒ s) :
  option { X : gset (ChannelData + ChannelData) | p must_pass (ta_Γ X s) ∧ ¬ q must_pass (ta_Γ X s) } :=
  distinguish_in p q s hp (elements (cowaiting_states q s hq))
    (λ q' m, cowaiting_states_spec1 _ _ _ _ (proj1 (elem_of_elements _ _) m)).

Lemma distinguish_in_none (p q : FW) (s : trace A) (hp : p ⇓ᶜᵒ s) (l : list FW) hl :
  distinguish_in p q s hp l hl = None →
  ∀ q', q' ∈ l → ∃ p', p ⟹ᶜᵒ[s] p' ∧ p' ↛ ∧ ⌈ Γᴠᴀᴄᴄꜱ ⌉ (coR p') ⊆ ⌈ Γᴠᴀᴄᴄꜱ ⌉ (coR q').
Proof.
  induction l as [| q0 l IH]; simpl.
  - intros _ q' m. inversion m.
  - destruct (acc_witness p s hp q0 _) as [(p' & hp') | (X & hX)]; [| discriminate].
    intros hnone q' [-> | m]%elem_of_cons.
    + exists p'. exact hp'.
    + exact (IH _ hnone q' m).
Qed.

Lemma distinguish_at_none (p q : FW) (s : trace A) (hp : p ⇓ᶜᵒ s) (hq : q ⇓ᶜᵒ s) :
  distinguish_at p q s hp hq = None →
  ∀ q', q ⟹ᶜᵒ[s] q' → q' ↛ → ∃ p', p ⟹ᶜᵒ[s] p' ∧ p' ↛ ∧ ⌈ Γᴠᴀᴄᴄꜱ ⌉ (coR p') ⊆ ⌈ Γᴠᴀᴄᴄꜱ ⌉ (coR q').
Proof.
  intros hnone q' w st. eapply (distinguish_in_none p q s hp _ _ hnone).
  apply elem_of_elements, cowaiting_states_spec2. split; [exact w | exact st].
Qed.

(* The alternative preorder on the forwarder, restricted to the co-traces of length at
   most [n] over [alphabet]. *)
Definition bounded_co_preorder (alphabet : list A) (n : nat) (p q : FW) : Prop :=
  ∀ s, s ∈ traces_upto alphabet n →
    (p ⇓ᶜᵒ s → q ⇓ᶜᵒ s) ∧
    (∀ q', p ⇓ᶜᵒ s → q ⟹ᶜᵒ[s] q' → q' ↛ →
       ∃ p', p ⟹ᶜᵒ[s] p' ∧ p' ↛ ∧ ⌈ Γᴠᴀᴄᴄꜱ ⌉ (coR p') ⊆ ⌈ Γᴠᴀᴄᴄꜱ ⌉ (coR q')).

Definition decide_in (k : nat) (p q : FW) : ∀ l : list (trace A),
  bounded_answer (A := A)
    (∀ s, s ∈ l → (p ⇓ᶜᵒ s → q ⇓ᶜᵒ s) ∧
       (∀ q', p ⇓ᶜᵒ s → q ⟹ᶜᵒ[s] q' → q' ↛ →
          ∃ p', p ⟹ᶜᵒ[s] p' ∧ p' ↛ ∧ ⌈ Γᴠᴀᴄᴄꜱ ⌉ (coR p') ⊆ ⌈ Γᴠᴀᴄᴄꜱ ⌉ (coR q')))
    (distinguishing_pair p q).
Proof.
  induction l as [| s l IH].
  - apply Holds. intros s m. inversion m.
  - destruct (cocnv_within k p s) eqn:ep; [| exact (Timeout s true)].
    destruct (cocnv_within k q s) eqn:eq; [| exact (Timeout s false)].
    pose proof (cocnv_within_sound k p s ep) as hp.
    pose proof (cocnv_within_sound k q s eq) as hq.
    destruct (distinguish_at p q s hp hq) as [[X h] |] eqn:ed.
    + exact (Distinguished (exist _ (s, X) h)).
    + destruct IH as [H | d | s' b].
      * apply Holds. intros s0 [-> | m]%elem_of_cons.
        -- split; [intros _; exact hq |].
           intros q' _ w st. exact (distinguish_at_none p q s hp hq ed q' w st).
        -- exact (H s0 m).
      * exact (Distinguished d).
      * exact (Timeout s' b).
Defined.

(* Decision for the processes [p] and [q], through their forwarders [p ▷ ∅] and [q ▷ ∅],
   with convergence checked within [k] τ-steps. *)
Definition decide_co_preorder (alphabet : list A) (n k : nat) (p q : proc) :
  bounded_answer (A := A) (bounded_co_preorder alphabet n (p ▷ ∅) (q ▷ ∅))
    (distinguishing_pair (p ▷ ∅) (q ▷ ∅)) :=
  decide_in k (p ▷ ∅) (q ▷ ∅) (traces_upto alphabet n).

Definition co_preorder_verdict (alphabet : list A) (n k : nat) (p q : proc) : verdict A proc :=
  match decide_co_preorder alphabet n k p q with
  | Holds _ => V_holds
  | Distinguished (exist _ (s, X) _) => V_distinguished s (ta_Γ X s)
  | Timeout s b => V_timeout s b
  end.

Definition co_preorder_holds (alphabet : list A) (n k : nat) (p q : proc) : bool :=
  match decide_co_preorder alphabet n k p q with
  | Holds _ => true
  | _ => false
  end.

Lemma co_preorder_holds_spec (alphabet : list A) (n k : nat) (p q : proc) :
  co_preorder_holds alphabet n k p q = true → bounded_co_preorder alphabet n (p ▷ ∅) (q ▷ ∅).
Proof.
  unfold co_preorder_holds.
  destruct (decide_co_preorder alphabet n k p q) as [h | | ]; [done | discriminate | discriminate].
Qed.

Definition co_preorder_refuted (alphabet : list A) (n k : nat) (p q : proc) : bool :=
  match decide_co_preorder alphabet n k p q with
  | Distinguished _ => true
  | _ => false
  end.

(* A distinguishing test found by the decision refutes the must preorder. *)
Lemma co_preorder_refuted_spec (alphabet : list A) (n k : nat) (p q : proc) :
  co_preorder_refuted alphabet n k p q = true → p ⋢ₘᵤₛₜᵢ q.
Proof.
  unfold co_preorder_refuted.
  destruct (decide_co_preorder alphabet n k p q) as [| [[s X] [h1 h2]] |]; [discriminate | | discriminate].
  intros _. exact (distinguishing_test_refutes p q _ h1 h2).
Qed.

(* From a proof that the bounded preorder fails: the distinguishing test, or a co-trace
   along which the convergence check ran out of steps. *)
Definition co_test_of_not_bounded (alphabet : list A) (n k : nat) (p q : proc)
  (H : ¬ bounded_co_preorder alphabet n (p ▷ ∅) (q ▷ ∅)) :
  distinguishing_pair (p ▷ ∅) (q ▷ ∅) + (trace A * bool).
Proof.
  destruct (decide_co_preorder alphabet n k p q) as [h | d | s b].
  - exfalso. exact (H h).
  - left. exact d.
  - right. exact (s, b).
Defined.

Lemma Γ_incl_of_ρ_incl (S S' : subset_of A) :
  ⌈ ρ[𝔸ᴠᴀᴄᴄꜱ] ⌉ S ⊆ ⌈ ρ[𝔸ᴠᴀᴄᴄꜱ] ⌉ S' → ⌈ Γᴠᴀᴄᴄꜱ ⌉ S ⊆ ⌈ Γᴠᴀᴄᴄꜱ ⌉ S'.
Proof.
  intros h x (μ & hμ & ->).
  destruct (h (ρ[𝔸ᴠᴀᴄᴄꜱ] μ)) as (μ' & hμ' & e); [by exists μ |].
  exists μ'. split; [exact hμ' |].
  apply (LA_proj_spec (R := label_ker 𝔸ᴠᴀᴄᴄꜱ) (f := Γᴠᴀᴄᴄꜱ)).
  apply (LA_proj_spec (R := label_ker 𝔸ᴠᴀᴄᴄꜱ) (f := ρ[𝔸ᴠᴀᴄᴄꜱ])). exact e.
Qed.

(* The alternative preorder implies each of its restrictions. *)
Lemma bounded_of_co_preorder (alphabet : list A) (n : nat) (p q : FW) :
  p ≼꜀ₒ₋ₐₛ[ ρ[𝔸ᴠᴀᴄᴄꜱ] ] q → bounded_co_preorder alphabet n p q.
Proof.
  intros [hc ha] s _. split; [exact (hc s) |].
  intros q' hps w st. destruct (ha s q' hps w st) as (p' & w' & st' & sub).
  exists p'. split_and!; [exact w' | exact st' | by apply Γ_incl_of_ρ_incl].
Qed.

Corollary not_preorder_of_not_bounded_co (alphabet : list A) (n : nat) (p q : proc) :
  ¬ bounded_co_preorder alphabet n (p ▷ ∅) (q ▷ ∅) → p ⋢ₘᵤₛₜᵢ q.
Proof.
  intros hn h%must_iff_co_acceptance_set_VACCS.
  exact (hn (bounded_of_co_preorder alphabet n _ _ h)).
Qed.

(* ** Bounded search with convergence assumed

   The convergence of the forwarders [p ▷ ∅] and [q ▷ ∅] along every co-trace is given
   by the hypotheses [hp] and [hq]: only the acceptance part of the preorder is
   searched. *)

Fixpoint search_in (p q : FW) (hp : ∀ s : trace A, p ⇓ᶜᵒ s) (hq : ∀ s : trace A, q ⇓ᶜᵒ s)
  (l : list (trace A)) : option (distinguishing_pair p q) :=
  match l with
  | [] => None
  | s :: l' =>
      match distinguish_at p q s (hp s) (hq s) with
      | Some (exist _ X h) => Some (exist _ (s, X) h)
      | None => search_in p q hp hq l'
      end
  end.

(* Bounded search: the first co-trace of length at most [n] along which an acceptance
   test distinguishes [p ▷ ∅] from [q ▷ ∅]. *)
Definition search_distinguishing_test (alphabet : list A) (n : nat) (p q : proc)
  (hp : ∀ s : trace A, (p ▷ ∅) ⇓ᶜᵒ s) (hq : ∀ s : trace A, (q ▷ ∅) ⇓ᶜᵒ s) :
  option (distinguishing_pair (p ▷ ∅) (q ▷ ∅)) :=
  search_in (p ▷ ∅) (q ▷ ∅) hp hq (traces_upto alphabet n).

(* The acceptance part of the alternative preorder on the forwarder, restricted to the
   co-traces of length at most [n] over [alphabet]. *)
Definition bounded_acc_preorder (alphabet : list A) (n : nat) (p q : FW) : Prop :=
  ∀ s, s ∈ traces_upto alphabet n → ∀ q', p ⇓ᶜᵒ s → q ⟹ᶜᵒ[s] q' → q' ↛ →
    ∃ p', p ⟹ᶜᵒ[s] p' ∧ p' ↛ ∧ ⌈ Γᴠᴀᴄᴄꜱ ⌉ (coR p') ⊆ ⌈ Γᴠᴀᴄᴄꜱ ⌉ (coR q').

Lemma search_in_none (p q : FW) (hp : ∀ s : trace A, p ⇓ᶜᵒ s) (hq : ∀ s : trace A, q ⇓ᶜᵒ s)
  (l : list (trace A)) :
  search_in p q hp hq l = None → ∀ s, s ∈ l → distinguish_at p q s (hp s) (hq s) = None.
Proof.
  induction l as [| s0 l IH]; simpl.
  - intros _ s m. inversion m.
  - destruct (distinguish_at p q s0 (hp s0) (hq s0)) as [[X h] |] eqn:e; [discriminate |].
    intros hnone s [-> | m]%elem_of_cons; [exact e | exact (IH hnone s m)].
Qed.

(* Completeness of the bounded search: when it fails, the bounded preorder holds. *)
Lemma search_complete (alphabet : list A) (n : nat) (p q : proc)
  (hp : ∀ s : trace A, (p ▷ ∅) ⇓ᶜᵒ s) (hq : ∀ s : trace A, (q ▷ ∅) ⇓ᶜᵒ s) :
  search_distinguishing_test alphabet n p q hp hq = None →
  bounded_acc_preorder alphabet n (p ▷ ∅) (q ▷ ∅).
Proof.
  intros hnone s m q' _ w st.
  exact (distinguish_at_none _ _ s (hp s) (hq s) (search_in_none _ _ hp hq _ hnone s m) q' w st).
Qed.

(* From a proof that the bounded preorder fails, the distinguishing test. *)
Definition test_of_not_bounded (alphabet : list A) (n : nat) (p q : proc)
  (hp : ∀ s : trace A, (p ▷ ∅) ⇓ᶜᵒ s) (hq : ∀ s : trace A, (q ▷ ∅) ⇓ᶜᵒ s)
  (H : ¬ bounded_acc_preorder alphabet n (p ▷ ∅) (q ▷ ∅)) :
  distinguishing_pair (p ▷ ∅) (q ▷ ∅).
Proof.
  destruct (search_distinguishing_test alphabet n p q hp hq) as [x |] eqn:e.
  - exact x.
  - exfalso. exact (H (search_complete alphabet n p q hp hq e)).
Defined.

(* Decision of the bounded preorder: either it holds, or a distinguishing test. *)
Definition decide_bounded_preorder (alphabet : list A) (n : nat) (p q : proc)
  (hp : ∀ s : trace A, (p ▷ ∅) ⇓ᶜᵒ s) (hq : ∀ s : trace A, (q ▷ ∅) ⇓ᶜᵒ s) :
  bounded_acc_preorder alphabet n (p ▷ ∅) (q ▷ ∅) + distinguishing_pair (p ▷ ∅) (q ▷ ∅).
Proof.
  destruct (search_distinguishing_test alphabet n p q hp hq) as [x |] eqn:e.
  - right. exact x.
  - left. exact (search_complete alphabet n p q hp hq e).
Defined.

(* The verdict without the proofs: [None] when the bounded preorder holds, otherwise
   the co-trace and the distinguishing test. *)
Definition bounded_verdict (alphabet : list A) (n : nat) (p q : proc)
  (hp : ∀ s : trace A, (p ▷ ∅) ⇓ᶜᵒ s) (hq : ∀ s : trace A, (q ▷ ∅) ⇓ᶜᵒ s) :
  option (trace A * proc) :=
  match decide_bounded_preorder alphabet n p q hp hq with
  | inl _ => None
  | inr (exist _ (s, X) _) => Some (s, ta_Γ X s)
  end.

Definition bounded_preorder_holds (alphabet : list A) (n : nat) (p q : proc)
  (hp : ∀ s : trace A, (p ▷ ∅) ⇓ᶜᵒ s) (hq : ∀ s : trace A, (q ▷ ∅) ⇓ᶜᵒ s) : bool :=
  match decide_bounded_preorder alphabet n p q hp hq with
  | inl _ => true
  | inr _ => false
  end.

Lemma bounded_preorder_holds_spec (alphabet : list A) (n : nat) (p q : proc)
  (hp : ∀ s : trace A, (p ▷ ∅) ⇓ᶜᵒ s) (hq : ∀ s : trace A, (q ▷ ∅) ⇓ᶜᵒ s) :
  bounded_preorder_holds alphabet n p q hp hq = true →
  bounded_acc_preorder alphabet n (p ▷ ∅) (q ▷ ∅).
Proof.
  unfold bounded_preorder_holds.
  destruct (decide_bounded_preorder alphabet n p q hp hq) as [h | _]; [done | discriminate].
Qed.

(* The alternative preorder implies each of its bounded restrictions. *)
Lemma bounded_of_acc_preorder (alphabet : list A) (n : nat) (p q : FW) :
  p ₐ꜀꜀≼꜀ₒ₋ₐₛ[ ρ[𝔸ᴠᴀᴄᴄꜱ] ] q → bounded_acc_preorder alphabet n p q.
Proof.
  intros h s _ q' hps w st. destruct (h s q' hps w st) as (p' & w' & st' & sub).
  exists p'. split_and!; [exact w' | exact st' | by apply Γ_incl_of_ρ_incl].
Qed.

Corollary not_preorder_of_not_bounded (alphabet : list A) (n : nat) (p q : proc) :
  ¬ bounded_acc_preorder alphabet n (p ▷ ∅) (q ▷ ∅) → p ⋢ₘᵤₛₜᵢ q.
Proof.
  intros hn h%must_iff_co_acceptance_set_VACCS.
  destruct h as [_ h]. exact (hn (bounded_of_acc_preorder alphabet n _ _ h)).
Qed.

(* The co-trace and the test found, without the proofs (for display). *)
Definition distinguishing_test (alphabet : list A) (n : nat) (p q : proc)
  (hp : ∀ s : trace A, (p ▷ ∅) ⇓ᶜᵒ s) (hq : ∀ s : trace A, (q ▷ ∅) ⇓ᶜᵒ s) :
  option (trace A * proc) :=
  match search_distinguishing_test alphabet n p q hp hq with
  | Some (exist _ (s, X) _) => Some (s, ta_Γ X s)
  | None => None
  end.

(* Whether the search succeeds, as a boolean (cheap to compute). *)
Definition search_succeeds (alphabet : list A) (n : nat) (p q : proc)
  (hp : ∀ s : trace A, (p ▷ ∅) ⇓ᶜᵒ s) (hq : ∀ s : trace A, (q ▷ ∅) ⇓ᶜᵒ s) : bool :=
  match search_distinguishing_test alphabet n p q hp hq with
  | Some _ => true
  | None => false
  end.

Lemma search_refutes (alphabet : list A) (n : nat) (p q : proc)
  (hp : ∀ s : trace A, (p ▷ ∅) ⇓ᶜᵒ s) (hq : ∀ s : trace A, (q ▷ ∅) ⇓ᶜᵒ s) :
  search_succeeds alphabet n p q hp hq = true → p ⋢ₘᵤₛₜᵢ q.
Proof.
  unfold search_succeeds.
  destruct (search_distinguishing_test alphabet n p q hp hq) as [[[s X] [h1 h2]] |]; [| discriminate].
  intros _. exact (distinguishing_test_refutes p q _ h1 h2).
Qed.

End VACCS_Distinguishing_Test.

Section Examples.

Import Uint63.

#[local] Instance int63_eq_dec : EqDecision int := Uint63.eqs.
#[local] Instance int63_countable : Countable int := inj_countable' to_Z of_Z of_to_Z.

(* Channels are natural numbers, values are 63-bit machine integers. *)
#[local] Instance VACCS_int63 : VACCS_Parameters := {| Channel := nat; Value := int; O := 0%uint63 |}.

(* [q1] may silently refuse to emit on channel [0]: the test receiving on [0] and then
   succeeding is passed by [p1 ▷ ∅] and failed by [q1 ▷ ∅], with the empty co-trace. *)
Definition p1 : proc := cst 0 ! cst 0%uint63 • 𝟘.
Definition q1 : proc := g ((𝛕 • (cst 0 ! cst 0%uint63 • 𝟘)) + (𝛕 • g 𝟘)).

Example p1_q1_verdict :
  co_preorder_verdict [] 0 5 p1 q1 = V_distinguished [] (g ((cst 0 ? • g ①) + 𝟘)).
Proof. vm_compute. reflexivity. Qed.

Example p1_not_below_q1 : p1 ⋢ₘᵤₛₜᵢ q1.
Proof. apply (co_preorder_refuted_spec (VP := VACCS_int63) [] 0 5). vm_compute. reflexivity. Qed.

Lemma q1_below_p1_bounded : bounded_co_preorder (VP := VACCS_int63) [] 0 (q1 ▷ ∅) (p1 ▷ ∅).
Proof. apply (co_preorder_holds_spec _ _ 5). vm_compute. reflexivity. Qed.

(* Inputs are not observed: the forwarder accepts every message, so a process waiting for a
   message behaves as [g 𝟘], in both directions. *)
Definition r1 : proc := g (cst 0 ? • g 𝟘).

Example r1_below_nil : co_preorder_verdict [] 0 5 r1 (g 𝟘) = V_holds.
Proof. vm_compute. reflexivity. Qed.

Example nil_below_r1 : co_preorder_verdict [] 0 5 (g 𝟘) r1 = V_holds.
Proof. vm_compute. reflexivity. Qed.

(* After receiving on [2], [p3] emits on [0] while [q3] may stop: along the co-trace [2!0],
   the message sent by the test waits in the mailbox of the forwarder until [p3] or [q3]
   consumes it. The test emits on [2] and waits on [0]. *)
Definition p3 : proc := g (cst 2 ? • (cst 0 ! cst 0%uint63 • 𝟘)).
Definition q3 : proc := g (cst 2 ? • g ((𝛕 • (cst 0 ! cst 0%uint63 • 𝟘)) + (𝛕 • g 𝟘))).

Example p3_q3_verdict :
  co_preorder_verdict [ActOut (cst 2, cst 0%uint63)] 1 5 p3 q3
  = V_distinguished [ActOut (cst 2, cst 0%uint63)]
      ((cst 2 ! cst 0%uint63 • 𝟘) ‖ g ((cst 0 ? • g ①) + 𝟘)).
Proof. vm_compute. reflexivity. Qed.

Example p3_not_below_q3 : p3 ⋢ₘᵤₛₜᵢ q3.
Proof.
  apply (co_preorder_refuted_spec (VP := VACCS_int63) [ActOut (cst 2, cst 0%uint63)] 1 5).
  vm_compute. reflexivity.
Qed.

Example q3_below_p3 : co_preorder_verdict [ActOut (cst 2, cst 0%uint63)] 1 5 q3 p3 = V_holds.
Proof. vm_compute. reflexivity. Qed.

(* A process that diverges: the convergence check runs out of steps. *)
Definition ω : proc := rec 0 • (pr_var 0).

Example ω_timeout : co_preorder_verdict [] 0 5 ω p1 = V_timeout [] true.
Proof. vm_compute. reflexivity. Qed.

(* With convergence assumed (here as hypotheses): the bounded search, no τ-step bound. *)
#[local] Instance SyncAction_ex : SyncAction (ExtAct TypeOfActions) (ExtAct TypeOfActions) :=
  SyncAction_of_dual.

Variable hp1 : ∀ s : trace (ExtAct TypeOfActions), (p1 ▷ ∅ : proc * MO (ExtAct TypeOfActions)) ⇓ᶜᵒ s.
Variable hq1 : ∀ s : trace (ExtAct TypeOfActions), (q1 ▷ ∅ : proc * MO (ExtAct TypeOfActions)) ⇓ᶜᵒ s.

Example p1_q1_test : distinguishing_test [] 0 p1 q1 hp1 hq1 = Some ([], g ((cst 0 ? • g ①) + 𝟘)).
Proof. vm_compute. reflexivity. Qed.

Example p1_not_below_q1_search : p1 ⋢ₘᵤₛₜᵢ q1.
Proof. apply (search_refutes (VP := VACCS_int63) [] 0 p1 q1 hp1 hq1). vm_compute. reflexivity. Qed.

(* The distinguishing test computed from a (here hypothetical) proof that the bounded
   preorder fails: the proof is never inspected when the search succeeds. *)
Variable not_bounded1 : ¬ bounded_acc_preorder (VP := VACCS_int63) [] 0 (p1 ▷ ∅) (q1 ▷ ∅).

Example p1_q1_test_of_not_bounded :
  let '(s, X) := proj1_sig (test_of_not_bounded [] 0 p1 q1 hp1 hq1 not_bounded1) in
  (s, ta_Γ X s) = ([], g ((cst 0 ? • g ①) + 𝟘)).
Proof. vm_compute. reflexivity. Qed.

Lemma q1_below_p1_acc : bounded_acc_preorder (VP := VACCS_int63) [] 0 (q1 ▷ ∅) (p1 ▷ ∅).
Proof. apply (bounded_preorder_holds_spec _ _ _ _ hq1 hp1). vm_compute. reflexivity. Qed.

Variable hp3 : ∀ s : trace (ExtAct TypeOfActions), (p3 ▷ ∅ : proc * MO (ExtAct TypeOfActions)) ⇓ᶜᵒ s.
Variable hq3 : ∀ s : trace (ExtAct TypeOfActions), (q3 ▷ ∅ : proc * MO (ExtAct TypeOfActions)) ⇓ᶜᵒ s.

Example p3_q3_test :
  distinguishing_test [ActOut (cst 2, cst 0%uint63)] 1 p3 q3 hp3 hq3
  = Some ([ActOut (cst 2, cst 0%uint63)], (cst 2 ! cst 0%uint63 • 𝟘) ‖ g ((cst 0 ? • g ①) + 𝟘)).
Proof. vm_compute. reflexivity. Qed.

End Examples.
(* end hide *)
