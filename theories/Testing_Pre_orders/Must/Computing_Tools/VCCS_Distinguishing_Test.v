(* begin hide *)
From stdpp Require Import sets gmap gmultiset countable numbers.
From Stdlib Require Uint63.

From TestingTheory Require Import VCCS.Testing.ta_tc_gen DefinitionAS Equivalence Must
  ParallelLTSConstruction InteractionBetweenLts Bisimulation
  ActTau InputOutputActions Convergence
  gLts Lts_OBA FiniteImageLTS Testing_Predicate Completeness Lts_FW Lts_OBA_FB MultisetLTSConstruction
  SetLTSConstruction ForwarderConstruction.
From TestingTheory Require Import coFiniteImage coConvergence coWeakTransition DefinitionASrel
  CompletenessASco EquivalenceASco TestSpecBridge SyncActions
  VCCS.Language.gLts_Instance VCCS.Language.Label_Abstraction
  Label_Abstraction.LabelAbstraction Label_Abstraction.Decidable_dichotomic Subset_Act
  Computing_Tools.Search_Helpers Computing_Tools.Acceptance_Tests_Gamma Computing_Tools.Bounded_Convergence.

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

(* First case: the convergence test. *)
Lemma gen_conv_distinguishes (p q : proc) (s : trace A) :
  p ⇓ᶜᵒ s → ¬ q ⇓ᶜᵒ s → p must_pass (gen_conv s) ∧ ¬ q must_pass (gen_conv s).
Proof.
  intros hp hq. split.
  - by apply must_iff_cocnv.
  - intros hm. by apply hq, must_iff_cocnv.
Qed.

Lemma PreCoAct_of_spec (p : proc) x : x ∈ PreCoAct_of p ↔ x ∈ ⌈ Γᴠᴄᴄꜱ ⌉ (coR p).
Proof.
  split.
  - apply (coR_abs_spec1 (FinitaryAbsAction := FinitaryAbsVCCS)).
  - apply (coR_abs_spec2 (FinitaryAbsAction := FinitaryAbsVCCS)).
Qed.

(* Compares the co-actions offered by two states. *)
Definition pre_dichotomy (p' q' : proc) :
  (⌈ Γᴠᴄᴄꜱ ⌉ (coR p') ⊆ ⌈ Γᴠᴄᴄꜱ ⌉ (coR q'))
  + { x | x ∈ ⌈ Γᴠᴄᴄꜱ ⌉ (coR p') ∧ x ∉ ⌈ Γᴠᴄᴄꜱ ⌉ (coR q') }.
Proof.
  destruct (elements (PreCoAct_of p' ∖ PreCoAct_of q')) as [|x l] eqn:e.
  - left. intros x hx%PreCoAct_of_spec. apply PreCoAct_of_spec.
    destruct (decide (x ∈ PreCoAct_of q')) as [h | h]; [exact h |].
    assert (x ∈ elements (PreCoAct_of p' ∖ PreCoAct_of q')) as m
      by (apply elem_of_elements; set_solver).
    rewrite e in m. inversion m.
  - right. exists x.
    assert (x ∈ PreCoAct_of p' ∖ PreCoAct_of q') as hx
      by (apply elem_of_elements; rewrite e; apply list_elem_of_here).
    split.
    + apply PreCoAct_of_spec. set_solver.
    + intros h%PreCoAct_of_spec. set_solver.
Defined.

(* For a stable state [q'] of [q] after [s]: either a stable state of [p] after [s]
   offers no more than [q'], or a set [X] of co-actions refused by [q'] meets every
   stable state of [p] after [s]. *)
Definition acc_witness (p : proc) (s : trace A) (hp : p ⇓ᶜᵒ s) (q' : proc) (st : q' ↛) :
  { p' | p ⟹ᶜᵒ[s] p' ∧ p' ↛ ∧ ⌈ Γᴠᴄᴄꜱ ⌉ (coR p') ⊆ ⌈ Γᴠᴄᴄꜱ ⌉ (coR q') }
  + { X : gset PreAct | (∀ x, x ∈ X → x ∉ ⌈ Γᴠᴄᴄꜱ ⌉ (coR q'))
        ∧ (∀ p', p ⟹ᶜᵒ[s] p' → p' ↛ → ∃ x, x ∈ X ∧ x ∈ ⌈ Γᴠᴄᴄꜱ ⌉ (coR p')) }.
Proof.
  destruct (included_or_witnesses (elements (cowaiting_states p s hp))
              (λ p', ⌈ Γᴠᴄᴄꜱ ⌉ (coR p')) (⌈ Γᴠᴄᴄꜱ ⌉ (coR q')))
    as [(p' & mem & sub) | (X & hXC & hXS)].
  - intros p' mem. exact (pre_dichotomy p' q').
  - left. exists p'.
    destruct (cowaiting_states_spec1 _ _ _ _ (proj1 (elem_of_elements _ _) mem)) as [w' st'].
    split_and!; [exact w' | exact st' | exact sub].
  - right. exists X. split; [exact hXC |].
    intros p' w' st'. apply hXS, elem_of_elements, cowaiting_states_spec2. split; [exact w' | exact st'].
Defined.

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

(* Looks for an acceptance test among the stable states [l] of [q] after [s]. *)
Fixpoint distinguish_in (p q : proc) (s : trace A) (hp : p ⇓ᶜᵒ s) (l : list proc) :
  (∀ q', q' ∈ l → q ⟹ᶜᵒ[s] q' ∧ q' ↛) →
  option { X : gset PreAct | p must_pass (gen_acc X s) ∧ ¬ q must_pass (gen_acc X s) } :=
  match l with
  | [] => λ _, None
  | q' :: l' => λ hl,
      match acc_witness p s hp q' (proj2 (hl q' (list_elem_of_here q' l'))) with
      | inl _ => distinguish_in p q s hp l' (λ x m, hl x (list_elem_of_further x q' l' m))
      | inr (exist _ X hX) =>
          Some (exist _ X (gen_acc_distinguishes p q q' s hp X
                             (proj1 (hl q' (list_elem_of_here q' l')))
                             (proj2 (hl q' (list_elem_of_here q' l')))
                             (proj1 hX) (proj2 hX)))
      end
  end.

(* Looks for an acceptance test along a given co-trace [s]. *)
Definition distinguish_at (p q : proc) (s : trace A) (hp : p ⇓ᶜᵒ s) (hq : q ⇓ᶜᵒ s) :
  option { X : gset PreAct | p must_pass (gen_acc X s) ∧ ¬ q must_pass (gen_acc X s) } :=
  distinguish_in p q s hp (elements (cowaiting_states q s hq))
    (λ q' m, cowaiting_states_spec1 _ _ _ _ (proj1 (elem_of_elements _ _) m)).

(* When no test is found, every stable state of [q] in [l] is dominated by one of [p]. *)
Lemma distinguish_in_none (p q : proc) (s : trace A) (hp : p ⇓ᶜᵒ s) (l : list proc) hl :
  distinguish_in p q s hp l hl = None →
  ∀ q', q' ∈ l → ∃ p', p ⟹ᶜᵒ[s] p' ∧ p' ↛ ∧ ⌈ Γᴠᴄᴄꜱ ⌉ (coR p') ⊆ ⌈ Γᴠᴄᴄꜱ ⌉ (coR q').
Proof.
  induction l as [| q0 l IH]; simpl.
  - intros _ q' m. inversion m.
  - destruct (acc_witness p s hp q0 _) as [(p' & hp') | (X & hX)]; [| discriminate].
    intros hnone q' [-> | m]%elem_of_cons.
    + exists p'. exact hp'.
    + exact (IH _ hnone q' m).
Qed.

Lemma distinguish_at_none (p q : proc) (s : trace A) (hp : p ⇓ᶜᵒ s) (hq : q ⇓ᶜᵒ s) :
  distinguish_at p q s hp hq = None →
  ∀ q', q ⟹ᶜᵒ[s] q' → q' ↛ → ∃ p', p ⟹ᶜᵒ[s] p' ∧ p' ↛ ∧ ⌈ Γᴠᴄᴄꜱ ⌉ (coR p') ⊆ ⌈ Γᴠᴄᴄꜱ ⌉ (coR q').
Proof.
  intros hnone q' w st. eapply (distinguish_in_none p q s hp _ _ hnone).
  apply elem_of_elements, cowaiting_states_spec2. split; [exact w | exact st].
Qed.

Fixpoint search_in (p q : proc) (hp : ∀ s, p ⇓ᶜᵒ s) (hq : ∀ s, q ⇓ᶜᵒ s) (l : list (trace A)) :
  option { sX : trace A * gset PreAct |
           p must_pass (gen_acc sX.2 sX.1) ∧ ¬ q must_pass (gen_acc sX.2 sX.1) } :=
  match l with
  | [] => None
  | s :: l' =>
      match distinguish_at p q s (hp s) (hq s) with
      | Some (exist _ X h) => Some (exist _ (s, X) h)
      | None => search_in p q hp hq l'
      end
  end.

(* Bounded search: the first co-trace of length at most [n] along which an acceptance
   test distinguishes [p] from [q]. *)
Definition search_distinguishing_test (alphabet : list A) (n : nat) (p q : proc)
  (hp : ∀ s, p ⇓ᶜᵒ s) (hq : ∀ s, q ⇓ᶜᵒ s) :
  option { sX : trace A * gset PreAct |
           p must_pass (gen_acc sX.2 sX.1) ∧ ¬ q must_pass (gen_acc sX.2 sX.1) } :=
  search_in p q hp hq (traces_upto alphabet n).

(* The acceptance part of the alternative preorder, restricted to the co-traces of
   length at most [n] over [alphabet]. *)
Definition bounded_acc_preorder (alphabet : list A) (n : nat) (p q : proc) : Prop :=
  ∀ s, s ∈ traces_upto alphabet n → ∀ q', p ⇓ᶜᵒ s → q ⟹ᶜᵒ[s] q' → q' ↛ →
    ∃ p', p ⟹ᶜᵒ[s] p' ∧ p' ↛ ∧ ⌈ Γᴠᴄᴄꜱ ⌉ (coR p') ⊆ ⌈ Γᴠᴄᴄꜱ ⌉ (coR q').

Lemma search_in_none (p q : proc) (hp : ∀ s, p ⇓ᶜᵒ s) (hq : ∀ s, q ⇓ᶜᵒ s) (l : list (trace A)) :
  search_in p q hp hq l = None → ∀ s, s ∈ l → distinguish_at p q s (hp s) (hq s) = None.
Proof.
  induction l as [| s0 l IH]; simpl.
  - intros _ s m. inversion m.
  - destruct (distinguish_at p q s0 (hp s0) (hq s0)) as [[X h] |] eqn:e; [discriminate |].
    intros hnone s [-> | m]%elem_of_cons; [exact e | exact (IH hnone s m)].
Qed.

(* Completeness of the bounded search: when it fails, the bounded preorder holds. *)
Lemma search_complete (alphabet : list A) (n : nat) (p q : proc)
  (hp : ∀ s, p ⇓ᶜᵒ s) (hq : ∀ s, q ⇓ᶜᵒ s) :
  search_distinguishing_test alphabet n p q hp hq = None → bounded_acc_preorder alphabet n p q.
Proof.
  intros hnone s m q' _ w st.
  exact (distinguish_at_none p q s (hp s) (hq s) (search_in_none p q hp hq _ hnone s m) q' w st).
Qed.

(* From a proof that the bounded preorder fails, the distinguishing test. *)
Definition test_of_not_bounded (alphabet : list A) (n : nat) (p q : proc)
  (hp : ∀ s, p ⇓ᶜᵒ s) (hq : ∀ s, q ⇓ᶜᵒ s) (H : ¬ bounded_acc_preorder alphabet n p q) :
  { sX : trace A * gset PreAct |
    p must_pass (gen_acc sX.2 sX.1) ∧ ¬ q must_pass (gen_acc sX.2 sX.1) }.
Proof.
  destruct (search_distinguishing_test alphabet n p q hp hq) as [x |] eqn:e.
  - exact x.
  - exfalso. exact (H (search_complete alphabet n p q hp hq e)).
Defined.

(* Decision of the bounded preorder: either it holds, or a distinguishing test. *)
Definition decide_bounded_preorder (alphabet : list A) (n : nat) (p q : proc)
  (hp : ∀ s, p ⇓ᶜᵒ s) (hq : ∀ s, q ⇓ᶜᵒ s) :
  bounded_acc_preorder alphabet n p q
  + { sX : trace A * gset PreAct |
      p must_pass (gen_acc sX.2 sX.1) ∧ ¬ q must_pass (gen_acc sX.2 sX.1) }.
Proof.
  destruct (search_distinguishing_test alphabet n p q hp hq) as [x |] eqn:e.
  - right. exact x.
  - left. exact (search_complete alphabet n p q hp hq e).
Defined.

(* The verdict without the proofs: [None] when the bounded preorder holds, otherwise
   the co-trace and the distinguishing test. *)
Definition bounded_verdict (alphabet : list A) (n : nat) (p q : proc)
  (hp : ∀ s, p ⇓ᶜᵒ s) (hq : ∀ s, q ⇓ᶜᵒ s) : option (trace A * proc) :=
  match decide_bounded_preorder alphabet n p q hp hq with
  | inl _ => None
  | inr (exist _ (s, X) _) => Some (s, gen_acc X s)
  end.

Definition bounded_preorder_holds (alphabet : list A) (n : nat) (p q : proc)
  (hp : ∀ s, p ⇓ᶜᵒ s) (hq : ∀ s, q ⇓ᶜᵒ s) : bool :=
  match decide_bounded_preorder alphabet n p q hp hq with
  | inl _ => true
  | inr _ => false
  end.

Lemma bounded_preorder_holds_spec (alphabet : list A) (n : nat) (p q : proc)
  (hp : ∀ s, p ⇓ᶜᵒ s) (hq : ∀ s, q ⇓ᶜᵒ s) :
  bounded_preorder_holds alphabet n p q hp hq = true → bounded_acc_preorder alphabet n p q.
Proof.
  unfold bounded_preorder_holds.
  destruct (decide_bounded_preorder alphabet n p q hp hq) as [h | _]; [done | discriminate].
Qed.

(* ** Bounded decision with bounded convergence

   The two bounds are parameters: [n] for the length of the co-traces, [k] for the
   number of τ-steps allowed to converge (restarting after each action). No
   convergence hypothesis is needed: convergence is checked within [k] steps, and a
   process that does not converge in time is reported. *)

(* The alternative preorder restricted to the co-traces of length at most [n] over
   [alphabet]. *)
Definition bounded_co_preorder (alphabet : list A) (n : nat) (p q : proc) : Prop :=
  ∀ s, s ∈ traces_upto alphabet n →
    (p ⇓ᶜᵒ s → q ⇓ᶜᵒ s) ∧
    (∀ q', p ⇓ᶜᵒ s → q ⟹ᶜᵒ[s] q' → q' ↛ →
       ∃ p', p ⟹ᶜᵒ[s] p' ∧ p' ↛ ∧ ⌈ Γᴠᴄᴄꜱ ⌉ (coR p') ⊆ ⌈ Γᴠᴄᴄꜱ ⌉ (coR q')).

(* An acceptance test passed by [p] and failed by [q], with its co-trace. *)
Definition distinguishing_pair (p q : proc) : Type :=
  { sX : trace A * gset PreAct | p must_pass (gen_acc sX.2 sX.1) ∧ ¬ q must_pass (gen_acc sX.2 sX.1) }.

Definition decide_in (k : nat) (p q : proc) : ∀ l : list (trace A),
  bounded_answer (A := A)
    (∀ s, s ∈ l → (p ⇓ᶜᵒ s → q ⇓ᶜᵒ s) ∧
       (∀ q', p ⇓ᶜᵒ s → q ⟹ᶜᵒ[s] q' → q' ↛ →
          ∃ p', p ⟹ᶜᵒ[s] p' ∧ p' ↛ ∧ ⌈ Γᴠᴄᴄꜱ ⌉ (coR p') ⊆ ⌈ Γᴠᴄᴄꜱ ⌉ (coR q')))
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

Definition decide_co_preorder (alphabet : list A) (n k : nat) (p q : proc) :
  bounded_answer (A := A) (bounded_co_preorder alphabet n p q) (distinguishing_pair p q) :=
  decide_in k p q (traces_upto alphabet n).

Definition co_preorder_verdict (alphabet : list A) (n k : nat) (p q : proc) : verdict A proc :=
  match decide_co_preorder alphabet n k p q with
  | Holds _ => V_holds
  | Distinguished (exist _ (s, X) _) => V_distinguished s (gen_acc X s)
  | Timeout s b => V_timeout s b
  end.

Definition co_preorder_holds (alphabet : list A) (n k : nat) (p q : proc) : bool :=
  match decide_co_preorder alphabet n k p q with
  | Holds _ => true
  | _ => false
  end.

Lemma co_preorder_holds_spec (alphabet : list A) (n k : nat) (p q : proc) :
  co_preorder_holds alphabet n k p q = true → bounded_co_preorder alphabet n p q.
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

#[local] Existing Instance LA_class_proj.

Lemma Γ_incl_of_ρ_incl (S S' : subset_of A) :
  ⌈ ρ[𝔸ᴠᴄᴄꜱ] ⌉ S ⊆ ⌈ ρ[𝔸ᴠᴄᴄꜱ] ⌉ S' → ⌈ Γᴠᴄᴄꜱ ⌉ S ⊆ ⌈ Γᴠᴄᴄꜱ ⌉ S'.
Proof.
  intros h x (μ & hμ & ->).
  destruct (h (ρ[𝔸ᴠᴄᴄꜱ] μ)) as (μ' & hμ' & e); [by exists μ |].
  exists μ'. split; [exact hμ' |].
  apply (LA_proj_spec (R := label_ker 𝔸ᴠᴄᴄꜱ) (f := Γᴠᴄᴄꜱ)).
  apply (LA_proj_spec (R := label_ker 𝔸ᴠᴄᴄꜱ) (f := ρ[𝔸ᴠᴄᴄꜱ])). exact e.
Qed.

(* The alternative preorder implies each of its bounded restrictions. *)
Lemma bounded_of_acc_preorder (alphabet : list A) (n : nat) (p q : proc) :
  p ₐ꜀꜀≼꜀ₒ₋ₐₛ[ ρ[𝔸ᴠᴄᴄꜱ] ] q → bounded_acc_preorder alphabet n p q.
Proof.
  intros h s _ q' hps w st. destruct (h s q' hps w st) as (p' & w' & st' & sub).
  exists p'. split_and!; [exact w' | exact st' | by apply Γ_incl_of_ρ_incl].
Qed.

Corollary not_preorder_of_not_bounded (alphabet : list A) (n : nat) (p q : proc) :
  ¬ bounded_acc_preorder alphabet n p q → ¬ p ≼꜀ₒ₋ₐₛ[ ρ[𝔸ᴠᴄᴄꜱ] ] q.
Proof. intros hn [_ h]. exact (hn (bounded_of_acc_preorder alphabet n p q h)). Qed.

(* The alternative preorder implies each of its restrictions. *)
Lemma bounded_of_co_preorder (alphabet : list A) (n : nat) (p q : proc) :
  p ≼꜀ₒ₋ₐₛ[ ρ[𝔸ᴠᴄᴄꜱ] ] q → bounded_co_preorder alphabet n p q.
Proof.
  intros [hc ha] s _. split; [exact (hc s) |].
  intros q' hps w st. destruct (ha s q' hps w st) as (p' & w' & st' & sub).
  exists p'. split_and!; [exact w' | exact st' | by apply Γ_incl_of_ρ_incl].
Qed.

(* The co-trace and the test found, without the proofs (for display). *)
Definition distinguishing_test (alphabet : list A) (n : nat) (p q : proc)
  (hp : ∀ s, p ⇓ᶜᵒ s) (hq : ∀ s, q ⇓ᶜᵒ s) : option (trace A * proc) :=
  match search_distinguishing_test alphabet n p q hp hq with
  | Some (exist _ (s, X) _) => Some (s, gen_acc X s)
  | None => None
  end.

(* Whether the search succeeds, as a boolean (cheap to compute). *)
Definition search_succeeds (alphabet : list A) (n : nat) (p q : proc)
  (hp : ∀ s, p ⇓ᶜᵒ s) (hq : ∀ s, q ⇓ᶜᵒ s) : bool :=
  match search_distinguishing_test alphabet n p q hp hq with
  | Some _ => true
  | None => false
  end.

Lemma search_refutes (alphabet : list A) (n : nat) (p q : proc)
  (hp : ∀ s, p ⇓ᶜᵒ s) (hq : ∀ s, q ⇓ᶜᵒ s) :
  search_succeeds alphabet n p q hp hq = true → p ⋢ₘᵤₛₜᵢ q.
Proof.
  unfold search_succeeds.
  destruct (search_distinguishing_test alphabet n p q hp hq) as [[[s X] [h1 h2]] |]; [| discriminate].
  intros _. exact (distinguishing_test_refutes p q _ h1 h2).
Qed.

End VCCS_Distinguishing_Test.

Section Examples.

Import Uint63.

#[local] Instance int63_eq_dec : EqDecision int := Uint63.eqs.
#[local] Instance int63_countable : Countable int := inj_countable' to_Z of_Z of_to_Z.

(* Channels are natural numbers, values are 63-bit machine integers. *)
#[local] Instance VCCS_int63 : VCCS_Parameters := {| Channel := nat; Value := int; O := 0%uint63 |}.

(* Co-convergence with the VCCS instances made explicit. *)
Definition cocnv_VCCS (p : proc) (s : list (ExtAct TypeOfActions)) : Prop :=
  @cocnv proc (ExtAct TypeOfActions) VCCS_ExtAction (@gLtsEq_gLts proc _ _ VCCS_gLtsEq)
    (ExtAct TypeOfActions) VCCS_ExtAction SyncAction_of_dual p s.

(* [q1] may silently refuse to emit on channel [0]: the test receiving on [0] and
   then succeeding is passed by [p1] and failed by [q1], with the empty co-trace. *)
Definition p1 : proc := g (cst 0 ! cst 0%uint63 • g 𝟘).
Definition q1 : proc := g ((𝛕 • g (cst 0 ! cst 0%uint63 • g 𝟘)) + (𝛕 • g 𝟘)).

Variable hp1 : ∀ s, cocnv_VCCS p1 s.
Variable hq1 : ∀ s, cocnv_VCCS q1 s.

Example p1_q1_test :
  distinguishing_test [ActIn (cst 0, cst 0%uint63)] 1 p1 q1 hp1 hq1
  = Some ([], g ((cst 0 ? • g ①) + 𝟘)).
Proof. vm_compute. reflexivity. Qed.

Example p1_not_below_q1 : p1 ⋢ₘᵤₛₜᵢ q1.
Proof. apply (search_refutes (VP := VCCS_int63) [ActIn (cst 0, cst 0%uint63)] 1 p1 q1 hp1 hq1). vm_compute. reflexivity. Qed.

(* The distinguishing test computed from a (here hypothetical) proof that the bounded
   preorder fails: the proof is never inspected when the search succeeds. *)
Variable not_bounded1 : ¬ bounded_acc_preorder (VP := VCCS_int63) [ActIn (cst 0, cst 0%uint63)] 1 p1 q1.

Example p1_q1_test_of_not_bounded :
  let '(s, X) := proj1_sig (test_of_not_bounded [ActIn (cst 0, cst 0%uint63)] 1 p1 q1 hp1 hq1 not_bounded1) in
  (s, gen_acc X s) = ([], g ((cst 0 ? • g ①) + 𝟘)).
Proof. vm_compute. reflexivity. Qed.

(* The bounded decision in both directions: [q1] is below [p1] up to length [1]
   (it may refuse more), while [p1] is not below [q1]. *)
Example q1_below_p1 :
  bounded_preorder_holds [ActIn (cst 0, cst 0%uint63)] 1 q1 p1 hq1 hp1 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma q1_below_p1_bounded :
  bounded_acc_preorder (VP := VCCS_int63) [ActIn (cst 0, cst 0%uint63)] 1 q1 p1.
Proof. apply (bounded_preorder_holds_spec _ _ _ _ hq1 hp1). vm_compute. reflexivity. Qed.

Example p1_q1_verdict :
  bounded_verdict [ActIn (cst 0, cst 0%uint63)] 1 p1 q1 hp1 hq1
  = Some ([], g ((cst 0 ? • g ①) + 𝟘)).
Proof. vm_compute. reflexivity. Qed.

(* The bounded decision with bounded convergence: no convergence hypothesis.
   Here [n = 1] (co-traces of length at most 1) and [k = 5] (at most 5 τ-steps). *)
Example p1_q1_co_verdict :
  co_preorder_verdict [ActIn (cst 0, cst 0%uint63)] 1 5 p1 q1
  = V_distinguished [] (g ((cst 0 ? • g ①) + 𝟘)).
Proof. vm_compute. reflexivity. Qed.

Lemma q1_below_p1_co :
  bounded_co_preorder (VP := VCCS_int63) [ActIn (cst 0, cst 0%uint63)] 1 q1 p1.
Proof. apply (co_preorder_holds_spec _ _ 5). vm_compute. reflexivity. Qed.

(* A process that diverges: the convergence check runs out of steps. *)
Definition ω : proc := rec 0 • (pr_var 0).

Example ω_timeout :
  co_preorder_verdict [ActIn (cst 0, cst 0%uint63)] 1 5 ω p1 = V_timeout [] true.
Proof. vm_compute. reflexivity. Qed.

(* [p2] may emit on [0] or [1], [q2] only on [0]: the test receiving on [1] separates
   them. *)
Definition p2 : proc := g ((cst 0 ! cst 0%uint63 • g 𝟘) + (cst 1 ! cst 0%uint63 • g 𝟘)).
Definition q2 : proc := g (cst 0 ! cst 0%uint63 • g 𝟘).

Variable hp2 : ∀ s, cocnv_VCCS p2 s.
Variable hq2 : ∀ s, cocnv_VCCS q2 s.

Example p2_q2_test :
  distinguishing_test [] 0 p2 q2 hp2 hq2 = Some ([], g ((cst 1 ? • g ①) + 𝟘)).
Proof. vm_compute. reflexivity. Qed.

(* After receiving on [2], [p3] emits on [0] while [q3] may stop: the distinguishing
   co-trace has length one. *)
Definition p3 : proc := g (cst 2 ? • g (cst 0 ! cst 0%uint63 • g 𝟘)).
Definition q3 : proc := g (cst 2 ? • g ((𝛕 • g (cst 0 ! cst 0%uint63 • g 𝟘)) + (𝛕 • g 𝟘))).

Variable hp3 : ∀ s, cocnv_VCCS p3 s.
Variable hq3 : ∀ s, cocnv_VCCS q3 s.

Example p3_q3_test :
  distinguishing_test [ActOut (cst 2, cst 0%uint63)] 1 p3 q3 hp3 hq3
  = Some ([ActOut (cst 2, cst 0%uint63)], g ((cst 2 ! cst 0%uint63 • g ((cst 0 ? • g ①) + 𝟘)) + (𝛕 • g ①))).
Proof. vm_compute. reflexivity. Qed.

End Examples.
(* end hide *)
