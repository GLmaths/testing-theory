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
  Computing_Tools.Search_Helpers Computing_Tools.Acceptance_Tests_Gamma Computing_Tools.Bounded_Convergence.
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

(* First case: the convergence test. *)
Lemma t_conv_distinguishes (p q : proc) (s : trace A) :
  p ⇓ᶜᵒ s → ¬ q ⇓ᶜᵒ s → p must_pass (t_conv nat s) ∧ ¬ q must_pass (t_conv nat s).
Proof.
  intros hp hq. split.
  - by apply must_iff_cocnv_PAL.
  - intros hm. by apply hq, must_iff_cocnv_PAL.
Qed.

(* For a stable state [q'] of [q] after [s]: either a stable state of [p] after [s]
   offers no more events than [q'], or a set [X] of events refused by [q'] meets every
   stable state of [p] after [s]. *)
Definition acc_witness (p : proc) (s : trace A) (hp : p ⇓ᶜᵒ s) (q' : proc) (st : q' ↛) :
  { p' | p ⟹ᶜᵒ[s] p' ∧ p' ↛ ∧ ⌈ Γᴘᴀʟ ⌉ (coR p') ⊆ ⌈ Γᴘᴀʟ ⌉ (coR q') }
  + { X : gset (Event nat) | (∀ x, x ∈ X → x ∉ ⌈ Γᴘᴀʟ ⌉ (coR q'))
        ∧ (∀ p', p ⟹ᶜᵒ[s] p' → p' ↛ → ∃ x, x ∈ X ∧ x ∈ ⌈ Γᴘᴀʟ ⌉ (coR p')) }.
Proof.
  destruct (included_or_witnesses (elements (cowaiting_states p s hp))
              (λ p', ⌈ Γᴘᴀʟ ⌉ (coR p')) (⌈ Γᴘᴀʟ ⌉ (coR q')))
    as [(p' & mem & sub) | (X & hXC & hXS)].
  - intros p' mem. exact (PALA_coR_dichotomy p' q').
  - left. exists p'.
    destruct (cowaiting_states_spec1 _ _ _ _ (proj1 (elem_of_elements _ _) mem)) as [w' st'].
    split_and!; [exact w' | exact st' | exact sub].
  - right. exists X. split; [exact hXC |].
    intros p' w' st'. apply hXS, elem_of_elements, cowaiting_states_spec2. split; [exact w' | exact st'].
Defined.

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

(* An acceptance test passed by [p] and failed by [q], with its co-trace. *)
Definition distinguishing_pair (p q : proc) : Type :=
  { sX : trace A * gset (Event nat) |
    p must_pass (ta nat sX.2 sX.1) ∧ ¬ q must_pass (ta nat sX.2 sX.1) }.

(* Looks for an acceptance test among the stable states [l] of [q] after [s]. *)
Fixpoint distinguish_in (p q : proc) (s : trace A) (hp : p ⇓ᶜᵒ s) (l : list proc) :
  (∀ q', q' ∈ l → q ⟹ᶜᵒ[s] q' ∧ q' ↛) →
  option { X : gset (Event nat) | p must_pass (ta nat X s) ∧ ¬ q must_pass (ta nat X s) } :=
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
Definition distinguish_at (p q : proc) (s : trace A) (hp : p ⇓ᶜᵒ s) (hq : q ⇓ᶜᵒ s) :
  option { X : gset (Event nat) | p must_pass (ta nat X s) ∧ ¬ q must_pass (ta nat X s) } :=
  distinguish_in p q s hp (elements (cowaiting_states q s hq))
    (λ q' m, cowaiting_states_spec1 _ _ _ _ (proj1 (elem_of_elements _ _) m)).

Lemma distinguish_in_none (p q : proc) (s : trace A) (hp : p ⇓ᶜᵒ s) (l : list proc) hl :
  distinguish_in p q s hp l hl = None →
  ∀ q', q' ∈ l → ∃ p', p ⟹ᶜᵒ[s] p' ∧ p' ↛ ∧ ⌈ Γᴘᴀʟ ⌉ (coR p') ⊆ ⌈ Γᴘᴀʟ ⌉ (coR q').
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
  ∀ q', q ⟹ᶜᵒ[s] q' → q' ↛ → ∃ p', p ⟹ᶜᵒ[s] p' ∧ p' ↛ ∧ ⌈ Γᴘᴀʟ ⌉ (coR p') ⊆ ⌈ Γᴘᴀʟ ⌉ (coR q').
Proof.
  intros hnone q' w st. eapply (distinguish_in_none p q s hp _ _ hnone).
  apply elem_of_elements, cowaiting_states_spec2. split; [exact w | exact st].
Qed.

(* The alternative preorder restricted to the co-traces of length at most [n] over
   [alphabet]. *)
Definition bounded_co_preorder (alphabet : list A) (n : nat) (p q : proc) : Prop :=
  ∀ s, s ∈ traces_upto alphabet n →
    (p ⇓ᶜᵒ s → q ⇓ᶜᵒ s) ∧
    (∀ q', p ⇓ᶜᵒ s → q ⟹ᶜᵒ[s] q' → q' ↛ →
       ∃ p', p ⟹ᶜᵒ[s] p' ∧ p' ↛ ∧ ⌈ Γᴘᴀʟ ⌉ (coR p') ⊆ ⌈ Γᴘᴀʟ ⌉ (coR q')).

Definition decide_in (k : nat) (p q : proc) : ∀ l : list (trace A),
  bounded_answer (A := A)
    (∀ s, s ∈ l → (p ⇓ᶜᵒ s → q ⇓ᶜᵒ s) ∧
       (∀ q', p ⇓ᶜᵒ s → q ⟹ᶜᵒ[s] q' → q' ↛ →
          ∃ p', p ⟹ᶜᵒ[s] p' ∧ p' ↛ ∧ ⌈ Γᴘᴀʟ ⌉ (coR p') ⊆ ⌈ Γᴘᴀʟ ⌉ (coR q')))
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

(* Decision of the bounded preorder, with convergence checked within [k] τ-steps. *)
Definition decide_co_preorder (alphabet : list A) (n k : nat) (p q : proc) :
  bounded_answer (A := A) (bounded_co_preorder alphabet n p q) (distinguishing_pair p q) :=
  decide_in k p q (traces_upto alphabet n).

Definition co_preorder_verdict (alphabet : list A) (n k : nat) (p q : proc) : verdict A proc :=
  match decide_co_preorder alphabet n k p q with
  | Holds _ => V_holds
  | Distinguished (exist _ (s, X) _) => V_distinguished s (ta nat X s)
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
  co_preorder_refuted alphabet n k p q = true → ¬ p ᴘᴀʟ⊑ₘᵤₛₜᵢ q.
Proof.
  unfold co_preorder_refuted.
  destruct (decide_co_preorder alphabet n k p q) as [| [[s X] [h1 h2]] |]; [discriminate | | discriminate].
  intros _. exact (distinguishing_test_refutes p q _ h1 h2).
Qed.

(* From a proof that the bounded preorder fails: the distinguishing test, or a co-trace
   along which the convergence check ran out of steps. *)
Definition co_test_of_not_bounded (alphabet : list A) (n k : nat) (p q : proc)
  (H : ¬ bounded_co_preorder alphabet n p q) : distinguishing_pair p q + (trace A * bool).
Proof.
  destruct (decide_co_preorder alphabet n k p q) as [h | d | s b].
  - exfalso. exact (H h).
  - left. exact d.
  - right. exact (s, b).
Defined.

Lemma Γ_incl_of_ρ_incl (S S' : subset_of A) :
  ⌈ ρ[𝔸ᴘᴀʟ] ⌉ S ⊆ ⌈ ρ[𝔸ᴘᴀʟ] ⌉ S' → ⌈ Γᴘᴀʟ ⌉ S ⊆ ⌈ Γᴘᴀʟ ⌉ S'.
Proof.
  intros h x (μ & hμ & ->).
  destruct (h (ρ[𝔸ᴘᴀʟ] μ)) as (μ' & hμ' & e); [by exists μ |].
  exists μ'. split; [exact hμ' |]. by apply ρᴘᴀʟ_eq.
Qed.

(* The alternative preorder implies each of its restrictions. *)
Lemma bounded_of_co_preorder (alphabet : list A) (n : nat) (p q : proc) :
  p ≼꜀ₒ₋ₐₛ[ ρ[𝔸ᴘᴀʟ] ] q → bounded_co_preorder alphabet n p q.
Proof.
  intros [hc ha] s _. split; [exact (hc s) |].
  intros q' hps w st. destruct (ha s q' hps w st) as (p' & w' & st' & sub).
  exists p'. split_and!; [exact w' | exact st' | by apply Γ_incl_of_ρ_incl].
Qed.

Corollary not_preorder_of_not_bounded_co (alphabet : list A) (n : nat) (p q : proc) :
  ¬ bounded_co_preorder alphabet n p q → ¬ p ≼꜀ₒ₋ₐₛ[ ρ[𝔸ᴘᴀʟ] ] q.
Proof. intros hn h. exact (hn (bounded_of_co_preorder alphabet n p q h)). Qed.

(* ** Bounded search with convergence assumed

   The convergence of [p] and [q] along every co-trace is given by the hypotheses [hp]
   and [hq]: only the acceptance part of the preorder is searched. *)

Fixpoint search_in (p q : proc) (hp : ∀ s : trace A, p ⇓ᶜᵒ s) (hq : ∀ s : trace A, q ⇓ᶜᵒ s) (l : list (trace A)) :
  option (distinguishing_pair p q) :=
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
  (hp : ∀ s : trace A, p ⇓ᶜᵒ s) (hq : ∀ s : trace A, q ⇓ᶜᵒ s) : option (distinguishing_pair p q) :=
  search_in p q hp hq (traces_upto alphabet n).

(* The acceptance part of the alternative preorder, restricted to the co-traces of
   length at most [n] over [alphabet]. *)
Definition bounded_acc_preorder (alphabet : list A) (n : nat) (p q : proc) : Prop :=
  ∀ s, s ∈ traces_upto alphabet n → ∀ q', p ⇓ᶜᵒ s → q ⟹ᶜᵒ[s] q' → q' ↛ →
    ∃ p', p ⟹ᶜᵒ[s] p' ∧ p' ↛ ∧ ⌈ Γᴘᴀʟ ⌉ (coR p') ⊆ ⌈ Γᴘᴀʟ ⌉ (coR q').

Lemma search_in_none (p q : proc) (hp : ∀ s : trace A, p ⇓ᶜᵒ s) (hq : ∀ s : trace A, q ⇓ᶜᵒ s) (l : list (trace A)) :
  search_in p q hp hq l = None → ∀ s, s ∈ l → distinguish_at p q s (hp s) (hq s) = None.
Proof.
  induction l as [| s0 l IH]; simpl.
  - intros _ s m. inversion m.
  - destruct (distinguish_at p q s0 (hp s0) (hq s0)) as [[X h] |] eqn:e; [discriminate |].
    intros hnone s [-> | m]%elem_of_cons; [exact e | exact (IH hnone s m)].
Qed.

(* Completeness of the bounded search: when it fails, the bounded preorder holds. *)
Lemma search_complete (alphabet : list A) (n : nat) (p q : proc)
  (hp : ∀ s : trace A, p ⇓ᶜᵒ s) (hq : ∀ s : trace A, q ⇓ᶜᵒ s) :
  search_distinguishing_test alphabet n p q hp hq = None → bounded_acc_preorder alphabet n p q.
Proof.
  intros hnone s m q' _ w st.
  exact (distinguish_at_none p q s (hp s) (hq s) (search_in_none p q hp hq _ hnone s m) q' w st).
Qed.

(* From a proof that the bounded preorder fails, the distinguishing test. *)
Definition test_of_not_bounded (alphabet : list A) (n : nat) (p q : proc)
  (hp : ∀ s : trace A, p ⇓ᶜᵒ s) (hq : ∀ s : trace A, q ⇓ᶜᵒ s) (H : ¬ bounded_acc_preorder alphabet n p q) :
  distinguishing_pair p q.
Proof.
  destruct (search_distinguishing_test alphabet n p q hp hq) as [x |] eqn:e.
  - exact x.
  - exfalso. exact (H (search_complete alphabet n p q hp hq e)).
Defined.

(* Decision of the bounded preorder: either it holds, or a distinguishing test. *)
Definition decide_bounded_preorder (alphabet : list A) (n : nat) (p q : proc)
  (hp : ∀ s : trace A, p ⇓ᶜᵒ s) (hq : ∀ s : trace A, q ⇓ᶜᵒ s) :
  bounded_acc_preorder alphabet n p q + distinguishing_pair p q.
Proof.
  destruct (search_distinguishing_test alphabet n p q hp hq) as [x |] eqn:e.
  - right. exact x.
  - left. exact (search_complete alphabet n p q hp hq e).
Defined.

(* The verdict without the proofs: [None] when the bounded preorder holds, otherwise
   the co-trace and the distinguishing test. *)
Definition bounded_verdict (alphabet : list A) (n : nat) (p q : proc)
  (hp : ∀ s : trace A, p ⇓ᶜᵒ s) (hq : ∀ s : trace A, q ⇓ᶜᵒ s) : option (trace A * proc) :=
  match decide_bounded_preorder alphabet n p q hp hq with
  | inl _ => None
  | inr (exist _ (s, X) _) => Some (s, ta nat X s)
  end.

Definition bounded_preorder_holds (alphabet : list A) (n : nat) (p q : proc)
  (hp : ∀ s : trace A, p ⇓ᶜᵒ s) (hq : ∀ s : trace A, q ⇓ᶜᵒ s) : bool :=
  match decide_bounded_preorder alphabet n p q hp hq with
  | inl _ => true
  | inr _ => false
  end.

Lemma bounded_preorder_holds_spec (alphabet : list A) (n : nat) (p q : proc)
  (hp : ∀ s : trace A, p ⇓ᶜᵒ s) (hq : ∀ s : trace A, q ⇓ᶜᵒ s) :
  bounded_preorder_holds alphabet n p q hp hq = true → bounded_acc_preorder alphabet n p q.
Proof.
  unfold bounded_preorder_holds.
  destruct (decide_bounded_preorder alphabet n p q hp hq) as [h | _]; [done | discriminate].
Qed.

(* The alternative preorder implies each of its bounded restrictions. *)
Lemma bounded_of_acc_preorder (alphabet : list A) (n : nat) (p q : proc) :
  p ₐ꜀꜀≼꜀ₒ₋ₐₛ[ ρ[𝔸ᴘᴀʟ] ] q → bounded_acc_preorder alphabet n p q.
Proof.
  intros h s _ q' hps w st. destruct (h s q' hps w st) as (p' & w' & st' & sub).
  exists p'. split_and!; [exact w' | exact st' | by apply Γ_incl_of_ρ_incl].
Qed.

Corollary not_preorder_of_not_bounded (alphabet : list A) (n : nat) (p q : proc) :
  ¬ bounded_acc_preorder alphabet n p q → ¬ p ≼꜀ₒ₋ₐₛ[ ρ[𝔸ᴘᴀʟ] ] q.
Proof. intros hn [_ h]. exact (hn (bounded_of_acc_preorder alphabet n p q h)). Qed.

(* The co-trace and the test found, without the proofs (for display). *)
Definition distinguishing_test (alphabet : list A) (n : nat) (p q : proc)
  (hp : ∀ s : trace A, p ⇓ᶜᵒ s) (hq : ∀ s : trace A, q ⇓ᶜᵒ s) : option (trace A * proc) :=
  match search_distinguishing_test alphabet n p q hp hq with
  | Some (exist _ (s, X) _) => Some (s, ta nat X s)
  | None => None
  end.

(* Whether the search succeeds, as a boolean (cheap to compute). *)
Definition search_succeeds (alphabet : list A) (n : nat) (p q : proc)
  (hp : ∀ s : trace A, p ⇓ᶜᵒ s) (hq : ∀ s : trace A, q ⇓ᶜᵒ s) : bool :=
  match search_distinguishing_test alphabet n p q hp hq with
  | Some _ => true
  | None => false
  end.

Lemma search_refutes (alphabet : list A) (n : nat) (p q : proc)
  (hp : ∀ s : trace A, p ⇓ᶜᵒ s) (hq : ∀ s : trace A, q ⇓ᶜᵒ s) :
  search_succeeds alphabet n p q hp hq = true → ¬ p ᴘᴀʟ⊑ₘᵤₛₜᵢ q.
Proof.
  unfold search_succeeds.
  destruct (search_distinguishing_test alphabet n p q hp hq) as [[[s X] [h1 h2]] |]; [| discriminate].
  intros _. exact (distinguishing_test_refutes p q _ h1 h2).
Qed.

End PAL_Distinguishing_Test.

Section Examples.

#[local] Open Scope pal_scope.

(* [p1] emits the tuple ⟨1⟩; [q1] may instead silently stop. *)
Definition p1 : term nat := t_out [f_actual (ve_val 1)] t_nil.
Definition q1 : term nat := t_ichoice p1 t_nil.

(* A process that diverges. *)
Definition ω : term nat := t_undef.

(* Parameters: no action ([n = 0], empty co-trace only) and at most 5 τ-steps. *)
Example p1_q1_verdict :
  co_preorder_verdict [] 0 5 p1 q1 = V_distinguished [] (t_echoice (t_in [f_formal 0] t_success) t_nil).
Proof. vm_compute. reflexivity. Qed.

Example p1_not_below_q1 : ¬ p1 ᴘᴀʟ⊑ₘᵤₛₜᵢ q1.
Proof. apply (co_preorder_refuted_spec [] 0 5). vm_compute. reflexivity. Qed.

Lemma q1_below_p1_bounded : bounded_co_preorder [] 0 q1 p1.
Proof. apply (co_preorder_holds_spec _ _ 5). vm_compute. reflexivity. Qed.

Example ω_timeout : co_preorder_verdict [] 0 5 ω p1 = V_timeout [] true.
Proof. vm_compute. reflexivity. Qed.

(* With convergence assumed (here as hypotheses): the bounded search, no τ-step bound. *)
Variable hp1 : ∀ s : trace (PALA_Act nat), p1 ⇓ᶜᵒ s.
Variable hq1 : ∀ s : trace (PALA_Act nat), q1 ⇓ᶜᵒ s.

Example p1_q1_test :
  distinguishing_test [] 0 p1 q1 hp1 hq1 = Some ([], t_echoice (t_in [f_formal 0] t_success) t_nil).
Proof. vm_compute. reflexivity. Qed.

Example p1_not_below_q1_search : ¬ p1 ᴘᴀʟ⊑ₘᵤₛₜᵢ q1.
Proof. apply (search_refutes [] 0 p1 q1 hp1 hq1). vm_compute. reflexivity. Qed.

(* The distinguishing test computed from a (here hypothetical) proof that the bounded
   preorder fails: the proof is never inspected when the search succeeds. *)
Variable not_bounded1 : ¬ bounded_acc_preorder [] 0 p1 q1.

Example p1_q1_test_of_not_bounded :
  let '(s, X) := proj1_sig (test_of_not_bounded [] 0 p1 q1 hp1 hq1 not_bounded1) in
  (s, ta nat X s) = ([], t_echoice (t_in [f_formal 0] t_success) t_nil).
Proof. vm_compute. reflexivity. Qed.

Lemma q1_below_p1_acc : bounded_acc_preorder [] 0 q1 p1.
Proof. apply (bounded_preorder_holds_spec _ _ _ _ hq1 hp1). vm_compute. reflexivity. Qed.

(* After receiving a tuple, [p3] behaves as [p1] and [q3] as [q1]: the distinguishing
   co-trace has length one (the observer emits ⟨5⟩). *)
Definition p3 : term nat := t_in [f_formal 0] p1.
Definition q3 : term nat := t_in [f_formal 0] q1.

Example p3_q3_verdict :
  co_preorder_verdict [AOut nat [of_val 5]] 1 5 p3 q3
  = V_distinguished [AOut nat [of_val 5]]
      (t_echoice (t_lmerge (t_out [f_actual (ve_val 5)] t_nil) (t_echoice (t_in [f_formal 0] t_success) t_nil))
                 (t_eval t_nil t_success)).
Proof. vm_compute. reflexivity. Qed.

Variable hp3 : ∀ s : trace (PALA_Act nat), p3 ⇓ᶜᵒ s.
Variable hq3 : ∀ s : trace (PALA_Act nat), q3 ⇓ᶜᵒ s.

Example p3_q3_test :
  distinguishing_test [AOut nat [of_val 5]] 1 p3 q3 hp3 hq3
  = Some ([AOut nat [of_val 5]],
          t_echoice (t_lmerge (t_out [f_actual (ve_val 5)] t_nil) (t_echoice (t_in [f_formal 0] t_success) t_nil))
                    (t_eval t_nil t_success)).
Proof. vm_compute. reflexivity. Qed.

End Examples.
(* end hide *)
