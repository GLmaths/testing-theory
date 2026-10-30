(* begin hide *)
From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base countable gmap list.
From TestingTheory Require Import VCCS.Testing.ta_tc_gen DefinitionAS Equivalence Must
  ParallelLTSConstruction InteractionBetweenLts Bisimulation ActTau InputOutputActions Convergence
  gLts Lts_OBA FiniteImageLTS Testing_Predicate Completeness Lts_FW Lts_OBA_FB MultisetLTSConstruction
  SetLTSConstruction ForwarderConstruction.
From TestingTheory Require Import coFiniteImage coConvergence coWeakTransition DefinitionASrel
  CompletenessASco EquivalenceASco TestSpecBridge SyncActions
  VCCS.Language.LTS VCCS.Language.gLts_Instance VCCS.Language.Label_Abstraction
  VCCS.Characterisations.Must_Characterisation Label_Abstraction.LabelAbstraction
  Label_Abstraction.Decidable_dichotomic Subset_Act
  Decision.Computing_Tools.Bounded_Search.
Import ListNotations.

Section VCCS_Bounded.

Context `{VP : VCCS_Parameters}.

#[local] Instance SyncAction_VCCS : SyncAction (ExtAct TypeOfActions) (ExtAct TypeOfActions) :=
  SyncAction_of_dual.

Notation A := (ExtAct TypeOfActions).

Notation Γᴠᴄᴄꜱ := (λ μ : A, αᴘᴠᴄᴄꜱ (αᴛᴠᴄᴄꜱ μ)).

Lemma PreCoAct_of_spec (p : proc) x : x ∈ PreCoAct_of p ↔ x ∈ ⌈ Γᴠᴄᴄꜱ ⌉ (coR p).
Proof.
  split.
  - apply (coR_abs_spec1 (FinitaryAbsAction := FinitaryAbsVCCS)).
  - apply (coR_abs_spec2 (FinitaryAbsAction := FinitaryAbsVCCS)).
Qed.

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

#[local] Instance Dichotomic_Γᴠᴄᴄꜱ : Dichotomic proc Γᴠᴄᴄꜱ := λ p' q' _ _, pre_dichotomy p' q'.

#[local] Instance LA_surj_VCCS : LA_surj Γᴠᴄᴄꜱ :=
  {| LA_repr := repr_pre_vccs; LA_repr_spec := ρᴠᴄᴄꜱ_repr |}.

Definition vccs_bounded_preorder (alphabet : list A) (n : nat) (p q : proc) : Prop :=
  bounded_co_preorder Γᴠᴄᴄꜱ alphabet n p q.

Definition vccs_bounded (alphabet : list A) (n k : nat) (p q : proc) :=
  bounded_verdict Γᴠᴄᴄꜱ alphabet n k p q.

Theorem vccs_bounded_holds alphabet n k (p q : proc) :
  vccs_bounded alphabet n k p q = B_holds → vccs_bounded_preorder alphabet n p q.
Proof. exact (bounded_verdict_holds Γᴠᴄᴄꜱ alphabet n k p q). Qed.

Theorem vccs_bounded_test alphabet n k (p q : proc) s E :
  vccs_bounded alphabet n k p q = B_distinguished s E →
  p must_pass (gen_acc E s) ∧ ¬ q must_pass (gen_acc E s).
Proof. exact (bounded_verdict_distinguishes 𝔸ᴠᴄᴄꜱ Γᴠᴄᴄꜱ (ta := gen_acc) alphabet n k p q s E). Qed.

Corollary vccs_bounded_refutes alphabet n k (p q : proc) s E :
  vccs_bounded alphabet n k p q = B_distinguished s E → ¬ p ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ q.
Proof. exact (bounded_verdict_refutes 𝔸ᴠᴄᴄꜱ Γᴠᴄᴄꜱ (ta := gen_acc) alphabet n k p q s E). Qed.

Definition vccs_holds_b (alphabet : list A) (n k : nat) (p q : proc) : bool :=
  bounded_holds_b Γᴠᴄᴄꜱ alphabet n k p q.

Theorem vccs_holds_b_spec alphabet n k (p q : proc) :
  vccs_holds_b alphabet n k p q = true → vccs_bounded_preorder alphabet n p q.
Proof. exact (bounded_holds_b_spec Γᴠᴄᴄꜱ alphabet n k p q). Qed.

Definition vccs_refuted_b (alphabet : list A) (n k : nat) (p q : proc) : bool :=
  bounded_refuted_b Γᴠᴄᴄꜱ alphabet n k p q.

Corollary vccs_refuted_b_spec alphabet n k (p q : proc) :
  vccs_refuted_b alphabet n k p q = true → ¬ p ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ q.
Proof. exact (bounded_refuted_b_spec 𝔸ᴠᴄᴄꜱ Γᴠᴄᴄꜱ (ta := gen_acc) alphabet n k p q). Qed.

Corollary vccs_bounded_of_must alphabet n (p q : proc) :
  p ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ q → vccs_bounded_preorder alphabet n p q.
Proof.
  intros h%must_iff_co_acceptance_set_VCCS_without_toFW.
  exact (bounded_of_co_preorder 𝔸ᴠᴄᴄꜱ Γᴠᴄᴄꜱ alphabet n p q h).
Qed.

Definition vccs_test_of_not_bounded (alphabet : list A) (n k : nat) (p q : proc) (hn : ¬ vccs_bounded_preorder alphabet n p q) :=
  bounded_test_of_not 𝔸ᴠᴄᴄꜱ Γᴠᴄᴄꜱ (ta := gen_acc) alphabet n k p q hn.

End VCCS_Bounded.

#[global] Instance VCCS_nat : VCCS_Parameters := {| Channel := nat; Value := nat; O := 0 |}.

Section VCCS_Bounded_nat.

Notation A := (ExtAct (@TypeOfActions VCCS_nat)).

Definition chan_of (c : ChannelData) : list nat := match c with cst c => [c] | bvar _ => [] end.

Fixpoint chans (p : proc) : list nat :=
  match p with
  | pr_par p1 p2 => chans p1 ++ chans p2
  | pr_var _ => []
  | pr_rec _ p => chans p
  | pr_if_then_else _ p1 p2 => chans p1 ++ chans p2
  | pr_restrict p => chans p
  | g gp => gchans gp
  end
with gchans (gp : gproc) : list nat :=
  match gp with
  | gpr_success | gpr_nil => []
  | gpr_input c p => chan_of c ++ chans p
  | gpr_output c _ p => chan_of c ++ chans p
  | gpr_tau p => chans p
  | gpr_choice g1 g2 => gchans g1 ++ gchans g2
  end.

Definition vccs_alphabet (b : nat) (q : proc) : list A :=
  flat_map (λ c, flat_map (λ v, [ActIn (cst c, cst v); ActOut (cst c, cst v)]) (seq 0 (2 ^ b)))
    (remove_dups (chans q)).

Definition vccs_bounded_preorder_nat (b n : nat) (p q : proc) : Prop :=
  vccs_bounded_preorder (vccs_alphabet b q) n p q.

Definition vccs_bounded_nat (b n k : nat) (p q : proc) :=
  vccs_bounded (vccs_alphabet b q) n k p q.

Definition vccs_holds_nat (b n k : nat) (p q : proc) : bool :=
  vccs_holds_b (vccs_alphabet b q) n k p q.

Theorem vccs_holds_nat_spec b n k (p q : proc) :
  vccs_holds_nat b n k p q = true → vccs_bounded_preorder_nat b n p q.
Proof. exact (vccs_holds_b_spec (vccs_alphabet b q) n k p q). Qed.

Definition vccs_refuted_nat (b n k : nat) (p q : proc) : bool :=
  vccs_refuted_b (vccs_alphabet b q) n k p q.

Theorem vccs_refuted_nat_spec b n k (p q : proc) :
  vccs_refuted_nat b n k p q = true → ¬ p ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ q.
Proof. exact (vccs_refuted_b_spec (vccs_alphabet b q) n k p q). Qed.

Theorem vccs_bounded_nat_test b n k (p q : proc) s E :
  vccs_bounded_nat b n k p q = B_distinguished s E →
  p must_pass (gen_acc E s) ∧ ¬ q must_pass (gen_acc E s).
Proof. exact (vccs_bounded_test (vccs_alphabet b q) n k p q s E). Qed.

Corollary vccs_bounded_nat_of_must b n (p q : proc) :
  p ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ q → vccs_bounded_preorder_nat b n p q.
Proof. exact (vccs_bounded_of_must (vccs_alphabet b q) n p q). Qed.

Definition vccs_test_of_not_bounded_nat (b n k : nat) (p q : proc) (hn : ¬ vccs_bounded_preorder_nat b n p q) :=
  vccs_test_of_not_bounded (vccs_alphabet b q) n k p q hn.

End VCCS_Bounded_nat.

Section Examples.

Definition p1 : proc := g (cst 0 ! cst 0 • g 𝟘).
Definition q1 : proc := g ((𝛕 • g (cst 0 ! cst 0 • g 𝟘)) + (𝛕 • g 𝟘)).
Definition ω : proc := rec 0 • pr_var 0.

Example p1_q1_verdict :
  match vccs_bounded_nat 0 2 5 p1 q1 with B_distinguished s E => Some (s, elements E) | _ => None end
  = Some ([], [Inputs_on (cst 0)]).
Proof. vm_compute. reflexivity. Qed.

Theorem p1_not_below_q1 : ¬ p1 ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ q1.
Proof. apply (vccs_refuted_nat_spec 0 2 5). vm_compute. reflexivity. Qed.

Lemma q1_below_p1_bounded : vccs_bounded_preorder_nat 2 4 q1 p1.
Proof. apply (vccs_holds_nat_spec 2 4 5). vm_compute. reflexivity. Qed.

Example p1_ω_verdict :
  match vccs_bounded_nat 1 2 5 p1 ω with B_timeout s b => Some (s, b) | _ => None end
  = Some ([], false).
Proof. vm_compute. reflexivity. Qed.

End Examples.
(* end hide *)
