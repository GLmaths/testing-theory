(* begin hide *)
From Stdlib Require Import Lia.
From stdpp Require Import base countable gmap list sets.
From TestingTheory Require Import ActTau gLts SyncActions Termination Subset_Act InListPropHelper
  coWeakTransition coConvergence coFiniteImage
  Decision.Tools_in_construction.Inductive.Generic.Helpers Decision.Tools_in_construction.Inductive.Generic.Bisim.
Import ListNotations.

Class TraceSearchLang (P A Atom PreAct T : Type) `{gLtsP : @gLts P A HA} `{SA : !SyncAction A A}
  `{CFI : !coFiniteImagegLts P A} `{EqDecision Atom} `{Countable PreAct} := {
  ts_Γ : A → PreAct;
  ts_dichotomy p' q' :
    (⌈ ts_Γ ⌉ (coR p') ⊆ ⌈ ts_Γ ⌉ (coR q')) + { x | x ∈ ⌈ ts_Γ ⌉ (coR p') ∧ x ∉ ⌈ ts_Γ ⌉ (coR q') };

  ts_must : P → T → Prop;
  ts_tc : trace A → T;
  ts_ta : gset PreAct → trace A → T;
  ts_tc_spec p s : ts_must p (ts_tc s) ↔ p ⇓ᶜᵒ s;
  ts_ta_spec p q q' s X :
    p ⇓ᶜᵒ s → q ⟹ᶜᵒ[s] q' → q' ↛ →
    (∀ x, x ∈ X → x ∉ ⌈ ts_Γ ⌉ (coR q')) →
    (∀ p', p ⟹ᶜᵒ[s] p' → p' ↛ → ∃ x, x ∈ X ∧ x ∈ ⌈ ts_Γ ⌉ (coR p')) →
    ts_must p (ts_ta X s) ∧ ¬ ts_must q (ts_ta X s);

  ts_swap : Atom → Atom → P → P;
  ts_swap_act : Atom → Atom → A → A;
  ts_swap_atom : Atom → Atom → Atom → Atom;
  ts_swap_pre : Atom → Atom → PreAct → PreAct;
  ts_swap_invol a b p : ts_swap a b (ts_swap a b p) = p;
  ts_swap_act_invol a b μ : ts_swap_act a b (ts_swap_act a b μ) = μ;
  ts_swap_pre_invol a b x : ts_swap_pre a b (ts_swap_pre a b x) = x;
  ts_swap_atom_other a b c : c ≠ a → c ≠ b → ts_swap_atom a b c = c;
  ts_step_swap a b p μ q : p ⟶[μ] q → ts_swap a b p ⟶[ts_swap_act a b μ] ts_swap a b q;
  ts_tau_swap a b p q : p ⟶ q → ts_swap a b p ⟶ ts_swap a b q;
  ts_sync_swap a b μ' μ : sync μ' μ → sync (ts_swap_act a b μ') (ts_swap_act a b μ);
  ts_nb_swap a b μ : non_blocking (ts_swap_act a b μ) → non_blocking μ;
  ts_Γ_swap a b μ : ts_Γ (ts_swap_act a b μ) = ts_swap_pre a b (ts_Γ μ);

  ts_atoms : P → list Atom;
  ts_atoms_act : A → list Atom;
  ts_atoms_act_swap a b μ : ts_atoms_act (ts_swap_act a b μ) = map (ts_swap_atom a b) (ts_atoms_act μ);
  ts_swap_fix a b p : a ∉ ts_atoms p → b ∉ ts_atoms p → ts_swap a b p = p;

  ts_next : list Atom → P → list A;
  ts_next_spec vals p μ μ' q :
    sync μ' μ → p ⟶[μ'] q → (∀ a, a ∈ ts_atoms_act μ → a ∈ vals) → μ ∈ ts_next vals p;
  ts_arity : P → nat;
  ts_arity_spec p μ μ' q : sync μ' μ → p ⟶[μ'] q → length (ts_atoms_act μ) ≤ ts_arity p;
  ts_pool : list Atom → nat → list Atom;
  ts_pool_avoid avoid N f : f ∈ ts_pool avoid N → f ∉ avoid;
  ts_pool_spec avoid N a M :
    length M ≤ N → a ∈ M → a ∉ ts_pool avoid N →
    ∃ f, f ∈ ts_pool avoid N ∧ f ∉ M ∧ ts_swap_atom a f a = f;

  ts_tau_next : P → list P;
  ts_tau_next_spec p q : q ∈ ts_tau_next p ↔ p ⟶ q;
  ts_co_next : P → A → list P;
  ts_co_next_spec p μ q : q ∈ ts_co_next p μ ↔ ∃ μ', sync μ' μ ∧ p ⟶[μ'] q;

  ts_div : P → bool;
  ts_div_spec p : ts_div p = true → ¬ p ⤓;

  ts_norm : P → P;
  ts_norm_spec p : sbisim (ts_norm p) p;

  ts_hash : P → nat;
}.

Definition dichotomy_of_finite {P A PreAct : Type} `{gLtsP : @gLts P A HA} `{SA : !SyncAction A A}
  `{Countable PreAct} (Γ : A → PreAct) (C : P → gset PreAct) (hC : ∀ p x, x ∈ C p ↔ x ∈ ⌈ Γ ⌉ (coR p))
  (p' q' : P) : (⌈ Γ ⌉ (coR p') ⊆ ⌈ Γ ⌉ (coR q')) + { x | x ∈ ⌈ Γ ⌉ (coR p') ∧ x ∉ ⌈ Γ ⌉ (coR q') }.
Proof.
  destruct (elements (C p' ∖ C q')) as [| x l] eqn:e.
  - left. intros x hx%hC. apply hC.
    destruct (decide (x ∈ C q')) as [h | h]; [exact h |].
    assert (x ∈ elements (C p' ∖ C q')) as m by (apply elem_of_elements; set_solver).
    rewrite e in m. inversion m.
  - right. exists x.
    assert (x ∈ C p' ∖ C q') as hx by (apply elem_of_elements; rewrite e; apply list_elem_of_here).
    split.
    + apply hC. set_solver.
    + intros h%hC. set_solver.
Defined.

(* end hide *)
