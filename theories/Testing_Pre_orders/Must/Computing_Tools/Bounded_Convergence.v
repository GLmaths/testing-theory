(* begin hide *)
From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base countable finite gmap list sets.
From TestingTheory Require Import ActTau gLts SyncActions Termination
  coWeakTransition coConvergence coFiniteImage.
Import ListNotations.

(* Convergence within a bounded number of τ-steps.

   [p ⇓ᶜᵒ s] is undecidable in general. Its bounded version is decidable: every
   τ-path has at most [k] steps from [p], and again from every state reached after
   each action of [s] (the count restarts after each action). The check works on
   sets of states, layer by layer, so a state reached along many paths is explored
   once per layer. A positive answer certifies the real convergence; a negative one
   only means that [k] steps were not enough. *)

Section Bounded_Convergence.

Context `{gLtsP : @gLts P Aproc Hp} `{Ht : ExtAction A} `{SA : !SyncAction Aproc A}.
Context `{CFI : !coFiniteImagegLts P A}.

(* Every τ-path from [X] has at most [k] steps. *)
Fixpoint tau_bounded_set (k : nat) (X : gset P) : bool :=
  match k with
  | 0 => bool_decide (colts_tau_set_from_pset X = ∅)
  | S k => tau_bounded_set k (colts_tau_set_from_pset X)
  end.

(* The states reached from [X] by at most [k] τ-steps. *)
Fixpoint tau_reach_set (k : nat) (X : gset P) : gset P :=
  match k with
  | 0 => X
  | S k => X ∪ tau_reach_set k (colts_tau_set_from_pset X)
  end.

Lemma tau_succ_mem (X : gset P) p q : p ∈ X → p ⟶ q → q ∈ colts_tau_set_from_pset X.
Proof. intros hp l. by eapply (colts_tau_set_from_pset_ispec X). Qed.

Lemma tau_bounded_set_terminate k : ∀ X, tau_bounded_set k X = true → ∀ p, p ∈ X → p ⤓.
Proof.
  induction k as [| k IH]; intros X h p hp; simpl in h.
  - apply bool_decide_eq_true in h. constructor. intros q l.
    exfalso. pose proof (tau_succ_mem X p q hp l) as m. rewrite h in m. set_solver.
  - constructor. intros q l. exact (IH _ h q (tau_succ_mem X p q hp l)).
Qed.

Lemma tau_reach_set_complete k : ∀ X, tau_bounded_set k X = true →
  ∀ p t, p ∈ X → p ⟹ᶜᵒ t → t ∈ tau_reach_set k X.
Proof.
  induction k as [| k IH]; intros X h p t hp w; simpl in *.
  - apply bool_decide_eq_true in h.
    remember ([] : trace A) as s0 eqn:hs0 in w. revert hs0 hp.
    induction w as [p | s0 p p' t l w IHw | ]; intros hs0 hp; [exact hp | | discriminate].
    exfalso. pose proof (tau_succ_mem X p p' hp l) as m. rewrite h in m. set_solver.
  - remember ([] : trace A) as s0 eqn:hs0 in w. revert hs0 hp.
    induction w as [p | s0 p p' t l w IHw | ]; intros hs0 hp; [set_solver | | discriminate].
    apply elem_of_union. right. subst.
    exact (IH _ h p' t (tau_succ_mem X p p' hp l) w).
Qed.

(* Convergence along [s] within [k] τ-steps per segment of [s]. *)
Fixpoint cocnv_within_set (k : nat) (X : gset P) (s : trace A) : bool :=
  tau_bounded_set k X &&
  match s with
  | [] => true
  | μ :: s' => cocnv_within_set k (colts_extaction_set_from_pset (tau_reach_set k X) μ) s'
  end.

Lemma cocnv_within_set_sound k s : ∀ X, cocnv_within_set k X s = true → ∀ p, p ∈ X → p ⇓ᶜᵒ s.
Proof.
  induction s as [| μ s IH]; intros X h p hp; simpl in h;
    apply andb_true_iff in h as [hb hs].
  - apply cocnv_nil. exact (tau_bounded_set_terminate k X hb p hp).
  - apply cocnv_act; [exact (tau_bounded_set_terminate k X hb p hp) |].
    intros q w. apply cowt_decomp_one in w as (t & r & μ' & w1 & duo & l & w2).
    eapply (cocnv_preserved_by_cowt_nil s r); [| exact w2].
    apply (IH _ hs r), elem_of_colts_extaction_set_from_pset.
    exists t. split; [exact (tau_reach_set_complete k X hb p t hp w1) |].
    exists μ'. split; [exact duo | exact l].
Qed.

(* The single-process versions. *)
Definition tau_bounded (k : nat) (p : P) : bool := tau_bounded_set k {[ p ]}.

Definition cocnv_within (k : nat) (p : P) (s : trace A) : bool := cocnv_within_set k {[ p ]} s.

Lemma tau_bounded_terminate k p : tau_bounded k p = true → p ⤓.
Proof. intros h. exact (tau_bounded_set_terminate k _ h p (elem_of_singleton_2 _ _ eq_refl)). Qed.

Lemma cocnv_within_sound k p s : cocnv_within k p s = true → p ⇓ᶜᵒ s.
Proof. intros h. exact (cocnv_within_set_sound k s _ h p (elem_of_singleton_2 _ _ eq_refl)). Qed.

End Bounded_Convergence.
(* end hide *)
