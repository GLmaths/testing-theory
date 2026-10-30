(* begin hide *)
From stdpp Require Import base list sets.
From TestingTheory Require Import ActTau gLts Bisimulation SyncActions Termination Subset_Act coWeakTransition.

Section Strong_Bisim.

Context `{gLtsP : @gLts P A HA} `{SA : !SyncAction A A}.

Definition is_bisim (R : P → P → Prop) : Prop :=
  ∀ p q, R p q →
    (∀ α p', p ⟶{α} p' → ∃ q', q ⟶{α} q' ∧ R p' q') ∧
    (∀ α q', q ⟶{α} q' → ∃ p', p ⟶{α} p' ∧ R p' q').

Definition sbisim (p q : P) : Prop := ∃ R, is_bisim R ∧ R p q.

Lemma sbisim_refl p : sbisim p p.
Proof.
  exists eq. split; [| reflexivity]. intros a b ->. split; intros α x l; exists x; split; done.
Qed.

Lemma sbisim_sym p q : sbisim p q → sbisim q p.
Proof.
  intros (R & hR & h). exists (λ a b, R b a). split; [| exact h].
  intros a b hab. destruct (hR b a hab) as [h1 h2]. split; [exact h2 | exact h1].
Qed.

Lemma sbisim_trans p q r : sbisim p q → sbisim q r → sbisim p r.
Proof.
  intros (R1 & h1 & hpq) (R2 & h2 & hqr). exists (λ a c, ∃ b, R1 a b ∧ R2 b c). split; [| by exists q].
  intros a c (b & hab & hbc). destruct (h1 a b hab) as [f1 b1], (h2 b c hbc) as [f2 b2]. split.
  - intros α a' l. destruct (f1 α a' l) as (b' & lb & hb). destruct (f2 α b' lb) as (c' & lc & hc).
    exists c'. split; [exact lc | by exists b'].
  - intros α c' l. destruct (b2 α c' l) as (b' & lb & hb). destruct (b1 α b' lb) as (a' & la & ha).
    exists a'. split; [exact la | by exists b'].
Qed.

Lemma sbisim_step p q α p' : sbisim p q → p ⟶{α} p' → ∃ q', q ⟶{α} q' ∧ sbisim p' q'.
Proof.
  intros (R & hR & h) l. destruct (proj1 (hR p q h) α p' l) as (q' & lq & h').
  exists q'. split; [exact lq | by exists R].
Qed.

Lemma sbisim_cowt p q s p' : sbisim p q → p ⟹ᶜᵒ[s] p' → ∃ q', q ⟹ᶜᵒ[s] q' ∧ sbisim p' q'.
Proof.
  intros h w. revert q h. induction w as [p | s p p1 p' l w IH | μ μ' s p p1 p' duo l w IH]; intros q h.
  - exists q. split; [apply cowt_nil | exact h].
  - destruct (sbisim_step p q τ p1 h l) as (q1 & lq & h1). destruct (IH q1 h1) as (q' & wq & h').
    exists q'. split; [exact (cowt_tau s q q1 q' lq wq) | exact h'].
  - destruct (sbisim_step p q (ActExt μ') p1 h l) as (q1 & lq & h1). destruct (IH q1 h1) as (q' & wq & h').
    exists q'. split; [exact (cowt_act μ μ' s q q1 q' duo lq wq) | exact h'].
Qed.

Lemma sbisim_terminate p q : sbisim p q → p ⤓ → q ⤓.
Proof.
  intros h t. revert q h. induction t as [p _ IH]. intros q h. constructor. intros q' l.
  destruct (sbisim_step q p τ q' (sbisim_sym p q h) l) as (p' & lp & h').
  exact (IH p' lp q' (sbisim_sym _ _ h')).
Qed.

Lemma sbisim_stable p q : sbisim p q → p ↛ → q ↛.
Proof.
  intros h st hm. destruct (lts_may_perform_spec1 _ _ hm) as [q' l].
  destruct (sbisim_step q p τ q' (sbisim_sym p q h) l) as (p' & lp & _).
  apply st, lts_may_perform_spec2. by exists p'.
Qed.

Lemma sbisim_coR {B} (Γ : A → B) p q x : sbisim p q → x ∈ ⌈ Γ ⌉ (coR p) → x ∈ ⌈ Γ ⌉ (coR q).
Proof.
  intros h (μ1 & (μ2 & hm & duo & hb) & ->). exists μ1. split; [| reflexivity].
  destruct (lts_may_perform_spec1 _ _ hm) as [p' l].
  destruct (sbisim_step p q (ActExt μ2) p' h l) as (q' & lq & _).
  exists μ2. split_and!; [| exact duo | exact hb].
  apply lts_may_perform_spec2. by exists q'.
Qed.

End Strong_Bisim.

Lemma eq_sbisim `{gLtsEqP : @gLtsEq P A HA} (p q : P) : p ⋍ q → sbisim (gLtsP := gLtsEq_gLts) p q.
Proof.
  intros h. exists eq_rel. split; [| exact h]. intros a b hab. split.
  - intros α a' l. destruct (eq_spec b a' α) as (b' & lb & hb); [exists a; split; [symmetry; exact hab | exact l] |].
    exists b'. split; [exact lb | symmetry; exact hb].
  - intros α b' l. destruct (eq_spec a b' α) as (a' & la & ha); [exists b; split; [exact hab | exact l] |].
    exists a'. split; [exact la | exact ha].
Qed.
(* end hide *)
