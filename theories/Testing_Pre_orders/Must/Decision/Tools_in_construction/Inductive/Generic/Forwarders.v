(* begin hide *)
From Stdlib Require Import Lia.
From stdpp Require Import base countable gmultiset list sets.
From TestingTheory Require Import ActTau gLts InteractionBetweenLts MultisetLTSConstruction
  ForwarderConstruction Decision.Tools_in_construction.Inductive.Generic.Bisim.

Section FW_Swap.

Context `{H : ExtAction A} {unique_nb : UniqueDual A} `{gLtsP : @gLts P A H}.
Context `{PI : !Prop_of_Inter P (MO A) A A fw_inter}.

Context (f : A → A) (g : P → P).
Context (f_invol : ∀ μ, f (f μ) = μ).
Context (g_invol : ∀ p, g (g p) = p).
Context (f_dual : ∀ μ η, dual μ η → dual (f μ) (f η)).
Context (f_nb : ∀ η, non_blocking η → non_blocking (f η)).

Definition map_label (α : Labels A) : Labels A :=
  match α with
  | ActExt μ => ActExt (f μ)
  | τ => τ
  end.

Context (g_step : ∀ p α q, p ⟶{α} q → g p ⟶{map_label α} g q).

Definition fw_map (pm : P * MO A) : P * MO A := (g pm.1, gmultiset_map f pm.2).

Lemma f_inj : Inj eq eq f.
Proof. intros x y e. by rewrite <- (f_invol x), <- (f_invol y), e. Qed.

Lemma fw_map_invol pm : fw_map (fw_map pm) = pm.
Proof.
  destruct pm as [p m]. unfold fw_map. simpl. rewrite g_invol. f_equal.
  apply gmultiset_eq. intros x. rewrite <- (f_invol x) at 1.
  rewrite !multiplicity_gmultiset_map; [reflexivity | apply f_inj | apply f_inj].
Qed.

Lemma fw_step_map pm α qm : pm ⟶{α} qm → fw_map pm ⟶{map_label α} fw_map qm.
Proof.
  intros l. inversion l as [α' a1 a2 b l1 | α' a b1 b2 l1 | μ1 μ2 a1 a2 b1 b2 eq l1 l2]; subst; unfold fw_map; simpl.
  - apply ParLeft. exact (g_step _ _ _ l1).
  - apply ParRight. inversion l1 as [m η μ duo nb | m η nb]; subst; simpl.
    + unfold MO in *; rewrite gmultiset_map_disj_union, gmultiset_map_singleton.
      apply lts_multiset_add; [exact (f_dual _ _ duo) | exact (f_nb _ nb)].
    + unfold MO in *; rewrite gmultiset_map_disj_union, gmultiset_map_singleton.
      apply lts_multiset_minus. exact (f_nb _ nb).
  - destruct eq as [duo nb]. eapply ParSync.
    + split; [exact (f_dual _ _ duo) | exact (f_nb _ nb)].
    + exact (g_step _ (ActExt μ1) _ l1).
    + inversion l2 as [m η μ duo' nb' | m η nb']; subst; simpl.
      * unfold MO in *; rewrite gmultiset_map_disj_union, gmultiset_map_singleton.
        apply lts_multiset_add; [exact (f_dual _ _ duo') | exact (f_nb _ nb')].
      * unfold MO in *; rewrite gmultiset_map_disj_union, gmultiset_map_singleton.
        apply lts_multiset_minus. exact (f_nb _ nb').
Qed.

Lemma gmultiset_map_fix (m : MO A) : (∀ x, x ∈ m → f x = x) → gmultiset_map f m = m.
Proof.
  intros h. unfold MO in *. apply gmultiset_eq. intros x.
  rewrite <- (f_invol x) at 1. rewrite multiplicity_gmultiset_map by apply f_inj.
  destruct (decide (x ∈ m)) as [hx | hx]; [by rewrite (h x hx) |].
  destruct (decide (f x ∈ m)) as [hf | hf].
  - exfalso. apply hx. pose proof (h _ hf) as e. rewrite f_invol in e. rewrite e. exact hf.
  - rewrite elem_of_multiplicity in hx, hf. lia.
Qed.

End FW_Swap.

Section FW_Bisim.

Context `{H : ExtAction A} {unique_nb : UniqueDual A} `{gLtsP : @gLts P A H}.
Context `{PI : !Prop_of_Inter P (MO A) A A fw_inter}.

Lemma fw_sbisim (p p' : P) (m : MO A) : sbisim p p' → sbisim (p, m) (p', m).
Proof.
  intros hp. exists (λ a b, sbisim a.1 b.1 ∧ a.2 = b.2). split; [| split; [exact hp | reflexivity]].
  intros [a1 b] [c1 d] [hac e]. simpl in hac, e. subst d. split.
  - intros α [a2 b2] l. inversion l as [α' x1 x2 y l1 | α' x y1 y2 l1 | μ1 μ2 x1 x2 y1 y2 eq l1 l2]; subst.
    + destruct (sbisim_step _ _ _ _ hac l1) as (c2 & lc & h2).
      eexists. split; [eapply ParLeft; exact lc | split; [exact h2 | reflexivity]].
    + eexists. split; [eapply ParRight; exact l1 | split; [exact hac | reflexivity]].
    + destruct (sbisim_step _ _ (ActExt μ1) _ hac l1) as (c2 & lc & h2).
      eexists. split; [eapply ParSync; [exact eq | exact lc | exact l2] | split; [exact h2 | reflexivity]].
  - intros α [c2 d2] l. inversion l as [α' x1 x2 y l1 | α' x y1 y2 l1 | μ1 μ2 x1 x2 y1 y2 eq l1 l2]; subst.
    + destruct (sbisim_step _ _ _ _ (sbisim_sym _ _ hac) l1) as (a2 & la & h2).
      eexists. split; [eapply ParLeft; exact la | split; [exact (sbisim_sym _ _ h2) | reflexivity]].
    + eexists. split; [eapply ParRight; exact l1 | split; [exact hac | reflexivity]].
    + destruct (sbisim_step _ _ (ActExt μ1) _ (sbisim_sym _ _ hac) l1) as (a2 & la & h2).
      eexists. split; [eapply ParSync; [exact eq | exact la | exact l2] | split; [exact (sbisim_sym _ _ h2) | reflexivity]].
Qed.

End FW_Bisim.
(* end hide *)
