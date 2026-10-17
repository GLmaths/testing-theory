(* begin hide *)
(*
   Copyright (c) 2026 Gaëtan Lopez <glopez@irif.fr>

   Permission is hereby granted, free of charge, to any person obtaining a copy
   of this software and associated documentation files (the "Software"), to deal
   in the Software without restriction, including without limitation the rights
   to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
   copies of the Software, and to permit persons to whom the Software is
   furnished to do so, subject to the following conditions:

   The above copyright notice and this permission notice shall be included in all
   copies or substantial portions of the Software.

   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
   OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
   SOFTWARE.
*)

From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base tactics decidable finite gmap.
From TestingTheory Require Import ActTau gLts SyncActions Subset_Act InteractionUnion
  Bisimulation InteractionBetweenLts coFiniteImage InListPropHelper.

Section Sum_LTS.
  Context {P Q A1 A2 : Type} {H1 : ExtAction A1} {H2 : ExtAction A2}
    {gLtsP : gLts P H1} {gLtsQ : gLts Q H2}.

  Definition sum_step (s : P + Q) (𝜆 : Labels (A1 + A2)) (s' : P + Q) : Prop :=
    match s, s' with
    | inl p, inl p' => lift_left_step p 𝜆 p'
    | inr q, inr q' => lift_right_step q 𝜆 q'
    | _, _ => False
    end.

  Definition sum_performs (s : P + Q) (𝜆 : Labels (A1 + A2)) : Prop :=
    match s with
    | inl p => lift_left_performs p 𝜆
    | inr q => lift_right_performs q 𝜆
    end.

  Definition gLts_sum : gLts (P + Q) (@ExtAction_sum A1 A2 H1 H2).
  Proof.
    refine {| lts_step := sum_step; lts_performs := sum_performs |}.
    - intros [p | q] 𝜆 [p' | q']; simpl;
        [apply decide_lift_left_step | apply _ | apply _ | apply decide_lift_right_step].
    - intros [p | q] 𝜆; simpl; [apply decide_lift_left_performs | apply decide_lift_right_performs].
    - intros [p | q] 𝜆 h; simpl in h.
      + destruct (lift_left_performs_spec1 p 𝜆 h) as (p' & tr). by exists (inl p').
      + destruct (lift_right_performs_spec1 q 𝜆 h) as (q' & tr). by exists (inr q').
    - intros [p | q] 𝜆 ([p' | q'] & tr); simpl in *; try done.
      + apply lift_left_performs_spec2. by exists p'.
      + apply lift_right_performs_spec2. by exists q'.
  Defined.

  Context {At : Type} {Ht : ExtAction At} {SA1 : SyncAction A1 At} {SA2 : SyncAction A2 At}.

  Definition sync_sum (a : A1 + A2) (β : At) : Prop :=
    match a with
    | inl a1 => sync a1 β
    | inr a2 => sync a2 β
    end.

  Definition SyncAction_sum : @SyncAction (A1 + A2) At ExtAction_sum Ht.
  Proof. refine {| sync := sync_sum |}. intros [a1 | a2] β; simpl; apply _. Defined.

  #[local] Hint Extern 0 (ExtAction (A1 + A2)) => exact ExtAction_sum : typeclass_instances.
  #[local] Existing Instance gLts_sum.
  #[local] Existing Instance SyncAction_sum.

  Lemma sum_step_inl (p p' : P) (μ : A1) : (inl p : P + Q) ⟶[inl μ : A1 + A2] inl p' ↔ p ⟶[μ] p'.
  Proof. done. Qed.

  Lemma sum_step_inr (q q' : Q) (μ : A2) : (inr q : P + Q) ⟶[inr μ : A1 + A2] inr q' ↔ q ⟶[μ] q'.
  Proof. done. Qed.

  Lemma coR_inl (p : P) (β : At) : β ∈ coR (H := gLts_sum) (SA := SyncAction_sum) (inl p) ↔ β ∈ coR p.
  Proof.
    split.
    - intros ([μ | μ] & acc & hs & b); [by exists μ | done].
    - intros (μ & acc & hs & b). by exists (inl μ).
  Qed.

  Lemma coR_inr (q : Q) (β : At) : β ∈ coR (H := gLts_sum) (SA := SyncAction_sum) (inr q) ↔ β ∈ coR q.
  Proof.
    split.
    - intros ([μ | μ] & acc & hs & b); [done | by exists μ].
    - intros (μ & acc & hs & b). by exists (inr μ).
  Qed.

  Lemma map_coR_inl {PreA : Type} (Γ : At → PreA) (p : P) x :
    x ∈ ⌈ Γ ⌉ (coR (H := gLts_sum) (SA := SyncAction_sum) (inl p)) ↔ x ∈ ⌈ Γ ⌉ (coR p).
  Proof.
    split; intros (β & hβ & ->); exists β; split; [by apply coR_inl | done | by apply coR_inl | done].
  Qed.

  Lemma map_coR_inr {PreA : Type} (Γ : At → PreA) (q : Q) x :
    x ∈ ⌈ Γ ⌉ (coR (H := gLts_sum) (SA := SyncAction_sum) (inr q)) ↔ x ∈ ⌈ Γ ⌉ (coR q).
  Proof.
    split; intros (β & hβ & ->); exists β; split; [by apply coR_inr | done | by apply coR_inr | done].
  Qed.
End Sum_LTS.
Section Sum_LTS_eq.
  Context {P Q A1 A2 : Type} {H1 : ExtAction A1} {H2 : ExtAction A2}
    {gLtsEqP : gLtsEq P H1} {gLtsEqQ : gLtsEq Q H2}.

  Definition sum_eq (s s' : P + Q) : Prop :=
    match s, s' with
    | inl p, inl p' => p ⋍ p'
    | inr q, inr q' => q ⋍ q'
    | _, _ => False
    end.

  Lemma sum_eq_equivalence : Equivalence sum_eq.
  Proof.
    split.
    - intros [p | q]; simpl; reflexivity.
    - intros [p | q] [p' | q'] h; simpl in *; try done; by symmetry.
    - intros [p1 | q1] [p2 | q2] [p3 | q3] h1 h2; simpl in *; try done; by etransitivity.
  Qed.

  Definition gLtsEq_sum : gLtsEq (P + Q) (@ExtAction_sum A1 A2 H1 H2).
  Proof.
    refine {| gLtsEq_gLts := gLts_sum; eq_rel := sum_eq; eq_rel_eq := sum_eq_equivalence |}.
    intros [p | q] [p' | q'] 𝜆 ([r | r] & e & l); simpl in *; try done;
      destruct 𝜆 as [[μ | μ] |]; simpl in l; try done.
    - destruct (eq_spec p p' (ActExt μ) (ex_intro _ r (conj e l))) as (r' & l' & e').
      by exists (inl r').
    - destruct (eq_spec p p' τ (ex_intro _ r (conj e l))) as (r' & l' & e').
      by exists (inl r').
    - destruct (eq_spec q q' (ActExt μ) (ex_intro _ r (conj e l))) as (r' & l' & e').
      by exists (inr r').
    - destruct (eq_spec q q' τ (ex_intro _ r (conj e l))) as (r' & l' & e').
      by exists (inr r').
  Defined.
End Sum_LTS_eq.

Section Sum_LTS_inter.
  Context {P Q T A1 A2 At : Type} {H1 : ExtAction A1} {H2 : ExtAction A2} {Ht : ExtAction At}.
  Context {gLtsP : gLts P H1} {gLtsQ : gLts Q H2} {gLtsT : gLts T Ht}.
  Context {SA1 : SyncAction A1 At} {SA2 : SyncAction A2 At}.
  Context (PIP : @Prop_of_Inter P T A1 At (@sync _ _ _ _ SA1) H1 gLtsP Ht gLtsT)
          (PIQ : @Prop_of_Inter Q T A2 At (@sync _ _ _ _ SA2) H2 gLtsQ Ht gLtsT).

  #[local] Hint Extern 0 (ExtAction (A1 + A2)) => exact ExtAction_sum : typeclass_instances.

  Notation leftP := (@lts_essential_actions_left _ _ _ _ _ _ _ _ _ PIP).
  Notation leftQ := (@lts_essential_actions_left _ _ _ _ _ _ _ _ _ PIQ).
  Notation rightP := (@lts_essential_actions_right _ _ _ _ _ _ _ _ _ PIP).
  Notation rightQ := (@lts_essential_actions_right _ _ _ _ _ _ _ _ _ PIQ).

  Definition Prop_of_Inter_sum :
    @Prop_of_Inter (P + Q) T (A1 + A2) At (@sync _ _ _ _ SyncAction_sum)
      ExtAction_sum gLts_sum Ht gLtsT.
  Proof.
    refine {| inter_dec := @sync_dec _ _ _ _ SyncAction_sum;
              lts_essential_actions_left s :=
                match s with
                | inl p => set_map inl (leftP p)
                | inr q => set_map inr (leftQ q)
                end;
              lts_essential_actions_right t := rightP t ∪ rightQ t;
              lts_co_inter_action_left ξ s :=
                match s with
                | inl p => set_map inl (@lts_co_inter_action_left _ _ _ _ _ _ _ _ _ PIP ξ p ∪ leftP p)
                | inr q => set_map inr (@lts_co_inter_action_left _ _ _ _ _ _ _ _ _ PIQ ξ q ∪ leftQ q)
                end;
              lts_co_inter_action_right ξ t :=
                match ξ with
                | inl a => @lts_co_inter_action_right _ _ _ _ _ _ _ _ _ PIP a t
                | inr a => @lts_co_inter_action_right _ _ _ _ _ _ _ _ _ PIQ a t
                end |}.
    - intros [p | q] [a | a] h.
      + assert (ha : a ∈ leftP p) by (apply elem_of_map in h as (? & e & ?); by injection e as ->).
        destruct (@lts_essential_action_spec_left _ _ _ _ _ _ _ _ _ PIP p a ha) as (p' & l).
        by exists (inl p').
      + exfalso. apply elem_of_map in h as (? & e & _). done.
      + exfalso. apply elem_of_map in h as (? & e & _). done.
      + assert (ha : a ∈ leftQ q) by (apply elem_of_map in h as (? & e & ?); by injection e as ->).
        destruct (@lts_essential_action_spec_left _ _ _ _ _ _ _ _ _ PIQ q a ha) as (q' & l).
        by exists (inr q').
    - intros t ξ h. destruct (decide (ξ ∈ rightP t)) as [h' | h'].
      + exact (@lts_essential_action_spec_right _ _ _ _ _ _ _ _ _ PIP t ξ h').
      + assert (h'' : ξ ∈ rightQ t) by set_solver.
        exact (@lts_essential_action_spec_right _ _ _ _ _ _ _ _ _ PIQ t ξ h'').
    - intros [p | q] [a | a] [p' | q'] t μ2 t' l1 l2 hs; simpl in l1; try done.
      + destruct (@lts_essential_actions_spec_interact _ _ _ _ _ _ _ _ _ PIP p a p' t μ2 t' l1 l2 hs)
          as [h | h]; [left; by apply elem_of_map_2 | right; set_solver].
      + destruct (@lts_essential_actions_spec_interact _ _ _ _ _ _ _ _ _ PIQ q a q' t μ2 t' l1 l2 hs)
          as [h | h]; [left; by apply elem_of_map_2 | right; set_solver].
    - intros [p | q] [p' | q'] ξ [a | a] t hξ l hs; simpl in l; try done.
      + apply elem_of_map_2. destruct (decide (ξ ∈ rightP t)) as [h' | h'].
        * apply elem_of_union_l.
          exact (@lts_co_inter_action_spec_left _ _ _ _ _ _ _ _ _ PIP p p' ξ a t h' l hs).
        * assert (h'' : ξ ∈ rightQ t) by set_solver.
          destruct (@lts_essential_action_spec_right _ _ _ _ _ _ _ _ _ PIQ t ξ h'') as (t' & lt).
          destruct (@lts_essential_actions_spec_interact _ _ _ _ _ _ _ _ _ PIP p a p' t ξ t' l lt hs)
            as [h | h]; [by apply elem_of_union_r | done].
      + apply elem_of_map_2. destruct (decide (ξ ∈ rightQ t)) as [h' | h'].
        * apply elem_of_union_l.
          exact (@lts_co_inter_action_spec_left _ _ _ _ _ _ _ _ _ PIQ q q' ξ a t h' l hs).
        * assert (h'' : ξ ∈ rightP t) by set_solver.
          destruct (@lts_essential_action_spec_right _ _ _ _ _ _ _ _ _ PIP t ξ h'') as (t' & lt).
          destruct (@lts_essential_actions_spec_interact _ _ _ _ _ _ _ _ _ PIQ q a q' t ξ t' l lt hs)
            as [h | h]; [by apply elem_of_union_r | done].
    - intros t t' [a | a] μ [p | q] hξ l hs; simpl in hξ.
      + assert (ha : a ∈ leftP p) by (apply elem_of_map in hξ as (? & e & ?); by injection e as ->).
        exact (@lts_co_inter_action_spec_right _ _ _ _ _ _ _ _ _ PIP t t' a μ p ha l hs).
      + exfalso. apply elem_of_map in hξ as (? & e & _). done.
      + exfalso. apply elem_of_map in hξ as (? & e & _). done.
      + assert (ha : a ∈ leftQ q) by (apply elem_of_map in hξ as (? & e & ?); by injection e as ->).
        exact (@lts_co_inter_action_spec_right _ _ _ _ _ _ _ _ _ PIQ t t' a μ q ha l hs).
  Defined.
End Sum_LTS_inter.

Section Sum_LTS_cofinite.
  Context {P Q A1 A2 At : Type} {H1 : ExtAction A1} {H2 : ExtAction A2} {Ht : ExtAction At}.
  Context {gLtsP : gLts P H1} {gLtsQ : gLts Q H2}.
  Context {SA1 : SyncAction A1 At} {SA2 : SyncAction A2 At}.
  Context `{CFIP : !@coFiniteImagegLts P At A1 H1 gLtsP Ht SA1}
          `{CFIQ : !@coFiniteImagegLts Q At A2 H2 gLtsQ Ht SA2}.

  #[local] Hint Extern 0 (ExtAction (A1 + A2)) => exact ExtAction_sum : typeclass_instances.
  #[local] Existing Instance gLts_sum.
  #[local] Existing Instance SyncAction_sum.

  Lemma sum_ext_inl (p p' : P) (𝜆 : At) :
    (∃ 𝜆' : A1 + A2, sync 𝜆' 𝜆 ∧ (inl p : P + Q) ⟶[𝜆'] inl p') ↔ (∃ μ, sync μ 𝜆 ∧ p ⟶[μ] p').
  Proof.
    split.
    - intros ([μ | μ] & hs & l); [by exists μ | done].
    - intros (μ & hs & l). by exists (inl μ).
  Qed.

  Lemma sum_ext_inr (q q' : Q) (𝜆 : At) :
    (∃ 𝜆' : A1 + A2, sync 𝜆' 𝜆 ∧ (inr q : P + Q) ⟶[𝜆'] inr q') ↔ (∃ μ, sync μ 𝜆 ∧ q ⟶[μ] q').
  Proof.
    split.
    - intros ([μ | μ] & hs & l); [done | by exists μ].
    - intros (μ & hs & l). by exists (inr μ).
  Qed.

  Definition sum_tau_finite (s : P + Q) :
    Finite (dsig (λ s', @lts_step (P + Q) (A1 + A2) ExtAction_sum gLts_sum s τ s')).
  Proof.
    unfold dsig. destruct s as [p | q].
    - eapply (in_list_finite (map (λ x, inl (proj1_sig x)) (enum (dsig (λ p', p ⟶ p'))))).
      intros [p' | q'] h%bool_decide_unpack; simpl in h; [| done].
      apply list_elem_of_fmap. exists (dexist p' h). split; [done | apply elem_of_enum].
    - eapply (in_list_finite (map (λ x, inr (proj1_sig x)) (enum (dsig (λ q', q ⟶ q'))))).
      intros [p' | q'] h%bool_decide_unpack; simpl in h; [done |].
      apply list_elem_of_fmap. exists (dexist q' h). split; [done | apply elem_of_enum].
  Defined.

  Definition sum_ext_dec (s : P + Q) (𝜆 : At) (s' : P + Q) :
    Decision (∃ 𝜆' : A1 + A2, sync 𝜆' 𝜆 ∧ s ⟶[𝜆'] s').
  Proof.
    destruct s as [p | q], s' as [p' | q'].
    - destruct (cofolts_next_states_decidable p 𝜆 p') as [h | h]; [left | right];
        by rewrite sum_ext_inl.
    - right. intros ([μ | μ] & ? & l); done.
    - right. intros ([μ | μ] & ? & l); done.
    - destruct (cofolts_next_states_decidable q 𝜆 q') as [h | h]; [left | right];
        by rewrite sum_ext_inr.
  Defined.

  #[local] Existing Instance sum_ext_dec.

  Definition sum_ext_finite (s : P + Q) (𝜆 : At) :
    Finite (dsig (λ s', ∃ 𝜆' : A1 + A2, sync 𝜆' 𝜆 ∧ s ⟶[𝜆'] s')).
  Proof.
    unfold dsig. destruct s as [p | q].
    - eapply (in_list_finite (map (λ x, inl (proj1_sig x))
                (enum (dsig (λ p', ∃ μ, sync μ 𝜆 ∧ p ⟶[μ] p'))))).
      intros [p' | q'] h%bool_decide_unpack; [| by destruct h as ([μ | μ] & ? & ?)].
      apply list_elem_of_fmap. exists (dexist p' (proj1 (sum_ext_inl p p' 𝜆) h)).
      split; [done | apply elem_of_enum].
    - eapply (in_list_finite (map (λ x, inr (proj1_sig x))
                (enum (dsig (λ q', ∃ μ, sync μ 𝜆 ∧ q ⟶[μ] q'))))).
      intros [p' | q'] h%bool_decide_unpack; [by destruct h as ([μ | μ] & ? & ?) |].
      apply list_elem_of_fmap. exists (dexist q' (proj1 (sum_ext_inr q q' 𝜆) h)).
      split; [done | apply elem_of_enum].
  Defined.

  Definition coFiniteImage_sum :
    @coFiniteImagegLts (P + Q) At (A1 + A2) ExtAction_sum gLts_sum Ht SyncAction_sum :=
    @MkCoFlts (P + Q) At (A1 + A2) ExtAction_sum gLts_sum Ht SyncAction_sum _
      sum_tau_finite sum_ext_dec sum_ext_finite.
End Sum_LTS_cofinite.
Section Lift_inter.
  Context {P Q T A1 A2 At : Type} {H1 : ExtAction A1} {H2 : ExtAction A2} {Ht : ExtAction At}.
  Context {gLtsP : gLts P H1} {gLtsQ : gLts Q H2} {gLtsT : gLts T Ht}.
  Context {SA1 : SyncAction A1 At} {SA2 : SyncAction A2 At}.

  Definition lift_left_inter
    (PIP : @Prop_of_Inter P T A1 At (@sync _ _ _ _ SA1) H1 gLtsP Ht gLtsT) :
    @Prop_of_Inter P T (A1 + A2) At (@sync _ _ _ _ SyncAction_sum)
      ExtAction_sum (lift_left_lts (H2 := H2)) Ht gLtsT.
  Proof.
    refine {| inter_dec := @sync_dec _ _ _ _ SyncAction_sum;
              lts_essential_actions_left p :=
                set_map inl (@lts_essential_actions_left _ _ _ _ _ _ _ _ _ PIP p);
              lts_essential_actions_right := @lts_essential_actions_right _ _ _ _ _ _ _ _ _ PIP;
              lts_co_inter_action_left ξ p :=
                set_map inl (@lts_co_inter_action_left _ _ _ _ _ _ _ _ _ PIP ξ p);
              lts_co_inter_action_right ξ t :=
                match ξ with
                | inl μ => @lts_co_inter_action_right _ _ _ _ _ _ _ _ _ PIP μ t
                | inr _ => ∅
                end |}.
    - intros p [μ | μ] h.
      + assert (hμ : μ ∈ @lts_essential_actions_left _ _ _ _ _ _ _ _ _ PIP p)
          by (apply elem_of_map in h as (? & e & ?); by injection e as ->).
        exact (@lts_essential_action_spec_left _ _ _ _ _ _ _ _ _ PIP p μ hμ).
      + exfalso. apply elem_of_map in h as (? & e & _). done.
    - intros t ξ h. exact (@lts_essential_action_spec_right _ _ _ _ _ _ _ _ _ PIP t ξ h).
    - intros p [μ | μ] p' t μ2 t' l1 l2 hs; [| done].
      destruct (@lts_essential_actions_spec_interact _ _ _ _ _ _ _ _ _ PIP p μ p' t μ2 t' l1 l2 hs)
        as [h | h]; [left; by apply elem_of_map_2 | by right].
    - intros p p' ξ [μ | μ] t hξ l hs; [| done].
      apply elem_of_map_2.
      exact (@lts_co_inter_action_spec_left _ _ _ _ _ _ _ _ _ PIP p p' ξ μ t hξ l hs).
    - intros t t' [μ | μ] μ2 p hξ l hs.
      + assert (hμ : μ ∈ @lts_essential_actions_left _ _ _ _ _ _ _ _ _ PIP p)
          by (apply elem_of_map in hξ as (? & e & ?); by injection e as ->).
        exact (@lts_co_inter_action_spec_right _ _ _ _ _ _ _ _ _ PIP t t' μ μ2 p hμ l hs).
      + exfalso. apply elem_of_map in hξ as (? & e & _). done.
  Defined.

  Definition lift_right_inter
    (PIQ : @Prop_of_Inter Q T A2 At (@sync _ _ _ _ SA2) H2 gLtsQ Ht gLtsT) :
    @Prop_of_Inter Q T (A1 + A2) At (@sync _ _ _ _ SyncAction_sum)
      ExtAction_sum (lift_right_lts (H1 := H1)) Ht gLtsT.
  Proof.
    refine {| inter_dec := @sync_dec _ _ _ _ SyncAction_sum;
              lts_essential_actions_left q :=
                set_map inr (@lts_essential_actions_left _ _ _ _ _ _ _ _ _ PIQ q);
              lts_essential_actions_right := @lts_essential_actions_right _ _ _ _ _ _ _ _ _ PIQ;
              lts_co_inter_action_left ξ q :=
                set_map inr (@lts_co_inter_action_left _ _ _ _ _ _ _ _ _ PIQ ξ q);
              lts_co_inter_action_right ξ t :=
                match ξ with
                | inl _ => ∅
                | inr μ => @lts_co_inter_action_right _ _ _ _ _ _ _ _ _ PIQ μ t
                end |}.
    - intros q [μ | μ] h.
      + exfalso. apply elem_of_map in h as (? & e & _). done.
      + assert (hμ : μ ∈ @lts_essential_actions_left _ _ _ _ _ _ _ _ _ PIQ q)
          by (apply elem_of_map in h as (? & e & ?); by injection e as ->).
        exact (@lts_essential_action_spec_left _ _ _ _ _ _ _ _ _ PIQ q μ hμ).
    - intros t ξ h. exact (@lts_essential_action_spec_right _ _ _ _ _ _ _ _ _ PIQ t ξ h).
    - intros q [μ | μ] q' t μ2 t' l1 l2 hs; [done |].
      destruct (@lts_essential_actions_spec_interact _ _ _ _ _ _ _ _ _ PIQ q μ q' t μ2 t' l1 l2 hs)
        as [h | h]; [left; by apply elem_of_map_2 | by right].
    - intros q q' ξ [μ | μ] t hξ l hs; [done |].
      apply elem_of_map_2.
      exact (@lts_co_inter_action_spec_left _ _ _ _ _ _ _ _ _ PIQ q q' ξ μ t hξ l hs).
    - intros t t' [μ | μ] μ2 q hξ l hs.
      + exfalso. apply elem_of_map in hξ as (? & e & _). done.
      + assert (hμ : μ ∈ @lts_essential_actions_left _ _ _ _ _ _ _ _ _ PIQ q)
          by (apply elem_of_map in hξ as (? & e & ?); by injection e as ->).
        exact (@lts_co_inter_action_spec_right _ _ _ _ _ _ _ _ _ PIQ t t' μ μ2 q hμ l hs).
  Defined.
End Lift_inter.
(* end hide *)
