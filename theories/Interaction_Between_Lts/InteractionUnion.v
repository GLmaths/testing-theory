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
From stdpp Require Import base countable decidable gmap.
From TestingTheory Require Import ActTau gLts Bisimulation InteractionBetweenLts UnionAction.

Definition ExtAction_sum {A1 A2 : Type} `{H1 : ExtAction A1} `{H2 : ExtAction A2} : ExtAction (A1 + A2) :=
  @ExtAction_union A1 A2 H1 H2 (λ _ _, False) (λ _ _, False_dec) (λ _ _ f, False_rect _ f).

Section Lift.

Context {A1 A2 : Type} `{H1 : ExtAction A1} `{H2 : ExtAction A2}.

Section Lift_left.

Context `{gLts1 : !gLts S1 H1}.

Definition lift_left_step (s : S1) (α : Act (A1 + A2)) (s' : S1) : Prop :=
  match α with
  | τ => s ⟶ s'
  | ActExt (inl μ1) => s ⟶[μ1] s'
  | ActExt (inr _) => False
  end.

Definition lift_left_performs (s : S1) (α : Act (A1 + A2)) : Prop :=
  match α with
  | τ => s ⟶
  | ActExt (inl μ1) => s ⟶[μ1]
  | ActExt (inr _) => False
  end.

Definition decide_lift_left_step s α s' : Decision (lift_left_step s α s').
Proof. destruct α as [[] |]; simpl; apply _. Defined.

Definition decide_lift_left_performs s α : Decision (lift_left_performs s α).
Proof. destruct α as [[] |]; simpl; apply _. Defined.

Lemma lift_left_performs_spec1 s α : lift_left_performs s α → { s' | lift_left_step s α s' }.
Proof. destruct α as [[] |]; simpl; [apply lts_performs_spec1 | done | apply lts_performs_spec1]. Defined.

Lemma lift_left_performs_spec2 s α : { s' | lift_left_step s α s' } → lift_left_performs s α.
Proof. destruct α as [[] |]; simpl; [apply lts_performs_spec2 | by intros [] | apply lts_performs_spec2]. Qed.

Definition lift_left_lts : gLts S1 (@ExtAction_sum A1 A2 H1 H2) :=
  {| lts_step := lift_left_step;
     lts_state_eqdec := _;
     lts_step_decidable := decide_lift_left_step;
     lts_performs := lift_left_performs;
     lts_performs_decidable := decide_lift_left_performs;
     lts_performs_spec1 := lift_left_performs_spec1;
     lts_performs_spec2 := lift_left_performs_spec2 |}.

End Lift_left.

Section Lift_right.

Context `{gLts2 : !gLts S2 H2}.

Definition lift_right_step (s : S2) (α : Act (A1 + A2)) (s' : S2) : Prop :=
  match α with
  | τ => s ⟶ s'
  | ActExt (inl _) => False
  | ActExt (inr μ2) => s ⟶[μ2] s'
  end.

Definition lift_right_performs (s : S2) (α : Act (A1 + A2)) : Prop :=
  match α with
  | τ => s ⟶
  | ActExt (inl _) => False
  | ActExt (inr μ2) => s ⟶[μ2]
  end.

Definition decide_lift_right_step s α s' : Decision (lift_right_step s α s').
Proof. destruct α as [[] |]; simpl; apply _. Defined.

Definition decide_lift_right_performs s α : Decision (lift_right_performs s α).
Proof. destruct α as [[] |]; simpl; apply _. Defined.

Lemma lift_right_performs_spec1 s α : lift_right_performs s α → { s' | lift_right_step s α s' }.
Proof. destruct α as [[] |]; simpl; [done | apply lts_performs_spec1 | apply lts_performs_spec1]. Defined.

Lemma lift_right_performs_spec2 s α : { s' | lift_right_step s α s' } → lift_right_performs s α.
Proof. destruct α as [[] |]; simpl; [by intros [] | apply lts_performs_spec2 | apply lts_performs_spec2]. Qed.

Definition lift_right_lts : gLts S2 (@ExtAction_sum A1 A2 H1 H2) :=
  {| lts_step := lift_right_step;
     lts_state_eqdec := _;
     lts_step_decidable := decide_lift_right_step;
     lts_performs := lift_right_performs;
     lts_performs_decidable := decide_lift_right_performs;
     lts_performs_spec1 := lift_right_performs_spec1;
     lts_performs_spec2 := lift_right_performs_spec2 |}.

End Lift_right.

End Lift.

Section Inter_union.

Context `{M : Prop_of_Inter S1 S2 A1 A2 inter}.

Notation EA := (@ExtAction_sum A1 A2 H1 H2).

Definition inter_sum (a1 a2 : A1 + A2) : Prop :=
  match a1, a2 with
  | inl μ1, inr μ2 => inter μ1 μ2
  | _, _ => False
  end.

#[local] Instance inter_sum_dec : RelDecision inter_sum.
Proof. intros [] []; simpl; apply _. Defined.

Definition sum_essential_left (s1 : S1) : gset (A1 + A2) :=
  set_map inl (lts_essential_actions_left s1).

Definition sum_essential_right (s2 : S2) : gset (A1 + A2) :=
  set_map inr (lts_essential_actions_right s2).

Definition sum_co_inter_left (ξ : A1 + A2) (s1 : S1) : gset (A1 + A2) :=
  match ξ with
  | inl _ => ∅
  | inr ξ2 => set_map inl (lts_co_inter_action_left ξ2 s1)
  end.

Definition sum_co_inter_right (ξ : A1 + A2) (s2 : S2) : gset (A1 + A2) :=
  match ξ with
  | inl ξ1 => set_map inr (lts_co_inter_action_right ξ1 s2)
  | inr _ => ∅
  end.

Lemma inl_elem_of_sum (x : A1) (X : gset A1) :
  inl x ∈ (set_map inl X : gset (A1 + A2)) ↔ x ∈ X.
Proof. rewrite elem_of_map. split; [by intros (y & [=->] & hy) | intros hx; by exists x]. Qed.

Lemma inr_elem_of_sum (x : A2) (X : gset A2) :
  inr x ∈ (set_map inr X : gset (A1 + A2)) ↔ x ∈ X.
Proof. rewrite elem_of_map. split; [by intros (y & [=->] & hy) | intros hx; by exists x]. Qed.

Lemma inr_not_elem_of_sum (x : A2) (X : gset A1) :
  inr x ∉ (set_map inl X : gset (A1 + A2)).
Proof. rewrite elem_of_map. by intros (y & ? & _). Qed.

Lemma inl_not_elem_of_sum (x : A1) (X : gset A2) :
  inl x ∉ (set_map inr X : gset (A1 + A2)).
Proof. rewrite elem_of_map. by intros (y & ? & _). Qed.

Definition sum_essential_left_spec (s1 : S1) (ξ : A1 + A2) :
  ξ ∈ sum_essential_left s1 → { s'1 | lift_left_step s1 (ActExt ξ) s'1 }.
Proof.
  destruct ξ as [ξ1 | ξ2]; intros hξ.
  - apply lts_essential_action_spec_left. by apply inl_elem_of_sum in hξ.
  - exfalso. by apply inr_not_elem_of_sum in hξ.
Defined.

Definition sum_essential_right_spec (s2 : S2) (ξ : A1 + A2) :
  ξ ∈ sum_essential_right s2 → { s'2 | lift_right_step s2 (ActExt ξ) s'2 }.
Proof.
  destruct ξ as [ξ1 | ξ2]; intros hξ.
  - exfalso. by apply inl_not_elem_of_sum in hξ.
  - apply lts_essential_action_spec_right. by apply inr_elem_of_sum in hξ.
Defined.

Lemma sum_essential_spec_interact (s1 : S1) a1 s'1 (s2 : S2) a2 s'2 :
  lift_left_step s1 (ActExt a1) s'1 → lift_right_step s2 (ActExt a2) s'2 → inter_sum a1 a2 →
  a1 ∈ sum_essential_left s1 ∨ a2 ∈ sum_essential_right s2.
Proof.
  destruct a1 as [μ1 | ], a2 as [ | μ2]; simpl; try done.
  intros l1 l2 hs.
  destruct (lts_essential_actions_spec_interact s1 μ1 s'1 s2 μ2 s'2 l1 l2 hs) as [h | h].
  - left. by apply inl_elem_of_sum.
  - right. by apply inr_elem_of_sum.
Qed.

Lemma sum_co_inter_left_spec s1 s'1 ξ a s2 :
  ξ ∈ sum_essential_right s2 → lift_left_step s1 (ActExt a) s'1 → inter_sum a ξ →
  a ∈ sum_co_inter_left ξ s1.
Proof.
  destruct a as [μ1 | ], ξ as [ξ1 | ξ2]; simpl; try done.
  intros hξ l hs. apply inr_elem_of_sum in hξ. apply inl_elem_of_sum.
  by eapply lts_co_inter_action_spec_left.
Qed.

Lemma sum_co_inter_right_spec s2 s'2 ξ a s1 :
  ξ ∈ sum_essential_left s1 → lift_right_step s2 (ActExt a) s'2 → inter_sum ξ a →
  a ∈ sum_co_inter_right ξ s2.
Proof.
  destruct a as [ | μ2], ξ as [ξ1 | ξ2]; simpl; try done.
  intros hξ l hs. apply inl_elem_of_sum in hξ. apply inr_elem_of_sum.
  by eapply lts_co_inter_action_spec_right.
Qed.

Definition Prop_of_Inter_sum :
  @Prop_of_Inter S1 S2 (A1 + A2) (A1 + A2) inter_sum EA lift_left_lts EA lift_right_lts :=
  @MkProp_of_Inter S1 S2 (A1 + A2) (A1 + A2) inter_sum EA lift_left_lts EA lift_right_lts
    inter_sum_dec
    sum_essential_left sum_essential_left_spec
    sum_essential_right sum_essential_right_spec
    sum_essential_spec_interact
    sum_co_inter_left sum_co_inter_left_spec
    sum_co_inter_right sum_co_inter_right_spec.

Definition inter_union_lts : gLts (S1 * S2) EA :=
  @inter_lts _ inter_sum S1 S2 EA lift_left_lts lift_right_lts Prop_of_Inter_sum.

End Inter_union.

Section Inter_union_eq.

#[local] Hint Mode ExtAction ! : typeclass_instances.

Context `{H1 : ExtAction A1} `{H2 : ExtAction A2}.
Context `{E1 : !gLtsEq S1 H1} `{E2 : !gLtsEq S2 H2}.
Context `{M : !Prop_of_Inter S1 S2 A1 A2 inter}.

#[local] Existing Instance inter_union_lts.

Definition inter_union_eq (x y : S1 * S2) : Prop := x.1 ⋍ y.1 ∧ x.2 ⋍ y.2.

Lemma inter_union_eq_equiv : Equivalence inter_union_eq.
Proof.
  split.
  - intros x. split; reflexivity.
  - intros x y [h1 h2]. split; by symmetry.
  - intros x y z [h1 h2] [h1' h2']. split; by etrans.
Qed.

Lemma lift_left_eq_spec (s1 r1 r'1 : S1) (α : Act (A1 + A2)) :
  s1 ⋍ r1 → lift_left_step r1 α r'1 → ∃ t1, lift_left_step s1 α t1 ∧ t1 ⋍ r'1.
Proof.
  intros he l. destruct α as [[μ1 | μ2] |]; simpl in *; [| done |].
  - destruct (eq_spec s1 r'1 (ActExt μ1)) as (t1 & l1 & e1); [by exists r1 |]. by exists t1.
  - destruct (eq_spec s1 r'1 τ) as (t1 & l1 & e1); [by exists r1 |]. by exists t1.
Qed.

Lemma lift_right_eq_spec (s2 r2 r'2 : S2) (α : Act (A1 + A2)) :
  s2 ⋍ r2 → lift_right_step r2 α r'2 → ∃ t2, lift_right_step s2 α t2 ∧ t2 ⋍ r'2.
Proof.
  intros he l. destruct α as [[μ1 | μ2] |]; simpl in *; [done | |].
  - destruct (eq_spec s2 r'2 (ActExt μ2)) as (t2 & l2 & e2); [by exists r2 |]. by exists t2.
  - destruct (eq_spec s2 r'2 τ) as (t2 & l2 & e2); [by exists r2 |]. by exists t2.
Qed.

Lemma inter_union_eq_spec (x y : S1 * S2) (α : Act (A1 + A2)) :
  (∃ r, inter_union_eq x r ∧ r ⟶{α} y) → ∃ r, x ⟶{α} r ∧ inter_union_eq r y.
Proof.
  destruct x as (s1, s2). intros ((r1, r2) & [h1 h2] & l). simpl in *.
  inversion l as [α' r1' r'1 r2' l1 | α' r1' r2' r'2 l2 | a1 a2 r1' r'1 r2' r'2 hs l1 l2]; subst.
  - destruct (lift_left_eq_spec s1 r1 r'1 α h1 l1) as (t1 & lt1 & e1).
    exists (t1, s2). split; [by apply ParLeft | done].
  - destruct (lift_right_eq_spec s2 r2 r'2 α h2 l2) as (t2 & lt2 & e2).
    exists (s1, t2). split; [by apply ParRight | done].
  - destruct (lift_left_eq_spec s1 r1 r'1 (ActExt a1) h1 l1) as (t1 & lt1 & e1).
    destruct (lift_right_eq_spec s2 r2 r'2 (ActExt a2) h2 l2) as (t2 & lt2 & e2).
    exists (t1, t2). split; [by eapply ParSync | done].
Qed.

Definition inter_union_ltsEq : gLtsEq (S1 * S2) (@ExtAction_sum A1 A2 H1 H2) :=
  {| gLtsEq_gLts := inter_union_lts;
     eq_rel := inter_union_eq;
     eq_rel_eq := inter_union_eq_equiv;
     eq_spec := inter_union_eq_spec |}.

End Inter_union_eq.
