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
(* end hide *)
(* begin hide *)
From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base countable decidable gmultiset.
From TestingTheory Require Import ActTau gLts Bisimulation InteractionBetweenLts SyncActions
  MemAction InteractionUnion MemForwarder MultisetLTSConstruction.

Section ForwarderMem.

#[local] Hint Mode ExtAction ! : typeclass_instances.

Context `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest} `{SA : !SyncAction Aproc Atest}.

Definition fw_inter_mem (μ : Aproc) (a : MemAct Atest) : Prop :=
  match a with
  | msg η => sync μ η ∧ non_blocking η
  | cobar _ => False
  end.

#[global] Instance fw_inter_mem_dec : RelDecision fw_inter_mem.
Proof. intros μ [η | η]; simpl; apply _. Defined.

Context `{gLtsEqP : !gLtsEq P Hp}.
Context `{PI : !Prop_of_Inter P (MO (MemAct Atest)) Aproc (MemAct Atest) fw_inter_mem}.

Definition toFw : gLts (P * MO (MemAct Atest)) (@ExtAction_sum Aproc (MemAct Atest) _ _) := inter_union_lts.

Definition toFwEq : gLtsEq (P * MO (MemAct Atest)) (@ExtAction_sum Aproc (MemAct Atest) _ _) := inter_union_ltsEq.

#[local] Existing Instance toFwEq.

Lemma toFw_boomerang (p : P * MO (MemAct Atest)) (η : Atest) :
  non_blocking η → ∃ p', p ⟶[inr (cobar η)] p' ∧ p' ⟶[inr (msg η)] p.
Proof.
  intros nb. destruct p as (p, m).
  exists (p, {[+ msg η +]} ⊎ m). split.
  - apply (ParRight (ActExt (inr (cobar η)))). by apply (lts_multiset_add m (msg η) (cobar η)).
  - apply (ParRight (ActExt (inr (msg η)))). by apply (lts_multiset_minus m (msg η)).
Qed.

Lemma toFw_feedback (p1 p2 p3 : P * MO (MemAct Atest)) (η : Atest) μ :
  non_blocking η → sync_mem μ η →
  p1 ⟶[inr (msg η)] p2 → p2 ⟶[μ] p3 → p1 ⟶⋍ p3 ∨ p1 ⋍ p3.
Proof.
  intros nb hs l1 l2.
  inversion l1 as [𝜆 s1 s'1 s2 l | 𝜆 s1 s2 s'2 lm |]; subst; [done |].
  assert (heq : {[+ msg η +]} ⊎ s'2 = s2)
    by exact (non_blocking_action_in_ms (A := MemAct Atest) s2 (msg η) s'2 nb lm).
  subst.
  destruct μ as [μ | [η' | η']]; simpl in hs.
  - inversion l2 as [𝜆 s1' s'1 s2' l | 𝜆 s1' s2' s''2 l |]; subst; [| done].
    left. exists (s'1, s'2). split; [| reflexivity].
    by apply (ParSync (inl μ) (inr (msg η))).
  - exfalso. inversion l2 as [𝜆 s1' s'1 s2' l | 𝜆 s1' s2' s''2 lm2 |]; subst; [done |].
    inversion lm2 as [m x μ' duo nbx | m x nbx]; subst.
    + destruct x; simpl in *; done.
    + by apply (dual_blocks η' η nb hs).
  - subst. inversion l2 as [𝜆 s1' s'1 s2' l | 𝜆 s1' s2' s''2 lm2 |]; subst; [done |].
    inversion lm2 as [m x μ' duo nbx | m x nbx]; subst.
    + destruct x as [η'' | η'']; simpl in duo, nbx; [| done]. subst.
      right. reflexivity.
    + done.
Qed.

Lemma toFw_delay (p q r : P * MO (MemAct Atest)) (η : Atest) 𝜆 :
  non_blocking η → p ⟶[inr (msg η)] q → q ⟶{𝜆} r →
  ∃ t, p ⟶{𝜆} t ∧ t ⟶⋍[inr (msg η)] r.
Proof.
  intros nb l1 l2.
  inversion l1 as [𝜆1 s1 s'1 s2 l | 𝜆1 s1 s2 s'2 lm |]; subst; [done |].
  inversion l2 as [𝜆' s1' s'1 s2' l | 𝜆' s1' s2' s''2 l' | a1 a2 s1' s'1 s2' s''2 hs l l']; subst.
  - exists (s'1, s2). split; [by apply ParLeft |].
    exists (s'1, s'2). split; [by apply (ParRight (ActExt (inr (msg η)))) | reflexivity].
  - destruct 𝜆 as [[μ1 | μ2] |]; simpl in l'; [done | | inversion l'].
    destruct (delay_in_ms (msg η) (ActExt μ2) s2 s'2 s''2 nb lm l') as (m & lm1 & (m' & lm2 & heq)).
    exists (s1, m). split; [by apply (ParRight (ActExt (inr μ2))) |].
    exists (s1, m'). split; [by apply (ParRight (ActExt (inr (msg η)))) | split; [reflexivity | exact heq]].
  - destruct a1 as [μ1 | ], a2 as [ | μ2]; simpl in hs; try done.
    destruct (delay_in_ms (msg η) (ActExt μ2) s2 s'2 s''2 nb lm l') as (m & lm1 & (m' & lm2 & heq)).
    exists (s'1, m). split; [by apply (ParSync (inl μ1) (inr μ2)) |].
    exists (s'1, m'). split; [by apply (ParRight (ActExt (inr (msg η)))) | split; [reflexivity | exact heq]].
Qed.

#[global] Instance toFw_gLtsFWMem : gLtsFWMem (P * MO (MemAct Atest)) Aproc Atest :=
  {| fwm_boomerang := toFw_boomerang;
     fwm_feedback := toFw_feedback;
     fwm_delay := toFw_delay |}.

End ForwarderMem.
(* end hide *)
