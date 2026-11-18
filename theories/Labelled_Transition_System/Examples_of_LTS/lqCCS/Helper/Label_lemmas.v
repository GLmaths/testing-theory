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
From Stdlib.Lists Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.
From stdpp Require Import base gmultiset countable decidable list numbers.
From TestingTheory Require Import ActTau.
From TestingTheory Require Import lqCCS.General_definition.Algebra lqCCS.quantum_mem.Syntax.
From TestingTheory Require Import lqCCS.lqCCS_prog.Syntax lqCCS.Helper.De_Brujin_lemmas lqCCS.General_definition.Parallel_choice_LTS lqCCS.quantum_mem.LTS lqCCS.lqCCS_prog.LTS lqCCS.lqCCS_par_Qmem.LTS lqCCS.lqCCS_process.LTS.LTS lqCCS.Helper.Conf_labels.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

Section Label_Lemmas.
  Context `{lqP : lqCCS_Parameters}.

(* ** Renaming of labels *)

Lemma ren_lbl_ext 𝜆 : ∀ μ, ren_lbl S 𝜆 = ActExt μ → ∃ μ', 𝜆 = ActExt μ'.
Proof. destruct 𝜆 as [μ0|]; simpl; intros μ Ha; simplify_eq; eauto. Qed.

Lemma ren_action_comp f g μ : ren_action f (ren_action g μ) = ren_action (f ∘ g) μ.
Proof. destruct μ; simpl; by rewrite ?ren_chan_comp. Qed.

Lemma ren_lbl_comp f g 𝜆 : ren_lbl f (ren_lbl g 𝜆) = ren_lbl (f ∘ g) 𝜆.
Proof. destruct 𝜆; simpl; by rewrite ?ren_action_comp. Qed.

Lemma ren_action_ext f g μ : (∀ i, f i = g i) → ren_action f μ = ren_action g μ.
Proof. intros H. destruct μ; simpl; by rewrite ?(ren_chan_ext f g). Qed.

Lemma ren_lbl_ext_fun f g 𝜆 : (∀ i, f i = g i) → ren_lbl f 𝜆 = ren_lbl g 𝜆.
Proof. intros H. destruct 𝜆; simpl; by rewrite ?(ren_action_ext f g). Qed.

(* [ren_lbl (lift f) (ren_lbl S 𝜆) = ren_lbl S (ren_lbl f 𝜆)] *)
Lemma ren_lbl_lift_S f 𝜆 : ren_lbl (lift f) (ren_lbl S 𝜆) = ren_lbl S (ren_lbl f 𝜆).
Proof. rewrite !ren_lbl_comp. by apply ren_lbl_ext_fun. Qed.

Lemma ren_action_inj f :
  (∀ i j, f i = f j → i = j) → ∀ μ μ', ren_action f μ = ren_action f μ' → μ = μ'.
Proof.
  intros Hf [c v|c v| | |] [c' v'|c' v'| | |]; simpl; intros [=]; subst; try done.
  all: f_equal; by eapply ren_chan_inj.
Qed.

Lemma ren_lbl_inj f :
  (∀ i j, f i = f j → i = j) → ∀ 𝜆 𝜆', ren_lbl f 𝜆 = ren_lbl f 𝜆' → 𝜆 = 𝜆'.
Proof.
  intros Hf [μ|] [μ'|]; simpl; intros [=]; try done. f_equal. by eapply ren_action_inj.
Qed.

Lemma ren_lbl_swap01_SS 𝜆 : ren_lbl swap01 (ren_lbl S (ren_lbl S 𝜆)) = ren_lbl S (ren_lbl S 𝜆).
Proof. rewrite !ren_lbl_comp. apply ren_lbl_ext_fun. intros i. apply swap01_SS. Qed.

Lemma ren_lbl_add_S n 𝜆 : ren_lbl (Nat.add n) (ren_lbl S 𝜆) = ren_lbl (Nat.add (S n)) 𝜆.
Proof. rewrite ren_lbl_comp. apply ren_lbl_ext_fun. intros i. simpl. lia. Qed.

Lemma ren_lbl_add_0 𝜆 : ren_lbl (Nat.add 0) 𝜆 = 𝜆.
Proof. destruct 𝜆 as [[c v|c v| | |]|]; simpl; by rewrite ?ren_chan_add_0. Qed.

(* ** Renaming of the indices commutes with the transitions *)

Lemma prog_gstep_ren f g k 𝜆 P' :
  g ⟶ᵍ{𝜆}[k] P' → gren f g ⟶ᵍ{ren_lbl f 𝜆}[k] (ren f P').
Proof.
  induction 1 as [t P | t c v P | t U es qs P Hq | t M es qs n P Hq | t es qs P Hq | g1 g2 k 𝜆 P' Hg IH | g1 g2 k 𝜆 P' Hg IH]; simpl.
  - constructor.
  - rewrite (proj1 ren_subst). constructor.
  - by constructor.
  - rewrite (proj1 ren_subst). by constructor.
  - by constructor.
  - by apply pg_sumL.
  - by apply pg_sumR.
Qed.

Lemma prog_step_ren f P k 𝜆 P' :
  P ⟶ₚ{𝜆}[k] P' → ren f P ⟶ₚ{ren_lbl f 𝜆}[k] (ren f P').
Proof.
  intros Hs. revert f. induction Hs as [g k 𝜆 P' Hg | t c e v He | e P Q k 𝜆 P' He Hp IH | e P Q k 𝜆 Q' He Hp IH | P Q k 𝜆 P' Hp IH | P Q k 𝜆 Q' Hp IH | P Q t t' c v P' Q' Hp1 IH1 Hp2 IH2 | P Q t t' c v P' Q' Hp1 IH1 Hp2 IH2 | P k 𝜆 P' Hp IH | t P]; intros f; simpl in *.
  - apply pr_guard. by apply prog_gstep_ren.
  - by constructor.
  - by apply pr_iteT.
  - by apply pr_iteF.
  - by apply pr_parL.
  - by apply pr_parR.
  - by eapply pr_syncL; [apply IH1|apply IH2].
  - by eapply pr_syncR; [apply IH1|apply IH2].
  - apply pr_res. rewrite <- ren_lbl_lift_S. apply IH.
  - rewrite (proj1 ren_pr_subst). simpl. rewrite <- (proj1 tren_ren P). exact (pr_rec t (ren f P)).
Qed.

(* The converse, for an injective renaming. *)
Lemma prog_gstep_ren_inv f :
  (∀ i j, f i = f j → i = j) →
  ∀ g k 𝜆' X, gren f g ⟶ᵍ{𝜆'}[k] X →
  ∃ 𝜆 P', 𝜆' = ren_lbl f 𝜆 ∧ X = ren f P' ∧ g ⟶ᵍ{𝜆}[k] P'.
Proof.
  intros Hf g k 𝜆' X Hs. remember (gren f g) as RG eqn:ER. revert g ER.
  induction Hs as [t P | t c v P | t U es qs P Hq | t M es qs n P Hq | t es qs P Hq | g1 g2 k 𝜆 P' Hgs IH | g1 g2 k 𝜆 P' Hgs IH]; intros g0 ER;
    destruct g0 as [es0| |π0 P0|g1' g2']; simpl in ER; simplify_eq.
  all: try (destruct π0; simpl in *; simplify_eq).
  - exists τ, P0. split_and!; [done|done|constructor].
  - exists (c0 ? v), (P0 ⁅ v ⁆ᵥ).
    split_and!; [done|by rewrite (proj1 ren_subst)|constructor].
  - exists (⦅qs⦆ ! U0), P0. split_and!; [done|done|by constructor].
  - exists (M0 ⦅qs⦆? n), (P0 ⁅ VNat n ⁆ᵥ).
    split_and!; [done|by rewrite (proj1 ren_subst)|by constructor].
  - exists (reinit qs), P0. split_and!; [done|done|by constructor].
  - destruct (IH g1' eq_refl) as (𝜆0 & P'0 & -> & -> & Hg). exists 𝜆0, P'0. split_and!; [done|done|by apply pg_sumL].
  - destruct (IH g2' eq_refl) as (𝜆0 & P'0 & -> & -> & Hg). exists 𝜆0, P'0. split_and!; [done|done|by apply pg_sumR].
Qed.

Lemma prog_step_ren_inv f :
  (∀ i j, f i = f j → i = j) →
  ∀ P k 𝜆' X, ren f P ⟶ₚ{𝜆'}[k] X →
  ∃ 𝜆 P', 𝜆' = ren_lbl f 𝜆 ∧ X = ren f P' ∧ P ⟶ₚ{𝜆}[k] P'.
Proof.
  intros Hf P k 𝜆' X Hs. remember (ren f P) as RP eqn:ER. revert f Hf P ER.
  induction Hs as [g k 𝜆 P' Hg | t c e v Hev | e P Q k 𝜆 P' Hev Hst IH | e P Q k 𝜆 Q' Hev Hst IH | P Q k 𝜆 P' Hst IH | P Q k 𝜆 Q' Hst IH | P Q t t' c v P' Q' Hst1 IH1 Hst2 IH2 | P Q t t' c v P' Q' Hst1 IH1 Hst2 IH2 | P k 𝜆 P' Hst IH | t P]; intros f Hf P0 ER;
    destruct P0 as [t0 c0 e0|e0 P1 P2|P1 P2|P1|X0|t0 P1|g0]; simpl in ER; simplify_eq.
  - destruct (prog_gstep_ren_inv f Hf g0 _ _ _ Hg) as (𝜆0 & P'0 & -> & -> & Hg0).
    exists 𝜆0, P'0. split_and!; [done|done|by apply pr_guard].
  - exists (c0 ! v), 𝟘. split_and!; [done|done|by constructor].
  - destruct (IH f Hf P1 eq_refl) as (𝜆0 & P'0 & -> & -> & Hp).
    exists 𝜆0, P'0. split_and!; [done|done|by apply pr_iteT].
  - destruct (IH f Hf P2 eq_refl) as (𝜆0 & P'0 & -> & -> & Hp).
    exists 𝜆0, P'0. split_and!; [done|done|by apply pr_iteF].
  - destruct (IH f Hf P1 eq_refl) as (𝜆0 & P'0 & -> & -> & Hp).
    exists 𝜆0, (P'0 ∥ P2). split_and!; [done|done|by apply pr_parL].
  - destruct (IH f Hf P2 eq_refl) as (𝜆0 & P'0 & -> & -> & Hp).
    exists 𝜆0, (P1 ∥ P'0). split_and!; [done|done|by apply pr_parR].
  - destruct (IH1 f Hf P1 eq_refl) as (𝜆1 & P1' & E1 & -> & Hp1).
    destruct (IH2 f Hf P2 eq_refl) as (𝜆2 & P2' & E2 & -> & Hp2).
    destruct 𝜆1 as [[c1 v1|c1 v1| | |]|]; simpl in E1; simplify_eq.
    destruct 𝜆2 as [[c2 v2|c2 v2| | |]|]; simpl in E2; simplify_eq.
    assert (c1 = c2) by (eapply ren_chan_inj; [exact Hf|congruence]). subst.
    exists τ, (P1' ∥ P2'). split_and!; [done|done|by eapply pr_syncL].
  - destruct (IH1 f Hf P1 eq_refl) as (𝜆1 & P1' & E1 & -> & Hp1).
    destruct (IH2 f Hf P2 eq_refl) as (𝜆2 & P2' & E2 & -> & Hp2).
    destruct 𝜆1 as [[c1 v1|c1 v1| | |]|]; simpl in E1; simplify_eq.
    destruct 𝜆2 as [[c2 v2|c2 v2| | |]|]; simpl in E2; simplify_eq.
    assert (c1 = c2) by (eapply ren_chan_inj; [exact Hf|congruence]). subst.
    exists τ, (P1' ∥ P2'). split_and!; [done|done|by eapply pr_syncR].
  - destruct (IH (lift f) (lift_inj f Hf) P1 eq_refl) as (𝜆0 & P'0 & E0 & -> & Hp).
    destruct 𝜆0 as [[[c0|[|i]] v0|[c0|[|i]] v0|U' qs|M qs n|qs0]|]; simpl in E0;
      destruct 𝜆 as [[[c1|i1] v1|[c1|i1] v1|E1 qs1|M1 qs1 n1|qs2]|]; simpl in E0; simplify_eq.
    + exists ((CName c0) ! v0), (ν P'0). split_and!; [done|done|by apply pr_res].
    + exists ((CIdx i) ! v0), (ν P'0). split_and!; [done|done|by apply pr_res].
    + exists ((CName c0) ? v0), (ν P'0). split_and!; [done|done|by apply pr_res].
    + exists ((CIdx i) ? v0), (ν P'0). split_and!; [done|done|by apply pr_res].
    + exists (⦅qs⦆ ! U'), (ν P'0). split_and!; [done|done|by apply pr_res].
    + exists (M ⦅qs⦆? n), (ν P'0). split_and!; [done|done|by apply pr_res].
    + exists (reinit qs0), (ν P'0). split_and!; [done|done|by apply pr_res].
    + exists τ, (ν P'0). split_and!; [done|done|by apply pr_res].
  - exists τ, (P1 ⁅ (t0 ∶ rec ∙ P1)↑ ⁆ₚ).
    split_and!; [done| |constructor]. rewrite (proj1 ren_pr_subst), <- (proj1 tren_ren). done.
Qed.

End Label_Lemmas.

(* end hide *)
