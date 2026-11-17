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
From stdpp Require Import base countable decidable list numbers.
From TestingTheory Require Import ActTau.
From TestingTheory Require Import lqCCS.Language.Algebra lqCCS.Language.Quantum.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Helper_substitution.De_Brujin_lemmas lqCCS.Language.LTS.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

Section LqP.
  Context `{LP : lqCCS_Parameters}.

(* ** Renaming of labels *)

Lemma ren_lbl_ext l : ∀ a, ren_lbl S l = ActExt a → ∃ a', l = ActExt a'.
Proof. destruct l; simpl; intros a Ha; simplify_eq; eauto. Qed.

Lemma ren_action_comp f g a : ren_action f (ren_action g a) = ren_action (f ∘ g) a.
Proof. destruct a; simpl; by rewrite ?ren_chan_comp. Qed.

Lemma ren_lbl_comp f g l : ren_lbl f (ren_lbl g l) = ren_lbl (f ∘ g) l.
Proof. destruct l; simpl; by rewrite ?ren_action_comp. Qed.

Lemma ren_action_ext f g a : (∀ i, f i = g i) → ren_action f a = ren_action g a.
Proof. intros H. destruct a; simpl; by rewrite ?(ren_chan_ext f g). Qed.

Lemma ren_lbl_ext_fun f g l : (∀ i, f i = g i) → ren_lbl f l = ren_lbl g l.
Proof. intros H. destruct l; simpl; by rewrite ?(ren_action_ext f g). Qed.

(* [ren_lbl (lift f) (ren_lbl S l) = ren_lbl S (ren_lbl f l)] *)
Lemma ren_lbl_lift_S f l : ren_lbl (lift f) (ren_lbl S l) = ren_lbl S (ren_lbl f l).
Proof. rewrite !ren_lbl_comp. by apply ren_lbl_ext_fun. Qed.

Lemma ren_action_inj f :
  (∀ i j, f i = f j → i = j) → ∀ a a', ren_action f a = ren_action f a' → a = a'.
Proof.
  intros Hf [c v|c v| | |] [c' v'|c' v'| | |]; simpl; intros [=]; subst; try done.
  all: f_equal; by eapply ren_chan_inj.
Qed.

Lemma ren_lbl_inj f :
  (∀ i j, f i = f j → i = j) → ∀ l l', ren_lbl f l = ren_lbl f l' → l = l'.
Proof.
  intros Hf [a|] [a'|]; simpl; intros [=]; try done. f_equal. by eapply ren_action_inj.
Qed.

Lemma ren_lbl_swap01_SS l : ren_lbl swap01 (ren_lbl S (ren_lbl S l)) = ren_lbl S (ren_lbl S l).
Proof. rewrite !ren_lbl_comp. apply ren_lbl_ext_fun. intros i. apply swap01_SS. Qed.

Lemma ren_lbl_add_S n l : ren_lbl (Nat.add n) (ren_lbl S l) = ren_lbl (Nat.add (S n)) l.
Proof. rewrite ren_lbl_comp. apply ren_lbl_ext_fun. intros i. simpl. lia. Qed.

Lemma ren_lbl_add_0 l : ren_lbl (Nat.add 0) l = l.
Proof. destruct l as [[c v|c v| | |]|]; simpl; by rewrite ?ren_chan_add_0. Qed.

(* ** Renaming of the indices commutes with the transitions *)

Lemma prog_gstep_ren f g s l P' :
  g ⟶ᵍ{l}[s] P' → gren f g ⟶ᵍ{ren_lbl f l}[s] (ren f P').
Proof.
  induction 1 as [t P | t c v P | t E es qs P Hq | t M es qs n P Hq | t es qs P Hq | g1 g2 s l P' Hg IH | g1 g2 s l P' Hg IH]; simpl.
  - constructor.
  - rewrite (proj1 ren_subst). constructor.
  - by constructor.
  - rewrite (proj1 ren_subst). by constructor.
  - by constructor.
  - by apply pg_sumL.
  - by apply pg_sumR.
Qed.

Lemma prog_step_ren f P s l P' :
  P ⟶{l}[s] P' → ren f P ⟶{ren_lbl f l}[s] (ren f P').
Proof.
  intros Hs. revert f. induction Hs as [g s l P' Hg | t c e v He | e P Q s l P' He Hp IH | e P Q s l Q' He Hp IH | P Q s l P' Hp IH | P Q s l Q' Hp IH | P Q t t' c v P' Q' Hp1 IH1 Hp2 IH2 | P Q t t' c v P' Q' Hp1 IH1 Hp2 IH2 | P s l P' Hp IH | t P]; intros f; simpl in *.
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
  ∀ g s l' X, gren f g ⟶ᵍ{l'}[s] X →
  ∃ l P', l' = ren_lbl f l ∧ X = ren f P' ∧ g ⟶ᵍ{l}[s] P'.
Proof.
  intros Hf g s l' X Hs. remember (gren f g) as RG eqn:ER. revert g ER.
  induction Hs as [t P | t c v P | t E es qs P Hq | t M es qs n P Hq | t es qs P Hq | g1 g2 s l P' Hgs IH | g1 g2 s l P' Hgs IH]; intros g0 ER;
    destruct g0 as [es0| |𝜆0 P0|g1' g2']; simpl in ER; simplify_eq.
  all: try (destruct 𝜆0; simpl in *; simplify_eq).
  - exists τ, P0. split_and!; [done|done|constructor].
  - exists (c0 ? v), (P0 ⁅ v ⁆ᵥ).
    split_and!; [done|by rewrite (proj1 ren_subst)|constructor].
  - exists (E0 ⦅qs⦆), P0. split_and!; [done|done|by constructor].
  - exists (M0 ⦅qs⦆? n), (P0 ⁅ VNat n ⁆ᵥ).
    split_and!; [done|by rewrite (proj1 ren_subst)|by constructor].
  - exists (init ⦅qs⦆), P0. split_and!; [done|done|by constructor].
  - destruct (IH g1' eq_refl) as (l0 & P'0 & -> & -> & Hg). exists l0, P'0. split_and!; [done|done|by apply pg_sumL].
  - destruct (IH g2' eq_refl) as (l0 & P'0 & -> & -> & Hg). exists l0, P'0. split_and!; [done|done|by apply pg_sumR].
Qed.

Lemma prog_step_ren_inv f :
  (∀ i j, f i = f j → i = j) →
  ∀ P s l' X, ren f P ⟶{l'}[s] X →
  ∃ l P', l' = ren_lbl f l ∧ X = ren f P' ∧ P ⟶{l}[s] P'.
Proof.
  intros Hf P s l' X Hs. remember (ren f P) as RP eqn:ER. revert f Hf P ER.
  induction Hs as [g s l P' Hg | t c e v Hev | e P Q s l P' Hev Hst IH | e P Q s l Q' Hev Hst IH | P Q s l P' Hst IH | P Q s l Q' Hst IH | P Q t t' c v P' Q' Hst1 IH1 Hst2 IH2 | P Q t t' c v P' Q' Hst1 IH1 Hst2 IH2 | P s l P' Hst IH | t P]; intros f Hf P0 ER;
    destruct P0 as [t0 c0 e0|e0 P1 P2|P1 P2|P1|X0|t0 P1|g0]; simpl in ER; simplify_eq.
  - destruct (prog_gstep_ren_inv f Hf g0 _ _ _ Hg) as (l0 & P'0 & -> & -> & Hg0).
    exists l0, P'0. split_and!; [done|done|by apply pr_guard].
  - exists (c0 ! v), 𝟘. split_and!; [done|done|by constructor].
  - destruct (IH f Hf P1 eq_refl) as (l0 & P'0 & -> & -> & Hp).
    exists l0, P'0. split_and!; [done|done|by apply pr_iteT].
  - destruct (IH f Hf P2 eq_refl) as (l0 & P'0 & -> & -> & Hp).
    exists l0, P'0. split_and!; [done|done|by apply pr_iteF].
  - destruct (IH f Hf P1 eq_refl) as (l0 & P'0 & -> & -> & Hp).
    exists l0, (P'0 ∥ P2). split_and!; [done|done|by apply pr_parL].
  - destruct (IH f Hf P2 eq_refl) as (l0 & P'0 & -> & -> & Hp).
    exists l0, (P1 ∥ P'0). split_and!; [done|done|by apply pr_parR].
  - destruct (IH1 f Hf P1 eq_refl) as (l1 & P1' & E1 & -> & Hp1).
    destruct (IH2 f Hf P2 eq_refl) as (l2 & P2' & E2 & -> & Hp2).
    destruct l1 as [[c1 v1|c1 v1| | |]|]; simpl in E1; simplify_eq.
    destruct l2 as [[c2 v2|c2 v2| | |]|]; simpl in E2; simplify_eq.
    assert (c1 = c2) by (eapply ren_chan_inj; [exact Hf|congruence]). subst.
    exists τ, (P1' ∥ P2'). split_and!; [done|done|by eapply pr_syncL].
  - destruct (IH1 f Hf P1 eq_refl) as (l1 & P1' & E1 & -> & Hp1).
    destruct (IH2 f Hf P2 eq_refl) as (l2 & P2' & E2 & -> & Hp2).
    destruct l1 as [[c1 v1|c1 v1| | |]|]; simpl in E1; simplify_eq.
    destruct l2 as [[c2 v2|c2 v2| | |]|]; simpl in E2; simplify_eq.
    assert (c1 = c2) by (eapply ren_chan_inj; [exact Hf|congruence]). subst.
    exists τ, (P1' ∥ P2'). split_and!; [done|done|by eapply pr_syncR].
  - destruct (IH (lift f) (lift_inj f Hf) P1 eq_refl) as (l0 & P'0 & E0 & -> & Hp).
    destruct l0 as [[[c0|[|i]] v0|[c0|[|i]] v0|E' qs|M qs n|qs0]|]; simpl in E0;
      destruct l as [[[c1|i1] v1|[c1|i1] v1|E1 qs1|M1 qs1 n1|qs2]|]; simpl in E0; simplify_eq.
    + exists ((CName c0) ! v0), (ν P'0). split_and!; [done|done|by apply pr_res].
    + exists ((CIdx i) ! v0), (ν P'0). split_and!; [done|done|by apply pr_res].
    + exists ((CName c0) ? v0), (ν P'0). split_and!; [done|done|by apply pr_res].
    + exists ((CIdx i) ? v0), (ν P'0). split_and!; [done|done|by apply pr_res].
    + exists (E' ⦅qs⦆), (ν P'0). split_and!; [done|done|by apply pr_res].
    + exists (M ⦅qs⦆? n), (ν P'0). split_and!; [done|done|by apply pr_res].
    + exists (init ⦅qs0⦆), (ν P'0). split_and!; [done|done|by apply pr_res].
    + exists τ, (ν P'0). split_and!; [done|done|by apply pr_res].
  - exists τ, (P1 ⁅ (t0 ∶ rec ∙ P1)↑ ⁆ₚ).
    split_and!; [done| |constructor]. rewrite (proj1 ren_pr_subst), <- (proj1 tren_ren). done.
Qed.

End LqP.

(* end hide *)
