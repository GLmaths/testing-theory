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
From TestingTheory Require Import lqCCS.lqCCS_prog.Syntax.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

Section De_Brujin_Lemmas.
  Context `{lqP : lqCCS_Parameters}.

(* ** Facts on renamings *)

Lemma lift_ext f g : (∀ i, f i = g i) → ∀ i, lift f i = lift g i.
Proof. intros H [|i]; simpl; congruence. Qed.

Lemma lift_id i : lift id i = i.
Proof. by destruct i. Qed.

Lemma lift_comp f g i : lift f (lift g i) = lift (f ∘ g) i.
Proof. by destruct i. Qed.

Lemma lift_S f i : lift f (S i) = S (f i).
Proof. done. Qed.

Lemma lift_lift_swap01 f i : lift (lift f) (swap01 i) = swap01 (lift (lift f) i).
Proof. destruct i as [|[|i]]; done. Qed.

Lemma swap01_invol i : swap01 (swap01 i) = i.
Proof. destruct i as [|[|i]]; done. Qed.

Lemma swap01_SS i : swap01 (S (S i)) = S (S i).
Proof. done. Qed.

Lemma ren_chan_ext f g c : (∀ i, f i = g i) → ren_chan f c = ren_chan g c.
Proof. intros H. destruct c; simpl; congruence. Qed.

Lemma ren_chan_comp f g c : ren_chan f (ren_chan g c) = ren_chan (f ∘ g) c.
Proof. by destruct c. Qed.

Lemma ren_chan_id c : ren_chan id c = c.
Proof. by destruct c. Qed.

Lemma ren_chan_inj f : (∀ i j, f i = f j → i = j) → ∀ c c', ren_chan f c = ren_chan f c' → c = c'.
Proof. intros Hf [c|i] [c'|j]; simpl; intros [=]; subst; [done|]. f_equal. by apply Hf. Qed.

Lemma lift_inj f : (∀ i j, f i = f j → i = j) → ∀ i j, lift f i = lift f j → i = j.
Proof. intros Hf [|i] [|j]; simpl; intros [=]; subst; [done|]. f_equal. by apply Hf. Qed.

Lemma prefix_ren_ext f g π : (∀ i, f i = g i) → prefix_ren f π = prefix_ren g π.
Proof. intros H. destruct π; simpl; [done| |done|done|done]. by rewrite (ren_chan_ext f g). Qed.

Lemma ren_ext_all :
  (∀ P f g, (∀ i, f i = g i) → ren f P = ren g P)
  ∧ (∀ h f g, (∀ i, f i = g i) → gren f h = gren g h).
Proof.
  apply prog_guard_ind; simpl; intros; try (f_equal; auto; done).
  - by rewrite (ren_chan_ext f g).
  - f_equal. apply H. by apply lift_ext.
  - f_equal; [by apply prefix_ren_ext | by apply H].
Qed.

Lemma ren_ext f g P : (∀ i, f i = g i) → ren f P = ren g P.
Proof. apply (proj1 ren_ext_all). Qed.

Lemma prefix_ren_comp f g π : prefix_ren f (prefix_ren g π) = prefix_ren (f ∘ g) π.
Proof. destruct π; simpl; [done| |done|done|done]. by rewrite ren_chan_comp. Qed.

Lemma ren_comp_all :
  (∀ P f g, ren f (ren g P) = ren (f ∘ g) P) ∧ (∀ h f g, gren f (gren g h) = gren (f ∘ g) h).
Proof.
  apply prog_guard_ind; simpl; intros; try (f_equal; auto; done).
  - by rewrite ren_chan_comp.
  - f_equal. rewrite H. apply ren_ext, lift_comp.
  - f_equal; [apply prefix_ren_comp | apply H].
Qed.

Lemma ren_comp f g P : ren f (ren g P) = ren (f ∘ g) P.
Proof. apply (proj1 ren_comp_all). Qed.

Lemma ren_id_all : (∀ P, ren id P = P) ∧ (∀ h, gren id h = h).
Proof.
  apply prog_guard_ind; simpl; intros; try (f_equal; auto; done).
  - by rewrite ren_chan_id.
  - f_equal. rewrite <- H at 2. apply ren_ext, lift_id.
  - f_equal; [|done]. destruct π; simpl; [done| |done|done|done]. by rewrite ren_chan_id.
Qed.

Lemma ren_id P : ren id P = P.
Proof. apply (proj1 ren_id_all). Qed.

(* [ren (lift f) (ren S P) = ren S (ren f P)] *)
Lemma ren_lift_S f P : ren (lift f) (ren S P) = ren S (ren f P).
Proof. rewrite !ren_comp. by apply ren_ext. Qed.

Lemma ren_swap01_invol P : ren swap01 (ren swap01 P) = P.
Proof.
  rewrite ren_comp. rewrite <- (ren_id P) at 2. apply ren_ext. intros i. apply swap01_invol.
Qed.

Lemma prefix_ren_subst f i v π :
  prefix_ren f (prefix_subst i v π) = prefix_subst i v (prefix_ren f π).
Proof. by destruct π. Qed.

Lemma prefix_ren_shift f i π : prefix_ren f (prefix_shift i π) = prefix_shift i (prefix_ren f π).
Proof. by destruct π. Qed.

Lemma prefix_ren_binds f π : prefix_binds (prefix_ren f π) = prefix_binds π.
Proof. by destruct π. Qed.

Lemma ren_subst :
  (∀ P f i v, ren f (P ⁅ v // i ⁆ᵥ) = (ren f P) ⁅ v // i ⁆ᵥ)
  ∧ (∀ g f i v, gren f (gsubst i v g) = gsubst i v (gren f g)).
Proof.
  apply prog_guard_ind; simpl; intros; try congruence.
  rewrite prefix_ren_subst, prefix_ren_binds. congruence.
Qed.

Lemma ren_shiftv :
  (∀ P f i, ren f (shiftv i P) = shiftv i (ren f P))
  ∧ (∀ g f i, gren f (gshiftv i g) = gshiftv i (gren f g)).
Proof.
  apply prog_guard_ind; simpl; intros; try congruence.
  rewrite prefix_ren_shift, prefix_ren_binds. congruence.
Qed.

Lemma ren_shiftv_iter n f Q : ren f (Nat.iter n ⇧ᵥ Q) = Nat.iter n ⇧ᵥ (ren f Q).
Proof. induction n; simpl; [done|]. by rewrite (proj1 ren_shiftv), IHn. Qed.

Lemma ren_rshift :
  (∀ P f i, ren f (rshift i P) = rshift i (ren f P))
  ∧ (∀ g f i, gren f (grshift i g) = grshift i (gren f g)).
Proof. apply prog_guard_ind; simpl; intros; try congruence. by case_decide. Qed.

Lemma ren_pr_subst :
  (∀ P f i Q, ren f (P ⁅ Q // i ⁆ₚ) = (ren f P) ⁅ ren f Q // i ⁆ₚ)
  ∧ (∀ g f i Q, gren f (gpr_subst i g Q) = gpr_subst i (gren f g) (ren f Q)).
Proof.
  apply prog_guard_ind; simpl; intros; try congruence.
  - f_equal. rewrite H. f_equal. apply ren_lift_S.
  - by repeat case_decide.
  - by rewrite H, (proj1 ren_rshift).
  - rewrite H, prefix_ren_binds, ren_shiftv_iter. done.
Qed.

Lemma size_ren : (∀ P f, size (ren f P) = size P) ∧ (∀ g f, gsize (gren f g) = gsize g).
Proof. apply prog_guard_ind; simpl; intros; congruence. Qed.

(* ** Tag renaming and indices *)

Lemma prefix_tren_binds f π : prefix_binds (prefix_tren f π) = prefix_binds π.
Proof. by destruct π. Qed.

Lemma prefix_tren_subst f i v π :
  prefix_tren f (prefix_subst i v π) = prefix_subst i v (prefix_tren f π).
Proof. by destruct π. Qed.

Lemma prefix_tren_shift f i π : prefix_tren f (prefix_shift i π) = prefix_shift i (prefix_tren f π).
Proof. by destruct π. Qed.

Lemma prefix_tren_ren f g π : prefix_tren f (prefix_ren g π) = prefix_ren g (prefix_tren f π).
Proof. by destruct π. Qed.

Lemma tren_subst :
  (∀ P f i v, tren f (P ⁅ v // i ⁆ᵥ) = (tren f P) ⁅ v // i ⁆ᵥ)
  ∧ (∀ g f i v, gtren f (gsubst i v g) = gsubst i v (gtren f g)).
Proof.
  apply prog_guard_ind; simpl; intros; try congruence.
  rewrite prefix_tren_subst, prefix_tren_binds. congruence.
Qed.

Lemma tren_shiftv :
  (∀ P f i, tren f (shiftv i P) = shiftv i (tren f P))
  ∧ (∀ g f i, gtren f (gshiftv i g) = gshiftv i (gtren f g)).
Proof.
  apply prog_guard_ind; simpl; intros; try congruence.
  rewrite prefix_tren_shift, prefix_tren_binds. congruence.
Qed.

Lemma tren_shiftv_iter n f Q : tren f (Nat.iter n ⇧ᵥ Q) = Nat.iter n ⇧ᵥ (tren f Q).
Proof. induction n; simpl; [done|]. by rewrite (proj1 tren_shiftv), IHn. Qed.

Lemma tren_ren :
  (∀ P f h, tren f (ren h P) = ren h (tren f P))
  ∧ (∀ g f h, gtren f (gren h g) = gren h (gtren f g)).
Proof.
  apply prog_guard_ind; simpl; intros; try congruence.
  rewrite prefix_tren_ren. congruence.
Qed.

Lemma tren_rshift :
  (∀ P f i, tren f (rshift i P) = rshift i (tren f P))
  ∧ (∀ g f i, gtren f (grshift i g) = grshift i (gtren f g)).
Proof. apply prog_guard_ind; simpl; intros; try congruence. by case_decide. Qed.

Lemma tren_pr_subst :
  (∀ P f i Q, tren f (P ⁅ Q // i ⁆ₚ) = (tren f P) ⁅ tren f Q // i ⁆ₚ)
  ∧ (∀ g f i Q, gtren f (gpr_subst i g Q) = gpr_subst i (gtren f g) (tren f Q)).
Proof.
  apply prog_guard_ind; simpl; intros; try congruence.
  - f_equal. rewrite H. f_equal. apply (proj1 tren_ren).
  - by repeat case_decide.
  - by rewrite H, (proj1 tren_rshift).
  - rewrite H, prefix_tren_binds, tren_shiftv_iter. done.
Qed.

(* ** Renamings of indices *)

Lemma ren_swap01_SS P : ren swap01 (ren S (ren S P)) = ren S (ren S P).
Proof. rewrite !ren_comp. apply ren_ext. intros i. apply swap01_SS. Qed.

Lemma ren_lift_lift_swap01 f P :
  ren (lift (lift f)) (ren swap01 P) = ren swap01 (ren (lift (lift f)) P).
Proof. rewrite !ren_comp. apply ren_ext. intros i. apply lift_lift_swap01. Qed.

(* ** Substitution and shift of values *)

Lemma exp_subst_closed i v e w : 〚 e 〛 = w → exp_subst i v e = e.
Proof.
  revert w. induction e; intros w He; simpl in He |- *; try done.
  all: repeat (destruct (eval _) as [[]|] eqn:? in He; try discriminate);
    repeat match goal with
    | IH : ∀ v, 〚 ?e 〛 = v → _, H : 〚 ?e 〛 = _ |- _ => rewrite (IH _ H); clear IH
    end; done.
Qed.

Lemma exp_shift_closed i e w : 〚 e 〛 = w → exp_shift i e = e.
Proof.
  revert w. induction e; intros w He; simpl in He |- *; try done.
  all: repeat (destruct (eval _) as [[]|] eqn:? in He; try discriminate);
    repeat match goal with
    | IH : ∀ v, 〚 ?e 〛 = v → _, H : 〚 ?e 〛 = _ |- _ => rewrite (IH _ H); clear IH
    end; done.
Qed.

Lemma exp_subst_shift j v e : exp_subst j v (exp_shift j e) = e.
Proof.
  induction e as [i|w|e IH|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2]; simpl; try congruence.
  case_decide as Hk; simpl.
  - case_decide as Ha; [lia|]. case_decide as Hb; [lia|done].
  - case_decide as Ha; [lia|]. case_decide as Hb; [done|lia].
Qed.

Lemma exps_subst_shift i v (es : list exp) : map (exp_subst i v) (map (exp_shift i) es) = es.
Proof. induction es as [|e es IH]; [done|]. simpl. by rewrite exp_subst_shift, IH. Qed.

Lemma prefix_subst_shift i v π : prefix_subst i v (prefix_shift i π) = π.
Proof. destruct π; simpl; by rewrite ?exps_subst_shift, ?exp_subst_shift. Qed.

Lemma prefix_binds_shift i π : prefix_binds (prefix_shift i π) = prefix_binds π.
Proof. by destruct π. Qed.

Lemma subst_shiftv i v P : (shiftv i P) ⁅ v // i ⁆ᵥ = P
with gsubst_gshiftv i v g : gsubst i v (gshiftv i g) = g.
Proof.
  - destruct P; simpl; rewrite ?exp_subst_shift, ?subst_shiftv, ?gsubst_gshiftv; done.
  - destruct g; simpl; rewrite ?exps_subst_shift, ?prefix_subst_shift, ?prefix_binds_shift,
      ?subst_shiftv, ?gsubst_gshiftv; done.
Qed.

(* ** Iterated restrictions and lifts *)

Lemma liftn_add n : ∀ f i, liftn n f (n + i) = n + f i.
Proof.
  induction n; intros f i; simpl; [done|].
  replace (S (n + i)) with (n + S i) by lia. rewrite IHn. simpl. lia.
Qed.

Lemma ren_chan_add_0 c : ren_chan (Nat.add 0) c = c.
Proof. by destruct c. Qed.

Lemma ren_chan_add_S n c : ren_chan (Nat.add n) (ren_chan S c) = ren_chan (Nat.add (S n)) c.
Proof. rewrite ren_chan_comp. apply ren_chan_ext. intros i. simpl. lia. Qed.

Lemma ren_chan_liftn f m c :
  ren_chan (liftn m f) (ren_chan (Nat.add m) c) = ren_chan (Nat.add m) (ren_chan f c).
Proof. rewrite !ren_chan_comp. apply ren_chan_ext. intros i. simpl. by rewrite liftn_add. Qed.

Lemma ren_add_S n P : ren (Nat.add n) (ren S P) = ren (Nat.add (S n)) P.
Proof. rewrite ren_comp. apply ren_ext. intros i. simpl. lia. Qed.

Lemma ren_resn f n P : ren f (Ѵ n P) = Ѵ n (ren (liftn n f) P).
Proof. revert f. induction n; intros f; simpl; [done|]. by rewrite IHn. Qed.

End De_Brujin_Lemmas.