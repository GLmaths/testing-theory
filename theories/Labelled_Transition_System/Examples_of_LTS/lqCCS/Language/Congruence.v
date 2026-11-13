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
(* * lqCCS: structural congruence

    The structural congruence of lqCCS (Ceragioli et al., POPL 2024,
    Figure 2), on the syntax with recursion, in the style of VACCS
    ([VACCS.Language.Congruence]): restricted channels are De Bruijn indices,
    so scope extrusion [(ν P) ∥ Q ≡ ν (P ∥ Q⁺)] has no side condition and
    the order of two restrictions is exchanged by a swap of indices.  Tags
    are kept: congruent processes have the same tags.  The congruence is
    closed under all contexts, recursion included.

    [≡*] is a bisimulation on the program LTS, with the same choices
    ([cgr_bisim]). *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list sets relations.
From TestingTheory Require Import ActTau.
From TestingTheory Require Import lqCCS.Language.Algebra lqCCS.Language.Quantum.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.LTS.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

(* ** One step of congruence *)

Inductive cgr_step : proc → proc → Prop :=
| cgr_par_nil_step P : cgr_step (P ∥ 𝟘) P
| cgr_par_com_step P Q : cgr_step (P ∥ Q) (Q ∥ P)
| cgr_par_assoc_rev_step P Q R : cgr_step (P ∥ (Q ∥ R)) ((P ∥ Q) ∥ R)
| cgr_if_true_step e P Q : eval e = Some (VBool true) → cgr_step (If e Then P Else Q) P
| cgr_if_false_step e P Q : eval e = Some (VBool false) → cgr_step (If e Then P Else Q) Q
| cgr_send_val_step t c e v : eval e = Some v → cgr_step (t ∶ c ! e) (t ∶ c ! (EVal v))
| cgr_if_val_step e v P Q : eval e = Some v → cgr_step (If e Then P Else Q) (If (EVal v) Then P Else Q)
| cgr_res_nil_step es : cgr_step (ν (GNil es)) ((GNil es))
| cgr_res_swap_step P : cgr_step (ν ν P) (ν ν (ren swap01 P))
| cgr_res_scope_rev_step P Q : cgr_step ((ν P) ∥ Q) (ν (P ∥ ren S Q))
(* contexts *)
| cgr_if_then_step e P P' Q : cgr_step P P' → cgr_step (If e Then P Else Q) (If e Then P' Else Q)
| cgr_if_else_step e P Q Q' : cgr_step Q Q' → cgr_step (If e Then P Else Q) (If e Then P Else Q')
| cgr_par_step P P' Q : cgr_step P P' → cgr_step (P ∥ Q) (P' ∥ Q)
| cgr_par_right_step P Q Q' : cgr_step Q Q' → cgr_step (P ∥ Q) (P ∥ Q')
| cgr_res_step P P' : cgr_step P P' → cgr_step (ν P) (ν P')
| cgr_recursion_step t X P P' : cgr_step P P' → cgr_step (t ∶ rec X ∙ P) (t ∶ rec X ∙ P')
| cgr_guard_step g g' : gcgr_step g g' → cgr_step g g'
with gcgr_step : guard → guard → Prop :=
| cgr_choice_nil_step g es : gcgr_step (g + GNil es) g
| cgr_choice_com_step g h : gcgr_step (g + h) (h + g)
| cgr_choice_assoc_rev_step g h k : gcgr_step (g + (h + k)) ((g + h) + k)
| cgr_nil_val_step es1 e v es2 :
    eval e = Some v → gcgr_step (GNil (es1 ++ e :: es2)) (GNil (es1 ++ EVal v :: es2))
| cgr_op_val_step t E es1 e v es2 P :
    eval e = Some v → gcgr_step (t ∶ E ⦅es1 ++ e :: es2⦆ ∙ P) (t ∶ E ⦅es1 ++ EVal v :: es2⦆ ∙ P)
| cgr_meas_val_step t M es1 e v es2 P :
    eval e = Some v → gcgr_step (t ∶ M ⦅es1 ++ e :: es2 ▷⦆ ∙ P) (t ∶ M ⦅es1 ++ EVal v :: es2 ▷⦆ ∙ P)
| cgr_init_val_step t es1 e v es2 P :
    eval e = Some v → gcgr_step (t ∶ init ⦅es1 ++ e :: es2⦆ ∙ P) (t ∶ init ⦅es1 ++ EVal v :: es2⦆ ∙ P)
(* contexts *)
| cgr_prefix_step 𝜆 P P' : cgr_step P P' → gcgr_step (𝜆 ∙ P) (𝜆 ∙ P')
| cgr_choice_step g g' h : gcgr_step g g' → gcgr_step (g + h) (g' + h)
| cgr_choice_right_step g h h' : gcgr_step h h' → gcgr_step (g + h) (g + h').

Scheme cgr_step_mut_ind := Induction for cgr_step Sort Prop
  with gcgr_step_mut_ind := Induction for gcgr_step Sort Prop.
Combined Scheme cgr_gcgr_step_ind from cgr_step_mut_ind, gcgr_step_mut_ind.

(* ** The congruence *)

Definition cgr : relation proc := rtsc cgr_step.
Definition gcgr : relation guard := rtsc gcgr_step.
Arguments cgr (_ _)%_lq.
Arguments gcgr (_ _)%_lq.

Notation "P ≡* Q" := (cgr P Q) (at level 70) : lqccs_scope.
Notation "g ≡ᵍ* h" := (gcgr g h) (at level 70) : lqccs_scope.

#[global] Instance cgr_equivalence : Equivalence cgr.
Proof. apply rtsc_equivalence. Qed.

#[global] Instance gcgr_equivalence : Equivalence gcgr.
Proof. apply rtsc_equivalence. Qed.

(* ** Evaluation *)

Lemma eval_qubits_val es1 e v es2 :
  eval e = Some v → eval_qubits (es1 ++ e :: es2) = eval_qubits (es1 ++ EVal v :: es2).
Proof.
  intros He. assert (E : eval_qubit e = eval_qubit (EVal v))
    by (unfold eval_qubit; simpl; by rewrite He).
  unfold eval_qubits. induction es1 as [|e1 es1 IH]; simpl; [by rewrite E|by rewrite IH].
Qed.

(* ** One step is a congruence *)

Lemma cgr_of_step P Q : cgr_step P Q → P ≡* Q.
Proof. apply rtsc_lr. Qed.

Lemma gcgr_of_step g h : gcgr_step g h → g ≡ᵍ* h.
Proof. apply rtsc_lr. Qed.

(* ** The rules, as congruences *)

Lemma cgr_par_nil P : P ∥ 𝟘 ≡* P.
Proof. apply cgr_of_step, cgr_par_nil_step. Qed.

Lemma cgr_par_nil_rev P : P ≡* P ∥ 𝟘.
Proof. apply rtsc_rl, cgr_par_nil_step. Qed.

Lemma cgr_par_com P Q : P ∥ Q ≡* Q ∥ P.
Proof. apply cgr_of_step, cgr_par_com_step. Qed.

Lemma cgr_par_assoc P Q R : (P ∥ Q) ∥ R ≡* P ∥ (Q ∥ R).
Proof. apply rtsc_rl, cgr_par_assoc_rev_step. Qed.

Lemma cgr_par_assoc_rev P Q R : P ∥ (Q ∥ R) ≡* (P ∥ Q) ∥ R.
Proof. apply cgr_of_step, cgr_par_assoc_rev_step. Qed.

Lemma cgr_if_true e P Q : eval e = Some (VBool true) → If e Then P Else Q ≡* P.
Proof. intros. by apply cgr_of_step, cgr_if_true_step. Qed.

Lemma cgr_if_true_rev e P Q : eval e = Some (VBool true) → P ≡* If e Then P Else Q.
Proof. intros. by apply rtsc_rl, cgr_if_true_step. Qed.

Lemma cgr_if_false e P Q : eval e = Some (VBool false) → If e Then P Else Q ≡* Q.
Proof. intros. by apply cgr_of_step, cgr_if_false_step. Qed.

Lemma cgr_if_false_rev e P Q : eval e = Some (VBool false) → Q ≡* If e Then P Else Q.
Proof. intros. by apply rtsc_rl, cgr_if_false_step. Qed.

Lemma cgr_res_nil es : (ν (GNil es)) ≡* (GNil es).
Proof. apply cgr_of_step, cgr_res_nil_step. Qed.

Lemma cgr_res_nil_rev es : (GNil es) ≡* (ν (GNil es)).
Proof. apply rtsc_rl, cgr_res_nil_step. Qed.

Lemma cgr_res_swap P : (ν ν P) ≡* (ν ν (ren swap01 P)).
Proof. apply cgr_of_step, cgr_res_swap_step. Qed.

Lemma cgr_res_swap_rev P : (ν ν (ren swap01 P)) ≡* (ν ν P).
Proof. apply rtsc_rl, cgr_res_swap_step. Qed.

Lemma cgr_res_scope P Q : (ν (P ∥ ren S Q)) ≡* (ν P) ∥ Q.
Proof. apply rtsc_rl, cgr_res_scope_rev_step. Qed.

Lemma cgr_res_scope_rev P Q : (ν P) ∥ Q ≡* (ν (P ∥ ren S Q)).
Proof. apply cgr_of_step, cgr_res_scope_rev_step. Qed.

Lemma gcgr_choice_nil g es : (g + GNil es) ≡ᵍ* g.
Proof. apply gcgr_of_step, cgr_choice_nil_step. Qed.

Lemma gcgr_choice_nil_rev g es : g ≡ᵍ* (g + GNil es).
Proof. apply rtsc_rl, cgr_choice_nil_step. Qed.

Lemma gcgr_choice_com g h : (g + h) ≡ᵍ* (h + g).
Proof. apply gcgr_of_step, cgr_choice_com_step. Qed.

Lemma gcgr_choice_assoc g h k : ((g + h) + k) ≡ᵍ* (g + (h + k)).
Proof. apply rtsc_rl, cgr_choice_assoc_rev_step. Qed.

Lemma gcgr_choice_assoc_rev g h k : (g + (h + k)) ≡ᵍ* ((g + h) + k).
Proof. apply gcgr_of_step, cgr_choice_assoc_rev_step. Qed.

(* ** Congruence under contexts *)

Lemma cgr_ctx (f : proc → proc) :
  (∀ P Q, cgr_step P Q → cgr_step (f P) (f Q)) → ∀ P Q, P ≡* Q → f P ≡* f Q.
Proof.
  intros Hf P Q. induction 1 as [P|P Q R [HPQ|HQP] _ IH]; [done| |].
  - etrans; [|exact IH]. apply rtsc_lr. by apply Hf.
  - etrans; [|exact IH]. apply rtsc_rl. by apply Hf.
Qed.

Lemma gcgr_ctx (f : guard → guard) :
  (∀ g h, gcgr_step g h → gcgr_step (f g) (f h)) → ∀ g h, g ≡ᵍ* h → (f g) ≡ᵍ* (f h).
Proof.
  intros Hf g h. induction 1 as [g|g h k [Hgh|Hhg] _ IH]; [done| |].
  - etrans; [|exact IH]. apply rtsc_lr. by apply Hf.
  - etrans; [|exact IH]. apply rtsc_rl. by apply Hf.
Qed.

Lemma cgr_par P P' Q : P ≡* P' → P ∥ Q ≡* P' ∥ Q.
Proof. apply (cgr_ctx (λ P, P ∥ Q)). intros. by constructor. Qed.

Lemma cgr_par_r P Q Q' : Q ≡* Q' → P ∥ Q ≡* P ∥ Q'.
Proof. apply (cgr_ctx (λ Q, P ∥ Q)). intros. by constructor. Qed.

Lemma cgr_res P P' : P ≡* P' → ν P ≡* ν P'.
Proof. apply (cgr_ctx (λ P, ν P)). intros. by constructor. Qed.

Lemma cgr_recursion t X P P' : P ≡* P' → t ∶ rec X ∙ P ≡* t ∶ rec X ∙ P'.
Proof. apply (cgr_ctx (λ P, t ∶ rec X ∙ P)). intros. by constructor. Qed.

Lemma cgr_if_then e P P' Q : P ≡* P' → If e Then P Else Q ≡* If e Then P' Else Q.
Proof. apply (cgr_ctx (λ P, If e Then P Else Q)). intros. by constructor. Qed.

Lemma cgr_if_else e P Q Q' : Q ≡* Q' → If e Then P Else Q ≡* If e Then P Else Q'.
Proof. apply (cgr_ctx (λ Q, If e Then P Else Q)). intros. by constructor. Qed.

Lemma cgr_fullpar P P' Q Q' : P ≡* P' → Q ≡* Q' → P ∥ Q ≡* P' ∥ Q'.
Proof. intros. etrans; [by apply cgr_par|by apply cgr_par_r]. Qed.

Lemma cgr_full_if e P P' Q Q' : P ≡* P' → Q ≡* Q' → If e Then P Else Q ≡* If e Then P' Else Q'.
Proof. intros. etrans; [by apply cgr_if_then|by apply cgr_if_else]. Qed.

Lemma cgr_guard g h : g ≡ᵍ* h → g ≡* h.
Proof.
  induction 1 as [g|g h k [Hgh|Hhg] _ IH]; [done| |].
  - etrans; [|exact IH]. apply rtsc_lr. by constructor.
  - etrans; [|exact IH]. apply rtsc_rl. by constructor.
Qed.

Lemma gcgr_prefix 𝜆 P P' : P ≡* P' → (𝜆 ∙ P) ≡ᵍ* (𝜆 ∙ P').
Proof.
  induction 1 as [P|P Q R [HPQ|HQP] _ IH]; [done| |].
  - etrans; [|exact IH]. apply rtsc_lr. by constructor.
  - etrans; [|exact IH]. apply rtsc_rl. by constructor.
Qed.

Lemma gcgr_choice g g' h : g ≡ᵍ* g' → (g + h) ≡ᵍ* (g' + h).
Proof. apply (gcgr_ctx (λ g, (g + h)%lq)). intros. by constructor. Qed.

Lemma gcgr_choice_r g h h' : h ≡ᵍ* h' → (g + h) ≡ᵍ* (g + h').
Proof. apply (gcgr_ctx (λ h, (g + h)%lq)). intros. by constructor. Qed.

Lemma gcgr_fullchoice g g' h h' : g ≡ᵍ* g' → h ≡ᵍ* h' → (g + h) ≡ᵍ* (g' + h').
Proof. intros. etrans; [by apply gcgr_choice|by apply gcgr_choice_r]. Qed.

(* [(P ∥ Q) ∥ R ≡ (P ∥ R) ∥ Q] *)
Lemma cgr_par_swap P Q R : (P ∥ Q) ∥ R ≡* (P ∥ R) ∥ Q.
Proof.
  etrans; [apply cgr_par_assoc|].
  etrans; [apply cgr_par_r, cgr_par_com|].
  apply cgr_par_assoc_rev.
Qed.

(* [(P ∥ Q) ∥ (R ∥ S) ≡ (P ∥ R) ∥ (Q ∥ S)] *)
Lemma cgr_par_inversion P Q R S : (P ∥ Q) ∥ (R ∥ S) ≡* (P ∥ R) ∥ (Q ∥ S).
Proof.
  etrans; [apply cgr_par_assoc_rev|].
  etrans; [apply cgr_par, cgr_par_swap|].
  apply cgr_par_assoc.
Qed.

(* ** Renamings of indices *)

Lemma ren_swap01_SS P : ren swap01 (ren S (ren S P)) = ren S (ren S P).
Proof. rewrite !ren_comp. apply ren_ext. intros i. apply swap01_SS. Qed.

Lemma ren_lift_lift_swap01 f P :
  ren (lift (lift f)) (ren swap01 P) = ren swap01 (ren (lift (lift f)) P).
Proof. rewrite !ren_comp. apply ren_ext. intros i. apply lift_lift_swap01. Qed.

Lemma cgr_step_ren :
  (∀ P Q, cgr_step P Q → ∀ f, cgr_step (ren f P) (ren f Q))
  ∧ (∀ g h, gcgr_step g h → ∀ f, gcgr_step (gren f g) (gren f h)).
Proof.
  apply cgr_gcgr_step_ind; simpl; intros; try (constructor; done); try (by constructor; apply H).
  - rewrite ren_lift_lift_swap01. apply cgr_res_swap_step.
  - rewrite ren_lift_S. apply cgr_res_scope_rev_step.
Qed.

Lemma cgr_ren f P Q : P ≡* Q → ren f P ≡* ren f Q.
Proof. apply (cgr_ctx (ren f)). intros. by apply cgr_step_ren. Qed.

(* ** Substitution and shift of values *)

Lemma exp_subst_closed k v e w : eval e = Some w → exp_subst k v e = e.
Proof.
  revert w. induction e; intros w He; simpl in He |- *; try done.
  all: repeat (destruct (eval _) as [[]|] eqn:? in He; try discriminate);
    repeat match goal with
    | IH : ∀ v, eval ?e = Some v → _, H : eval ?e = Some _ |- _ => rewrite (IH _ H); clear IH
    end; done.
Qed.

Lemma exp_shift_closed k e w : eval e = Some w → exp_shift k e = e.
Proof.
  revert w. induction e; intros w He; simpl in He |- *; try done.
  all: repeat (destruct (eval _) as [[]|] eqn:? in He; try discriminate);
    repeat match goal with
    | IH : ∀ v, eval ?e = Some v → _, H : eval ?e = Some _ |- _ => rewrite (IH _ H); clear IH
    end; done.
Qed.

Lemma cgr_step_subst :
  (∀ P Q, cgr_step P Q → ∀ k v, cgr_step (subst k v P) (subst k v Q))
  ∧ (∀ g h, gcgr_step g h → ∀ k v, gcgr_step (gsubst k v g) (gsubst k v h)).
Proof.
  apply cgr_gcgr_step_ind; simpl; intros; try (constructor; done); try (by constructor; apply H).
  all: try (rewrite <- (proj1 ren_subst); by constructor).
  all: rewrite ?map_app; simpl;
    match goal with Hx : eval ?e = Some _ |- _ => rewrite (exp_subst_closed _ _ e _ Hx) end;
    by constructor.
Qed.

Lemma cgr_subst k v P Q : P ≡* Q → subst k v P ≡* subst k v Q.
Proof. apply (cgr_ctx (subst k v)). intros. by apply cgr_step_subst. Qed.

Lemma cgr_step_shiftv :
  (∀ P Q, cgr_step P Q → ∀ k, cgr_step (shiftv k P) (shiftv k Q))
  ∧ (∀ g h, gcgr_step g h → ∀ k, gcgr_step (gshiftv k g) (gshiftv k h)).
Proof.
  apply cgr_gcgr_step_ind; simpl; intros; try (constructor; done); try (by constructor; apply H).
  all: try (rewrite <- (proj1 ren_shiftv); by constructor).
  all: rewrite ?map_app; simpl;
    match goal with Hx : eval ?e = Some _ |- _ => rewrite (exp_shift_closed _ e _ Hx) end;
    by constructor.
Qed.

Lemma cgr_shiftv k P Q : P ≡* Q → shiftv k P ≡* shiftv k Q.
Proof. apply (cgr_ctx (shiftv k)). intros. by apply cgr_step_shiftv. Qed.

Lemma cgr_shiftv_iter n P Q : P ≡* Q → Nat.iter n (shiftv 0) P ≡* Nat.iter n (shiftv 0) Q.
Proof. induction n; simpl; [done|]. intros. by apply cgr_shiftv, IHn. Qed.

(* ** Substitution of processes *)

Lemma cgr_step_pr_subst_l :
  (∀ P P', cgr_step P P' → ∀ X Q, cgr_step (P ⦃ Q // X ⦄) (P' ⦃ Q // X ⦄))
  ∧ (∀ g g', gcgr_step g g' → ∀ X Q, gcgr_step (gpr_subst X g Q) (gpr_subst X g' Q)).
Proof.
  apply cgr_gcgr_step_ind; simpl; intros; try (constructor; done); try (by constructor; apply H).
  - replace ((ren swap01 P) ⦃ ren S (ren S Q) // X ⦄) with (ren swap01 (P ⦃ ren S (ren S Q) // X ⦄)).
    + apply cgr_res_swap_step.
    + rewrite (proj1 (ren_pr_subst X)). by rewrite ren_swap01_SS.
  - rewrite <- (proj1 (ren_pr_subst X)). apply cgr_res_scope_rev_step.
  - case_decide; [by apply cgr_recursion_step|]. by constructor; apply H.
Qed.

Lemma cgr_pr_subst_l P P' X Q : P ≡* P' → P ⦃ Q // X ⦄ ≡* P' ⦃ Q // X ⦄.
Proof. apply (cgr_ctx (λ P, P ⦃ Q // X ⦄)). intros. by apply cgr_step_pr_subst_l. Qed.

Lemma cgr_pr_subst_r :
  (∀ P X Q Q', Q ≡* Q' → P ⦃ Q // X ⦄ ≡* P ⦃ Q' // X ⦄)
  ∧ (∀ g X Q Q', Q ≡* Q' → (gpr_subst X g Q) ≡ᵍ* (gpr_subst X g Q')).
Proof.
  apply proc_guard_ind; simpl; intros; try done.
  - apply cgr_full_if; auto.
  - apply cgr_fullpar; auto.
  - apply cgr_res, H. by apply cgr_ren.
  - by case_decide.
  - case_decide; [done|]. apply cgr_recursion. by apply H.
  - apply cgr_guard. by apply H.
  - apply gcgr_prefix, H. by apply cgr_shiftv_iter.
  - apply gcgr_fullchoice; auto.
Qed.

(* Unfolding congruent recursions gives congruent processes. *)
Lemma cgr_unfold t X P P' :
  P ≡* P' → P ⦃ t ∶ rec X ∙ P // X ⦄ ≡* P' ⦃ t ∶ rec X ∙ P' // X ⦄.
Proof.
  intros H. etrans; [by apply cgr_pr_subst_l|].
  apply (proj1 cgr_pr_subst_r). by apply cgr_recursion.
Qed.

(* ** Facts on steps *)

Lemma pstep_nil es s l P' : ¬ (GNil es) ⟶{l}[s] P'.
Proof. by inversion 1. Qed.

Lemma S_inj_fun : ∀ i j : nat, S i = S j → i = j.
Proof. intros i j [=]. done. Qed.

(* ** Structural congruence is a bisimulation *)

Definition fwd (P Q : proc) : Prop :=
  ∀ s l P', P ⟶{l}[s] P' → ∃ Q', Q ⟶{l}[s] Q' ∧ P' ≡* Q'.

Lemma fwd_refl_step P Q : (∀ s l P', P ⟶{l}[s] P' → Q ⟶{l}[s] P') → fwd P Q.
Proof. intros H s l P' Hs. exists P'. split; [by apply H|done]. Qed.

Lemma fwd_par_nil P : fwd (P ∥ 𝟘) P ∧ fwd P (P ∥ 𝟘).
Proof.
  split.
  - intros s l X Hs. inversion Hs as [| | | | | | | | | |? ? ? ? P' HP| | | | |]; subst;
      try (exfalso; by eapply pstep_nil).
    exists P'. split; [done|]. apply cgr_par_nil.
  - intros s l P' Hs. exists (P' ∥ 𝟘). split; [by apply pr_parL|].
    symmetry. apply cgr_par_nil.
Qed.

Lemma fwd_par_comm P Q : fwd (P ∥ Q) (Q ∥ P).
Proof.
  intros s l X Hs.
  inversion Hs as [| | | | | | | | | |? ? ? ? P' HP|? ? ? ? Q' HQ|? ? t t' c v P' Q' HP HQ|? ? t t' c v P' Q' HP HQ| |];
    subst.
  - exists (Q ∥ P'). split; [by apply pr_parR|]. apply cgr_par_com.
  - exists (Q' ∥ P). split; [by apply pr_parL|]. apply cgr_par_com.
  - exists (Q' ∥ P'). split; [rewrite cpair_comm; by eapply pr_syncR|]. apply cgr_par_com.
  - exists (Q' ∥ P'). split; [rewrite cpair_comm; by eapply pr_syncL|]. apply cgr_par_com.
Qed.

Lemma fwd_par_assoc P Q R :
  fwd (P ∥ (Q ∥ R)) ((P ∥ Q) ∥ R) ∧ fwd ((P ∥ Q) ∥ R) (P ∥ (Q ∥ R)).
Proof.
  split.
  - intros s l X Hs.
    inversion Hs as [| | | | | | | | | |? ? ? ? P' HP|? ? ? ? X' HX|? ? t t' c v P' X' HP HX|? ? t t' c v P' X' HP HX| |];
      subst.
    + exists ((P' ∥ Q) ∥ R). split; [by do 2 apply pr_parL|]. apply cgr_par_assoc_rev.
    + inversion HX as [| | | | | | | | | |? ? ? ? Q' HQ|? ? ? ? R' HR|? ? t t' c v Q' R' HQ HR|? ? t t' c v Q' R' HQ HR| |];
        subst.
      * exists ((P ∥ Q') ∥ R). split; [by apply pr_parL, pr_parR|]. apply cgr_par_assoc_rev.
      * exists ((P ∥ Q) ∥ R'). split; [by apply pr_parR|]. apply cgr_par_assoc_rev.
      * exists ((P ∥ Q') ∥ R'). split; [eapply pr_syncL; [by apply pr_parR|done]|].
        apply cgr_par_assoc_rev.
      * exists ((P ∥ Q') ∥ R'). split; [eapply pr_syncR; [by apply pr_parR|done]|].
        apply cgr_par_assoc_rev.
    + inversion HX as [| | | | | | | | | |? ? ? ? Q' HQ|? ? ? ? R' HR| | | |]; subst.
      * exists ((P' ∥ Q') ∥ R). split; [apply pr_parL; by eapply pr_syncL|]. apply cgr_par_assoc_rev.
      * exists ((P' ∥ Q) ∥ R'). split; [eapply pr_syncL; [by apply pr_parL|done]|].
        apply cgr_par_assoc_rev.
    + inversion HX as [| | | | | | | | | |? ? ? ? Q' HQ|? ? ? ? R' HR| | | |]; subst.
      * exists ((P' ∥ Q') ∥ R). split; [apply pr_parL; by eapply pr_syncR|]. apply cgr_par_assoc_rev.
      * exists ((P' ∥ Q) ∥ R'). split; [eapply pr_syncR; [by apply pr_parL|done]|].
        apply cgr_par_assoc_rev.
  - intros s l X Hs.
    inversion Hs as [| | | | | | | | | |? ? ? ? X' HX|? ? ? ? R' HR|? ? t t' c v X' R' HX HR|? ? t t' c v X' R' HX HR| |];
      subst.
    + inversion HX as [| | | | | | | | | |? ? ? ? P' HP|? ? ? ? Q' HQ|? ? t t' c v P' Q' HP HQ|? ? t t' c v P' Q' HP HQ| |];
        subst.
      * exists (P' ∥ (Q ∥ R)). split; [by apply pr_parL|]. symmetry. apply cgr_par_assoc_rev.
      * exists (P ∥ (Q' ∥ R)). split; [by apply pr_parR, pr_parL|]. symmetry. apply cgr_par_assoc_rev.
      * exists (P' ∥ (Q' ∥ R)). split; [eapply pr_syncL; [done|by apply pr_parL]|].
        symmetry. apply cgr_par_assoc_rev.
      * exists (P' ∥ (Q' ∥ R)). split; [eapply pr_syncR; [done|by apply pr_parL]|].
        symmetry. apply cgr_par_assoc_rev.
    + exists (P ∥ (Q ∥ R')). split; [by do 2 apply pr_parR|]. symmetry. apply cgr_par_assoc_rev.
    + inversion HX as [| | | | | | | | | |? ? ? ? P' HP|? ? ? ? Q' HQ| | | |]; subst.
      * exists (P' ∥ (Q ∥ R')). split; [eapply pr_syncL; [done|by apply pr_parR]|].
        symmetry. apply cgr_par_assoc_rev.
      * exists (P ∥ (Q' ∥ R')). split; [apply pr_parR; by eapply pr_syncL|].
        symmetry. apply cgr_par_assoc_rev.
    + inversion HX as [| | | | | | | | | |? ? ? ? P' HP|? ? ? ? Q' HQ| | | |]; subst.
      * exists (P' ∥ (Q ∥ R')). split; [eapply pr_syncR; [done|by apply pr_parR]|].
        symmetry. apply cgr_par_assoc_rev.
      * exists (P ∥ (Q' ∥ R')). split; [apply pr_parR; by eapply pr_syncR|].
        symmetry. apply cgr_par_assoc_rev.
Qed.

Lemma fwd_ite_t e P Q : eval e = Some (VBool true) → fwd (If e Then P Else Q) P ∧ fwd P (If e Then P Else Q).
Proof.
  intros He. split; apply fwd_refl_step; intros s l P' Hs.
  - inversion Hs; subst; [done|congruence].
  - by apply pr_iteT.
Qed.

Lemma fwd_ite_f e P Q : eval e = Some (VBool false) → fwd (If e Then P Else Q) Q ∧ fwd Q (If e Then P Else Q).
Proof.
  intros He. split; apply fwd_refl_step; intros s l P' Hs.
  - inversion Hs; subst; [congruence|done].
  - by apply pr_iteF.
Qed.

Lemma fwd_send_val t c e v :
  eval e = Some v → fwd (t ∶ c ! e) (t ∶ c ! (EVal v)) ∧ fwd (t ∶ c ! (EVal v)) (t ∶ c ! e).
Proof.
  intros He.
  split; apply fwd_refl_step; intros s l P' Hs; inversion Hs; subst; constructor; simpl in *; congruence.
Qed.

Lemma fwd_ite_val e v P Q :
  eval e = Some v → fwd (If e Then P Else Q) (If (EVal v) Then P Else Q) ∧ fwd (If (EVal v) Then P Else Q) (If e Then P Else Q).
Proof.
  intros He.
  split; apply fwd_refl_step; intros s l P' Hs; inversion Hs; subst;
    [apply pr_iteT|apply pr_iteF|apply pr_iteT|apply pr_iteF]; simpl in *; congruence.
Qed.

Lemma fwd_res_nil es : fwd (ν (GNil es)) ((GNil es)) ∧ fwd ((GNil es)) (ν (GNil es)).
Proof.
  split; intros s l P' Hs; inversion Hs; subst; exfalso; by eapply pstep_nil.
Qed.

Lemma ren_lbl_swap01_SS l : ren_lbl swap01 (ren_lbl S (ren_lbl S l)) = ren_lbl S (ren_lbl S l).
Proof. rewrite !ren_lbl_comp. apply ren_lbl_ext_fun. intros i. apply swap01_SS. Qed.

Lemma fwd_res_swap_1 P : fwd (ν ν P) (ν ν (ren swap01 P)).
Proof.
  intros s l X Hs. inversion Hs as [| | | | | | | | | | | | | |? ? ? Y HY|]; subst.
  inversion HY as [| | | | | | | | | | | | | |? ? ? P' HP|]; subst.
  pose proof (prog_step_ren swap01 _ _ _ _ HP) as HP'. rewrite ren_lbl_swap01_SS in HP'.
  exists (ν ν (ren swap01 P')). split; [by do 2 apply pr_res|].
  apply cgr_res_swap.
Qed.

Lemma fwd_res_swap P : fwd (ν ν P) (ν ν (ren swap01 P)) ∧ fwd (ν ν (ren swap01 P)) (ν ν P).
Proof.
  split; [apply fwd_res_swap_1|].
  rewrite <- (ren_swap01_invol P) at 2. apply fwd_res_swap_1.
Qed.

Lemma fwd_res_scope P Q : fwd ((ν P) ∥ Q) (ν (P ∥ ren S Q)) ∧ fwd (ν (P ∥ ren S Q)) ((ν P) ∥ Q).
Proof.
  split.
  - intros s l X Hs.
    inversion Hs as [| | | | | | | | | |? ? ? ? X' HX|? ? ? ? Q' HQ|? ? t t' c v X' Q' HX HQ|? ? t t' c v X' Q' HX HQ| |];
      subst.
    + inversion HX as [| | | | | | | | | | | | | |? ? ? P' HP|]; subst.
      exists (ν (P' ∥ ren S Q)). split; [by apply pr_res, pr_parL|]. apply cgr_res_scope_rev.
    + exists (ν (P ∥ ren S Q')). split; [apply pr_res, pr_parR; by apply prog_step_ren|].
      apply cgr_res_scope_rev.
    + inversion HX as [| | | | | | | | | | | | | |? ? ? P' HP|]; subst.
      pose proof (prog_step_ren S _ _ _ _ HQ) as HQ'. simpl in HQ'.
      exists (ν (P' ∥ ren S Q')). split; [apply pr_res; simpl; by eapply pr_syncL|].
      apply cgr_res_scope_rev.
    + inversion HX as [| | | | | | | | | | | | | |? ? ? P' HP|]; subst.
      pose proof (prog_step_ren S _ _ _ _ HQ) as HQ'. simpl in HQ'.
      exists (ν (P' ∥ ren S Q')). split; [apply pr_res; simpl; by eapply pr_syncR|].
      apply cgr_res_scope_rev.
  - intros s l X Hs. inversion Hs as [| | | | | | | | | | | | | |? ? ? Y HY|]; subst.
    inversion HY as [| | | | | | | | | |? ? ? ? P' HP|? ? ? ? Y' HQ|? ? t t' c v P' Y' HP HQ|? ? t t' c v P' Y' HP HQ| |];
      subst.
    + exists ((ν P') ∥ Q). split; [by apply pr_parL, pr_res|]. symmetry. apply cgr_res_scope_rev.
    + destruct (prog_step_ren_inv S S_inj_fun _ _ _ _ HQ) as (l0 & Q' & El & -> & HQ0).
      apply ren_lbl_inj in El as ->; [|exact S_inj_fun].
      exists ((ν P) ∥ Q'). split; [by apply pr_parR|]. symmetry. apply cgr_res_scope_rev.
    + destruct l; simpl in *; simplify_eq.
      destruct (prog_step_ren_inv S S_inj_fun _ _ _ _ HQ) as (l0 & Q' & El & -> & HQ0).
      destruct l0 as [[c0 v0|c0 v0| | |]|]; simpl in El; simplify_eq.
      exists ((ν P') ∥ Q'). split; [|symmetry; apply cgr_res_scope_rev].
      eapply pr_syncL; [|exact HQ0]. by apply pr_res.
    + destruct l; simpl in *; simplify_eq.
      destruct (prog_step_ren_inv S S_inj_fun _ _ _ _ HQ) as (l0 & Q' & El & -> & HQ0).
      destruct l0 as [[c0 v0|c0 v0| | |]|]; simpl in El; simplify_eq.
      exists ((ν P') ∥ Q'). split; [|symmetry; apply cgr_res_scope_rev].
      eapply pr_syncR; [|exact HQ0]. by apply pr_res.
Qed.

Lemma fwd_sum_nil g es : fwd (g + GNil es) g ∧ fwd g (g + GNil es).
Proof.
  split; apply fwd_refl_step; intros s l P' Hs.
  - inversion Hs; subst; [done|exfalso; by eapply pstep_nil].
  - by apply pr_sumL.
Qed.

Lemma fwd_sum_comm g h : fwd (g + h) (h + g).
Proof.
  apply fwd_refl_step. intros s l P' Hs. inversion Hs; subst; [by apply pr_sumR|by apply pr_sumL].
Qed.

Lemma fwd_sum_assoc g h k :
  fwd (g + (h + k)) ((g + h) + k) ∧ fwd ((g + h) + k) (g + (h + k)).
Proof.
  split; apply fwd_refl_step; intros s l P' Hs.
  - inversion Hs as [| | | | |? ? ? ? ? H1|? ? ? ? ? H2| | | | | | | | |]; subst.
    + by do 2 apply pr_sumL.
    + inversion H2; subst; [by apply pr_sumL, pr_sumR|by apply pr_sumR].
  - inversion Hs as [| | | | |? ? ? ? ? H1|? ? ? ? ? H2| | | | | | | | |]; subst.
    + inversion H1; subst; [by apply pr_sumL|by apply pr_sumR, pr_sumL].
    + by do 2 apply pr_sumR.
Qed.

Lemma fwd_nil_val es es' : fwd (GNil es) (GNil es').
Proof. intros s l P' Hs. exfalso. by eapply pstep_nil. Qed.

Lemma fwd_op_val t E es1 e v es2 P :
  eval e = Some v →
  fwd (t ∶ E ⦅es1 ++ e :: es2⦆ ∙ P) (t ∶ E ⦅es1 ++ EVal v :: es2⦆ ∙ P)
  ∧ fwd (t ∶ E ⦅es1 ++ EVal v :: es2⦆ ∙ P) (t ∶ E ⦅es1 ++ e :: es2⦆ ∙ P).
Proof.
  intros He. pose proof (eval_qubits_val es1 e v es2 He) as Ev.
  split; apply fwd_refl_step; intros s l X Hs; inversion Hs; subst; constructor; congruence.
Qed.

Lemma fwd_meas_val t M es1 e v es2 P :
  eval e = Some v →
  fwd (t ∶ M ⦅es1 ++ e :: es2 ▷⦆ ∙ P) (t ∶ M ⦅es1 ++ EVal v :: es2 ▷⦆ ∙ P)
  ∧ fwd (t ∶ M ⦅es1 ++ EVal v :: es2 ▷⦆ ∙ P) (t ∶ M ⦅es1 ++ e :: es2 ▷⦆ ∙ P).
Proof.
  intros He. pose proof (eval_qubits_val es1 e v es2 He) as Ev.
  split; apply fwd_refl_step; intros s l X Hs; inversion Hs; subst; constructor; congruence.
Qed.

Lemma fwd_init_val t es1 e v es2 P :
  eval e = Some v →
  fwd (t ∶ init ⦅es1 ++ e :: es2⦆ ∙ P) (t ∶ init ⦅es1 ++ EVal v :: es2⦆ ∙ P)
  ∧ fwd (t ∶ init ⦅es1 ++ EVal v :: es2⦆ ∙ P) (t ∶ init ⦅es1 ++ e :: es2⦆ ∙ P).
Proof.
  intros He. pose proof (eval_qubits_val es1 e v es2 He) as Ev.
  split; apply fwd_refl_step; intros s l X Hs; inversion Hs; subst; constructor; congruence.
Qed.

(* *** Contexts *)

Lemma fwd_ite_l e P P' Q : fwd P P' → fwd (If e Then P Else Q) (If e Then P' Else Q).
Proof.
  intros H s l X Hs. inversion Hs as [| | | | | | | |? ? ? ? ? ? He Hp|? ? ? ? ? ? He Hq| | | | | |]; subst.
  - destruct (H _ _ _ Hp) as (Y & Hs' & HY). exists Y. split; [|done]. by apply pr_iteT.
  - exists X. split; [by apply pr_iteF|done].
Qed.

Lemma fwd_ite_r e P Q Q' : fwd Q Q' → fwd (If e Then P Else Q) (If e Then P Else Q').
Proof.
  intros H s l X Hs. inversion Hs as [| | | | | | | |? ? ? ? ? ? He Hp|? ? ? ? ? ? He Hq| | | | | |]; subst.
  - exists X. split; [by apply pr_iteT|done].
  - destruct (H _ _ _ Hq) as (Y & Hs' & HY). exists Y. split; [|done]. by apply pr_iteF.
Qed.

Lemma fwd_par_l P P' Q : P ≡* P' → fwd P P' → fwd (P ∥ Q) (P' ∥ Q).
Proof.
  intros Hc H s l X Hs.
  inversion Hs as [| | | | | | | | | |? ? ? ? P1 HP|? ? ? ? Q1 HQ|? ? t t' c v P1 Q1 HP HQ|? ? t t' c v P1 Q1 HP HQ| |];
    subst.
  - destruct (H _ _ _ HP) as (Y & Hs' & HY). exists (Y ∥ Q). split; [by apply pr_parL|by apply cgr_par].
  - exists (P' ∥ Q1). split; [by apply pr_parR|by apply cgr_par].
  - destruct (H _ _ _ HP) as (Y & Hs' & HY). exists (Y ∥ Q1). split; [by eapply pr_syncL|by apply cgr_par].
  - destruct (H _ _ _ HP) as (Y & Hs' & HY). exists (Y ∥ Q1). split; [by eapply pr_syncR|by apply cgr_par].
Qed.

Lemma fwd_par_r P Q Q' : Q ≡* Q' → fwd Q Q' → fwd (P ∥ Q) (P ∥ Q').
Proof.
  intros Hc H s l X Hs.
  inversion Hs as [| | | | | | | | | |? ? ? ? P1 HP|? ? ? ? Q1 HQ|? ? t t' c v P1 Q1 HP HQ|? ? t t' c v P1 Q1 HP HQ| |];
    subst.
  - exists (P1 ∥ Q'). split; [by apply pr_parL|by apply cgr_par_r].
  - destruct (H _ _ _ HQ) as (Y & Hs' & HY). exists (P ∥ Y). split; [by apply pr_parR|by apply cgr_par_r].
  - destruct (H _ _ _ HQ) as (Y & Hs' & HY). exists (P1 ∥ Y). split; [by eapply pr_syncL|by apply cgr_par_r].
  - destruct (H _ _ _ HQ) as (Y & Hs' & HY). exists (P1 ∥ Y). split; [by eapply pr_syncR|by apply cgr_par_r].
Qed.

Lemma fwd_res P P' : fwd P P' → fwd (ν P) (ν P').
Proof.
  intros H s l X Hs. inversion Hs as [| | | | | | | | | | | | | |? ? ? P1 HP|]; subst.
  destruct (H _ _ _ HP) as (Y & Hs' & HY). exists (ν Y). split; [by apply pr_res|by apply cgr_res].
Qed.

Lemma fwd_rec t X P P' : P ≡* P' → fwd (t ∶ rec X ∙ P) (t ∶ rec X ∙ P').
Proof.
  intros H s l Y Hs. inversion Hs; subst.
  exists (P' ⦃ t ∶ rec X ∙ P' // X ⦄). split; [constructor|by apply cgr_unfold].
Qed.

Lemma fwd_pre 𝜆 P P' : P ≡* P' → fwd (𝜆 ∙ P) (𝜆 ∙ P').
Proof.
  intros Hc s l X Hs. inversion Hs; subst.
  - exists P'. split; [constructor|done].
  - exists (P' ⟦ v ⟧). split; [constructor|by apply cgr_subst].
  - exists P'. split; [by constructor|done].
  - exists (P' ⟦ VNat n ⟧). split; [by constructor|by apply cgr_subst].
  - exists P'. split; [by constructor|done].
Qed.

Lemma fwd_sum_l (g g' h : guard) : fwd g g' → fwd (g + h) (g' + h).
Proof.
  intros H s l X Hs. inversion Hs as [| | | | |? ? ? ? ? Hg|? ? ? ? ? Hh| | | | | | | | |]; subst.
  - destruct (H _ _ _ Hg) as (Y & Hs' & HY). exists Y. split; [by apply pr_sumL|done].
  - exists X. split; [by apply pr_sumR|done].
Qed.

Lemma fwd_sum_r (g h h' : guard) : fwd h h' → fwd (g + h) (g + h').
Proof.
  intros H s l X Hs. inversion Hs as [| | | | |? ? ? ? ? Hg|? ? ? ? ? Hh| | | | | | | | |]; subst.
  - exists X. split; [by apply pr_sumL|done].
  - destruct (H _ _ _ Hh) as (Y & Hs' & HY). exists Y. split; [by apply pr_sumR|done].
Qed.

(* *** The bisimulation *)

Theorem cgr_step_bisim :
  (∀ P Q, cgr_step P Q → fwd P Q ∧ fwd Q P) ∧ (∀ g h, gcgr_step g h → fwd g h ∧ fwd h g).
Proof.
  apply cgr_gcgr_step_ind; intros.
  - apply fwd_par_nil.
  - split; apply fwd_par_comm.
  - apply fwd_par_assoc.
  - by apply fwd_ite_t.
  - by apply fwd_ite_f.
  - by apply fwd_send_val.
  - by apply fwd_ite_val.
  - apply fwd_res_nil.
  - apply fwd_res_swap.
  - apply fwd_res_scope.
  - destruct H. split; by apply fwd_ite_l.
  - destruct H. split; by apply fwd_ite_r.
  - destruct H. split; apply fwd_par_l; try done; [by apply cgr_of_step|symmetry; by apply cgr_of_step].
  - destruct H. split; apply fwd_par_r; try done; [by apply cgr_of_step|symmetry; by apply cgr_of_step].
  - destruct H. split; by apply fwd_res.
  - split; apply fwd_rec; [by apply cgr_of_step|symmetry; by apply cgr_of_step].
  - done.
  - apply fwd_sum_nil.
  - split; apply fwd_sum_comm.
  - apply fwd_sum_assoc.
  - split; apply fwd_nil_val.
  - by apply fwd_op_val.
  - by apply fwd_meas_val.
  - by apply fwd_init_val.
  - split; apply fwd_pre; [by apply cgr_of_step|symmetry; by apply cgr_of_step].
  - destruct H. split; by apply fwd_sum_l.
  - destruct H. split; by apply fwd_sum_r.
Qed.

(* [≡*] is a bisimulation, with the same choices. *)
Theorem cgr_bisim P Q : P ≡* Q → fwd P Q.
Proof.
  induction 1 as [P|P Q R [H|H] _ IH]; [by apply fwd_refl_step| |].
  all: intros s l P' Hs.
  - destruct (proj1 (proj1 cgr_step_bisim P Q H) s l P' Hs) as (Q' & Hs1 & H1).
    destruct (IH _ _ _ Hs1) as (R' & Hs2 & H2).
    exists R'. split; [done|by etrans].
  - destruct (proj2 (proj1 cgr_step_bisim Q P H) s l P' Hs) as (Q' & Hs1 & H1).
    destruct (IH _ _ _ Hs1) as (R' & Hs2 & H2).
    exists R'. split; [done|by etrans].
Qed.

(* ** Congruence respects transitions, as in VACCS *)

Definition sc_then_lts (P : proc) (s : choice) (l : Labels prog_action) (Q : proc) : Prop :=
  ∃ R, P ≡* R ∧ R ⟶{l}[s] Q.

Definition lts_then_sc (P : proc) (s : choice) (l : Labels prog_action) (Q : proc) : Prop :=
  ∃ R, P ⟶{l}[s] R ∧ R ≡* Q.

Theorem Congruence_Respects_Transition P s l Q : sc_then_lts P s l Q → lts_then_sc P s l Q.
Proof.
  intros (R & HPR & HR). destruct (cgr_bisim R P (symmetry HPR) s l Q HR) as (Q' & HQ' & HQ).
  exists Q'. split; [done|by symmetry].
Qed.
(* end hide *)
