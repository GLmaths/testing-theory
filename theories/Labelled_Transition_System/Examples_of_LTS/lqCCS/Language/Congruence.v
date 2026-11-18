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
From stdpp Require Import base gmultiset countable decidable list sets relations.
From TestingTheory Require Import ActTau.
From TestingTheory Require Import lqCCS.Language.Algebra lqCCS.Language.Quantum.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Helper_substitution.De_Brujin_lemmas lqCCS.General_definition.Parallel_choice_LTS lqCCS.Language.LTS_quantum_mem lqCCS.Language.LTS_lqCCS_prog lqCCS.Language.LTS_lqCCS_process lqCCS.Language.LTS_lqCCS_par_Qmem lqCCS.Helper_substitution.Label_lemmas.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

(* ** One step of congruence *)

Reserved Notation "P ≡ Q" (at level 70, no associativity).
Reserved Notation "g ≡ᵍ h" (at level 70, no associativity).

Section LqP.
  Context `{LP : lqCCS_Parameters}.

Inductive cgr_step : proc → proc → Prop :=
| cgr_par_nil_step P : (P ∥ 𝟘) ≡ P
| cgr_par_com_step P Q : (P ∥ Q) ≡ (Q ∥ P)
| cgr_par_assoc_rev_step P Q R : (P ∥ (Q ∥ R)) ≡ ((P ∥ Q) ∥ R)
| cgr_if_true_step e P Q : 〚 e 〛 = true → (If e Then P Else Q) ≡ P
| cgr_if_false_step e P Q : 〚 e 〛 = false → (If e Then P Else Q) ≡ Q
| cgr_send_val_step t c e v : 〚 e 〛 = v → (t ∶ c ! e) ≡ (t ∶ c ! v)
| cgr_if_val_step e v P Q : 〚 e 〛 = v → (If e Then P Else Q) ≡ (If v Then P Else Q)
| cgr_res_nil_step es : (ν 𝟘{es}) ≡ 𝟘{es}
| cgr_res_swap_step P : (ν ν P) ≡ (ν ν (ren swap01 P))
| cgr_res_scope_rev_step P Q : ((ν P) ∥ Q) ≡ (ν (P ∥ ren S Q))
(* contexts *)
| cgr_if_then_step e P P' Q : P ≡ P' → (If e Then P Else Q) ≡ (If e Then P' Else Q)
| cgr_if_else_step e P Q Q' : Q ≡ Q' → (If e Then P Else Q) ≡ (If e Then P Else Q')
| cgr_par_step P P' Q : P ≡ P' → (P ∥ Q) ≡ (P' ∥ Q)
| cgr_par_right_step P Q Q' : Q ≡ Q' → (P ∥ Q) ≡ (P ∥ Q')
| cgr_res_step P P' : P ≡ P' → (ν P) ≡ (ν P')
| cgr_recursion_step t P P' : P ≡ P' → (t ∶ rec ∙ P) ≡ (t ∶ rec ∙ P')
| cgr_guard_step g g' : g ≡ᵍ g' → g ≡ g'
with gcgr_step : guard → guard → Prop :=
| cgr_choice_nil_step g es : (g + 𝟘{es}) ≡ᵍ g
| cgr_choice_com_step g h : (g + h) ≡ᵍ (h + g)
| cgr_choice_assoc_rev_step g h k : (g + (h + k)) ≡ᵍ ((g + h) + k)
| cgr_nil_val_step es1 e v es2 :
    〚 e 〛 = v → 𝟘{es1 ++ e :: es2} ≡ᵍ 𝟘{es1 ++ EVal v :: es2}
| cgr_op_val_step t U es1 e v es2 P :
    〚 e 〛 = v → (t ∶ U ⦅es1 ++ e :: es2⦆ ∙ P) ≡ᵍ (t ∶ U ⦅es1 ++ EVal v :: es2⦆ ∙ P)
| cgr_meas_val_step t M es1 e v es2 P :
    〚 e 〛 = v → (t ∶ M ⦅es1 ++ e :: es2 ▷⦆ ∙ P) ≡ᵍ (t ∶ M ⦅es1 ++ EVal v :: es2 ▷⦆ ∙ P)
| cgr_init_val_step t e v P :
    〚 e 〛 = v → (t ∶ e := |0⟩ ∙ P) ≡ᵍ (t ∶ v := |0⟩ ∙ P)
(* contexts *)
| cgr_prefix_step 𝜆 P P' : P ≡ P' → (𝜆 ∙ P) ≡ᵍ (𝜆 ∙ P')
| cgr_choice_step g g' h : g ≡ᵍ g' → (g + h) ≡ᵍ (g' + h)
| cgr_choice_right_step g h h' : h ≡ᵍ h' → (g + h) ≡ᵍ (g + h')
where "P ≡ Q" := (cgr_step P Q) : lqccs_scope
and "g ≡ᵍ h" := (gcgr_step g h) : lqccs_scope.

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
  〚 e 〛 = v → eval_qubits (es1 ++ e :: es2) = eval_qubits (es1 ++ EVal v :: es2).
Proof.
  intros He. assert (E : eval_qubit e = eval_qubit v)
    by (unfold eval_qubit; simpl; by rewrite He).
  unfold eval_qubits. induction es1 as [|e1 es1 IH]; simpl; [by rewrite E|by rewrite IH].
Qed.

(* ** One step is a congruence *)

Lemma cgr_of_step P Q : P ≡ Q → P ≡* Q.
Proof. apply rtsc_lr. Qed.

Lemma gcgr_of_step g h : g ≡ᵍ h → g ≡ᵍ* h.
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

Lemma cgr_if_true e P Q : 〚 e 〛 = true → If e Then P Else Q ≡* P.
Proof. intros. by apply cgr_of_step, cgr_if_true_step. Qed.

Lemma cgr_if_true_rev e P Q : 〚 e 〛 = true → P ≡* If e Then P Else Q.
Proof. intros. by apply rtsc_rl, cgr_if_true_step. Qed.

Lemma cgr_if_false e P Q : 〚 e 〛 = false → If e Then P Else Q ≡* Q.
Proof. intros. by apply cgr_of_step, cgr_if_false_step. Qed.

Lemma cgr_if_false_rev e P Q : 〚 e 〛 = false → Q ≡* If e Then P Else Q.
Proof. intros. by apply rtsc_rl, cgr_if_false_step. Qed.

Lemma cgr_res_nil es : (ν 𝟘{es}) ≡* 𝟘{es}.
Proof. apply cgr_of_step, cgr_res_nil_step. Qed.

Lemma cgr_res_nil_rev es : 𝟘{es} ≡* (ν 𝟘{es}).
Proof. apply rtsc_rl, cgr_res_nil_step. Qed.

Lemma cgr_res_swap P : (ν ν P) ≡* (ν ν (ren swap01 P)).
Proof. apply cgr_of_step, cgr_res_swap_step. Qed.

Lemma cgr_res_swap_rev P : (ν ν (ren swap01 P)) ≡* (ν ν P).
Proof. apply rtsc_rl, cgr_res_swap_step. Qed.

Lemma cgr_res_scope P Q : (ν (P ∥ ren S Q)) ≡* (ν P) ∥ Q.
Proof. apply rtsc_rl, cgr_res_scope_rev_step. Qed.

Lemma cgr_res_scope_rev P Q : (ν P) ∥ Q ≡* (ν (P ∥ ren S Q)).
Proof. apply cgr_of_step, cgr_res_scope_rev_step. Qed.

Lemma gcgr_choice_nil g es : (g + 𝟘{es}) ≡ᵍ* g.
Proof. apply gcgr_of_step, cgr_choice_nil_step. Qed.

Lemma gcgr_choice_nil_rev g es : g ≡ᵍ* (g + 𝟘{es}).
Proof. apply rtsc_rl, cgr_choice_nil_step. Qed.

Lemma gcgr_choice_com g h : (g + h) ≡ᵍ* (h + g).
Proof. apply gcgr_of_step, cgr_choice_com_step. Qed.

Lemma gcgr_choice_assoc g h k : ((g + h) + k) ≡ᵍ* (g + (h + k)).
Proof. apply rtsc_rl, cgr_choice_assoc_rev_step. Qed.

Lemma gcgr_choice_assoc_rev g h k : (g + (h + k)) ≡ᵍ* ((g + h) + k).
Proof. apply gcgr_of_step, cgr_choice_assoc_rev_step. Qed.

(* ** Congruence under contexts *)

Lemma cgr_ctx (f : proc → proc) :
  (∀ P Q, P ≡ Q → (f P) ≡ (f Q)) → ∀ P Q, P ≡* Q → f P ≡* f Q.
Proof.
  intros Hf P Q. induction 1 as [P|P Q R [HPQ|HQP] _ IH]; [done| |].
  - etrans; [|exact IH]. apply rtsc_lr. by apply Hf.
  - etrans; [|exact IH]. apply rtsc_rl. by apply Hf.
Qed.

Lemma gcgr_ctx (f : guard → guard) :
  (∀ g h, g ≡ᵍ h → (f g) ≡ᵍ (f h)) → ∀ g h, g ≡ᵍ* h → (f g) ≡ᵍ* (f h).
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

Lemma cgr_recursion t P P' : P ≡* P' → t ∶ rec ∙ P ≡* t ∶ rec ∙ P'.
Proof. apply (cgr_ctx (λ P, t ∶ rec ∙ P)). intros. by constructor. Qed.

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

(* ** Congruence as morphisms *)

#[global] Instance par_proper : Proper (cgr ==> cgr ==> cgr) PPar.
Proof. intros P P' HP Q Q' HQ. by apply cgr_fullpar. Qed.

#[global] Instance res_proper : Proper (cgr ==> cgr) PRes.
Proof. intros P P' HP. by apply cgr_res. Qed.

#[global] Instance ite_proper e : Proper (cgr ==> cgr ==> cgr) (PIte e).
Proof. intros P P' HP Q Q' HQ. by apply cgr_full_if. Qed.

#[global] Instance rec_proper t : Proper (cgr ==> cgr) (PRec t).
Proof. intros P P' HP. by apply cgr_recursion. Qed.

#[global] Instance guard_proper : Proper (gcgr ==> cgr) PG.
Proof. intros g h Hg. by apply cgr_guard. Qed.

#[global] Instance prefix_proper 𝜆 : Proper (cgr ==> gcgr) (GPre 𝜆).
Proof. intros P P' HP. by apply gcgr_prefix. Qed.

#[global] Instance sum_proper : Proper (gcgr ==> gcgr ==> gcgr) GSum.
Proof. intros g g' Hg h h' Hh. by apply gcgr_fullchoice. Qed.

(* [(P ∥ Q) ∥ R ≡ (P ∥ R) ∥ Q] *)
Lemma cgr_par_swap P Q R : (P ∥ Q) ∥ R ≡* (P ∥ R) ∥ Q.
Proof. by rewrite cgr_par_assoc, (cgr_par_com Q R), cgr_par_assoc_rev. Qed.

(* [(P ∥ Q) ∥ (R ∥ S) ≡ (P ∥ R) ∥ (Q ∥ S)] *)
Lemma cgr_par_inversion P Q R S : (P ∥ Q) ∥ (R ∥ S) ≡* (P ∥ R) ∥ (Q ∥ S).
Proof. by rewrite cgr_par_assoc_rev, (cgr_par_swap P Q R), cgr_par_assoc. Qed.

(* ** Renamings of indices *)

Lemma cgr_step_ren :
  (∀ P Q, P ≡ Q → ∀ f, (ren f P) ≡ (ren f Q))
  ∧ (∀ g h, g ≡ᵍ h → ∀ f, (gren f g) ≡ᵍ (gren f h)).
Proof.
  apply cgr_gcgr_step_ind; simpl; intros; try (constructor; done); try (by constructor; apply H).
  - rewrite ren_lift_lift_swap01. apply cgr_res_swap_step.
  - rewrite ren_lift_S. apply cgr_res_scope_rev_step.
Qed.

Lemma cgr_ren f P Q : P ≡* Q → ren f P ≡* ren f Q.
Proof. apply (cgr_ctx (ren f)). intros. by apply cgr_step_ren. Qed.

#[global] Instance ren_proper f : Proper (cgr ==> cgr) (ren f).
Proof. intros P P' HP. by apply cgr_ren. Qed.

(* ** Substitution and shift of values *)

Lemma cgr_step_subst :
  (∀ P Q, P ≡ Q → ∀ k v, (P ⁅ v // k ⁆ᵥ) ≡ (Q ⁅ v // k ⁆ᵥ))
  ∧ (∀ g h, g ≡ᵍ h → ∀ k v, (gsubst k v g) ≡ᵍ (gsubst k v h)).
Proof.
  apply cgr_gcgr_step_ind; simpl; intros; try (constructor; done); try (by constructor; apply H).
  all: try (rewrite <- (proj1 ren_subst); by constructor).
  all: rewrite ?map_app; simpl;
    match goal with Hx : 〚 ?e 〛 = _ |- _ => rewrite (exp_subst_closed _ _ e _ Hx) end;
    by constructor.
Qed.

Lemma cgr_subst k v P Q : P ≡* Q → P ⁅ v // k ⁆ᵥ ≡* Q ⁅ v // k ⁆ᵥ.
Proof. apply (cgr_ctx (subst k v)). intros. by apply cgr_step_subst. Qed.

#[global] Instance subst_proper k v : Proper (cgr ==> cgr) (subst k v).
Proof. intros P P' HP. by apply cgr_subst. Qed.

Lemma cgr_step_shiftv :
  (∀ P Q, P ≡ Q → ∀ k, (shiftv k P) ≡ (shiftv k Q))
  ∧ (∀ g h, g ≡ᵍ h → ∀ k, (gshiftv k g) ≡ᵍ (gshiftv k h)).
Proof.
  apply cgr_gcgr_step_ind; simpl; intros; try (constructor; done); try (by constructor; apply H).
  all: try (rewrite <- (proj1 ren_shiftv); by constructor).
  all: rewrite ?map_app; simpl;
    match goal with Hx : 〚 ?e 〛 = _ |- _ => rewrite (exp_shift_closed _ e _ Hx) end;
    by constructor.
Qed.

Lemma cgr_shiftv k P Q : P ≡* Q → shiftv k P ≡* shiftv k Q.
Proof. apply (cgr_ctx (shiftv k)). intros. by apply cgr_step_shiftv. Qed.

Lemma cgr_shiftv_iter n P Q : P ≡* Q → Nat.iter n ⇧ᵥ P ≡* Nat.iter n ⇧ᵥ Q.
Proof. induction n; simpl; [done|]. intros. by apply cgr_shiftv, IHn. Qed.

(* ** Substitution of processes *)

Lemma cgr_step_pr_subst_l :
  (∀ P P', P ≡ P' → ∀ k Q, (P ⁅ Q // k ⁆ₚ) ≡ (P' ⁅ Q // k ⁆ₚ))
  ∧ (∀ g g', g ≡ᵍ g' → ∀ k Q, (gpr_subst k g Q) ≡ᵍ (gpr_subst k g' Q)).
Proof.
  apply cgr_gcgr_step_ind; simpl; intros; try (constructor; done); try (by constructor; apply H).
  - replace ((ren swap01 P) ⁅ ren S (ren S Q) // k ⁆ₚ) with (ren swap01 (P ⁅ ren S (ren S Q) // k ⁆ₚ)).
    + apply cgr_res_swap_step.
    + rewrite (proj1 ren_pr_subst). by rewrite ren_swap01_SS.
  - rewrite <- (proj1 ren_pr_subst). apply cgr_res_scope_rev_step.
Qed.

Lemma cgr_pr_subst_l P P' k Q : P ≡* P' → P ⁅ Q // k ⁆ₚ ≡* P' ⁅ Q // k ⁆ₚ.
Proof. apply (cgr_ctx (λ P, P ⁅ Q // k ⁆ₚ)). intros. by apply cgr_step_pr_subst_l. Qed.

Lemma cgr_step_rshift :
  (∀ P P', P ≡ P' → ∀ k, (rshift k P) ≡ (rshift k P'))
  ∧ (∀ g g', g ≡ᵍ g' → ∀ k, (grshift k g) ≡ᵍ (grshift k g')).
Proof.
  apply cgr_gcgr_step_ind; simpl; intros; try (constructor; done); try (by constructor; apply H).
  - rewrite <- (proj1 ren_rshift). apply cgr_res_swap_step.
  - rewrite <- (proj1 ren_rshift). apply cgr_res_scope_rev_step.
Qed.

Lemma cgr_rshift k P P' : P ≡* P' → rshift k P ≡* rshift k P'.
Proof. apply (cgr_ctx (rshift k)). intros. by apply cgr_step_rshift. Qed.

Lemma cgr_pr_subst_r :
  (∀ P k Q Q', Q ≡* Q' → P ⁅ Q // k ⁆ₚ ≡* P ⁅ Q' // k ⁆ₚ)
  ∧ (∀ g k Q Q', Q ≡* Q' → (gpr_subst k g Q) ≡ᵍ* (gpr_subst k g Q')).
Proof.
  apply proc_guard_ind; simpl; intros; try done.
  - apply cgr_full_if; auto.
  - apply cgr_fullpar; auto.
  - apply cgr_res, H. by apply cgr_ren.
  - by repeat case_decide.
  - apply cgr_recursion, H. by apply cgr_rshift.
  - apply cgr_guard. by apply H.
  - apply gcgr_prefix, H. by apply cgr_shiftv_iter.
  - apply gcgr_fullchoice; auto.
Qed.

Lemma cgr_step_tren :
  (∀ P P', P ≡ P' → ∀ f, (tren f P) ≡ (tren f P'))
  ∧ (∀ g g', g ≡ᵍ g' → ∀ f, (gtren f g) ≡ᵍ (gtren f g')).
Proof.
  apply cgr_gcgr_step_ind; simpl; intros; try (constructor; done); try (by constructor; apply H).
  - rewrite (proj1 tren_ren). apply cgr_res_swap_step.
  - rewrite (proj1 tren_ren). apply cgr_res_scope_rev_step.
Qed.

Lemma cgr_tren f P P' : P ≡* P' → tren f P ≡* tren f P'.
Proof. apply (cgr_ctx (tren f)). intros. by apply cgr_step_tren. Qed.

#[global] Instance tren_proper f : Proper (cgr ==> cgr) (tren f).
Proof. intros P P' HP. by apply cgr_tren. Qed.

(* Unfolding congruent recursions gives congruent processes. *)
Lemma cgr_unfold t P P' :
  P ≡* P' → P ⁅ (t ∶ rec ∙ P)↑ ⁆ₚ ≡* P' ⁅ (t ∶ rec ∙ P')↑ ⁆ₚ.
Proof.
  intros H. etrans; [by apply cgr_pr_subst_l|].
  apply (proj1 cgr_pr_subst_r). by apply cgr_tren, cgr_recursion.
Qed.

(* ** Facts on steps *)

Lemma pstep_nil es s l P' : 𝟘{es} ↛ₚ{l}[s] P'.
Proof. intros Hs%prog_step_guard. inversion Hs. Qed.

Lemma S_inj_fun : ∀ i j : nat, S i = S j → i = j.
Proof. intros i j [=]. done. Qed.

(* ** Structural congruence is a bisimulation *)

Definition fwd (P Q : proc) : Prop :=
  ∀ s l P', P ⟶ₚ{l}[s] P' → ∃ Q', Q ⟶ₚ{l}[s] Q' ∧ P' ≡* Q'.

Lemma fwd_refl_step P Q : (∀ s l P', P ⟶ₚ{l}[s] P' → Q ⟶ₚ{l}[s] P') → fwd P Q.
Proof. intros H s l P' Hs. exists P'. split; [by apply H|done]. Qed.

Lemma fwd_par_nil P : fwd (P ∥ 𝟘) P ∧ fwd P (P ∥ 𝟘).
Proof.
  split.
  - intros s l X Hs. inversion Hs as [| | | |? ? ? ? P' HP| | | | |]; subst;
      try (exfalso; by eapply pstep_nil).
    exists P'. split; [done|]. apply cgr_par_nil.
  - intros s l P' Hs. exists (P' ∥ 𝟘). split; [by apply pr_parL|].
    symmetry. apply cgr_par_nil.
Qed.

Lemma fwd_par_comm P Q : fwd (P ∥ Q) (Q ∥ P).
Proof.
  intros s l X Hs.
  inversion Hs as [| | | |? ? ? ? P' HP|? ? ? ? Q' HQ|? ? t t' c v P' Q' HP HQ|? ? t t' c v P' Q' HP HQ| |];
    subst.
  - exists (Q ∥ P'). split; [by apply pr_parR|]. apply cgr_par_com.
  - exists (Q' ∥ P). split; [by apply pr_parL|]. apply cgr_par_com.
  - exists (Q' ∥ P'). split; [rewrite (comm disj_union {[+ t +]}); by eapply pr_syncR|]. apply cgr_par_com.
  - exists (Q' ∥ P'). split; [rewrite (comm disj_union {[+ t +]}); by eapply pr_syncL|]. apply cgr_par_com.
Qed.

Lemma fwd_par_assoc P Q R :
  fwd (P ∥ (Q ∥ R)) ((P ∥ Q) ∥ R) ∧ fwd ((P ∥ Q) ∥ R) (P ∥ (Q ∥ R)).
Proof.
  split.
  - intros s l X Hs.
    inversion Hs as [| | | |? ? ? ? P' HP|? ? ? ? X' HX|? ? t t' c v P' X' HP HX|? ? t t' c v P' X' HP HX| |];
      subst.
    + exists ((P' ∥ Q) ∥ R). split; [by do 2 apply pr_parL|]. apply cgr_par_assoc_rev.
    + inversion HX as [| | | |? ? ? ? Q' HQ|? ? ? ? R' HR|? ? t t' c v Q' R' HQ HR|? ? t t' c v Q' R' HQ HR| |];
        subst.
      * exists ((P ∥ Q') ∥ R). split; [by apply pr_parL, pr_parR|]. apply cgr_par_assoc_rev.
      * exists ((P ∥ Q) ∥ R'). split; [by apply pr_parR|]. apply cgr_par_assoc_rev.
      * exists ((P ∥ Q') ∥ R'). split; [eapply pr_syncL; [by apply pr_parR|done]|].
        apply cgr_par_assoc_rev.
      * exists ((P ∥ Q') ∥ R'). split; [eapply pr_syncR; [by apply pr_parR|done]|].
        apply cgr_par_assoc_rev.
    + inversion HX as [| | | |? ? ? ? Q' HQ|? ? ? ? R' HR| | | |]; subst.
      * exists ((P' ∥ Q') ∥ R). split; [apply pr_parL; by eapply pr_syncL|]. apply cgr_par_assoc_rev.
      * exists ((P' ∥ Q) ∥ R'). split; [eapply pr_syncL; [by apply pr_parL|done]|].
        apply cgr_par_assoc_rev.
    + inversion HX as [| | | |? ? ? ? Q' HQ|? ? ? ? R' HR| | | |]; subst.
      * exists ((P' ∥ Q') ∥ R). split; [apply pr_parL; by eapply pr_syncR|]. apply cgr_par_assoc_rev.
      * exists ((P' ∥ Q) ∥ R'). split; [eapply pr_syncR; [by apply pr_parL|done]|].
        apply cgr_par_assoc_rev.
  - intros s l X Hs.
    inversion Hs as [| | | |? ? ? ? X' HX|? ? ? ? R' HR|? ? t t' c v X' R' HX HR|? ? t t' c v X' R' HX HR| |];
      subst.
    + inversion HX as [| | | |? ? ? ? P' HP|? ? ? ? Q' HQ|? ? t t' c v P' Q' HP HQ|? ? t t' c v P' Q' HP HQ| |];
        subst.
      * exists (P' ∥ (Q ∥ R)). split; [by apply pr_parL|]. symmetry. apply cgr_par_assoc_rev.
      * exists (P ∥ (Q' ∥ R)). split; [by apply pr_parR, pr_parL|]. symmetry. apply cgr_par_assoc_rev.
      * exists (P' ∥ (Q' ∥ R)). split; [eapply pr_syncL; [done|by apply pr_parL]|].
        symmetry. apply cgr_par_assoc_rev.
      * exists (P' ∥ (Q' ∥ R)). split; [eapply pr_syncR; [done|by apply pr_parL]|].
        symmetry. apply cgr_par_assoc_rev.
    + exists (P ∥ (Q ∥ R')). split; [by do 2 apply pr_parR|]. symmetry. apply cgr_par_assoc_rev.
    + inversion HX as [| | | |? ? ? ? P' HP|? ? ? ? Q' HQ| | | |]; subst.
      * exists (P' ∥ (Q ∥ R')). split; [eapply pr_syncL; [done|by apply pr_parR]|].
        symmetry. apply cgr_par_assoc_rev.
      * exists (P ∥ (Q' ∥ R')). split; [apply pr_parR; by eapply pr_syncL|].
        symmetry. apply cgr_par_assoc_rev.
    + inversion HX as [| | | |? ? ? ? P' HP|? ? ? ? Q' HQ| | | |]; subst.
      * exists (P' ∥ (Q ∥ R')). split; [eapply pr_syncR; [done|by apply pr_parR]|].
        symmetry. apply cgr_par_assoc_rev.
      * exists (P ∥ (Q' ∥ R')). split; [apply pr_parR; by eapply pr_syncR|].
        symmetry. apply cgr_par_assoc_rev.
Qed.

Lemma fwd_ite_t e P Q : 〚 e 〛 = true → fwd (If e Then P Else Q) P ∧ fwd P (If e Then P Else Q).
Proof.
  intros He. split; apply fwd_refl_step; intros s l P' Hs.
  - inversion Hs; subst; [done|congruence].
  - by apply pr_iteT.
Qed.

Lemma fwd_ite_f e P Q : 〚 e 〛 = false → fwd (If e Then P Else Q) Q ∧ fwd Q (If e Then P Else Q).
Proof.
  intros He. split; apply fwd_refl_step; intros s l P' Hs.
  - inversion Hs; subst; [congruence|done].
  - by apply pr_iteF.
Qed.

Lemma fwd_send_val t c e v :
  〚 e 〛 = v → fwd (t ∶ c ! e) (t ∶ c ! v) ∧ fwd (t ∶ c ! v) (t ∶ c ! e).
Proof.
  intros He.
  split; apply fwd_refl_step; intros s l P' Hs; inversion Hs; subst; constructor; simpl in *; congruence.
Qed.

Lemma fwd_ite_val e v P Q :
  〚 e 〛 = v → fwd (If e Then P Else Q) (If v Then P Else Q) ∧ fwd (If v Then P Else Q) (If e Then P Else Q).
Proof.
  intros He.
  split; apply fwd_refl_step; intros s l P' Hs; inversion Hs; subst;
    [apply pr_iteT|apply pr_iteF|apply pr_iteT|apply pr_iteF]; simpl in *; congruence.
Qed.

Lemma fwd_res_nil es : fwd (ν 𝟘{es}) 𝟘{es} ∧ fwd 𝟘{es} (ν 𝟘{es}).
Proof.
  split; intros s l P' Hs; inversion Hs; subst; exfalso; by eapply pstep_nil.
Qed.



Lemma fwd_res_swap_1 P : fwd (ν ν P) (ν ν (ren swap01 P)).
Proof.
  intros s l X Hs. inversion Hs as [| | | | | | | |? ? ? Y HY|]; subst.
  inversion HY as [| | | | | | | |? ? ? P' HP|]; subst.
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
    inversion Hs as [| | | |? ? ? ? X' HX|? ? ? ? Q' HQ|? ? t t' c v X' Q' HX HQ|? ? t t' c v X' Q' HX HQ| |];
      subst.
    + inversion HX as [| | | | | | | |? ? ? P' HP|]; subst.
      exists (ν (P' ∥ ren S Q)). split; [by apply pr_res, pr_parL|]. apply cgr_res_scope_rev.
    + exists (ν (P ∥ ren S Q')). split; [apply pr_res, pr_parR; by apply prog_step_ren|].
      apply cgr_res_scope_rev.
    + inversion HX as [| | | | | | | |? ? ? P' HP|]; subst.
      pose proof (prog_step_ren S _ _ _ _ HQ) as HQ'. simpl in HQ'.
      exists (ν (P' ∥ ren S Q')). split; [apply pr_res; simpl; by eapply pr_syncL|].
      apply cgr_res_scope_rev.
    + inversion HX as [| | | | | | | |? ? ? P' HP|]; subst.
      pose proof (prog_step_ren S _ _ _ _ HQ) as HQ'. simpl in HQ'.
      exists (ν (P' ∥ ren S Q')). split; [apply pr_res; simpl; by eapply pr_syncR|].
      apply cgr_res_scope_rev.
  - intros s l X Hs. inversion Hs as [| | | | | | | |? ? ? Y HY|]; subst.
    inversion HY as [| | | |? ? ? ? P' HP|? ? ? ? Y' HQ|? ? t t' c v P' Y' HP HQ|? ? t t' c v P' Y' HP HQ| |];
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

Lemma fwd_sum_nil g es : fwd (g + 𝟘{es}) g ∧ fwd g (g + 𝟘{es}).
Proof.
  split; apply fwd_refl_step; intros s l P' Hs.
  - apply prog_step_guard in Hs. inversion Hs; subst; [by apply pr_guard|exfalso; by eapply pstep_nil, pr_guard].
  - by apply pr_sumL.
Qed.

Lemma fwd_sum_comm g h : fwd (g + h) (h + g).
Proof.
  apply fwd_refl_step. intros s l P' Hs%prog_step_guard. apply prog_step_guard.
  inversion Hs; subst; [by apply pg_sumR|by apply pg_sumL].
Qed.

Lemma fwd_sum_assoc g h k :
  fwd (g + (h + k)) ((g + h) + k) ∧ fwd ((g + h) + k) (g + (h + k)).
Proof.
  split; apply fwd_refl_step; intros s l P' Hs%prog_step_guard; apply prog_step_guard.
  - inversion Hs as [| | | | |? ? ? ? ? H1|? ? ? ? ? H2]; subst.
    + by do 2 apply pg_sumL.
    + inversion H2; subst; [by apply pg_sumL, pg_sumR|by apply pg_sumR].
  - inversion Hs as [| | | | |? ? ? ? ? H1|? ? ? ? ? H2]; subst.
    + inversion H1; subst; [by apply pg_sumL|by apply pg_sumR, pg_sumL].
    + by do 2 apply pg_sumR.
Qed.

Lemma fwd_nil_val es es' : fwd 𝟘{es} 𝟘{es'}.
Proof. intros s l P' Hs. exfalso. by eapply pstep_nil. Qed.

Lemma fwd_op_val t U es1 e v es2 P :
  〚 e 〛 = v →
  fwd (t ∶ U ⦅es1 ++ e :: es2⦆ ∙ P) (t ∶ U ⦅es1 ++ EVal v :: es2⦆ ∙ P)
  ∧ fwd (t ∶ U ⦅es1 ++ EVal v :: es2⦆ ∙ P) (t ∶ U ⦅es1 ++ e :: es2⦆ ∙ P).
Proof.
  intros He. pose proof (eval_qubits_val es1 e v es2 He) as Ev.
  split; apply fwd_refl_step; intros s l X Hs%prog_step_guard; apply prog_step_guard; inversion Hs; subst; constructor; congruence.
Qed.

Lemma fwd_meas_val t M es1 e v es2 P :
  〚 e 〛 = v →
  fwd (t ∶ M ⦅es1 ++ e :: es2 ▷⦆ ∙ P) (t ∶ M ⦅es1 ++ EVal v :: es2 ▷⦆ ∙ P)
  ∧ fwd (t ∶ M ⦅es1 ++ EVal v :: es2 ▷⦆ ∙ P) (t ∶ M ⦅es1 ++ e :: es2 ▷⦆ ∙ P).
Proof.
  intros He. pose proof (eval_qubits_val es1 e v es2 He) as Ev.
  split; apply fwd_refl_step; intros s l X Hs%prog_step_guard; apply prog_step_guard; inversion Hs; subst; constructor; congruence.
Qed.

Lemma fwd_init_val t e v P :
  〚 e 〛 = v →
  fwd (t ∶ e := |0⟩ ∙ P) (t ∶ v := |0⟩ ∙ P) ∧ fwd (t ∶ v := |0⟩ ∙ P) (t ∶ e := |0⟩ ∙ P).
Proof.
  intros He. assert (Ev : eval_qubit e = eval_qubit v) by (unfold eval_qubit; simpl; by rewrite He).
  split; apply fwd_refl_step; intros s l X Hs%prog_step_guard; apply prog_step_guard; inversion Hs; subst; constructor; congruence.
Qed.

(* *** Contexts *)

Lemma fwd_ite_l e P P' Q : fwd P P' → fwd (If e Then P Else Q) (If e Then P' Else Q).
Proof.
  intros H s l X Hs. inversion Hs as [| |? ? ? ? ? ? He Hp|? ? ? ? ? ? He Hq| | | | | |]; subst.
  - destruct (H _ _ _ Hp) as (Y & Hs' & HY). exists Y. split; [|done]. by apply pr_iteT.
  - exists X. split; [by apply pr_iteF|done].
Qed.

Lemma fwd_ite_r e P Q Q' : fwd Q Q' → fwd (If e Then P Else Q) (If e Then P Else Q').
Proof.
  intros H s l X Hs. inversion Hs as [| |? ? ? ? ? ? He Hp|? ? ? ? ? ? He Hq| | | | | |]; subst.
  - exists X. split; [by apply pr_iteT|done].
  - destruct (H _ _ _ Hq) as (Y & Hs' & HY). exists Y. split; [|done]. by apply pr_iteF.
Qed.

Lemma fwd_par_l P P' Q : P ≡* P' → fwd P P' → fwd (P ∥ Q) (P' ∥ Q).
Proof.
  intros Hc H s l X Hs.
  inversion Hs as [| | | |? ? ? ? P1 HP|? ? ? ? Q1 HQ|? ? t t' c v P1 Q1 HP HQ|? ? t t' c v P1 Q1 HP HQ| |];
    subst.
  - destruct (H _ _ _ HP) as (Y & Hs' & HY). exists (Y ∥ Q). split; [by apply pr_parL|by apply cgr_par].
  - exists (P' ∥ Q1). split; [by apply pr_parR|by apply cgr_par].
  - destruct (H _ _ _ HP) as (Y & Hs' & HY). exists (Y ∥ Q1). split; [by eapply pr_syncL|by apply cgr_par].
  - destruct (H _ _ _ HP) as (Y & Hs' & HY). exists (Y ∥ Q1). split; [by eapply pr_syncR|by apply cgr_par].
Qed.

Lemma fwd_par_r P Q Q' : Q ≡* Q' → fwd Q Q' → fwd (P ∥ Q) (P ∥ Q').
Proof.
  intros Hc H s l X Hs.
  inversion Hs as [| | | |? ? ? ? P1 HP|? ? ? ? Q1 HQ|? ? t t' c v P1 Q1 HP HQ|? ? t t' c v P1 Q1 HP HQ| |];
    subst.
  - exists (P1 ∥ Q'). split; [by apply pr_parL|by apply cgr_par_r].
  - destruct (H _ _ _ HQ) as (Y & Hs' & HY). exists (P ∥ Y). split; [by apply pr_parR|by apply cgr_par_r].
  - destruct (H _ _ _ HQ) as (Y & Hs' & HY). exists (P1 ∥ Y). split; [by eapply pr_syncL|by apply cgr_par_r].
  - destruct (H _ _ _ HQ) as (Y & Hs' & HY). exists (P1 ∥ Y). split; [by eapply pr_syncR|by apply cgr_par_r].
Qed.

Lemma fwd_res P P' : fwd P P' → fwd (ν P) (ν P').
Proof.
  intros H s l X Hs. inversion Hs as [| | | | | | | |? ? ? P1 HP|]; subst.
  destruct (H _ _ _ HP) as (Y & Hs' & HY). exists (ν Y). split; [by apply pr_res|by apply cgr_res].
Qed.

Lemma fwd_rec t P P' : P ≡* P' → fwd (t ∶ rec ∙ P) (t ∶ rec ∙ P').
Proof.
  intros H s l Y Hs. inversion Hs; subst.
  exists (P' ⁅ (t ∶ rec ∙ P')↑ ⁆ₚ). split; [constructor|by apply cgr_unfold].
Qed.

Lemma fwd_pre 𝜆 P P' : P ≡* P' → fwd (𝜆 ∙ P) (𝜆 ∙ P').
Proof.
  intros Hc s l X Hs%prog_step_guard. inversion Hs; subst.
  - exists P'. split; [apply pr_tau|done].
  - exists (P' ⁅ v ⁆ᵥ). split; [apply pr_recv|by apply cgr_subst].
  - exists P'. split; [by apply pr_op|done].
  - exists (P' ⁅ VNat n ⁆ᵥ). split; [by apply pr_meas|by apply cgr_subst].
  - exists P'. split; [by apply pr_init|done].
Qed.

Lemma fwd_sum_l (g g' h : guard) : fwd g g' → fwd (g + h) (g' + h).
Proof.
  intros H s l X Hs%prog_step_guard. inversion Hs as [| | | | |? ? ? ? ? Hg|? ? ? ? ? Hh]; subst.
  - destruct (H _ _ _ (pr_guard _ _ _ _ Hg)) as (Y & Hs' & HY). exists Y. split; [by apply pr_sumL|done].
  - exists X. split; [by apply pr_guard, pg_sumR|done].
Qed.

Lemma fwd_sum_r (g h h' : guard) : fwd h h' → fwd (g + h) (g + h').
Proof.
  intros H s l X Hs%prog_step_guard. inversion Hs as [| | | | |? ? ? ? ? Hg|? ? ? ? ? Hh]; subst.
  - exists X. split; [by apply pr_guard, pg_sumL|done].
  - destruct (H _ _ _ (pr_guard _ _ _ _ Hh)) as (Y & Hs' & HY). exists Y. split; [by apply pr_sumR|done].
Qed.

(* *** The bisimulation *)

Theorem cgr_step_bisim :
  (∀ P Q, P ≡ Q → fwd P Q ∧ fwd Q P) ∧ (∀ g h, g ≡ᵍ h → fwd g h ∧ fwd h g).
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
  ∃ R, P ≡* R ∧ R ⟶ₚ{l}[s] Q.

Definition lts_then_sc (P : proc) (s : choice) (l : Labels prog_action) (Q : proc) : Prop :=
  ∃ R, P ⟶ₚ{l}[s] R ∧ R ≡* Q.

Theorem Congruence_Respects_Transition P s l Q : sc_then_lts P s l Q → lts_then_sc P s l Q.
Proof.
  intros (R & HPR & HR). destruct (cgr_bisim R P (symmetry HPR) s l Q HR) as (Q' & HQ' & HQ).
  exists Q'. split; [done|by symmetry].
Qed.

End LqP.

Arguments cgr {_} (_ _)%_lq.
Arguments gcgr {_} (_ _)%_lq.
Notation "P ≡ Q" := (cgr_step P Q) : lqccs_scope.
Notation "g ≡ᵍ h" := (gcgr_step g h) : lqccs_scope.
Notation "P ≡* Q" := (cgr P Q) (at level 70) : lqccs_scope.
Notation "g ≡ᵍ* h" := (gcgr g h) (at level 70) : lqccs_scope.

(* end hide *)
