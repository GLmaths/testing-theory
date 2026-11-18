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

    A transition after [≡*] is a transition followed by [≡*], with the
    same choices ([Congruence_Respects_Transition]). *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base gmultiset countable decidable list sets relations.
From TestingTheory Require Import ActTau.
From TestingTheory Require Import lqCCS.quantum_mem.Algebra lqCCS.quantum_mem.Syntax.
From TestingTheory Require Import lqCCS.lqCCS_prog.Syntax lqCCS.Helper_substitution.De_Brujin_lemmas lqCCS.General_definition.Parallel_choice_LTS lqCCS.quantum_mem.LTS lqCCS.lqCCS_prog.LTS lqCCS.lqCCS_par_Qmem.LTS lqCCS.lqCCS_process.LTS.LTS lqCCS.Helper_substitution.Label_lemmas.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

(* ** One step of congruence *)

Reserved Notation "P ≡ Q" (at level 70, no associativity).
Reserved Notation "g ≡ᵍ h" (at level 70, no associativity).

Section LqP.
  Context `{LP : lqCCS_Parameters}.

Inductive cgr_step : proc → proc → Prop :=
| cgr_par_nil_step P : (P ∥ 𝟘) ≡ P
| cgr_par_nil_rev_step P : P ≡ (P ∥ 𝟘)
| cgr_par_com_step P Q : (P ∥ Q) ≡ (Q ∥ P)
| cgr_par_assoc_rev_step P Q R : (P ∥ (Q ∥ R)) ≡ ((P ∥ Q) ∥ R)
| cgr_par_assoc_step P Q R : ((P ∥ Q) ∥ R) ≡ (P ∥ (Q ∥ R))
| cgr_if_true_step e P Q : 〚 e 〛 = true → (If e Then P Else Q) ≡ P
| cgr_if_true_rev_step e P Q : 〚 e 〛 = true → P ≡ (If e Then P Else Q)
| cgr_if_false_step e P Q : 〚 e 〛 = false → (If e Then P Else Q) ≡ Q
| cgr_if_false_rev_step e P Q : 〚 e 〛 = false → Q ≡ (If e Then P Else Q)
| cgr_send_val_step t c e v : 〚 e 〛 = v → (t ∶ c ! e) ≡ (t ∶ c ! v)
| cgr_send_val_rev_step t c e v : 〚 e 〛 = v → (t ∶ c ! v) ≡ (t ∶ c ! e)
| cgr_if_val_step e v P Q : 〚 e 〛 = v → (If e Then P Else Q) ≡ (If v Then P Else Q)
| cgr_if_val_rev_step e v P Q : 〚 e 〛 = v → (If v Then P Else Q) ≡ (If e Then P Else Q)
| cgr_res_nil_step es : (ν 𝟘{es}) ≡ 𝟘{es}
| cgr_res_nil_rev_step es : 𝟘{es} ≡ (ν 𝟘{es})
| cgr_res_swap_step P : (ν ν P) ≡ (ν ν (ren swap01 P))
| cgr_res_swap_rev_step P : (ν ν (ren swap01 P)) ≡ (ν ν P)
| cgr_res_scope_rev_step P Q : ((ν P) ∥ Q) ≡ (ν (P ∥ ren S Q))
| cgr_res_scope_step P Q : (ν (P ∥ ren S Q)) ≡ ((ν P) ∥ Q)
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
| cgr_choice_nil_rev_step g es : g ≡ᵍ (g + 𝟘{es})
| cgr_choice_com_step g h : (g + h) ≡ᵍ (h + g)
| cgr_choice_assoc_rev_step g h k : (g + (h + k)) ≡ᵍ ((g + h) + k)
| cgr_choice_assoc_step g h k : ((g + h) + k) ≡ᵍ (g + (h + k))
| cgr_nil_val_step es1 e v es2 :
    〚 e 〛 = v → 𝟘{es1 ++ e :: es2} ≡ᵍ 𝟘{es1 ++ EVal v :: es2}
| cgr_nil_val_rev_step es1 e v es2 :
    〚 e 〛 = v → 𝟘{es1 ++ EVal v :: es2} ≡ᵍ 𝟘{es1 ++ e :: es2}
| cgr_op_val_step t U es1 e v es2 P :
    〚 e 〛 = v → (t ∶ U ⦅es1 ++ e :: es2⦆ ∙ P) ≡ᵍ (t ∶ U ⦅es1 ++ EVal v :: es2⦆ ∙ P)
| cgr_op_val_rev_step t U es1 e v es2 P :
    〚 e 〛 = v → (t ∶ U ⦅es1 ++ EVal v :: es2⦆ ∙ P) ≡ᵍ (t ∶ U ⦅es1 ++ e :: es2⦆ ∙ P)
| cgr_meas_val_step t M es1 e v es2 P :
    〚 e 〛 = v → (t ∶ M ⦅es1 ++ e :: es2 ▷⦆ ∙ P) ≡ᵍ (t ∶ M ⦅es1 ++ EVal v :: es2 ▷⦆ ∙ P)
| cgr_meas_val_rev_step t M es1 e v es2 P :
    〚 e 〛 = v → (t ∶ M ⦅es1 ++ EVal v :: es2 ▷⦆ ∙ P) ≡ᵍ (t ∶ M ⦅es1 ++ e :: es2 ▷⦆ ∙ P)
| cgr_init_val_step t e v P :
    〚 e 〛 = v → (t ∶ e := |0⟩ ∙ P) ≡ᵍ (t ∶ v := |0⟩ ∙ P)
| cgr_init_val_rev_step t e v P :
    〚 e 〛 = v → (t ∶ v := |0⟩ ∙ P) ≡ᵍ (t ∶ e := |0⟩ ∙ P)
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

Definition cgr : relation proc := rtc cgr_step.
Definition gcgr : relation guard := rtc gcgr_step.
Arguments cgr (_ _)%_lq.
Arguments gcgr (_ _)%_lq.

Notation "P ≡* Q" := (cgr P Q) (at level 70) : lqccs_scope.
Notation "g ≡ᵍ* h" := (gcgr g h) (at level 70) : lqccs_scope.

Lemma cgr_step_sym : (∀ P Q, P ≡ Q → Q ≡ P) ∧ (∀ g h, g ≡ᵍ h → h ≡ᵍ g).
Proof. apply cgr_gcgr_step_ind; intros; by constructor. Qed.

#[global] Instance cgr_equivalence : Equivalence cgr.
Proof. apply rtc_equivalence. intros P Q. apply cgr_step_sym. Qed.

#[global] Instance gcgr_equivalence : Equivalence gcgr.
Proof. apply rtc_equivalence. intros g h. apply cgr_step_sym. Qed.

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
Proof. apply rtc_once. Qed.

Lemma gcgr_of_step g h : g ≡ᵍ h → g ≡ᵍ* h.
Proof. apply rtc_once. Qed.

(* ** The rules, as congruences *)

Lemma cgr_par_nil P : P ∥ 𝟘 ≡* P.
Proof. apply cgr_of_step, cgr_par_nil_step. Qed.

Lemma cgr_par_nil_rev P : P ≡* P ∥ 𝟘.
Proof. apply rtc_once, cgr_par_nil_rev_step. Qed.

Lemma cgr_par_com P Q : P ∥ Q ≡* Q ∥ P.
Proof. apply cgr_of_step, cgr_par_com_step. Qed.

Lemma cgr_par_assoc P Q R : (P ∥ Q) ∥ R ≡* P ∥ (Q ∥ R).
Proof. apply rtc_once, cgr_par_assoc_step. Qed.

Lemma cgr_par_assoc_rev P Q R : P ∥ (Q ∥ R) ≡* (P ∥ Q) ∥ R.
Proof. apply cgr_of_step, cgr_par_assoc_rev_step. Qed.

Lemma cgr_if_true e P Q : 〚 e 〛 = true → If e Then P Else Q ≡* P.
Proof. intros. by apply cgr_of_step, cgr_if_true_step. Qed.

Lemma cgr_if_true_rev e P Q : 〚 e 〛 = true → P ≡* If e Then P Else Q.
Proof. intros. by apply rtc_once, cgr_if_true_rev_step. Qed.

Lemma cgr_if_false e P Q : 〚 e 〛 = false → If e Then P Else Q ≡* Q.
Proof. intros. by apply cgr_of_step, cgr_if_false_step. Qed.

Lemma cgr_if_false_rev e P Q : 〚 e 〛 = false → Q ≡* If e Then P Else Q.
Proof. intros. by apply rtc_once, cgr_if_false_rev_step. Qed.

Lemma cgr_res_nil es : (ν 𝟘{es}) ≡* 𝟘{es}.
Proof. apply cgr_of_step, cgr_res_nil_step. Qed.

Lemma cgr_res_nil_rev es : 𝟘{es} ≡* (ν 𝟘{es}).
Proof. apply rtc_once, cgr_res_nil_rev_step. Qed.

Lemma cgr_res_swap P : (ν ν P) ≡* (ν ν (ren swap01 P)).
Proof. apply cgr_of_step, cgr_res_swap_step. Qed.

Lemma cgr_res_swap_rev P : (ν ν (ren swap01 P)) ≡* (ν ν P).
Proof. apply rtc_once, cgr_res_swap_rev_step. Qed.

Lemma cgr_res_scope P Q : (ν (P ∥ ren S Q)) ≡* (ν P) ∥ Q.
Proof. apply rtc_once, cgr_res_scope_step. Qed.

Lemma cgr_res_scope_rev P Q : (ν P) ∥ Q ≡* (ν (P ∥ ren S Q)).
Proof. apply cgr_of_step, cgr_res_scope_rev_step. Qed.

Lemma gcgr_choice_nil g es : (g + 𝟘{es}) ≡ᵍ* g.
Proof. apply gcgr_of_step, cgr_choice_nil_step. Qed.

Lemma gcgr_choice_nil_rev g es : g ≡ᵍ* (g + 𝟘{es}).
Proof. apply rtc_once, cgr_choice_nil_rev_step. Qed.

Lemma gcgr_choice_com g h : (g + h) ≡ᵍ* (h + g).
Proof. apply gcgr_of_step, cgr_choice_com_step. Qed.

Lemma gcgr_choice_assoc g h k : ((g + h) + k) ≡ᵍ* (g + (h + k)).
Proof. apply rtc_once, cgr_choice_assoc_step. Qed.

Lemma gcgr_choice_assoc_rev g h k : (g + (h + k)) ≡ᵍ* ((g + h) + k).
Proof. apply gcgr_of_step, cgr_choice_assoc_rev_step. Qed.

(* ** Congruence under contexts *)

Lemma cgr_ctx (f : proc → proc) :
  (∀ P Q, P ≡ Q → (f P) ≡ (f Q)) → ∀ P Q, P ≡* Q → f P ≡* f Q.
Proof.
  intros Hf P Q. induction 1 as [P|P Q R HPQ _ IH]; [done|].
  etrans; [|exact IH]. apply rtc_once. by apply Hf.
Qed.

Lemma gcgr_ctx (f : guard → guard) :
  (∀ g h, g ≡ᵍ h → (f g) ≡ᵍ (f h)) → ∀ g h, g ≡ᵍ* h → (f g) ≡ᵍ* (f h).
Proof.
  intros Hf g h. induction 1 as [g|g h k Hgh _ IH]; [done|].
  etrans; [|exact IH]. apply rtc_once. by apply Hf.
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
  induction 1 as [g|g h k Hgh _ IH]; [done|].
  etrans; [|exact IH]. apply rtc_once. by constructor.
Qed.

Lemma gcgr_prefix 𝜆 P P' : P ≡* P' → (𝜆 ∙ P) ≡ᵍ* (𝜆 ∙ P').
Proof.
  induction 1 as [P|P Q R HPQ _ IH]; [done|].
  etrans; [|exact IH]. apply rtc_once. by constructor.
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
  all: first [rewrite ren_lift_lift_swap01 | rewrite ren_lift_S]; by constructor.
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
  all: try (rewrite <- (proj1 ren_pr_subst); by constructor).
  all: replace ((ren swap01 P) ⁅ ren S (ren S Q) // k ⁆ₚ) with (ren swap01 (P ⁅ ren S (ren S Q) // k ⁆ₚ))
    by (rewrite (proj1 ren_pr_subst); by rewrite ren_swap01_SS); by constructor.
Qed.

Lemma cgr_pr_subst_l P P' k Q : P ≡* P' → P ⁅ Q // k ⁆ₚ ≡* P' ⁅ Q // k ⁆ₚ.
Proof. apply (cgr_ctx (λ P, P ⁅ Q // k ⁆ₚ)). intros. by apply cgr_step_pr_subst_l. Qed.

Lemma cgr_step_rshift :
  (∀ P P', P ≡ P' → ∀ k, (rshift k P) ≡ (rshift k P'))
  ∧ (∀ g g', g ≡ᵍ g' → ∀ k, (grshift k g) ≡ᵍ (grshift k g')).
Proof.
  apply cgr_gcgr_step_ind; simpl; intros; try (constructor; done); try (by constructor; apply H).
  all: rewrite <- (proj1 ren_rshift); by constructor.
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
  all: rewrite (proj1 tren_ren); by constructor.
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

(* ** Congruence respects transitions, as in VACCS *)

Definition sc_then_lts (P : proc) (s : choice) (l : Labels prog_action) (Q : proc) : Prop :=
  ∃ R, P ≡* R ∧ R ⟶ₚ{l}[s] Q.

Definition lts_then_sc (P : proc) (s : choice) (l : Labels prog_action) (Q : proc) : Prop :=
  ∃ R, P ⟶ₚ{l}[s] R ∧ R ≡* Q.

Notation "P ≡* . ⟶ₚ{ l }[ s ] Q" := (sc_then_lts P s l Q) (at level 70, format "P  ≡*  .  ⟶ₚ{ l }[ s ]  Q") : lqccs_scope.
Notation "P ⟶ₚ{ l }[ s ] . ≡* Q" := (lts_then_sc P s l Q) (at level 70, format "P  ⟶ₚ{ l }[ s ]  .  ≡*  Q") : lqccs_scope.

Theorem Congruence_Respects_Transition : ∀ P s l Q, P ≡* . ⟶ₚ{l}[s] Q → P ⟶ₚ{l}[s] . ≡* Q.
Proof.
  intros P s l Q (R & HPR & HR). symmetry in HPR. revert Q HR.
  induction HPR as [R0|R0 R1 P0 H1 _ IH]; intros Q HR; [by exists Q|].
  assert (∃ Q1, R1 ⟶ₚ{l}[s] Q1 ∧ Q ≡* Q1) as (Q1 & HQ1 & E1).
  { clear IH. revert s l Q HR. induction H1 as [P|P|P Q|P Q R|P Q R|e P Q He|e P Q He|e P Q He|e P Q He|t c e v He|t c e v He|e v P Q He|e v P Q He|es|es|P|P|P Q|P Q|e P P' Q _ IH|e P Q Q' _ IH|P P' Q H IH|P Q Q' H IH|P P' _ IH|t P P' H _|g g' H].
    (* [P ∥ 𝟘 ≡ P] *)
    - intros s l X Hs. inversion Hs as [| | | |? ? ? ? P' HP| | | | |]; subst;
        try (exfalso; by eapply pstep_nil).
      exists P'. split; [done|]. apply cgr_par_nil.
    - intros s l P' Hs. exists (P' ∥ 𝟘). split; [by apply pr_parL|]. apply cgr_par_nil_rev.
    (* [P ∥ Q ≡ Q ∥ P] *)
    - intros s l X Hs.
      inversion Hs as [| | | |? ? ? ? P' HP|? ? ? ? Q' HQ|? ? t t' c v P' Q' HP HQ|? ? t t' c v P' Q' HP HQ| |];
        subst.
      + exists (Q ∥ P'). split; [by apply pr_parR|]. apply cgr_par_com.
      + exists (Q' ∥ P). split; [by apply pr_parL|]. apply cgr_par_com.
      + exists (Q' ∥ P'). split; [rewrite (comm disj_union {[+ t +]}); by eapply pr_syncR|]. apply cgr_par_com.
      + exists (Q' ∥ P'). split; [rewrite (comm disj_union {[+ t +]}); by eapply pr_syncL|]. apply cgr_par_com.
    (* [P ∥ (Q ∥ R) ≡ (P ∥ Q) ∥ R] *)
    - intros s l X Hs.
      inversion Hs as [| | | |? ? ? ? P' HP|? ? ? ? X' HX|? ? t t' c v P' X' HP HX|? ? t t' c v P' X' HP HX| |];
        subst.
      + exists ((P' ∥ Q) ∥ R). split; [by do 2 apply pr_parL|]. apply cgr_par_assoc_rev.
      + inversion HX as [| | | |? ? ? ? Q' HQ|? ? ? ? R' HR|? ? t t' c v Q' R' HQ HR|? ? t t' c v Q' R' HQ HR| |];
          subst.
        * exists ((P ∥ Q') ∥ R). split; [by apply pr_parL, pr_parR|]. apply cgr_par_assoc_rev.
        * exists ((P ∥ Q) ∥ R'). split; [by apply pr_parR|]. apply cgr_par_assoc_rev.
        * exists ((P ∥ Q') ∥ R'). split; [eapply pr_syncL; [by apply pr_parR|done]|]. apply cgr_par_assoc_rev.
        * exists ((P ∥ Q') ∥ R'). split; [eapply pr_syncR; [by apply pr_parR|done]|]. apply cgr_par_assoc_rev.
      + inversion HX as [| | | |? ? ? ? Q' HQ|? ? ? ? R' HR| | | |]; subst.
        * exists ((P' ∥ Q') ∥ R). split; [apply pr_parL; by eapply pr_syncL|]. apply cgr_par_assoc_rev.
        * exists ((P' ∥ Q) ∥ R'). split; [eapply pr_syncL; [by apply pr_parL|done]|]. apply cgr_par_assoc_rev.
      + inversion HX as [| | | |? ? ? ? Q' HQ|? ? ? ? R' HR| | | |]; subst.
        * exists ((P' ∥ Q') ∥ R). split; [apply pr_parL; by eapply pr_syncR|]. apply cgr_par_assoc_rev.
        * exists ((P' ∥ Q) ∥ R'). split; [eapply pr_syncR; [by apply pr_parL|done]|]. apply cgr_par_assoc_rev.
    (* [(P ∥ Q) ∥ R ≡ P ∥ (Q ∥ R)] *)
    - intros s l X Hs.
      inversion Hs as [| | | |? ? ? ? X' HX|? ? ? ? R' HR|? ? t t' c v X' R' HX HR|? ? t t' c v X' R' HX HR| |];
        subst.
      + inversion HX as [| | | |? ? ? ? P' HP|? ? ? ? Q' HQ|? ? t t' c v P' Q' HP HQ|? ? t t' c v P' Q' HP HQ| |];
          subst.
        * exists (P' ∥ (Q ∥ R)). split; [by apply pr_parL|]. apply cgr_par_assoc.
        * exists (P ∥ (Q' ∥ R)). split; [by apply pr_parR, pr_parL|]. apply cgr_par_assoc.
        * exists (P' ∥ (Q' ∥ R)). split; [eapply pr_syncL; [done|by apply pr_parL]|]. apply cgr_par_assoc.
        * exists (P' ∥ (Q' ∥ R)). split; [eapply pr_syncR; [done|by apply pr_parL]|]. apply cgr_par_assoc.
      + exists (P ∥ (Q ∥ R')). split; [by do 2 apply pr_parR|]. apply cgr_par_assoc.
      + inversion HX as [| | | |? ? ? ? P' HP|? ? ? ? Q' HQ| | | |]; subst.
        * exists (P' ∥ (Q ∥ R')). split; [eapply pr_syncL; [done|by apply pr_parR]|]. apply cgr_par_assoc.
        * exists (P ∥ (Q' ∥ R')). split; [apply pr_parR; by eapply pr_syncL|]. apply cgr_par_assoc.
      + inversion HX as [| | | |? ? ? ? P' HP|? ? ? ? Q' HQ| | | |]; subst.
        * exists (P' ∥ (Q ∥ R')). split; [eapply pr_syncR; [done|by apply pr_parR]|]. apply cgr_par_assoc.
        * exists (P ∥ (Q' ∥ R')). split; [apply pr_parR; by eapply pr_syncR|]. apply cgr_par_assoc.
    (* [If e Then P Else Q ≡ P] when [e] is true *)
    - intros s l P' Hs. exists P'. split; [|done]. inversion Hs; subst; [done|congruence].
    - intros s l P' Hs. exists P'. split; [by apply pr_iteT|done].
    (* [If e Then P Else Q ≡ Q] when [e] is false *)
    - intros s l P' Hs. exists P'. split; [|done]. inversion Hs; subst; [congruence|done].
    - intros s l P' Hs. exists P'. split; [by apply pr_iteF|done].
    (* evaluation in an output *)
    - intros s l P' Hs. exists P'. split; [|done].
      inversion Hs; subst; constructor; simpl in *; congruence.
    - intros s l P' Hs. exists P'. split; [|done].
      inversion Hs; subst; constructor; simpl in *; congruence.
    (* evaluation in a conditional *)
    - intros s l P' Hs. exists P'. split; [|done].
      inversion Hs; subst; [apply pr_iteT|apply pr_iteF]; simpl in *; congruence.
    - intros s l P' Hs. exists P'. split; [|done].
      inversion Hs; subst; [apply pr_iteT|apply pr_iteF]; simpl in *; congruence.
    (* [ν 𝟘 ≡ 𝟘] *)
    - intros s l P' Hs. inversion Hs; subst. exfalso. by eapply pstep_nil.
    - intros s l P' Hs. exfalso. by eapply pstep_nil.
    (* [ν ν P ≡ ν ν (swap P)] *)
    - intros s l X Hs. inversion Hs as [| | | | | | | |? ? ? Y HY|]; subst.
      inversion HY as [| | | | | | | |? ? ? P' HP|]; subst.
      pose proof (prog_step_ren swap01 _ _ _ _ HP) as HP'. rewrite ren_lbl_swap01_SS in HP'.
      exists (ν ν (ren swap01 P')). split; [by do 2 apply pr_res|]. apply cgr_res_swap.
    - intros s l X Hs. inversion Hs as [| | | | | | | |? ? ? Y HY|]; subst.
      inversion HY as [| | | | | | | |? ? ? P' HP|]; subst.
      pose proof (prog_step_ren swap01 _ _ _ _ HP) as HP'.
      rewrite ren_lbl_swap01_SS, ren_swap01_invol in HP'.
      exists (ν ν (ren swap01 P')). split; [by do 2 apply pr_res|]. apply cgr_res_swap.
    (* [(ν P) ∥ Q ≡ ν (P ∥ Q⁺)] *)
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
      + exists ((ν P') ∥ Q). split; [by apply pr_parL, pr_res|]. apply cgr_res_scope.
      + destruct (prog_step_ren_inv S S_inj_fun _ _ _ _ HQ) as (l0 & Q' & El & -> & HQ0).
        apply ren_lbl_inj in El as ->; [|exact S_inj_fun].
        exists ((ν P) ∥ Q'). split; [by apply pr_parR|]. apply cgr_res_scope.
      + destruct l; simpl in *; simplify_eq.
        destruct (prog_step_ren_inv S S_inj_fun _ _ _ _ HQ) as (l0 & Q' & El & -> & HQ0).
        destruct l0 as [[c0 v0|c0 v0| | |]|]; simpl in El; simplify_eq.
        exists ((ν P') ∥ Q'). split; [|apply cgr_res_scope].
        eapply pr_syncL; [|exact HQ0]. by apply pr_res.
      + destruct l; simpl in *; simplify_eq.
        destruct (prog_step_ren_inv S S_inj_fun _ _ _ _ HQ) as (l0 & Q' & El & -> & HQ0).
        destruct l0 as [[c0 v0|c0 v0| | |]|]; simpl in El; simplify_eq.
        exists ((ν P') ∥ Q'). split; [|apply cgr_res_scope].
        eapply pr_syncR; [|exact HQ0]. by apply pr_res.
    (* contexts *)
    - intros s l X Hs. inversion Hs as [| |? ? ? ? ? ? He Hp|? ? ? ? ? ? He Hq| | | | | |]; subst.
      + destruct (IH _ _ _ Hp) as (Y & Hs' & HY). exists Y. split; [|done]. by apply pr_iteT.
      + exists X. split; [by apply pr_iteF|done].
    - intros s l X Hs. inversion Hs as [| |? ? ? ? ? ? He Hp|? ? ? ? ? ? He Hq| | | | | |]; subst.
      + exists X. split; [by apply pr_iteT|done].
      + destruct (IH _ _ _ Hq) as (Y & Hs' & HY). exists Y. split; [|done]. by apply pr_iteF.
    - intros s l X Hs.
      inversion Hs as [| | | |? ? ? ? P1 HP|? ? ? ? Q1 HQ|? ? t t' c v P1 Q1 HP HQ|? ? t t' c v P1 Q1 HP HQ| |];
        subst.
      + destruct (IH _ _ _ HP) as (Y & Hs' & HY). exists (Y ∥ Q). split; [by apply pr_parL|by apply cgr_par].
      + exists (P' ∥ Q1). split; [by apply pr_parR|by apply cgr_par, cgr_of_step].
      + destruct (IH _ _ _ HP) as (Y & Hs' & HY). exists (Y ∥ Q1). split; [by eapply pr_syncL|by apply cgr_par].
      + destruct (IH _ _ _ HP) as (Y & Hs' & HY). exists (Y ∥ Q1). split; [by eapply pr_syncR|by apply cgr_par].
    - intros s l X Hs.
      inversion Hs as [| | | |? ? ? ? P1 HP|? ? ? ? Q1 HQ|? ? t t' c v P1 Q1 HP HQ|? ? t t' c v P1 Q1 HP HQ| |];
        subst.
      + exists (P1 ∥ Q'). split; [by apply pr_parL|by apply cgr_par_r, cgr_of_step].
      + destruct (IH _ _ _ HQ) as (Y & Hs' & HY). exists (P ∥ Y). split; [by apply pr_parR|by apply cgr_par_r].
      + destruct (IH _ _ _ HQ) as (Y & Hs' & HY). exists (P1 ∥ Y). split; [by eapply pr_syncL|by apply cgr_par_r].
      + destruct (IH _ _ _ HQ) as (Y & Hs' & HY). exists (P1 ∥ Y). split; [by eapply pr_syncR|by apply cgr_par_r].
    - intros s l X Hs. inversion Hs as [| | | | | | | |? ? ? P1 HP|]; subst.
      destruct (IH _ _ _ HP) as (Y & Hs' & HY). exists (ν Y). split; [by apply pr_res|by apply cgr_res].
    - intros s l Y Hs. inversion Hs; subst.
      exists (P' ⁅ (t ∶ rec ∙ P')↑ ⁆ₚ). split; [constructor|by apply cgr_unfold, cgr_of_step].
    - induction H as [g es|g es|g h|g h k|g h k|es1 e v es2 _|es1 e v es2 _|t U es1 e v es2 P He|t U es1 e v es2 P He|t M es1 e v es2 P He|t M es1 e v es2 P He|t e v P He|t e v P He|𝜆 P P' H|g g' h _ IH|g h h' _ IH].
      (* [g + 𝟘 ≡ g] *)
      + intros s l P' Hs. exists P'. split; [|done].
        apply prog_step_guard in Hs. inversion Hs; subst; [by apply pr_guard|exfalso; by eapply pstep_nil, pr_guard].
      + intros s l P' Hs. exists P'. split; [by apply pr_sumL|done].
      (* [g + h ≡ h + g] *)
      + intros s l P' Hs%prog_step_guard. exists P'. split; [|done]. apply prog_step_guard.
        inversion Hs; subst; [by apply pg_sumR|by apply pg_sumL].
      (* [g + (h + k) ≡ (g + h) + k] *)
      + intros s l P' Hs%prog_step_guard. exists P'. split; [|done]. apply prog_step_guard.
        inversion Hs as [| | | | |? ? ? ? ? H1|? ? ? ? ? H2]; subst.
        * by do 2 apply pg_sumL.
        * inversion H2; subst; [by apply pg_sumL, pg_sumR|by apply pg_sumR].
      + intros s l P' Hs%prog_step_guard. exists P'. split; [|done]. apply prog_step_guard.
        inversion Hs as [| | | | |? ? ? ? ? H1|? ? ? ? ? H2]; subst.
        * inversion H1; subst; [by apply pg_sumL|by apply pg_sumR, pg_sumL].
        * by do 2 apply pg_sumR.
      (* evaluation in the prefixes *)
      + intros s l P' Hs. exfalso. by eapply pstep_nil.
      + intros s l P' Hs. exfalso. by eapply pstep_nil.
      + pose proof (eval_qubits_val es1 e v es2 He) as Ev.
        intros s l X Hs%prog_step_guard. exists X. split; [|done]. apply prog_step_guard.
        inversion Hs; subst; constructor; congruence.
      + pose proof (eval_qubits_val es1 e v es2 He) as Ev.
        intros s l X Hs%prog_step_guard. exists X. split; [|done]. apply prog_step_guard.
        inversion Hs; subst; constructor; congruence.
      + pose proof (eval_qubits_val es1 e v es2 He) as Ev.
        intros s l X Hs%prog_step_guard. exists X. split; [|done]. apply prog_step_guard.
        inversion Hs; subst; constructor; congruence.
      + pose proof (eval_qubits_val es1 e v es2 He) as Ev.
        intros s l X Hs%prog_step_guard. exists X. split; [|done]. apply prog_step_guard.
        inversion Hs; subst; constructor; congruence.
      + assert (Ev : eval_qubit e = eval_qubit v) by (unfold eval_qubit; simpl; by rewrite He).
        intros s l X Hs%prog_step_guard. exists X. split; [|done]. apply prog_step_guard.
        inversion Hs; subst; constructor; congruence.
      + assert (Ev : eval_qubit e = eval_qubit v) by (unfold eval_qubit; simpl; by rewrite He).
        intros s l X Hs%prog_step_guard. exists X. split; [|done]. apply prog_step_guard.
        inversion Hs; subst; constructor; congruence.
      (* contexts *)
      + intros s l X Hs%prog_step_guard. pose proof (cgr_of_step _ _ H) as Hc. inversion Hs; subst.
        * exists P'. split; [apply pr_tau|done].
        * exists (P' ⁅ v ⁆ᵥ). split; [apply pr_recv|by apply cgr_subst].
        * exists P'. split; [by apply pr_op|done].
        * exists (P' ⁅ VNat n ⁆ᵥ). split; [by apply pr_meas|by apply cgr_subst].
        * exists P'. split; [by apply pr_init|done].
      + intros s l X Hs%prog_step_guard. inversion Hs as [| | | | |? ? ? ? ? Hg|? ? ? ? ? Hh]; subst.
        * destruct (IH _ _ _ (pr_guard _ _ _ _ Hg)) as (Y & Hs' & HY). exists Y. split; [by apply pr_sumL|done].
        * exists X. split; [by apply pr_guard, pg_sumR|done].
      + intros s l X Hs%prog_step_guard. inversion Hs as [| | | | |? ? ? ? ? Hg|? ? ? ? ? Hh]; subst.
        * exists X. split; [by apply pr_guard, pg_sumL|done].
        * destruct (IH _ _ _ (pr_guard _ _ _ _ Hh)) as (Y & Hs' & HY). exists Y. split; [by apply pr_sumR|done]. }
  destruct (IH _ HQ1) as (Q2 & HQ2 & E2). exists Q2. split; [done|]. etrans; [exact E2|by symmetry].
Qed.

End LqP.

Arguments cgr {_} (_ _)%_lq.
Arguments gcgr {_} (_ _)%_lq.
Notation "P ≡ Q" := (cgr_step P Q) : lqccs_scope.
Notation "g ≡ᵍ h" := (gcgr_step g h) : lqccs_scope.
Notation "P ≡* Q" := (cgr P Q) (at level 70) : lqccs_scope.
Notation "g ≡ᵍ* h" := (gcgr g h) (at level 70) : lqccs_scope.
Notation "P ≡* . ⟶ₚ{ l }[ s ] Q" := (sc_then_lts P s l Q) (at level 70, format "P  ≡*  .  ⟶ₚ{ l }[ s ]  Q") : lqccs_scope.
Notation "P ⟶ₚ{ l }[ s ] . ≡* Q" := (lts_then_sc P s l Q) (at level 70, format "P  ⟶ₚ{ l }[ s ]  .  ≡*  Q") : lqccs_scope.

(* end hide *)
