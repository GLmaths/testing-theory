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

(* * LTS of lqCCS programs *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base gmultiset countable decidable list sets numbers.
From TestingTheory Require Import ActTau.
From TestingTheory Require Import lqCCS.lqCCS_prog.Syntax lqCCS.Helper.De_Brujin_lemmas lqCCS.General_definition.Parallel_choice_LTS.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

Section Prog_LTS.
  Context `{lqP : lqCCS_Parameters}.

Inductive prog_action : Type :=
| PrOut (c : channel) (v : val)
| PrIn (c : channel) (v : val)
| PrOp (U : unitary) (qs : list qubit)
| PrMeas (M : meas) (qs : list qubit) (n : nat)
| PrReinit (q : qubit).

Notation "c ! v" := (ActExt (PrOut c v)) (at level 30, v at level 9) : lqccs_scope.
Notation "c ? v" := (ActExt (PrIn c v)) (at level 30, v at level 9) : lqccs_scope.
Notation "⦅ qs ⦆ ! U" := (ActExt (PrOp U qs)) (at level 30, U at level 9, format "⦅ qs ⦆  !  U") : lqccs_scope.
Notation "M ⦅ qs ⦆? n" := (ActExt (PrMeas M qs n)) (at level 30, n at level 9, format "M  ⦅ qs ⦆?  n") : lqccs_scope.
Notation "'reinit' q" := (ActExt (PrReinit q)) (at level 30, q at level 9, format "'reinit'  q") : lqccs_scope.

Definition chan_action (μ : prog_action) : Prop :=
  ∃ c v, μ = PrOut c v ∨ μ = PrIn c v.

(* Renaming of the channel of an action. *)
Definition ren_action (f : nat → nat) (μ : prog_action) : prog_action :=
  match μ with
  | PrOut c v => PrOut (ren_chan f c) v
  | PrIn c v => PrIn (ren_chan f c) v
  | _ => μ
  end.

Definition ren_lbl (f : nat → nat) (𝜆 : Labels prog_action) : Labels prog_action :=
  match 𝜆 with ActExt μ => ActExt (ren_action f μ) | τ => τ end.

Reserved Notation "P ⟶ₚ{ 𝜆 }[ k ] P'" (at level 70, format "P  ⟶ₚ{ 𝜆 }[ k ]  P'").
Reserved Notation "g ⟶ᵍ{ 𝜆 }[ k ] P'" (at level 70, format "g  ⟶ᵍ{ 𝜆 }[ k ]  P'").

(* ** Transitions of a program and of a guard *)

Inductive prog_step : prog → choice → Labels prog_action → prog → Prop :=
| pr_guard (g : guard) k 𝜆 P' :
    g ⟶ᵍ{𝜆}[k] P' → g ⟶ₚ{𝜆}[k] P'
| pr_send t c e v :
    〚 e 〛 = v → t ∶ c ! e ⟶ₚ{c ! v}[{[+ t +]}] 𝟘
| pr_iteT e P Q k 𝜆 P' :
    〚 e 〛 = true → P ⟶ₚ{𝜆}[k] P' → If e Then P Else Q ⟶ₚ{𝜆}[k] P'
| pr_iteF e P Q k 𝜆 Q' :
    〚 e 〛 = false → Q ⟶ₚ{𝜆}[k] Q' → If e Then P Else Q ⟶ₚ{𝜆}[k] Q'
| pr_parL P Q k 𝜆 P' :
    P ⟶ₚ{𝜆}[k] P' → P ∥ Q ⟶ₚ{𝜆}[k] (P' ∥ Q)
| pr_parR P Q k 𝜆 Q' :
    Q ⟶ₚ{𝜆}[k] Q' → P ∥ Q ⟶ₚ{𝜆}[k] (P ∥ Q')
| pr_syncL P Q (t t' : tag) c v P' Q' :
    P ⟶ₚ{c ! v}[{[+ t +]}] P' → Q ⟶ₚ{c ? v}[{[+ t' +]}] Q' →
    P ∥ Q ⟶ₚ{τ}[{[+ t; t' +]}] (P' ∥ Q')
| pr_syncR P Q (t t' : tag) c v P' Q' :
    P ⟶ₚ{c ? v}[{[+ t +]}] P' → Q ⟶ₚ{c ! v}[{[+ t' +]}] Q' →
    P ∥ Q ⟶ₚ{τ}[{[+ t; t' +]}] (P' ∥ Q')
| pr_res P k 𝜆 P' :
    P ⟶ₚ{ren_lbl S 𝜆}[k] P' → ν P ⟶ₚ{𝜆}[k] (ν P')
| pr_rec t P :
    t ∶ rec ∙ P ⟶ₚ{τ}[{[+ t +]}] (P ⁅ (t ∶ rec ∙ P)↑ ⁆ₚ)
with prog_gstep : guard → choice → Labels prog_action → prog → Prop :=
| pg_tau t P :
    (t ∶ 𝛕 ∙ P) ⟶ᵍ{τ}[{[+ t +]}] P
| pg_recv t c v P :
    (t ∶ c ? ∙ P) ⟶ᵍ{c ? v}[{[+ t +]}] (P ⁅ v ⁆ᵥ)
| pg_op t U es qs P :
    eval_qubits es = Some qs →
    (t ∶ U ⦅es⦆ ∙ P) ⟶ᵍ{⦅qs⦆ ! U}[{[+ t +]}] P
| pg_meas t M es qs n P :
    eval_qubits es = Some qs →
    (t ∶ M ⦅es ▷⦆ ∙ P) ⟶ᵍ{M ⦅qs⦆? n}[{[+ t +]}] (P ⁅ VNat n ⁆ᵥ)
| pg_init t e q P :
    eval_qubit e = Some q →
    (t ∶ e := |0⟩ ∙ P) ⟶ᵍ{reinit q}[{[+ t +]}] P
| pg_sumL (g1 g2 : guard) k 𝜆 P' :
    g1 ⟶ᵍ{𝜆}[k] P' → (g1 + g2) ⟶ᵍ{𝜆}[k] P'
| pg_sumR (g1 g2 : guard) k 𝜆 P' :
    g2 ⟶ᵍ{𝜆}[k] P' → (g1 + g2) ⟶ᵍ{𝜆}[k] P'
where "P ⟶ₚ{ 𝜆 }[ k ] P'" := (prog_step P k 𝜆 P') : lqccs_scope
and "g ⟶ᵍ{ 𝜆 }[ k ] P'" := (prog_gstep g k 𝜆 P') : lqccs_scope.

Notation "P ↛ₚ{ 𝜆 }[ k ] P'" := (¬ prog_step P k 𝜆 P') (at level 70, format "P  ↛ₚ{ 𝜆 }[ k ]  P'") : lqccs_scope.
Notation "g ↛ᵍ{ 𝜆 }[ k ] P'" := (¬ prog_gstep g k 𝜆 P') (at level 70, format "g  ↛ᵍ{ 𝜆 }[ k ]  P'") : lqccs_scope.

Lemma prog_step_guard (g : guard) k 𝜆 P' : g ⟶ₚ{𝜆}[k] P' ↔ g ⟶ᵍ{𝜆}[k] P'.
Proof. split; [by inversion 1|apply pr_guard]. Qed.

Lemma pr_tau t P : (t ∶ 𝛕 ∙ P) ⟶ₚ{τ}[{[+ t +]}] P.
Proof. apply pr_guard, pg_tau. Qed.

Lemma pr_recv t c v P : (t ∶ c ? ∙ P) ⟶ₚ{c ? v}[{[+ t +]}] (P ⁅ v ⁆ᵥ).
Proof. apply pr_guard, pg_recv. Qed.

Lemma pr_op t U es qs P : eval_qubits es = Some qs → (t ∶ U ⦅es⦆ ∙ P) ⟶ₚ{⦅qs⦆ ! U}[{[+ t +]}] P.
Proof. intros H. by apply pr_guard, pg_op. Qed.

Lemma pr_meas t M es qs n P :
  eval_qubits es = Some qs → (t ∶ M ⦅es ▷⦆ ∙ P) ⟶ₚ{M ⦅qs⦆? n}[{[+ t +]}] (P ⁅ VNat n ⁆ᵥ).
Proof. intros H. by apply pr_guard, pg_meas. Qed.

Lemma pr_init t e q P : eval_qubit e = Some q → (t ∶ e := |0⟩ ∙ P) ⟶ₚ{reinit q}[{[+ t +]}] P.
Proof. intros H. by apply pr_guard, pg_init. Qed.

Lemma pr_sumL (g1 g2 : guard) k 𝜆 P' : g1 ⟶ₚ{𝜆}[k] P' → (g1 + g2) ⟶ₚ{𝜆}[k] P'.
Proof. intros H%prog_step_guard. by apply pr_guard, pg_sumL. Qed.

Lemma pr_sumR (g1 g2 : guard) k 𝜆 P' : g2 ⟶ₚ{𝜆}[k] P' → (g1 + g2) ⟶ₚ{𝜆}[k] P'.
Proof. intros H%prog_step_guard. by apply pr_guard, pg_sumR. Qed.

(* ** Facts on the program LTS *)

Lemma prog_gstep_not_out (g : guard) k c v P' : g ↛ₚ{c ! v}[k] P'.
Proof.
  intros Hs%prog_step_guard. remember (c ! v) as 𝜆 eqn:El. induction Hs; simplify_eq; auto.
Qed.

Lemma prog_gstep_tag g k 𝜆 P' : g ⟶ᵍ{𝜆}[k] P' → ∃ t, k = {[+ t +]}.
Proof. induction 1; eauto. Qed.

Lemma prog_step_ext_choice P k μ P' : P ⟶ₚ{ActExt μ}[k] P' → ∃ t, k = {[+ t +]}.
Proof.
  intros Hs. remember (ActExt μ) as 𝜆 eqn:El. revert μ El.
  induction Hs as [g k 𝜆 P' Hg| | | | | | | | |]; intros μ0 El; simplify_eq; eauto using prog_gstep_tag.
Qed.

End Prog_LTS.

Notation "c ! v" := (ActExt (PrOut c v)) (at level 30, v at level 9) : lqccs_scope.
Notation "c ? v" := (ActExt (PrIn c v)) (at level 30, v at level 9) : lqccs_scope.
Notation "⦅ qs ⦆ ! U" := (ActExt (PrOp U qs)) (at level 30, U at level 9, format "⦅ qs ⦆  !  U") : lqccs_scope.
Notation "M ⦅ qs ⦆? n" := (ActExt (PrMeas M qs n)) (at level 30, n at level 9, format "M  ⦅ qs ⦆?  n") : lqccs_scope.
Notation "'reinit' q" := (ActExt (PrReinit q)) (at level 30, q at level 9, format "'reinit'  q") : lqccs_scope.
Reserved Notation "P ⟶ₚ{ 𝜆 }[ k ] P'" (at level 70, format "P  ⟶ₚ{ 𝜆 }[ k ]  P'").
Reserved Notation "g ⟶ᵍ{ 𝜆 }[ k ] P'" (at level 70, format "g  ⟶ᵍ{ 𝜆 }[ k ]  P'").
Notation "g ⟶ᵍ{ 𝜆 }[ k ] P'" := (prog_gstep g k 𝜆 P') : lqccs_scope.
Notation "P ⟶ₚ{ 𝜆 }[ k ] P'" := (prog_step P k 𝜆 P') : lqccs_scope.
Notation "P ↛ₚ{ 𝜆 }[ k ] P'" := (¬ prog_step P k 𝜆 P') (at level 70, format "P  ↛ₚ{ 𝜆 }[ k ]  P'") : lqccs_scope.
Notation "g ↛ᵍ{ 𝜆 }[ k ] P'" := (¬ prog_gstep g k 𝜆 P') (at level 70, format "g  ↛ᵍ{ 𝜆 }[ k ]  P'") : lqccs_scope.
