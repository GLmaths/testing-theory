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

(* * The LTS of lqCCS processes [⟨ρ, P⟩] *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base gmultiset countable decidable list sets numbers.
From TestingTheory Require Import ActTau.
From TestingTheory Require Import lqCCS.General_definition.Algebra lqCCS.quantum_mem.Syntax.
From TestingTheory Require Import lqCCS.lqCCS_prog.Syntax lqCCS.Helper.De_Brujin_lemmas lqCCS.General_definition.Parallel_choice_LTS.
From TestingTheory Require Import lqCCS.quantum_mem.LTS lqCCS.lqCCS_prog.LTS lqCCS.Helper.Conf_labels.

#[local] Open Scope lqccs_scope.

#[local] Open Scope nat_scope.

Reserved Notation "⟨ ρ , P ⟩ ⟶{ 𝜆 }[ k ] ⟨ ρ' , P' ⟩" (at level 70, format "⟨ ρ ,  P ⟩  ⟶{ 𝜆 }[ k ]  ⟨ ρ' ,  P' ⟩").
Reserved Notation "⟨ ρ , P ⟩ ⟶ₘ{ μ } ⟨ ρ' , P' ⟩" (at level 70, format "⟨ ρ ,  P ⟩  ⟶ₘ{ μ }  ⟨ ρ' ,  P' ⟩").

Section Process_LTS.
  Context `{lqP : lqCCS_Parameters} `{QM : QuantumModel}.

  (* Renaming of the channels of a label. *)
  Definition ren_clbl (f : nat → nat) (𝜆 : Labels (mem_action + prog_action)) : Labels (mem_action + prog_action) :=
    match 𝜆 with
    | ActExt (inr μ) => ActExt (inr (ren_action f μ))
    | _ => 𝜆
    end.

  Lemma ren_clbl_lift f (𝜆 : Labels prog_action) :
    ren_clbl f (lbl_inr 𝜆) = @lbl_inr mem_action prog_action (ren_lbl f 𝜆).
  Proof. by destruct 𝜆. Qed.

  (* ** The configuration LTS

      The rules of the contexts carry the actions of the program only: a move
      of the memory does not go through a context. *)

  Inductive conf_step (ρ : St) : prog → choice → Labels (mem_action + prog_action) → St → prog → Prop :=
  | co_tau t P :
      ⟨ρ, t ∶ 𝛕 ∙ P⟩ ⟶{τ}[{[+ t +]}] ⟨ρ, P⟩
  | co_recv t c v P :
      ⟨ρ, t ∶ c ? ∙ P⟩ ⟶{c ? v}[{[+ t +]}] ⟨ρ, P ⁅ v ⁆ᵥ⟩
  | co_op t U es qs P :
      eval_qubits es = Some qs →
      ⟨ρ, t ∶ U ⦅es⦆ ∙ P⟩ ⟶{⦅qs⦆ ! U}[{[+ t +]}] ⟨ρ, P⟩
  | co_meas t M es qs n P :
      eval_qubits es = Some qs →
      ⟨ρ, t ∶ M ⦅es ▷⦆ ∙ P⟩ ⟶{M ⦅qs⦆? n}[{[+ t +]}] ⟨ρ, P ⁅ VNat n ⁆ᵥ⟩
  | co_init t e q P :
      eval_qubit e = Some q →
      ⟨ρ, t ∶ e := |0⟩ ∙ P⟩ ⟶{reinit q}[{[+ t +]}] ⟨ρ, P⟩
  | co_sumL (g1 g2 : guard) k 𝜆 ρ' P' :
      (∀ μ, 𝜆 ≠ ActExt (mlbl μ)) → ⟨ρ, g1⟩ ⟶{𝜆}[k] ⟨ρ', P'⟩ → ⟨ρ, g1 + g2⟩ ⟶{𝜆}[k] ⟨ρ', P'⟩
  | co_sumR (g1 g2 : guard) k 𝜆 ρ' P' :
      (∀ μ, 𝜆 ≠ ActExt (mlbl μ)) → ⟨ρ, g2⟩ ⟶{𝜆}[k] ⟨ρ', P'⟩ → ⟨ρ, g1 + g2⟩ ⟶{𝜆}[k] ⟨ρ', P'⟩
  | co_send t c e v :
      〚 e 〛 = v → ⟨ρ, t ∶ c ! e⟩ ⟶{c ! v}[{[+ t +]}] ⟨ρ, 𝟘⟩
  | co_iteT e P Q k 𝜆 ρ' P' :
      〚 e 〛 = true → (∀ μ, 𝜆 ≠ ActExt (mlbl μ)) → ⟨ρ, P⟩ ⟶{𝜆}[k] ⟨ρ', P'⟩ → ⟨ρ, If e Then P Else Q⟩ ⟶{𝜆}[k] ⟨ρ', P'⟩
  | co_iteF e P Q k 𝜆 ρ' Q' :
      〚 e 〛 = false → (∀ μ, 𝜆 ≠ ActExt (mlbl μ)) → ⟨ρ, Q⟩ ⟶{𝜆}[k] ⟨ρ', Q'⟩ → ⟨ρ, If e Then P Else Q⟩ ⟶{𝜆}[k] ⟨ρ', Q'⟩
  | co_parL P Q k 𝜆 ρ' P' :
      (∀ μ, 𝜆 ≠ ActExt (mlbl μ)) → ⟨ρ, P⟩ ⟶{𝜆}[k] ⟨ρ', P'⟩ → ⟨ρ, P ∥ Q⟩ ⟶{𝜆}[k] ⟨ρ', P' ∥ Q⟩
  | co_parR P Q k 𝜆 ρ' Q' :
      (∀ μ, 𝜆 ≠ ActExt (mlbl μ)) → ⟨ρ, Q⟩ ⟶{𝜆}[k] ⟨ρ', Q'⟩ → ⟨ρ, P ∥ Q⟩ ⟶{𝜆}[k] ⟨ρ', P ∥ Q'⟩
  | co_syncL P Q (t t' : tag) c v P' Q' :
      ⟨ρ, P⟩ ⟶{c ! v}[{[+ t +]}] ⟨ρ, P'⟩ →
      ⟨ρ, Q⟩ ⟶{c ? v}[{[+ t' +]}] ⟨ρ, Q'⟩ →
      ⟨ρ, P ∥ Q⟩ ⟶{τ}[{[+ t; t' +]}] ⟨ρ, P' ∥ Q'⟩
  | co_syncR P Q (t t' : tag) c v P' Q' :
      ⟨ρ, P⟩ ⟶{c ? v}[{[+ t +]}] ⟨ρ, P'⟩ →
      ⟨ρ, Q⟩ ⟶{c ! v}[{[+ t' +]}] ⟨ρ, Q'⟩ →
      ⟨ρ, P ∥ Q⟩ ⟶{τ}[{[+ t; t' +]}] ⟨ρ, P' ∥ Q'⟩
  | co_res P k 𝜆 ρ' P' :
      (∀ μ, 𝜆 ≠ ActExt (mlbl μ)) → ⟨ρ, P⟩ ⟶{ren_clbl S 𝜆}[k] ⟨ρ', P'⟩ → ⟨ρ, ν P⟩ ⟶{𝜆}[k] ⟨ρ', ν P'⟩
  | co_rec t P :
      ⟨ρ, t ∶ rec ∙ P⟩ ⟶{τ}[{[+ t +]}] ⟨ρ, P ⁅ (t ∶ rec ∙ P)↑ ⁆ₚ⟩
  | co_mem_sop P (ℰ : Act) :
      ⟨ρ, P⟩ ⟶ₘ{? ℰ} ⟨ℰ · ρ, P⟩
  | co_mem_meas P ℳ n :
      n ∈ outs ℳ → ⟨ρ, P⟩ ⟶ₘ{ℳ !ₘ n} ⟨ℳ ·[n] ρ, P⟩
  | co_opCom P k U qs ρ' P' :
      ⟨ρ, P⟩ ⟶{⦅qs⦆ ! U}[k] ⟨ρ, P'⟩ →
      ⟨ρ, P⟩ ⟶ₘ{? (sop_act U qs)} ⟨ρ', P⟩ →
      ⟨ρ, P⟩ ⟶{τ}[k] ⟨ρ', P'⟩
  | co_measCom P k M qs n ρ' P' :
      ⟨ρ, P⟩ ⟶{M ⦅qs⦆? n}[k] ⟨ρ, P'⟩ →
      ⟨ρ, P⟩ ⟶ₘ{meas_of M qs !ₘ n} ⟨ρ', P⟩ →
      ⟨ρ, P⟩ ⟶{τ}[k] ⟨ρ', P'⟩
  | co_initCom P k q ρ' P' :
      ⟨ρ, P⟩ ⟶{reinit q}[k] ⟨ρ, P'⟩ →
      ⟨ρ, P⟩ ⟶ₘ{? (init_act q)} ⟨ρ', P⟩ →
      ⟨ρ, P⟩ ⟶{τ}[k] ⟨ρ', P'⟩
  where "⟨ ρ , P ⟩ ⟶{ 𝜆 }[ k ] ⟨ ρ' , P' ⟩" := (conf_step ρ P k 𝜆 ρ' P') : lqccs_scope
  and "⟨ ρ , P ⟩ ⟶ₘ{ μ } ⟨ ρ' , P' ⟩" := (conf_step ρ P ∅ (ActExt (mlbl μ)) ρ' P') : lqccs_scope.
End Process_LTS.

Notation "⟨ ρ , P ⟩ ⟶{ 𝜆 }[ k ] ⟨ ρ' , P' ⟩" := (conf_step ρ P k 𝜆 ρ' P') (at level 70, format "⟨ ρ ,  P ⟩  ⟶{ 𝜆 }[ k ]  ⟨ ρ' ,  P' ⟩") : lqccs_scope.
Notation "⟨ ρ , P ⟩ ⟶ₘ{ μ } ⟨ ρ' , P' ⟩" := (conf_step ρ P ∅ (ActExt (mlbl μ)) ρ' P')
  (at level 70, only parsing) : lqccs_scope.
Notation "⟨ ρ , P ⟩ ⟶ₘ{ μ } ⟨ ρ' , P' ⟩" := (conf_step ρ P ∅ (ActExt (mlbl μ)) ρ' P')
  (at level 70, only printing, format "⟨ ρ ,  P ⟩  ⟶ₘ{ μ }  ⟨ ρ' ,  P' ⟩") : lqccs_scope.
Notation "⟨ ρ , P ⟩ ↛{ 𝜆 }[ k ] ⟨ ρ' , P' ⟩" := (¬ conf_step ρ P k 𝜆 ρ' P') (at level 70, format "⟨ ρ ,  P ⟩  ↛{ 𝜆 }[ k ]  ⟨ ρ' ,  P' ⟩") : lqccs_scope.
Notation "⟨ ρ , P ⟩ ↛ₘ{ μ } ⟨ ρ' , P' ⟩" := (¬ conf_step ρ P ∅ (ActExt (mlbl μ)) ρ' P') (at level 70, format "⟨ ρ ,  P ⟩  ↛ₘ{ μ }  ⟨ ρ' ,  P' ⟩") : lqccs_scope.