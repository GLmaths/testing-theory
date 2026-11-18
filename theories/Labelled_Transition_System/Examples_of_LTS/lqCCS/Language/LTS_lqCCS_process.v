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

(* * lqCCS: the LTS of processes [⟨ρ, P⟩] *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base gmultiset countable decidable list sets numbers.
From TestingTheory Require Import ActTau.
From TestingTheory Require Import lqCCS.Language.Algebra lqCCS.Language.Quantum.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Helper_substitution.De_Brujin_lemmas lqCCS.General_definition.Parallel_choice_LTS.
From TestingTheory Require Import lqCCS.Language.LTS_quantum_mem lqCCS.Language.LTS_lqCCS_prog.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

Section LqP.
  Context `{LP : lqCCS_Parameters}.

Reserved Notation "⟨ ρ , P ⟩ ⟶{ l }[ s ] ⟨ ρ' , P' ⟩" (at level 70, format "⟨ ρ ,  P ⟩  ⟶{ l }[ s ]  ⟨ ρ' ,  P' ⟩").
Reserved Notation "⟨ ρ , P ⟩ ⟶ₘ{ μ } ⟨ ρ' , P' ⟩" (at level 70, format "⟨ ρ ,  P ⟩  ⟶ₘ{ μ }  ⟨ ρ' ,  P' ⟩").

Section Process.
  Context `{QM : QuantumModel}.

  (* ** The configuration LTS *)

  Inductive conf_step (ρ : St) : proc → choice → Labels prog_action + mem_action → St → proc → Prop :=
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
  | co_sumL (g1 g2 : guard) s l ρ' P' :
      ⟨ρ, g1⟩ ⟶{l}[s] ⟨ρ', P'⟩ → ⟨ρ, g1 + g2⟩ ⟶{l}[s] ⟨ρ', P'⟩
  | co_sumR (g1 g2 : guard) s l ρ' P' :
      ⟨ρ, g2⟩ ⟶{l}[s] ⟨ρ', P'⟩ → ⟨ρ, g1 + g2⟩ ⟶{l}[s] ⟨ρ', P'⟩
  | co_send t c e v :
      〚 e 〛 = v → ⟨ρ, t ∶ c ! e⟩ ⟶{c ! v}[{[+ t +]}] ⟨ρ, 𝟘⟩
  | co_iteT e P Q s l ρ' P' :
      〚 e 〛 = true → ⟨ρ, P⟩ ⟶{l}[s] ⟨ρ', P'⟩ → ⟨ρ, If e Then P Else Q⟩ ⟶{l}[s] ⟨ρ', P'⟩
  | co_iteF e P Q s l ρ' Q' :
      〚 e 〛 = false → ⟨ρ, Q⟩ ⟶{l}[s] ⟨ρ', Q'⟩ → ⟨ρ, If e Then P Else Q⟩ ⟶{l}[s] ⟨ρ', Q'⟩
  | co_parL P Q s l ρ' P' :
      ⟨ρ, P⟩ ⟶{l}[s] ⟨ρ', P'⟩ → ⟨ρ, P ∥ Q⟩ ⟶{l}[s] ⟨ρ', P' ∥ Q⟩
  | co_parR P Q s l ρ' Q' :
      ⟨ρ, Q⟩ ⟶{l}[s] ⟨ρ', Q'⟩ → ⟨ρ, P ∥ Q⟩ ⟶{l}[s] ⟨ρ', P ∥ Q'⟩
  | co_syncL P Q (t t' : tag) c v P' Q' :
      ⟨ρ, P⟩ ⟶{c ! v}[{[+ t +]}] ⟨ρ, P'⟩ →
      ⟨ρ, Q⟩ ⟶{c ? v}[{[+ t' +]}] ⟨ρ, Q'⟩ →
      ⟨ρ, P ∥ Q⟩ ⟶{τ}[{[+ t; t' +]}] ⟨ρ, P' ∥ Q'⟩
  | co_syncR P Q (t t' : tag) c v P' Q' :
      ⟨ρ, P⟩ ⟶{c ? v}[{[+ t +]}] ⟨ρ, P'⟩ →
      ⟨ρ, Q⟩ ⟶{c ! v}[{[+ t' +]}] ⟨ρ, Q'⟩ →
      ⟨ρ, P ∥ Q⟩ ⟶{τ}[{[+ t; t' +]}] ⟨ρ, P' ∥ Q'⟩
  | co_res P s l ρ' P' :
      ⟨ρ, P⟩ ⟶{ren_lbl S l}[s] ⟨ρ', P'⟩ → ⟨ρ, ν P⟩ ⟶{l}[s] ⟨ρ', ν P'⟩
  | co_rec t P :
      ⟨ρ, t ∶ rec ∙ P⟩ ⟶{τ}[{[+ t +]}] ⟨ρ, P ⁅ (t ∶ rec ∙ P)↑ ⁆ₚ⟩
  | co_mem_sop P (ℰ : Act) :
      ⟨ρ, P⟩ ⟶ₘ{? ℰ} ⟨ℰ · ρ, P⟩
  | co_mem_meas P ℳ k :
      k ∈ outs ℳ → ⟨ρ, P⟩ ⟶ₘ{ℳ !ₘ k} ⟨ℳ ·[k] ρ, P⟩
  | co_opCom P s U qs ρ' P' :
      ⟨ρ, P⟩ ⟶{⦅qs⦆ ! U}[s] ⟨ρ, P'⟩ →
      ⟨ρ, P⟩ ⟶ₘ{? (sop_act U qs)} ⟨ρ', P⟩ →
      ⟨ρ, P⟩ ⟶{τ}[s] ⟨ρ', P'⟩
  | co_measCom P s M qs n ρ' P' :
      ⟨ρ, P⟩ ⟶{M ⦅qs⦆? n}[s] ⟨ρ, P'⟩ →
      ⟨ρ, P⟩ ⟶ₘ{meas_of M qs !ₘ n} ⟨ρ', P⟩ →
      ⟨ρ, P⟩ ⟶{τ}[s] ⟨ρ', P'⟩
  | co_initCom P s q ρ' P' :
      ⟨ρ, P⟩ ⟶{reinit q}[s] ⟨ρ, P'⟩ →
      ⟨ρ, P⟩ ⟶ₘ{? (init_act q)} ⟨ρ', P⟩ →
      ⟨ρ, P⟩ ⟶{τ}[s] ⟨ρ', P'⟩
  where "⟨ ρ , P ⟩ ⟶{ l }[ s ] ⟨ ρ' , P' ⟩" := (conf_step ρ P s (inl l) ρ' P') : lqccs_scope
  and "⟨ ρ , P ⟩ ⟶ₘ{ μ } ⟨ ρ' , P' ⟩" := (conf_step ρ P ∅ (inr (μ : mem_action)) ρ' P') : lqccs_scope.
End Process.

End LqP.

Reserved Notation "⟨ ρ , P ⟩ ⟶{ l }[ s ] ⟨ ρ' , P' ⟩" (at level 70, format "⟨ ρ ,  P ⟩  ⟶{ l }[ s ]  ⟨ ρ' ,  P' ⟩").
Reserved Notation "⟨ ρ , P ⟩ ⟶ₘ{ μ } ⟨ ρ' , P' ⟩" (at level 70, format "⟨ ρ ,  P ⟩  ⟶ₘ{ μ }  ⟨ ρ' ,  P' ⟩").
Notation "⟨ ρ , P ⟩ ⟶{ l }[ s ] ⟨ ρ' , P' ⟩" := (conf_step ρ P s (inl l) ρ' P') (at level 70, format "⟨ ρ ,  P ⟩  ⟶{ l }[ s ]  ⟨ ρ' ,  P' ⟩") : lqccs_scope.
Notation "⟨ ρ , P ⟩ ⟶ₘ{ μ } ⟨ ρ' , P' ⟩" := (conf_step ρ P ∅ (inr (μ : mem_action)) ρ' P')
  (at level 70, only parsing) : lqccs_scope.
Notation "⟨ ρ , P ⟩ ⟶ₘ{ μ } ⟨ ρ' , P' ⟩" := (conf_step ρ P ∅ (inr μ) ρ' P')
  (at level 70, only printing, format "⟨ ρ ,  P ⟩  ⟶ₘ{ μ }  ⟨ ρ' ,  P' ⟩") : lqccs_scope.
Notation "⟨ ρ , P ⟩ ↛{ l }[ s ] ⟨ ρ' , P' ⟩" := (¬ conf_step ρ P s (inl l) ρ' P') (at level 70, format "⟨ ρ ,  P ⟩  ↛{ l }[ s ]  ⟨ ρ' ,  P' ⟩") : lqccs_scope.
Notation "⟨ ρ , P ⟩ ↛ₘ{ μ } ⟨ ρ' , P' ⟩" := (¬ conf_step ρ P ∅ (inr μ) ρ' P') (at level 70, format "⟨ ρ ,  P ⟩  ↛ₘ{ μ }  ⟨ ρ' ,  P' ⟩") : lqccs_scope.