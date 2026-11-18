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
(* * lqCCS: the reduction semantics of processes [⟨ρ, P⟩], with choices *)

From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base gmultiset list.
From TestingTheory Require Import lqCCS.quantum_mem.Algebra lqCCS.quantum_mem.Syntax.
From TestingTheory Require Import lqCCS.lqCCS_prog.Syntax lqCCS.lqCCS_prog.LTS lqCCS.lqCCS_prog.Congruence.
From TestingTheory Require Import lqCCS.General_definition.Parallel_choice_LTS.

#[local] Open Scope lqccs_scope.

Reserved Notation "⟨ ρ , P ⟩ ⟶[ s ] ⟨ ρ' , P' ⟩" (at level 70, format "⟨ ρ ,  P ⟩  ⟶[ s ]  ⟨ ρ' ,  P' ⟩").

Section LqP.
  Context `{LP : lqCCS_Parameters}.

Section STS.
  Context `{QM : QuantumModel}.

  Inductive sts : St → proc → choice → St → proc → Prop :=
  | sts_com ρ t c e v t' P K :
      〚 e 〛 = v →
      ⟨ρ, t ∶ c ! e ∥ ((t' ∶ c ? ∙ P) + K)⟩ ⟶[{[+ t; t' +]}] ⟨ρ, 𝟘 ∥ P ⁅ v ⁆ᵥ⟩
  | sts_tau ρ t P K :
      ⟨ρ, ((t ∶ 𝛕 ∙ P) + K)⟩ ⟶[{[+ t +]}] ⟨ρ, P⟩
  | sts_op ρ t U es qs P K :
      eval_qubits es = Some qs →
      ⟨ρ, ((t ∶ U ⦅es⦆ ∙ P) + K)⟩ ⟶[{[+ t +]}] ⟨sop_apply U qs ρ, P⟩
  | sts_init ρ t e q P K :
      eval_qubit e = Some q →
      ⟨ρ, ((t ∶ e := |0⟩ ∙ P) + K)⟩ ⟶[{[+ t +]}] ⟨init_apply q ρ, P⟩
  | sts_meas ρ t M es qs k P K :
      eval_qubits es = Some qs → k ∈ outs (meas_of M qs) →
      ⟨ρ, ((t ∶ M ⦅es ▷⦆ ∙ P) + K)⟩ ⟶[{[+ t +]}] ⟨M ⦅qs⦆[k] · ρ, P ⁅ VNat k ⁆ᵥ⟩
  | sts_rec ρ t P :
      ⟨ρ, t ∶ rec ∙ P⟩ ⟶[{[+ t +]}] ⟨ρ, P ⁅ (t ∶ rec ∙ P)↑ ⁆ₚ⟩
  | sts_par ρ P s ρ' P' Q :
      ⟨ρ, P⟩ ⟶[s] ⟨ρ', P'⟩ → ⟨ρ, P ∥ Q⟩ ⟶[s] ⟨ρ', P' ∥ Q⟩
  | sts_res ρ P s ρ' P' :
      ⟨ρ, P⟩ ⟶[s] ⟨ρ', P'⟩ → ⟨ρ, ν P⟩ ⟶[s] ⟨ρ', ν P'⟩
  | sts_cong ρ P P1 s ρ' Q1 Q :
      P ≡* P1 → ⟨ρ, P1⟩ ⟶[s] ⟨ρ', Q1⟩ → Q1 ≡* Q → ⟨ρ, P⟩ ⟶[s] ⟨ρ', Q⟩
  where "⟨ ρ , P ⟩ ⟶[ s ] ⟨ ρ' , P' ⟩" := (sts ρ P s ρ' P') : lqccs_scope.
End STS.

End LqP.

Notation "⟨ ρ , P ⟩ ⟶[ s ] ⟨ ρ' , P' ⟩" := (sts ρ P s ρ' P') (at level 70, format "⟨ ρ ,  P ⟩  ⟶[ s ]  ⟨ ρ' ,  P' ⟩") : lqccs_scope.
Notation "⟨ ρ , P ⟩ ↛[ s ] ⟨ ρ' , P' ⟩" := (¬ sts ρ P s ρ' P') (at level 70, format "⟨ ρ ,  P ⟩  ↛[ s ]  ⟨ ρ' ,  P' ⟩") : lqccs_scope.

(* end hide *)
