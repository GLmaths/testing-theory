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

(* * The probabilistic reduction semantics of lqCCS processes [⟨ρ, P⟩]

    A measurement reduces to the distribution of its branches of non-zero probability: the branch [n] has the memory [M_n ρ M_n† / tr (M_n ρ M_n†)] and the probability
    [tr (M_n ρ M_n†)].  Every step is weighted in the same way: the target [⟨ρ', P'⟩] of the reduction gives the branch of
    probability [tr ρ'] and memory [ρ' / tr ρ']. *)

From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base list.
From TestingTheory Require Import lqCCS.General_definition.Algebra lqCCS.quantum_mem.Syntax.
From TestingTheory Require Import lqCCS.lqCCS_prog.Syntax lqCCS.lqCCS_prog.Congruence.

#[local] Open Scope lqccs_scope.

Reserved Notation "⟨ ρ , P ⟩ ⟶ Δ" (at level 70, format "⟨ ρ ,  P ⟩  ⟶  Δ").

Section Process_pSTS.
  Context `{lqP : lqCCS_Parameters} `{QM : QuantumModel}.

  (* Two distributions with equal probabilities, equal memories and
      congruent processes. *)
  Definition dist_cgr (Δ Δ' : list (W * (St * prog))) : Prop :=
    Forall2 (λ x y, x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ x.2.2 ≡* y.2.2) Δ Δ'.

  Inductive psts : St → prog → list (W * (St * prog)) → Prop :=
  | psts_com ρ t c e v t' P K :
      〚 e 〛 = v →
      ⟨ρ, t ∶ c ! e ∥ ((t' ∶ c ? ∙ P) + K)⟩ ⟶ [(tr ρ, (snorm ρ, 𝟘 ∥ P ⁅ v ⁆ᵥ))]
  | psts_tau ρ t P K :
      ⟨ρ, ((t ∶ 𝛕 ∙ P) + K)⟩ ⟶ [(tr ρ, (snorm ρ, P))]
  | psts_op ρ t U es qs P K :
      eval_qubits es = Some qs →
      ⟨ρ, ((t ∶ U ⦅es⦆ ∙ P) + K)⟩ ⟶ [(tr (sop_apply U qs ρ), (snorm (sop_apply U qs ρ), P))]
  | psts_init ρ t e q P K :
      eval_qubit e = Some q →
      ⟨ρ, ((t ∶ e := |0⟩ ∙ P) + K)⟩ ⟶ [(tr (init_apply q ρ), (snorm (init_apply q ρ), P))]
  | psts_meas ρ t M es qs P K :
      eval_qubits es = Some qs →
      ⟨ρ, ((t ∶ M ⦅es ▷⦆ ∙ P) + K)⟩ ⟶
        map (λ n, (tr (M ⦅qs⦆[n] · ρ), (snorm (M ⦅qs⦆[n] · ρ), P ⁅ VNat n ⁆ᵥ)))
          (outs_nz (meas_of M qs) ρ)
  | psts_rec ρ t P :
      ⟨ρ, t ∶ rec ∙ P⟩ ⟶ [(tr ρ, (snorm ρ, P ⁅ (t ∶ rec ∙ P)↑ ⁆ₚ))]
  | psts_par ρ P Δ Q :
      ⟨ρ, P⟩ ⟶ Δ → ⟨ρ, P ∥ Q⟩ ⟶ map (λ x, (x.1, (x.2.1, x.2.2 ∥ Q))) Δ
  | psts_res ρ P Δ :
      ⟨ρ, P⟩ ⟶ Δ → ⟨ρ, ν P⟩ ⟶ map (λ x, (x.1, (x.2.1, ν x.2.2))) Δ
  | psts_cong ρ P P1 Δ1 Δ :
      P ≡* P1 → ⟨ρ, P1⟩ ⟶ Δ1 → dist_cgr Δ1 Δ → ⟨ρ, P⟩ ⟶ Δ
  where "⟨ ρ , P ⟩ ⟶ Δ" := (psts ρ P Δ) : lqccs_scope.
End Process_pSTS.

Notation "⟨ ρ , P ⟩ ⟶ Δ" := (psts ρ P Δ) (at level 70, format "⟨ ρ ,  P ⟩  ⟶  Δ") : lqccs_scope.
Notation "⟨ ρ , P ⟩ ↛ Δ" := (¬ psts ρ P Δ) (at level 70, format "⟨ ρ ,  P ⟩  ↛  Δ") : lqccs_scope.
