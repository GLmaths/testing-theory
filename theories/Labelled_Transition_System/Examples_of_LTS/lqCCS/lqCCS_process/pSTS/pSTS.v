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
(* * lqCCS: the probabilistic reduction semantics of processes [⟨ρ, P⟩]

    No choice: a process reduces to a distribution of processes with their
    memory, each with its probability.  A measurement reduces to the
    distribution of its branches of non-zero probability: the branch [k] has
    the memory [M_k ρ M_k† / tr (M_k ρ M_k†)] and the probability
    [tr (M_k ρ M_k†)].  The other steps keep the trace of the memory. *)

From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base list.
From TestingTheory Require Import lqCCS.quantum_mem.Algebra lqCCS.quantum_mem.Syntax.
From TestingTheory Require Import lqCCS.lqCCS_prog.Syntax lqCCS.lqCCS_prog.Congruence.

#[local] Open Scope lqccs_scope.

Reserved Notation "⟨ ρ , P ⟩ ⟶ Δ" (at level 70, format "⟨ ρ ,  P ⟩  ⟶  Δ").

Section LqP.
  Context `{LP : lqCCS_Parameters}.

Section pSTS.
  Context `{QM : QuantumModel}.

  (* Two distributions with congruent processes, equal memories and equal
      probabilities. *)
  Definition dist_cgr (Δ Δ' : list ((proc * St) * W)) : Prop :=
    Forall2 (λ x y, x.1.1 ≡* y.1.1 ∧ x.1.2 = y.1.2 ∧ x.2 = y.2) Δ Δ'.

  Inductive psts : St → proc → list ((proc * St) * W) → Prop :=
  | psts_com ρ t c e v t' P K :
      〚 e 〛 = v →
      ⟨ρ, t ∶ c ! e ∥ ((t' ∶ c ? ∙ P) + K)⟩ ⟶ [((𝟘 ∥ P ⁅ v ⁆ᵥ, ρ), tr ρ)]
  | psts_tau ρ t P K :
      ⟨ρ, ((t ∶ 𝛕 ∙ P) + K)⟩ ⟶ [((P, ρ), tr ρ)]
  | psts_op ρ t U es qs P K :
      eval_qubits es = Some qs →
      ⟨ρ, ((t ∶ U ⦅es⦆ ∙ P) + K)⟩ ⟶ [((P, sop_apply U qs ρ), tr ρ)]
  | psts_init ρ t e q P K :
      eval_qubit e = Some q →
      ⟨ρ, ((t ∶ e := |0⟩ ∙ P) + K)⟩ ⟶ [((P, init_apply q ρ), tr ρ)]
  | psts_meas ρ t M es qs P K :
      eval_qubits es = Some qs →
      ⟨ρ, ((t ∶ M ⦅es ▷⦆ ∙ P) + K)⟩ ⟶
        map (λ k, ((P ⁅ VNat k ⁆ᵥ, snorm (M ⦅qs⦆[k] · ρ)), tr (M ⦅qs⦆[k] · ρ)))
          (outs_nz (meas_of M qs) ρ)
  | psts_rec ρ t P :
      ⟨ρ, t ∶ rec ∙ P⟩ ⟶ [((P ⁅ (t ∶ rec ∙ P)↑ ⁆ₚ, ρ), tr ρ)]
  | psts_par ρ P Δ Q :
      ⟨ρ, P⟩ ⟶ Δ → ⟨ρ, P ∥ Q⟩ ⟶ map (λ x, ((x.1.1 ∥ Q, x.1.2), x.2)) Δ
  | psts_res ρ P Δ :
      ⟨ρ, P⟩ ⟶ Δ → ⟨ρ, ν P⟩ ⟶ map (λ x, ((ν x.1.1, x.1.2), x.2)) Δ
  | psts_cong ρ P P1 Δ1 Δ :
      P ≡* P1 → ⟨ρ, P1⟩ ⟶ Δ1 → dist_cgr Δ1 Δ → ⟨ρ, P⟩ ⟶ Δ
  where "⟨ ρ , P ⟩ ⟶ Δ" := (psts ρ P Δ) : lqccs_scope.
End pSTS.

End LqP.

Notation "⟨ ρ , P ⟩ ⟶ Δ" := (psts ρ P Δ) (at level 70, format "⟨ ρ ,  P ⟩  ⟶  Δ") : lqccs_scope.
Notation "⟨ ρ , P ⟩ ↛ Δ" := (¬ psts ρ P Δ) (at level 70, format "⟨ ρ ,  P ⟩  ↛  Δ") : lqccs_scope.

(* end hide *)
