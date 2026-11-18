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

(* * lqCCS: the composition [ρ ∣ P] of the quantum memory and of a program *)

From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base gmultiset countable decidable list.
From TestingTheory Require Import ActTau.
From TestingTheory Require Import lqCCS.General_definition.Algebra lqCCS.quantum_mem.Syntax lqCCS.lqCCS_prog.Syntax.
From TestingTheory Require Import lqCCS.General_definition.Parallel_choice_LTS.
From TestingTheory Require Import lqCCS.quantum_mem.LTS lqCCS.lqCCS_prog.LTS.

#[local] Open Scope lqccs_scope.

Section Prog_Sync_Mem.
  Context `{lqP : lqCCS_Parameters} `{QM : QuantumModel}.

  (* Synchronisation of the program and of the memory, in [ρ ∣ P]. *)
  Inductive sync : mem_action → prog_action → Prop :=
  | sync_op U qs : sync (? (sop_act U qs)) (PrOp U qs)
  | sync_meas M qs n : sync (meas_of M qs !ₘ n) (PrMeas M qs n)
  | sync_init q : sync (? (init_act q)) (PrReinit q).

  Lemma sync_lbl_ren μ1 μ2 : sync μ1 μ2 → ren_lbl S (ActExt μ2) = ActExt μ2.
  Proof. by destruct 1. Qed.

End Prog_Sync_Mem.

Notation "'𝔻ₘₑₘ'" := sync : lqccs_scope.
Notation "P ⟶{ 𝜆 }[ k ] P'" := (par_step mem_step prog_step sync P k 𝜆 P')
  (at level 70, format "P  ⟶{ 𝜆 }[ k ]  P'") : lqccs_scope.
Notation "P ↛{ 𝜆 }[ k ] P'" := (¬ par_step mem_step prog_step sync P k 𝜆 P')
  (at level 70, format "P  ↛{ 𝜆 }[ k ]  P'") : lqccs_scope.