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
From TestingTheory Require Import lqCCS.quantum_mem.Algebra lqCCS.quantum_mem.Syntax lqCCS.lqCCS_prog.Syntax.
From TestingTheory Require Import lqCCS.General_definition.Parallel_choice_LTS.
From TestingTheory Require Import lqCCS.quantum_mem.LTS lqCCS.lqCCS_prog.LTS.

#[local] Open Scope lqccs_scope.

Section LqP.
  Context `{LP : lqCCS_Parameters}.

Section Par_Qmem.
  Context `{QM : QuantumModel}.

  Inductive sync : mem_action → prog_action → Prop :=
  | sync_op U qs : sync (? (sop_act U qs)) (PrOp U qs)
  | sync_meas M qs n : sync (meas_of M qs !ₘ n) (PrMeas M qs n)
  | sync_init q : sync (? (init_act q)) (PrReinit q).

  Inductive sync_sys : mem_action + prog_action → prog_action → Prop :=
  | sync_sys_mem b a : sync b a → sync_sys (inl b) a
  | sync_sys_chan a a' : sync_chan a a' → sync_sys (inr a) a'.

End Par_Qmem.

End LqP.

Notation "'𝔻ₘₑₘ'" := sync : lqccs_scope.
Notation "P ⟶{ l }[ s ] P'" := (par_step mem_step prog_step sync P s l P')
  (at level 70, format "P  ⟶{ l }[ s ]  P'") : lqccs_scope.
Notation "P ↛{ l }[ s ] P'" := (¬ par_step mem_step prog_step sync P s l P')
  (at level 70, format "P  ↛{ l }[ s ]  P'") : lqccs_scope.