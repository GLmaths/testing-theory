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

(* * lqCCS: the program, memory and composed LTSs are LTSs with choices *)

From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base gmultiset.
From TestingTheory Require Import ActTau.
From TestingTheory Require Import lqCCS.Language.Algebra lqCCS.Language.Quantum lqCCS.Language.Syntax.
From TestingTheory Require Import lqCCS.General_definition.Choice_LTS lqCCS.General_definition.Parallel_choice_LTS.
From TestingTheory Require Import lqCCS.Language.LTS_quantum_mem lqCCS.Language.LTS_lqCCS_prog lqCCS.Language.LTS_lqCCS_process lqCCS.Language.LTS_lqCCS_par_Qmem.

#[local] Open Scope lqccs_scope.
#[local] Open Scope par_scope.

#[global] Instance lqCCS_prog_clts `{LP : lqCCS_Parameters} : Choice_LTS proc choice prog_action :=
  {| clts_step := prog_step |}.

Lemma lqCCS_prog_clts_step `{LP : lqCCS_Parameters} P s l P' :
  (P ⟶{l}[s] P')%clts ↔ P ⟶ₚ{l}[s] P'.
Proof. done. Qed.

#[global] Instance mem_q_clts `{QM : QuantumModel} : Choice_LTS St choice mem_action :=
  {| clts_step := mem_step |}.

Lemma mem_q_clts_step `{QM : QuantumModel} ρ (μ : mem_action) ρ' :
  (ρ ⟶{ActExt μ}[∅] ρ')%clts ↔ ρ ⟶ₘ{μ} ρ'.
Proof. done. Qed.

#[global] Instance lqCCS_process_clts `{LP : lqCCS_Parameters} `{QM : QuantumModel} :
  Choice_LTS (St * proc) choice (mem_action + prog_action) :=
  {| clts_step := par_step mem_step prog_step sync |}.

Lemma lqCCS_process_clts_step `{LP : lqCCS_Parameters} `{QM : QuantumModel} ρ P s l ρ' P' :
  ((ρ, P) ⟶{l}[s] (ρ', P'))%clts ↔ ρ ∣ P ⟶{l}[s] ρ' ∣ P'.
Proof. done. Qed.
