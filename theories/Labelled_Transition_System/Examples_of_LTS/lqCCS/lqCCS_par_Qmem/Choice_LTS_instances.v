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
(* * lqCCS: the composition [ρ ∣ P] is an LTS with choices, with equality on
    the memory and structural congruence on the program *)

From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base gmultiset list relations.
From TestingTheory Require Import ActTau.
From TestingTheory Require Import lqCCS.General_definition.Choice_LTS lqCCS.General_definition.Choice_LTS_eq.
From TestingTheory Require Import lqCCS.General_definition.Algebra lqCCS.General_definition.Parallel_choice_LTS.
From TestingTheory Require Import lqCCS.quantum_mem.Syntax lqCCS.quantum_mem.LTS lqCCS.quantum_mem.Congruence.
From TestingTheory Require Import lqCCS.lqCCS_prog.Syntax lqCCS.lqCCS_prog.LTS lqCCS.lqCCS_prog.Congruence.
From TestingTheory Require Import lqCCS.lqCCS_par_Qmem.LTS lqCCS.lqCCS_process.Congruence.

#[local] Open Scope lqccs_scope.
#[local] Open Scope par_scope.

#[global] Instance lqCCS_par_Qmem_clts `{lqP : lqCCS_Parameters} `{QM : QuantumModel} :
  Choice_LTS (St * prog) choice (mem_action + prog_action) :=
  {| clts_step := par_step mem_step prog_step sync |}.

Lemma lqCCS_par_Qmem_clts_step `{lqP : lqCCS_Parameters} `{QM : QuantumModel} ρ P k 𝜆 ρ' P' :
  ((ρ, P) ⟶{𝜆}[k] (ρ', P'))%clts ↔ ρ ∣ P ⟶{𝜆}[k] ρ' ∣ P'.
Proof. done. Qed.

#[global] Program Instance lqCCS_par_Qmem_clts_eq `{lqP : lqCCS_Parameters} `{QM : QuantumModel} :
  Choice_LTS_eq (St * prog) choice (mem_action + prog_action) :=
  {| clts_eq_rel := conf_cgr |}.
Next Obligation.
  intros lqP ? ? ? ? ? [ρ P] k 𝜆 [ρ' Q] ([ρ1 P1] & [Hm HP] & Hs). simpl in *. unfold mem_cgr in Hm. subst ρ1.
  inversion Hs as [? ? ? 𝜆0 ? Hm' El | ? ? ? 𝜆0 Q1 Hq El | ? ? c1 c2 μ1 μ2 ? Q1 Hm' Hq Hsy]; subst.
  - exists (ρ', P). split; [by apply par_left|]. split; [done|by simpl].
  - destruct (Congruence_Respects_Transition P _ _ Q (ex_intro _ P1 (conj HP Hq))) as (Q2 & HQ2 & EQ).
    eexists (_, Q2). split; [by apply par_right|]. split; [done|exact EQ].
  - destruct (Congruence_Respects_Transition P _ _ Q (ex_intro _ P1 (conj HP Hq))) as (Q2 & HQ2 & EQ).
    exists (ρ', Q2). split; [by eapply par_sync|]. split; [done|exact EQ].
Qed.

(* end hide *)
