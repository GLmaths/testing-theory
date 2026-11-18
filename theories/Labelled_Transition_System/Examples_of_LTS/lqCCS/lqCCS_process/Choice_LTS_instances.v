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

(* * The LTS of lqCCS processes [⟨ρ, P⟩] is an LTS with choices, with
    equality on the memory and structural congruence on the program *)

From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base gmultiset list relations.
From TestingTheory Require Import ActTau.
From TestingTheory Require Import lqCCS.General_definition.Choice_LTS lqCCS.General_definition.Choice_LTS_eq.
From TestingTheory Require Import lqCCS.General_definition.Algebra lqCCS.General_definition.Parallel_choice_LTS.
From TestingTheory Require Import lqCCS.quantum_mem.Syntax lqCCS.quantum_mem.LTS lqCCS.quantum_mem.Congruence.
From TestingTheory Require Import lqCCS.lqCCS_prog.Syntax lqCCS.lqCCS_prog.LTS lqCCS.lqCCS_prog.Congruence.
From TestingTheory Require Import lqCCS.lqCCS_par_Qmem.LTS lqCCS.lqCCS_process.LTS.LTS lqCCS.Helper.Conf_labels lqCCS.lqCCS_process.Congruence.
From TestingTheory Require Import lqCCS.lqCCS_process.Memory_Harmony.

#[local] Open Scope lqccs_scope.

Section Process.
  Context `{lqP : lqCCS_Parameters} `{QM : QuantumModel}.

  #[global] Instance lqCCS_process_clts : Choice_LTS (St * prog) choice (mem_action + prog_action) :=
    {| clts_step c k 𝜆 c' := conf_step c.1 c.2 k 𝜆 c'.1 c'.2 |}.

  Lemma lqCCS_process_clts_step ρ P k 𝜆 ρ' P' :
    ((ρ, P) ⟶{𝜆}[k] (ρ', P'))%clts ↔ ⟨ρ, P⟩ ⟶{𝜆}[k] ⟨ρ', P'⟩.
  Proof. done. Qed.

  #[global] Program Instance lqCCS_process_clts_eq : Choice_LTS_eq (St * prog) choice (mem_action + prog_action) :=
    {| clts_eq_rel := conf_cgr |}.
  Next Obligation.
    intros [ρ P] k 𝜆 [ρ' Q] ([ρ1 P1] & [Hm HP] & Hs). simpl in *. unfold mem_cgr in Hm. subst ρ1.
    destruct 𝜆 as [[μ1|μ2]|].
    - destruct (conf_step_mem_inv ρ P1 k μ1 ρ' Q Hs) as (-> & -> & Hmem).
      exists (ρ', P). split; [by apply mem_step_conf|]. split; [done|exact HP].
    - destruct (conf_step_ext_inv ρ P1 k μ2 ρ' Q Hs) as (Hq & ->).
      destruct (Congruence_Respects_Transition P _ _ Q (ex_intro _ P1 (conj HP Hq))) as (Q2 & HQ2 & EQ).
      exists (ρ, Q2). split; [exact (prog_step_conf _ _ _ _ _ HQ2)|]. split; [done|exact EQ].
    - destruct (conf_step_tau_inv _ _ _ _ _ Hs) as [(Hq & ->)|(μ2 & μ1 & Hq & Hmem & Hsy)].
      + destruct (Congruence_Respects_Transition P _ _ Q (ex_intro _ P1 (conj HP Hq))) as (Q2 & HQ2 & EQ).
        exists (ρ, Q2). split; [exact (prog_step_conf _ _ _ _ _ HQ2)|]. split; [done|exact EQ].
      + destruct (Congruence_Respects_Transition P _ _ Q (ex_intro _ P1 (conj HP Hq))) as (Q2 & HQ2 & EQ).
        exists (ρ', Q2). split; [by eapply prog_step_mem_conf|]. split; [done|exact EQ].
  Qed.
End Process.
