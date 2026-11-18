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

(* * The Harmony lemma for lqCCS processes [⟨ρ, P⟩] : 
    A silent transition of [⟨ρ, P⟩] is a silent transition of [ρ ∣ P]
    ([pre_harmony]), and a reduction of the STS is a silent transition of
    the LTS followed by structural congruence, with the same choice
    ([harmony]). *)

From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base gmultiset list.
From TestingTheory Require Import ActTau.
From TestingTheory Require Import lqCCS.General_definition.Algebra lqCCS.quantum_mem.Syntax.
From TestingTheory Require Import lqCCS.lqCCS_prog.Syntax lqCCS.lqCCS_prog.LTS lqCCS.lqCCS_prog.Congruence.
From TestingTheory Require Import lqCCS.General_definition.Parallel_choice_LTS lqCCS.quantum_mem.LTS lqCCS.lqCCS_par_Qmem.LTS.
From TestingTheory Require Import lqCCS.lqCCS_process.LTS.LTS lqCCS.Helper.Conf_labels lqCCS.lqCCS_process.STS.STS.
From TestingTheory Require Import lqCCS.lqCCS_process.Memory_Harmony lqCCS.lqCCS_par_Qmem.STS_Harmony.
From TestingTheory Require Import lqCCS.General_definition.Choice_LTS lqCCS.General_definition.Choice_LTS_eq.
From TestingTheory Require Import lqCCS.quantum_mem.Congruence lqCCS.lqCCS_process.Congruence lqCCS.lqCCS_process.Choice_LTS_instances.

#[local] Open Scope lqccs_scope.
#[local] Open Scope par_scope.

Section Pre_Harmony.
  Context `{lqP : lqCCS_Parameters} `{QM : QuantumModel}.

(* ** The pre-harmony lemma *)

Theorem pre_harmony ρ P k ρ' P' :
  ⟨ρ, P⟩ ⟶{τ}[k] ⟨ρ', P'⟩ ↔ ρ ∣ P ⟶{τ}[k] ρ' ∣ P'.
Proof.
  split.
  - intros Hc. destruct (conf_step_tau_inv _ _ _ _ _ Hc)
      as [(Hp & ->) | (μ2 & μ1 & Hp & Hm & Hs)].
    + exact (par_right mem_step prog_step sync ρ P k τ P' Hp).
    + rewrite <- (left_id_L ∅ (⊎) k). eapply par_sync; [exact Hm | exact Hp | exact Hs].
  - intros Hp. inversion Hp as [? ? ? 𝜆 ? Hm El | ? ? ? 𝜆 ? Hq El | ? ? c1 c2 μ1 μ2 ? ? Hm Hq Hs]; subst.
    + destruct (mem_step_choice _ _ _ _ Hm) as (_ & μ1 & ->). discriminate.
    + destruct 𝜆; [discriminate |]. by apply prog_step_conf.
    + destruct (mem_step_choice _ _ _ _ Hm) as (-> & _).
      rewrite (left_id_L ∅ (⊎)). by eapply prog_step_mem_conf.
Qed.

End Pre_Harmony.

(* ** The Harmony lemma *)

Section Harmony.
  Context `{lqP : lqCCS_Parameters} `{QM : QuantumModel}.
  Open Scope choice_lts_scope.

Theorem harmony ρ P k ρ' Q :
  ⟨ρ, P⟩ ⟶[k] ⟨ρ', Q⟩ ↔ (ρ, P) ⟶{τ}[k] . ⋍ (ρ', Q).
Proof.
  rewrite STS_Harmony. split.
  - intros (ρ'' & Q' & Hc & HQ). exists (ρ'', Q'). split; [by apply pre_harmony|exact HQ].
  - intros ([ρ'' Q'] & Hc & HQ). exists ρ'', Q'. split; [by apply pre_harmony|exact HQ].
Qed.

End Harmony.