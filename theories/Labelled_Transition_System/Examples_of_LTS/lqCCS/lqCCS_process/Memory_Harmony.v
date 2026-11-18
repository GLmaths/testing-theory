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
(* * Pre-harmony: [⟨ρ, P⟩ -τ->_s ⟨ρ', P'⟩ ↔ (ρ ∣ P) -τ->_s (ρ' ∣ P')]

    The configuration LTS is the parallel composition, for [sync], of the
    memory LTS and the program LTS ([pre_harmony], in
    [lqCCS_process.Harmony_Lemma]).  The lemmas
    [conf_step_tau_inv], [conf_step_ext_inv], [conf_step_mem_inv],
    [prog_step_conf], [mem_step_conf] and [prog_step_mem_conf] are the two
    directions. *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base gmultiset countable decidable list.
From TestingTheory Require Import ActTau.
From TestingTheory Require Import lqCCS.General_definition.Algebra pMust_almost_sure lqCCS.quantum_mem.Syntax.
From TestingTheory Require Import lqCCS.lqCCS_prog.Syntax lqCCS.Helper.De_Brujin_lemmas lqCCS.General_definition.Parallel_choice_LTS lqCCS.quantum_mem.LTS lqCCS.lqCCS_prog.LTS lqCCS.lqCCS_par_Qmem.LTS lqCCS.lqCCS_process.LTS.LTS lqCCS.Helper.Conf_labels lqCCS.Helper.Label_lemmas.

#[local] Open Scope lqccs_scope.
#[local] Open Scope par_scope.
#[local] Open Scope nat_scope.

Section Memory_Harmony.
  Context `{lqP : lqCCS_Parameters} `{QM : QuantumModel}.

  (* ** From the configuration to the program and the memory *)

  Definition conf_view (ρ : St) (P : prog) (k : choice) (𝜆 : Labels (mem_action + prog_action))
    (ρ' : St) (P' : prog) : Prop :=
    match 𝜆 with
    | τ => (P ⟶ₚ{τ}[k] P' ∧ ρ' = ρ)
           ∨ (∃ μ2 μ1, P ⟶ₚ{ActExt μ2}[k] P' ∧ ρ ⟶ₘ{μ1} ρ' ∧ 𝔻ₘₑₘ μ1 μ2)
    | ActExt (inr μ2) => P ⟶ₚ{ActExt μ2}[k] P' ∧ ρ' = ρ
    | ActExt (inl μ1) => k = ∅ ∧ P' = P ∧ ρ ⟶ₘ{μ1} ρ'
    end.

  Lemma conf_step_view ρ P k 𝜆 ρ' P' : ⟨ρ, P⟩ ⟶{𝜆}[k] ⟨ρ', P'⟩ → conf_view ρ P k 𝜆 ρ' P'.
  Proof.
    induction 1 as [t P | t c v P | t U es qs P Hq | t M es qs n P Hq | t es qs P Hq
                   | g1 g2 k 𝜆 ρ' P' Hl Hc IH | g1 g2 k 𝜆 ρ' P' Hl Hc IH | t c e v He
                   | e P Q k 𝜆 ρ' P' He Hl Hc IH | e P Q k 𝜆 ρ' Q' He Hl Hc IH
                   | P Q k 𝜆 ρ' P' Hl Hc IH | P Q k 𝜆 ρ' Q' Hl Hc IH
                   | P Q t t' c v P' Q' HcP IHP HcQ IHQ | P Q t t' c v P' Q' HcP IHP HcQ IHQ
                   | P k 𝜆 ρ' P' Hl Hc IH | t X P | P ℰ | P M qs n
                   | P k U qs ρ' P' HcP IHP HcM IHM | P k M qs n ρ' P' HcP IHP HcM IHM
                   | P k qs ρ' P' HcP IHP HcM IHM]; simpl in *.
    - left. split; [apply pr_tau | done].
    - split; [apply pr_recv | done].
    - split; [by apply pr_op | done].
    - split; [by apply pr_meas | done].
    - split; [by apply pr_init | done].
    - destruct 𝜆 as [[μ1|μ2]|]; [exfalso; by apply (Hl μ1)| |].
      + destruct IH as (Hp & ->). split; [by apply pr_sumL | done].
      + destruct IH as [(Hp & ->) | (μ2 & μ1 & Hp & Hm & Hs)].
        * left. split; [by apply pr_sumL | done].
        * right. exists μ2, μ1. split_and!; [by apply pr_sumL | done | done].
    - destruct 𝜆 as [[μ1|μ2]|]; [exfalso; by apply (Hl μ1)| |].
      + destruct IH as (Hp & ->). split; [by apply pr_sumR | done].
      + destruct IH as [(Hp & ->) | (μ2 & μ1 & Hp & Hm & Hs)].
        * left. split; [by apply pr_sumR | done].
        * right. exists μ2, μ1. split_and!; [by apply pr_sumR | done | done].
    - split; [by apply pr_send | done].
    - destruct 𝜆 as [[μ1|μ2]|]; [exfalso; by apply (Hl μ1)| |].
      + destruct IH as (Hp & ->). split; [by apply pr_iteT | done].
      + destruct IH as [(Hp & ->) | (μ2 & μ1 & Hp & Hm & Hs)].
        * left. split; [by apply pr_iteT | done].
        * right. exists μ2, μ1. split_and!; [by apply pr_iteT | done | done].
    - destruct 𝜆 as [[μ1|μ2]|]; [exfalso; by apply (Hl μ1)| |].
      + destruct IH as (Hp & ->). split; [by apply pr_iteF | done].
      + destruct IH as [(Hp & ->) | (μ2 & μ1 & Hp & Hm & Hs)].
        * left. split; [by apply pr_iteF | done].
        * right. exists μ2, μ1. split_and!; [by apply pr_iteF | done | done].
    - destruct 𝜆 as [[μ1|μ2]|]; [exfalso; by apply (Hl μ1)| |].
      + destruct IH as (Hp & ->). split; [by apply pr_parL | done].
      + destruct IH as [(Hp & ->) | (μ2 & μ1 & Hp & Hm & Hs)].
        * left. split; [by apply pr_parL | done].
        * right. exists μ2, μ1. split_and!; [by apply pr_parL | done | done].
    - destruct 𝜆 as [[μ1|μ2]|]; [exfalso; by apply (Hl μ1)| |].
      + destruct IH as (Hp & ->). split; [by apply pr_parR | done].
      + destruct IH as [(Hp & ->) | (μ2 & μ1 & Hp & Hm & Hs)].
        * left. split; [by apply pr_parR | done].
        * right. exists μ2, μ1. split_and!; [by apply pr_parR | done | done].
    - destruct IHP as (HpP & _), IHQ as (HpQ & _).
      left. split; [by eapply pr_syncL | done].
    - destruct IHP as (HpP & _), IHQ as (HpQ & _).
      left. split; [by eapply pr_syncR | done].
    - destruct 𝜆 as [[μ1|μ2]|]; [exfalso; by apply (Hl μ1)| |]; simpl in IH.
      + destruct IH as (Hp & ->). split; [by apply pr_res | done].
      + destruct IH as [(Hp & ->) | (μ2 & μ1 & Hp & Hm & Hs)].
        * left. split; [by apply pr_res | done].
        * right. exists μ2, μ1. split_and!; [| done | done].
          apply pr_res. by rewrite (sync_lbl_ren _ _ Hs).
    - left. split; [apply pr_rec | done].
    - split_and!; [done | done | apply me_sop].
    - split_and!; [done | done | by apply me_meas].
    - destruct IHP as (Hp & _), IHM as (_ & _ & Hm).
      right. exists (PrOp U qs), (? (sop_act U qs)). split_and!; [done | done | constructor].
    - destruct IHP as (Hp & _), IHM as (_ & _ & Hm).
      right. exists (PrMeas M qs n), (meas_of M qs !ₘ n). split_and!; [done | done | constructor].
    - destruct IHP as (Hp & _), IHM as (_ & _ & Hm).
      right. exists (PrReinit qs), (? (init_act qs)). split_and!; [done | done | constructor].
  Qed.

  Lemma conf_step_tau_inv ρ P k ρ' P' :
    ⟨ρ, P⟩ ⟶{τ}[k] ⟨ρ', P'⟩ →
    (P ⟶ₚ{τ}[k] P' ∧ ρ' = ρ) ∨ (∃ μ2 μ1, P ⟶ₚ{ActExt μ2}[k] P' ∧ ρ ⟶ₘ{μ1} ρ' ∧ 𝔻ₘₑₘ μ1 μ2).
  Proof. intros Hc. exact (conf_step_view _ _ _ _ _ _ Hc). Qed.

  Lemma conf_step_ext_inv ρ P k (μ : prog_action) ρ' P' :
    ⟨ρ, P⟩ ⟶{ActExt μ}[k] ⟨ρ', P'⟩ → P ⟶ₚ{ActExt μ}[k] P' ∧ ρ' = ρ.
  Proof. intros Hc. exact (conf_step_view _ _ _ _ _ _ Hc). Qed.

  Lemma conf_step_mem_inv ρ P k (μ : mem_action) ρ' P' :
    ⟨ρ, P⟩ ⟶{ActExt μ}[k] ⟨ρ', P'⟩ → k = ∅ ∧ P' = P ∧ ρ ⟶ₘ{μ} ρ'.
  Proof. intros Hc. exact (conf_step_view _ _ _ _ _ _ Hc). Qed.

  (* ** From the program and the memory to the configuration *)

  Lemma prog_gstep_conf ρ (g : guard) k 𝜆 P' : g ⟶ᵍ{𝜆}[k] P' → ⟨ρ, g⟩ ⟶{lbl_inr 𝜆}[k] ⟨ρ, P'⟩.
  Proof.
    induction 1 as [| | | | | g1 g2 k 𝜆 P' Hg IH | g1 g2 k 𝜆 P' Hg IH]; [by econstructor..| |].
    - apply co_sumL; [intros μ; by destruct 𝜆|done].
    - apply co_sumR; [intros μ; by destruct 𝜆|done].
  Qed.

  Lemma prog_step_conf ρ P k 𝜆 P' : P ⟶ₚ{𝜆}[k] P' → ⟨ρ, P⟩ ⟶{lbl_inr 𝜆}[k] ⟨ρ, P'⟩.
  Proof.
    induction 1 as [g k 𝜆 P' Hg| |e P Q k 𝜆 P' He Hp IH|e P Q k 𝜆 Q' He Hq IH|P Q k 𝜆 P' Hp IH|P Q k 𝜆 Q' Hq IH
                   | | |P k 𝜆 P' Hp IH|].
    - by apply prog_gstep_conf.
    - by constructor.
    - apply co_iteT; [done|intros μ; by destruct 𝜆|done].
    - apply co_iteF; [done|intros μ; by destruct 𝜆|done].
    - apply co_parL; [intros μ; by destruct 𝜆|done].
    - apply co_parR; [intros μ; by destruct 𝜆|done].
    - by eapply co_syncL.
    - by eapply co_syncR.
    - apply co_res; [intros μ; by destruct 𝜆|]. by rewrite ren_clbl_lift.
    - apply co_rec.
  Qed.

  Lemma mem_step_conf ρ P μ ρ' : ρ ⟶ₘ{μ} ρ' → ⟨ρ, P⟩ ⟶ₘ{μ} ⟨ρ', P⟩.
  Proof. inversion 1; subst; by constructor. Qed.

  Lemma prog_step_mem_conf ρ P k μ2 P' μ1 ρ' :
    P ⟶ₚ{ActExt μ2}[k] P' → ρ ⟶ₘ{μ1} ρ' → 𝔻ₘₑₘ μ1 μ2 →
    ⟨ρ, P⟩ ⟶{τ}[k] ⟨ρ', P'⟩.
  Proof.
    intros Hp Hm Hs. destruct Hs.
    - eapply co_opCom; [exact (prog_step_conf _ _ _ _ _ Hp) | by apply mem_step_conf].
    - eapply co_measCom; [exact (prog_step_conf _ _ _ _ _ Hp) | by apply mem_step_conf].
    - eapply co_initCom; [exact (prog_step_conf _ _ _ _ _ Hp) | by apply mem_step_conf].
  Qed.

End Memory_Harmony.

(* end hide *)
