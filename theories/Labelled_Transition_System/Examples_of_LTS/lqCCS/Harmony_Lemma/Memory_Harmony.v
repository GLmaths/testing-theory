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
    memory LTS and the program LTS ([pre_harmony]).  The lemmas
    [conf_step_tau_inv], [conf_step_ext_inv], [conf_step_mem_inv],
    [prog_step_conf], [mem_step_conf] and [prog_step_mem_conf] are the two
    directions. *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list.
From TestingTheory Require Import ActTau.
From TestingTheory Require Import lqCCS.Language.Algebra pMust_almost_sure lqCCS.Language.Quantum.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.LTS.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

Lemma sync_lbl_ren `{QuantumModel} b a : 𝔻ₘₑₘ b a → ren_lbl S (ActExt a) = ActExt a.
Proof. by destruct 1. Qed.

Lemma cmul_eps_l_inv c2 c : cmul CEps c2 c → c = c2.
Proof. inversion 1; done. Qed.

Section Memory_Harmony.
  Context `{QM : QuantumModel}.

  Lemma mem_step_choice ρ c l ρ' : mem_step ρ c l ρ' → c = CEps ∧ ∃ b, l = ActExt b.
  Proof. inversion 1; eauto. Qed.

  (* ** From the configuration to the program and the memory *)

  Definition conf_view (ρ : St) (P : proc) (s : choice) (l : Labels prog_action + mem_action)
    (ρ' : St) (P' : proc) : Prop :=
    match l with
    | inl τ => (P ⟶{τ}[s] P' ∧ ρ' = ρ)
               ∨ (∃ a b, P ⟶{ActExt a}[s] P' ∧ ρ ⟶ₘ{b} ρ' ∧ 𝔻ₘₑₘ b a)
    | inl (ActExt a) => P ⟶{ActExt a}[s] P' ∧ ρ' = ρ
    | inr b => s = CEps ∧ P' = P ∧ ρ ⟶ₘ{b} ρ'
    end.

  Lemma conf_step_view ρ P s l ρ' P' : conf_step ρ P s l ρ' P' → conf_view ρ P s l ρ' P'.
  Proof.
    induction 1 as [t P | t c v P | t E es qs P Hq | t M es qs n P Hq | t es qs P Hq
                   | g1 g2 s l ρ' P' Hc IH | g1 g2 s l ρ' P' Hc IH | t c e v He
                   | e P Q s l ρ' P' He Hc IH | e P Q s l ρ' Q' He Hc IH
                   | P Q s l ρ' P' Hc IH | P Q s l ρ' Q' Hc IH
                   | P Q t t' c v P' Q' HcP IHP HcQ IHQ | P Q t t' c v P' Q' HcP IHP HcQ IHQ
                   | P s l ρ' P' Hc IH | t X P | P ℰ | P M qs k
                   | P s E qs ρ' P' HcP IHP HcM IHM | P s M qs n ρ' P' HcP IHP HcM IHM
                   | P s qs ρ' P' HcP IHP HcM IHM]; simpl in *.
    - left. split; [apply pr_tau | done].
    - split; [apply pr_recv | done].
    - split; [by apply pr_op | done].
    - split; [by apply pr_meas | done].
    - split; [by apply pr_init | done].
    - destruct l as [a |].
      + destruct IH as (Hp & ->). split; [by apply pr_sumL | done].
      + destruct IH as [(Hp & ->) | (a & b & Hp & Hm & Hs)].
        * left. split; [by apply pr_sumL | done].
        * right. exists a, b. split_and!; [by apply pr_sumL | done | done].
    - destruct l as [a |].
      + destruct IH as (Hp & ->). split; [by apply pr_sumR | done].
      + destruct IH as [(Hp & ->) | (a & b & Hp & Hm & Hs)].
        * left. split; [by apply pr_sumR | done].
        * right. exists a, b. split_and!; [by apply pr_sumR | done | done].
    - split; [by apply pr_send | done].
    - destruct l as [a |].
      + destruct IH as (Hp & ->). split; [by apply pr_iteT | done].
      + destruct IH as [(Hp & ->) | (a & b & Hp & Hm & Hs)].
        * left. split; [by apply pr_iteT | done].
        * right. exists a, b. split_and!; [by apply pr_iteT | done | done].
    - destruct l as [a |].
      + destruct IH as (Hp & ->). split; [by apply pr_iteF | done].
      + destruct IH as [(Hp & ->) | (a & b & Hp & Hm & Hs)].
        * left. split; [by apply pr_iteF | done].
        * right. exists a, b. split_and!; [by apply pr_iteF | done | done].
    - destruct l as [a |].
      + destruct IH as (Hp & ->). split; [by apply pr_parL | done].
      + destruct IH as [(Hp & ->) | (a & b & Hp & Hm & Hs)].
        * left. split; [by apply pr_parL | done].
        * right. exists a, b. split_and!; [by apply pr_parL | done | done].
    - destruct l as [a |].
      + destruct IH as (Hp & ->). split; [by apply pr_parR | done].
      + destruct IH as [(Hp & ->) | (a & b & Hp & Hm & Hs)].
        * left. split; [by apply pr_parR | done].
        * right. exists a, b. split_and!; [by apply pr_parR | done | done].
    - destruct IHP as (HpP & _), IHQ as (HpQ & _).
      left. split; [by eapply pr_syncL | done].
    - destruct IHP as (HpP & _), IHQ as (HpQ & _).
      left. split; [by eapply pr_syncR | done].
    - destruct l as [a |]; simpl in IH.
      + destruct IH as (Hp & ->). split; [by apply pr_res | done].
      + destruct IH as [(Hp & ->) | (a & b & Hp & Hm & Hs)].
        * left. split; [by apply pr_res | done].
        * right. exists a, b. split_and!; [| done | done].
          apply pr_res. by rewrite (sync_lbl_ren _ _ Hs).
    - left. split; [apply pr_rec | done].
    - split_and!; [done | done | apply me_sop].
    - split_and!; [done | done | apply me_meas].
    - destruct IHP as (Hp & _), IHM as (_ & _ & Hm).
      right. exists (PrOp E qs), (MeSop (sop_act E qs)). split_and!; [done | done | constructor].
    - destruct IHP as (Hp & _), IHM as (_ & _ & Hm).
      right. exists (PrMeas M qs n), (M ⦅qs⦆! n). split_and!; [done | done | constructor].
    - destruct IHP as (Hp & _), IHM as (_ & _ & Hm).
      right. exists (PrInit qs), (MeSop (init_act qs)). split_and!; [done | done | constructor].
  Qed.

  Lemma conf_step_tau_inv ρ P s ρ' P' :
    ⟨ρ, P⟩ ⟶{τ}[s] ⟨ρ', P'⟩ →
    (P ⟶{τ}[s] P' ∧ ρ' = ρ) ∨ (∃ a b, P ⟶{ActExt a}[s] P' ∧ ρ ⟶ₘ{b} ρ' ∧ 𝔻ₘₑₘ b a).
  Proof. intros Hc. exact (conf_step_view _ _ _ _ _ _ Hc). Qed.

  Lemma conf_step_ext_inv ρ P s a ρ' P' :
    ⟨ρ, P⟩ ⟶{ActExt a}[s] ⟨ρ', P'⟩ → P ⟶{ActExt a}[s] P' ∧ ρ' = ρ.
  Proof. intros Hc. exact (conf_step_view _ _ _ _ _ _ Hc). Qed.

  Lemma conf_step_mem_inv ρ P s b ρ' P' :
    conf_step ρ P s (inr b) ρ' P' → s = CEps ∧ P' = P ∧ ρ ⟶ₘ{b} ρ'.
  Proof. intros Hc. exact (conf_step_view _ _ _ _ _ _ Hc). Qed.

  (* ** From the program and the memory to the configuration *)

  Lemma prog_step_conf ρ P s l P' : P ⟶{l}[s] P' → ⟨ρ, P⟩ ⟶{l}[s] ⟨ρ, P'⟩.
  Proof. induction 1; by econstructor. Qed.

  Lemma mem_step_conf ρ P b ρ' : ρ ⟶ₘ{b} ρ' → ⟨ρ, P⟩ ⟶ₘ{b} ⟨ρ', P⟩.
  Proof. inversion 1; subst; constructor. Qed.

  Lemma prog_step_mem_conf ρ P s a P' b ρ' :
    P ⟶{ActExt a}[s] P' → ρ ⟶ₘ{b} ρ' → 𝔻ₘₑₘ b a →
    ⟨ρ, P⟩ ⟶{τ}[s] ⟨ρ', P'⟩.
  Proof.
    intros Hp Hm Hs. destruct Hs.
    - eapply co_opCom; [by apply prog_step_conf | by apply mem_step_conf].
    - eapply co_measCom; [by apply prog_step_conf | by apply mem_step_conf].
    - eapply co_initCom; [by apply prog_step_conf | by apply mem_step_conf].
  Qed.

  (* ** The pre-harmony lemma *)

  Theorem pre_harmony ρ P s ρ' P' :
    ⟨ρ, P⟩ ⟶{τ}[s] ⟨ρ', P'⟩ ↔ ρ ∣ P ⟶{τ}[s] ρ' ∣ P'.
  Proof.
    split.
    - intros Hc. destruct (conf_step_tau_inv _ _ _ _ _ Hc)
        as [(Hp & ->) | (a & b & Hp & Hm & Hs)].
      + exact (par_right mem_step prog_step sync ρ P s τ P' Hp).
      + eapply par_sync; [exact Hm | exact Hp | exact Hs | constructor].
    - intros Hp. inversion Hp as [? ? ? l ? Hm El | ? ? ? l ? Hq El | ? ? c1 c2 ? μ1 μ2 ? ? Hm Hq Hs Hc]; subst.
      + destruct (mem_step_choice _ _ _ _ Hm) as (_ & b & ->). discriminate.
      + destruct l; [discriminate |]. by apply prog_step_conf.
      + destruct (mem_step_choice _ _ _ _ Hm) as (-> & _).
        rewrite (cmul_eps_l_inv _ _ Hc). by eapply prog_step_mem_conf.
  Qed.
End Memory_Harmony.
(* end hide *)
