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
    [conf_step_tau_inv], [conf_step_ext_inv], [prog_step_tau_conf],
    [prog_step_ext_conf] and [prog_step_mem_conf] are the two directions,
    rule by rule. *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list.
From TestingTheory Require Import ActTau.
From TestingTheory Require Import lqCCS.Harmony_Lemma.Lifted lqCCS.Harmony_Lemma.Paths lqCCS.Harmony_Lemma.States pMust_almost_sure lqCCS.Language.Quantum.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.LTS.

#[local] Open Scope lqccs_scope.

Lemma prog_step_guard g s l P' : prog_step (PG g) s l P' ↔ prog_gstep g s l P'.
Proof. split; [by inversion 1 | by constructor]. Qed.

Lemma sync_lbl_ren b a : sync b a → ren_lbl S (ActExt a) = ActExt a.
Proof. by destruct 1. Qed.

Lemma sync_ren_action b a : sync b a → sync b (ren_action S a).
Proof. by destruct 1; constructor. Qed.

Lemma chan_action_ren a : chan_action a → chan_action (ren_action S a).
Proof. intros (c & v & [-> | ->]); exists (ren_chan S c), v; [by left | by right]. Qed.

Lemma chan_action_ren_inv a : chan_action (ren_action S a) → chan_action a.
Proof.
  destruct a as [c v|c v| | |]; [by exists c, v; left | by exists c, v; right | | |];
    intros (? & ? & [[=] | [=]]).
Qed.

Lemma cmul_eps_l_inv c2 c : cmul CEps c2 c → c = c2.
Proof. inversion 1; done. Qed.

Section Memory_Harmony.
  Context `{QM : QuantumModel}.

  Lemma mem_step_choice ρ c l ρ' : mem_step ρ c l ρ' → c = CEps ∧ ∃ b, l = ActExt b.
  Proof. inversion 1; eauto. Qed.

  (* ** From the configuration to the program and the memory *)

  Definition conf_view (ρ : St) (P : proc) (s : choice) (l : Labels prog_action)
    (ρ' : St) (P' : proc) : Prop :=
    match l with
    | τ => (prog_step P s τ P' ∧ ρ' = ρ)
           ∨ (∃ t a b, s = CTag t ∧ prog_step P (CTag t) (ActExt a) P'
                       ∧ mem_step ρ CEps (ActExt b) ρ' ∧ sync b a)
    | ActExt a => chan_action a ∧ prog_step P s (ActExt a) P' ∧ ρ' = ρ
    end.

  Lemma conf_gstep_view ρ g s l ρ' P' :
    conf_gstep ρ g s l ρ' P' → conf_view ρ (PG g) s l ρ' P'.
  Proof.
    induction 1 as [t P | t E es qs P Hq | t M es qs k P Hq | t es qs P Hq | t c v P
                   | g1 g2 s l ρ' P' Hg IH | g1 g2 s l ρ' P' Hg IH]; simpl.
    - left. split; [apply pr_guard, pg_tau | done].
    - right. exists t, (PrOp E qs), (MeSop (SGate E) qs).
      split_and!; [done | by apply pr_guard, pg_op | apply (me_sop ρ (SGate E)) | constructor].
    - right. exists t, (PrMeas M qs (code _ k)), (MeMeas M qs (code _ k)).
      split_and!; [done | by apply pr_guard, pg_meas | apply me_meas | constructor].
    - right. exists t, (PrInit qs), (MeSop SInit qs).
      split_and!; [done | by apply pr_guard, pg_init | apply (me_sop ρ SInit) | constructor].
    - split_and!; [by exists c, v; right | apply pr_guard, pg_recv | done].
    - destruct l as [a |]; simpl in IH.
      + destruct IH as (Ha & Hp & ->).
        split_and!; [done | apply prog_step_guard, pg_sumL, prog_step_guard, Hp | done].
      + destruct IH as [(Hp & ->) | (t & a & b & -> & Hp & Hm & Hs)].
        * left. split; [apply prog_step_guard, pg_sumL, prog_step_guard, Hp | done].
        * right. exists t, a, b.
          split_and!; [done | apply prog_step_guard, pg_sumL, prog_step_guard, Hp | done | done].
    - destruct l as [a |]; simpl in IH.
      + destruct IH as (Ha & Hp & ->).
        split_and!; [done | apply prog_step_guard, pg_sumR, prog_step_guard, Hp | done].
      + destruct IH as [(Hp & ->) | (t & a & b & -> & Hp & Hm & Hs)].
        * left. split; [apply prog_step_guard, pg_sumR, prog_step_guard, Hp | done].
        * right. exists t, a, b.
          split_and!; [done | apply prog_step_guard, pg_sumR, prog_step_guard, Hp | done | done].
  Qed.

  Lemma conf_step_view ρ P s l ρ' P' :
    conf_step ρ P s l ρ' P' → conf_view ρ P s l ρ' P'.
  Proof.
    induction 1 as [g s l ρ' P' Hg | t c e v He | e P Q s l ρ' P' He Hc IH | e P Q s l ρ' Q' He Hc IH
                   | P Q s l ρ' P' Hc IH | P Q s l ρ' Q' Hc IH
                   | P Q t t' c v P' Q' HcP IHP HcQ IHQ | P Q t t' c v P' Q' HcP IHP HcQ IHQ
                   | P s l ρ' P' Hc IH | t X P]; simpl.
    - by apply conf_gstep_view.
    - split_and!; [by exists c, v; left | by apply pr_send | done].
    - destruct l as [a |]; simpl in IH.
      + destruct IH as (Ha & Hp & ->). split_and!; [done | by apply pr_iteT | done].
      + destruct IH as [(Hp & ->) | (t & a & b & -> & Hp & Hm & Hs)].
        * left. split; [by apply pr_iteT | done].
        * right. exists t, a, b. split_and!; [done | by apply pr_iteT | done | done].
    - destruct l as [a |]; simpl in IH.
      + destruct IH as (Ha & Hp & ->). split_and!; [done | by apply pr_iteF | done].
      + destruct IH as [(Hp & ->) | (t & a & b & -> & Hp & Hm & Hs)].
        * left. split; [by apply pr_iteF | done].
        * right. exists t, a, b. split_and!; [done | by apply pr_iteF | done | done].
    - destruct l as [a |]; simpl in IH.
      + destruct IH as (Ha & Hp & ->). split_and!; [done | by apply pr_parL | done].
      + destruct IH as [(Hp & ->) | (t & a & b & -> & Hp & Hm & Hs)].
        * left. split; [by apply pr_parL | done].
        * right. exists t, a, b. split_and!; [done | by apply pr_parL | done | done].
    - destruct l as [a |]; simpl in IH.
      + destruct IH as (Ha & Hp & ->). split_and!; [done | by apply pr_parR | done].
      + destruct IH as [(Hp & ->) | (t & a & b & -> & Hp & Hm & Hs)].
        * left. split; [by apply pr_parR | done].
        * right. exists t, a, b. split_and!; [done | by apply pr_parR | done | done].
    - destruct IHP as (_ & HpP & _), IHQ as (_ & HpQ & _).
      left. split; [by eapply pr_syncL | done].
    - destruct IHP as (_ & HpP & _), IHQ as (_ & HpQ & _).
      left. split; [by eapply pr_syncR | done].
    - destruct l as [a |]; simpl in IH.
      + destruct IH as (Ha & Hp & ->).
        split_and!; [by apply chan_action_ren_inv | by apply pr_res | done].
      + destruct IH as [(Hp & ->) | (t & a & b & -> & Hp & Hm & Hs)].
        * left. split; [by apply pr_res | done].
        * right. exists t, a, b. split_and!; [done | | done | done].
          apply pr_res. by rewrite (sync_lbl_ren _ _ Hs).
    - left. split; [apply pr_rec | done].
  Qed.

  (* ** From the program and the memory to the configuration *)

  Definition prog_view (ρ : St) (P : proc) (s : choice) (l : Labels prog_action) (P' : proc) : Prop :=
    match l with
    | τ => conf_step ρ P s τ ρ P'
    | ActExt a =>
        (chan_action a → conf_step ρ P s (ActExt a) ρ P')
        ∧ (∀ b ρ', mem_step ρ CEps (ActExt b) ρ' → sync b a → conf_step ρ P s τ ρ' P')
    end.

  Lemma prog_gstep_view ρ g s l P' : prog_gstep g s l P' → prog_view ρ (PG g) s l P'.
  Proof.
    induction 1 as [t P | t c v P | t E es qs P Hq | t M es qs n P Hq | t es qs P Hq
                   | g1 g2 s l P' Hg IH | g1 g2 s l P' Hg IH]; simpl.
    - apply co_guard, cg_tau.
    - split; [intros _; apply co_guard, cg_recv | intros b ρ' _ Hs; inversion Hs].
    - split; [by intros (? & ? & [[=] | [=]]) |].
      intros b ρ' Hm Hs. inversion Hs; subst. inversion Hm; subst.
      by apply co_guard, cg_op.
    - split; [by intros (? & ? & [[=] | [=]]) |].
      intros b ρ' Hm Hs. inversion Hs; subst. inversion Hm; subst.
      by apply co_guard, cg_meas.
    - split; [by intros (? & ? & [[=] | [=]]) |].
      intros b ρ' Hm Hs. inversion Hs; subst. inversion Hm; subst.
      by apply co_guard, cg_init.
    - destruct l as [a | s']; simpl in IH.
      + destruct IH as [Hc1 Hc2]. split.
        * intros Ha. specialize (Hc1 Ha). inversion Hc1; subst. by apply co_guard, cg_sumL.
        * intros b ρ' Hm Hs. specialize (Hc2 b ρ' Hm Hs). inversion Hc2; subst.
          by apply co_guard, cg_sumL.
      + inversion IH; subst. by apply co_guard, cg_sumL.
    - destruct l as [a | s']; simpl in IH.
      + destruct IH as [Hc1 Hc2]. split.
        * intros Ha. specialize (Hc1 Ha). inversion Hc1; subst. by apply co_guard, cg_sumR.
        * intros b ρ' Hm Hs. specialize (Hc2 b ρ' Hm Hs). inversion Hc2; subst.
          by apply co_guard, cg_sumR.
      + inversion IH; subst. by apply co_guard, cg_sumR.
  Qed.

  Lemma prog_step_view ρ P s l P' : prog_step P s l P' → prog_view ρ P s l P'.
  Proof.
    induction 1 as [g s l P' Hg | t c e v He | e P Q s l P' He Hp IH | e P Q s l Q' He Hp IH
                   | P Q s l P' Hp IH | P Q s l Q' Hp IH
                   | P Q t t' c v P' Q' HpP IHP HpQ IHQ | P Q t t' c v P' Q' HpP IHP HpQ IHQ
                   | P s l P' Hp IH | t X P]; simpl.
    - by apply prog_gstep_view.
    - split; [intros _; by apply co_send | intros b ρ' _ Hs; inversion Hs].
    - destruct l as [a |]; simpl in IH.
      + destruct IH as [Hc1 Hc2]. split; [intros Ha | intros b ρ' Hm Hs]; apply co_iteT; eauto.
      + by apply co_iteT.
    - destruct l as [a |]; simpl in IH.
      + destruct IH as [Hc1 Hc2]. split; [intros Ha | intros b ρ' Hm Hs]; apply co_iteF; eauto.
      + by apply co_iteF.
    - destruct l as [a |]; simpl in IH.
      + destruct IH as [Hc1 Hc2]. split; [intros Ha | intros b ρ' Hm Hs]; apply co_parL; eauto.
      + by apply co_parL.
    - destruct l as [a |]; simpl in IH.
      + destruct IH as [Hc1 Hc2]. split; [intros Ha | intros b ρ' Hm Hs]; apply co_parR; eauto.
      + by apply co_parR.
    - destruct IHP as [HP _], IHQ as [HQ _].
      apply (co_syncL ρ P Q t t' c v P' Q');
        [apply HP; by exists c, v; left | apply HQ; by exists c, v; right].
    - destruct IHP as [HP _], IHQ as [HQ _].
      apply (co_syncR ρ P Q t t' c v P' Q');
        [apply HP; by exists c, v; right | apply HQ; by exists c, v; left].
    - destruct l as [a |]; simpl in IH.
      + destruct IH as [Hc1 Hc2]. split.
        * intros Ha. apply co_res, Hc1. by apply chan_action_ren.
        * intros b ρ' Hm Hs. apply co_res. simpl. apply (Hc2 b ρ' Hm). by apply sync_ren_action.
      + by apply co_res.
    - apply co_rec.
  Qed.

  (* ** The two directions, rule by rule *)

  Lemma conf_step_tau_inv ρ P s ρ' P' :
    conf_step ρ P s τ ρ' P' →
    (prog_step P s τ P' ∧ ρ' = ρ)
    ∨ (∃ t a b, s = CTag t ∧ prog_step P (CTag t) (ActExt a) P'
                ∧ mem_step ρ CEps (ActExt b) ρ' ∧ sync b a).
  Proof. intros Hc. exact (conf_step_view _ _ _ _ _ _ Hc). Qed.

  Lemma conf_step_ext_inv ρ P s a ρ' P' :
    conf_step ρ P s (ActExt a) ρ' P' →
    chan_action a ∧ prog_step P s (ActExt a) P' ∧ ρ' = ρ.
  Proof. intros Hc. exact (conf_step_view _ _ _ _ _ _ Hc). Qed.

  Lemma prog_step_tau_conf ρ P s P' : prog_step P s τ P' → conf_step ρ P s τ ρ P'.
  Proof. intros Hp. exact (prog_step_view ρ _ _ _ _ Hp). Qed.

  Lemma prog_step_ext_conf ρ P s a P' :
    chan_action a → prog_step P s (ActExt a) P' → conf_step ρ P s (ActExt a) ρ P'.
  Proof. intros Ha Hp. exact (proj1 (prog_step_view ρ _ _ _ _ Hp) Ha). Qed.

  Lemma prog_step_mem_conf ρ P s a P' b ρ' :
    prog_step P s (ActExt a) P' → mem_step ρ CEps (ActExt b) ρ' → sync b a →
    conf_step ρ P s τ ρ' P'.
  Proof. intros Hp Hm Hs. exact (proj2 (prog_step_view ρ _ _ _ _ Hp) b ρ' Hm Hs). Qed.

  (* ** The pre-harmony lemma *)

  Theorem pre_harmony ρ P s ρ' P' :
    conf_step ρ P s τ ρ' P' ↔ (mem_step ∣[sync] prog_step) (ρ, P) s τ (ρ', P').
  Proof.
    split.
    - intros Hc. destruct (conf_step_tau_inv _ _ _ _ _ Hc)
        as [(Hp & ->) | (t & a & b & -> & Hp & Hm & Hs)].
      + exact (par_right mem_step prog_step sync ρ P s τ P' Hp).
      + eapply par_sync; [exact Hm | exact Hp | exact Hs | constructor].
    - intros Hp. inversion Hp as [? ? ? l ? Hm El | ? ? ? l ? Hq El | ? ? c1 c2 ? μ1 μ2 ? ? Hm Hq Hs Hc]; subst.
      + destruct (mem_step_choice _ _ _ _ Hm) as (_ & b & ->). discriminate.
      + destruct l; [discriminate |]. by apply prog_step_tau_conf.
      + destruct (mem_step_choice _ _ _ _ Hm) as (-> & _).
        rewrite (cmul_eps_l_inv _ _ Hc). by eapply prog_step_mem_conf.
  Qed.
End Memory_Harmony.
(* end hide *)
