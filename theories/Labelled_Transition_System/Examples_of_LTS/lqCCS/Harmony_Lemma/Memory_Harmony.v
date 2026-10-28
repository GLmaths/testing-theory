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
From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list.
From TestingTheory Require Import lqCCS.Harmony_Lemma.Lifted lqCCS.Harmony_Lemma.Paths lqCCS.Harmony_Lemma.States pMust_almost_sure lqCCS.Language.Quantum.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.Program lqCCS.Language.Paper_LTS.

#[local] Open Scope lqccs_scope.

Section Memory_Harmony.
  Context `{QM : QuantumModel}.

  Definition conf_view (ρ : St) (P : proc) (l : prog_label) (ρ' : St) (P' : proc) : Prop :=
    match l with
    | PrTau _ => par_step (ρ, P) (ParProg l) (ρ', P')
    | PrAct _ a => chan_action a ∧ prog_step P l P' ∧ ρ' = ρ
    end.

  Lemma prog_step_guard g l P' : prog_step (PG g) l P' ↔ prog_gstep g l P'.
  Proof. split; [by inversion 1 | by constructor]. Qed.

  Lemma sync_not_chan c t a b : sync b a → ¬ chan_label c (PrAct t a).
  Proof. intros Hs (? & ? & [[= _ ->] | [= _ ->]]); inversion Hs. Qed.

  Lemma conf_gstep_view ρ g l ρ' P' :
    conf_gstep ρ g l ρ' P' → conf_view ρ (PG g) l ρ' P'.
  Proof.
    induction 1 as [t P | t E es qs P Hq | t M es x qs k P Hq | t c x v P
                   | g1 g2 l ρ' P' Hg IH | g1 g2 l ρ' P' Hg IH]; simpl.
    - apply par_prog, pr_guard, pg_tau.
    - eapply par_sync; [apply pr_guard, pg_op, Hq | apply me_op | apply sync_op].
    - eapply par_sync;
        [apply pr_guard, (pg_meas t M es x qs (code _ k) P Hq) | apply me_meas | apply sync_meas].
    - split; [by exists c, v; right | split; [apply pr_guard, pg_recv | done]].
    - destruct l as [s | t a]; simpl in IH.
      + inversion IH as [| ? ? ? ? Hp | ? ? ? ? t a b Hp Hm Hs]; subst.
        * apply par_prog, prog_step_guard, pg_sumL, prog_step_guard, Hp.
        * eapply par_sync; [apply prog_step_guard, pg_sumL, prog_step_guard, Hp | exact Hm | exact Hs].
      + destruct IH as (Ha & Hp & ->).
        split; [done | split; [apply prog_step_guard, pg_sumL, prog_step_guard, Hp | done]].
    - destruct l as [s | t a]; simpl in IH.
      + inversion IH as [| ? ? ? ? Hp | ? ? ? ? t a b Hp Hm Hs]; subst.
        * apply par_prog, prog_step_guard, pg_sumR, prog_step_guard, Hp.
        * eapply par_sync; [apply prog_step_guard, pg_sumR, prog_step_guard, Hp | exact Hm | exact Hs].
      + destruct IH as (Ha & Hp & ->).
        split; [done | split; [apply prog_step_guard, pg_sumR, prog_step_guard, Hp | done]].
  Qed.

  Lemma conf_step_view ρ P l ρ' P' :
    conf_step ρ P l ρ' P' → conf_view ρ P l ρ' P'.
  Proof.
    induction 1 as [g l ρ' P' Hg | t c e v He | e P Q l ρ' P' He Hc IH | e P Q l ρ' Q' He Hc IH
                   | P Q l ρ' P' Hc IH | P Q l ρ' Q' Hc IH
                   | P Q t t' c v P' Q' HcP IHP HcQ IHQ | P Q t t' c v P' Q' HcP IHP HcQ IHQ
                   | P c l ρ' P' Hl Hc IH]; simpl.
    - by apply conf_gstep_view.
    - split; [by exists c, v; left | split; [by apply pr_send | done]].
    - destruct l as [s | t a]; simpl in IH.
      + inversion IH as [| ? ? ? ? Hp | ? ? ? ? t a b Hp Hm Hs]; subst.
        * by apply par_prog, pr_iteT.
        * eapply par_sync; [by apply pr_iteT | exact Hm | exact Hs].
      + destruct IH as (Ha & Hp & ->). split; [done | split; [by apply pr_iteT | done]].
    - destruct l as [s | t a]; simpl in IH.
      + inversion IH as [| ? ? ? ? Hp | ? ? ? ? t a b Hp Hm Hs]; subst.
        * by apply par_prog, pr_iteF.
        * eapply par_sync; [by apply pr_iteF | exact Hm | exact Hs].
      + destruct IH as (Ha & Hp & ->). split; [done | split; [by apply pr_iteF | done]].
    - destruct l as [s | t a]; simpl in IH.
      + inversion IH as [| ? ? ? ? Hp | ? ? ? ? t a b Hp Hm Hs]; subst.
        * by apply par_prog, pr_parL.
        * eapply par_sync; [by apply pr_parL | exact Hm | exact Hs].
      + destruct IH as (Ha & Hp & ->). split; [done | split; [by apply pr_parL | done]].
    - destruct l as [s | t a]; simpl in IH.
      + inversion IH as [| ? ? ? ? Hp | ? ? ? ? t a b Hp Hm Hs]; subst.
        * by apply par_prog, pr_parR.
        * eapply par_sync; [by apply pr_parR | exact Hm | exact Hs].
      + destruct IH as (Ha & Hp & ->). split; [done | split; [by apply pr_parR | done]].
    - destruct IHP as (_ & HpP & _), IHQ as (_ & HpQ & _).
      apply par_prog. by eapply pr_syncL.
    - destruct IHP as (_ & HpP & _), IHQ as (_ & HpQ & _).
      apply par_prog. by eapply pr_syncR.
    - destruct l as [s | t a]; simpl in IH.
      + inversion IH as [| ? ? ? ? Hp | ? ? ? ? t a b Hp Hm Hs]; subst.
        * by apply par_prog, pr_res.
        * eapply par_sync; [apply pr_res; [by eapply sync_not_chan | exact Hp] | exact Hm | exact Hs].
      + destruct IH as (Ha & Hp & ->). split; [done | split; [by apply pr_res | done]].
  Qed.

  Definition prog_view (ρ : St) (P : proc) (l : prog_label) (P' : proc) : Prop :=
    match l with
    | PrTau _ => conf_step ρ P l ρ P'
    | PrAct t a =>
        (chan_action a → conf_step ρ P l ρ P')
        ∧ (∀ b ρ', mem_step ρ b ρ' → sync b a → conf_step ρ P (PrTau (STag t)) ρ' P')
    end.

  Lemma prog_gstep_view ρ g l P' : prog_gstep g l P' → prog_view ρ (PG g) l P'.
  Proof.
    induction 1 as [t P | t c x v P | t E es qs P Hq | t M es x qs n P Hq
                   | g1 g2 l P' Hg IH | g1 g2 l P' Hg IH]; simpl.
    - apply cs_guard, cg_tau.
    - split; [intros _; apply cs_guard, cg_recv | intros b ρ' _ Hs; inversion Hs].
    - split; [by intros (? & ? & [[=] | [=]]) |].
      intros b ρ' Hm Hs. inversion Hs; subst. inversion Hm; subst.
      by apply cs_guard, cg_op.
    - split; [by intros (? & ? & [[=] | [=]]) |].
      intros b ρ' Hm Hs. inversion Hs; subst. inversion Hm; subst.
      by apply cs_guard, cg_meas.
    - destruct l as [s | t a]; simpl in IH.
      + inversion IH; subst. by apply cs_guard, cg_sumL.
      + destruct IH as [Hc1 Hc2]. split.
        * intros Ha. specialize (Hc1 Ha). inversion Hc1; subst. by apply cs_guard, cg_sumL.
        * intros b ρ' Hm Hs. specialize (Hc2 b ρ' Hm Hs). inversion Hc2; subst.
          by apply cs_guard, cg_sumL.
    - destruct l as [s | t a]; simpl in IH.
      + inversion IH; subst. by apply cs_guard, cg_sumR.
      + destruct IH as [Hc1 Hc2]. split.
        * intros Ha. specialize (Hc1 Ha). inversion Hc1; subst. by apply cs_guard, cg_sumR.
        * intros b ρ' Hm Hs. specialize (Hc2 b ρ' Hm Hs). inversion Hc2; subst.
          by apply cs_guard, cg_sumR.
  Qed.

  Lemma prog_step_view ρ P l P' : prog_step P l P' → prog_view ρ P l P'.
  Proof.
    induction 1 as [g l P' Hg | t c e v He | e P Q l P' He Hp IH | e P Q l Q' He Hp IH
                   | P Q l P' Hp IH | P Q l Q' Hp IH
                   | P Q t t' c v P' Q' HpP IHP HpQ IHQ | P Q t t' c v P' Q' HpP IHP HpQ IHQ
                   | P c l P' Hl Hp IH]; simpl.
    - by apply prog_gstep_view.
    - split; [intros _; by apply cs_send | intros b ρ' _ Hs; inversion Hs].
    - destruct l as [s | t a]; simpl in IH.
      + by apply cs_iteT.
      + destruct IH as [Hc1 Hc2]. split; [intros Ha | intros b ρ' Hm Hs]; apply cs_iteT; eauto.
    - destruct l as [s | t a]; simpl in IH.
      + by apply cs_iteF.
      + destruct IH as [Hc1 Hc2]. split; [intros Ha | intros b ρ' Hm Hs]; apply cs_iteF; eauto.
    - destruct l as [s | t a]; simpl in IH.
      + by apply cs_parL.
      + destruct IH as [Hc1 Hc2]. split; [intros Ha | intros b ρ' Hm Hs]; apply cs_parL; eauto.
    - destruct l as [s | t a]; simpl in IH.
      + by apply cs_parR.
      + destruct IH as [Hc1 Hc2]. split; [intros Ha | intros b ρ' Hm Hs]; apply cs_parR; eauto.
    - destruct IHP as [HP _], IHQ as [HQ _].
      apply (cs_syncL ρ P Q t t' c v P' Q'); [apply HP; by exists c, v; left | apply HQ; by exists c, v; right].
    - destruct IHP as [HP _], IHQ as [HQ _].
      apply (cs_syncR ρ P Q t t' c v P' Q'); [apply HP; by exists c, v; right | apply HQ; by exists c, v; left].
    - destruct l as [s | t a]; simpl in IH.
      + by apply cs_res.
      + destruct IH as [Hc1 Hc2]. split.
        * intros Ha. apply cs_res; auto.
        * intros b ρ' Hm Hs. apply cs_res; [by intros (? & ? & [[=] | [=]]) | eauto].
  Qed.

  Theorem harmony ρ P s ρ' P' :
    conf_step ρ P (PrTau s) ρ' P' ↔ par_step (ρ, P) (ParProg (PrTau s)) (ρ', P').
  Proof.
    split.
    - intros Hc. exact (conf_step_view _ _ _ _ _ Hc).
    - intros Hp. inversion Hp as [| ? ? ? ? Hs | ? ? ? ? t a b Hs Hm Hy]; subst.
      + exact (prog_step_view _ _ _ _ Hs).
      + eapply (proj2 (prog_step_view _ _ _ _ Hs)); eauto.
  Qed.
End Memory_Harmony.
(* end hide *)
