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
(* * Harmony for lqCCS: [ρ • (P ∥ Q)] and [(P, ρ) ∥ Q]

    The silent steps of the configuration [ρ • (P ∥ Q)] in the density
    operator semantics ([qstep], Figure 9 of arXiv:2604.23756) are exactly
    the steps of the composition [(Prog, Mem) ∥ Test] ([cstep]), up to
    writing the configuration [(P', Q')] as [P' ∥ Q'] ([harmony]).  This
    generalises Lemma 5.1 of [Harmony_lemma/Harmony.v] (one program and its
    memory) to two programs sharing one memory.

    One hypothesis of the paper is used: processes are closed, so that
    substituting the outcome of a measurement in one component does not
    touch the others. *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list sets.
From TestingTheory Require Import Lifted Paths States pMust_almost_sure lqCCS_Quantum.
From TestingTheory Require Import lqCCS_Syntax lqCCS_Program lqCCS_Composition lqCCS_Semantics.
Definition closed (P : proc) : Prop := fv P = [].

Section Harmony.
  Context `{QM : QuantumModel}.

  (* ** Distributions under renamings *)

  Lemma dmap_dpoint {C D} (f : C → D) c w : dmap f (dpoint c w) = dpoint (f c) w.
  Proof. done. Qed.

  Lemma meas_dist_ext {C} M qs ρ (g g' : nat → C) :
    (∀ k, g k = g' k) → meas_dist M qs ρ g = meas_dist M qs ρ g'.
  Proof.
    intros E. unfold meas_dist. f_equal. apply map_ext. intros k. by rewrite E.
  Qed.

  Lemma dmap_meas_dist {C D} (f : C → D) M qs ρ (g : nat → C) :
    dmap f (meas_dist M qs ρ g) = meas_dist M qs ρ (λ k, f (g k)).
  Proof.
    unfold meas_dist, dmap, dsum, dpoint.
    induction (outs (meas_of M qs)) as [|k l IH]; simpl; [done|]. f_equal. exact IH.
  Qed.

  Lemma dpoint_inj {C} (c c' : C) w w' :
    dpoint c w = dpoint c' w' → c = c' ∧ w = w'.
  Proof. unfold dpoint. by intros [= -> ->]. Qed.

  (* ** Closedness and typing of components *)

  Lemma closed_app l1 l2 : l1 ++ l2 = @nil var → l1 = [] ∧ l2 = [].
  Proof. by destruct l1, l2. Qed.

  (* ** Steps of guards *)

  Lemma qgstep_vis_inv ρ g t a Δ :
    qgstep ρ g (LAct t a) Δ →
    ∃ P', gstep g (LAct t a) P' ∧ Δ = dpoint P' ρ.
  Proof.
    intros Hq. remember (LAct t a) as l eqn:El.
    induction Hq; simplify_eq.
    - eexists. split; [by constructor|done].
    - edestruct IHHq as (P' & Hs & ->); [done|]. exists P'. eauto using gstep.
    - edestruct IHHq as (P' & Hs & ->); [done|]. exists P'. eauto using gstep.
  Qed.

  Lemma qgstep_vis ρ g t a P' :
    gstep g (LAct t a) P' →
    (∀ E qs, a ≠ AOp E qs) → (∀ M qs x, a ≠ AMeas M qs x) →
    qgstep ρ g (LAct t a) (dpoint P' ρ).
  Proof.
    intros Hq. remember (LAct t a) as l eqn:El. revert t a El.
    induction Hq; intros t0 a0 El Hop Hmeas; simplify_eq.
    - by constructor.
    - by edestruct Hop.
    - by edestruct Hmeas.
    - eapply qg_sumL; eauto.
    - eapply qg_sumR; eauto.
  Qed.

  Definition gtau_view (ρ : St) (g : guard) (s : Sched) (Δ : dist proc) : Prop :=
    (∃ P', gstep g (LTau s) P' ∧ Δ = dpoint P' ρ)
    ∨ (∃ t E qs P', s = STag t ∧ gstep g (LAct t (AOp E qs)) P'
                    ∧ Δ = dpoint P' (sop_apply E qs ρ))
    ∨ (∃ t M qs x P', s = STag t ∧ gstep g (LAct t (AMeas M qs x)) P'
                      ∧ Δ = meas_dist M qs ρ (λ k, subst P' x (VNat k))).

  Lemma qgstep_tau_inv ρ g s Δ : qgstep ρ g (LTau s) Δ → gtau_view ρ g s Δ.
  Proof.
    intros Hq. remember (LTau s) as l eqn:El. revert s El.
    induction Hq; intros s0 El; simplify_eq.
    - left. eexists. split; [constructor|done].
    - left. eexists. split; [constructor|done].
    - right; left. do 4 eexists. split; [done|]. split; [by constructor|done].
    - right; right. do 5 eexists. split; [done|]. split; [by constructor|done].
    - destruct (IHHq s0 eq_refl) as [(P'&?&?)|[(t&E&qs&P'&?&?&?)|(t&M&qs&x&P'&?&?&?)]];
        [left|right;left|right;right]; repeat eexists; eauto using gstep.
    - destruct (IHHq s0 eq_refl) as [(P'&?&?)|[(t&E&qs&P'&?&?&?)|(t&M&qs&x&P'&?&?&?)]];
        [left|right;left|right;right]; repeat eexists; eauto using gstep.
  Qed.

  Lemma qgstep_tau ρ g s P' : gstep g (LTau s) P' → qgstep ρ g (LTau s) (dpoint P' ρ).
  Proof.
    intros Hq. remember (LTau s) as l eqn:El. revert s El.
    induction Hq; intros s0 El; simplify_eq; eauto using qgstep.
  Qed.

  Lemma qgstep_op ρ g t E qs P' :
    gstep g (LAct t (AOp E qs)) P' →
    qgstep ρ g (LTau (STag t)) (dpoint P' (sop_apply E qs ρ)).
  Proof.
    intros Hq. remember (LAct t (AOp E qs)) as l eqn:El. revert El.
    induction Hq; intros El; simplify_eq; eauto using qgstep.
  Qed.

  Lemma qgstep_meas ρ g t M qs x P' :
    gstep g (LAct t (AMeas M qs x)) P' →
    qgstep ρ g (LTau (STag t)) (meas_dist M qs ρ (λ k, subst P' x (VNat k))).
  Proof.
    intros Hq. remember (LAct t (AMeas M qs x)) as l eqn:El. revert El.
    induction Hq; intros El; simplify_eq; eauto using qgstep.
  Qed.

  (* ** Visible steps *)

  Lemma qstep_vis_inv ρ P t a Δ :
    qstep ρ P (LAct t a) Δ →
    ∃ P', pstep P (LAct t a) P' ∧ Δ = dpoint P' ρ.
  Proof.
    intros Hq. remember (LAct t a) as l eqn:El.
    induction Hq; simplify_eq.
    - match goal with Hg : qgstep _ _ _ _ |- _ =>
        destruct (qgstep_vis_inv _ _ _ _ _ Hg) as (P' & Hs & ->) end.
      exists P'. eauto using pstep.
    - eexists. split; [by constructor|done].
    - edestruct IHHq as (P' & Hs & ->); [done|].
      exists P'. eauto using pstep.
    - edestruct IHHq as (P' & Hs & ->); [done|].
      exists P'. eauto using pstep.
    - edestruct IHHq as (P' & Hs & ->); [done|].
      exists (PPar P' Q). rewrite dmap_dpoint. eauto using pstep.
    - edestruct IHHq as (Q' & Hs & ->); [done|].
      exists (PPar P Q'). rewrite dmap_dpoint. eauto using pstep.
    - edestruct IHHq as (P' & Hs & ->); [done|].
      exists (PRes P' c). rewrite dmap_dpoint. eauto using pstep.
  Qed.

  Lemma qstep_vis ρ P t a P' :
    pstep P (LAct t a) P' →
    (∀ E qs, a ≠ AOp E qs) → (∀ M qs x, a ≠ AMeas M qs x) →
    qstep ρ P (LAct t a) (dpoint P' ρ).
  Proof.
    intros Hq. remember (LAct t a) as l eqn:El. revert t a El.
    induction Hq; intros t0 a0 El Hop Hmeas; simplify_eq.
    - constructor. by eapply qgstep_vis.
    - by constructor.
    - eapply qs_iteT; eauto.
    - eapply qs_iteF; eauto.
    - rewrite <- (dmap_dpoint (λ P, PPar P Q)). apply qs_parL; eauto.
    - rewrite <- (dmap_dpoint (λ Q, PPar P Q)). apply qs_parR; eauto.
    - rewrite <- (dmap_dpoint (λ P, PRes P c)). apply qs_res; eauto.
  Qed.

  (* Invert the visible premises of a synchronisation. *)
  Ltac vis_inv :=
    repeat match goal with
      | Hx : qstep _ _ (LAct _ _) (dpoint _ _) |- _ =>
          apply qstep_vis_inv in Hx as (? & ? & ?)
      end;
    repeat match goal with
      | Hx : dpoint _ _ = dpoint _ _ |- _ => apply dpoint_inj in Hx as [? _]
      end;
    subst.

  (* ** Silent steps

      A silent step of [ρ • P] is a silent step of the program, a request
      of a superoperator, or a measurement. *)

  Definition tau_view (ρ : St) (P : proc) (s : Sched) (Δ : dist proc) : Prop :=
    (∃ P', pstep P (LTau s) P' ∧ Δ = dpoint P' ρ)
    ∨ (∃ t E qs P', s = STag t ∧ pstep P (LAct t (AOp E qs)) P'
                    ∧ Δ = dpoint P' (sop_apply E qs ρ))
    ∨ (∃ t M qs x P', s = STag t ∧ pstep P (LAct t (AMeas M qs x)) P'
                      ∧ Δ = meas_dist M qs ρ (λ k, subst P' x (VNat k))).

  Lemma qstep_tau_inv ρ P s Δ :
    closed P → qstep ρ P (LTau s) Δ → tau_view ρ P s Δ.
  Proof.
    intros Hc Hq. remember (LTau s) as l eqn:El. revert s El Hc.
    induction Hq; intros s0 El Hc; simplify_eq; unfold closed in *; simpl in Hc.
    - match goal with Hg : qgstep _ _ _ _ |- _ => destruct (qgstep_tau_inv _ _ _ _ Hg)
        as [(P'&?&?)|[(t&E&qs&P'&?&?&?)|(t&M&qs&x&P'&?&?&?)]] end;
        [left|right;left|right;right]; repeat eexists; eauto using pstep.
    - apply closed_app in Hc as [_ Hc]. apply closed_app in Hc as [Hc _].
      destruct (IHHq s0 eq_refl Hc) as [(P'&?&?)|[(t&E&qs&P'&?&?&?)|(t&M&qs&x&P'&?&?&?)]];
        [left|right;left|right;right]; repeat eexists; eauto using pstep.
    - apply closed_app in Hc as [_ Hc]. apply closed_app in Hc as [_ Hc].
      destruct (IHHq s0 eq_refl Hc) as [(P'&?&?)|[(t&E&qs&P'&?&?&?)|(t&M&qs&x&P'&?&?&?)]];
        [left|right;left|right;right]; repeat eexists; eauto using pstep.
    - (* parL *)
      apply closed_app in Hc as [HcP HcQ].
      destruct (IHHq s0 eq_refl HcP)
        as [(P'&Hs&->)|[(t&E&qs&P'&->&Hs&->)|(t&M&qs&x&P'&->&Hs&->)]].
      + left. exists (PPar P' Q). rewrite dmap_dpoint. eauto using pstep.
      + right; left. exists t, E, qs, (PPar P' Q). rewrite dmap_dpoint.
        split; [done|]. split; [|done]. by apply ps_parL.
      + right; right. exists t, M, qs, x, (PPar P' Q). split; [done|]. split.
        * by apply ps_parL.
        * rewrite dmap_meas_dist. apply meas_dist_ext. intros k. simpl.
          rewrite (subst_fresh Q); [done|]. rewrite HcQ. set_solver.
    - (* parR *)
      apply closed_app in Hc as [HcP HcQ].
      destruct (IHHq s0 eq_refl HcQ)
        as [(Q'&Hs&->)|[(t&E&qs&Q'&->&Hs&->)|(t&M&qs&x&Q'&->&Hs&->)]].
      + left. exists (PPar P Q'). rewrite dmap_dpoint. eauto using pstep.
      + right; left. exists t, E, qs, (PPar P Q'). rewrite dmap_dpoint.
        split; [done|]. split; [|done]. by apply ps_parR.
      + right; right. exists t, M, qs, x, (PPar P Q'). split; [done|]. split.
        * by apply ps_parR.
        * rewrite dmap_meas_dist. apply meas_dist_ext. intros k. simpl.
          rewrite (subst_fresh P); [done|]. rewrite HcP. set_solver.
    - (* syncL *)
      vis_inv. left. eexists. split; [by eapply ps_syncL|done].
    - (* syncR *)
      vis_inv. left. eexists. split; [by eapply ps_syncR|done].
    - (* res *)
      destruct (IHHq s0 eq_refl Hc)
        as [(P'&Hs&->)|[(t&E&qs&P'&->&Hs&->)|(t&M&qs&x&P'&->&Hs&->)]].
      + left. exists (PRes P' c). rewrite dmap_dpoint.
        split; [|done]. apply ps_res; [|done]. by intros (?&?&[[=]|[=]]).
      + right; left. exists t, E, qs, (PRes P' c). rewrite dmap_dpoint.
        split; [done|]. split; [|done]. apply ps_res; [|done]. by intros (?&?&[[=]|[=]]).
      + right; right. exists t, M, qs, x, (PRes P' c). split; [done|]. split.
        * apply ps_res; [|done]. by intros (?&?&[[=]|[=]]).
        * rewrite dmap_meas_dist. by apply meas_dist_ext.
  Qed.

  Lemma qstep_tau_prog ρ P s P' :
    pstep P (LTau s) P' → qstep ρ P (LTau s) (dpoint P' ρ).
  Proof.
    intros Hq. remember (LTau s) as l eqn:El. revert s El.
    induction Hq; intros s0 El; simplify_eq.
    - constructor. by apply qgstep_tau.
    - eapply qs_iteT; eauto.
    - eapply qs_iteF; eauto.
    - rewrite <- (dmap_dpoint (λ P, PPar P Q)). apply qs_parL; eauto.
    - rewrite <- (dmap_dpoint (λ Q, PPar P Q)). apply qs_parR; eauto.
    - eapply qs_syncL; (eapply qstep_vis; [eassumption|done|done]).
    - eapply qs_syncR; (eapply qstep_vis; [eassumption|done|done]).
    - rewrite <- (dmap_dpoint (λ P, PRes P c)). apply qs_res; eauto.
  Qed.

  Lemma qstep_op ρ P t E qs P' :
    pstep P (LAct t (AOp E qs)) P' →
    qstep ρ P (LTau (STag t)) (dpoint P' (sop_apply E qs ρ)).
  Proof.
    intros Hq. remember (LAct t (AOp E qs)) as l eqn:El. revert El.
    induction Hq; intros El; simplify_eq.
    - constructor. by apply qgstep_op.
    - eapply qs_iteT; eauto.
    - eapply qs_iteF; eauto.
    - rewrite <- (dmap_dpoint (λ P, PPar P Q)). apply qs_parL; eauto.
    - rewrite <- (dmap_dpoint (λ Q, PPar P Q)). apply qs_parR; eauto.
    - rewrite <- (dmap_dpoint (λ P, PRes P c)). apply qs_res; [|eauto].
      by intros (?&?&[[=]|[=]]).
  Qed.

  Lemma qstep_meas ρ P t M qs x P' :
    closed P → pstep P (LAct t (AMeas M qs x)) P' →
    qstep ρ P (LTau (STag t)) (meas_dist M qs ρ (λ k, subst P' x (VNat k))).
  Proof.
    intros Hc Hq. remember (LAct t (AMeas M qs x)) as l eqn:El. revert El Hc.
    induction Hq; intros El Hc; simplify_eq; unfold closed in *; simpl in Hc.
    - constructor. by apply qgstep_meas.
    - apply closed_app in Hc as [_ Hc]. apply closed_app in Hc as [Hc _].
      eapply qs_iteT; eauto.
    - apply closed_app in Hc as [_ Hc]. apply closed_app in Hc as [_ Hc].
      eapply qs_iteF; eauto.
    - apply closed_app in Hc as [HcP HcQ].
      erewrite meas_dist_ext.
      2:{ intros k. simpl. rewrite (subst_fresh Q); [done|]. rewrite HcQ. set_solver. }
      rewrite <- (dmap_meas_dist (λ P, PPar P Q)). apply qs_parL; eauto.
    - apply closed_app in Hc as [HcP HcQ].
      erewrite meas_dist_ext.
      2:{ intros k. simpl. rewrite (subst_fresh P); [done|]. rewrite HcP. set_solver. }
      rewrite <- (dmap_meas_dist (λ Q, PPar P Q)). apply qs_parR; eauto.
    - replace (meas_dist M qs ρ (λ k, subst (PRes P' c) x (VNat k)))
        with (meas_dist M qs ρ (λ k, PRes (subst P' x (VNat k)) c)) by reflexivity.
      rewrite <- (dmap_meas_dist (λ P, PRes P c)). apply qs_res; [|eauto].
      by intros (?&?&[[=]|[=]]).
  Qed.

  (* ** The Harmony lemma *)

  Theorem harmony ρ P Q s Δ :
    closed P → closed Q →
    qstep ρ (PPar P Q) (LTau s) Δ
    ↔ ∃ Δ', cstep ρ (P, Q) s Δ' ∧ Δ = dmap (λ C : conf, PPar C.1 C.2) Δ'.
  Proof.
    intros HcP HcQ. split.
    - intros Hq. inversion Hq; subst.
      + destruct (qstep_tau_inv ρ P s Δ0 HcP ltac:(done))
          as [(P'&Hs&->)|[(t&E&qs&P'&->&Hs&->)|(t&M&qs&x&P'&->&Hs&->)]].
        * eexists. split; [by apply cs_tauL|].
          by rewrite !dmap_dpoint.
        * eexists. split; [by eapply cs_opL|].
          by rewrite !dmap_dpoint.
        * eexists. split; [by eapply cs_measL|].
          by rewrite !dmap_meas_dist.
      + destruct (qstep_tau_inv ρ Q s Δ0 HcQ ltac:(done))
          as [(Q'&Hs&->)|[(t&E&qs&Q'&->&Hs&->)|(t&M&qs&x&Q'&->&Hs&->)]].
        * eexists. split; [by apply cs_tauR|].
          by rewrite !dmap_dpoint.
        * eexists. split; [by eapply cs_opR|].
          by rewrite !dmap_dpoint.
        * eexists. split; [by eapply cs_measR|].
          by rewrite !dmap_meas_dist.
      + vis_inv. eexists. split; [eapply cs_comLR; eauto|]. by rewrite dmap_dpoint.
      + vis_inv. eexists. split; [eapply cs_comRL; eauto|]. by rewrite dmap_dpoint.
    - intros (Δ' & Hc' & ->). inversion Hc'; subst.
      + rewrite dmap_dpoint. simpl.
        rewrite <- (dmap_dpoint (λ P, PPar P Q)). apply qs_parL.
        by apply qstep_tau_prog.
      + rewrite dmap_dpoint. simpl.
        rewrite <- (dmap_dpoint (λ Q, PPar P Q)). apply qs_parR.
        by apply qstep_tau_prog.
      + rewrite dmap_dpoint. simpl.
        rewrite <- (dmap_dpoint (λ P, PPar P Q)). apply qs_parL.
        by eapply qstep_op.
      + rewrite dmap_dpoint. simpl.
        rewrite <- (dmap_dpoint (λ Q, PPar P Q)). apply qs_parR.
        by eapply qstep_op.
      + rewrite dmap_meas_dist. simpl.
        rewrite <- (dmap_meas_dist (λ P, PPar P Q)). apply qs_parL.
        by eapply qstep_meas.
      + rewrite dmap_meas_dist. simpl.
        rewrite <- (dmap_meas_dist (λ Q, PPar P Q)). apply qs_parR.
        by eapply qstep_meas.
      + rewrite dmap_dpoint. simpl.
        eapply qs_syncL; (eapply qstep_vis; [eassumption|done|done]).
      + rewrite dmap_dpoint. simpl.
        eapply qs_syncR; (eapply qstep_vis; [eassumption|done|done]).
  Qed.
End Harmony.
(* end hide *)
