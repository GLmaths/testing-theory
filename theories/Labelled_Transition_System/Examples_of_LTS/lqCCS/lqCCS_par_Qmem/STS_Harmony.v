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

(* * The Harmony lemma of lqCCS with memory relates the reductions to the silent transitions of the composition memory ∣ program ([STS_Harmony]). *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base gmultiset countable decidable list sets relations.
From TestingTheory Require Import ActTau.
From TestingTheory Require Import lqCCS.General_definition.Algebra lqCCS.quantum_mem.Syntax.
From TestingTheory Require Import lqCCS.lqCCS_prog.Syntax lqCCS.Helper.De_Brujin_lemmas lqCCS.General_definition.Parallel_choice_LTS lqCCS.quantum_mem.LTS lqCCS.lqCCS_prog.LTS lqCCS.lqCCS_par_Qmem.LTS lqCCS.lqCCS_process.LTS.LTS lqCCS.Helper.Conf_labels lqCCS.Helper.Label_lemmas.
From TestingTheory Require Import lqCCS.lqCCS_prog.Congruence lqCCS.lqCCS_process.STS.STS.

#[local] Open Scope lqccs_scope.
#[local] Open Scope par_scope.
#[local] Open Scope nat_scope.

(* ** Iterated restrictions and congruence *)

Section STS_Harmony.
  Context `{lqP : lqCCS_Parameters}.

Lemma cgr_resn n P Q : P ≡* Q → Ѵ n P ≡* Ѵ n Q.
Proof. intros H. induction n; simpl; [done|]. by apply cgr_res. Qed.

#[global] Instance resn_proper n : Proper (cgr ==> cgr) (Ѵ n).
Proof. intros P Q H. by apply cgr_resn. Qed.

(* [(Ѵ n P) ∥ Q ≡ Ѵ n (P ∥ Q⁺ⁿ)] *)
Lemma cgr_res_scope_n n P Q : (Ѵ n P) ∥ Q ≡* Ѵ n (P ∥ ren (Nat.add n) Q).
Proof.
  revert Q. induction n; intros Q; simpl.
  - rewrite <- (ren_id Q) at 1. apply cgr_par_r, cgr_ren. done.
  - etrans; [apply cgr_res_scope_rev|]. apply cgr_res.
    etrans; [apply IHn|]. apply cgr_resn, cgr_par_r. by rewrite ren_add_S.
Qed.

(* ** The shapes of the transitions *)

Lemma gstep_in_shape (g : guard) k c v Q' :
  g ⟶ᵍ{c ? v}[k] Q' →
  ∃ (t : tag) P K, k = {[+ t +]} ∧ g ≡ᵍ* ((t ∶ c ? ∙ P) + K) ∧ Q' = P ⁅ v ⁆ᵥ.
Proof.
  intros Hs. remember (c ? v) as 𝜆 eqn:El.
  induction Hs as [| | | | | ? ? ? ? ? ? IHHs | ? ? ? ? ? ? IHHs]; simplify_eq.
  - exists t, P, 𝟘{ [] }. split_and!; [done|apply gcgr_choice_nil_rev|done].
  - destruct (IHHs eq_refl) as (t & P & K & -> & Hg & ->).
    exists t, P, (K + g2)%lq. split_and!; [done| |done].
    by rewrite Hg, gcgr_choice_assoc.
  - destruct (IHHs eq_refl) as (t & P & K & -> & Hg & ->).
    exists t, P, (K + g1)%lq. split_and!; [done| |done].
    by rewrite gcgr_choice_com, Hg, gcgr_choice_assoc.
Qed.

Lemma TransitionShapeForOutput P k c v Q :
  P ⟶ₚ{c ! v}[k] Q →
  ∃ (t : tag) e R n, 〚 e 〛 = v ∧ k = {[+ t +]}
    ∧ P ≡* Ѵ n (t ∶ (ren_chan (Nat.add n) c) ! e ∥ R) ∧ Q ≡* Ѵ n (𝟘 ∥ R).
Proof.
  intros Hs. remember (c ! v) as 𝜆 eqn:El. revert c v El.
  induction Hs as [? ? ? ? H | ? ? ? ? ? | ? ? ? ? ? ? ? ? IHHs | ? ? ? ? ? ? ? ? IHHs | ? ? ? ? ? ? IHHs | ? ? ? ? ? ? IHHs | ? ? ? ? ? ? ? ? ? IHHs1 ? IHHs2 | ? ? ? ? ? ? ? ? ? IHHs1 ? IHHs2 | ? ? ? ? ? IHHs | ? ? ?]; intros c0 v0 El; simplify_eq.
  - exfalso. by eapply prog_gstep_not_out, pr_guard.
  - exists t, e, 𝟘, 0. split_and!; [done|done| |].
    + simpl. rewrite ren_chan_add_0. apply cgr_par_nil_rev.
    + simpl. apply cgr_par_nil_rev.
  - destruct (IHHs _ _ eq_refl) as (t & e' & R & n & He' & -> & HP & HQ).
    exists t, e', R, n. split_and!; [done|done| |done].
    etrans; [|exact HP]. by apply cgr_if_true.
  - destruct (IHHs _ _ eq_refl) as (t & e' & R & n & He' & -> & HP & HQ).
    exists t, e', R, n. split_and!; [done|done| |done].
    etrans; [|exact HP]. by apply cgr_if_false.
  - destruct (IHHs _ _ eq_refl) as (t & e & R & n & He & -> & HP & HQ).
    exists t, e, (R ∥ ren (Nat.add n) Q), n. split_and!; [done|done| |].
    + by rewrite HP, cgr_res_scope_n, cgr_par_assoc.
    + by rewrite HQ, cgr_res_scope_n, cgr_par_assoc.
  - destruct (IHHs _ _ eq_refl) as (t & e & R & n & He & -> & HP & HQ).
    exists t, e, (R ∥ ren (Nat.add n) P), n. split_and!; [done|done| |].
    + by rewrite cgr_par_com, HP, cgr_res_scope_n, cgr_par_assoc.
    + by rewrite cgr_par_com, HQ, cgr_res_scope_n, cgr_par_assoc.
  - destruct (IHHs _ _ eq_refl) as (t & e & R & n & He & -> & HP & HQ).
    exists t, e, R, (S n). split_and!; [done|done| |].
    + apply cgr_res. rewrite <- ren_chan_add_S. exact HP.
    + by apply cgr_res.
Qed.

Lemma TransitionShapeForInput P k c v Q :
  P ⟶ₚ{c ? v}[k] Q →
  ∃ (t : tag) P1 K R n, k = {[+ t +]}
    ∧ P ≡* Ѵ n (((t ∶ (ren_chan (Nat.add n) c) ? ∙ P1) + K) ∥ R)
    ∧ Q ≡* Ѵ n (P1 ⁅ v ⁆ᵥ ∥ R).
Proof.
  intros Hs. remember (c ? v) as 𝜆 eqn:El. revert c v El.
  induction Hs as [? ? ? ? H | ? ? ? ? ? | ? ? ? ? ? ? ? ? IHHs | ? ? ? ? ? ? ? ? IHHs | ? ? ? ? ? ? IHHs | ? ? ? ? ? ? IHHs | ? ? ? ? ? ? ? ? ? IHHs1 ? IHHs2 | ? ? ? ? ? ? ? ? ? IHHs1 ? IHHs2 | ? ? ? ? ? IHHs | ? ? ?]; intros c0 v0 El; simplify_eq.
  - destruct (gstep_in_shape _ _ _ _ _ H) as (t & P1 & K & -> & Hg & ->).
    exists t, P1, K, 𝟘, 0. split_and!; [done| |].
    + simpl. rewrite ren_chan_add_0. etrans; [by apply cgr_guard|]. apply cgr_par_nil_rev.
    + simpl. apply cgr_par_nil_rev.
  - destruct (IHHs _ _ eq_refl) as (t & P1 & K & R & n & -> & HP & HQ).
    exists t, P1, K, R, n. split_and!; [done| |done].
    etrans; [|exact HP]. by apply cgr_if_true.
  - destruct (IHHs _ _ eq_refl) as (t & P1 & K & R & n & -> & HP & HQ).
    exists t, P1, K, R, n. split_and!; [done| |done].
    etrans; [|exact HP]. by apply cgr_if_false.
  - destruct (IHHs _ _ eq_refl) as (t & P1 & K & R & n & -> & HP & HQ).
    exists t, P1, K, (R ∥ ren (Nat.add n) Q), n. split_and!; [done| |].
    + by rewrite HP, cgr_res_scope_n, cgr_par_assoc.
    + by rewrite HQ, cgr_res_scope_n, cgr_par_assoc.
  - destruct (IHHs _ _ eq_refl) as (t & P1 & K & R & n & -> & HP & HQ).
    exists t, P1, K, (R ∥ ren (Nat.add n) P), n. split_and!; [done| |].
    + by rewrite cgr_par_com, HP, cgr_res_scope_n, cgr_par_assoc.
    + by rewrite cgr_par_com, HQ, cgr_res_scope_n, cgr_par_assoc.
  - destruct (IHHs _ _ eq_refl) as (t & P1 & K & R & n & -> & HP & HQ).
    exists t, P1, K, R, (S n). split_and!; [done| |].
    + apply cgr_res. rewrite <- ren_chan_add_S. exact HP.
    + by apply cgr_res.
Qed.

(* ** Sums: the guard that moves can be brought in front *)

Lemma TransitionShapeForGuard (g : guard) k 𝜆 P' :
  g ⟶ᵍ{𝜆}[k] P' →
  ∃ π Q K, g ≡ᵍ* ((π ∙ Q) + K) ∧ (π ∙ Q) ⟶ₚ{𝜆}[k] P'.
Proof.
  intros Hs0. induction Hs0 as [t P | t c v P | t U es qs P Hq | t M es qs n P Hq | t e q P Hq
                 | g1 g2 k 𝜆 P' Hg IH | g1 g2 k 𝜆 P' Hg IH].
  - exists (t ∶ 𝛕), P, 𝟘{ [] }. split; [apply gcgr_choice_nil_rev|apply pr_tau].
  - exists (t ∶ c ?), P, 𝟘{ [] }. split; [apply gcgr_choice_nil_rev|apply pr_recv].
  - exists (t ∶ U ⦅es⦆), P, 𝟘{ [] }. split; [apply gcgr_choice_nil_rev|by apply pr_op].
  - exists (t ∶ M ⦅es ▷⦆), P, 𝟘{ [] }. split; [apply gcgr_choice_nil_rev|by apply pr_meas].
  - exists (t ∶ e := |0⟩), P, 𝟘{ [] }. split; [apply gcgr_choice_nil_rev|by apply pr_init].
  - destruct IH as (π & Q & K & Hc & Hs).
    exists π, Q, (K + g2)%lq. split; [|done].
    by rewrite Hc, gcgr_choice_assoc.
  - destruct IH as (π & Q & K & Hc & Hs).
    exists π, Q, (K + g1)%lq. split; [|done].
    by rewrite gcgr_choice_com, Hc, gcgr_choice_assoc.
Qed.

Definition quant_action (μ : prog_action) : Prop :=
  match μ with PrOut _ _ | PrIn _ _ => False | _ => True end.

Lemma TransitionShapeForQuantum P k μ Q :
  quant_action μ → P ⟶ₚ{ActExt μ}[k] Q →
  ∃ π P1 K R n Q1, P ≡* Ѵ n (((π ∙ P1) + K) ∥ R)
    ∧ (π ∙ P1) ⟶ₚ{ActExt μ}[k] Q1 ∧ Q ≡* Ѵ n (Q1 ∥ R).
Proof.
  intros Ha Hs. remember (ActExt μ) as 𝜆 eqn:El. revert μ Ha El.
  induction Hs as [? ? ? ? H | ? ? ? ? ? | ? ? ? ? ? ? ? ? IHHs | ? ? ? ? ? ? ? ? IHHs | ? ? ? ? ? ? IHHs | ? ? ? ? ? ? IHHs | ? ? ? ? ? ? ? ? ? IHHs1 ? IHHs2 | ? ? ? ? ? ? ? ? ? IHHs1 ? IHHs2 | ? ? ? ? ? IHHs | ? ? ?]; intros μ0 Ha El; simplify_eq.
  - destruct (TransitionShapeForGuard _ _ _ _ H) as (π & Q0 & K & Hg & Hs0).
    exists π, Q0, K, 𝟘, 0, P'. split_and!; [|done|].
    + simpl. etrans; [by apply cgr_guard|]. apply cgr_par_nil_rev.
    + simpl. apply cgr_par_nil_rev.
  - done.
  - destruct (IHHs _ Ha eq_refl) as (π & P1 & K & R & n & Q1 & HP & Hg & HQ).
    exists π, P1, K, R, n, Q1. split_and!; [|done|done].
    etrans; [|exact HP]. by apply cgr_if_true.
  - destruct (IHHs _ Ha eq_refl) as (π & P1 & K & R & n & Q1 & HP & Hg & HQ).
    exists π, P1, K, R, n, Q1. split_and!; [|done|done].
    etrans; [|exact HP]. by apply cgr_if_false.
  - destruct (IHHs _ Ha eq_refl) as (π & P1 & K & R & n & Q1 & HP & Hg & HQ).
    exists π, P1, K, (R ∥ ren (Nat.add n) Q), n, Q1. split_and!; [|done|].
    + by rewrite HP, cgr_res_scope_n, cgr_par_assoc.
    + by rewrite HQ, cgr_res_scope_n, cgr_par_assoc.
  - destruct (IHHs _ Ha eq_refl) as (π & P1 & K & R & n & Q1 & HP & Hg & HQ).
    exists π, P1, K, (R ∥ ren (Nat.add n) P), n, Q1. split_and!; [|done|].
    + by rewrite cgr_par_com, HP, cgr_res_scope_n, cgr_par_assoc.
    + by rewrite cgr_par_com, HQ, cgr_res_scope_n, cgr_par_assoc.
  - assert (E : ren_lbl S (ActExt μ0) = ActExt μ0) by (destruct μ0; simpl in *; done).
    destruct (IHHs _ Ha E) as (π & P1 & K & R & n & Q1 & HP & Hg & HQ).
    rewrite E in Hg.
    exists π, P1, K, R, (S n), Q1. split_and!; [by apply cgr_res|done|by apply cgr_res].
Qed.


Section STS.
  Context `{QM : QuantumModel}.

  (* ** Silent transitions of the composition memory ∣ program *)

  Lemma comp_tau_inv ρ P k ρ' P' :
    ρ ∣ P ⟶{τ}[k] ρ' ∣ P' →
    (P ⟶ₚ{τ}[k] P' ∧ ρ' = ρ) ∨ (∃ μ2 μ1, P ⟶ₚ{ActExt μ2}[k] P' ∧ ρ ⟶ₘ{μ1} ρ' ∧ 𝔻ₘₑₘ μ1 μ2).
  Proof.
    intros Hp. inversion Hp as [? ? ? 𝜆 ? Hm El | ? ? ? 𝜆 ? Hq El | ? ? c1 c2 μ1 μ2 ? ? Hm Hq Hs]; subst.
    - destruct (mem_step_choice _ _ _ _ Hm) as (_ & μ1 & ->). discriminate.
    - destruct 𝜆; [discriminate |]. by left.
    - destruct (mem_step_choice _ _ _ _ Hm) as (-> & _).
      rewrite (left_id_L ∅ (⊎) c2). right. by exists μ2, μ1.
  Qed.

  Lemma comp_tau_right ρ P k P' : P ⟶ₚ{τ}[k] P' → ρ ∣ P ⟶{τ}[k] ρ ∣ P'.
  Proof. intros Hp. exact (par_right mem_step prog_step sync ρ P k τ P' Hp). Qed.

  Lemma comp_tau_sync ρ P k μ2 P' μ1 ρ' :
    P ⟶ₚ{ActExt μ2}[k] P' → ρ ⟶ₘ{μ1} ρ' → 𝔻ₘₑₘ μ1 μ2 → ρ ∣ P ⟶{τ}[k] ρ' ∣ P'.
  Proof. intros Hp Hm Hs. rewrite <- (left_id_L ∅ (⊎) k). eapply par_sync; [exact Hm | exact Hp | exact Hs]. Qed.

  Lemma sts_resn n ρ P k ρ' P' : ⟨ρ, P⟩ ⟶[k] ⟨ρ', P'⟩ → ⟨ρ, Ѵ n P⟩ ⟶[k] ⟨ρ', Ѵ n P'⟩.
  Proof. intros Hs. induction n; simpl; [done|]. by apply sts_res. Qed.

  (* ** From the LTS to the STS *)

  (* A communication between an output under [n] restrictions and an input
      under [m] restrictions: the restrictions are extruded one by one. *)
  Lemma Com_shapes ρ n :
    ∀ m c e v t t' P1 K R R', 〚 e 〛 = v →
    ⟨ρ, Ѵ n (t ∶ (ren_chan (Nat.add n) c) ! e ∥ R)
        ∥ Ѵ m (((t' ∶ (ren_chan (Nat.add m) c) ? ∙ P1) + K) ∥ R')⟩
      ⟶[{[+ t; t' +]}] ⟨ρ, Ѵ n (𝟘 ∥ R) ∥ Ѵ m (P1 ⁅ v ⁆ᵥ ∥ R')⟩.
  Proof.
    induction n as [|n IHn]; intros m.
    - induction m as [|m IHm]; intros c e v t t' P1 K R R' He; cbn [Ѵ].
      + rewrite !ren_chan_add_0.
        eapply sts_cong; [apply cgr_par_inversion| |apply cgr_par_inversion].
        apply sts_par. by apply sts_com.
      + eapply sts_cong.
        * etrans; [apply cgr_par_com|].
          etrans; [apply cgr_res_scope_rev|]. apply cgr_res, cgr_par_com.
        * apply sts_res. cbn [ren gren]. rewrite ren_chan_add_0.
          specialize (IHm (ren_chan S c) e v t t' P1 K (ren S R) R' He). cbn [Ѵ] in IHm.
          rewrite ren_chan_add_0, ren_chan_add_S in IHm. exact IHm.
        * etrans; [apply cgr_res, cgr_par_com|].
          change (𝟘 ∥ ren S R) with (ren S (𝟘 ∥ R)).
          etrans; [apply cgr_res_scope|]. apply cgr_par_com.
    - intros c e v t t' P1 K R R' He. cbn [Ѵ].
      eapply sts_cong.
      + apply cgr_res_scope_rev.
      + apply sts_res. rewrite ren_resn. cbn [ren gren prefix_ren].
        rewrite ren_chan_liftn, <- ren_chan_add_S.
        apply (IHn m (ren_chan S c) e v t t' (ren (liftn m S) P1) (gren (liftn m S) K) R
                 (ren (liftn m S) R') He).
      + rewrite <- (proj1 ren_subst).
        replace (Ѵ m (ren (liftn m S) (P1 ⁅ v ⁆ᵥ) ∥ ren (liftn m S) R'))
          with (ren S (Ѵ m (P1 ⁅ v ⁆ᵥ ∥ R'))) by (rewrite ren_resn; done).
        apply cgr_res_scope.
  Qed.

  (* A silent transition of the program is a reduction. *)
  Lemma Taus_Implies_Reduction ρ P k P' : P ⟶ₚ{τ}[k] P' → ⟨ρ, P⟩ ⟶[k] ⟨ρ, P'⟩.
  Proof.
    intros Hp. remember (τ : Labels prog_action) as 𝜆 eqn:El. revert El.
    induction Hp as [g k 𝜆 P' Hg | t c e v He | e P Q k 𝜆 P' He Hp IH | e P Q k 𝜆 Q' He Hp IH
                   | P Q k 𝜆 P' Hp IH | P Q k 𝜆 Q' Hp IH
                   | P Q t t' c v P' Q' HpP _ HpQ _ | P Q t t' c v P' Q' HpP _ HpQ _
                   | P k 𝜆 P' Hp IH | t P]; intros El; subst.
    - destruct (TransitionShapeForGuard _ _ _ _ Hg) as (π & Q & K & Hcg & Hs).
      eapply sts_cong; [apply cgr_guard, Hcg| |reflexivity].
      apply prog_step_guard in Hs. inversion Hs; subst. apply sts_tau.
    - discriminate.
    - eapply sts_cong; [by apply cgr_if_true | by apply IH | reflexivity].
    - eapply sts_cong; [by apply cgr_if_false | by apply IH | reflexivity].
    - apply sts_par. by apply IH.
    - eapply sts_cong; [apply cgr_par_com | apply sts_par; by apply IH | apply cgr_par_com].
    - destruct (TransitionShapeForOutput _ _ _ _ _ HpP) as (t0 & e & R & n & He & Et & HP1 & HP2).
      destruct (TransitionShapeForInput _ _ _ _ _ HpQ) as (t0' & P1 & K & R' & m & Et' & HQ1 & HQ2).
      simplify_eq.
      eapply sts_cong; [by apply cgr_fullpar | by apply Com_shapes | symmetry; by apply cgr_fullpar].
    - destruct (TransitionShapeForInput _ _ _ _ _ HpP) as (t0 & P1 & K & R & n & Et & HP1 & HP2).
      destruct (TransitionShapeForOutput _ _ _ _ _ HpQ) as (t0' & e & R' & m & He & Et' & HQ1 & HQ2).
      simplify_eq. rewrite (comm disj_union {[+ t0 +]}).
      eapply sts_cong.
      + etrans; [apply cgr_par_com|]. by apply cgr_fullpar.
      + by apply Com_shapes.
      + etrans; [apply cgr_par_com|]. symmetry. by apply cgr_fullpar.
    - apply sts_res. by apply IH.
    - apply sts_rec.
  Qed.

  (* A quantum action of the program answered by the memory is a reduction. *)
  Lemma Quantum_Implies_Reduction ρ P k μ2 P' μ1 ρ' :
    P ⟶ₚ{ActExt μ2}[k] P' → ρ ⟶ₘ{μ1} ρ' → 𝔻ₘₑₘ μ1 μ2 → ⟨ρ, P⟩ ⟶[k] ⟨ρ', P'⟩.
  Proof.
    intros Hp Hm Hd. assert (Ha : quant_action μ2) by (by destruct Hd).
    destruct (TransitionShapeForQuantum _ _ _ _ Ha Hp) as (π & P1 & K & R & n & Q1 & HP & Hg & HQ).
    eapply sts_cong; [exact HP| |symmetry; exact HQ].
    apply sts_resn, sts_par.
    apply prog_step_guard in Hg. inversion Hd; subst; inversion Hm; subst; inversion Hg; subst.
    - by apply sts_op.
    - by apply sts_meas.
    - by apply sts_init.
  Qed.

  Lemma Internal_Implies_Reduction ρ P k ρ' P' :
    ρ ∣ P ⟶{τ}[k] ρ' ∣ P' → ⟨ρ, P⟩ ⟶[k] ⟨ρ', P'⟩.
  Proof.
    intros Hc. destruct (comp_tau_inv _ _ _ _ _ Hc) as [(Hp & ->)|(μ2 & μ1 & Hp & Hm & Hd)].
    - by apply Taus_Implies_Reduction.
    - by eapply Quantum_Implies_Reduction.
  Qed.

  (* ** From the STS to the LTS *)

  Lemma Reduction_Implies_Internal ρ P k ρ' Q :
    ⟨ρ, P⟩ ⟶[k] ⟨ρ', Q⟩ → ∃ Q', ρ ∣ P ⟶{τ}[k] ρ' ∣ Q' ∧ Q' ≡* Q.
  Proof.
    induction 1 as [ρ t c e v t' P K He | ρ t P K | ρ t U es qs P K Hq | ρ t e q P K Hq
                   | ρ t M es qs n P K Hq Hk | ρ t P
                   | ρ P k ρ' P' Q _ (P'' & Hc & HP)
                   | ρ P k ρ' P' _ (P'' & Hc & HP)
                   | ρ P P1 k ρ' Q1 Q Hcg _ (Q1' & Hc & HQ) Hcg'].
    - exists (𝟘 ∥ P ⁅ v ⁆ᵥ). split; [|reflexivity]. apply comp_tau_right.
      eapply pr_syncL; [by apply pr_send | apply pr_sumL, pr_recv].
    - exists P. split; [|reflexivity]. apply comp_tau_right.
      apply pr_sumL, pr_tau.
    - exists P. split; [|reflexivity].
      eapply comp_tau_sync; [by apply pr_sumL, pr_op | apply (me_sop ρ (sop_act U qs)) | constructor].
    - exists P. split; [|reflexivity].
      eapply comp_tau_sync; [by apply pr_sumL, pr_init | apply (me_sop ρ (init_act q)) | constructor].
    - exists (P ⁅ VNat n ⁆ᵥ). split; [|reflexivity].
      eapply comp_tau_sync; [by apply pr_sumL, pr_meas | by apply me_meas | constructor].
    - exists (P ⁅ (t ∶ rec ∙ P)↑ ⁆ₚ). split; [|reflexivity]. apply comp_tau_right, pr_rec.
    - exists (P'' ∥ Q). split; [|by apply cgr_par].
      destruct (comp_tau_inv _ _ _ _ _ Hc) as [(Hp & ->)|(μ2 & μ1 & Hp & Hm & Hd)].
      + apply comp_tau_right. by apply pr_parL.
      + eapply comp_tau_sync; [by apply pr_parL | exact Hm | exact Hd].
    - exists (ν P''). split; [|by apply cgr_res].
      destruct (comp_tau_inv _ _ _ _ _ Hc) as [(Hp & ->)|(μ2 & μ1 & Hp & Hm & Hd)].
      + apply comp_tau_right. by apply pr_res.
      + eapply comp_tau_sync; [|exact Hm | exact Hd].
        apply pr_res. by rewrite (sync_lbl_ren _ _ Hd).
    - destruct (comp_tau_inv _ _ _ _ _ Hc) as [(Hp & ->)|(μ2 & μ1 & Hp & Hm & Hd)];
        destruct (Congruence_Respects_Transition P _ _ _ (ex_intro _ P1 (conj Hcg Hp))) as (Q' & Hp' & HQ');
        exists Q'.
      + split; [by apply comp_tau_right|]. etrans; [exact HQ'|]. etrans; [exact HQ|exact Hcg'].
      + split; [by eapply comp_tau_sync|]. etrans; [exact HQ'|]. etrans; [exact HQ|exact Hcg'].
  Qed.

  (* ** The Harmony lemma *)

  Theorem STS_Harmony ρ P k ρ' Q :
    ⟨ρ, P⟩ ⟶[k] ⟨ρ', Q⟩ ↔ ∃ Q', ρ ∣ P ⟶{τ}[k] ρ' ∣ Q' ∧ Q' ≡* Q.
  Proof.
    split; [apply Reduction_Implies_Internal|].
    intros (Q' & Hc & HQ).
    eapply sts_cong; [reflexivity | by apply Internal_Implies_Reduction | exact HQ].
  Qed.

  (* The same statement on the LTS given directly on the configurations. *)
End STS.


End STS_Harmony.


(* end hide *)
