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
From stdpp Require Import base gmultiset countable decidable list.
From TestingTheory Require Import ActTau pMust_scheduled pMust_almost_sure pMust_smyth pMust_transfer pMust_canonical.
From TestingTheory Require Import lqCCS.General_definition.Algebra lqCCS.quantum_mem.Syntax lqCCS.quantum_mem.Quantum_Weights.
From TestingTheory Require Import lqCCS.lqCCS_prog.Syntax lqCCS.Helper.De_Brujin_lemmas lqCCS.General_definition.Parallel_choice_LTS lqCCS.quantum_mem.LTS lqCCS.lqCCS_prog.LTS lqCCS.lqCCS_par_Qmem.LTS lqCCS.lqCCS_process.LTS.LTS lqCCS.Helper.Conf_labels lqCCS.Helper.Label_lemmas lqCCS.Testing.Scheduled lqCCS.Testing.Observer_predicates lqCCS.Helper.Tag_lemmas.
From TestingTheory Require Import lqCCS.Testing.DistLTS lqCCS.Testing.Programs lqCCS.Testing.Observers lqCCS.Testing.Smyth_Soundness lqCCS.Testing.Canonical.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

Section Silent_Observers.
  Context `{lqP : lqCCS_Parameters}.

Section Detau.
  Context (U : unitary).

  Definition pdetau (π : prefix) : prefix :=
    match π with (t ∶ 𝛕) => t ∶ U ⦅[]⦆ | _ => π end.

  Fixpoint detau (P : prog) : prog :=
    match P with
    | t ∶ c ! e => t ∶ c ! e
    | If e Then P Else Q => If e Then detau P Else detau Q
    | P ∥ Q => detau P ∥ detau Q
    | ν P => ν (detau P)
    | PVar X => PVar X
    | t ∶ rec ∙ P => t ∶ rec ∙ detau P
    | PG g => PG (gdetau g)
    end
  with gdetau (g : guard) : guard :=
    match g with
    | 𝟘{es} => 𝟘{es}
    | 𝟙 => 𝟙
    | π ∙ P => pdetau π ∙ detau P
    | (g1 + g2)%lq => (gdetau g1 + gdetau g2)%lq
    end.

  Lemma pdetau_binds π : prefix_binds (pdetau π) = prefix_binds π.
  Proof. by destruct π. Qed.

  Lemma pdetau_subst i v π : pdetau (prefix_subst i v π) = prefix_subst i v (pdetau π).
  Proof. by destruct π. Qed.

  Lemma pdetau_shift i π : pdetau (prefix_shift i π) = prefix_shift i (pdetau π).
  Proof. by destruct π. Qed.

  Lemma pdetau_ren f π : pdetau (prefix_ren f π) = prefix_ren f (pdetau π).
  Proof. by destruct π. Qed.

  Lemma pdetau_tren f π : pdetau (prefix_tren f π) = prefix_tren f (pdetau π).
  Proof. by destruct π. Qed.

  Lemma detau_subst :
    (∀ P i v, detau (P ⁅ v // i ⁆ᵥ) = (detau P) ⁅ v // i ⁆ᵥ)
    ∧ (∀ g i v, gdetau (gsubst i v g) = gsubst i v (gdetau g)).
  Proof.
    apply prog_guard_ind; simpl; intros; try congruence.
    rewrite pdetau_subst, pdetau_binds. congruence.
  Qed.

  Lemma detau_shiftv :
    (∀ P i, detau (shiftv i P) = shiftv i (detau P))
    ∧ (∀ g i, gdetau (gshiftv i g) = gshiftv i (gdetau g)).
  Proof.
    apply prog_guard_ind; simpl; intros; try congruence.
    rewrite pdetau_shift, pdetau_binds. congruence.
  Qed.

  Lemma detau_shiftv_iter n Q : detau (Nat.iter n ⇧ᵥ Q) = Nat.iter n ⇧ᵥ (detau Q).
  Proof. induction n; simpl; [done|]. by rewrite (proj1 detau_shiftv), IHn. Qed.

  Lemma detau_ren :
    (∀ P f, detau (ren f P) = ren f (detau P)) ∧ (∀ g f, gdetau (gren f g) = gren f (gdetau g)).
  Proof.
    apply prog_guard_ind; simpl; intros; try congruence.
    rewrite pdetau_ren. congruence.
  Qed.

  Lemma detau_tren :
    (∀ P f, detau (tren f P) = tren f (detau P)) ∧ (∀ g f, gdetau (gtren f g) = gtren f (gdetau g)).
  Proof.
    apply prog_guard_ind; simpl; intros; try congruence.
    rewrite pdetau_tren. congruence.
  Qed.

  Lemma detau_rshift :
    (∀ P i, detau (rshift i P) = rshift i (detau P)) ∧ (∀ g i, gdetau (grshift i g) = grshift i (gdetau g)).
  Proof. apply prog_guard_ind; simpl; intros; try congruence. by case_decide. Qed.

  Lemma detau_pr_subst :
    (∀ P i Q, detau (P ⁅ Q // i ⁆ₚ) = (detau P) ⁅ detau Q // i ⁆ₚ)
    ∧ (∀ g i Q, gdetau (gpr_subst i g Q) = gpr_subst i (gdetau g) (detau Q)).
  Proof.
    apply prog_guard_ind; simpl; intros; try congruence.
    - f_equal. rewrite H. f_equal. apply (proj1 detau_ren).
    - by repeat case_decide.
    - by rewrite H, (proj1 detau_rshift).
    - rewrite H, pdetau_binds, detau_shiftv_iter. done.
  Qed.

  Definition lrel (𝜆 𝜆' : Labels prog_action) : Prop :=
    𝜆' = 𝜆 ∨ (𝜆 = τ ∧ 𝜆' = ⦅[]⦆ ! U).

  Lemma lrel_ext μ 𝜆' : lrel (ActExt μ) 𝜆' → 𝜆' = ActExt μ.
  Proof. by intros [->|[? _]]. Qed.

  Lemma detau_gstep g k 𝜆 P' : g ⟶ᵍ{𝜆}[k] P' → ∃ 𝜆', gdetau g ⟶ᵍ{𝜆'}[k] detau P' ∧ lrel 𝜆 𝜆'.
  Proof.
    induction 1 as [t P | t c v P | t U0 es qs P Hq | t M es qs n P Hq | t es qs P Hq | g1 g2 k 𝜆 P' Hgs IH | g1 g2 k 𝜆 P' Hgs IH]; simpl.
    - exists (⦅[]⦆ ! U). split; [by apply pg_op|by right].
    - exists (c ? v). split; [|by left]. rewrite (proj1 detau_subst). constructor.
    - exists (⦅qs⦆ ! U0). split; [by constructor|by left].
    - exists (M ⦅qs⦆? n). split; [|by left]. rewrite (proj1 detau_subst). by constructor.
    - exists (reinit qs). split; [by constructor|by left].
    - destruct IH as (𝜆' & Hs & Hl). exists 𝜆'. split; [by apply pg_sumL|done].
    - destruct IH as (𝜆' & Hs & Hl). exists 𝜆'. split; [by apply pg_sumR|done].
  Qed.

  Lemma detau_step P k 𝜆 P' : P ⟶ₚ{𝜆}[k] P' → ∃ 𝜆', detau P ⟶ₚ{𝜆'}[k] detau P' ∧ lrel 𝜆 𝜆'.
  Proof.
    induction 1 as [g k 𝜆 P' Hg | t c e v He | e P Q k 𝜆 P' He Hp IH | e P Q k 𝜆 Q' He Hp IH | P Q k 𝜆 P' Hp IH | P Q k 𝜆 Q' Hp IH | P Q t t' c v P' Q' Hp1 IH1 Hp2 IH2 | P Q t t' c v P' Q' Hp1 IH1 Hp2 IH2 | P k 𝜆 P' Hp IH | t P]; simpl.
    - destruct (detau_gstep _ _ _ _ Hg) as (𝜆' & Hs & Hl). exists 𝜆'. split; [by apply pr_guard|done].
    - exists (c ! v). split; [by constructor|by left].
    - destruct IH as (𝜆' & Hs & Hl). exists 𝜆'. split; [by apply pr_iteT|done].
    - destruct IH as (𝜆' & Hs & Hl). exists 𝜆'. split; [by apply pr_iteF|done].
    - destruct IH as (𝜆' & Hs & Hl). exists 𝜆'. split; [by apply pr_parL|done].
    - destruct IH as (𝜆' & Hs & Hl). exists 𝜆'. split; [by apply pr_parR|done].
    - destruct IH1 as (𝜆1 & Hs1 & ->%lrel_ext). destruct IH2 as (𝜆2 & Hs2 & ->%lrel_ext).
      exists τ. split; [by eapply pr_syncL|by left].
    - destruct IH1 as (𝜆1 & Hs1 & ->%lrel_ext). destruct IH2 as (𝜆2 & Hs2 & ->%lrel_ext).
      exists τ. split; [by eapply pr_syncR|by left].
    - destruct IH as (𝜆' & Hs & [->|[El ->]]).
      + exists 𝜆. split; [by apply pr_res|by left].
      + destruct 𝜆 as [μ|]; [destruct μ; discriminate El|].
        exists (⦅[]⦆ ! U). split; [by apply pr_res|by right].
    - exists τ. split; [|by left]. rewrite (proj1 detau_pr_subst). simpl.
      rewrite (proj1 detau_tren). exact (pr_rec t (detau P)).
  Qed.
  Lemma lrel_chan 𝜆 μ : lrel 𝜆 (ActExt μ) → (∀ qs, μ ≠ PrOp U qs) → 𝜆 = ActExt μ.
  Proof. intros [->|[_ U1]] Ha; [done|]. injection U1 as ->. by destruct (Ha []). Qed.

  Lemma detau_step_inv :
    (∀ P k 𝜆' X, detau P ⟶ₚ{𝜆'}[k] X → ∃ 𝜆 P', P ⟶ₚ{𝜆}[k] P' ∧ X = detau P' ∧ lrel 𝜆 𝜆')
    ∧ (∀ g k 𝜆' X, gdetau g ⟶ᵍ{𝜆'}[k] X → ∃ 𝜆 P', g ⟶ᵍ{𝜆}[k] P' ∧ X = detau P' ∧ lrel 𝜆 𝜆').
  Proof.
    apply prog_guard_ind; simpl.
    - intros t c e k 𝜆' X Hs. inversion Hs; subst. exists (c ! v), 𝟘. split; [by constructor|]. split; [done|by left].
    - intros e P IHP Q IHQ k 𝜆' X Hs. inversion Hs; subst.
      + match goal with Hp : detau P ⟶ₚ{_}[_] _ |- _ => destruct (IHP _ _ _ Hp) as (𝜆 & P1 & Hs' & -> & Hl) end.
        exists 𝜆, P1. split; [by apply pr_iteT|done].
      + match goal with Hp : detau Q ⟶ₚ{_}[_] _ |- _ => destruct (IHQ _ _ _ Hp) as (𝜆 & Q1 & Hs' & -> & Hl) end.
        exists 𝜆, Q1. split; [by apply pr_iteF|done].
    - intros P IHP Q IHQ k 𝜆' X Hs. inversion Hs; subst.
      + match goal with Hp : detau P ⟶ₚ{_}[_] _ |- _ => destruct (IHP _ _ _ Hp) as (𝜆 & P1 & Hs' & -> & Hl) end.
        exists 𝜆, (P1 ∥ Q). split; [by apply pr_parL|done].
      + match goal with Hp : detau Q ⟶ₚ{_}[_] _ |- _ => destruct (IHQ _ _ _ Hp) as (𝜆 & Q1 & Hs' & -> & Hl) end.
        exists 𝜆, (P ∥ Q1). split; [by apply pr_parR|done].
      + match goal with Hp : detau P ⟶ₚ{_}[_] _, Hq : detau Q ⟶ₚ{_}[_] _ |- _ =>
          destruct (IHP _ _ _ Hp) as (𝜆1 & P1 & Hs1 & -> & Hl1); destruct (IHQ _ _ _ Hq) as (𝜆2 & Q1 & Hs2 & -> & Hl2) end.
        apply lrel_chan in Hl1; [|done]. apply lrel_chan in Hl2; [|done]. subst.
        exists τ, (P1 ∥ Q1). split; [by eapply pr_syncL|]. split; [done|by left].
      + match goal with Hp : detau P ⟶ₚ{_}[_] _, Hq : detau Q ⟶ₚ{_}[_] _ |- _ =>
          destruct (IHP _ _ _ Hp) as (𝜆1 & P1 & Hs1 & -> & Hl1); destruct (IHQ _ _ _ Hq) as (𝜆2 & Q1 & Hs2 & -> & Hl2) end.
        apply lrel_chan in Hl1; [|done]. apply lrel_chan in Hl2; [|done]. subst.
        exists τ, (P1 ∥ Q1). split; [by eapply pr_syncR|]. split; [done|by left].
    - intros P IHP k 𝜆' X Hs. inversion Hs; subst.
      match goal with Hp : detau P ⟶ₚ{_}[_] _ |- _ => destruct (IHP _ _ _ Hp) as (𝜆0 & P1 & Hs' & -> & Hl) end.
      destruct Hl as [El|[-> El]].
      + exists 𝜆', (ν P1). split; [apply pr_res; by rewrite El|]. split; [done|by left].
      + destruct 𝜆' as [[c v|c v|U0 qs|M qs n|qs]|]; simpl in El; try discriminate El.
        injection El as -> ->. exists τ, (ν P1). split; [by apply pr_res|]. split; [done|by right].
    - intros X0 k 𝜆' X Hs. inversion Hs.
    - intros t P IHP k 𝜆' Y Hs. inversion Hs; subst. exists τ, (P ⁅ (t ∶ rec ∙ P)↑ ⁆ₚ).
      split; [constructor|]. split; [|by left].
      rewrite (proj1 detau_pr_subst). simpl. by rewrite (proj1 detau_tren).
    - intros g IHg k 𝜆' X Hs%prog_step_guard. destruct (IHg k 𝜆' X Hs) as (𝜆 & P' & Hs' & -> & Hl).
      exists 𝜆, P'. split; [by apply pr_guard|done].
    - intros es k 𝜆' X Hs. inversion Hs.
    - intros k 𝜆' X Hs. inversion Hs.
    - intros π P IHP k 𝜆' X Hs. destruct π as [t|t c|t U0 es|t M es|t e]; simpl in Hs; inversion Hs; subst.
      + match goal with Hq : eval_qubits [] = Some ?qs |- _ => change (Some (@nil qubit) = Some qs) in Hq; injection Hq as <- end.
        exists τ, P. split; [constructor|]. split; [done|by right].
      + exists (c ? v), (P ⁅ v ⁆ᵥ). split; [constructor|]. split; [by rewrite (proj1 detau_subst)|by left].
      + exists (⦅qs⦆ ! U0), P. split; [by constructor|]. split; [done|by left].
      + exists (M ⦅qs⦆? n), (P ⁅ VNat n ⁆ᵥ). split; [by constructor|]. split; [by rewrite (proj1 detau_subst)|by left].
      + eexists _, P. split; [by constructor|]. split; [done|by left].
    - intros g1 IH1 g2 IH2 k 𝜆' X Hs. inversion Hs; subst.
      + match goal with Hp : gdetau g1 ⟶ᵍ{_}[_] _ |- _ => destruct (IH1 _ _ _ Hp) as (𝜆 & P1 & Hs' & -> & Hl) end.
        exists 𝜆, P1. split; [by apply pg_sumL|done].
      + match goal with Hp : gdetau g2 ⟶ᵍ{_}[_] _ |- _ => destruct (IH2 _ _ _ Hp) as (𝜆 & P1 & Hs' & -> & Hl) end.
        exists 𝜆, P1. split; [by apply pg_sumR|done].
  Qed.
  Lemma detau_successb :
    (∀ P, successb (detau P) = successb P) ∧ (∀ g, gsuccessb (gdetau g) = gsuccessb g).
  Proof.
    apply prog_guard_ind; simpl; intros; try done; try congruence.
    destruct (eval e) as [[[]| |]|]; done.
  Qed.

  Lemma detau_success P : success (detau P) ↔ success P.
  Proof. unfold success. by rewrite (proj1 detau_successb). Qed.

  Lemma pdetau_idem π : pdetau (pdetau π) = pdetau π.
  Proof. by destruct π. Qed.

  Lemma detau_idem : (∀ P, detau (detau P) = detau P) ∧ (∀ g, gdetau (gdetau g) = gdetau g).
  Proof. apply prog_guard_ind; simpl; intros; try congruence. by rewrite pdetau_idem, H. Qed.

  Lemma detau_obs :
    (∀ P, obsb P = true → detau P = P) ∧ (∀ g, gobsb g = true → gdetau g = g).
  Proof.
    apply prog_guard_ind; simpl; intros; try done.
    - apply andb_prop in H1 as [H1 H2]. by rewrite H, H0.
    - apply andb_prop in H1 as [H1 H2]. by rewrite H, H0.
    - by rewrite H.
    - destruct π; simpl in *; try done; by rewrite H.
    - apply andb_prop in H1 as [H1 _]. apply andb_prop in H1 as [H1 H2]. by rewrite H, H0.
  Qed.
End Detau.

Section Sched_Detau.
  Context `{QM : QuantumModel} (U : unitary).
  Hypothesis HE : ∀ ρ, sop_apply U [] ρ = ρ.

  Notation dd := (map (λ x : prog * St, (detau U x.1, x.2))).

  Lemma lrel_not_op 𝜆 μ : lrel U 𝜆 (ActExt μ) → (∀ qs, μ ≠ PrOp U qs) → 𝜆 = ActExt μ.
  Proof. apply lrel_chan. Qed.

  Lemma meas_fwd R k M qs (ns : list (nat)) Rs :
    Forall2 (λ n R', R ⟶ₚ{M ⦅qs⦆? n}[k] R') ns Rs →
    Forall2 (λ n R', (detau U R) ⟶ₚ{M ⦅qs⦆? n}[k] R') ns (map (detau U) Rs).
  Proof.
    induction 1 as [|n R' ns Rs Hp _ IH]; simpl; constructor; [|done].
    destruct (detau_step U _ _ _ _ Hp) as (𝜆' & Hs & ->%lrel_ext). done.
  Qed.

  Lemma meas_bwd R k M qs (ns : list (nat)) Rs' :
    Forall2 (λ n R', (detau U R) ⟶ₚ{M ⦅qs⦆? n}[k] R') ns Rs' →
    ∃ Rs, Forall2 (λ n R', R ⟶ₚ{M ⦅qs⦆? n}[k] R') ns Rs ∧ map (detau U) Rs = Rs'.
  Proof.
    induction 1 as [|n R'' ns Rs' Hp _ (Rs & HF & <-)]; [by exists []|].
    destruct (proj1 (detau_step_inv U) _ _ _ _ Hp) as (𝜆 & P' & Hs & -> & Hl).
    apply lrel_not_op in Hl; [|done]. subst 𝜆. exists (P' :: Rs). split; [by constructor|done].
  Qed.

  Lemma map_zip_detau {A} (f : A → St) (ns : list A) (Rs : list prog) :
    dd (zip_with (λ n R', (R', f n)) ns Rs) = zip_with (λ n R', (R', f n)) ns (map (detau U) Rs).
  Proof. revert Rs. induction ns as [|n ns IH]; intros [|R Rs]; simpl; try done. by rewrite IH. Qed.

  Lemma sched_detau_fwd ρ R k Δ : sched_step ρ R k Δ → sched_step ρ (detau U R) k (dd Δ).
  Proof.
    intros Hs. inversion Hs as [R' Hp|U0 qs R' Hp|qs R' Hp|M qs Rs R0 Hp0 HF]; subst; simpl.
    - destruct (detau_step U _ _ _ _ Hp) as (𝜆' & Hs' & [->|[_ ->]]).
      + by apply ss_tau.
      + rewrite <- (HE ρ) at 2. by apply ss_op.
    - destruct (detau_step U _ _ _ _ Hp) as (𝜆' & Hs' & ->%lrel_ext). by apply ss_op.
    - destruct (detau_step U _ _ _ _ Hp) as (𝜆' & Hs' & ->%lrel_ext). by apply ss_init.
    - destruct (detau_step U _ _ _ _ Hp0) as (𝜆' & Hs' & ->%lrel_ext). rewrite map_zip_detau.
      eapply ss_meas; [exact Hs'|by apply meas_fwd].
  Qed.

  Lemma sched_detau_bwd ρ R k Δ' : sched_step ρ (detau U R) k Δ' → ∃ Δ, sched_step ρ R k Δ ∧ dd Δ = Δ'.
  Proof.
    intros Hs. inversion Hs as [R' Hp|U0 qs R' Hp|qs R' Hp|M qs Rs' R0 Hp0 HF]; subst.
    - destruct (proj1 (detau_step_inv U) _ _ _ _ Hp) as (𝜆 & P' & Hs1 & -> & [El|[_ El]]); [|discriminate El].
      subst 𝜆. exists [(P', ρ)]. split; [by apply ss_tau|done].
    - destruct (proj1 (detau_step_inv U) _ _ _ _ Hp) as (𝜆 & P' & Hs1 & -> & [El|[-> El]]).
      + subst 𝜆. exists [(P', sop_apply U0 qs ρ)]. split; [by apply ss_op|done].
      + injection El as -> ->. exists [(P', ρ)]. split; [by apply ss_tau|]. simpl. by rewrite HE.
    - destruct (proj1 (detau_step_inv U) _ _ _ _ Hp) as (𝜆 & P' & Hs1 & -> & Hl).
      apply lrel_not_op in Hl; [|done]. subst 𝜆. exists [(P', init_apply qs ρ)]. split; [by apply ss_init|done].
    - destruct (proj1 (detau_step_inv U) _ _ _ _ Hp0) as (𝜆 & P0 & Hs0 & -> & Hl).
      apply lrel_not_op in Hl; [|done]. subst 𝜆. destruct (meas_bwd _ _ _ _ _ _ HF) as (Rs & HFs & <-).
      eexists. split; [by eapply ss_meas|]. apply map_zip_detau.
  Qed.

  Definition fdetau (c : prog * prog) : prog * prog := (detau U c.1, detau U c.2).

  Notation fd := (map (λ x : prog * prog * St, (fdetau x.1, x.2))).

  Lemma dmap_fdetau (Δ : dist (prog * prog)) : dmap par_of (fd Δ) = dd (dmap par_of Δ).
  Proof. unfold dmap. rewrite !map_map. by apply map_ext. Qed.

  Lemma unpar_detau (Δ0 : dist prog) (Δ' : dist (prog * prog)) :
    dd Δ0 = dmap par_of Δ' → ∃ Δ, dmap par_of Δ = Δ0 ∧ fd Δ = Δ'.
  Proof.
    revert Δ'. induction Δ0 as [|[x ρ] Δ0 IH]; intros [|[[a b] ρ'] Δ'] Eq; simpl in Eq; try discriminate Eq; [by exists []|].
    injection Eq as U1 U2 E3. destruct (IH _ E3) as (Δ & <- & <-).
    destruct x as [| |u v| | | |]; simpl in U1; try discriminate U1. injection U1 as Ea Eb. subst a b ρ'.
    exists (((u, v), ρ) :: Δ). split; done.
  Qed.

  Lemma conf_detau_fwd ρ c k Δ : conf_sched ρ c k Δ → conf_sched ρ (fdetau c) k (fd Δ).
  Proof. unfold conf_sched. rewrite dmap_fdetau. apply sched_detau_fwd. Qed.

  Lemma conf_detau_bwd ρ c k Δ' : conf_sched ρ (fdetau c) k Δ' → ∃ Δ, conf_sched ρ c k Δ ∧ fd Δ = Δ'.
  Proof.
    unfold conf_sched. intros Hs. destruct (sched_detau_bwd ρ (par_of c) k _ Hs) as (Δ0 & Hs0 & U0).
    destruct (unpar_detau Δ0 Δ' U0) as (Δ & <- & <-). by exists Δ.
  Qed.

  Theorem smyth_detau (DC : dep_choice) (p q : prog * St) (T : prog) :
    smyth_le (SchedSts0 := lq_SchedSts) Stay (compose p T) (compose q T)
    ↔ smyth_le (SchedSts0 := lq_SchedSts) Stay (compose (detau U p.1, p.2) (detau U T)) (compose (detau U q.1, q.2) (detau U T)).
  Proof.
    exact (bisim_smyth lq_SchedSts lq_SchedSts fdetau (λ c, iff_sym (detau_success U c.2))
             conf_detau_fwd conf_detau_bwd DC (compose p T) (compose q T)).
  Qed.

  Theorem smyth_detau_obs (DC : dep_choice) (p q : prog * St) (T : prog) :
    smyth_le (SchedSts0 := lq_SchedSts) Stay (compose p T) (compose q T)
    ↔ smyth_le (SchedSts0 := lq_SchedSts) Stay (compose p (detau U T)) (compose q (detau U T)).
  Proof.
    rewrite (smyth_detau DC p q T), (smyth_detau DC p q (detau U T)), (proj1 (detau_idem U)). done.
  Qed.

  Definition obs_for_silent (p q : prog * St) (T : prog) : Prop := obs_for p q (detau U T).

  Theorem silent_observers (DC : dep_choice) (p q : prog * St) :
    ctx_pre_sm_on Stay (obs_for_silent p q) p q ↔ ctx_pre_sm_on Stay (obs_for p q) p q.
  Proof.
    split.
    - intros Hc T HT. apply Hc. unfold obs_for_silent. by rewrite (proj1 (detau_obs U) T (proj1 (proj1 (proj1 HT)))).
    - intros Hc T HT. apply (smyth_detau_obs DC p q T). exact (Hc _ HT).
  Qed.
End Sched_Detau.

End Silent_Observers.

(* end hide *)
