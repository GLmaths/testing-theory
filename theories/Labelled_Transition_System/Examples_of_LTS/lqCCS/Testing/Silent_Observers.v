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
From TestingTheory Require Import ActTau pMust_scheduled pMust_almost_sure pMust_smyth pMust_transfer pMust_canonical.
From TestingTheory Require Import lqCCS.Language.Algebra lqCCS.Language.Quantum lqCCS.Language.Quantum_Weights.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.LTS lqCCS.Testing.Scheduled.
From TestingTheory Require Import lqCCS.Testing.DistLTS lqCCS.Testing.Programs lqCCS.Testing.Observers lqCCS.Testing.Smyth_Soundness lqCCS.Testing.Canonical.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

Section Detau.
  Context (E : sop).

  Definition pdetau (𝜆 : prefix) : prefix :=
    match 𝜆 with PTau t => POp t E [] | _ => 𝜆 end.

  Fixpoint detau (P : proc) : proc :=
    match P with
    | PSend t c e => PSend t c e
    | PIte e P Q => PIte e (detau P) (detau Q)
    | P ∥ Q => detau P ∥ detau Q
    | ν P => ν (detau P)
    | PVar X => PVar X
    | PRec t X P => PRec t X (detau P)
    | PG g => PG (gdetau g)
    end
  with gdetau (g : guard) : guard :=
    match g with
    | GNil es => GNil es
    | ① => ①
    | 𝜆 ∙ P => pdetau 𝜆 ∙ detau P
    | (g1 + g2)%lq => (gdetau g1 + gdetau g2)%lq
    end.

  Lemma pdetau_binds 𝜆 : prefix_binds (pdetau 𝜆) = prefix_binds 𝜆.
  Proof. by destruct 𝜆. Qed.

  Lemma pdetau_subst k v 𝜆 : pdetau (prefix_subst k v 𝜆) = prefix_subst k v (pdetau 𝜆).
  Proof. by destruct 𝜆. Qed.

  Lemma pdetau_shift k 𝜆 : pdetau (prefix_shift k 𝜆) = prefix_shift k (pdetau 𝜆).
  Proof. by destruct 𝜆. Qed.

  Lemma pdetau_ren f 𝜆 : pdetau (prefix_ren f 𝜆) = prefix_ren f (pdetau 𝜆).
  Proof. by destruct 𝜆. Qed.

  Lemma pdetau_tren f 𝜆 : pdetau (prefix_tren f 𝜆) = prefix_tren f (pdetau 𝜆).
  Proof. by destruct 𝜆. Qed.

  Lemma detau_subst :
    (∀ P k v, detau (subst k v P) = subst k v (detau P))
    ∧ (∀ g k v, gdetau (gsubst k v g) = gsubst k v (gdetau g)).
  Proof.
    apply proc_guard_ind; simpl; intros; try congruence.
    rewrite pdetau_subst, pdetau_binds. congruence.
  Qed.

  Lemma detau_shiftv :
    (∀ P k, detau (shiftv k P) = shiftv k (detau P))
    ∧ (∀ g k, gdetau (gshiftv k g) = gshiftv k (gdetau g)).
  Proof.
    apply proc_guard_ind; simpl; intros; try congruence.
    rewrite pdetau_shift, pdetau_binds. congruence.
  Qed.

  Lemma detau_shiftv_iter n Q : detau (Nat.iter n (shiftv 0) Q) = Nat.iter n (shiftv 0) (detau Q).
  Proof. induction n; simpl; [done|]. by rewrite (proj1 detau_shiftv), IHn. Qed.

  Lemma detau_ren :
    (∀ P f, detau (ren f P) = ren f (detau P)) ∧ (∀ g f, gdetau (gren f g) = gren f (gdetau g)).
  Proof.
    apply proc_guard_ind; simpl; intros; try congruence.
    rewrite pdetau_ren. congruence.
  Qed.

  Lemma detau_tren :
    (∀ P f, detau (tren f P) = tren f (detau P)) ∧ (∀ g f, gdetau (gtren f g) = gtren f (gdetau g)).
  Proof.
    apply proc_guard_ind; simpl; intros; try congruence.
    rewrite pdetau_tren. congruence.
  Qed.

  Lemma detau_pr_subst X :
    (∀ P Q, detau (P ⦃ Q // X ⦄) = (detau P) ⦃ detau Q // X ⦄)
    ∧ (∀ g Q, gdetau (gpr_subst X g Q) = gpr_subst X (gdetau g) (detau Q)).
  Proof.
    apply proc_guard_ind; simpl; intros; try congruence.
    - f_equal. rewrite H. f_equal. apply (proj1 detau_ren).
    - by case_decide.
    - case_decide; simpl; congruence.
    - rewrite H, pdetau_binds, detau_shiftv_iter. done.
  Qed.

  Definition lrel (l l' : Labels prog_action) : Prop :=
    l' = l ∨ (l = τ ∧ l' = ActExt (PrOp E [])).

  Lemma lrel_ext a l' : lrel (ActExt a) l' → l' = ActExt a.
  Proof. by intros [->|[? _]]. Qed.

  Lemma detau_step P s l P' : P ⟶{l}[s] P' → ∃ l', detau P ⟶{l'}[s] detau P' ∧ lrel l l'.
  Proof.
    induction 1 as [t P | t c v P | t E0 es qs P Hq | t M es qs n P Hq | t es qs P Hq | g1 g2 s l P' Hgs IH | g1 g2 s l P' Hgs IH | t c e v He | e P Q s l P' He Hp IH | e P Q s l Q' He Hp IH | P Q s l P' Hp IH | P Q s l Q' Hp IH | P Q t t' c v P' Q' Hp1 IH1 Hp2 IH2 | P Q t t' c v P' Q' Hp1 IH1 Hp2 IH2 | P s l P' Hp IH | t X P]; simpl.
    - exists (ActExt (PrOp E [])). split; [by apply pr_op|by right].
    - exists (c ? v). split; [|by left]. rewrite (proj1 detau_subst). constructor.
    - exists (E0 ⦅qs⦆). split; [by constructor|by left].
    - exists (M ⦅qs⦆? n). split; [|by left]. rewrite (proj1 detau_subst). by constructor.
    - exists (init ⦅qs⦆). split; [by constructor|by left].
    - destruct IH as (l' & Hs & Hl). exists l'. split; [by apply pr_sumL|done].
    - destruct IH as (l' & Hs & Hl). exists l'. split; [by apply pr_sumR|done].
    - exists (c ! v). split; [by constructor|by left].
    - destruct IH as (l' & Hs & Hl). exists l'. split; [by apply pr_iteT|done].
    - destruct IH as (l' & Hs & Hl). exists l'. split; [by apply pr_iteF|done].
    - destruct IH as (l' & Hs & Hl). exists l'. split; [by apply pr_parL|done].
    - destruct IH as (l' & Hs & Hl). exists l'. split; [by apply pr_parR|done].
    - destruct IH1 as (l1 & Hs1 & ->%lrel_ext). destruct IH2 as (l2 & Hs2 & ->%lrel_ext).
      exists τ. split; [by eapply pr_syncL|by left].
    - destruct IH1 as (l1 & Hs1 & ->%lrel_ext). destruct IH2 as (l2 & Hs2 & ->%lrel_ext).
      exists τ. split; [by eapply pr_syncR|by left].
    - destruct IH as (l' & Hs & [->|[El ->]]).
      + exists l. split; [by apply pr_res|by left].
      + destruct l as [a|]; [destruct a; discriminate El|].
        exists (ActExt (PrOp E [])). split; [by apply pr_res|by right].
    - exists τ. split; [|by left]. rewrite (proj1 (detau_pr_subst X)). simpl.
      rewrite (proj1 detau_tren). exact (pr_rec t X (detau P)).
  Qed.
  Lemma lrel_chan l a : lrel l (ActExt a) → (∀ qs, a ≠ PrOp E qs) → l = ActExt a.
  Proof. intros [->|[_ E1]] Ha; [done|]. injection E1 as ->. by destruct (Ha []). Qed.

  Lemma detau_step_inv :
    (∀ P s l' X, detau P ⟶{l'}[s] X → ∃ l P', P ⟶{l}[s] P' ∧ X = detau P' ∧ lrel l l')
    ∧ (∀ g s l' X, PG (gdetau g) ⟶{l'}[s] X → ∃ l P', PG g ⟶{l}[s] P' ∧ X = detau P' ∧ lrel l l').
  Proof.
    apply proc_guard_ind; simpl.
    - intros t c e s l' X Hs. inversion Hs; subst. exists (c ! v), 𝟘. split; [by constructor|]. split; [done|by left].
    - intros e P IHP Q IHQ s l' X Hs. inversion Hs; subst.
      + match goal with Hp : detau P ⟶{_}[_] _ |- _ => destruct (IHP _ _ _ Hp) as (l & P1 & Hs' & -> & Hl) end.
        exists l, P1. split; [by apply pr_iteT|done].
      + match goal with Hp : detau Q ⟶{_}[_] _ |- _ => destruct (IHQ _ _ _ Hp) as (l & Q1 & Hs' & -> & Hl) end.
        exists l, Q1. split; [by apply pr_iteF|done].
    - intros P IHP Q IHQ s l' X Hs. inversion Hs; subst.
      + match goal with Hp : detau P ⟶{_}[_] _ |- _ => destruct (IHP _ _ _ Hp) as (l & P1 & Hs' & -> & Hl) end.
        exists l, (P1 ∥ Q). split; [by apply pr_parL|done].
      + match goal with Hp : detau Q ⟶{_}[_] _ |- _ => destruct (IHQ _ _ _ Hp) as (l & Q1 & Hs' & -> & Hl) end.
        exists l, (P ∥ Q1). split; [by apply pr_parR|done].
      + match goal with Hp : detau P ⟶{_}[_] _, Hq : detau Q ⟶{_}[_] _ |- _ =>
          destruct (IHP _ _ _ Hp) as (l1 & P1 & Hs1 & -> & Hl1); destruct (IHQ _ _ _ Hq) as (l2 & Q1 & Hs2 & -> & Hl2) end.
        apply lrel_chan in Hl1; [|done]. apply lrel_chan in Hl2; [|done]. subst.
        exists τ, (P1 ∥ Q1). split; [by eapply pr_syncL|]. split; [done|by left].
      + match goal with Hp : detau P ⟶{_}[_] _, Hq : detau Q ⟶{_}[_] _ |- _ =>
          destruct (IHP _ _ _ Hp) as (l1 & P1 & Hs1 & -> & Hl1); destruct (IHQ _ _ _ Hq) as (l2 & Q1 & Hs2 & -> & Hl2) end.
        apply lrel_chan in Hl1; [|done]. apply lrel_chan in Hl2; [|done]. subst.
        exists τ, (P1 ∥ Q1). split; [by eapply pr_syncR|]. split; [done|by left].
    - intros P IHP s l' X Hs. inversion Hs; subst.
      match goal with Hp : detau P ⟶{_}[_] _ |- _ => destruct (IHP _ _ _ Hp) as (l0 & P1 & Hs' & -> & Hl) end.
      destruct Hl as [El|[-> El]].
      + exists l', (ν P1). split; [apply pr_res; by rewrite El|]. split; [done|by left].
      + destruct l' as [[c v|c v|E0 qs|M qs n|qs]|]; simpl in El; try discriminate El.
        injection El as -> ->. exists τ, (ν P1). split; [by apply pr_res|]. split; [done|by right].
    - intros X0 s l' X Hs. inversion Hs.
    - intros t X P IHP s l' Y Hs. inversion Hs; subst. exists τ, (P ⦃ (t ∶ rec X ∙ P)↑ // X ⦄).
      split; [constructor|]. split; [|by left].
      rewrite (proj1 (detau_pr_subst X)). simpl. by rewrite (proj1 detau_tren).
    - intros g IHg s l' X Hs. exact (IHg s l' X Hs).
    - intros es s l' X Hs. inversion Hs.
    - intros s l' X Hs. inversion Hs.
    - intros 𝜆 P IHP s l' X Hs. destruct 𝜆 as [t|t c|t E0 es|t M es|t es]; simpl in Hs; inversion Hs; subst.
      + match goal with Hq : eval_qubits [] = Some ?qs |- _ => change (Some (@nil qubit) = Some qs) in Hq; injection Hq as <- end.
        exists τ, P. split; [constructor|]. split; [done|by right].
      + exists (c ? v), (P ⟦ v ⟧). split; [constructor|]. split; [by rewrite (proj1 detau_subst)|by left].
      + exists (E0 ⦅qs⦆), P. split; [by constructor|]. split; [done|by left].
      + exists (M ⦅qs⦆? n), (P ⟦ VNat n ⟧). split; [by constructor|]. split; [by rewrite (proj1 detau_subst)|by left].
      + exists (init ⦅qs⦆), P. split; [by constructor|]. split; [done|by left].
    - intros g1 IH1 g2 IH2 s l' X Hs. inversion Hs; subst.
      + match goal with Hp : PG (gdetau g1) ⟶{_}[_] _ |- _ => destruct (IH1 _ _ _ Hp) as (l & P1 & Hs' & -> & Hl) end.
        exists l, P1. split; [by apply pr_sumL|done].
      + match goal with Hp : PG (gdetau g2) ⟶{_}[_] _ |- _ => destruct (IH2 _ _ _ Hp) as (l & P1 & Hs' & -> & Hl) end.
        exists l, P1. split; [by apply pr_sumR|done].
  Qed.
  Lemma detau_successb :
    (∀ P, successb (detau P) = successb P) ∧ (∀ g, gsuccessb (gdetau g) = gsuccessb g).
  Proof.
    apply proc_guard_ind; simpl; intros; try done; try congruence.
    destruct (eval e) as [[[]| |]|]; done.
  Qed.

  Lemma detau_success P : success (detau P) ↔ success P.
  Proof. unfold success. by rewrite (proj1 detau_successb). Qed.

  Lemma pdetau_idem 𝜆 : pdetau (pdetau 𝜆) = pdetau 𝜆.
  Proof. by destruct 𝜆. Qed.

  Lemma detau_idem : (∀ P, detau (detau P) = detau P) ∧ (∀ g, gdetau (gdetau g) = gdetau g).
  Proof. apply proc_guard_ind; simpl; intros; try congruence. by rewrite pdetau_idem, H. Qed.

  Lemma detau_obs :
    (∀ P, obsb P = true → detau P = P) ∧ (∀ g, gobsb g = true → gdetau g = g).
  Proof.
    apply proc_guard_ind; simpl; intros; try done.
    - apply andb_prop in H1 as [H1 H2]. by rewrite H, H0.
    - apply andb_prop in H1 as [H1 H2]. by rewrite H, H0.
    - by rewrite H.
    - destruct 𝜆; simpl in *; try done; by rewrite H.
    - apply andb_prop in H1 as [H1 _]. apply andb_prop in H1 as [H1 H2]. by rewrite H, H0.
  Qed.
End Detau.

Section Sched_Detau.
  Context `{QM : QuantumModel} (E : sop).
  Hypothesis HE : ∀ ρ, sop_apply E [] ρ = ρ.

  Notation dd := (map (λ x : proc * St, (detau E x.1, x.2))).

  Lemma lrel_not_op l a : lrel E l (ActExt a) → (∀ qs, a ≠ PrOp E qs) → l = ActExt a.
  Proof. apply lrel_chan. Qed.

  Lemma meas_fwd R s M qs (ks : list (Out (meas_of M qs))) Rs :
    Forall2 (λ k R', prog_step R s (ActExt (PrMeas M qs (code _ k))) R') ks Rs →
    Forall2 (λ k R', prog_step (detau E R) s (ActExt (PrMeas M qs (code _ k))) R') ks (map (detau E) Rs).
  Proof.
    induction 1 as [|k R' ks Rs Hp _ IH]; simpl; constructor; [|done].
    destruct (detau_step E _ _ _ _ Hp) as (l' & Hs & ->%lrel_ext). done.
  Qed.

  Lemma meas_bwd R s M qs (ks : list (Out (meas_of M qs))) Rs' :
    Forall2 (λ k R', prog_step (detau E R) s (ActExt (PrMeas M qs (code _ k))) R') ks Rs' →
    ∃ Rs, Forall2 (λ k R', prog_step R s (ActExt (PrMeas M qs (code _ k))) R') ks Rs ∧ map (detau E) Rs = Rs'.
  Proof.
    induction 1 as [|k R'' ks Rs' Hp _ (Rs & HF & <-)]; [by exists []|].
    destruct (proj1 (detau_step_inv E) _ _ _ _ Hp) as (l & P' & Hs & -> & Hl).
    apply lrel_not_op in Hl; [|done]. subst l. exists (P' :: Rs). split; [by constructor|done].
  Qed.

  Lemma map_zip_detau {A} (f : A → St) (ks : list A) (Rs : list proc) :
    dd (zip_with (λ k R', (R', f k)) ks Rs) = zip_with (λ k R', (R', f k)) ks (map (detau E) Rs).
  Proof. revert Rs. induction ks as [|k ks IH]; intros [|R Rs]; simpl; try done. by rewrite IH. Qed.

  Lemma sched_detau_fwd ρ R s Δ : sched_step ρ R s Δ → sched_step ρ (detau E R) s (dd Δ).
  Proof.
    intros Hs. inversion Hs as [R' Hp|E0 qs R' Hp|qs R' Hp|M qs Rs R0 Hp0 HF]; subst; simpl.
    - destruct (detau_step E _ _ _ _ Hp) as (l' & Hs' & [->|[_ ->]]).
      + by apply ss_tau.
      + rewrite <- (HE ρ) at 2. by apply ss_op.
    - destruct (detau_step E _ _ _ _ Hp) as (l' & Hs' & ->%lrel_ext). by apply ss_op.
    - destruct (detau_step E _ _ _ _ Hp) as (l' & Hs' & ->%lrel_ext). by apply ss_init.
    - destruct (detau_step E _ _ _ _ Hp0) as (l' & Hs' & ->%lrel_ext). rewrite map_zip_detau.
      eapply ss_meas; [exact Hs'|by apply meas_fwd].
  Qed.

  Lemma sched_detau_bwd ρ R s Δ' : sched_step ρ (detau E R) s Δ' → ∃ Δ, sched_step ρ R s Δ ∧ dd Δ = Δ'.
  Proof.
    intros Hs. inversion Hs as [R' Hp|E0 qs R' Hp|qs R' Hp|M qs Rs' R0 Hp0 HF]; subst.
    - destruct (proj1 (detau_step_inv E) _ _ _ _ Hp) as (l & P' & Hs1 & -> & [El|[_ El]]); [|discriminate El].
      subst l. exists [(P', ρ)]. split; [by apply ss_tau|done].
    - destruct (proj1 (detau_step_inv E) _ _ _ _ Hp) as (l & P' & Hs1 & -> & [El|[-> El]]).
      + subst l. exists [(P', sop_apply E0 qs ρ)]. split; [by apply ss_op|done].
      + injection El as -> ->. exists [(P', ρ)]. split; [by apply ss_tau|]. simpl. by rewrite HE.
    - destruct (proj1 (detau_step_inv E) _ _ _ _ Hp) as (l & P' & Hs1 & -> & Hl).
      apply lrel_not_op in Hl; [|done]. subst l. exists [(P', init_apply qs ρ)]. split; [by apply ss_init|done].
    - destruct (proj1 (detau_step_inv E) _ _ _ _ Hp0) as (l & P0 & Hs0 & -> & Hl).
      apply lrel_not_op in Hl; [|done]. subst l. destruct (meas_bwd _ _ _ _ _ _ HF) as (Rs & HFs & <-).
      eexists. split; [by eapply ss_meas|]. apply map_zip_detau.
  Qed.

  Definition fdetau (c : proc * proc) : proc * proc := (detau E c.1, detau E c.2).

  Notation fd := (map (λ x : proc * proc * St, (fdetau x.1, x.2))).

  Lemma dmap_fdetau (Δ : dist (proc * proc)) : dmap par_of (fd Δ) = dd (dmap par_of Δ).
  Proof. unfold dmap. rewrite !map_map. by apply map_ext. Qed.

  Lemma unpar_detau (Δ0 : dist proc) (Δ' : dist (proc * proc)) :
    dd Δ0 = dmap par_of Δ' → ∃ Δ, dmap par_of Δ = Δ0 ∧ fd Δ = Δ'.
  Proof.
    revert Δ'. induction Δ0 as [|[x ρ] Δ0 IH]; intros [|[[a b] ρ'] Δ'] Eq; simpl in Eq; try discriminate Eq; [by exists []|].
    injection Eq as E1 E2 E3. destruct (IH _ E3) as (Δ & <- & <-).
    destruct x as [| |u v| | | |]; simpl in E1; try discriminate E1. injection E1 as Ea Eb. subst a b ρ'.
    exists (((u, v), ρ) :: Δ). split; done.
  Qed.

  Lemma conf_detau_fwd ρ c s Δ : conf_sched ρ c s Δ → conf_sched ρ (fdetau c) s (fd Δ).
  Proof. unfold conf_sched. rewrite dmap_fdetau. apply sched_detau_fwd. Qed.

  Lemma conf_detau_bwd ρ c s Δ' : conf_sched ρ (fdetau c) s Δ' → ∃ Δ, conf_sched ρ c s Δ ∧ fd Δ = Δ'.
  Proof.
    unfold conf_sched. intros Hs. destruct (sched_detau_bwd ρ (par_of c) s _ Hs) as (Δ0 & Hs0 & E0).
    destruct (unpar_detau Δ0 Δ' E0) as (Δ & <- & <-). by exists Δ.
  Qed.

  Theorem smyth_detau (DC : dep_choice) (p q : proc * St) (T : proc) :
    smyth_le (SchedSts0 := lq_SchedSts) Stay (compose p T) (compose q T)
    ↔ smyth_le (SchedSts0 := lq_SchedSts) Stay (compose (detau E p.1, p.2) (detau E T)) (compose (detau E q.1, q.2) (detau E T)).
  Proof.
    exact (bisim_smyth lq_SchedSts lq_SchedSts fdetau (λ c, iff_sym (detau_success E c.2))
             conf_detau_fwd conf_detau_bwd DC (compose p T) (compose q T)).
  Qed.

  Theorem smyth_detau_obs (DC : dep_choice) (p q : proc * St) (T : proc) :
    smyth_le (SchedSts0 := lq_SchedSts) Stay (compose p T) (compose q T)
    ↔ smyth_le (SchedSts0 := lq_SchedSts) Stay (compose p (detau E T)) (compose q (detau E T)).
  Proof.
    rewrite (smyth_detau DC p q T), (smyth_detau DC p q (detau E T)), (proj1 (detau_idem E)). done.
  Qed.

  Definition obs_for_silent (p q : proc * St) (T : proc) : Prop := obs_for p q (detau E T).

  Theorem silent_observers (DC : dep_choice) (p q : proc * St) :
    ctx_pre_sm_on Stay (obs_for_silent p q) p q ↔ ctx_pre_sm_on Stay (obs_for p q) p q.
  Proof.
    split.
    - intros Hc T HT. apply Hc. unfold obs_for_silent. by rewrite (proj1 (detau_obs E) T (proj1 (proj1 (proj1 HT)))).
    - intros Hc T HT. apply (smyth_detau_obs DC p q T). exact (Hc _ HT).
  Qed.
End Sched_Detau.
(* end hide *)
