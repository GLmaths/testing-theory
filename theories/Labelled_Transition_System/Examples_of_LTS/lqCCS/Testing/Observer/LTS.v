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
(* * lqCCS processes observed by lqCCS programs without memory

    The observers are lqCCS programs run without a memory of their own.
    Their actions ([tstep]) are those of the program:

    - the messages [c!v] and [c?v];
    - the operations [E(q̃)] and the measurements [M(q̃ ▷ x)], which act on the
      memory of the process tested: [LOp E q̃], and [LMeas M q̃ k] with [x]
      bound to the outcome [k].  Each is its own co-action: it meets the same
      action of the memory, in one blocking synchronisation.

    The abstraction of the actions ([lαᴛᴇꜱᴛ], [lαᴘʀᴏ]):
    - [lαᴛᴇꜱᴛ] keeps the channel of a message, and the operation or the
      measurement of a memory action — not the outcome, which an observer
      cannot choose;
    - [lαᴘʀᴏ] then merges all operations into one class, and all measurements
      into another: the memory of a process accepts every operation, and,
      when it is non-zero, every measurement ([meas_nonzero_branch]).
    It is finitary: the co-actions of [(P, ρ)] are, up to [lαᴘʀᴏ], the channels
    of the outputs of [P], the operations, and the measurements if [ρ ≠ 0].

    The states of the memory are assumed countable (e.g. amplitudes in a
    countable field), as the framework asks of the states of a process. *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list numbers finite sets gmap gmultiset.
From TestingTheory Require Import lqCCS.Harmony_Lemma.Lifted lqCCS.Harmony_Lemma.Paths lqCCS.Harmony_Lemma.States lqCCS.Language.Quantum.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.Program lqCCS.Language.Succ lqCCS.Language.Congruence
  lqCCS.Language.LTS lqCCS.Language.FwLTS.
From TestingTheory Require Import ActTau InListPropHelper
  gLts Bisimulation Lts_OBA Lts_OBA_FB Lts_FW Lts_Finite_Non_Blocking_Chain
  FiniteImageLTS coFiniteImage Subset_Act Termination Convergence WeakTransitions
  coWeakTransition coConvergence StateTransitionSystems
  InteractionBetweenLts MultisetLTSConstruction ForwarderConstruction
  ParallelLTSConstruction SetLTSConstruction
  Must MustE Lift Testing_Predicate
  DefinitionAS Completeness Equivalence
  CompletenessASco SoundnessASco EquivalenceASco TestSpecBridge.

(* ** Receptions take any value *)

Lemma grecv_any g t c v w P' :
  gstep g (LAct t (AIn c v)) P' → ∃ P'', gstep g (LAct t (AIn c w)) P''.
Proof.
  intros Hs. remember (LAct t (AIn c v)) as l eqn:El. revert El.
  induction Hs as [| |t0 c0 x v0 P|t0 E es qs P Hq|t0 M es x qs P Hq
                  |g1 g2 l P' Hs IH|g1 g2 l P' Hs IH]; intros El; simplify_eq.
  - eexists. constructor.
  - destruct (IH eq_refl) as (P'' & HP). eexists. by apply gs_sumL.
  - destruct (IH eq_refl) as (P'' & HP). eexists. by apply gs_sumR.
Qed.

Lemma precv_any P t c v w P' :
  pstep P (LAct t (AIn c v)) P' → ∃ P'', pstep P (LAct t (AIn c w)) P''.
Proof.
  intros Hs. remember (LAct t (AIn c v)) as l eqn:El. revert El.
  induction Hs as [g l P' Hg|t0 c0 e v0 He|e P Q l P' He Hs IH|e P Q l Q' He Hs IH
                  |P Q l P' Hs IH|P Q l Q' Hs IH| | |P d l P' Hd Hs IH];
    intros El; simplify_eq.
  - destruct (grecv_any _ _ _ _ w _ Hg) as (P'' & HP). eexists. by constructor.
  - destruct (IH eq_refl) as (P'' & HP). eexists. by apply ps_iteT.
  - destruct (IH eq_refl) as (P'' & HP). eexists. by apply ps_iteF.
  - destruct (IH eq_refl) as (P'' & HP). eexists. by apply ps_parL.
  - destruct (IH eq_refl) as (P'' & HP). eexists. by apply ps_parR.
  - destruct (IH eq_refl) as (P'' & HP). eexists. apply ps_res; [|exact HP].
    intros (t' & v' & [E|E]); simplify_eq. apply Hd. exists t', v. by right.
Qed.

Lemma recv_any Q c v w Q' :
  ustep Q (UAct (AIn c v)) Q' → ∃ Q'', ustep Q (UAct (AIn c w)) Q''.
Proof.
  intros ([s|t a] & El & Hs); simpl in El; simplify_eq.
  destruct (precv_any _ _ _ _ w _ Hs) as (Q'' & HQ). exists Q''. by exists (LAct t (AIn c w)).
Qed.

(* ** The observers: programs without memory *)

Definition tstep (Q : proc) (𝜆 : Labels lact) (Q' : proc) : Prop :=
  match 𝜆 with
  | τ => ustep Q UTau Q'
  | ActExt (LOut c v) => ustep Q (UAct (AOut c v)) Q'
  | ActExt (LIn c v) => ustep Q (UAct (AIn c v)) Q'
  | ActExt (LOp E qs) => ustep Q (UAct (AOp E qs)) Q'
  | ActExt (LMeas M qs n) =>
      ∃ x Q0, ustep Q (UAct (AMeas M qs x)) Q0 ∧ Q' = subst Q0 x (VNat n)
  end.

Definition meas_res (M : meas) (qs : list qubit) (n : nat) (aQ : pact * proc) : list proc :=
  match aQ with
  | (AMeas M' qs' x, Q0) => if decide (M' = M ∧ qs' = qs) then [subst Q0 x (VNat n)] else []
  | _ => []
  end.

Definition tsuccs (Q : proc) (𝜆 : Labels lact) : list proc :=
  match 𝜆 with
  | τ => succ Q UTau
  | ActExt (LOut c v) => succ Q (UAct (AOut c v))
  | ActExt (LIn c v) => succ Q (UAct (AIn c v))
  | ActExt (LOp E qs) => succ Q (UAct (AOp E qs))
  | ActExt (LMeas M qs n) => acts Q ≫= meas_res M qs n
  end.

Lemma tsuccs_spec Q 𝜆 Q' : Q' ∈ tsuccs Q 𝜆 ↔ tstep Q 𝜆 Q'.
Proof.
  destruct 𝜆 as [[c v|c v|E qs|M qs n]|]; simpl; try apply succ_spec.
  rewrite list_elem_of_bind. split.
  - intros ([a Q0] & Hin & Hacts). apply acts_spec in Hacts as (_ & t & Hs).
    destruct a as [c0 v0|c0 v0|E0 qs0|M' qs' x]; simpl in Hin; try set_solver.
    case_decide as Hd; [|set_solver]. destruct Hd as [-> ->].
    apply list_elem_of_singleton in Hin as ->. exists x, Q0. split; [|done].
    by exists (LAct t (AMeas M qs x)).
  - intros (x & Q0 & ([s|t a] & E & Hs) & ->); simpl in E; simplify_eq.
    exists (AMeas M qs x, Q0). split.
    + simpl. rewrite decide_True by done. by left.
    + apply acts_spec. split; [done|]. eauto.
Qed.

#[global] Instance obs_gLts : gLts proc lact_ExtAction := gLts_of_succs tsuccs.

Lemma obs_step_def Q 𝜆 Q' : Q ⟶{𝜆} Q' ↔ tstep Q 𝜆 Q'.
Proof. change (Q' ∈ tsuccs Q 𝜆 ↔ tstep Q 𝜆 Q'). apply tsuccs_spec. Qed.

Lemma cgr_tstep R P 𝜆 Q : R ≡* P → tstep R 𝜆 Q → ∃ Q', tstep P 𝜆 Q' ∧ Q ≡* Q'.
Proof.
  intros Hc. destruct 𝜆 as [[c v|c v|E qs|M qs n]|]; simpl; try (by apply cgr_ustep).
  intros (x & Q0 & Hs & ->). destruct (cgr_ustep _ _ _ _ Hc Hs) as (Q1 & Hs1 & HQ).
  exists (subst Q1 x (VNat n)). split; [eauto|by apply cgr_subst].
Qed.

#[global] Instance obs_gLtsEq : gLtsEq proc lact_ExtAction.
Proof.
  refine {| gLtsEq_gLts := obs_gLts; eq_rel := cgr; eq_rel_eq := _ |}.
  intros P Q 𝜆 (R & HPR & HR). apply obs_step_def in HR.
  destruct (cgr_tstep R P 𝜆 Q (symmetry HPR) HR) as (P' & HP' & HQ).
  exists P'. split; [by apply obs_step_def|by symmetry].
Defined.

(* *** Asynchronous outputs: the output axioms *)

Lemma tstep_par_l Q 𝜆 Q' t c v :
  tstep Q 𝜆 Q' → tstep (PPar Q (oproc t c v)) 𝜆 (PPar Q' (oproc t c v)).
Proof.
  destruct 𝜆 as [[c' v'|c' v'|E qs|M qs n]|]; simpl; try apply ustep_par_l.
  intros (x & Q0 & Hs & ->). exists x, (PPar Q0 (oproc t c v)). split; [by apply ustep_par_l|done].
Qed.

Lemma tstep_par_out_inv Q t c v 𝜆 X :
  tstep (PPar Q (oproc t c v)) 𝜆 X →
    (∃ Q', tstep Q 𝜆 Q' ∧ X = PPar Q' (oproc t c v))
  ∨ (𝜆 = ActExt (LOut c v) ∧ X = PPar Q 𝟘)
  ∨ (𝜆 = τ ∧ ∃ Q', ustep Q (UAct (AIn c v)) Q' ∧ X = PPar Q' 𝟘).
Proof.
  destruct 𝜆 as [[c' v'|c' v'|E qs|M qs n]|]; simpl; intros Hs.
  - destruct (ustep_par_out_inv _ _ _ _ _ _ Hs) as [(Q' & HQ & ->)|[[E ->]|[E _]]].
    + left. eauto.
    + right; left. simplify_eq. done.
    + discriminate.
  - destruct (ustep_par_out_inv _ _ _ _ _ _ Hs) as [(Q' & HQ & ->)|[[E _]|[E _]]];
      [left; eauto|discriminate|discriminate].
  - destruct (ustep_par_out_inv _ _ _ _ _ _ Hs) as [(Q' & HQ & ->)|[[E0 _]|[E0 _]]];
      [left; eauto|discriminate|discriminate].
  - destruct Hs as (x & X0 & Hs & ->).
    destruct (ustep_par_out_inv _ _ _ _ _ _ Hs) as [(Q0 & HQ & ->)|[[E _]|[E _]]];
      [|discriminate|discriminate].
    left. exists (subst Q0 x (VNat n)). split; [eauto|done].
  - destruct (ustep_par_out_inv _ _ _ _ _ _ Hs) as [(Q' & HQ & ->)|[[E _]|[_ (Q' & HQ & ->)]]].
    + left. eauto.
    + discriminate.
    + right; right. eauto.
Qed.

Lemma t_out_from_par Q Q1 t c v :
  Q ≡* PPar Q1 (oproc t c v) → ∃ Z, tstep Q (ActExt (LOut c v)) Z ∧ Z ≡* Q1.
Proof.
  intros HQ.
  destruct (cgr_tstep _ _ (ActExt (LOut c v)) _ (symmetry HQ) (ustep_par_out_emit Q1 t c v))
    as (Z & HZ & HZ').
  exists Z. split; [done|]. symmetry. etrans; [symmetry; apply cgr_par_nil|exact HZ'].
Qed.

Lemma t_nb_delay Q Q1 Q2 c v 𝜆 :
  tstep Q (ActExt (LOut c v)) Q1 → tstep Q1 𝜆 Q2 →
  ∃ W, tstep Q 𝜆 W ∧ ∃ Z, tstep W (ActExt (LOut c v)) Z ∧ Z ≡* Q2.
Proof.
  intros H1 H2. destruct (ustep_out_par _ _ _ _ H1) as [t Ht].
  destruct (cgr_tstep _ _ _ _ (symmetry Ht) (tstep_par_l _ _ _ t c v H2)) as (W & HW & HW').
  exists W. split; [done|]. apply (t_out_from_par _ _ t). by symmetry.
Qed.

Lemma t_nb_confluence Q Q1 Q2 c v μ :
  μ ≠ LOut c v → tstep Q (ActExt (LOut c v)) Q1 → tstep Q (ActExt μ) Q2 →
  ∃ R, tstep Q1 (ActExt μ) R ∧ ∃ R', tstep Q2 (ActExt (LOut c v)) R' ∧ R' ≡* R.
Proof.
  intros Hμ H1 H2. destruct (ustep_out_par _ _ _ _ H1) as [t Ht].
  destruct (cgr_tstep _ _ _ _ Ht H2) as (Z & HZ & HQ2).
  destruct (tstep_par_out_inv _ _ _ _ _ _ HZ) as [(R & HR & ->)|[[E _]|[E _]]].
  - exists R. split; [done|]. by apply (t_out_from_par _ _ t).
  - simplify_eq.
  - discriminate.
Qed.

Lemma t_nb_tau Q Q1 Q2 c v :
  tstep Q (ActExt (LOut c v)) Q1 → tstep Q τ Q2 →
  (∃ R, tstep Q1 τ R ∧ ∃ R', tstep Q2 (ActExt (LOut c v)) R' ∧ R' ≡* R)
  ∨ (∃ R, tstep Q1 (ActExt (LIn c v)) R ∧ R ≡* Q2).
Proof.
  intros H1 H2. destruct (ustep_out_par _ _ _ _ H1) as [t Ht].
  destruct (cgr_tstep _ _ _ _ Ht H2) as (Z & HZ & HQ2).
  destruct (tstep_par_out_inv _ _ _ _ _ _ HZ)
    as [(R & HR & ->)|[[E _]|[_ (R & HR & ->)]]]; [|discriminate|].
  - left. exists R. split; [done|]. by apply (t_out_from_par _ _ t).
  - right. exists R. split; [done|].
    etrans; [symmetry; apply cgr_par_nil|by symmetry].
Qed.

Lemma t_nb_determinacy Q Q1 Q2 c v :
  tstep Q (ActExt (LOut c v)) Q1 → tstep Q (ActExt (LOut c v)) Q2 → Q1 ≡* Q2.
Proof.
  intros ([s|t a] & E1 & Hs1); simpl in E1; simplify_eq.
  intros ([s|t' a] & E2 & Hs2); simpl in E2; simplify_eq.
  by eapply out_det.
Qed.

Lemma t_backwards Q1 Q2 R1 R2 c v :
  tstep Q1 (ActExt (LOut c v)) R1 → tstep Q2 (ActExt (LOut c v)) R2 → R1 ≡* R2 → Q1 ≡* Q2.
Proof.
  intros H1 H2 HR.
  destruct (ustep_out_par _ _ _ _ H1) as [t1 Ht1].
  destruct (ustep_out_par _ _ _ _ H2) as [t2 Ht2].
  etrans; [exact Ht1|]. etrans; [|symmetry; exact Ht2].
  etrans; [apply cgr_par_l, HR|]. apply cgr_par_r, cgr_send_tag.
Qed.

Lemma t_feedback Q Q1 Q2 c v :
  tstep Q (ActExt (LOut c v)) Q1 → tstep Q1 (ActExt (LIn c v)) Q2 →
  ∃ W, tstep Q τ W ∧ W ≡* Q2.
Proof.
  intros H1 H2. destruct (ustep_out_par _ _ _ _ H1) as [t Ht].
  destruct (cgr_tstep _ _ τ _ (symmetry Ht) (ustep_par_out_sync _ _ t _ _ H2))
    as (W & HW & HW').
  exists W. split; [done|]. symmetry. etrans; [symmetry; apply cgr_par_nil|exact HW'].
Qed.

#[global] Instance obs_gLtsOba : @gLtsOba proc lact lact_ExtAction obs_gLtsEq.
Proof.
  split.
  - intros p q r η 𝜆 Hη Hpq Hqr. destruct η as [c v| | |]; try done.
    apply obs_step_def in Hpq, Hqr.
    destruct (t_nb_delay _ _ _ _ _ _ Hpq Hqr) as (W & HW & Z & HZ & HZr).
    exists W. split; [by apply obs_step_def|]. exists Z. split; [by apply obs_step_def|exact HZr].
  - intros p q1 q2 η μ Hη Hμ Hs1 Hs2. destruct η as [c v| | |]; try done.
    apply obs_step_def in Hs1, Hs2.
    destruct (t_nb_confluence _ _ _ _ _ μ Hμ Hs1 Hs2) as (R & HR & R' & HR' & Heq).
    exists R. split; [by apply obs_step_def|]. exists R'. split; [by apply obs_step_def|exact Heq].
  - intros p q1 q2 η Hη Hs1 Hs2. destruct η as [c v| | |]; try done.
    apply obs_step_def in Hs1, Hs2.
    destruct (t_nb_tau _ _ _ _ _ Hs1 Hs2) as [(R & HR & R' & HR' & Heq)|(R & HR & Heq)].
    + left. exists R. split; [by apply obs_step_def|].
      exists R'. split; [by apply obs_step_def|exact Heq].
    + right. exists (LIn c v). split; [done|].
      exists R. split; [by apply obs_step_def|exact Heq].
  - intros p1 p2 p3 η Hη Hs1 Hs2. destruct η as [c v| | |]; try done.
    apply obs_step_def in Hs1, Hs2. exact (t_nb_determinacy _ _ _ _ _ Hs1 Hs2).
  - intros p1 p2 q1 q2 η Hη Hs1 Hs2 Hq. destruct η as [c v| | |]; try done.
    apply obs_step_def in Hs1, Hs2. exact (t_backwards _ _ _ _ _ _ Hs1 Hs2 Hq).
Qed.

#[global] Instance obs_gLtsObaFB : gLtsObaFB proc lact.
Proof.
  split. intros p1 p2 p3 η β Hη Hd Hs1 Hs2. destruct η as [c v| | |]; try done.
  destruct β as [c' v'|c' v'| |]; simpl in Hd; simplify_eq.
  apply obs_step_def in Hs1, Hs2.
  destruct (t_feedback _ _ _ _ _ Hs1 Hs2) as (W & HW & Heq).
  exists W. split; [by apply obs_step_def|exact Heq].
Qed.

(* *** The outputs of an observer *)

Definition tmo (Q : proc) : gmultiset lact :=
  list_to_set_disj ((λ cv : chan * val, LOut cv.1 cv.2) <$> pouts Q).

Lemma tmo_elem Q a : a ∈ tmo Q ↔ ∃ c v, a = LOut c v ∧ (c, v) ∈ pouts Q.
Proof.
  unfold tmo. rewrite elem_of_list_to_set_disj, list_elem_of_fmap. split.
  - intros ([c v] & -> & Hin). eauto.
  - intros (c & v & -> & Hin). by exists (c, v).
Qed.

Lemma tmo_step Q a : a ∈ tmo Q → ∃ Q', Q ⟶[a] Q'.
Proof.
  intros (c & v & -> & Hin)%tmo_elem.
  destruct (pouts_spec _ _ _ Hin) as (t & Q' & Hs).
  exists Q'. apply obs_step_def. exists (LAct t (AOut c v)). by split.
Qed.

Definition tmo_witness Q a (Hin : a ∈ tmo Q) : {Q' | non_blocking a ∧ Q ⟶[a] Q'}.
Proof.
  destruct (step_witness Q a (tmo_step Q a Hin)) as [Q' HQ'].
  exists Q'. split; [|done].
  apply tmo_elem in Hin as (c & v & -> & _). done.
Defined.

Lemma tmo_of_step Q c v Q' : Q ⟶[LOut c v] Q' → LOut c v ∈ tmo Q.
Proof.
  intros ([s|t a] & E & Hs)%obs_step_def; simpl in E; simplify_eq.
  apply tmo_elem. exists c, v. split; [done|].
  rewrite (pouts_step _ _ _ _ _ Hs). by left.
Qed.

#[global] Instance obs_FiniteNonBlockingChain : FiniteNonBlockingChain_LtsOba proc (A := lact).
Proof.
  refine {| lts_oba_mo := tmo; lts_oba_mo_spec_bis2 := tmo_witness |}.
  - intros Q η Q' Hη Hs. destruct η as [c v| | |]; try done. by eapply tmo_of_step.
  - intros Q η Q' Hη Hs. destruct η as [c v| | |]; try done.
    apply obs_step_def in Hs as ([s|t a] & E & Hs); simpl in E; simplify_eq.
    unfold tmo. rewrite (pouts_step _ _ _ _ _ Hs). done.
Defined.

#[global] Program Instance obs_FiniteImage : FiniteImagegLts proc lact.
Next Obligation.
  intros Q 𝜆. eapply (in_list_finite (tsuccs Q 𝜆)).
  intros Q' HQ'%bool_decide_unpack. exact HQ'.
Defined.

(* *** The operations an observer can perform on a memory *)

Section Memory.
  Context `{QM : QuantumModel}.

  Definition tmem_of (aQ : pact * proc) : list lact :=
    match aQ.1 with
    | AOp E qs => [LOp E qs]
    | AMeas M qs _ => (λ k, LMeas M qs (code _ k)) <$> outs (meas_of M qs)
    | _ => []
    end.

  Definition tmem (Q : proc) : gset lact := list_to_set (acts Q ≫= tmem_of).

  Lemma tmem_step Q a : a ∈ tmem Q → ∃ Q', Q ⟶[a] Q'.
  Proof.
    unfold tmem. rewrite elem_of_list_to_set, list_elem_of_bind.
    intros ([b Q0] & Hin & Hacts). apply acts_spec in Hacts as (_ & t & Hs).
    destruct b as [c v|c v|E qs|M qs x]; simpl in Hin; try set_solver.
    - apply list_elem_of_singleton in Hin as ->. exists Q0. apply obs_step_def.
      by exists (LAct t (AOp E qs)).
    - apply list_elem_of_fmap in Hin as (k & -> & _).
      exists (subst Q0 x (VNat (code _ k))). apply obs_step_def. exists x, Q0.
      split; [by exists (LAct t (AMeas M qs x))|done].
  Qed.

  Lemma tmem_of_op Q E qs Q' : Q ⟶[LOp E qs] Q' → LOp E qs ∈ tmem Q.
  Proof.
    intros ([s|t a] & El & Hs)%obs_step_def; simpl in El; simplify_eq.
    unfold tmem. rewrite elem_of_list_to_set, list_elem_of_bind.
    exists (AOp E qs, Q'). split; [simpl; by left|]. apply acts_spec. split; [done|eauto].
  Qed.

  Lemma tmem_of_meas Q M qs (k : Out (meas_of M qs)) Q' :
    Q ⟶[LMeas M qs (code _ k)] Q' → LMeas M qs (code _ k) ∈ tmem Q.
  Proof.
    intros (x & Q0 & ([s|t a] & El & Hs) & _)%obs_step_def; simpl in El; simplify_eq.
    unfold tmem. rewrite elem_of_list_to_set, list_elem_of_bind.
    exists (AMeas M qs x, Q0). split.
    - simpl. apply list_elem_of_fmap. exists k. split; [done|]. apply list_elem_of_In, outs_all.
    - apply acts_spec. split; [done|eauto].
  Qed.
End Memory.

(* *** Success *)

Lemma out_goodb Q c v Q' : ustep Q (UAct (AOut c v)) Q' → goodb Q = goodb Q'.
Proof.
  intros Hs. destruct (ustep_out_par _ _ _ _ Hs) as [t Ht].
  rewrite (cgr_goodb _ _ Ht). simpl. by rewrite orb_false_r.
Qed.

#[global] Instance obs_predicate : Testing_Predicate good obs_gLtsEq.
Proof.
  split.
  - intros Q. apply _.
  - intros P Q HP HPQ. unfold good in *. by rewrite <- (cgr_goodb _ _ HPQ).
  - intros P Q η Hη Hs HP. destruct η as [c v| | |]; try done. apply obs_step_def in Hs.
    unfold good in *. by rewrite <- (out_goodb _ _ _ _ Hs).
  - intros P Q η Hη Hs HQ. destruct η as [c v| | |]; try done. apply obs_step_def in Hs.
    unfold good in *. by rewrite (out_goodb _ _ _ _ Hs).
Qed.
(* end hide *)
