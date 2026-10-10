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

(* * lqCCS processes observed by lqCCS programs without memory

    The observers are lqCCS programs run without a memory of their own.
    Their actions ([tstep]) are those of the program:

    - the messages [c!v] and [c?v];
    - the operations [E(q̃)] and the measurements [M(q̃ ▷ x)], which act on the
      memory of the process tested: [LOp E q̃], and [LMeas M q̃ k] with [x]
      bound to the outcome [k].  Each is its own co-action: it meets the same
      action of the memory, in one blocking synchronisation.

    The abstraction of the actions ([lΦ], [l𝝳]):
    - [lΦ] keeps the channel of a message, and the operation or the
      measurement of a memory action — not the outcome, which an observer
      cannot choose;
    - [l𝝳] then merges all operations into one class, and all measurements
      into another: the memory of a process accepts every operation, and,
      when it is non-zero, every measurement ([meas_nonzero_branch]).
    It is finitary: the co-actions of [(P, ρ)] are, up to [l𝝳], the channels
    of the outputs of [P], the operations, and the measurements if [ρ ≠ 0].

    The states of the memory are assumed countable (e.g. amplitudes in a
    countable field), as the framework asks of the states of a process. *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list numbers finite sets gmap gmultiset.
From TestingTheory Require Import Lifted Paths States lqCCS_Quantum.
From TestingTheory Require Import lqCCS_Syntax lqCCS_Program lqCCS_Succ lqCCS_Congruence
  lqCCS_LTS lqCCS_FwLTS.
From TestingTheory Require Import ActTau InListPropHelper
  gLts Bisimulation Lts_OBA Lts_OBA_FB Lts_FW Lts_Finite_Output_Chain
  FiniteImageLTS coFiniteImage Subset_Act Termination Convergence WeakTransitions
  coWeakTransition coConvergence StateTransitionSystems
  InteractionBetweenLts MultisetLTSConstruction ForwarderConstruction
  ParallelLTSConstruction SetLTSConstruction
  Must MustE Lift Testing_Predicate
  DefinitionAS Completeness Soundness Equivalence
  DefinitionASco CompletenessASco SoundnessASco EquivalenceASco TestSpecBridge.

(* The lift of an abstraction to the forwarder in [DefinitionAS.v] rests on an
    [Admitted] obligation; as for Erlang, it is replaced below. *)
Remove Hints PreActActionForFW FinitaryPreActActionForFW : typeclass_instances.

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

Definition tstep (Q : proc) (α : Act lact) (Q' : proc) : Prop :=
  match α with
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

Definition tsuccs (Q : proc) (α : Act lact) : list proc :=
  match α with
  | τ => succ Q UTau
  | ActExt (LOut c v) => succ Q (UAct (AOut c v))
  | ActExt (LIn c v) => succ Q (UAct (AIn c v))
  | ActExt (LOp E qs) => succ Q (UAct (AOp E qs))
  | ActExt (LMeas M qs n) => acts Q ≫= meas_res M qs n
  end.

Lemma tsuccs_spec Q α Q' : Q' ∈ tsuccs Q α ↔ tstep Q α Q'.
Proof.
  destruct α as [[c v|c v|E qs|M qs n]|]; simpl; try apply succ_spec.
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

Lemma obs_step_def Q α Q' : Q ⟶{α} Q' ↔ tstep Q α Q'.
Proof. change (Q' ∈ tsuccs Q α ↔ tstep Q α Q'). apply tsuccs_spec. Qed.

Lemma cgr_tstep R P α Q : R ≡* P → tstep R α Q → ∃ Q', tstep P α Q' ∧ Q ≡* Q'.
Proof.
  intros Hc. destruct α as [[c v|c v|E qs|M qs n]|]; simpl; try (by apply cgr_ustep).
  intros (x & Q0 & Hs & ->). destruct (cgr_ustep _ _ _ _ Hc Hs) as (Q1 & Hs1 & HQ).
  exists (subst Q1 x (VNat n)). split; [eauto|by apply cgr_subst].
Qed.

#[global] Instance obs_gLtsEq : gLtsEq proc lact_ExtAction.
Proof.
  refine {| gLtsEq_gLts := obs_gLts; eq_rel := cgr; eq_rel_eq := _ |}.
  intros P Q α (R & HPR & HR). apply obs_step_def in HR.
  destruct (cgr_tstep R P α Q (symmetry HPR) HR) as (P' & HP' & HQ).
  exists P'. split; [by apply obs_step_def|by symmetry].
Defined.

(* *** Asynchronous outputs: the output axioms *)

Lemma tstep_par_l Q α Q' t c v :
  tstep Q α Q' → tstep (PPar Q (oproc t c v)) α (PPar Q' (oproc t c v)).
Proof.
  destruct α as [[c' v'|c' v'|E qs|M qs n]|]; simpl; try apply ustep_par_l.
  intros (x & Q0 & Hs & ->). exists x, (PPar Q0 (oproc t c v)). split; [by apply ustep_par_l|done].
Qed.

Lemma tstep_par_out_inv Q t c v α X :
  tstep (PPar Q (oproc t c v)) α X →
    (∃ Q', tstep Q α Q' ∧ X = PPar Q' (oproc t c v))
  ∨ (α = ActExt (LOut c v) ∧ X = PPar Q 𝟘)
  ∨ (α = τ ∧ ∃ Q', ustep Q (UAct (AIn c v)) Q' ∧ X = PPar Q' 𝟘).
Proof.
  destruct α as [[c' v'|c' v'|E qs|M qs n]|]; simpl; intros Hs.
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

Lemma t_nb_delay Q Q1 Q2 c v α :
  tstep Q (ActExt (LOut c v)) Q1 → tstep Q1 α Q2 →
  ∃ W, tstep Q α W ∧ ∃ Z, tstep W (ActExt (LOut c v)) Z ∧ Z ≡* Q2.
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
  - intros p q r η α Hη Hpq Hqr. destruct η as [c v| | |]; try done.
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

#[global] Instance obs_FiniteOutputChain : FiniteOutputChain_LtsOba proc (A := lact).
Proof.
  refine {| lts_oba_mo := tmo; lts_oba_mo_spec_bis2 := tmo_witness |}.
  - intros Q η Q' Hη Hs. destruct η as [c v| | |]; try done. by eapply tmo_of_step.
  - intros Q η Q' Hη Hs. destruct η as [c v| | |]; try done.
    apply obs_step_def in Hs as ([s|t a] & E & Hs); simpl in E; simplify_eq.
    unfold tmo. rewrite (pouts_step _ _ _ _ _ Hs). done.
Defined.

#[global] Program Instance obs_FiniteImage : FiniteImagegLts proc lact.
Next Obligation.
  intros Q α. eapply (in_list_finite (tsuccs Q α)).
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

(* ** The abstraction *)

Inductive lfin : Type :=
| FChan (c : chan)
| FOp (E : sop) (qs : list qubit)
| FMeas (M : meas) (qs : list qubit).

Inductive lpre : Type :=
| PChan (c : chan)
| POpAll
| PMeasAll.

#[global] Instance lpre_eq_dec : EqDecision lpre.
Proof. solve_decision. Defined.

#[global] Instance lpre_countable : Countable lpre.
Proof.
  refine (inj_countable'
    (λ p, match p with PChan c => inl c | POpAll => inr true | PMeasAll => inr false end
       : chan + bool)
    (λ s, match s with inl c => PChan c | inr true => POpAll | inr false => PMeasAll end) _).
  by intros [| |].
Defined.

Definition lΦ (a : lact) : lfin :=
  match a with
  | LOut c _ | LIn c _ => FChan c
  | LOp E qs => FOp E qs
  | LMeas M qs _ => FMeas M qs
  end.

Definition l𝝳 (f : lfin) : lpre :=
  match f with FChan c => PChan c | FOp _ _ => POpAll | FMeas _ _ => PMeasAll end.

(* The observer's side: an observer that can receive a value, or accept an
    outcome, can receive or accept any other one. *)
Lemma obs_abs_test (t : proc) (β β' : lact) :
  blocking β → blocking β' → lΦ β = lΦ β' → β ∈ R t → β' ∈ R t.
Proof.
  intros hb hb' heq hmem.
  assert (Hs : t ⟶[β]) by exact hmem.
  change (t ⟶[β']). destruct (decide (t ⟶[β'])) as [Hok | Href]; [exact Hok |].
  rename Hs into Hr. exfalso.
  apply lts_performs_spec1 in Hr as (Q & HQ). apply obs_step_def in HQ.
  assert (∃ Q'', tstep t (ActExt β') Q'') as (Q'' & HQ'').
  { destruct β as [c v|c v|E qs|M qs n]; [exfalso; by apply hb| | |];
      destruct β' as [c' v'|c' v'|E' qs'|M' qs' n']; simpl in heq; simplify_eq;
      try (exfalso; by apply hb');
      first [ exact (recv_any _ _ _ _ _ HQ)
            | by exists Q
            | (destruct HQ as (x & Q0 & Hs & _); eexists _, x, Q0; split; [exact Hs|reflexivity]) ]. }
  apply (proj2 (obs_step_def _ _ _)) in HQ''.
  exact (Href (lts_performs_spec2 t (ActExt β') (exist _ Q'' HQ''))).
Qed.

(* ** The observers of the characterisation

    [gen k s] follows the trace [s], then behaves as [k].  An output is put
    in parallel; a blocking action is a prefix in a sum with [τ.①], whose
    continuation succeeds unless the value received, or the outcome
    accepted, is the one of the trace. *)

Definition succP : proc := PG GSucc.

Definition qexps (qs : list qubit) : list exp := (λ q, EVal (VQubit q)) <$> qs.

Lemma eval_qexps qs : eval_qubits (qexps qs) = Some qs.
Proof.
  unfold eval_qubits, qexps. induction qs as [|q qs IH]; [done|].
  simpl in *.
  change (mapM eval_qubit ((λ q0 : qubit, EVal (VQubit q0)) <$> qs)
            ≫= (λ k : list qubit, mret (q :: k)) = Some (q :: qs)).
  by rewrite IH.
Qed.

Definition check (v : val) (P : proc) : proc := PIte (EEq (EVar 0) (EVal v)) P succP.

Definition tau_succ : guard := GPre (PTau 0) succP.

Fixpoint gen (k : proc) (s : list lact) : proc :=
  match s with
  | [] => k
  | LOut c v :: s => PPar (gen k s) (PSend 0 c (EVal v))
  | LIn c v :: s => PG (GSum (GPre (PRecv 0 c 0) (check v (gen k s))) tau_succ)
  | LOp E qs :: s => PG (GSum (GPre (POp 0 E (qexps qs)) (gen k s)) tau_succ)
  | LMeas M qs n :: s =>
      PG (GSum (GPre (PMeas 0 M (qexps qs) 0) (check (VNat n) (gen k s))) tau_succ)
  end.

Lemma qexps_fv qs : concat (map exp_fv (qexps qs)) = [].
Proof. induction qs as [|q qs IH]; [done|]. simpl. by rewrite IH. Qed.

Section Generators.
  Context (k : proc) (Hk_fv : fv k = []) (Hk_good : goodb k = false).

  Lemma gen_fv s : fv (gen k s) = [].
  Proof.
    induction s as [|[c v|c v|E qs|M qs n] s IH]; simpl; [done| | | |];
      rewrite ?IH; try done; by rewrite ?qexps_fv.
  Qed.

  Lemma gen_subst s w : subst (gen k s) 0 w = gen k s.
  Proof. apply subst_fresh. rewrite gen_fv. set_solver. Qed.

  Lemma gen_ungood s : goodb (gen k s) = false.
  Proof. induction s as [|[c v|c v|E qs|M qs n] s IH]; simpl; try done. by rewrite IH. Qed.

  Lemma check_subst v w s :
    subst (check v (gen k s)) 0 w = PIte (EEq (EVal w) (EVal v)) (gen k s) succP.
  Proof. simpl. by rewrite gen_subst. Qed.

  Lemma check_same v s : PIte (EEq (EVal v) (EVal v)) (gen k s) succP ≡* gen k s.
  Proof. apply cgr_of_cs, cs_ite_t. simpl. by rewrite bool_decide_eq_true_2. Qed.

  Lemma check_other v w s : w ≠ v → good (PIte (EEq (EVal w) (EVal v)) (gen k s) succP).
  Proof. intros Hne. unfold good. simpl. by rewrite bool_decide_eq_false_2. Qed.

  (* The steps of a blocking prefix of [gen]. *)
  Lemma gen_guard_step α0 P0 Q :
    tstep (PG (GSum (GPre α0 P0) tau_succ)) τ Q → Q = succP ∨ ∃ t, α0 = PTau t ∨ ∃ t', α0 = PTauPair t t'.
  Proof.
    intros Hs. apply succ_spec in Hs. simpl in Hs. apply elem_of_app in Hs as [Hs|Hs].
    - right. destruct α0; simpl in Hs; try set_solver; eauto.
    - left. by apply list_elem_of_singleton in Hs.
  Qed.

  Lemma gen_step_tau β s Q : blocking β → tstep (gen k (β :: s)) τ Q → Q = succP.
  Proof.
    intros hb Hs. destruct β as [c v|c v|E qs|M qs n]; [exfalso; by apply hb| | |];
      apply gen_guard_step in Hs as [->|(t & [Et|(t' & Et)])]; first [done|discriminate].
  Qed.

  Lemma gen_tau β s : blocking β → tstep (gen k (β :: s)) τ succP.
  Proof.
    intros hb. destruct β as [c v|c v|E qs|M qs n]; [exfalso; by apply hb| | |];
      apply succ_spec; simpl; by left.
  Qed.

  (* The external steps of [gen] on a blocking action: only those of the
      prefix, to the continuation checked against the trace. *)
  Lemma gen_in_step c v s μ Q :
    tstep (gen k (LIn c v :: s)) (ActExt μ) Q ↔
      ∃ w, μ = LIn c w ∧ Q = PIte (EEq (EVal w) (EVal v)) (gen k s) succP.
  Proof.
    destruct μ as [c' w|c' w|E qs|M qs n]; simpl.
    - rewrite <- succ_spec. simpl. split; [set_solver|]. by intros (? & ? & _).
    - rewrite <- succ_spec. simpl. case_decide as Hc; simpl.
      + subst c'. rewrite gen_subst. split.
        * intros Hin%list_elem_of_singleton. eauto.
        * intros (w' & E & ->). simplify_eq. by left.
      + split; [set_solver|]. intros (? & ? & _). simplify_eq.
    - rewrite <- succ_spec. simpl. split; [set_solver|]. by intros (? & ? & _).
    - split.
      + intros (x & Q0 & Hs & _). apply succ_spec in Hs. simpl in Hs. set_solver.
      + by intros (? & ? & _).
  Qed.

  Lemma gen_op_step E qs s μ Q :
    tstep (gen k (LOp E qs :: s)) (ActExt μ) Q ↔ μ = LOp E qs ∧ Q = gen k s.
  Proof.
    destruct μ as [c' w|c' w|E' qs'|M qs'' n]; simpl.
    - rewrite <- succ_spec. simpl. split; [set_solver|]. by intros (? & _).
    - rewrite <- succ_spec. simpl. split; [set_solver|]. by intros (? & _).
    - rewrite <- succ_spec. simpl. rewrite eval_qexps. case_decide as Hc; simpl.
      + destruct Hc as [-> [= ->]]. split.
        * intros Hin%list_elem_of_singleton. by subst.
        * intros (_ & ->). by left.
      + split; [set_solver|]. intros (E0 & _). simplify_eq. exfalso. by apply Hc.
    - split.
      + intros (x & Q0 & Hs & _). apply succ_spec in Hs. simpl in Hs. set_solver.
      + by intros (? & _).
  Qed.

  Lemma gen_meas_step M qs n s μ Q :
    tstep (gen k (LMeas M qs n :: s)) (ActExt μ) Q ↔
      ∃ n', μ = LMeas M qs n' ∧ Q = PIte (EEq (EVal (VNat n')) (EVal (VNat n))) (gen k s) succP.
  Proof.
    destruct μ as [c' w|c' w|E' qs'|M' qs' n']; simpl.
    - rewrite <- succ_spec. simpl. split; [set_solver|]. by intros (? & ? & _).
    - rewrite <- succ_spec. simpl. split; [set_solver|]. by intros (? & ? & _).
    - rewrite <- succ_spec. simpl. split; [set_solver|]. by intros (? & ? & _).
    - split.
      + intros (x & Q0 & Hs & ->). apply succ_spec in Hs. simpl in Hs.
        rewrite eval_qexps in Hs. case_decide as Hc; [|set_solver].
        destruct Hc as (-> & <- & [= ->]). apply list_elem_of_singleton in Hs as ->.
        exists n'. split; [done|]. apply check_subst.
      + intros (n'' & E & ->). simplify_eq. exists 0, (check (VNat n) (gen k s)).
        split; [|by rewrite check_subst].
        apply succ_spec. simpl. rewrite eval_qexps, decide_True by done. by left.
  Qed.

  #[global] Instance gen_test_spec : Completeness.test_spec (gen k).
  Proof.
    split.
    - intros s. unfold good. by rewrite gen_ungood.
    - intros [c v|c v|E qs|M qs n] s.
      + exists (PPar (gen k s) 𝟘). split; [|apply cgr_par_nil].
        apply obs_step_def. apply ustep_par_out_emit.
      + exists (PIte (EEq (EVal v) (EVal v)) (gen k s) succP). split; [|apply check_same].
        apply obs_step_def, gen_in_step. eauto.
      + exists (gen k s). split; [|done]. apply obs_step_def, gen_op_step. done.
      + exists (PIte (EEq (EVal (VNat n)) (EVal (VNat n))) (gen k s) succP).
        split; [|apply check_same]. apply obs_step_def, gen_meas_step. eauto.
    - intros β s hb. exists succP. apply obs_step_def. by apply gen_tau.
    - intros β s t hb Hs. apply obs_step_def, (gen_step_tau β s t hb) in Hs as ->. done.
    - intros β s t hb Hs. apply obs_step_def in Hs.
      destruct β as [c v|c v|E qs|M qs n]; [exfalso; by apply hb| | |].
      + apply gen_in_step in Hs as (w & E & ->). simplify_eq. apply check_same.
      + apply gen_op_step in Hs as (_ & ->). done.
      + apply gen_meas_step in Hs as (n' & E & ->). simplify_eq. apply check_same.
    - intros t β μ s hb Hs Hne. apply obs_step_def in Hs.
      destruct β as [c v|c v|E qs|M qs n]; [exfalso; by apply hb| | |].
      + apply gen_in_step in Hs as (w & -> & ->). apply check_other.
        intros ->. by apply Hne.
      + apply gen_op_step in Hs as (-> & _). done.
      + apply gen_meas_step in Hs as (n' & -> & ->). apply check_other.
        intros [= ->]. by apply Hne.
  Qed.
End Generators.

(* The observer of convergence: [τ.①] after the trace. *)
Definition kconv : proc := PG (GPre (PTau 0) succP).
Definition tconv : list lact → proc := gen kconv.

#[global] Instance tconv_spec : Completeness.test_convergence_spec tconv.
Proof.
  split.
  - by apply gen_test_spec.
  - intros μ. destruct μ; intros H; now apply H.
  - exists succP. apply obs_step_def, succ_spec. simpl. by left.
  - intros e He. apply obs_step_def, succ_spec in He. simpl in He.
    apply list_elem_of_singleton in He as ->. done.
Qed.

(* The observer of a co-acceptance set: for each class of [E], a blocking
    action of that class, then [①]. *)
Definition ta_prefix (p : lpre) : prefix :=
  match p with
  | PChan c => PRecv 0 c 0
  | POpAll => POp 0 0 []
  | PMeasAll => PMeas 0 0 [] 0
  end.

Fixpoint sumg (l : list lpre) : guard :=
  match l with
  | [] => GNil []
  | p :: l => GSum (GPre (ta_prefix p) succP) (sumg l)
  end.

Definition ta0 (E : gset lpre) : proc := PG (sumg (elements E)).
Definition ta (E : gset lpre) : list lact → proc := gen (ta0 E).

Lemma sumg_fv l : gfv (sumg l) = [].
Proof. induction l as [|[c| |] l IH]; simpl; [done|..]; by rewrite IH. Qed.

Lemma sumg_ungood l : ggoodb (sumg l) = false.
Proof. induction l as [|p l IH]; simpl; [done|]. rewrite IH. by destruct p. Qed.

Lemma sumg_tau l : gsucc (sumg l) UTau = [].
Proof. induction l as [|[c| |] l IH]; simpl; [done|..]; by rewrite IH. Qed.

Lemma sumg_out l c v : gsucc (sumg l) (UAct (AOut c v)) = [].
Proof. induction l as [|[c'| |] l IH]; simpl; [done|..]; by rewrite IH. Qed.

Lemma sumg_step_inv l μ Q :
  tstep (PG (sumg l)) (ActExt μ) Q → l𝝳 (lΦ μ) ∈ l ∧ ¬ is_out μ ∧ Q = succP.
Proof.
  revert Q. induction l as [|p l IH]; intros Q Hs.
  - destruct μ as [c v|c v|E qs|M qs n]; simpl in Hs.
    + apply succ_spec in Hs. simpl in Hs. set_solver.
    + apply succ_spec in Hs. simpl in Hs. set_solver.
    + apply succ_spec in Hs. simpl in Hs. set_solver.
    + destruct Hs as (x & Q0 & Hs & _). apply succ_spec in Hs. simpl in Hs. set_solver.
  - destruct μ as [c v|c v|E qs|M qs n]; simpl in Hs.
    + apply succ_spec in Hs. simpl in Hs. rewrite sumg_out in Hs.
      destruct p; simpl in Hs; set_solver.
    + apply succ_spec in Hs. simpl in Hs. apply elem_of_app in Hs as [Hq|Hq].
      * destruct p as [c'| |]; simpl in Hq; try set_solver.
        case_decide; [subst|set_solver]. apply list_elem_of_singleton in Hq as ->.
        split_and!; [set_solver|by intros ?|done].
      * destruct (IH Q (proj1 (succ_spec (PG (sumg l)) _ _) Hq)) as (Hin & Ho & ->).
        split_and!; [set_solver|done|done].
    + apply succ_spec in Hs. simpl in Hs. apply elem_of_app in Hs as [Hq|Hq].
      * destruct p as [c'| |]; simpl in Hq; try set_solver.
        case_decide; [|set_solver]. apply list_elem_of_singleton in Hq as ->.
        split_and!; [set_solver|by intros ?|done].
      * destruct (IH Q (proj1 (succ_spec (PG (sumg l)) _ _) Hq)) as (Hin & Ho & ->).
        split_and!; [set_solver|done|done].
    + destruct Hs as (x & Q0 & Hs & ->). apply succ_spec in Hs. simpl in Hs.
      apply elem_of_app in Hs as [Hq|Hq].
      * destruct p as [c'| |]; simpl in Hq; try set_solver.
        case_decide; [|set_solver]. apply list_elem_of_singleton in Hq as ->.
        split_and!; [set_solver|by intros ?|done].
      * assert (Hs : tstep (PG (sumg l)) (ActExt (LMeas M qs n)) (subst Q0 x (VNat n)))
          by (exists x, Q0; split; [by apply succ_spec|done]).
        destruct (IH _ Hs) as (Hin & Ho & HQ). rewrite HQ.
        split_and!; [set_solver|done|done].
Qed.

Lemma sumg_step_ex l p : p ∈ l → ∃ μ, l𝝳 (lΦ μ) = p ∧ tstep (PG (sumg l)) (ActExt μ) succP.
Proof.
  induction l as [|p' l IH]; intros Hp; [set_solver|].
  destruct (decide (p = p')) as [->|Hne].
  - destruct p' as [c| |].
    + exists (LIn c (VNat 0)). split; [done|]. apply succ_spec. simpl. rewrite ?decide_True by done. simpl.
      first [by left|apply elem_of_app; left; by left].
    + exists (LOp 0 []). split; [done|]. apply succ_spec. simpl. rewrite ?decide_True by done. simpl.
      first [by left|apply elem_of_app; left; by left].
    + exists (LMeas 0 [] 0). split; [done|]. exists 0, succP. split; [|done].
      apply succ_spec. simpl. rewrite ?decide_True by done. simpl.
      first [by left|apply elem_of_app; left; by left].
  - destruct (IH ltac:(set_solver)) as (μ & Hμ & Hs). exists μ. split; [done|].
    destruct μ as [c v|c v|E qs|M qs n]; simpl in Hs |- *.
    + apply succ_spec. simpl. apply elem_of_app. right. by apply succ_spec in Hs.
    + apply succ_spec. simpl. apply elem_of_app. right. by apply succ_spec in Hs.
    + apply succ_spec. simpl. apply elem_of_app. right. by apply succ_spec in Hs.
    + destruct Hs as (x & Q0 & Hs & HQ). exists x, Q0. split; [|done].
      apply succ_spec. simpl. apply elem_of_app. right. by apply succ_spec in Hs.
Qed.

#[global] Instance ta_spec :
  Completeness.test_co_acceptance_set_spec lpre ta (λ x, l𝝳 (lΦ x)).
Proof.
  split.
  - intros E. apply gen_test_spec.
    + unfold ta0. simpl. apply sumg_fv.
    + unfold ta0. simpl. apply sumg_ungood.
  - intros E H. apply H. change (gsucc (sumg (elements E)) UTau = []). apply sumg_tau.
  - intros E η Hη. destruct η as [c v| | |]; try done.
    intros H. apply H. change (gsucc (sumg (elements E)) (UAct (AOut c v)) = []). apply sumg_out.
  - intros E β e hb Hs. apply obs_step_def in Hs.
    apply sumg_step_inv in Hs as (Hin & _ & _). by apply elem_of_elements.
  - intros E pβ Hp. apply elem_of_elements in Hp.
    destruct (sumg_step_ex _ _ Hp) as (μ & Hμ & Hs).
    exists succP, μ. split; [by apply obs_step_def|done].
  - intros β e' E hb Hs. apply obs_step_def in Hs.
    apply sumg_step_inv in Hs as (_ & _ & ->). done.
Qed.

(* ** The process side of the abstraction

    [abs_prog_core]: what a process accepts is, up to [l𝝳], closed under the
    abstraction, as soon as it accepts every operation, and every
    measurement once it accepts one. *)

Lemma abs_prog_core {X} {GL : @gLts X lact lact_ExtAction} (x : X)
  (Hop : ∀ E qs, x ⟶[LOp E qs])
  (Hm : (∃ M qs n, x ⟶[LMeas M qs n]) → ∀ M qs, ∃ n, x ⟶[LMeas M qs n])
  (β β' : lact) :
  ¬ is_out β' → l𝝳 (lΦ β) = l𝝳 (lΦ β') →
  (∃ μ', (∃ μ2, x ⟶[μ2] ∧ μ' = lco μ2 ∧ ¬ is_out μ') ∧ lΦ β = lΦ μ') →
  (∃ μ', (∃ μ2, x ⟶[μ2] ∧ μ' = lco μ2 ∧ ¬ is_out μ') ∧ lΦ β' = lΦ μ').
Proof.
  intros hb' heq (μ' & (μ2 & Hacc & -> & Hb) & HΦ).
  destruct β' as [c v|c v|E qs|M qs n].
  - exfalso. by apply hb'.
  - exists (lco μ2). split; [eauto|]. rewrite <- HΦ.
    destruct β; simpl in heq |- *; congruence.
  - exists (LOp E qs). split; [|done].
    exists (LOp E qs). split_and!; [apply Hop|done|by intros ?].
  - destruct β as [| | |M0 qs0 n0]; simpl in heq; try discriminate.
    destruct μ2 as [| | |M1 qs1 n1]; simpl in HΦ; try discriminate.
    destruct (Hm (ex_intro _ M1 (ex_intro _ qs1 (ex_intro _ n1 Hacc))) M qs) as (n2 & Hn2).
    exists (LMeas M qs n2). split; [|done].
    exists (LMeas M qs n2). split_and!; [done|done|by intros ?].
Qed.

Section Characterisation.
  Context `{QM : QuantumModel} `{SC : !Countable St}.

  Notation pconf := (proc * St)%type.

  #[global] Program Instance pconf_FiniteImage : FiniteImagegLts pconf lact.
  Next Obligation.
    intros x α. eapply (in_list_finite (lsuccs x α)).
    intros y Hy%bool_decide_unpack. exact Hy.
  Defined.

  Lemma pfw_dual_image_iff (x y : pconf * MO lact) (α : lact) :
    (∃ α', dual α' α ∧ x ⟶[α'] y) ↔ x ⟶[co α] y.
  Proof.
    split.
    - intros (α' & hd & hl). assert (α' = co α) as ->; [| done].
      apply lact_UniqueDual. by symmetry.
    - intros hl. exists (co α). split; [| done].
      symmetry. exact (proj2_sig (exists_dual α)).
  Qed.

  #[global] Instance pconf_FW_coFiniteImage : coFiniteImagegLts (pconf * MO lact) lact.
  Proof.
    unshelve refine {|
      cofolts_states_countable := folts_states_countable;
      cofolts_tau_next_states_finite := _;
      cofolts_next_states_decidable := _;
      cofolts_next_states_finite := _;
    |}.
    - intros p α q. destruct (decide (p ⟶[co α] q)) as [h | h].
      + left. by apply pfw_dual_image_iff.
      + right. intros hc. apply h. by apply pfw_dual_image_iff.
    - intros p α. unfold dsig.
      eapply (in_list_finite (map proj1_sig (finite.enum (dsig (fun q => p ⟶[co α] q))))).
      intros q hq%bool_decide_unpack.
      apply list_elem_of_fmap. apply pfw_dual_image_iff in hq.
      exists (dexist q hq). split; [reflexivity | eapply elem_of_enum].
  Defined.

  (* *** What a process accepts *)

  Lemma pmo_out x μ : μ ∈ dom (fmo x) → ∃ c v, μ = LOut c v.
  Proof. intros (c & v & -> & _)%gmultiset_elem_of_dom%fmo_elem. eauto. Qed.

  Lemma pmo_step x μ : μ ∈ dom (fmo x) → ∃ y, x ⟶[μ] y.
  Proof.
    intros Hin%gmultiset_elem_of_dom. destruct (fmo_witness x μ Hin) as [y [_ Hs]]. eauto.
  Qed.

  Lemma pmo_of_step x c v y : x ⟶[LOut c v] y → LOut c v ∈ dom (fmo x).
  Proof.
    intros Hs. apply gmultiset_elem_of_dom. apply pconf_step_def in Hs.
    by eapply fmo_spec1.
  Qed.

  Lemma p_accepts_op (x : pconf) E qs : x ⟶[LOp E qs].
  Proof.
    destruct x as [P ρ].
    assert (Hs : (P, ρ) ⟶[LOp E qs] (P, sop_apply E qs ρ)) by (apply pconf_step_def; constructor).
    apply (lts_performs_spec2 (P, ρ) (ActExt (LOp E qs))). eexists. exact Hs.
  Qed.

  Lemma p_meas_code (x : pconf) M qs n y :
    x ⟶[LMeas M qs n] y → x.2 ≠ szero ∧ ∃ k : Out (meas_of M qs), n = code _ k.
  Proof.
    intros Hs. apply pconf_step_def in Hs.
    inversion Hs as [| | | | | |P ρ M' qs' k Hn]; subst. simpl. split; [|eauto].
    intros ->. apply Hn. unfold meas_branch. apply app_szero.
  Qed.

  Lemma p_accepts_meas (x : pconf) M qs : x.2 ≠ szero → ∃ n, x ⟶[LMeas M qs n].
  Proof.
    destruct x as [P ρ]. intros Hρ. simpl in Hρ.
    destruct (meas_nonzero_branch M qs ρ Hρ) as (k & Hk).
    exists (code _ k).
    assert (Hs : (P, ρ) ⟶[LMeas M qs (code _ k)] (P, meas_branch M qs k ρ))
      by (apply pconf_step_def; by constructor).
    apply (lts_performs_spec2 (P, ρ) (ActExt (LMeas M qs (code _ k)))).
    eexists. exact Hs.
  Qed.

  Lemma p_meas_all (x : pconf) :
    (∃ M qs n, x ⟶[LMeas M qs n]) → ∀ M qs, ∃ n, x ⟶[LMeas M qs n].
  Proof.
    intros (M & qs & n & Hacc) M' qs'. apply lts_performs_spec1 in Hacc as (y & Hs).
    apply p_accepts_meas. by apply p_meas_code in Hs as [? _].
  Qed.

  (* The same for the forwarder: the mailbox takes no part in the memory. *)
  Lemma fw_step_mem (x : pconf * MO lact) μ y :
    x ⟶[μ] y → ¬ is_out μ → (∀ c v, μ ≠ LIn c v) → ∃ p', x.1 ⟶[μ] p'.
  Proof.
    destruct x as [p m]. intros Hs Hb Hi.
    inversion Hs as [α0 a1 a2 b0 l|α0 a0 b1 b2 l|μ1 μ2 a1 a2 b1 b2 eq l1 l2]; subst.
    - simpl. by exists a2.
    - inversion l; subst; exfalso;
        destruct μ as [c v|c v| |]; simpl in *; subst; simpl in *;
        first [by apply Hb | (eapply Hi; reflexivity) | tauto].
  Qed.

  Lemma fw_accepts_op (x : pconf * MO lact) E qs : x ⟶[LOp E qs].
  Proof.
    destruct x as [p m].
    pose proof (p_accepts_op p E qs) as Hr.
    apply lts_performs_spec1 in Hr as (p' & Hs).
    assert (Hs' : (p, m) ⟶[LOp E qs] (p', m)) by (by apply ParLeft).
    apply (lts_performs_spec2 (p, m) (ActExt (LOp E qs))). eexists. exact Hs'.
  Qed.

  Lemma fw_meas_all (x : pconf * MO lact) :
    (∃ M qs n, x ⟶[LMeas M qs n]) → ∀ M qs, ∃ n, x ⟶[LMeas M qs n].
  Proof.
    destruct x as [p m]. intros (M & qs & n & Hacc) M' qs'.
    apply lts_performs_spec1 in Hacc as (y & Hs).
    destruct (fw_step_mem _ _ _ Hs ltac:(by intros ?) ltac:(done)) as (p' & Hp).
    simpl in Hp. apply pconf_step_def in Hp.
    assert (Hacc : p ⟶[LMeas M qs n]).
    { apply (lts_performs_spec2 p (ActExt (LMeas M qs n))).
      eexists. apply pconf_step_def. exact Hp. }
    destruct (p_meas_all p (ex_intro _ M (ex_intro _ qs (ex_intro _ n Hacc))) M' qs')
      as (n' & Hn').
    exists n'. apply lts_performs_spec1 in Hn' as (p'' & Hs').
    assert (Hs'' : (p, m) ⟶[LMeas M' qs' n'] (p'', m)) by (by apply ParLeft).
    apply (lts_performs_spec2 (p, m) (ActExt (LMeas M' qs' n'))).
    eexists. exact Hs''.
  Qed.

  (* *** A process and an observer *)

  Lemma ess_right_step Q μ : μ ∈ dom (tmo Q) ∪ tmem Q → ∃ Q', Q ⟶[μ] Q'.
  Proof.
    intros [Hin|Hin]%elem_of_union.
    - apply gmultiset_elem_of_dom in Hin. by apply tmo_step.
    - by apply tmem_step.
  Qed.

  (* Every synchronisation goes through an output of the process, or an
      output or a memory action of the observer. *)
  Lemma cover_test μ1 Q μ2 Q' :
    Q ⟶[μ2] Q' → μ2 = lco μ1 → (∀ M qs n, μ1 = LMeas M qs n → ∃ k, n = code (meas_of M qs) k) →
    is_out μ1 ∨ μ2 ∈ dom (tmo Q) ∪ tmem Q.
  Proof.
    intros Ht -> Hcode. destruct μ1 as [c v|c v|E qs|M qs n].
    - by left.
    - right. apply elem_of_union_l, gmultiset_elem_of_dom. exact (tmo_of_step _ _ _ _ Ht).
    - right. apply elem_of_union_r. exact (tmem_of_op _ _ _ _ Ht).
    - right. apply elem_of_union_r. destruct (Hcode M qs n eq_refl) as (k & ->).
      exact (tmem_of_meas _ _ _ _ _ Ht).
  Qed.

  #[global] Program Instance pconf_Inter_test : Prop_of_Inter pconf proc lact lact dual :=
    {| lts_essential_actions_left x := dom (fmo x) ;
       lts_essential_actions_right Q := dom (tmo Q) ∪ tmem Q ;
       lts_co_inter_action_left ξ _ := {[ lco ξ ]} ;
       lts_co_inter_action_right ξ _ := {[ lco ξ ]} |}.
  Next Obligation. intros x ξ hin. apply step_witness. by apply pmo_step. Defined.
  Next Obligation. intros Q ξ hin. apply step_witness. by apply ess_right_step. Defined.
  Next Obligation.
    intros x μ1 x' Q μ2 Q' hl1 hl2 hinter.
    assert (Hcode : ∀ M qs n, μ1 = LMeas M qs n → ∃ k, n = code (meas_of M qs) k).
    { intros M qs n ->. apply p_meas_code in hl1 as [_ Hk]. exact Hk. }
    destruct (cover_test μ1 Q μ2 Q' hl2 hinter Hcode) as [Ho|Hr]; [|by right].
    left. destruct μ1 as [c v| | |]; try done. exact (pmo_of_step _ _ _ _ hl1).
  Defined.
  Next Obligation.
    intros x x' ξ μ Q hmem hl hinter; simpl in *. subst. rewrite lco_involutive. set_solver.
  Defined.
  Next Obligation.
    intros Q Q' ξ μ x hmem hl hinter; simpl in *. subst. set_solver.
  Defined.

  #[global] Program Instance pconf_Inter_FW_test :
    Prop_of_Inter (pconf * MO lact) proc lact lact dual :=
    {| lts_essential_actions_left p := dom (fmo p.1) ∪ dom (MO_without_not_nb p.2) ;
       lts_essential_actions_right Q := dom (tmo Q) ∪ tmem Q ;
       lts_co_inter_action_left ξ _ := {[ lco ξ ]} ;
       lts_co_inter_action_right ξ _ := {[ lco ξ ]} |}.
  Next Obligation.
    intros (x, m) ξ hin. simpl in *.
    destruct (decide (ξ ∈ dom (MO_without_not_nb m))) as [hm | hm].
    - apply gmultiset_elem_of_dom in hm.
      apply lts_MO_nb_with_nb_spec1 in hm as (nb & hmem).
      assert (m = {[+ ξ +]} ⊎ (m ∖ {[+ ξ +]})) as heq by multiset_solver.
      exists (x, m ∖ {[+ ξ +]}). apply ParRight.
      rewrite heq at 1. by apply lts_multiset_minus.
    - assert (ξ ∈ dom (fmo x)) as hx by set_solver.
      destruct (step_witness x ξ (pmo_step x ξ hx)) as (y & hl).
      exists (y, m). by apply ParLeft.
  Defined.
  Next Obligation. intros Q ξ hin. apply step_witness. by apply ess_right_step. Defined.
  Next Obligation.
    intros (x, m) μ1 (x', m') Q μ2 Q' hl1 hl2 hinter.
    assert (Hcode : ∀ M qs n, μ1 = LMeas M qs n → ∃ k, n = code (meas_of M qs) k).
    { intros M qs n ->.
      destruct (fw_step_mem _ _ _ hl1 ltac:(by intros ?) ltac:(done)) as (p' & Hp).
      apply p_meas_code in Hp as [_ Hk]. exact Hk. }
    destruct (cover_test μ1 Q μ2 Q' hl2 hinter Hcode) as [Ho|Hr]; [|by right].
    simpl. left. destruct μ1 as [c v| | |]; try done. inversion hl1; subst.
      + apply elem_of_union. left. by eapply pmo_of_step.
      + apply elem_of_union. right.
        assert (non_blocking (LOut c v)) as nb by done.
        eapply non_blocking_action_in_ms in l; eauto.
        apply gmultiset_elem_of_dom.
        apply (lts_MO_nb_with_nb_spec2 (LOut c v) _ nb). multiset_solver.
  Defined.
  Next Obligation.
    intros x x' ξ μ Q hmem hl hinter; simpl in *. subst. rewrite lco_involutive. set_solver.
  Defined.
  Next Obligation.
    intros Q Q' ξ μ x hmem hl hinter; simpl in *. subst. set_solver.
  Defined.

  (* *** The abstraction *)

  #[global] Program Instance pconf_AbsAction :
    @AbsAction pconf proc lfin lpre lact lact_ExtAction lΦ l𝝳 _ _ _ obs_gLtsEq _.
  Next Obligation.
    intros t β β' hb hb' heq hmem. exact (obs_abs_test t β β' hb hb' heq hmem).
  Qed.
  Next Obligation.
    intros x β β' hb hb' heq hmem.
    exact (abs_prog_core x (p_accepts_op x) (p_meas_all x) β β' hb' heq hmem).
  Qed.

  Definition coR_abs_lq (x : pconf) : gset lpre :=
    set_map (λ μ, l𝝳 (lΦ μ)) (dom (fmo x)) ∪ {[ POpAll ]}
    ∪ (if decide (x.2 = szero) then ∅ else {[ PMeasAll ]}).

  #[global] Program Instance pconf_FinitaryAbsAction :
    @FinitaryAbsAction pconf proc lfin lpre lact lact_ExtAction lΦ l𝝳 _ _ _ obs_gLtsEq _ _ _ :=
    {| coR_abs := coR_abs_lq |}.
  Next Obligation.
    intros x pre_μ hmem. unfold coR_abs_lq in hmem.
    apply elem_of_union in hmem as [hmem|hmem]; [apply elem_of_union in hmem as [hmem|hmem]|].
    - apply elem_of_map in hmem as (ξ & -> & hin).
      destruct (pmo_out x ξ hin) as (c & v & ->).
      exists (LIn c v). split; [|done].
      exists (LOut c v). split_and!; [|done|by intros ?].
      destruct (pmo_step x _ hin) as (y & hl).
      apply (lts_performs_spec2 x (ActExt (LOut c v))). eexists. exact hl.
    - apply elem_of_singleton in hmem as ->.
      exists (LOp 0 []). split; [|done].
      exists (LOp 0 []). split_and!; [apply p_accepts_op|done|by intros ?].
    - case_decide as Hz; [set_solver|]. apply elem_of_singleton in hmem as ->.
      destruct (p_accepts_meas x 0 [] Hz) as (n & Hn).
      exists (LMeas 0 [] n). split; [|done].
      exists (LMeas 0 [] n). split_and!; [done|done|by intros ?].
  Qed.
  Next Obligation.
    intros pre_μ x (μ & (μ2 & haccept & hsync & hb) & ->).
    simpl in hsync. subst μ. unfold coR_abs_lq.
    apply lts_performs_spec1 in haccept as (y & hl).
    destruct μ2 as [c v|c v|E qs|M qs n].
    - apply elem_of_union_l, elem_of_union_l, elem_of_map.
      exists (LOut c v). split; [done|]. by eapply pmo_of_step.
    - exfalso. by apply hb.
    - apply elem_of_union_l, elem_of_union_r. simpl. set_solver.
    - apply elem_of_union_r. apply p_meas_code in hl as [Hz _].
      rewrite decide_False by done. simpl. set_solver.
  Qed.

  #[global] Program Instance pconf_AbsAction_FW :
    @AbsAction (pconf * MO lact) proc lfin lpre lact lact_ExtAction lΦ l𝝳 _ _ _ obs_gLtsEq _.
  Next Obligation.
    intros t β β' hb hb' heq hmem. exact (obs_abs_test t β β' hb hb' heq hmem).
  Qed.
  Next Obligation.
    intros x β β' hb hb' heq hmem.
    exact (abs_prog_core x (fw_accepts_op x) (fw_meas_all x) β β' hb' heq hmem).
  Qed.

  #[global] Program Instance pconf_FinitaryAbsAction_FW :
    @FinitaryAbsAction (pconf * MO lact) proc lfin lpre lact lact_ExtAction lΦ l𝝳 _ _ _
      obs_gLtsEq _ _ _ :=
    {| FinitaryAbsAction_Abs := pconf_AbsAction_FW ;
       coR_abs p := coR_abs p.1
                    ∪ dom (gmultiset_map (fun x => l𝝳 (lΦ (co x)))
                             (MO_without_not_nb p.2)) |}.
  Next Obligation.
    intros p pre_mu hmem. destruct p as (p, m). simpl in *.
    apply elem_of_union in hmem. destruct hmem as [in_p | in_M].
    + change (pre_mu ∈ coR_abs p) in in_p. eapply coR_abs_spec1 in in_p.
      destruct in_p as (μ & mem & eq). subst.
      exists μ. split.
      - destruct mem as (μ2 & tr & duo & b).
        eapply lts_performs_spec1 in tr as (p2 & tr).
        exists μ2. repeat split; eauto.
        eapply lts_performs_spec2. exists (p2 ▷ m).
        eapply ParLeft. exact tr.
      - eauto.
    + simpl in *. eapply gmultiset_elem_of_dom, elem_of_gmultiset_map in in_M.
      destruct in_M as (μ & eq & mem).
      apply (lts_MO_nb_with_nb_spec1 μ m) in mem as Hmem. destruct Hmem as (nb & mem2).
      exists (co μ). split; [|exact eq].
      exists μ. split_and!.
      - eapply lts_performs_spec2.
        exists (p, m ∖ {[+ μ +]}).
        eapply ParRight.
        assert (m = {[+ μ +]} ⊎ (m ∖ {[+ μ +]})) as eqm by multiset_solver.
        rewrite eqm at 1.
        eapply lts_multiset_minus. exact nb.
      - exact (proj2_sig (exists_dual μ)).
      - eapply dual_blocks; [exact nb|]. symmetry. exact (proj2_sig (exists_dual μ)).
  Qed.
  Next Obligation.
    intros pre_mu p hmem. destruct hmem as (μ & mem & eq). subst.
    destruct p as (p, m). destruct mem as (μ2 & tr & duo & b).
    eapply lts_performs_spec1 in tr as ((p2 , m2) & eq).
    inversion eq; subst; simpl in *.
    + eapply elem_of_union. left.
      change (l𝝳 (lΦ μ) ∈ coR_abs p). eapply coR_abs_spec2.
      exists μ. split; [|reflexivity]. exists μ2.
      split_and!; [eapply lts_performs_spec2; eexists; exact l|exact duo|exact b].
    + eapply elem_of_union. right.
      eapply gmultiset_elem_of_dom, elem_of_gmultiset_map.
      destruct (decide (non_blocking μ2)) as [nb2 | b2].
      - exists μ2. split; eauto.
        * assert (μ = co μ2) as ->; [| eauto]. eapply lact_UniqueDual; eauto.
        * eapply non_blocking_action_in_ms in l; eauto. subst.
          apply (lts_MO_nb_with_nb_spec2 μ2 _ nb2). multiset_solver.
      - assert (blocking μ2) as Imp; eauto.
        eapply blocking_action_in_ms in Imp as (mem2 & duo2 & nb2); eauto.
        eapply lact_UniqueDual in duo; eauto. subst. contradiction.
  Qed.

  (* ** The characterisations *)

  (* The must preorder on lqCCS processes [(P, ρ)], tested by lqCCS programs
      without memory that act on the memory of the process, is the inclusion
      of co-acceptance sets. *)
  Corollary must_iff_co_acceptance_set_lqCCS (x y : pconf) :
    x ⊑ₘᵤₛₜᵢ y ↔ (x ▷ (∅ : MO lact)) ≼꜀ₒ₋ₐₛ (y ▷ (∅ : MO lact)).
  Proof. exact (equivalence_acc_set_and_must_i_co_trace x y). Qed.

  (* The same, on traces rather than co-traces. *)
  Corollary must_iff_acceptance_set_lqCCS (x y : pconf) :
    x ⊑ₘᵤₛₜᵢ y ↔ (x ▷ (∅ : MO lact)) ≼ₐₛ (y ▷ (∅ : MO lact)).
  Proof. exact (equivalence_acc_set_and_must_i x y). Qed.
End Characterisation.
(* end hide *)
