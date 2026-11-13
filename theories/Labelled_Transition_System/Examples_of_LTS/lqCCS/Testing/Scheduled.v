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
(* * lqCCS: the Smyth must of tested programs

    A program [P] with an initial memory [ρ] is tested by a program [T]
    marked with [①]: the tested system is the pair of [P] and [T], running as [P ∥ T] on
    the memory [ρ], success being that of [T] alone, a component of the scheduled systems of
    [pMust_almost_sure].  A scheduled step of a component is a silent step
    of the configuration LTS, the outcomes of a measurement being grouped
    into one distribution ([sched_step], as [den] in [Denotational.v]); the
    distribution moves as a whole under one choice, the components that do
    not have it stay (admissible schedulers), and the Smyth must of
    [pMust_smyth] compares the success probabilities of the runs.

    Tests without [τ] prefixes ([tau_free]) are the ones whose offers at a
    point of an interaction do not depend on the instant at which a
    component reaches that point; they are the tests of the
    characterisation. *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list.
From TestingTheory Require Import ActTau pMust_almost_sure pMust_smyth.
From TestingTheory Require Import lqCCS.Language.Algebra lqCCS.Language.Quantum lqCCS.Language.Quantum_Weights.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.LTS lqCCS.Language.Congruence lqCCS.Harmony_Lemma.Memory_Harmony.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

(* ** Success: [①] at top level, through parallel composition, restriction,
    evaluated conditionals and sums *)

Fixpoint gsuccessb (g : guard) : bool :=
  match g with
  | ① => true
  | (g1 + g2)%lq => gsuccessb g1 || gsuccessb g2
  | _ => false
  end.

Fixpoint successb (P : proc) : bool :=
  match P with
  | PG g => gsuccessb g
  | P ∥ Q => successb P || successb Q
  | ν P => successb P
  | PIte e P Q =>
      match eval e with
      | Some (VBool true) => successb P
      | Some (VBool false) => successb Q
      | _ => false
      end
  | _ => false
  end.

Definition success (P : proc) : Prop := successb P = true.

#[global] Instance success_dec P : Decision (success P).
Proof. unfold success. apply _. Qed.

(* ** Tests without [τ] *)

Fixpoint tau_freeb (P : proc) : bool :=
  match P with
  | PSend _ _ _ | PVar _ => true
  | PIte _ P Q | P ∥ Q => tau_freeb P && tau_freeb Q
  | ν P | PRec _ _ P => tau_freeb P
  | PG g => gtau_freeb g
  end
with gtau_freeb (g : guard) : bool :=
  match g with
  | GNil _ | ① => true
  | PTau _ ∙ _ => false
  | _ ∙ P => tau_freeb P
  | (g1 + g2)%lq => gtau_freeb g1 && gtau_freeb g2
  end.

Definition tau_free (T : proc) : Prop := tau_freeb T = true.

Section Sched.
  Context `{QM : QuantumModel}.

  (* The outcomes of a measurement that have a non-zero probability: a
      distribution is its support, as in a pLTS. *)
  Definition outs_nz M qs (ρ : St) : list (Out (meas_of M qs)) :=
    filter (λ k, meas_branch M qs k ρ ≠ szero) (outs (meas_of M qs)).

  Lemma outs_nz_spec M qs ρ k : k ∈ outs_nz M qs ρ ↔ meas_branch M qs k ρ ≠ szero.
  Proof.
    unfold outs_nz. rewrite list_elem_of_filter. split; [tauto|]. intros Hk. split; [done|].
    apply list_elem_of_In, outs_all.
  Qed.

  Lemma outs_nz_nonempty M qs ρ : ρ ≠ szero → outs_nz M qs ρ ≠ [].
  Proof.
    intros Hρ E. destruct (meas_nonzero_branch M qs ρ Hρ) as (k & Hk).
    apply (outs_nz_spec M qs ρ k) in Hk. rewrite E in Hk. by apply elem_of_nil in Hk.
  Qed.

  (* ** The scheduled step of a tested program

      [ρ • R —s→ Δ]: the silent steps of [⟨ρ, R⟩] with choice [s], the
      outcomes of a measurement grouped. *)

  Inductive sched_step (ρ : St) (R : proc) (s : choice) : dist proc → Prop :=
  | ss_tau R' : prog_step R s τ R' → sched_step ρ R s [(R', ρ)]
  | ss_op E qs R' :
      prog_step R s (ActExt (PrOp E qs)) R' → sched_step ρ R s [(R', sop_apply E qs ρ)]
  | ss_init qs R' :
      prog_step R s (ActExt (PrInit qs)) R' → sched_step ρ R s [(R', init_apply qs ρ)]
  | ss_meas M qs (Rs : list proc) R0 :
      prog_step R s (ActExt (PrMeas M qs 0)) R0 →
      Forall2 (λ k R', prog_step R s (ActExt (PrMeas M qs (code _ k))) R') (outs_nz M qs ρ) Rs →
      sched_step ρ R s (zip_with (λ k R', (R', meas_branch M qs k ρ)) (outs_nz M qs ρ) Rs).

  Definition par_of (c : proc * proc) : proc := c.1 ∥ c.2.

  Definition conf_sched (ρ : St) (c : proc * proc) (s : choice) (Δ : dist (proc * proc)) : Prop :=
    sched_step ρ (par_of c) s (dmap par_of Δ).

  #[global] Instance lq_SchedSts : SchedSts (proc * proc) choice :=
    {| pMust_scheduled.sstep := conf_sched; psuccess := λ c, success c.2 |}.

  Definition compose (Pρ : proc * St) (T : proc) : dist (proc * proc) := [((Pρ.1, T), Pρ.2)].

  #[global] Instance lq_pTesting : pTesting (proc * St) proc (proc * proc) choice :=
    {| pMust_scheduled.compose := compose |}.

  (* ** The steps of a component are the silent steps of the configuration *)

  Lemma sched_step_conf ρ R s Δ R' ρ' :
    sched_step ρ R s Δ → (R', ρ') ∈ Δ → ⟨ρ, R⟩ ⟶{τ}[s] ⟨ρ', R'⟩.
  Proof.
    intros Hs Hin. inversion Hs as [? Hp|E qs ? Hp|qs ? Hp|M qs Rs R0 Hp0 Hf]; subst.
    - apply list_elem_of_singleton in Hin. simplify_eq. by apply prog_step_conf.
    - apply list_elem_of_singleton in Hin. simplify_eq.
      eapply prog_step_mem_conf; [exact Hp|apply (me_sop ρ (sop_act E qs))|constructor].
    - apply list_elem_of_singleton in Hin. simplify_eq.
      eapply prog_step_mem_conf; [exact Hp|apply (me_sop ρ (init_act qs))|constructor].
    - remember (outs_nz M qs ρ) as ks eqn:Eks. clear Eks Hs.
      clear Hp0. revert Hin. induction Hf as [|k R1 ks Rs Hp _ IH]; simpl; intros Hin; [by apply elem_of_nil in Hin|].
      apply elem_of_cons in Hin as [Hin|Hin]; [|by apply IH]. simplify_eq.
      eapply prog_step_mem_conf; [exact Hp|apply me_meas|constructor].
  Qed.

  Lemma prog_step_meas_any R s M qs n R' :
    prog_step R s (ActExt (PrMeas M qs n)) R' →
    ∀ n', ∃ R'', prog_step R s (ActExt (PrMeas M qs n')) R''.
  Proof.
    intros Hp. remember (ActExt (PrMeas M qs n)) as l eqn:El. revert El.
    induction Hp; intros El n'; simplify_eq;
      try (edestruct IHHp as (R'' & HR''); [done|]; eexists; by econstructor).
    eexists. by apply pr_meas.
  Qed.

  Lemma mem_step_meas_inv ρ M qs n ρ' :
    mem_step ρ CEps (ActExt (MeMeas M qs n)) ρ' →
    ∃ k : Out (meas_of M qs), n = code _ k ∧ ρ' = meas_branch M qs k ρ.
  Proof. inversion 1; subst. by eexists. Qed.

  Lemma conf_sched_step ρ R s ρ' R' :
    ⟨ρ, R⟩ ⟶{τ}[s] ⟨ρ', R'⟩ → ρ' ≠ szero → ∃ Δ, sched_step ρ R s Δ ∧ (R', ρ') ∈ Δ.
  Proof.
    intros Hc Hnz. destruct (conf_step_tau_inv _ _ _ _ _ Hc) as [(Hp & ->)|(a & b & Hp & Hm & Hsy)];
      [|destruct (prog_step_ext_choice _ _ _ _ Hp) as (t & ->)].
    - eexists. split; [by apply ss_tau|]. by apply list_elem_of_singleton.
    - inversion Hsy; subst.
      + inversion Hm; subst. eexists. split; [by apply ss_op|]. by apply list_elem_of_singleton.
      + destruct (mem_step_meas_inv _ _ _ _ _ Hm) as (k & -> & ->).
        assert (Hall : ∀ ks : list (Out (meas_of M qs)),
          ∃ Rs, Forall2 (λ k R'', prog_step R (CTag t) (ActExt (PrMeas M qs (code _ k))) R'') ks Rs
                ∧ (k ∈ ks → (R', meas_branch M qs k ρ) ∈ zip_with (λ k R'', (R'', meas_branch M qs k ρ)) ks Rs)).
        { intros ks. induction ks as [|k' ks (Rs & Hf & Hin)].
          - exists []. split; [constructor|]. by intros ?%elem_of_nil.
          - destruct (decide (code _ k' = code _ k)) as [Hk|Hne].
            + apply code_inj in Hk. subst k'.
              exists (R' :: Rs). split; [by constructor|]. intros _. simpl. by left.
            + destruct (prog_step_meas_any _ _ _ _ _ _ Hp (code _ k')) as (R'' & HR'').
              exists (R'' :: Rs). split; [by constructor|].
              intros [->|Hk]%elem_of_cons; [by destruct Hne|]. simpl. right. by apply Hin. }
        destruct (Hall (outs_nz M qs ρ)) as (Rs & Hf & Hin).
        exists (zip_with (λ k R'', (R'', meas_branch M qs k ρ)) (outs_nz M qs ρ) Rs).
        split; [|by apply Hin, outs_nz_spec].
        destruct (prog_step_meas_any _ _ _ _ _ _ Hp 0) as (R0 & HR0). by apply (ss_meas _ _ _ M qs Rs R0).
      + inversion Hm; subst. eexists. split; [by apply ss_init|]. by apply list_elem_of_singleton.
  Qed.

  (* ** Non-zero weights are preserved *)

  Lemma sched_step_nonzero ρ R s Δ :
    ρ ≠ szero → sched_step ρ R s Δ → ∀ R' ρ', (R', ρ') ∈ Δ → ρ' ≠ szero.
  Proof.
    intros Hρ Hs R' ρ' Hin. inversion Hs as [? Hp|E qs ? Hp|qs ? Hp|M qs Rs R0 Hp0 Hf]; subst.
    - apply list_elem_of_singleton in Hin. by simplify_eq.
    - apply list_elem_of_singleton in Hin. simplify_eq. by apply sop_apply_nonzero.
    - apply list_elem_of_singleton in Hin. simplify_eq. by apply init_apply_nonzero.
    - clear Hs Hp0. assert (Hks : ∀ k, k ∈ outs_nz M qs ρ → meas_branch M qs k ρ ≠ szero)
        by (intros k; apply outs_nz_spec).
      remember (outs_nz M qs ρ) as ks0 eqn:Eks. clear Eks. revert Hin Hks.
      induction Hf as [|k R1 ks Rs Hp _ IH]; simpl; intros Hin Hks; [by apply elem_of_nil in Hin|].
      apply elem_of_cons in Hin as [Hin|Hin].
      + simplify_eq. apply Hks. by left.
      + apply IH; [done|]. intros k' Hk'. apply Hks. by right.
  Qed.

  Lemma sched_step_nonempty ρ R s Δ : ρ ≠ szero → sched_step ρ R s Δ → Δ ≠ [].
  Proof.
    intros Hρ Hs. inversion Hs as [? Hp|E qs ? Hp|qs ? Hp|M qs Rs R0 Hp0 Hf]; subst; try done.
    intros E. pose proof (outs_nz_nonempty M qs ρ Hρ) as Hne.
    destruct (outs_nz M qs ρ); [done|]. inversion Hf; subst. done.
  Qed.

  Inductive vis_step (ρ : St) (P : proc) :
      choice → Labels prog_action + mem_action →
      list ((Labels prog_action + mem_action) * (proc * St)) → Prop :=
  | vs_prog (t : tag) a P' :
      P ⟶{ActExt a}[t] P' →
      vis_step ρ P t (inl (ActExt a)) [(inl (ActExt a), (P', ρ))]
  | vs_sop (ℰ : Act) :
      vis_step ρ P CEps (inr (MeSop ℰ)) [(inr (MeSop ℰ), (P, ℰ · ρ))]
  | vs_meas M qs :
      vis_step ρ P CEps (inr (MeMeas M qs 0))
        (map (λ k, (inr (MeMeas M qs (code _ k)), (P, M ⦅qs⦆[k] · ρ))) (outs_nz M qs ρ)).

  Lemma vis_step_conf ρ P s l Λ x :
    vis_step ρ P s l Λ → x ∈ Λ → conf_step ρ P s x.1 x.2.2 x.2.1.
  Proof.
    intros Hv Hx. inversion Hv as [t a P' Hp|ℰ|M qs]; subst.
    - apply list_elem_of_singleton in Hx. subst x. by apply prog_step_conf.
    - apply list_elem_of_singleton in Hx. subst x. apply co_mem_sop.
    - apply list_elem_of_fmap in Hx as (k & -> & _). apply co_mem_meas.
  Qed.
End Sched.

(* The Smyth must of lqCCS is [⊑ₛₘ] of [pMust_smyth]; the characterisation
    is for [⊑ₛₘ[ tau_free ]]. *)

(* ** Divergence is the bottom of the Smyth musts, under both liftings *)

Section Bottom.
  Context `{QM : QuantumModel}.

  Definition Omega (t : tag) : proc := PRec t 0 (PVar 0).

  Lemma Omega_step t : prog_step (Omega t) (CTag t) τ (Omega t).
  Proof. exact (pr_rec t 0 (PVar 0)). Qed.

  Lemma Omega_run L t T ρ : is_run L [((Omega t, T), ρ)] (λ _, [((Omega t, T), ρ)]).
  Proof.
    split; [done|]. intros n. destruct (decide (success T)) as [Hs|Hs].
    - right. split; [|done]. intros σ (c & ρ' & Δ & Hin & Hns & _).
      apply list_elem_of_singleton in Hin. simplify_eq. by apply Hns.
    - left. exists (CTag t). split.
      + exists (Omega t, T), ρ, [((Omega t, T), ρ)]. split; [by left|]. split; [done|].
        apply ss_tau. by apply pr_parL, Omega_step.
      + exists [[((Omega t, T), ρ)]]. split; [|done]. constructor; [|constructor]. left. split; [done|].
        apply ss_tau. by apply pr_parL, Omega_step.
  Qed.

  Theorem Omega_bottom L t (Q : proc) (ρ : St) : ctx_pre_sm L (Omega t, ρ) (Q, ρ).
  Proof.
    intros T r Hr. exists (λ _, [((Omega t, T), ρ)]). split; [apply Omega_run|].
    intros n w Hw. unfold succ_mass in *. simpl in Hw.
    destruct (decide (success T)) as [Hs|Hs].
    - exists 0. destruct Hr as [-> _]. simpl.
      rewrite decide_True; [|done]. exact (proj1 Hw).
    - destruct Hw as [_ Hnz]. exfalso. apply Hnz, W_zero_le.
  Qed.
End Bottom.
(* end hide *)
