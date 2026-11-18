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
    marked with [𝟙]: the tested system is the pair of [P] and [T], running as [P ∥ T] on
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
From stdpp Require Import base gmultiset countable decidable list.
From TestingTheory Require Import ActTau pMust_almost_sure pMust_smyth.
From TestingTheory Require Import lqCCS.Language.Algebra lqCCS.Language.Quantum lqCCS.Language.Quantum_Weights.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Helper_substitution.De_Brujin_lemmas lqCCS.General_definition.Parallel_choice_LTS lqCCS.Language.LTS_quantum_mem lqCCS.Language.LTS_lqCCS_prog lqCCS.Language.LTS_lqCCS_process lqCCS.Language.LTS_lqCCS_par_Qmem lqCCS.Helper_substitution.Label_lemmas lqCCS.Language.Congruence lqCCS.Harmony_Lemma.Memory_Harmony.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

(* ** Success: [𝟙] at top level, through parallel composition, restriction,
    evaluated conditionals and sums *)

Section LqP.
  Context `{LP : lqCCS_Parameters}.

Fixpoint gsuccessb (g : guard) : bool :=
  match g with
  | 𝟙 => true
  | (g1 + g2)%lq => gsuccessb g1 || gsuccessb g2
  | _ => false
  end.

Fixpoint successb (P : proc) : bool :=
  match P with
  | PG g => gsuccessb g
  | P ∥ Q => successb P || successb Q
  | ν P => successb P
  | If e Then P Else Q =>
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
  | If _ Then P Else Q | P ∥ Q => tau_freeb P && tau_freeb Q
  | ν P | _ ∶ rec ∙ P => tau_freeb P
  | PG g => gtau_freeb g
  end
with gtau_freeb (g : guard) : bool :=
  match g with
  | 𝟘{_} | 𝟙 => true
  | _ ∶ 𝛕 ∙ _ => false
  | _ ∙ P => tau_freeb P
  | (g1 + g2)%lq => gtau_freeb g1 && gtau_freeb g2
  end.

Definition tau_free (T : proc) : Prop := tau_freeb T = true.

Section Sched.
  Context `{QM : QuantumModel}.

  (* The outcomes of a measurement that have a non-zero probability: a
      distribution is its support, as in a pLTS. *)
  Definition outs_nz (ℳ : Meas) (ρ : St) : list nat :=
    filter (λ k, ℳ ·[k] ρ ≠ szero) (outs ℳ).

  Lemma outs_nz_spec ℳ ρ k : k ∈ outs_nz ℳ ρ ↔ k ∈ outs ℳ ∧ ℳ ·[k] ρ ≠ szero.
  Proof. unfold outs_nz. rewrite list_elem_of_filter. tauto. Qed.

  Lemma outs_nz_nonempty M qs ρ : ρ ≠ szero → outs_nz (meas_of M qs) ρ ≠ [].
  Proof.
    intros Hρ E. destruct (meas_nonzero_branch M qs ρ Hρ) as (k & Hk).
    apply (outs_nz_spec (meas_of M qs) ρ k) in Hk. rewrite E in Hk. by apply elem_of_nil in Hk.
  Qed.

  (* ** The scheduled step of a tested program

      [ρ • R —s→ Δ]: the silent steps of [⟨ρ, R⟩] with choice [s], the
      outcomes of a measurement grouped. *)

  Inductive sched_step (ρ : St) (R : proc) (s : choice) : dist proc → Prop :=
  | ss_tau R' : R ⟶ₚ{τ}[s] R' → sched_step ρ R s [(R', ρ)]
  | ss_op U qs R' :
      R ⟶ₚ{⦅qs⦆ ! U}[s] R' → sched_step ρ R s [(R', sop_apply U qs ρ)]
  | ss_init qs R' :
      R ⟶ₚ{reinit qs}[s] R' → sched_step ρ R s [(R', init_apply qs ρ)]
  | ss_meas M qs (Rs : list proc) R0 :
      R ⟶ₚ{M ⦅qs⦆? 0}[s] R0 →
      Forall2 (λ k R', R ⟶ₚ{M ⦅qs⦆? k}[s] R') (outs_nz (meas_of M qs) ρ) Rs →
      sched_step ρ R s (zip_with (λ k R', (R', M ⦅qs⦆[k] · ρ)) (outs_nz (meas_of M qs) ρ) Rs).

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
    intros Hs Hin. inversion Hs as [? Hp|U qs ? Hp|qs ? Hp|M qs Rs R0 Hp0 Hf]; subst.
    - apply list_elem_of_singleton in Hin. simplify_eq. by apply prog_step_conf.
    - apply list_elem_of_singleton in Hin. simplify_eq.
      eapply prog_step_mem_conf; [exact Hp|apply (me_sop ρ (sop_act U qs))|constructor].
    - apply list_elem_of_singleton in Hin. simplify_eq.
      eapply prog_step_mem_conf; [exact Hp|apply (me_sop ρ (init_act qs))|constructor].
    - assert (Hks : ∀ k, k ∈ outs_nz (meas_of M qs) ρ → k ∈ outs (meas_of M qs))
        by (intros k Hk; by apply outs_nz_spec in Hk as [? _]).
      remember (outs_nz (meas_of M qs) ρ) as ks eqn:Eks. clear Eks Hs.
      clear Hp0. revert Hin Hks. induction Hf as [|k R1 ks Rs Hp _ IH]; simpl; intros Hin Hks; [by apply elem_of_nil in Hin|].
      apply elem_of_cons in Hin as [Hin|Hin]; [|apply IH; [done|intros k' Hk'; apply Hks; by right]]. simplify_eq.
      eapply prog_step_mem_conf; [exact Hp|apply me_meas, Hks; by left|constructor].
  Qed.

  Lemma prog_gstep_meas_any g s M qs n R' :
    g ⟶ᵍ{M ⦅qs⦆? n}[s] R' →
    ∀ n', ∃ R'', g ⟶ᵍ{M ⦅qs⦆? n'}[s] R''.
  Proof.
    intros Hp. remember (M ⦅qs⦆? n) as l eqn:El. revert El.
    induction Hp; intros El n'; simplify_eq;
      try (edestruct IHHp as (R'' & HR''); [done|]; eexists; by econstructor).
    eexists. by apply pg_meas.
  Qed.

  Lemma prog_step_meas_any R s M qs n R' :
    R ⟶ₚ{M ⦅qs⦆? n}[s] R' →
    ∀ n', ∃ R'', R ⟶ₚ{M ⦅qs⦆? n'}[s] R''.
  Proof.
    intros Hp. remember (M ⦅qs⦆? n) as l eqn:El. revert El.
    induction Hp as [g s l P' Hg| | | | | | | | |]; intros El n'; simplify_eq;
      try (edestruct IHHp as (R'' & HR''); [done|]; eexists; by econstructor).
    destruct (prog_gstep_meas_any _ _ _ _ _ _ Hg n') as (R'' & HR''). eexists. by apply pr_guard.
  Qed.

  Lemma mem_step_meas_inv ρ M qs n ρ' :
    ρ ⟶ₘ{meas_of M qs !ₘ n} ρ' →
    n ∈ outs (meas_of M qs) ∧ ρ' = M ⦅qs⦆[n] · ρ.
  Proof. by inversion 1; subst. Qed.

  Lemma conf_sched_step ρ R s ρ' R' :
    ⟨ρ, R⟩ ⟶{τ}[s] ⟨ρ', R'⟩ → ρ' ≠ szero → ∃ Δ, sched_step ρ R s Δ ∧ (R', ρ') ∈ Δ.
  Proof.
    intros Hc Hnz. destruct (conf_step_tau_inv _ _ _ _ _ Hc) as [(Hp & ->)|(a & b & Hp & Hm & Hsy)];
      [|destruct (prog_step_ext_choice _ _ _ _ Hp) as (t & ->)].
    - eexists. split; [by apply ss_tau|]. by apply list_elem_of_singleton.
    - inversion Hsy; subst.
      + inversion Hm; subst. eexists. split; [by apply ss_op|]. by apply list_elem_of_singleton.
      + rename n into k. destruct (mem_step_meas_inv _ _ _ _ _ Hm) as (Hko & ->).
        assert (Hall : ∀ ks : list (nat),
          ∃ Rs, Forall2 (λ k R'', R ⟶ₚ{M ⦅qs⦆? k}[{[+ t +]}] R'') ks Rs
                ∧ (k ∈ ks → (R', M ⦅qs⦆[k] · ρ) ∈ zip_with (λ k R'', (R'', M ⦅qs⦆[k] · ρ)) ks Rs)).
        { intros ks. induction ks as [|k' ks (Rs & Hf & Hin)].
          - exists []. split; [constructor|]. by intros ?%elem_of_nil.
          - destruct (decide (k' = k)) as [Hk|Hne].
            + subst k'.
              exists (R' :: Rs). split; [by constructor|]. intros _. simpl. by left.
            + destruct (prog_step_meas_any _ _ _ _ _ _ Hp k') as (R'' & HR'').
              exists (R'' :: Rs). split; [by constructor|].
              intros [->|Hk]%elem_of_cons; [by destruct Hne|]. simpl. right. by apply Hin. }
        destruct (Hall (outs_nz (meas_of M qs) ρ)) as (Rs & Hf & Hin).
        exists (zip_with (λ k R'', (R'', M ⦅qs⦆[k] · ρ)) (outs_nz (meas_of M qs) ρ) Rs).
        split; [|by apply Hin, outs_nz_spec].
        destruct (prog_step_meas_any _ _ _ _ _ _ Hp 0) as (R0 & HR0). by apply (ss_meas _ _ _ M qs Rs R0).
      + inversion Hm; subst. eexists. split; [by apply ss_init|]. by apply list_elem_of_singleton.
  Qed.

  (* ** Non-zero weights are preserved *)

  Lemma sched_step_nonzero ρ R s Δ :
    ρ ≠ szero → sched_step ρ R s Δ → ∀ R' ρ', (R', ρ') ∈ Δ → ρ' ≠ szero.
  Proof.
    intros Hρ Hs R' ρ' Hin. inversion Hs as [? Hp|U qs ? Hp|qs ? Hp|M qs Rs R0 Hp0 Hf]; subst.
    - apply list_elem_of_singleton in Hin. by simplify_eq.
    - apply list_elem_of_singleton in Hin. simplify_eq. by apply sop_apply_nonzero.
    - apply list_elem_of_singleton in Hin. simplify_eq. by apply init_apply_nonzero.
    - clear Hs Hp0. assert (Hks : ∀ k, k ∈ outs_nz (meas_of M qs) ρ → M ⦅qs⦆[k] · ρ ≠ szero)
        by (intros k Hk; exact (proj2 (proj1 (outs_nz_spec (meas_of M qs) ρ k) Hk))).
      remember (outs_nz (meas_of M qs) ρ) as ks0 eqn:Eks. clear Eks. revert Hin Hks.
      induction Hf as [|k R1 ks Rs Hp _ IH]; simpl; intros Hin Hks; [by apply elem_of_nil in Hin|].
      apply elem_of_cons in Hin as [Hin|Hin].
      + simplify_eq. apply Hks. by left.
      + apply IH; [done|]. intros k' Hk'. apply Hks. by right.
  Qed.

  Lemma sched_step_nonempty ρ R s Δ : ρ ≠ szero → sched_step ρ R s Δ → Δ ≠ [].
  Proof.
    intros Hρ Hs. inversion Hs as [? Hp|U qs ? Hp|qs ? Hp|M qs Rs R0 Hp0 Hf]; subst; try done.
    intros U. pose proof (outs_nz_nonempty M qs ρ Hρ) as Hne.
    destruct (outs_nz (meas_of M qs) ρ); [done|]. inversion Hf; subst. done.
  Qed.

  Inductive vis_step (ρ : St) (P : proc) :
      choice → Labels prog_action + mem_action →
      list ((Labels prog_action + mem_action) * (proc * St)) → Prop :=
  | vs_prog (t : tag) a P' :
      P ⟶ₚ{ActExt a}[{[+ t +]}] P' →
      vis_step ρ P {[+ t +]} (inl (ActExt a)) [(inl (ActExt a), (P', ρ))]
  | vs_sop (ℰ : Act) :
      vis_step ρ P ∅ (inr (? ℰ)) [(inr (? ℰ), (P, ℰ · ρ))]
  | vs_meas ℳ :
      vis_step ρ P ∅ (inr (ℳ !ₘ 0))
        (map (λ k, (inr (ℳ !ₘ k), (P, ℳ ·[k] ρ))) (outs_nz ℳ ρ)).

  Lemma vis_step_conf ρ P s l Λ x :
    vis_step ρ P s l Λ → x ∈ Λ → conf_step ρ P s x.1 x.2.2 x.2.1.
  Proof.
    intros Hv Hx. inversion Hv as [t a P' Hp|ℰ|ℳ]; subst.
    - apply list_elem_of_singleton in Hx. subst x. by apply prog_step_conf.
    - apply list_elem_of_singleton in Hx. subst x. apply co_mem_sop.
    - apply list_elem_of_fmap in Hx as (k & -> & Hk). apply co_mem_meas. by apply outs_nz_spec in Hk as [? _].
  Qed.
End Sched.

(* The Smyth must of lqCCS is [⊑ₛₘ] of [pMust_smyth]; the characterisation
    is for [⊑ₛₘ[ tau_free ]]. *)

(* ** Divergence is the bottom of the Smyth musts, under both liftings *)

Section Bottom.
  Context `{QM : QuantumModel}.

  Definition Omega (t : tag) : proc := t ∶ rec ∙ PVar 0.

  Lemma Omega_step t : (Omega t) ⟶ₚ{τ}[{[+ t +]}] (Omega (tag_up t)).
  Proof. exact (pr_rec t (PVar 0)). Qed.

  Definition Omega_run_of (t : tag) (T : proc) (ρ : St) (i : nat) : dist (proc * proc) :=
    [((Omega (if decide (success T) then t else Nat.iter i tag_up t), T), ρ)].

  Lemma Omega_run L t T ρ : is_run L [((Omega t, T), ρ)] (Omega_run_of t T ρ).
  Proof.
    unfold Omega_run_of. split; [by case_decide|]. intros n. destruct (decide (success T)) as [Hs|Hs].
    - right. split; [|done]. intros σ (c & ρ' & Δ & Hin & Hns & _).
      apply list_elem_of_singleton in Hin. simplify_eq. by apply Hns.
    - left. exists ({[+ Nat.iter n tag_up t +]}). split.
      + eexists _, ρ, [((Omega (tag_up (Nat.iter n tag_up t)), T), ρ)]. split; [by left|]. split; [done|].
        apply ss_tau. by apply pr_parL, Omega_step.
      + exists [[((Omega (tag_up (Nat.iter n tag_up t)), T), ρ)]]. split; [|done].
        constructor; [|constructor]. left. split; [done|].
        apply ss_tau. by apply pr_parL, Omega_step.
  Qed.

  Theorem Omega_bottom L t (Q : proc) (ρ : St) : ctx_pre_sm L (Omega t, ρ) (Q, ρ).
  Proof.
    intros T r Hr. exists (Omega_run_of t T ρ). split; [apply Omega_run|].
    intros n w Hw. unfold succ_mass, Omega_run_of in *. simpl in Hw.
    destruct (decide (success T)) as [Hs|Hs].
    - exists 0. destruct Hr as [-> _]. simpl.
      rewrite decide_True; [|done]. exact (proj1 Hw).
    - destruct Hw as [_ Hnz]. exfalso. apply Hnz, W_zero_le.
  Qed.
End Bottom.

End LqP.

(* end hide *)
