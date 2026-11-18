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
From TestingTheory Require Import lqCCS.General_definition.Algebra lqCCS.quantum_mem.Syntax lqCCS.quantum_mem.Quantum_Weights.
From TestingTheory Require Import lqCCS.lqCCS_prog.Syntax lqCCS.Helper.De_Brujin_lemmas lqCCS.General_definition.Parallel_choice_LTS lqCCS.quantum_mem.LTS lqCCS.lqCCS_prog.LTS lqCCS.lqCCS_par_Qmem.LTS lqCCS.lqCCS_process.LTS.LTS lqCCS.Helper.Conf_labels lqCCS.Helper.Label_lemmas lqCCS.lqCCS_prog.Congruence lqCCS.lqCCS_process.Memory_Harmony.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

(* ** Success: [𝟙] at top level, through parallel composition, restriction,
    evaluated conditionals and sums *)

Section Scheduled.
  Context `{lqP : lqCCS_Parameters}.

Fixpoint gsuccessb (g : guard) : bool :=
  match g with
  | 𝟙 => true
  | (g1 + g2)%lq => gsuccessb g1 || gsuccessb g2
  | _ => false
  end.

Fixpoint successb (P : prog) : bool :=
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

Definition success (P : prog) : Prop := successb P = true.

#[global] Instance success_dec P : Decision (success P).
Proof. unfold success. apply _. Qed.

(* ** Tests without [τ] *)

Fixpoint tau_freeb (P : prog) : bool :=
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

Definition tau_free (T : prog) : Prop := tau_freeb T = true.

Section Sched.
  Context `{QM : QuantumModel}.

  (* ** The scheduled step of a tested program

      [ρ • R —k→ Δ]: the silent steps of [⟨ρ, R⟩] with choice [k], the
      outcomes of a measurement grouped. *)

  Inductive sched_step (ρ : St) (R : prog) (k : choice) : dist prog → Prop :=
  | ss_tau R' : R ⟶ₚ{τ}[k] R' → sched_step ρ R k [(R', ρ)]
  | ss_op U qs R' :
      R ⟶ₚ{⦅qs⦆ ! U}[k] R' → sched_step ρ R k [(R', sop_apply U qs ρ)]
  | ss_init qs R' :
      R ⟶ₚ{reinit qs}[k] R' → sched_step ρ R k [(R', init_apply qs ρ)]
  | ss_meas M qs (Rs : list prog) R0 :
      R ⟶ₚ{M ⦅qs⦆? 0}[k] R0 →
      Forall2 (λ n R', R ⟶ₚ{M ⦅qs⦆? n}[k] R') (outs_nz (meas_of M qs) ρ) Rs →
      sched_step ρ R k (zip_with (λ n R', (R', M ⦅qs⦆[n] · ρ)) (outs_nz (meas_of M qs) ρ) Rs).

  Definition par_of (c : prog * prog) : prog := c.1 ∥ c.2.

  Definition conf_sched (ρ : St) (c : prog * prog) (k : choice) (Δ : dist (prog * prog)) : Prop :=
    sched_step ρ (par_of c) k (dmap par_of Δ).

  #[global] Instance lq_SchedSts : SchedSts (prog * prog) choice :=
    {| pMust_scheduled.sstep := conf_sched; psuccess := λ c, success c.2 |}.

  Definition compose (Pρ : prog * St) (T : prog) : dist (prog * prog) := [((Pρ.1, T), Pρ.2)].

  #[global] Instance lq_pTesting : pTesting (prog * St) prog (prog * prog) choice :=
    {| pMust_scheduled.compose := compose |}.

  (* ** The steps of a component are the silent steps of the configuration *)

  Lemma sched_step_conf ρ R k Δ R' ρ' :
    sched_step ρ R k Δ → (R', ρ') ∈ Δ → ⟨ρ, R⟩ ⟶{τ}[k] ⟨ρ', R'⟩.
  Proof.
    intros Hs Hin. inversion Hs as [? Hp|U qs ? Hp|qs ? Hp|M qs Rs R0 Hp0 Hf]; subst.
    - apply list_elem_of_singleton in Hin. simplify_eq. exact (prog_step_conf _ _ _ _ _ Hp).
    - apply list_elem_of_singleton in Hin. simplify_eq.
      eapply prog_step_mem_conf; [exact Hp|apply (me_sop ρ (sop_act U qs))|constructor].
    - apply list_elem_of_singleton in Hin. simplify_eq.
      eapply prog_step_mem_conf; [exact Hp|apply (me_sop ρ (init_act qs))|constructor].
    - assert (Hks : ∀ n, n ∈ outs_nz (meas_of M qs) ρ → n ∈ outs (meas_of M qs))
        by (intros n Hk; by apply outs_nz_spec in Hk as [? _]).
      remember (outs_nz (meas_of M qs) ρ) as ns eqn:Eks. clear Eks Hs.
      clear Hp0. revert Hin Hks. induction Hf as [|n R1 ns Rs Hp _ IH]; simpl; intros Hin Hks; [by apply elem_of_nil in Hin|].
      apply elem_of_cons in Hin as [Hin|Hin]; [|apply IH; [done|intros n' Hk'; apply Hks; by right]]. simplify_eq.
      eapply prog_step_mem_conf; [exact Hp|apply me_meas, Hks; by left|constructor].
  Qed.

  Lemma prog_gstep_meas_any g k M qs n R' :
    g ⟶ᵍ{M ⦅qs⦆? n}[k] R' →
    ∀ n', ∃ R'', g ⟶ᵍ{M ⦅qs⦆? n'}[k] R''.
  Proof.
    intros Hp. remember (M ⦅qs⦆? n) as 𝜆 eqn:El. revert El.
    induction Hp; intros El n'; simplify_eq;
      try (edestruct IHHp as (R'' & HR''); [done|]; eexists; by econstructor).
    eexists. by apply pg_meas.
  Qed.

  Lemma prog_step_meas_any R k M qs n R' :
    R ⟶ₚ{M ⦅qs⦆? n}[k] R' →
    ∀ n', ∃ R'', R ⟶ₚ{M ⦅qs⦆? n'}[k] R''.
  Proof.
    intros Hp. remember (M ⦅qs⦆? n) as 𝜆 eqn:El. revert El.
    induction Hp as [g k 𝜆 P' Hg| | | | | | | | |]; intros El n'; simplify_eq;
      try (edestruct IHHp as (R'' & HR''); [done|]; eexists; by econstructor).
    destruct (prog_gstep_meas_any _ _ _ _ _ _ Hg n') as (R'' & HR''). eexists. by apply pr_guard.
  Qed.

  Lemma mem_step_meas_inv ρ M qs n ρ' :
    ρ ⟶ₘ{meas_of M qs !ₘ n} ρ' →
    n ∈ outs (meas_of M qs) ∧ ρ' = M ⦅qs⦆[n] · ρ.
  Proof. by inversion 1; subst. Qed.

  Lemma conf_sched_step ρ R k ρ' R' :
    ⟨ρ, R⟩ ⟶{τ}[k] ⟨ρ', R'⟩ → ρ' ≠ szero → ∃ Δ, sched_step ρ R k Δ ∧ (R', ρ') ∈ Δ.
  Proof.
    intros Hc Hnz. destruct (conf_step_tau_inv _ _ _ _ _ Hc) as [(Hp & ->)|(μ2 & μ1 & Hp & Hm & Hsy)];
      [|destruct (prog_step_ext_choice _ _ _ _ Hp) as (t & ->)].
    - eexists. split; [by apply ss_tau|]. by apply list_elem_of_singleton.
    - inversion Hsy; subst.
      + inversion Hm; subst. eexists. split; [by apply ss_op|]. by apply list_elem_of_singleton.
      + destruct (mem_step_meas_inv _ _ _ _ _ Hm) as (Hko & ->).
        assert (Hall : ∀ ns : list (nat),
          ∃ Rs, Forall2 (λ n R'', R ⟶ₚ{M ⦅qs⦆? n}[{[+ t +]}] R'') ns Rs
                ∧ (n ∈ ns → (R', M ⦅qs⦆[n] · ρ) ∈ zip_with (λ n R'', (R'', M ⦅qs⦆[n] · ρ)) ns Rs)).
        { intros ns. induction ns as [|n' ns (Rs & Hf & Hin)].
          - exists []. split; [constructor|]. by intros ?%elem_of_nil.
          - destruct (decide (n' = n)) as [Hk|Hne].
            + subst n'.
              exists (R' :: Rs). split; [by constructor|]. intros _. simpl. by left.
            + destruct (prog_step_meas_any _ _ _ _ _ _ Hp n') as (R'' & HR'').
              exists (R'' :: Rs). split; [by constructor|].
              intros [->|Hk]%elem_of_cons; [by destruct Hne|]. simpl. right. by apply Hin. }
        destruct (Hall (outs_nz (meas_of M qs) ρ)) as (Rs & Hf & Hin).
        exists (zip_with (λ n R'', (R'', M ⦅qs⦆[n] · ρ)) (outs_nz (meas_of M qs) ρ) Rs).
        split; [|by apply Hin, outs_nz_spec].
        destruct (prog_step_meas_any _ _ _ _ _ _ Hp 0) as (R0 & HR0). by apply (ss_meas _ _ _ M qs Rs R0).
      + inversion Hm; subst. eexists. split; [by apply ss_init|]. by apply list_elem_of_singleton.
  Qed.

  (* ** Non-zero weights are preserved *)

  Lemma sched_step_nonzero ρ R k Δ :
    ρ ≠ szero → sched_step ρ R k Δ → ∀ R' ρ', (R', ρ') ∈ Δ → ρ' ≠ szero.
  Proof.
    intros Hρ Hs R' ρ' Hin. inversion Hs as [? Hp|U qs ? Hp|qs ? Hp|M qs Rs R0 Hp0 Hf]; subst.
    - apply list_elem_of_singleton in Hin. by simplify_eq.
    - apply list_elem_of_singleton in Hin. simplify_eq. by apply sop_apply_nonzero.
    - apply list_elem_of_singleton in Hin. simplify_eq. by apply init_apply_nonzero.
    - clear Hs Hp0. assert (Hks : ∀ n, n ∈ outs_nz (meas_of M qs) ρ → M ⦅qs⦆[n] · ρ ≠ szero)
        by (intros n Hk; exact (proj2 (proj1 (outs_nz_spec (meas_of M qs) ρ n) Hk))).
      remember (outs_nz (meas_of M qs) ρ) as ks0 eqn:Eks. clear Eks. revert Hin Hks.
      induction Hf as [|n R1 ns Rs Hp _ IH]; simpl; intros Hin Hks; [by apply elem_of_nil in Hin|].
      apply elem_of_cons in Hin as [Hin|Hin].
      + simplify_eq. apply Hks. by left.
      + apply IH; [done|]. intros n' Hk'. apply Hks. by right.
  Qed.

  Lemma sched_step_nonempty ρ R k Δ : ρ ≠ szero → sched_step ρ R k Δ → Δ ≠ [].
  Proof.
    intros Hρ Hs. inversion Hs as [? Hp|U qs ? Hp|qs ? Hp|M qs Rs R0 Hp0 Hf]; subst; try done.
    intros U. pose proof (outs_nz_nonempty M qs ρ Hρ) as Hne.
    destruct (outs_nz (meas_of M qs) ρ); [done|]. inversion Hf; subst. done.
  Qed.

  Inductive vis_step (ρ : St) (P : prog) :
      choice → Labels (mem_action + prog_action) →
      list (Labels (mem_action + prog_action) * (prog * St)) → Prop :=
  | vs_prog (t : tag) (μ : prog_action) P' :
      P ⟶ₚ{ActExt μ}[{[+ t +]}] P' →
      vis_step ρ P {[+ t +]} (ActExt μ) [(ActExt (plbl μ), (P', ρ))]
  | vs_sop (ℰ : Act) :
      vis_step ρ P ∅ (ActExt (? ℰ)) [(ActExt (mlbl (? ℰ)), (P, ℰ · ρ))]
  | vs_meas ℳ :
      vis_step ρ P ∅ (ActExt (ℳ !ₘ 0))
        (map (λ n, (ActExt (mlbl (ℳ !ₘ n)), (P, ℳ ·[n] ρ))) (outs_nz ℳ ρ)).

  Lemma vis_step_conf ρ P k 𝜆 Λ x :
    vis_step ρ P k 𝜆 Λ → x ∈ Λ → ⟨ρ, P⟩ ⟶{x.1}[k] ⟨x.2.2, x.2.1⟩.
  Proof.
    intros Hv Hx. inversion Hv as [t μ P' Hp|ℰ|ℳ]; subst.
    - apply list_elem_of_singleton in Hx. subst x. exact (prog_step_conf _ _ _ _ _ Hp).
    - apply list_elem_of_singleton in Hx. subst x. apply co_mem_sop.
    - apply list_elem_of_fmap in Hx as (n & -> & Hk). apply co_mem_meas. by apply outs_nz_spec in Hk as [? _].
  Qed.
End Sched.

(* The Smyth must of lqCCS is [⊑ₛₘ] of [pMust_smyth]; the characterisation
    is for [⊑ₛₘ[ tau_free ]]. *)

(* ** Divergence is the bottom of the Smyth musts, under both liftings *)

Section Bottom.
  Context `{QM : QuantumModel}.

  Definition Omega (t : tag) : prog := t ∶ rec ∙ PVar 0.

  Lemma Omega_step t : (Omega t) ⟶ₚ{τ}[{[+ t +]}] (Omega (tag_up t)).
  Proof. exact (pr_rec t (PVar 0)). Qed.

  Definition Omega_run_of (t : tag) (T : prog) (ρ : St) (n : nat) : dist (prog * prog) :=
    [((Omega (if decide (success T) then t else Nat.iter n tag_up t), T), ρ)].

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

  Theorem Omega_bottom L t (Q : prog) (ρ : St) : ctx_pre_sm L (Omega t, ρ) (Q, ρ).
  Proof.
    intros T r Hr. exists (Omega_run_of t T ρ). split; [apply Omega_run|].
    intros n w Hw. unfold succ_mass, Omega_run_of in *. simpl in Hw.
    destruct (decide (success T)) as [Hs|Hs].
    - exists 0. destruct Hr as [-> _]. simpl.
      rewrite decide_True; [|done]. exact (proj1 Hw).
    - destruct Hw as [_ Hnz]. exfalso. apply Hnz, W_zero_le.
  Qed.
End Bottom.

End Scheduled.

(* end hide *)
