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
(* * The Smyth must of lqCCS: least runs and thresholds

    lqCCS has no recursion: every run of a tested configuration ends in a
    stable distribution ([lqCCS.Characterisations.AlmostSure]), and a step has finitely many
    possible results ([dstep_dcands]).  So every distribution has a run of
    least value ([lq_min_run]): the Smyth comparison of [pMust_smyth.v] is a
    comparison of minima, and the Smyth must is the family of threshold
    musts [must_lt w] ([lq_pre_sm_iff_must_lt]); the threshold "whole mass" is
    the almost-sure must.

    The characterisation of the Smyth must is the next step.  Pointers to
    the literature, for definitions in the same spirit:
    - Deng, van Glabbeek, Hennessy, Morgan, "Characterising testing preorders
      for finite probabilistic processes" (LICS 2007, LMCS 2008): finite
      pCSP, must = failure simulation, modal logic F with [αᴛᴇꜱᴛ p⊕ ψ];
      "Testing finitary probabilistic processes" (CONCUR 2009) with
      divergence.
    - Segala, "Testing probabilistic automata" (CONCUR 1996): vector testing
      (several success actions) and trace distributions.
    - Jonsson, Yi, "Testing preorders for probabilistic processes can be
      characterized by simulations" (TCS 2002).
    - Georgievska, Andova, "Probabilistic may/must testing: retaining
      probabilities by restricted schedulers" (FAC 2012; arXiv 0907.1540,
      "Testing probabilistic processes: can random choices be
      unobservable?"): testing under schedulers that cannot see the outcome
      of random choices — close to the admissible schedulers of lqCCS (one
      tag for the whole distribution).
    - Chatzikokolakis, Palamidessi, "Making random choices invisible to the
      scheduler" (CONCUR 2007, Inf. Comput. 2010): the same restriction on
      schedulers, for compositional reasoning.
    - Castiglioni, "Behavioural metrics and compositionality in probabilistic
      process algebras" (PhD thesis, 2018), and her work with Gebler and
      Tini: compositionality of probabilistic behavioural relations. *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list sets gmap.
From TestingTheory Require Import lqCCS.Harmony_Lemma.Lifted lqCCS.Harmony_Lemma.Paths lqCCS.Harmony_Lemma.States pMust_almost_sure pMust_smyth lqCCS.Language.Quantum.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.Program lqCCS.Language.Succ lqCCS.Language.Composition
  lqCCS.Language.LTS lqCCS.Characterisations.AlmostSure.
Section Smyth.
  Context `{QM : QuantumModel}.
  Context (XM : ∀ P : Prop, P ∨ ¬ P).
  Context (W_total : ∀ a b : W, W_le a b ∨ W_le b a).
  Context (W_dense : ∀ a b : W, a <ₚ b → ∃ c, a <ₚ c ∧ c <ₚ b).

  #[local] Instance lq_DenseWeights : DenseWeights := {| prob_dense := W_dense |}.

  (* ** Runs *)

  Lemma dstep_moves Δ σ Δ' : dstep Δ σ Δ' → ¬ dstable Δ.
  Proof. intros [Hm _] Hst. by apply (Hst σ). Qed.

  Lemma stable_stays Δ r n m : is_run Δ r → dstable (r n) → n ≤ m → r m = r n.
  Proof.
    intros [_ Hr] Hst Hle. induction Hle as [|m Hle IH]; [done|].
    destruct (Hr m) as [(σ & Hs)|[_ ->]]; [|done].
    exfalso. rewrite IH in Hs. by eapply dstep_moves.
  Qed.

  Lemma succ_mono Δ r n m : is_run Δ r → n ≤ m → W_le (succ_mass r n) (succ_mass r m).
  Proof.
    intros [_ Hr] Hle. induction Hle as [|m Hle IH]; [done|].
    etrans; [exact IH|]. unfold succ_mass.
    destruct (Hr m) as [(σ & Hs)|[_ ->]]; [by eapply dstep_succ_mono|done].
  Qed.

  (* The value of a run is reached when it is stable. *)
  Lemma run_final N Δ r :
    bounded N Δ → is_run Δ r → ∃ n, ∀ m, W_le (succ_mass r m) (succ_mass r n).
  Proof.
    intros Hb Hr. destruct (run_stable N Δ r Hb Hr) as [n Hn]. exists n. intros m.
    destruct (decide (m ≤ n)) as [Hle|Hgt].
    - by apply (succ_mono Δ).
    - unfold succ_mass. rewrite (stable_stays Δ r n m Hr Hn); [done|lia].
  Qed.

  Lemma run_le_total N1 N2 Δ1 Δ2 r1 r2 :
    bounded N1 Δ1 → bounded N2 Δ2 → is_run Δ1 r1 → is_run Δ2 r2 →
    run_le r1 r2 ∨ run_le r2 r1.
  Proof.
    intros Hb1 Hb2 Hr1 Hr2.
    destruct (run_final N1 Δ1 r1 Hb1 Hr1) as [n1 Hf1].
    destruct (run_final N2 Δ2 r2 Hb2 Hr2) as [n2 Hf2].
    destruct (W_total (succ_mass r1 n1) (succ_mass r2 n2)) as [Hle|Hle].
    - left. intros n w [Hw _]. exists n2. etrans; [exact Hw|]. etrans; [apply Hf1|exact Hle].
    - right. intros n w [Hw _]. exists n1. etrans; [exact Hw|]. etrans; [apply Hf2|exact Hle].
  Qed.

  (* Prefixing a step to a run, and dropping the first step. *)
  Definition rcons (Δ : dist conf) (r : nat → dist conf) : nat → dist conf :=
    λ n, match n with 0 => Δ | S n => r n end.

  Definition rtail (r : nat → dist conf) : nat → dist conf := λ n, r (S n).

  Lemma rcons_run Δ σ Δ' r : dstep Δ σ Δ' → is_run Δ' r → is_run Δ (rcons Δ r).
  Proof.
    intros Hs [Hr0 Hr]. split; [done|]. intros [|n]; simpl.
    - left. exists σ. by rewrite Hr0.
    - apply Hr.
  Qed.

  Lemma rtail_run Δ r : is_run Δ r → is_run (r 1) (rtail r).
  Proof. intros [_ Hr]. split; [done|]. intros n. apply (Hr (S n)). Qed.

  Lemma run_le_rcons Δ r1 r : is_run Δ r → run_le r1 (rtail r) → run_le (rcons Δ r1) r.
  Proof.
    intros [Hr0 _] Hle [|n] w Hw; simpl in Hw.
    - exists 0. unfold succ_mass. rewrite Hr0. by destruct Hw.
    - destruct (Hle n w Hw) as [m Hm]. by exists (S m).
  Qed.

  (* A stable distribution has one run, which stays. *)
  Lemma stable_runs Δ r : dstable Δ → is_run Δ r → ∀ n, r n = Δ.
  Proof.
    intros Hst Hr n. pose proof Hr as [Hr0 _].
    rewrite (stable_stays Δ r 0 n Hr); [done| |lia]. by rewrite Hr0.
  Qed.

  Lemma const_run Δ : dstable Δ → is_run Δ (λ _, Δ).
  Proof. intros Hst. split; [done|]. intros n. by right. Qed.

  (* ** The results of a step are among finitely many candidates *)

  Definition cands_l (C : conf) (ρ : St) (aP : pact * proc) : list (dist conf) :=
    let '(a, P') := aP in
    match a with
    | AOp E qs => [dpoint (P', C.2) (sop_apply E qs ρ)]
    | AMeas M qs x => [meas_dist M qs ρ (λ k, (subst P' x (VNat k), C.2))]
    | AOut c v => (λ Q', dpoint (P', Q') ρ) <$> succ C.2 (UAct (AIn c v))
    | AIn _ _ => []
    end.

  Definition cands_r (C : conf) (ρ : St) (aQ : pact * proc) : list (dist conf) :=
    let '(a, Q') := aQ in
    match a with
    | AOp E qs => [dpoint (C.1, Q') (sop_apply E qs ρ)]
    | AMeas M qs x => [meas_dist M qs ρ (λ k, (C.1, subst Q' x (VNat k)))]
    | AOut c v => (λ P', dpoint (P', Q') ρ) <$> succ C.1 (UAct (AIn c v))
    | AIn _ _ => []
    end.

  Definition cands (C : conf) (ρ : St) : list (dist conf) :=
    ((λ P', dpoint (P', C.2) ρ) <$> succ C.1 UTau)
    ++ ((λ Q', dpoint (C.1, Q') ρ) <$> succ C.2 UTau)
    ++ (acts C.1 ≫= cands_l C ρ)
    ++ (acts C.2 ≫= cands_r C ρ).

  Lemma tau_succ P s P' : pstep P (LTau s) P' → P' ∈ succ P UTau.
  Proof. intros Hs. apply succ_spec. by exists (LTau s). Qed.

  Lemma cstep_cands ρ C s Δ : cstep ρ C s Δ → Δ ∈ cands C ρ.
  Proof.
    unfold cands. rewrite !elem_of_app.
    destruct 1 as [P Q s P' Hp|P Q s Q' Hq|P Q t E qs P' Hp|P Q t E qs Q' Hq
                  |P Q t M qs x P' Hp|P Q t M qs x Q' Hq
                  |P Q t t' c v P' Q' Hp Hq|P Q t t' c v P' Q' Hp Hq]; simpl.
    - left. apply list_elem_of_fmap. exists P'. split; [done|]. by eapply tau_succ.
    - right; left. apply list_elem_of_fmap. exists Q'. split; [done|]. by eapply tau_succ.
    - right; right; left. apply list_elem_of_bind. exists (AOp E qs, P').
      split; [simpl; by left|]. apply acts_spec. split; [done|eauto].
    - right; right; right. apply list_elem_of_bind. exists (AOp E qs, Q').
      split; [simpl; by left|]. apply acts_spec. split; [done|eauto].
    - right; right; left. apply list_elem_of_bind. exists (AMeas M qs x, P').
      split; [simpl; by left|]. apply acts_spec. split; [done|eauto].
    - right; right; right. apply list_elem_of_bind. exists (AMeas M qs x, Q').
      split; [simpl; by left|]. apply acts_spec. split; [done|eauto].
    - right; right; left. apply list_elem_of_bind. exists (AOut c v, P'). split.
      + simpl. apply list_elem_of_fmap. exists Q'. split; [done|].
        apply succ_spec. by exists (LAct t' (AIn c v)).
      + apply acts_spec. split; [done|eauto].
    - right; right; right. apply list_elem_of_bind. exists (AOut c v, Q'). split.
      + simpl. apply list_elem_of_fmap. exists P'. split; [done|].
        apply succ_spec. by exists (LAct t (AIn c v)).
      + apply acts_spec. split; [done|eauto].
  Qed.

  Definition opts (x : conf * St) : list (dist conf) := dpoint x.1 x.2 :: cands x.1 x.2.

  Lemma comp_step_opts σ x Δx : comp_step x.2 x.1 σ Δx → Δx ∈ opts x.
  Proof.
    intros Hc. destruct (comp_step_cases σ x Δx Hc) as [[_ Hs]|[_ ->]].
    - right. by eapply cstep_cands.
    - destruct x. left.
  Qed.

  Fixpoint dchoices (Δ : dist conf) : list (list (dist conf)) :=
    match Δ with
    | [] => [[]]
    | x :: Δ => opts x ≫= λ Δx, (λ Δs, Δx :: Δs) <$> dchoices Δ
    end.

  Lemma forall2_dchoices σ Δ Δs :
    Forall2 (λ cρ Δ, comp_step cρ.2 cρ.1 σ Δ) Δ Δs → Δs ∈ dchoices Δ.
  Proof.
    induction 1 as [|x Δx Δ Δs Hx HF IH]; cbn [dchoices]; [by left|].
    apply list_elem_of_bind. exists Δx. split; [|by eapply comp_step_opts].
    apply list_elem_of_fmap. by exists Δs.
  Qed.

  Definition dcands (Δ : dist conf) : list (dist conf) := dsum <$> dchoices Δ.

  Lemma dstep_dcands Δ σ Δ' : dstep Δ σ Δ' → Δ' ∈ dcands Δ.
  Proof.
    intros [_ (Δs & HF & ->)]. apply list_elem_of_fmap. exists Δs. split; [done|].
    by eapply forall2_dchoices.
  Qed.

  (* A component that moves makes the whole distribution step (as
      [dstep_with] in [lqCCS.Characterisations.AlmostSure], with the excluded middle only). *)
  Lemma comp_steps_with' σ (x0 : conf * St) Δ0 (Δ : dist conf) :
    ¬ conf_good x0.1 → cstep x0.2 x0.1 σ Δ0 →
    ∃ Δs, Forall2 (λ cρ Δ, comp_step cρ.2 cρ.1 σ Δ) Δ Δs.
  Proof.
    intros Hg Hs. induction Δ as [|x Δ IH].
    { exists []. constructor. }
    destruct IH as (Δs & HF).
    destruct (XM (¬ conf_good x.1 ∧ ∃ Δx, cstep x.2 x.1 σ Δx)) as [[Hgx [Δx Hsx]]|Hno].
    - exists (Δx :: Δs). constructor; [|done]. left. by split.
    - exists ([x] :: Δs). constructor; [|done]. right. split; [|by destruct x].
      destruct (decide (conf_good x.1)) as [Hgx|Hgx]; [by left|right].
      intros Δ' Hs'. apply Hno. split; [done|]. by exists Δ'.
  Qed.

  Lemma dstep_with' σ x0 Δ0 (Δ : dist conf) :
    x0 ∈ Δ → ¬ conf_good x0.1 → cstep x0.2 x0.1 σ Δ0 → ∃ Δ', dstep Δ σ Δ'.
  Proof.
    intros Hin Hg Hs. destruct (comp_steps_with' σ x0 Δ0 Δ Hg Hs) as (Δs & HF).
    exists (concat Δs). split; [|by exists Δs]. destruct x0 as [c ρ]. exists c, ρ, Δ0. done.
  Qed.

  (* ** Least runs *)

  (* Among the distributions of a finite list that satisfy [S], one has
      a least run below the runs of all the others. *)
  Lemma min_list N (S : dist conf → Prop) (l : list (dist conf)) :
    (∃ Δ', S Δ' ∧ Δ' ∈ l) →
    (∀ Δ', S Δ' → bounded N Δ' ∧ min_run Δ') →
    ∃ Δm rm, S Δm ∧ is_run Δm rm ∧
      ∀ Δ' r', S Δ' → Δ' ∈ l → is_run Δ' r' → run_le rm r'.
  Proof.
    intros Hex HS. induction l as [|a l IH].
    { exfalso. destruct Hex as (Δ' & _ & Hin). set_solver. }
    destruct (XM (∃ Δ', S Δ' ∧ Δ' ∈ l)) as [Hl|Hl].
    - destruct (IH Hl) as (Δm & rm & HSm & Hrm & Hmin).
      destruct (XM (S a)) as [Ha|Ha].
      + destruct (HS a Ha) as [Hba (ra & Hra & Hmina)].
        destruct (HS Δm HSm) as [Hbm _].
        destruct (run_le_total N N a Δm ra rm Hba Hbm Hra Hrm) as [Hle|Hle].
        * exists a, ra. split_and!; [done|done|].
          intros Δ' r' HS' Hin Hr'. apply elem_of_cons in Hin as [->|Hin].
          -- by apply Hmina.
          -- eapply run_le_trans; [exact Hle|]. by apply (Hmin Δ').
        * exists Δm, rm. split_and!; [done|done|].
          intros Δ' r' HS' Hin Hr'. apply elem_of_cons in Hin as [->|Hin].
          -- eapply run_le_trans; [exact Hle|]. by apply Hmina.
          -- by apply (Hmin Δ').
      + exists Δm, rm. split_and!; [done|done|].
        intros Δ' r' HS' Hin Hr'. apply elem_of_cons in Hin as [->|Hin]; [done|].
        by apply (Hmin Δ').
    - destruct Hex as (Δ' & HS' & Hin). apply elem_of_cons in Hin as [->|Hin].
      + destruct (HS a HS') as [_ (ra & Hra & Hmina)].
        exists a, ra. split_and!; [done|done|].
        intros Δ'' r' HS'' Hin' Hr'. apply elem_of_cons in Hin' as [->|Hin'].
        * by apply Hmina.
        * exfalso. apply Hl. eauto.
      + exfalso. apply Hl. eauto.
  Qed.

  Theorem lq_min_run N Δ : bounded N Δ → min_run Δ.
  Proof.
    intros Hb. pose proof (dstep_sn N Δ Hb) as Hacc. revert Hb.
    induction Hacc as [Δ _ IH]. intros Hb.
    destruct (XM (∃ σ, dmoves Δ σ)) as [(σ & c & ρ & Δc & Hin & Hg & Hs)|Hno].
    - set (S := λ Δ', ∃ σ, dstep Δ σ Δ').
      destruct (dstep_with' σ (c, ρ) Δc Δ Hin Hg Hs) as (Δ1 & Hst1).
      destruct (min_list N S (dcands Δ)) as (Δm & rm & (σm & Hsm) & Hrm & Hmin).
      + exists Δ1. split; [by exists σ|]. by eapply dstep_dcands.
      + intros Δ' HS'. split; [destruct HS' as [σ' HS']; by eapply dstep_bounded|].
        apply IH; [done|]. destruct HS' as [σ' HS']. by eapply dstep_bounded.
      + exists (rcons Δ rm). split; [by eapply rcons_run|].
        intros r Hr. apply run_le_rcons; [done|].
        pose proof Hr as [Hr0 Hrs].
        destruct (Hrs 0) as [(σ' & Hst)|[Hstab _]].
        * rewrite Hr0 in Hst.
          apply (Hmin (r 1)); [by exists σ'|by eapply dstep_dcands|exact (rtail_run Δ r Hr)].
        * exfalso. rewrite Hr0 in Hstab. apply (Hstab σ). exists c, ρ, Δc. done.
    - assert (Hst : dstable Δ) by (intros σ Hσ; apply Hno; by exists σ).
      exists (λ _, Δ). split; [by apply const_run|].
      intros r Hr n w [Hw _]. exists 0. unfold succ_mass in *.
      by rewrite (stable_runs Δ r Hst Hr 0).
  Qed.

  (* ** The Smyth must of lqCCS as threshold musts *)

  Lemma compose_bounded (x : proc * St) (T : proc) :
    bounded (csize (x.1, T)) (compose_lq x T).
  Proof. intros y Hy. unfold compose_lq, dpoint in Hy. set_solver. Qed.

  Theorem lq_pre_sm_iff_must_lt (x y : proc * St) :
    x ⊑ₛₘ y ↔ ∀ T w, must_lt w (compose x T) → must_lt w (compose y T).
  Proof.
    apply ctx_pre_sm_iff_must_lt. intros T.
    exact (lq_min_run _ _ (compose_bounded x T)).
  Qed.
End Smyth.
(* end hide *)
