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
(* * The Smyth must sees correlations between measurement branches

    A measurement [M] on a qubit [q] with two outcomes [k0], [k1] of
    non-zero weight.  After it, both processes send the outcome on [c] and
    choose between [a!0] and [b!0] with the tags [t1], [t2]:

    - [P_corr]: [t1] gives [a] and [t2] gives [b] in both branches;
    - [P_anti]: the choice is swapped in the branch [k1].

    Branch by branch the two processes offer the same choices; only the
    correlation of the choices across the branches differs, and admissible
    schedulers (one tag for the whole distribution) make it observable.  The
    observer [T = c?y. if y = k0 then a?_.① else b?_.①] branches on the
    outcome: [P_anti ∥ T] has a run that never succeeds (choose [t2]), while
    every run of [P_corr ∥ T] succeeds with positive weight.  So
    [(P_corr, ρ) ⋢ₛₘ (P_anti, ρ)] ([corr_not_below_anti]).

    The observer branches: tests that follow one sequence of actions
    (co-ready traces, Georgievska and Andova) cannot tell such processes
    apart when the two outcomes have the same weight; the characterisation
    of the Smyth must needs trees (as the [αᴛᴇꜱᴛ p⊕ ψ] of the logic F of Deng,
    van Glabbeek, Hennessy and Morgan). *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list sets gmap.
From TestingTheory Require Import lqCCS.Harmony_Lemma.Lifted lqCCS.Harmony_Lemma.Paths lqCCS.Harmony_Lemma.States pMust_almost_sure pMust_smyth lqCCS.Language.Quantum.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.Program lqCCS.Language.Succ lqCCS.Language.Composition
  lqCCS.Language.LTS lqCCS.Characterisations.AlmostSure lqCCS.Language.Congruence.
(* ** Inversion of the steps of small programs *)

Lemma pstep_send_inv t c e l X :
  pstep (PSend t c e) l X → ∃ v, l = LAct t (AOut c v) ∧ eval e = Some v ∧ X = PG (GNil []).
Proof. inversion 1; subst. eauto. Qed.

Lemma pstep_par_inv P Q l X :
  pstep (PPar P Q) l X →
    (∃ P', pstep P l P' ∧ X = PPar P' Q)
  ∨ (∃ Q', pstep Q l Q' ∧ X = PPar P Q')
  ∨ (∃ t t' c v P' Q', l = LTau (SPair t t') ∧ X = PPar P' Q' ∧
       ((pstep P (LAct t (AOut c v)) P' ∧ pstep Q (LAct t' (AIn c v)) Q')
        ∨ (pstep P (LAct t (AIn c v)) P' ∧ pstep Q (LAct t' (AOut c v)) Q'))).
Proof.
  inversion 1; subst.
  - left. eauto.
  - right; left. eauto.
  - right; right. eauto 15.
  - right; right. eauto 15.
Qed.

Lemma pstep_ite_inv e P Q l X :
  pstep (PIte e P Q) l X →
  (eval e = Some (VBool true) ∧ pstep P l X) ∨ (eval e = Some (VBool false) ∧ pstep Q l X).
Proof. inversion 1; subst; eauto. Qed.

Lemma pstep_sum_inv g1 g2 l X :
  pstep (PG (GSum g1 g2)) l X → pstep (PG g1) l X ∨ pstep (PG g2) l X.
Proof.
  inversion 1 as [? ? ? Hg| | | | | | | |]; subst.
  inversion Hg; subst; [left|right]; by constructor.
Qed.

Lemma pstep_tau_inv t P l X : pstep (PG (GPre (PTau t) P)) l X → l = LTau (STag t) ∧ X = P.
Proof. inversion 1 as [? ? ? Hg| | | | | | | |]; subst. by inversion Hg. Qed.

Lemma pstep_recv_inv t c x P l X :
  pstep (PG (GPre (PRecv t c x) P)) l X → ∃ v, l = LAct t (AIn c v) ∧ X = subst P x v.
Proof. inversion 1 as [? ? ? Hg| | | | | | | |]; subst. inversion Hg; subst. eauto. Qed.

Lemma pstep_succ_inv l X : ¬ pstep (PG GSucc) l X.
Proof. inversion 1 as [? ? ? Hg| | | | | | | |]; subst. inversion Hg. Qed.

Lemma pstep_meas_inv t M es x P l X :
  pstep (PG (GPre (PMeas t M es x) P)) l X →
  ∃ qs, eval_qubits es = Some qs ∧ l = LAct t (AMeas M qs x) ∧ X = P.
Proof. inversion 1 as [? ? ? Hg| | | | | | | |]; subst. inversion Hg; subst. eauto. Qed.

Section Example.
  Context `{QM : QuantumModel}.
  Context (W_strict : ∀ a b, W_le (W_add a b) a → b = W_zero).
  Context (W_dense : ∀ a b : W, a <ₚ b → ∃ c, a <ₚ c ∧ c <ₚ b).
  Context (M : meas) (q : qubit) (ρ : St) (k0 k1 : Out (meas_of M [q])).
  Context (Houts : outs (meas_of M [q]) = [k0; k1]).
  Context (Hcode : code _ k0 ≠ code _ k1).
  Context (Hn0 : nonzero (meas_branch M [q] k0 ρ)) (Hn1 : nonzero (meas_branch M [q] k1 ρ)).

  Notation c0 := (code _ k0).
  Notation c1 := (code _ k1).

  (* ** The processes and the observer *)

  Definition vk (b : bool) : val := VNat (if b then c0 else c1).
  Definition wk (b : bool) : St := meas_branch M [q] (if b then k0 else k1) ρ.

  Definition sendA : proc := PSend 4 1 (EVal (VNat 0)).
  Definition sendB : proc := PSend 5 2 (EVal (VNat 0)).
  Definition ChAB : proc := PG (GSum (GPre (PTau 2) sendA) (GPre (PTau 3) sendB)).
  Definition ChBA : proc := PG (GSum (GPre (PTau 2) sendB) (GPre (PTau 3) sendA)).
  Definition qes : list exp := [EVal (VQubit q)].

  Definition corr_body : proc := PPar (PSend 1 0 (EVar 0)) ChAB.
  Definition anti_body : proc :=
    PPar (PSend 1 0 (EVar 0)) (PIte (EEq (EVar 0) (EVal (VNat c0))) ChAB ChBA).

  Definition Pcorr : proc := PG (GPre (PMeas 0 M qes 0) corr_body).
  Definition Panti : proc := PG (GPre (PMeas 0 M qes 0) anti_body).

  Definition TA : proc := PG (GPre (PRecv 11 1 2) (PG GSucc)).
  Definition TB : proc := PG (GPre (PRecv 12 2 2) (PG GSucc)).
  Definition Tite (v : val) : proc := PIte (EEq (EVal v) (EVal (VNat c0))) TA TB.
  Definition Tbr : proc := PG (GPre (PRecv 10 0 1) (PIte (EEq (EVar 1) (EVal (VNat c0))) TA TB)).

  Lemma eval_vk b : eval (EEq (EVal (vk b)) (EVal (VNat c0))) = Some (VBool b).
  Proof.
    destruct b; simpl.
    - by rewrite bool_decide_eq_true_2.
    - rewrite bool_decide_eq_false_2; [done|]. intros [=]. by apply Hcode.
  Qed.

  Lemma eval_qes : eval_qubits qes = Some [q].
  Proof. done. Qed.

  Lemma tr_pos b : W_zero <ₚ (tr (wk b)).
  Proof.
    split; [apply W_zero_le|]. intros Hle. assert (Hz : tr (wk b) = W_zero).
    { apply (W_strict W_zero). by rewrite W_add_zero. }
    apply tr_zero_inv in Hz. destruct b; [by apply Hn0|by apply Hn1].
  Qed.

  Lemma meas_split (f : nat → conf) :
    meas_dist M [q] ρ f = [(f c0, wk true); (f c1, wk false)].
  Proof. unfold meas_dist. rewrite Houts. done. Qed.

  (* ** A run of [P_anti ∥ T] that never succeeds *)

  Definition anti_mid (b : bool) : proc :=
    PPar (PSend 1 0 (EVal (vk b))) (PIte (EEq (EVal (vk b)) (EVal (VNat c0))) ChAB ChBA).
  Definition anti_chosen (b : bool) : proc := if b then sendB else sendA.

  Definition Δa0 : dist conf := dpoint (Panti, Tbr) ρ.
  Definition Δa1 : dist conf :=
    [((anti_mid true, Tbr), wk true); ((anti_mid false, Tbr), wk false)].
  Definition Δa2 : dist conf :=
    [((PPar (PSend 1 0 (EVal (vk true))) (anti_chosen true), Tbr), wk true);
     ((PPar (PSend 1 0 (EVal (vk false))) (anti_chosen false), Tbr), wk false)].
  Definition Δa3 : dist conf :=
    [((PPar (PG (GNil [])) (anti_chosen true), Tite (vk true)), wk true);
     ((PPar (PG (GNil [])) (anti_chosen false), Tite (vk false)), wk false)].

  Lemma not_good_Tite v : ¬ good (Tite v).
  Proof. unfold good, Tite. simpl. intros Hg. repeat case_match; discriminate. Qed.

  Lemma step_a01 : dstep Δa0 (STag 0) Δa1.
  Proof.
    assert (Hs : cstep ρ (Panti, Tbr) (STag 0) Δa1).
    { replace Δa1 with (meas_dist M [q] ρ (λ k, (subst anti_body 0 (VNat k), Tbr))).
      - apply cs_measL. constructor. by apply gs_meas.
      - rewrite meas_split. done. }
    split.
    - exists (Panti, Tbr), ρ, Δa1. split_and!; [by left|by intros [=]|done].
    - exists [Δa1]. split; [constructor; [left; split; [simpl; by intros [=]|done]|constructor]|].
      unfold dsum. simpl. by rewrite ?app_nil_r.
  Qed.

  Lemma tau_mid b :
    pstep (anti_mid b) (LTau (STag 3)) (PPar (PSend 1 0 (EVal (vk b))) (anti_chosen b)).
  Proof.
    apply ps_parR. destruct b.
    - apply ps_iteT; [apply (eval_vk true)|]. constructor. apply gs_sumR. constructor.
    - apply ps_iteF; [apply (eval_vk false)|]. constructor. apply gs_sumR. constructor.
  Qed.

  Lemma step_a12 : dstep Δa1 (STag 3) Δa2.
  Proof.
    unfold Δa1, Δa2. split.
    - eexists _, _, _. split_and!; [by left|by intros [=]|]. apply cs_tauL, tau_mid.
    - exists [[((PPar (PSend 1 0 (EVal (vk true))) (anti_chosen true), Tbr), wk true)];
              [((PPar (PSend 1 0 (EVal (vk false))) (anti_chosen false), Tbr), wk false)]].
      split; [|reflexivity].
      constructor; [left; split; [simpl; by intros [=]|apply cs_tauL, tau_mid]|].
      constructor; [left; split; [simpl; by intros [=]|apply cs_tauL, tau_mid]|constructor].
  Qed.

  Lemma com_c b P :
    cstep (wk b) (PPar (PSend 1 0 (EVal (vk b))) P, Tbr) (SPair 1 10)
      (dpoint (PPar (PG (GNil [])) P, Tite (vk b)) (wk b)).
  Proof.
    eapply (cs_comLR _ _ _ 1 10 0 (vk b)).
    - apply ps_parL. by constructor.
    - constructor. replace (Tite (vk b)) with
        (subst (PIte (EEq (EVar 1) (EVal (VNat c0))) TA TB) 1 (vk b)) by done.
      constructor.
  Qed.

  Lemma step_a23 : dstep Δa2 (SPair 1 10) Δa3.
  Proof.
    unfold Δa2, Δa3. split.
    - eexists _, _, _. split_and!; [by left|by intros [=]|apply com_c].
    - exists [[((PPar (PG (GNil [])) (anti_chosen true), Tite (vk true)), wk true)];
              [((PPar (PG (GNil [])) (anti_chosen false), Tite (vk false)), wk false)]].
      split; [|reflexivity].
      constructor; [left; split; [simpl; by intros [=]|apply com_c]|].
      constructor; [left; split; [simpl; by intros [=]|apply com_c]|constructor].
  Qed.

  (* The last distribution is stable: in each branch, the program offers
      the wrong channel. *)
  Lemma final_no_step b w σ Δx :
    ¬ cstep w (PPar (PG (GNil [])) (anti_chosen b), Tite (vk b)) σ Δx.
  Proof.
    intros Hc.
    assert (HP : ∀ l X, pstep (PPar (PG (GNil [])) (anti_chosen b)) l X →
              ∃ v, l = LAct (if b then 5 else 4) (AOut (if b then 2 else 1) v)).
    { intros l X Hs.
      destruct (pstep_par_inv _ _ _ _ Hs) as [(P' & Hp & _)|[(Q' & Hq & _)|(? & ? & ? & ? & ? & ? & _ & _ & [[Hp _]|[Hp _]])]].
      - by apply pstep_nil in Hp.
      - destruct b; apply pstep_send_inv in Hq as (v & -> & _); eauto.
      - by apply pstep_nil in Hp.
      - by apply pstep_nil in Hp. }
    assert (HQ : ∀ l X, pstep (Tite (vk b)) l X →
              ∃ v, l = LAct (if b then 11 else 12) (AIn (if b then 1 else 2) v)).
    { intros l X Hs. apply pstep_ite_inv in Hs as [[He Hs]|[He Hs]];
        rewrite eval_vk in He; simplify_eq; apply pstep_recv_inv in Hs as (v & -> & _); eauto. }
    inversion Hc as [P Q s P' Hp|P Q s Q' Hq|P Q t E qs P' Hp|P Q t E qs Q' Hq
                    |P Q t M' qs x P' Hp|P Q t M' qs x Q' Hq
                    |P Q t t' c v P' Q' Hp Hq|P Q t t' c v P' Q' Hp Hq]; subst.
    - destruct (HP _ _ Hp) as [v ?]. discriminate.
    - destruct (HQ _ _ Hq) as [v ?]. discriminate.
    - destruct (HP _ _ Hp) as [v ?]. discriminate.
    - destruct (HQ _ _ Hq) as [v ?]. discriminate.
    - destruct (HP _ _ Hp) as [v ?]. discriminate.
    - destruct (HQ _ _ Hq) as [v ?]. discriminate.
    - destruct (HP _ _ Hp) as [v1 E1]. destruct (HQ _ _ Hq) as [v2 E2].
      destruct b; simplify_eq.
    - destruct (HP _ _ Hp) as [v1 E1]. discriminate.
  Qed.

  Lemma stable_a3 : dstable Δa3.
  Proof.
    intros σ (C & w & Δx & Hin & _ & Hs). unfold Δa3 in Hin.
    repeat (apply elem_of_cons in Hin as [Hin|Hin]); [| |set_solver]; simplify_eq;
      [apply (final_no_step true _ σ Δx Hs)|apply (final_no_step false _ σ Δx Hs)].
  Qed.

  Lemma dmass_of_zero (Δ : dist conf) :
    (∀ x, x ∈ Δ → ¬ conf_good x.1) → dmass_of conf_good Δ = W_zero.
  Proof.
    induction Δ as [|x Δ IH]; intros Hg; [done|].
    rewrite dmass_of_cons, decide_False by (apply Hg; by left).
    apply IH. intros y Hy. apply Hg. by right.
  Qed.

  Lemma not_good_Tbr : ¬ conf_good (Panti, Tbr).
  Proof. unfold conf_good, good. simpl. done. Qed.

  Definition r_anti : nat → dist conf := chain_run Δa0 [Δa1; Δa2; Δa3].

  Lemma r_anti_run : is_run Δa0 r_anti.
  Proof.
    apply chain_is_run; [|exact stable_a3].
    split; [exists (STag 0); apply step_a01|].
    split; [exists (STag 3); apply step_a12|].
    split; [exists (SPair 1 10); apply step_a23|done].
  Qed.

  Lemma r_anti_zero n : succ_mass r_anti n = W_zero.
  Proof.
    unfold succ_mass, r_anti, chain_run. apply dmass_of_zero.
    destruct n as [|[|[|n]]]; simpl.
    - intros x Hx. unfold Δa0, dpoint in Hx. apply list_elem_of_singleton in Hx as ->.
      apply not_good_Tbr.
    - intros x Hx. unfold Δa1 in Hx.
      repeat (apply elem_of_cons in Hx as [->|Hx]); [| |set_solver];
        unfold conf_good, good; simpl; done.
    - intros x Hx. unfold Δa2 in Hx.
      repeat (apply elem_of_cons in Hx as [->|Hx]); [| |set_solver];
        unfold conf_good, good; simpl; done.
    - intros x Hx. assert (Hx' : x ∈ Δa3) by (destruct n as [|[|]]; exact Hx). clear Hx.
      unfold Δa3 in Hx'.
      repeat (apply elem_of_cons in Hx' as [->|Hx']); [| |set_solver]; apply not_good_Tite.
  Qed.

  (* ** Every run of [P_corr ∥ T] succeeds with positive weight *)

  (* The state of a branch: [c] sent, the choice made, the synchronisation
      on [a] or [b] done. *)
  Notation cst := (bool * option bool * bool)%type.

  Definition chpart (ch : option bool) (d : bool) : proc :=
    match ch with
    | None => ChAB
    | Some true => if d then PG (GNil []) else sendA
    | Some false => if d then PG (GNil []) else sendB
    end.

  Definition pc (b : bool) (s : cst) : proc :=
    let '(cd, ch, d) := s in
    PPar (if cd then PG (GNil []) else PSend 1 0 (EVal (vk b))) (chpart ch d).

  Definition tc (b : bool) (s : cst) : proc :=
    let '(cd, ch, d) := s in if cd then (if d then PG GSucc else Tite (vk b)) else Tbr.

  Definition wf (s : cst) : Prop := let '(cd, ch, d) := s in d = true → cd = true ∧ ch ≠ None.

  Inductive ttrans (b : bool) : Sched → cst → cst → Prop :=
  | tt_c ch : ttrans b (SPair 1 10) (false, ch, false) (true, ch, false)
  | tt_A cd : ttrans b (STag 2) (cd, None, false) (cd, Some true, false)
  | tt_B cd : ttrans b (STag 3) (cd, None, false) (cd, Some false, false)
  | tt_a : b = true → ttrans b (SPair 4 11) (true, Some true, false) (true, Some true, true)
  | tt_b : b = false → ttrans b (SPair 5 12) (true, Some false, false) (true, Some false, true).

  Lemma chpart_step ch d l X :
    pstep (chpart ch d) l X →
      (ch = None ∧ ((l = LTau (STag 2) ∧ X = sendA) ∨ (l = LTau (STag 3) ∧ X = sendB)))
    ∨ (ch = Some true ∧ d = false ∧ l = LAct 4 (AOut 1 (VNat 0)) ∧ X = PG (GNil []))
    ∨ (ch = Some false ∧ d = false ∧ l = LAct 5 (AOut 2 (VNat 0)) ∧ X = PG (GNil [])).
  Proof.
    destruct ch as [[]|]; [destruct d| destruct d|]; simpl; intros Hs.
    - by apply pstep_nil in Hs.
    - apply pstep_send_inv in Hs as (v & -> & Hv & ->). simpl in Hv. simplify_eq. eauto 10.
    - by apply pstep_nil in Hs.
    - apply pstep_send_inv in Hs as (v & -> & Hv & ->). simpl in Hv. simplify_eq. eauto 10.
    - left. split; [done|].
      apply pstep_sum_inv in Hs as [Hs|Hs]; apply pstep_tau_inv in Hs as [-> ->]; eauto.
  Qed.

  Lemma pc_step b s l X : wf s → pstep (pc b s) l X →
      (∃ ch d, s = (false, ch, d) ∧ l = LAct 1 (AOut 0 (vk b)) ∧ X = pc b (true, ch, d))
    ∨ (∃ cd, s = (cd, None, false) ∧
         ((l = LTau (STag 2) ∧ X = pc b (cd, Some true, false))
          ∨ (l = LTau (STag 3) ∧ X = pc b (cd, Some false, false))))
    ∨ (∃ cd, s = (cd, Some true, false) ∧ l = LAct 4 (AOut 1 (VNat 0)) ∧ X = pc b (cd, Some true, true))
    ∨ (∃ cd, s = (cd, Some false, false) ∧ l = LAct 5 (AOut 2 (VNat 0)) ∧ X = pc b (cd, Some false, true)).
  Proof.
    destruct s as [[cd ch] d]. intros Hwf Hs. simpl in Hs.
    assert (Hleft : ∀ l X, pstep (if cd then PG (GNil []) else PSend 1 0 (EVal (vk b))) l X →
              cd = false ∧ l = LAct 1 (AOut 0 (vk b)) ∧ X = PG (GNil [])).
    { intros l' X' H'. destruct cd; [by apply pstep_nil in H'|].
      apply pstep_send_inv in H' as (v & -> & Hv & ->). simpl in Hv. by simplify_eq. }
    destruct (pstep_par_inv _ _ _ _ Hs)
      as [(P' & Hp & ->)|[(Q' & Hq & ->)|(t & t' & c & v & P' & Q' & -> & -> & [[Hp Hq]|[Hp Hq]])]].
    - destruct (Hleft _ _ Hp) as (-> & -> & ->). left. eauto.
    - destruct (chpart_step _ _ _ _ Hq) as [(-> & [[-> ->]|[-> ->]])|[(-> & -> & -> & ->)|(-> & -> & -> & ->)]].
      + assert (d = false) as -> by (destruct d; [by destruct (Hwf eq_refl)|done]).
        right; left. exists cd. split; [done|]. left. by destruct cd.
      + assert (d = false) as -> by (destruct d; [by destruct (Hwf eq_refl)|done]).
        right; left. exists cd. split; [done|]. right. by destruct cd.
      + right; right; left. exists cd. split_and!; [done|done|by destruct cd].
      + right; right; right. exists cd. split_and!; [done|done|by destruct cd].
    - destruct (chpart_step _ _ _ _ Hq) as [(_ & [[? _]|[? _]])|[(_ & _ & ? & _)|(_ & _ & ? & _)]];
        discriminate.
    - destruct (Hleft _ _ Hp) as (_ & ? & _). discriminate.
  Qed.

  Lemma tc_step b s l X :
    pstep (tc b s) l X →
      (∃ ch d v, s = (false, ch, d) ∧ l = LAct 10 (AIn 0 v) ∧ X = Tite v)
    ∨ (∃ ch v, s = (true, ch, false) ∧
         ((b = true ∧ l = LAct 11 (AIn 1 v)) ∨ (b = false ∧ l = LAct 12 (AIn 2 v))) ∧
         X = PG GSucc).
  Proof.
    destruct s as [[cd ch] d]. simpl. intros Hs. destruct cd; [destruct d|].
    - by apply pstep_succ_inv in Hs.
    - right. apply pstep_ite_inv in Hs as [[He Hs]|[He Hs]];
        rewrite eval_vk in He; simplify_eq;
        apply pstep_recv_inv in Hs as (v & -> & ->); eauto 10.
    - left. apply pstep_recv_inv in Hs as (v & -> & ->). eauto 10.
  Qed.

  Lemma comp_cstep b s w σ Δx :
    wf s → cstep w (pc b s, tc b s) σ Δx →
    ∃ s', ttrans b σ s s' ∧ Δx = dpoint (pc b s', tc b s') w.
  Proof.
    intros Hwf Hc.
    inversion Hc as [P Q s0 P' Hp|P Q s0 Q' Hq|P Q t E qs P' Hp|P Q t E qs Q' Hq
                    |P Q t M' qs x P' Hp|P Q t M' qs x Q' Hq
                    |P Q t t' c v P' Q' Hp Hq|P Q t t' c v P' Q' Hp Hq]; subst.
    - destruct (pc_step _ _ _ _ Hwf Hp)
        as [(? & ? & -> & ? & ->)|[(cd & -> & [[[= ->] ->]|[[= ->] ->]])|[(? & -> & ? & ->)|(? & -> & ? & ->)]]];
        try discriminate.
      + eexists. split; [constructor|]. done.
      + eexists. split; [constructor|]. done.
    - destruct (tc_step _ _ _ _ Hq) as [(? & ? & ? & -> & ? & _)|(? & ? & -> & [[_ ?]|[_ ?]] & _)];
        discriminate.
    - destruct (pc_step _ _ _ _ Hwf Hp)
        as [(? & ? & -> & ? & ->)|[(cd & -> & [[? _]|[? _]])|[(? & -> & ? & ->)|(? & -> & ? & ->)]]];
        discriminate.
    - destruct (tc_step _ _ _ _ Hq) as [(? & ? & ? & -> & ? & _)|(? & ? & -> & [[_ ?]|[_ ?]] & _)];
        discriminate.
    - destruct (pc_step _ _ _ _ Hwf Hp)
        as [(? & ? & -> & ? & ->)|[(cd & -> & [[? _]|[? _]])|[(? & -> & ? & ->)|(? & -> & ? & ->)]]];
        discriminate.
    - destruct (tc_step _ _ _ _ Hq) as [(? & ? & ? & -> & ? & _)|(? & ? & -> & [[_ ?]|[_ ?]] & _)];
        discriminate.
    - destruct (pc_step _ _ _ _ Hwf Hp)
        as [(ch & d & Hs & El & ->)|[(cd & -> & [[? _]|[? _]])|[(cd & Hs & El & ->)|(cd & Hs & El & ->)]]];
        try discriminate;
      destruct (tc_step _ _ _ _ Hq) as [(ch' & d' & v' & Hs' & El' & ->)|(ch' & v' & Hs' & [[Hb El']|[Hb El']] & ->)];
        simplify_eq.
      + assert (d' = false) as -> by (destruct d'; [by destruct (Hwf eq_refl)|done]).
        eexists. split; [constructor|]. done.
      + eexists. split; [by constructor|]. done.
      + eexists. split; [by constructor|]. done.
    - destruct (pc_step _ _ _ _ Hwf Hp)
        as [(? & ? & -> & ? & ->)|[(cd & -> & [[? _]|[? _]])|[(? & -> & ? & ->)|(? & -> & ? & ->)]]];
        discriminate.
  Qed.

  Lemma good_shape b s : conf_good (pc b s, tc b s) → ∃ ch, s = (true, ch, true).
  Proof.
    destruct s as [[[] ch] []]; simpl; eauto; unfold conf_good; simpl.
    - intros Hg. by apply not_good_Tite in Hg.
    - by unfold good.
    - by unfold good.
  Qed.

  Lemma recv_Tbr v : pstep Tbr (LAct 10 (AIn 0 v)) (Tite v).
  Proof.
    replace (Tite v) with (subst (PIte (EEq (EVar 1) (EVal (VNat c0))) TA TB) 1 v) by done.
    constructor. constructor.
  Qed.

  Lemma ttrans_cstep b σ s s' w :
    ttrans b σ s s' → cstep w (pc b s, tc b s) σ (dpoint (pc b s', tc b s') w).
  Proof.
    destruct 1 as [ch|cd|cd|Hb|Hb]; simpl.
    - eapply (cs_comLR _ _ _ 1 10 0 (vk b)); [apply ps_parL; by constructor|apply recv_Tbr].
    - apply cs_tauL. apply ps_parR. constructor. apply gs_sumL. constructor.
    - apply cs_tauL. apply ps_parR. constructor. apply gs_sumR. constructor.
    - subst. eapply (cs_comLR _ _ _ 4 11 1 (VNat 0)); [apply ps_parR; by constructor|].
      apply ps_iteT; [apply (eval_vk true)|]. replace (PG GSucc) with (subst (PG GSucc) 2 (VNat 0)) by done.
      constructor. constructor.
    - subst. eapply (cs_comLR _ _ _ 5 12 2 (VNat 0)); [apply ps_parR; by constructor|].
      apply ps_iteF; [apply (eval_vk false)|]. replace (PG GSucc) with (subst (PG GSucc) 2 (VNat 0)) by done.
      constructor. constructor.
  Qed.

  Lemma ttrans_det b σ s s1 s2 : ttrans b σ s s1 → ttrans b σ s s2 → s1 = s2.
  Proof. destruct 1; inversion 1; subst; done. Qed.

  Lemma ttrans_wf b σ s s' : ttrans b σ s s' → wf s'.
  Proof. destruct 1; simpl; intros; try done; split; done. Qed.

  Lemma comp_step_shape b s w σ Δx :
    wf s → comp_step w (pc b s, tc b s) σ Δx →
    Δx = dpoint (pc b s, tc b s) w ∨ ∃ s', ttrans b σ s s' ∧ Δx = dpoint (pc b s', tc b s') w.
  Proof.
    intros Hwf [[_ Hs]|[_ ->]]; [right|by left]. by apply (comp_cstep b s w σ Δx).
  Qed.

  Lemma must_move b s w σ s' Δx :
    wf s → ttrans b σ s s' → ¬ conf_good (pc b s, tc b s) →
    comp_step w (pc b s, tc b s) σ Δx → Δx = dpoint (pc b s', tc b s') w.
  Proof.
    intros Hwf Ht Hg [[_ Hs]|[[Hg'|Hno] _]].
    - destruct (comp_cstep b s w σ Δx Hwf Hs) as (s'' & Ht' & ->).
      by rewrite (ttrans_det b σ s s'' s' Ht' Ht).
    - done.
    - exfalso. by apply (Hno _ (ttrans_cstep b σ s s' w Ht)).
  Qed.

  Definition Inv (s0 s1 : cst) : Prop := s0.1 = s1.1 ∧ wf s0 ∧ wf s1.

  Definition Shape (s0 s1 : cst) : dist conf :=
    [((pc true s0, tc true s0), wk true); ((pc false s1, tc false s1), wk false)].

  (* The silent and choice steps move both branches together. *)
  Lemma ttrans_other b b2 σ s s' s2 :
    ttrans b σ s s' → σ ≠ SPair 4 11 → σ ≠ SPair 5 12 → s2.1 = s.1 → wf s2 →
    ¬ conf_good (pc b2 s2, tc b2 s2) ∧ ∃ s2', ttrans b2 σ s2 s2' ∧ s2'.1 = s'.1.
  Proof.
    destruct s2 as [[cd2 ch2] d2].
    destruct 1 as [ch|cd|cd|Hb|Hb]; intros Ha Hb' E Hwf; simpl in E; simplify_eq;
      try done.
    - assert (d2 = false) as -> by (destruct d2; [by destruct (Hwf eq_refl)|done]).
      split; [intros (? & [=])%good_shape|]. eexists. split; [constructor|done].
    - assert (d2 = false) as -> by (destruct d2; [by destruct (Hwf eq_refl)|done]).
      split; [intros (? & [=])%good_shape|]. eexists. split; [constructor|done].
    - assert (d2 = false) as -> by (destruct d2; [by destruct (Hwf eq_refl)|done]).
      split; [intros (? & [=])%good_shape|]. eexists. split; [constructor|done].
  Qed.

  Lemma ttrans_sync b σ s s' : ttrans b σ s s' → (σ = SPair 4 11 ∨ σ = SPair 5 12) → s'.1 = s.1.
  Proof. destruct 1; intros [?|?]; simplify_eq; done. Qed.

  Lemma shape_step s0 s1 σ Δ' :
    Inv s0 s1 → dstep (Shape s0 s1) σ Δ' → ∃ s0' s1', Inv s0' s1' ∧ Δ' = Shape s0' s1'.
  Proof.
    intros (Heq & Hw0 & Hw1) [_ (Δs & HF & ->)]. unfold Shape in HF.
    inversion HF as [|x0 Δx0 l0 Δs0 Hc0 HF0]; subst.
    inversion HF0 as [|x1 Δx1 l1 Δs1 Hc1 HF1]; subst. inversion HF1; subst.
    simpl in Hc0, Hc1.
    destruct (decide (σ = SPair 4 11 ∨ σ = SPair 5 12)) as [Hab|Hab].
    - destruct (comp_step_shape true s0 _ σ Δx0 Hw0 Hc0) as [->|(s0' & Ht0 & ->)];
      destruct (comp_step_shape false s1 _ σ Δx1 Hw1 Hc1) as [->|(s1' & Ht1 & ->)].
      + exists s0, s1. split; [by repeat split|reflexivity].
      + exists s0, s1'. unfold Inv. split_and!; [by rewrite (ttrans_sync _ _ _ _ Ht1 Hab)|done|by eapply ttrans_wf|done].
      + exists s0', s1. unfold Inv. split_and!; [by rewrite (ttrans_sync _ _ _ _ Ht0 Hab)|by eapply ttrans_wf|done|done].
      + exists s0', s1'. unfold Inv. split_and!; [by rewrite (ttrans_sync _ _ _ _ Ht0 Hab), (ttrans_sync _ _ _ _ Ht1 Hab)
                                     |by eapply ttrans_wf|by eapply ttrans_wf|done].
    - assert (Hσ1 : σ ≠ SPair 4 11) by naive_solver.
      assert (Hσ2 : σ ≠ SPair 5 12) by naive_solver.
      destruct (comp_step_shape true s0 _ σ Δx0 Hw0 Hc0) as [->|(s0' & Ht0 & ->)].
      + destruct (comp_step_shape false s1 _ σ Δx1 Hw1 Hc1) as [->|(s1' & Ht1 & ->)].
        * exists s0, s1. split; [by repeat split|reflexivity].
        * destruct (ttrans_other false true σ s1 s1' s0 Ht1 Hσ1 Hσ2 Heq Hw0) as (Hg & s0' & Ht0 & E).
          exfalso. pose proof (must_move true s0 _ σ s0' _ Hw0 Ht0 Hg Hc0) as Heq'.
          simplify_eq. pose proof (ttrans_wf _ _ _ _ Ht0).
          destruct s0 as [[cd ch] d]; inversion Ht0; subst; simpl in *; simplify_eq;
            destruct d; simplify_eq.
      + destruct (ttrans_other true false σ s0 s0' s1 Ht0 Hσ1 Hσ2 (eq_sym Heq) Hw1) as (Hg & s1' & Ht1 & E).
        rewrite (must_move false s1 _ σ s1' _ Hw1 Ht1 Hg Hc1).
        exists s0', s1'. unfold Inv. split_and!; [by rewrite E|by eapply ttrans_wf|by eapply ttrans_wf|done].
  Qed.
  (* The first step measures; the two branches start in [s_init]. *)
  Definition s_init : cst := (false, None, false).
  Definition Δc0 : dist conf := dpoint (Pcorr, Tbr) ρ.

  Lemma start_cstep_ex : cstep ρ (Pcorr, Tbr) (STag 0) (Shape s_init s_init).
  Proof.
    replace (Shape s_init s_init) with (meas_dist M [q] ρ (λ k, (subst corr_body 0 (VNat k), Tbr))).
    - apply cs_measL. constructor. by apply gs_meas.
    - rewrite meas_split. done.
  Qed.

  Lemma start_cstep σ Δ : cstep ρ (Pcorr, Tbr) σ Δ → σ = STag 0 ∧ Δ = Shape s_init s_init.
  Proof.
    intros Hc.
    inversion Hc as [P Q s P' Hp|P Q s Q' Hq|P Q t E qs P' Hp|P Q t E qs Q' Hq
                    |P Q t M' qs x P' Hp|P Q t M' qs x Q' Hq
                    |P Q t t' c v P' Q' Hp Hq|P Q t t' c v P' Q' Hp Hq]; subst;
      try (apply pstep_meas_inv in Hp as (? & _ & ? & _); discriminate);
      try (apply pstep_recv_inv in Hq as (? & ? & _); discriminate).
    apply pstep_meas_inv in Hp as (qs' & Hqs & Hl & ->). rewrite eval_qes in Hqs. simplify_eq.
    split; [done|]. rewrite meas_split. done.
  Qed.

  Lemma start_step σ Δ' : dstep Δc0 σ Δ' → Δ' = Shape s_init s_init.
  Proof.
    intros [(c & w & Δ & Hin & _ & Hs) (Δs & HF & ->)].
    unfold Δc0, dpoint in Hin, HF. apply list_elem_of_singleton in Hin. simplify_eq.
    destruct (start_cstep _ _ Hs) as [-> _].
    inversion HF as [|x Δx l Δs' Hc HF']; subst. inversion HF'; subst.
    destruct Hc as [[_ Hc]|[[Hg|Hno] _]].
    - destruct (start_cstep _ _ Hc) as [_ ->]. unfold dsum. simpl. rewrite ?app_nil_r. done.
    - by apply not_good_Tbr in Hg.
    - exfalso. exact (Hno _ Hs).
  Qed.

  Lemma Inv_init : Inv s_init s_init.
  Proof. unfold Inv. split_and!; [done|by intros ?|by intros ?]. Qed.

  Lemma run_reach r : is_run Δc0 r → ∀ n, r n = Δc0 ∨ ∃ s0 s1, Inv s0 s1 ∧ r n = Shape s0 s1.
  Proof.
    intros [Hr0 Hr] n. induction n as [|n IH]; [by left|].
    destruct (Hr n) as [(σ & Hs)|[_ ->]]; [|done]. right.
    destruct IH as [E|(s0 & s1 & HI & E)]; rewrite E in Hs.
    - exists s_init, s_init. split; [apply Inv_init|]. by eapply start_step.
    - by eapply shape_step.
  Qed.

  (* A stable shape has a successful branch. *)
  Lemma ttrans_not_good b σ s s' : ttrans b σ s s' → ¬ conf_good (pc b s, tc b s).
  Proof. intros Ht (ch & ->)%good_shape. inversion Ht. Qed.

  Lemma shape_move0 s0 s1 σ s' : ttrans true σ s0 s' → dmoves (Shape s0 s1) σ.
  Proof.
    intros Ht. eexists _, _, _. split_and!; [by left|apply (ttrans_not_good _ _ _ _ Ht)|].
    apply (ttrans_cstep _ _ _ _ _ Ht).
  Qed.

  Lemma shape_move1 s0 s1 σ s' : ttrans false σ s1 s' → dmoves (Shape s0 s1) σ.
  Proof.
    intros Ht. eexists _, _, _. split_and!; [by right; left|apply (ttrans_not_good _ _ _ _ Ht)|].
    apply (ttrans_cstep _ _ _ _ _ Ht).
  Qed.

  Lemma shape_stable s0 s1 :
    Inv s0 s1 → dstable (Shape s0 s1) →
    (∃ ch, s0 = (true, ch, true)) ∨ (∃ ch, s1 = (true, ch, true)).
  Proof.
    destruct s0 as [[cd ch] d0], s1 as [[cd1 ch1] d1].
    intros (E & Hw0 & Hw1) Hst. simpl in E. injection E as <- <-. simpl in Hw0, Hw1.
    destruct cd.
    - destruct ch as [[]|].
      + destruct d0; [left; eauto|]. exfalso. apply (Hst (SPair 4 11)).
        eapply shape_move0. by constructor.
      + destruct d1; [right; eauto|]. exfalso. apply (Hst (SPair 5 12)).
        eapply shape_move1. by constructor.
      + assert (d0 = false) as -> by (destruct d0; [by destruct (Hw0 eq_refl)|done]).
        exfalso. apply (Hst (STag 2)). eapply shape_move0. constructor.
    - assert (d0 = false) as -> by (destruct d0; [by destruct (Hw0 eq_refl)|done]).
      exfalso. apply (Hst (SPair 1 10)). eapply shape_move0. constructor.
  Qed.

  Lemma lt_le_W a b c : a <ₚ b → W_le b c → a <ₚ c.
  Proof.
    intros [Hab Hba] Hbc. split; [by etrans|]. intros Hca. apply Hba. by etrans.
  Qed.

  Lemma le_add_l' a b : W_le a (W_add a b).
  Proof.
    rewrite <- (W_add_zero a) at 1. rewrite (W_add_comm W_zero a), (W_add_comm a b).
    rewrite (W_add_comm b a). rewrite !(W_add_comm a). apply W_add_mono, W_zero_le.
  Qed.

  Lemma le_add_r' a b : W_le b (W_add a b).
  Proof. rewrite W_add_comm. apply le_add_l'. Qed.

  Lemma succ_shape s0 s1 :
    (∃ ch, s0 = (true, ch, true)) ∨ (∃ ch, s1 = (true, ch, true)) →
    W_zero <ₚ (dmass_of conf_good (Shape s0 s1)).
  Proof.
    unfold Shape, dmass_of. cbn [foldr fst snd].
    intros [(ch & ->)|(ch & ->)].
    - rewrite decide_True by done. eapply lt_le_W; [apply (tr_pos true)|]. apply le_add_l'.
    - rewrite (decide_True (P := conf_good (pc false (true, ch, true), tc false (true, ch, true))))
        by done.
      case_decide; (eapply lt_le_W; [apply (tr_pos false)|]).
      + etrans; [apply le_add_l'|apply le_add_r'].
      + apply le_add_l'.
  Qed.

  Lemma corr_positive r : is_run Δc0 r → ∃ n, W_zero <ₚ (succ_mass r n).
  Proof.
    intros Hr.
    destruct (run_stable (csize (Pcorr, Tbr)) Δc0 r) as [n Hn]; [|done|].
    { intros x Hx. unfold Δc0, dpoint in Hx. by apply list_elem_of_singleton in Hx as ->. }
    exists n. destruct (run_reach r Hr n) as [E|(s0 & s1 & HI & E)]; unfold succ_mass; rewrite E in Hn |- *.
    - exfalso. apply (Hn (STag 0)). eexists _, _, _.
      split_and!; [by left|apply not_good_Tbr|apply start_cstep_ex].
    - by apply succ_shape, shape_stable.
  Qed.

  (* ** The two processes are not related by the Smyth must *)

  Theorem corr_not_below_anti : ¬ ((Pcorr, ρ) ⊑ₛₘ (Panti, ρ)).
  Proof.
    intros Hsm. destruct (Hsm Tbr r_anti r_anti_run) as (r1 & Hr1 & Hle).
    destruct (corr_positive r1 Hr1) as (n & Hn).
    destruct (W_dense _ _ Hn) as (w & Hw0 & Hw).
    destruct (Hle n w Hw) as (m & Hm). rewrite r_anti_zero in Hm.
    by destruct Hw0 as [_ Hw0].
  Qed.
End Example.
(* end hide *)
