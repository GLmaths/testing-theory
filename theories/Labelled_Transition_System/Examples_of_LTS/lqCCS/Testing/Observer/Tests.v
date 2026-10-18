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
From TestingTheory Require Import lqCCS.Testing.Observer.LTS.

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

Definition lαᴛᴇꜱᴛ (a : lact) : lfin :=
  match a with
  | LOut c _ | LIn c _ => FChan c
  | LOp E qs => FOp E qs
  | LMeas M qs _ => FMeas M qs
  end.

Definition lαᴘʀᴏ (f : lfin) : lpre :=
  match f with FChan c => PChan c | FOp _ _ => POpAll | FMeas _ _ => PMeasAll end.

(* The observer's side: an observer that can receive a value, or accept an
    outcome, can receive or accept any other one. *)
Lemma obs_abs_test (t : proc) (β β' : lact) :
  blocking β → blocking β' → lαᴛᴇꜱᴛ β = lαᴛᴇꜱᴛ β' → β ∈ R t → β' ∈ R t.
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
  Lemma gen_guard_step 𝜆0 P0 Q :
    tstep (PG (GSum (GPre 𝜆0 P0) tau_succ)) τ Q → Q = succP ∨ ∃ t, 𝜆0 = PTau t ∨ ∃ t', 𝜆0 = PTauPair t t'.
  Proof.
    intros Hs. apply succ_spec in Hs. simpl in Hs. apply elem_of_app in Hs as [Hs|Hs].
    - right. destruct 𝜆0; simpl in Hs; try set_solver; eauto.
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
  tstep (PG (sumg l)) (ActExt μ) Q → lαᴘʀᴏ (lαᴛᴇꜱᴛ μ) ∈ l ∧ ¬ is_out μ ∧ Q = succP.
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

Lemma sumg_step_ex l p : p ∈ l → ∃ μ, lαᴘʀᴏ (lαᴛᴇꜱᴛ μ) = p ∧ tstep (PG (sumg l)) (ActExt μ) succP.
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
  Completeness.test_co_acceptance_set_spec ta (λ x, lαᴘʀᴏ (lαᴛᴇꜱᴛ x)).
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

    [abs_prog_core]: what a process accepts is, up to [lαᴘʀᴏ], closed under the
    abstraction, as soon as it accepts every operation, and every
    measurement once it accepts one. *)

Lemma abs_prog_core {X} {GL : @gLts X lact lact_ExtAction} (x : X)
  (Hop : ∀ E qs, x ⟶[LOp E qs])
  (Hm : (∃ M qs n, x ⟶[LMeas M qs n]) → ∀ M qs, ∃ n, x ⟶[LMeas M qs n])
  (β β' : lact) :
  ¬ is_out β' → lαᴘʀᴏ (lαᴛᴇꜱᴛ β) = lαᴘʀᴏ (lαᴛᴇꜱᴛ β') →
  (∃ μ', (∃ μ2, x ⟶[μ2] ∧ μ' = lco μ2 ∧ ¬ is_out μ') ∧ lαᴛᴇꜱᴛ β = lαᴛᴇꜱᴛ μ') →
  (∃ μ', (∃ μ2, x ⟶[μ2] ∧ μ' = lco μ2 ∧ ¬ is_out μ') ∧ lαᴛᴇꜱᴛ β' = lαᴛᴇꜱᴛ μ').
Proof.
  intros hb' heq (μ' & (μ2 & Hacc & -> & Hb) & Hαᴛᴇꜱᴛ).
  destruct β' as [c v|c v|E qs|M qs n].
  - exfalso. by apply hb'.
  - exists (lco μ2). split; [eauto|]. rewrite <- Hαᴛᴇꜱᴛ.
    destruct β; simpl in heq |- *; congruence.
  - exists (LOp E qs). split; [|done].
    exists (LOp E qs). split_and!; [apply Hop|done|by intros ?].
  - destruct β as [| | |M0 qs0 n0]; simpl in heq; try discriminate.
    destruct μ2 as [| | |M1 qs1 n1]; simpl in Hαᴛᴇꜱᴛ; try discriminate.
    destruct (Hm (ex_intro _ M1 (ex_intro _ qs1 (ex_intro _ n1 Hacc))) M qs) as (n2 & Hn2).
    exists (LMeas M qs n2). split; [|done].
    exists (LMeas M qs n2). split_and!; [done|done|by intros ?].
Qed.
(* end hide *)
