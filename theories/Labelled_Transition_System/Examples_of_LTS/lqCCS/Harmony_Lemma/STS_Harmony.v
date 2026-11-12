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
(* * The Harmony lemma of lqCCS with memory

    The reduction semantics [sts] of configurations [⟨ρ, P⟩ ⟶[s] ⟨ρ', P'⟩],
    indexed by the choice [s], as the STS of VACCS
    ([VACCS.Harmony_Lemma.Harmony]): communication, silent prefix, quantum
    operation, measurement, initialisation, recursion, under parallel
    composition, restriction and structural congruence.  [sts_lab] is the
    same relation with the redex recorded, [κ]: the outcome of a measurement
    ([MMeas M q̃ m]) or nothing ([MNone]), as the labels of the transitions
    of Unruh, Valiron and Ying (Table 3); it serves the correspondence with
    the denotational semantics ([lqCCS.Harmony_Lemma.Denotational_Harmony]).

    The Harmony lemma is proved at the level of the program LTS: a step of
    the program with its effect on the memory ([mstep], the rule Sync of the
    composition memory ∣ program) is a reduction, and conversely up to
    congruence.  The proof follows VACCS: the shape lemmas
    [TransitionShapeForOutput], [TransitionShapeForInput] and
    [TransitionShapeForGuard] bring the redex of a transition to the top,
    under iterated restrictions [Ѵ n] ([cgr_res_scope_n]); the converse uses
    the bisimulation [cgr_bisim].  [harmony] is the statement on
    configurations: [⟨ρ, P⟩ ⟶[s, κ] ⟨ρ', Q⟩] for some [κ] iff
    [⟨ρ, P⟩ -τ->_s ⟨ρ', Q'⟩] for some [Q' ≡* Q]. *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list sets relations.
From TestingTheory Require Import ActTau.
From TestingTheory Require Import lqCCS.Harmony_Lemma.Lifted lqCCS.Harmony_Lemma.Paths lqCCS.Harmony_Lemma.States lqCCS.Language.Quantum.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.LTS.
From TestingTheory Require Import lqCCS.Language.Congruence lqCCS.Harmony_Lemma.Memory_Harmony.

#[local] Open Scope lqccs_scope.

(* ** Iterated restrictions and shifts *)

Fixpoint Ѵ (n : nat) (P : proc) : proc :=
  match n with 0 => P | S n => ν (Ѵ n P) end.

Fixpoint liftn (n : nat) (f : nat → nat) : nat → nat :=
  match n with 0 => f | S n => liftn n (lift f) end.

Lemma liftn_add n : ∀ f i, liftn n f (n + i) = n + f i.
Proof.
  induction n; intros f i; simpl; [done|].
  replace (S (n + i)) with (n + S i) by lia. rewrite IHn. simpl. lia.
Qed.

Lemma ren_chan_add_0 c : ren_chan (Nat.add 0) c = c.
Proof. by destruct c. Qed.

Lemma ren_chan_add_S n c : ren_chan (Nat.add n) (ren_chan S c) = ren_chan (Nat.add (S n)) c.
Proof. rewrite ren_chan_comp. apply ren_chan_ext. intros i. simpl. lia. Qed.

Lemma ren_chan_liftn f m c :
  ren_chan (liftn m f) (ren_chan (Nat.add m) c) = ren_chan (Nat.add m) (ren_chan f c).
Proof. rewrite !ren_chan_comp. apply ren_chan_ext. intros i. simpl. by rewrite liftn_add. Qed.

Lemma ren_add_S n P : ren (Nat.add n) (ren S P) = ren (Nat.add (S n)) P.
Proof. rewrite ren_comp. apply ren_ext. intros i. simpl. lia. Qed.

Lemma ren_lbl_add_S n l : ren_lbl (Nat.add n) (ren_lbl S l) = ren_lbl (Nat.add (S n)) l.
Proof. rewrite ren_lbl_comp. apply ren_lbl_ext_fun. intros i. simpl. lia. Qed.

Lemma ren_lbl_add_0 l : ren_lbl (Nat.add 0) l = l.
Proof. destruct l as [[c v|c v| | |]|]; simpl; by rewrite ?ren_chan_add_0. Qed.

Lemma ren_resn f n P : ren f (Ѵ n P) = Ѵ n (ren (liftn n f) P).
Proof. revert f. induction n; intros f; simpl; [done|]. by rewrite IHn. Qed.

Lemma cgr_resn n P Q : P ≡* Q → Ѵ n P ≡* Ѵ n Q.
Proof. intros H. induction n; simpl; [done|]. by apply cgr_res. Qed.

(* [(Ѵ n P) ∥ Q ≡ Ѵ n (P ∥ Q⁺ⁿ)] *)
Lemma cgr_res_scope_n n P Q : (Ѵ n P) ∥ Q ≡* Ѵ n (P ∥ ren (Nat.add n) Q).
Proof.
  revert Q. induction n; intros Q; simpl.
  - rewrite <- (ren_id Q) at 1. apply cgr_par_r, cgr_ren. done.
  - etrans; [apply cgr_of_cs, cs_res_scope|]. apply cgr_res.
    etrans; [apply IHn|]. apply cgr_resn, cgr_par_r. by rewrite ren_add_S.
Qed.

(* ** The shapes of the transitions *)

Lemma gstep_in_shape g s c v Q' :
  prog_gstep g s (ActExt (PrIn c v)) Q' →
  ∃ t P K, s = CTag t ∧ gcgr g ((PRecv t c ∙ P) ⊕ K) ∧ Q' = P ⟦ v ⟧.
Proof.
  intros Hs. remember (ActExt (PrIn c v)) as l eqn:El.
  induction Hs; simplify_eq.
  - exists t, P, (GNil []). split_and!; [done|apply rtsc_rl, gcs_sum_nil|done].
  - destruct (IHHs eq_refl) as (t & P & K & -> & Hg & ->).
    exists t, P, (K ⊕ g2). split_and!; [done| |done].
    etrans; [by apply gcgr_sum_l|]. apply rtsc_rl, gcs_sum_assoc.
  - destruct (IHHs eq_refl) as (t & P & K & -> & Hg & ->).
    exists t, P, (K ⊕ g1). split_and!; [done| |done].
    etrans; [apply gcgr_of_gcs, gcs_sum_comm|].
    etrans; [by apply gcgr_sum_l|]. apply rtsc_rl, gcs_sum_assoc.
Qed.

Lemma TransitionShapeForOutput P s c v Q :
  prog_step P s (ActExt (PrOut c v)) Q →
  ∃ t e R n, eval e = Some v ∧ s = CTag t
    ∧ P ≡* Ѵ n (PSend t (ren_chan (Nat.add n) c) e ∥ R) ∧ Q ≡* Ѵ n (𝟘 ∥ R).
Proof.
  intros Hs. remember (ActExt (PrOut c v)) as l eqn:El. revert c v El.
  induction Hs; intros c0 v0 El; simplify_eq.
  - exfalso. by eapply prog_gstep_not_out.
  - exists t, e, 𝟘, 0. split_and!; [done|done| |].
    + simpl. rewrite ren_chan_add_0. apply rtsc_rl, cs_par_nil.
    + simpl. apply rtsc_rl, cs_par_nil.
  - destruct (IHHs _ _ eq_refl) as (t & e' & R & n & He' & -> & HP & HQ).
    exists t, e', R, n. split_and!; [done|done| |done].
    etrans; [|exact HP]. apply cgr_of_cs. by apply cs_ite_t.
  - destruct (IHHs _ _ eq_refl) as (t & e' & R & n & He' & -> & HP & HQ).
    exists t, e', R, n. split_and!; [done|done| |done].
    etrans; [|exact HP]. apply cgr_of_cs. by apply cs_ite_f.
  - destruct (IHHs _ _ eq_refl) as (t & e & R & n & He & -> & HP & HQ).
    exists t, e, (R ∥ ren (Nat.add n) Q), n. split_and!; [done|done| |].
    + etrans; [by apply cgr_par_l|]. etrans; [apply cgr_res_scope_n|].
      apply cgr_resn, rtsc_rl, cs_par_assoc.
    + etrans; [by apply cgr_par_l|]. etrans; [apply cgr_res_scope_n|].
      apply cgr_resn, rtsc_rl, cs_par_assoc.
  - destruct (IHHs _ _ eq_refl) as (t & e & R & n & He & -> & HP & HQ).
    exists t, e, (R ∥ ren (Nat.add n) P), n. split_and!; [done|done| |].
    + etrans; [apply cgr_of_cs, cs_par_comm|].
      etrans; [by apply cgr_par_l|]. etrans; [apply cgr_res_scope_n|].
      apply cgr_resn, rtsc_rl, cs_par_assoc.
    + etrans; [apply cgr_of_cs, cs_par_comm|].
      etrans; [by apply cgr_par_l|]. etrans; [apply cgr_res_scope_n|].
      apply cgr_resn, rtsc_rl, cs_par_assoc.
  - destruct (IHHs _ _ eq_refl) as (t & e & R & n & He & -> & HP & HQ).
    exists t, e, R, (S n). split_and!; [done|done| |].
    + apply cgr_res. rewrite <- ren_chan_add_S. exact HP.
    + by apply cgr_res.
Qed.

Lemma TransitionShapeForInput P s c v Q :
  prog_step P s (ActExt (PrIn c v)) Q →
  ∃ t P1 K R n, s = CTag t
    ∧ P ≡* Ѵ n (PG ((PRecv t (ren_chan (Nat.add n) c) ∙ P1) ⊕ K) ∥ R)
    ∧ Q ≡* Ѵ n (P1 ⟦ v ⟧ ∥ R).
Proof.
  intros Hs. remember (ActExt (PrIn c v)) as l eqn:El. revert c v El.
  induction Hs; intros c0 v0 El; simplify_eq.
  - destruct (gstep_in_shape _ _ _ _ _ H) as (t & P1 & K & -> & Hg & ->).
    exists t, P1, K, 𝟘, 0. split_and!; [done| |].
    + simpl. rewrite ren_chan_add_0. etrans; [by apply cgr_guard|]. apply rtsc_rl, cs_par_nil.
    + simpl. apply rtsc_rl, cs_par_nil.
  - destruct (IHHs _ _ eq_refl) as (t & P1 & K & R & n & -> & HP & HQ).
    exists t, P1, K, R, n. split_and!; [done| |done].
    etrans; [|exact HP]. apply cgr_of_cs. by apply cs_ite_t.
  - destruct (IHHs _ _ eq_refl) as (t & P1 & K & R & n & -> & HP & HQ).
    exists t, P1, K, R, n. split_and!; [done| |done].
    etrans; [|exact HP]. apply cgr_of_cs. by apply cs_ite_f.
  - destruct (IHHs _ _ eq_refl) as (t & P1 & K & R & n & -> & HP & HQ).
    exists t, P1, K, (R ∥ ren (Nat.add n) Q), n. split_and!; [done| |].
    + etrans; [by apply cgr_par_l|]. etrans; [apply cgr_res_scope_n|].
      apply cgr_resn, rtsc_rl, cs_par_assoc.
    + etrans; [by apply cgr_par_l|]. etrans; [apply cgr_res_scope_n|].
      apply cgr_resn, rtsc_rl, cs_par_assoc.
  - destruct (IHHs _ _ eq_refl) as (t & P1 & K & R & n & -> & HP & HQ).
    exists t, P1, K, (R ∥ ren (Nat.add n) P), n. split_and!; [done| |].
    + etrans; [apply cgr_of_cs, cs_par_comm|].
      etrans; [by apply cgr_par_l|]. etrans; [apply cgr_res_scope_n|].
      apply cgr_resn, rtsc_rl, cs_par_assoc.
    + etrans; [apply cgr_of_cs, cs_par_comm|].
      etrans; [by apply cgr_par_l|]. etrans; [apply cgr_res_scope_n|].
      apply cgr_resn, rtsc_rl, cs_par_assoc.
  - destruct (IHHs _ _ eq_refl) as (t & P1 & K & R & n & -> & HP & HQ).
    exists t, P1, K, R, (S n). split_and!; [done| |].
    + apply cgr_res. rewrite <- ren_chan_add_S. exact HP.
    + by apply cgr_res.
Qed.

(* ** Sums: the guard that moves can be brought in front *)

Lemma TransitionShapeForGuard g s l P' :
  prog_gstep g s l P' →
  ∃ 𝜆 Q K, gcgr g ((𝜆 ∙ Q) ⊕ K) ∧ prog_gstep (𝜆 ∙ Q) s l P'.
Proof.
  induction 1 as [t P | t c v P | t E es qs P Hq | t M es qs n P Hq | t es qs P Hq
                 | g1 g2 s l P' Hg IH | g1 g2 s l P' Hg IH].
  - exists (PTau t), P, (GNil []). split; [apply rtsc_rl, gcs_sum_nil|constructor].
  - exists (PRecv t c), P, (GNil []). split; [apply rtsc_rl, gcs_sum_nil|constructor].
  - exists (POp t E es), P, (GNil []). split; [apply rtsc_rl, gcs_sum_nil|by constructor].
  - exists (PMeas t M es), P, (GNil []). split; [apply rtsc_rl, gcs_sum_nil|by constructor].
  - exists (PInit t es), P, (GNil []). split; [apply rtsc_rl, gcs_sum_nil|by constructor].
  - destruct IH as (𝜆 & Q & K & Hc & Hs).
    exists 𝜆, Q, (K ⊕ g2). split; [|done].
    etrans; [by apply gcgr_sum_l|]. apply rtsc_rl, gcs_sum_assoc.
  - destruct IH as (𝜆 & Q & K & Hc & Hs).
    exists 𝜆, Q, (K ⊕ g1). split; [|done].
    etrans; [apply gcgr_of_gcs, gcs_sum_comm|].
    etrans; [by apply gcgr_sum_l|]. apply rtsc_rl, gcs_sum_assoc.
Qed.

(* ** Labels of the reductions: the outcome of a measurement, or nothing *)

Inductive mlabel : Type :=
| MNone
| MMeas (M : meas) (qs : list qubit) (n : nat).

Section STS.
  Context `{QM : QuantumModel}.

  (* ** The effect of an internal action on the memory

      [mem_eff ρ l ρ' κ]: the action [l] of a program (a silent move, or a
      request to the memory) takes the memory from [ρ] to [ρ'], with label
      [κ].  Channel actions have no effect: they are not internal. *)
  Inductive mem_eff (ρ : St) : Labels prog_action → St → mlabel → Prop :=
  | me_tau : mem_eff ρ τ ρ MNone
  | me_opl E qs : mem_eff ρ (ActExt (PrOp E qs)) (sop_apply E qs ρ) MNone
  | me_initl qs : mem_eff ρ (ActExt (PrInit qs)) (init_apply qs ρ) MNone
  | me_measl M qs (k : Out (meas_of M qs)) :
      mem_eff ρ (ActExt (PrMeas M qs (code _ k))) (meas_branch M qs k ρ) (MMeas M qs (code _ k)).

  (* A step of the program with its effect on the memory. *)
  Definition mstep (ρ : St) (P : proc) (s : choice) (κ : mlabel) (ρ' : St) (P' : proc) : Prop :=
    ∃ l, prog_step P s l P' ∧ mem_eff ρ l ρ' κ.

  Lemma mem_eff_ren ρ l ρ' κ f : mem_eff ρ l ρ' κ → ren_lbl f l = l.
  Proof. by destruct 1. Qed.

  Lemma mem_eff_mem_step ρ l ρ' κ :
    mem_eff ρ l ρ' κ →
    (l = τ ∧ ρ' = ρ) ∨ (∃ a b, l = ActExt a ∧ mem_step ρ CEps (ActExt b) ρ' ∧ sync b a).
  Proof.
    destruct 1; [by left|right..].
    - exists (PrOp E qs), (MeOp E qs). split_and!; [done|constructor|constructor].
    - exists (PrInit qs), (MeInit qs). split_and!; [done|constructor|constructor].
    - exists (PrMeas M qs (code _ k)), (MeMeas M qs (code _ k)).
      split_and!; [done|constructor|constructor].
  Qed.

  Lemma mem_step_mem_eff ρ a b ρ' :
    mem_step ρ CEps (ActExt b) ρ' → sync b a → ∃ κ, mem_eff ρ (ActExt a) ρ' κ.
  Proof.
    intros Hm Hs. inversion Hs; subst; inversion Hm; subst; eexists; constructor.
  Qed.

  (* ** The reduction semantics *)

  Inductive sts : St → proc → choice → St → proc → Prop :=
  | sts_com ρ t c e v t' P K :
      eval e = Some v →
      sts ρ (PSend t c e ∥ PG ((PRecv t' c ∙ P) ⊕ K)) (cpair t t') ρ (𝟘 ∥ P ⟦ v ⟧)
  | sts_tau ρ t P K :
      sts ρ (PG ((PTau t ∙ P) ⊕ K)) (CTag t) ρ P
  | sts_op ρ t E es qs P K :
      eval_qubits es = Some qs →
      sts ρ (PG ((POp t E es ∙ P) ⊕ K)) (CTag t) (sop_apply E qs ρ) P
  | sts_init ρ t es qs P K :
      eval_qubits es = Some qs →
      sts ρ (PG ((PInit t es ∙ P) ⊕ K)) (CTag t) (init_apply qs ρ) P
  | sts_meas ρ t M es qs (k : Out (meas_of M qs)) P K :
      eval_qubits es = Some qs →
      sts ρ (PG ((PMeas t M es ∙ P) ⊕ K)) (CTag t) (meas_branch M qs k ρ) (P ⟦ VNat (code _ k) ⟧)
  | sts_rec ρ t X P :
      sts ρ (PRec t X P) (CTag t) ρ (P ⦃ PRec t X P // X ⦄)
  | sts_par ρ P s ρ' P' Q :
      sts ρ P s ρ' P' → sts ρ (P ∥ Q) s ρ' (P' ∥ Q)
  | sts_res ρ P s ρ' P' :
      sts ρ P s ρ' P' → sts ρ (ν P) s ρ' (ν P')
  | sts_cong ρ P P1 s ρ' Q1 Q :
      P ≡* P1 → sts ρ P1 s ρ' Q1 → Q1 ≡* Q → sts ρ P s ρ' Q.

  (* The same reductions, with the redex recorded. *)
  Inductive sts_lab : St → proc → choice → mlabel → St → proc → Prop :=
  | sl_com ρ t c e v t' P K :
      eval e = Some v →
      sts_lab ρ (PSend t c e ∥ PG ((PRecv t' c ∙ P) ⊕ K)) (cpair t t') MNone ρ (𝟘 ∥ P ⟦ v ⟧)
  | sl_tau ρ t P K :
      sts_lab ρ (PG ((PTau t ∙ P) ⊕ K)) (CTag t) MNone ρ P
  | sl_op ρ t E es qs P K :
      eval_qubits es = Some qs →
      sts_lab ρ (PG ((POp t E es ∙ P) ⊕ K)) (CTag t) MNone (sop_apply E qs ρ) P
  | sl_init ρ t es qs P K :
      eval_qubits es = Some qs →
      sts_lab ρ (PG ((PInit t es ∙ P) ⊕ K)) (CTag t) MNone (init_apply qs ρ) P
  | sl_meas ρ t M es qs (k : Out (meas_of M qs)) P K :
      eval_qubits es = Some qs →
      sts_lab ρ (PG ((PMeas t M es ∙ P) ⊕ K)) (CTag t) (MMeas M qs (code _ k))
        (meas_branch M qs k ρ) (P ⟦ VNat (code _ k) ⟧)
  | sl_rec ρ t X P :
      sts_lab ρ (PRec t X P) (CTag t) MNone ρ (P ⦃ PRec t X P // X ⦄)
  | sl_par ρ P s κ ρ' P' Q :
      sts_lab ρ P s κ ρ' P' → sts_lab ρ (P ∥ Q) s κ ρ' (P' ∥ Q)
  | sl_res ρ P s κ ρ' P' :
      sts_lab ρ P s κ ρ' P' → sts_lab ρ (ν P) s κ ρ' (ν P')
  | sl_cong ρ P P1 s κ ρ' Q1 Q :
      P ≡* P1 → sts_lab ρ P1 s κ ρ' Q1 → Q1 ≡* Q → sts_lab ρ P s κ ρ' Q.

  Lemma sts_lab_sts ρ P s κ ρ' P' : sts_lab ρ P s κ ρ' P' → sts ρ P s ρ' P'.
  Proof. induction 1; eauto using sts. Qed.

  Lemma sts_sts_lab ρ P s ρ' P' : sts ρ P s ρ' P' → ∃ κ, sts_lab ρ P s κ ρ' P'.
  Proof.
    induction 1 as [| | | | | | ? ? ? ? ? ? _ (κ & Hs) | ? ? ? ? ? _ (κ & Hs)
                   | ? ? ? ? ? ? ? Hc _ (κ & Hs) Hc']; eexists; eauto using sts_lab.
  Qed.

  Lemma sts_resn n ρ P s κ ρ' P' : sts_lab ρ P s κ ρ' P' → sts_lab ρ (Ѵ n P) s κ ρ' (Ѵ n P').
  Proof. intros Hs. induction n; simpl; [done|]. by apply sl_res. Qed.

  (* ** From the LTS to the STS *)

  (* A communication between an output under [n] restrictions and an input
      under [m] restrictions: the restrictions are extruded one by one. *)
  Lemma Com_shapes ρ n :
    ∀ m c e v t t' P1 K R R', eval e = Some v →
    sts_lab ρ (Ѵ n (PSend t (ren_chan (Nat.add n) c) e ∥ R)
           ∥ Ѵ m (PG ((PRecv t' (ren_chan (Nat.add m) c) ∙ P1) ⊕ K) ∥ R'))
        (cpair t t') MNone ρ (Ѵ n (𝟘 ∥ R) ∥ Ѵ m (P1 ⟦ v ⟧ ∥ R')).
  Proof.
    induction n as [|n IHn]; intros m.
    - induction m as [|m IHm]; intros c e v t t' P1 K R R' He; cbn [Ѵ].
      + rewrite !ren_chan_add_0.
        eapply sl_cong; [apply cgr_par_inversion| |apply cgr_par_inversion].
        apply sl_par. by apply sl_com.
      + eapply sl_cong.
        * etrans; [apply cgr_of_cs, cs_par_comm|].
          etrans; [apply cgr_of_cs, cs_res_scope|]. apply cgr_res, cgr_of_cs, cs_par_comm.
        * apply sl_res. cbn [ren gren]. rewrite ren_chan_add_0.
          specialize (IHm (ren_chan S c) e v t t' P1 K (ren S R) R' He). cbn [Ѵ] in IHm.
          rewrite ren_chan_add_0, ren_chan_add_S in IHm. exact IHm.
        * etrans; [apply cgr_res, cgr_of_cs, cs_par_comm|].
          change (𝟘 ∥ ren S R) with (ren S (𝟘 ∥ R)).
          etrans; [apply rtsc_rl, cs_res_scope|]. apply cgr_of_cs, cs_par_comm.
    - intros c e v t t' P1 K R R' He. cbn [Ѵ].
      eapply sl_cong.
      + apply cgr_of_cs, cs_res_scope.
      + apply sl_res. rewrite ren_resn. cbn [ren gren prefix_ren].
        rewrite ren_chan_liftn, <- ren_chan_add_S.
        apply (IHn m (ren_chan S c) e v t t' (ren (liftn m S) P1) (gren (liftn m S) K) R
                 (ren (liftn m S) R') He).
      + rewrite <- (proj1 ren_subst).
        replace (Ѵ m (ren (liftn m S) (P1 ⟦ v ⟧) ∥ ren (liftn m S) R'))
          with (ren S (Ѵ m (P1 ⟦ v ⟧ ∥ R'))) by (rewrite ren_resn; done).
        apply rtsc_rl, cs_res_scope.
  Qed.

  (* A program step with its effect on the memory is a reduction. *)
  Lemma Internal_Implies_Reduction P s l P' :
    prog_step P s l P' → ∀ ρ ρ' κ, mem_eff ρ l ρ' κ → sts_lab ρ P s κ ρ' P'.
  Proof.
    induction 1 as [g s l P' Hg | t c e v He | e P Q s l P' He Hp IH | e P Q s l Q' He Hp IH
                   | P Q s l P' Hp IH | P Q s l Q' Hp IH
                   | P Q t t' c v P' Q' HpP _ HpQ _ | P Q t t' c v P' Q' HpP _ HpQ _
                   | P s l P' Hp IH | t X P]; intros ρ ρ' κ Hm.
    - destruct (TransitionShapeForGuard _ _ _ _ Hg) as (𝜆 & Q & K & Hcg & Hs).
      eapply sl_cong; [apply cgr_guard, Hcg| |reflexivity].
      inversion Hs; subst; inversion Hm; subst.
      + apply sl_tau.
      + by apply sl_op.
      + by apply sl_meas.
      + by apply sl_init.
    - inversion Hm.
    - eapply sl_cong; [apply cgr_of_cs; by apply cs_ite_t | by apply IH | reflexivity].
    - eapply sl_cong; [apply cgr_of_cs; by apply cs_ite_f | by apply IH | reflexivity].
    - apply sl_par. by apply IH.
    - eapply sl_cong; [apply cgr_of_cs, cs_par_comm | apply sl_par; by apply IH | apply cgr_of_cs, cs_par_comm].
    - inversion Hm; subst.
      destruct (TransitionShapeForOutput _ _ _ _ _ HpP) as (t0 & e & R & n & He & Et & HP1 & HP2).
      destruct (TransitionShapeForInput _ _ _ _ _ HpQ) as (t0' & P1 & K & R' & m & Et' & HQ1 & HQ2).
      simplify_eq.
      eapply sl_cong; [by apply cgr_par | by apply Com_shapes | symmetry; by apply cgr_par].
    - inversion Hm; subst.
      destruct (TransitionShapeForInput _ _ _ _ _ HpP) as (t0 & P1 & K & R & n & Et & HP1 & HP2).
      destruct (TransitionShapeForOutput _ _ _ _ _ HpQ) as (t0' & e & R' & m & He & Et' & HQ1 & HQ2).
      simplify_eq. rewrite cpair_comm.
      eapply sl_cong.
      + etrans; [apply cgr_of_cs, cs_par_comm|]. by apply cgr_par.
      + by apply Com_shapes.
      + etrans; [apply cgr_of_cs, cs_par_comm|]. symmetry. by apply cgr_par.
    - apply sl_res. apply IH. by rewrite (mem_eff_ren _ _ _ _ S Hm).
    - inversion Hm; subst. apply sl_rec.
  Qed.

  Lemma mstep_sts_lab ρ P s κ ρ' P' : mstep ρ P s κ ρ' P' → sts_lab ρ P s κ ρ' P'.
  Proof. intros (l & Hp & Hm). by eapply Internal_Implies_Reduction. Qed.

  Lemma mstep_sts ρ P s κ ρ' P' : mstep ρ P s κ ρ' P' → sts ρ P s ρ' P'.
  Proof. intros Hm. eapply sts_lab_sts, mstep_sts_lab, Hm. Qed.

  (* ** From the STS to the LTS *)

  (* The congruence is a simulation of the program steps with memory
      effect, with the same choice and label, up to congruence. *)
  Lemma mstep_cgr ρ P P1 s κ ρ' Q1 :
    P ≡* P1 → mstep ρ P1 s κ ρ' Q1 → ∃ Q, mstep ρ P s κ ρ' Q ∧ Q ≡* Q1.
  Proof.
    intros Hc (l & Hp & Hm). assert (Hf : fwd P1 P) by (apply cgr_bisim; by symmetry).
    destruct (Hf _ _ _ Hp) as (Q & Hq & HQ).
    exists Q. split; [by exists l | by symmetry].
  Qed.

  Lemma Reduction_Implies_Internal ρ P s κ ρ' Q :
    sts_lab ρ P s κ ρ' Q → ∃ Q', mstep ρ P s κ ρ' Q' ∧ Q' ≡* Q.
  Proof.
    induction 1 as [ρ t c e v t' P K He | ρ t P K | ρ t E es qs P K Hq | ρ t es qs P K Hq
                   | ρ t M es qs k P K Hq | ρ t X P
                   | ρ P s κ ρ' P' Q _ (P'' & (l & Hs & Hm) & HP)
                   | ρ P s κ ρ' P' _ (P'' & (l & Hs & Hm) & HP)
                   | ρ P P1 s κ ρ' Q1 Q Hc _ (Q1' & Hs & HQ) Hc'].
    - exists (𝟘 ∥ P ⟦ v ⟧). split; [|reflexivity]. exists τ. split; [|constructor].
      eapply pr_syncL; [by apply pr_send | apply pr_guard, pg_sumL, pg_recv].
    - exists P. split; [|reflexivity]. exists τ. split; [|constructor].
      apply pr_guard, pg_sumL, pg_tau.
    - exists P. split; [|reflexivity]. eexists. split; [|constructor].
      by apply pr_guard, pg_sumL, pg_op.
    - exists P. split; [|reflexivity]. eexists. split; [|constructor].
      by apply pr_guard, pg_sumL, pg_init.
    - exists (P ⟦ VNat (code _ k) ⟧). split; [|reflexivity]. eexists. split; [|constructor].
      by apply pr_guard, pg_sumL, pg_meas.
    - exists (P ⦃ PRec t X P // X ⦄). split; [|reflexivity]. exists τ. split; [|constructor].
      apply pr_rec.
    - exists (P'' ∥ Q). split; [|by apply cgr_par_l]. exists l. split; [by apply pr_parL | done].
    - exists (ν P''). split; [|by apply cgr_res]. exists l. split; [|done].
      apply pr_res. by rewrite (mem_eff_ren _ _ _ _ S Hm).
    - destruct (mstep_cgr _ _ _ _ _ _ _ Hc Hs) as (Q' & Hs' & HQ').
      exists Q'. split; [done|]. etrans; [exact HQ'|]. by etrans.
  Qed.

  Lemma Reduction_Implies_Internal_sts ρ P s ρ' Q :
    sts ρ P s ρ' Q → ∃ κ Q', mstep ρ P s κ ρ' Q' ∧ Q' ≡* Q.
  Proof.
    intros Hs. destruct (sts_sts_lab _ _ _ _ _ Hs) as (κ & Hl).
    destruct (Reduction_Implies_Internal _ _ _ _ _ _ Hl) as (Q' & Hm & HQ). eauto.
  Qed.

  (* ** The Harmony lemma, on the configuration LTS *)

  Lemma mstep_conf ρ P s κ ρ' P' : mstep ρ P s κ ρ' P' → conf_step ρ P s τ ρ' P'.
  Proof.
    intros (l & Hp & Hm).
    destruct (mem_eff_mem_step _ _ _ _ Hm) as [(-> & ->) | (a & b & -> & Hms & Hsy)].
    - by apply prog_step_tau_conf.
    - by eapply prog_step_mem_conf.
  Qed.

  Lemma conf_mstep ρ P s ρ' P' : conf_step ρ P s τ ρ' P' → ∃ κ, mstep ρ P s κ ρ' P'.
  Proof.
    intros Hc. destruct (conf_step_tau_inv _ _ _ _ _ Hc)
      as [(Hp & ->) | (t & a & b & -> & Hp & Hm & Hs)].
    - exists MNone, τ. split; [done|constructor].
    - destruct (mem_step_mem_eff _ _ _ _ Hm Hs) as (κ & He). exists κ, (ActExt a). done.
  Qed.

  Theorem harmony ρ P s ρ' Q :
    sts ρ P s ρ' Q ↔ ∃ Q', conf_step ρ P s τ ρ' Q' ∧ Q' ≡* Q.
  Proof.
    split.
    - intros Hs. destruct (Reduction_Implies_Internal_sts _ _ _ _ _ Hs) as (κ & Q' & Hm & HQ).
      exists Q'. split; [by eapply mstep_conf | done].
    - intros (Q' & Hc & HQ). destruct (conf_mstep _ _ _ _ _ Hc) as (κ & Hm).
      eapply sts_cong; [reflexivity | by eapply mstep_sts | exact HQ].
  Qed.

  Corollary harmony_par ρ P Q s ρ' R :
    sts ρ (P ∥ Q) s ρ' R ↔ ∃ R', conf_step ρ (P ∥ Q) s τ ρ' R' ∧ R' ≡* R.
  Proof. apply harmony. Qed.
End STS.

Notation "⟨ ρ , P ⟩ ⟶[ s ] ⟨ ρ' , P' ⟩" := (sts ρ P s ρ' P') (at level 70) : lqccs_scope.
Notation "⟨ ρ , P ⟩ ⟶[ s , κ ] ⟨ ρ' , P' ⟩" := (sts_lab ρ P s κ ρ' P') (at level 70) : lqccs_scope.
(* end hide *)
