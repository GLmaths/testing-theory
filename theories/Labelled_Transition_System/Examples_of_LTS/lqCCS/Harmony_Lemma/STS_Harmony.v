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
    composition, restriction and structural congruence.

    The Harmony lemma relates the reductions to the silent transitions of
    the composition memory ∣ program ([harmony_composition]).  The proof
    follows VACCS: the shape lemmas [TransitionShapeForOutput],
    [TransitionShapeForInput], [TransitionShapeForQuantum] and
    [TransitionShapeForGuard] bring the redex of a transition to the top,
    under iterated restrictions [Ѵ n] ([cgr_res_scope_n]).  A silent
    transition of the program is a reduction ([Taus_Implies_Reduction]), and
    so is a quantum action answered by the memory
    ([Quantum_Implies_Reduction]); the converse
    ([Reduction_Implies_Internal]) uses the bisimulation [cgr_bisim]. *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list sets relations.
From TestingTheory Require Import ActTau.
From TestingTheory Require Import lqCCS.Language.Algebra lqCCS.Language.Quantum.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.LTS.
From TestingTheory Require Import lqCCS.Language.Congruence lqCCS.Harmony_Lemma.Memory_Harmony.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

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
  - etrans; [apply cgr_res_scope_rev|]. apply cgr_res.
    etrans; [apply IHn|]. apply cgr_resn, cgr_par_r. by rewrite ren_add_S.
Qed.

(* ** The shapes of the transitions *)

Lemma gstep_in_shape (g : guard) s c v Q' :
  g ⟶{c ? v}[s] Q' →
  ∃ (t : tag) P K, s = t ∧ g ≡ᵍ* ((t ∶ c ? ∙ P) + K) ∧ Q' = P ⟦ v ⟧.
Proof.
  intros Hs. remember (c ? v) as l eqn:El.
  change (prog_gstep g s l Q') in Hs. induction Hs as [| | | | | ? ? ? ? ? ? IHHs | ? ? ? ? ? ? IHHs] using prog_gstep_ind; simplify_eq.
  - exists t, P, (GNil []). split_and!; [done|apply gcgr_choice_nil_rev|done].
  - destruct (IHHs eq_refl) as (t & P & K & -> & Hg & ->).
    exists t, P, (K + g2)%lq. split_and!; [done| |done].
    etrans; [by apply gcgr_choice|]. apply gcgr_choice_assoc.
  - destruct (IHHs eq_refl) as (t & P & K & -> & Hg & ->).
    exists t, P, (K + g1)%lq. split_and!; [done| |done].
    etrans; [apply gcgr_choice_com|].
    etrans; [by apply gcgr_choice|]. apply gcgr_choice_assoc.
Qed.

Lemma TransitionShapeForOutput P s c v Q :
  P ⟶{c ! v}[s] Q →
  ∃ (t : tag) e R n, eval e = Some v ∧ s = t
    ∧ P ≡* Ѵ n (t ∶ (ren_chan (Nat.add n) c) ! e ∥ R) ∧ Q ≡* Ѵ n (𝟘 ∥ R).
Proof.
  intros Hs. remember (c ! v) as l eqn:El. revert c v El.
  induction Hs as [? ? ? ? H | ? ? ? ? ? | ? ? ? ? ? ? ? ? IHHs | ? ? ? ? ? ? ? ? IHHs | ? ? ? ? ? ? IHHs | ? ? ? ? ? ? IHHs | ? ? ? ? ? ? ? ? ? IHHs1 ? IHHs2 | ? ? ? ? ? ? ? ? ? IHHs1 ? IHHs2 | ? ? ? ? ? IHHs | ? ? ?] using prog_step_guard_ind; intros c0 v0 El; simplify_eq.
  - exfalso. by eapply prog_gstep_not_out.
  - exists t, e, 𝟘, 0. split_and!; [done|done| |].
    + simpl. rewrite ren_chan_add_0. apply cgr_par_nil_rev.
    + simpl. apply cgr_par_nil_rev.
  - destruct (IHHs _ _ eq_refl) as (t & e' & R & n & He' & -> & HP & HQ).
    exists t, e', R, n. split_and!; [done|done| |done].
    etrans; [|exact HP]. by apply cgr_if_true.
  - destruct (IHHs _ _ eq_refl) as (t & e' & R & n & He' & -> & HP & HQ).
    exists t, e', R, n. split_and!; [done|done| |done].
    etrans; [|exact HP]. by apply cgr_if_false.
  - destruct (IHHs _ _ eq_refl) as (t & e & R & n & He & -> & HP & HQ).
    exists t, e, (R ∥ ren (Nat.add n) Q), n. split_and!; [done|done| |].
    + etrans; [by apply cgr_par|]. etrans; [apply cgr_res_scope_n|].
      apply cgr_resn, cgr_par_assoc.
    + etrans; [by apply cgr_par|]. etrans; [apply cgr_res_scope_n|].
      apply cgr_resn, cgr_par_assoc.
  - destruct (IHHs _ _ eq_refl) as (t & e & R & n & He & -> & HP & HQ).
    exists t, e, (R ∥ ren (Nat.add n) P), n. split_and!; [done|done| |].
    + etrans; [apply cgr_par_com|].
      etrans; [by apply cgr_par|]. etrans; [apply cgr_res_scope_n|].
      apply cgr_resn, cgr_par_assoc.
    + etrans; [apply cgr_par_com|].
      etrans; [by apply cgr_par|]. etrans; [apply cgr_res_scope_n|].
      apply cgr_resn, cgr_par_assoc.
  - destruct (IHHs _ _ eq_refl) as (t & e & R & n & He & -> & HP & HQ).
    exists t, e, R, (S n). split_and!; [done|done| |].
    + apply cgr_res. rewrite <- ren_chan_add_S. exact HP.
    + by apply cgr_res.
Qed.

Lemma TransitionShapeForInput P s c v Q :
  P ⟶{c ? v}[s] Q →
  ∃ (t : tag) P1 K R n, s = t
    ∧ P ≡* Ѵ n (((t ∶ (ren_chan (Nat.add n) c) ? ∙ P1) + K) ∥ R)
    ∧ Q ≡* Ѵ n (P1 ⟦ v ⟧ ∥ R).
Proof.
  intros Hs. remember (c ? v) as l eqn:El. revert c v El.
  induction Hs as [? ? ? ? H | ? ? ? ? ? | ? ? ? ? ? ? ? ? IHHs | ? ? ? ? ? ? ? ? IHHs | ? ? ? ? ? ? IHHs | ? ? ? ? ? ? IHHs | ? ? ? ? ? ? ? ? ? IHHs1 ? IHHs2 | ? ? ? ? ? ? ? ? ? IHHs1 ? IHHs2 | ? ? ? ? ? IHHs | ? ? ?] using prog_step_guard_ind; intros c0 v0 El; simplify_eq.
  - destruct (gstep_in_shape _ _ _ _ _ H) as (t & P1 & K & -> & Hg & ->).
    exists t, P1, K, 𝟘, 0. split_and!; [done| |].
    + simpl. rewrite ren_chan_add_0. etrans; [by apply cgr_guard|]. apply cgr_par_nil_rev.
    + simpl. apply cgr_par_nil_rev.
  - destruct (IHHs _ _ eq_refl) as (t & P1 & K & R & n & -> & HP & HQ).
    exists t, P1, K, R, n. split_and!; [done| |done].
    etrans; [|exact HP]. by apply cgr_if_true.
  - destruct (IHHs _ _ eq_refl) as (t & P1 & K & R & n & -> & HP & HQ).
    exists t, P1, K, R, n. split_and!; [done| |done].
    etrans; [|exact HP]. by apply cgr_if_false.
  - destruct (IHHs _ _ eq_refl) as (t & P1 & K & R & n & -> & HP & HQ).
    exists t, P1, K, (R ∥ ren (Nat.add n) Q), n. split_and!; [done| |].
    + etrans; [by apply cgr_par|]. etrans; [apply cgr_res_scope_n|].
      apply cgr_resn, cgr_par_assoc.
    + etrans; [by apply cgr_par|]. etrans; [apply cgr_res_scope_n|].
      apply cgr_resn, cgr_par_assoc.
  - destruct (IHHs _ _ eq_refl) as (t & P1 & K & R & n & -> & HP & HQ).
    exists t, P1, K, (R ∥ ren (Nat.add n) P), n. split_and!; [done| |].
    + etrans; [apply cgr_par_com|].
      etrans; [by apply cgr_par|]. etrans; [apply cgr_res_scope_n|].
      apply cgr_resn, cgr_par_assoc.
    + etrans; [apply cgr_par_com|].
      etrans; [by apply cgr_par|]. etrans; [apply cgr_res_scope_n|].
      apply cgr_resn, cgr_par_assoc.
  - destruct (IHHs _ _ eq_refl) as (t & P1 & K & R & n & -> & HP & HQ).
    exists t, P1, K, R, (S n). split_and!; [done| |].
    + apply cgr_res. rewrite <- ren_chan_add_S. exact HP.
    + by apply cgr_res.
Qed.

(* ** Sums: the guard that moves can be brought in front *)

Lemma TransitionShapeForGuard (g : guard) s l P' :
  g ⟶{l}[s] P' →
  ∃ 𝜆 Q K, g ≡ᵍ* ((𝜆 ∙ Q) + K) ∧ (𝜆 ∙ Q) ⟶{l}[s] P'.
Proof.
  intros Hs0. change (prog_gstep g s l P') in Hs0. induction Hs0 as [t P | t c v P | t E es qs P Hq | t M es qs n P Hq | t es qs P Hq
                 | g1 g2 s l P' Hg IH | g1 g2 s l P' Hg IH] using prog_gstep_ind.
  - exists (t ∶ 𝛕), P, (GNil []). split; [apply gcgr_choice_nil_rev|constructor].
  - exists (t ∶ c ?), P, (GNil []). split; [apply gcgr_choice_nil_rev|constructor].
  - exists (t ∶ E ⦅es⦆), P, (GNil []). split; [apply gcgr_choice_nil_rev|by constructor].
  - exists (t ∶ M ⦅es ▷⦆), P, (GNil []). split; [apply gcgr_choice_nil_rev|by constructor].
  - exists (t ∶ init ⦅es⦆), P, (GNil []). split; [apply gcgr_choice_nil_rev|by constructor].
  - destruct IH as (𝜆 & Q & K & Hc & Hs).
    exists 𝜆, Q, (K + g2)%lq. split; [|done].
    etrans; [by apply gcgr_choice|]. apply gcgr_choice_assoc.
  - destruct IH as (𝜆 & Q & K & Hc & Hs).
    exists 𝜆, Q, (K + g1)%lq. split; [|done].
    etrans; [apply gcgr_choice_com|].
    etrans; [by apply gcgr_choice|]. apply gcgr_choice_assoc.
Qed.

Definition quant_action (a : prog_action) : Prop :=
  match a with PrOut _ _ | PrIn _ _ => False | _ => True end.

Lemma TransitionShapeForQuantum P s a Q :
  quant_action a → P ⟶{ActExt a}[s] Q →
  ∃ 𝜆 P1 K R n Q1, P ≡* Ѵ n (((𝜆 ∙ P1) + K) ∥ R)
    ∧ (𝜆 ∙ P1) ⟶{ActExt a}[s] Q1 ∧ Q ≡* Ѵ n (Q1 ∥ R).
Proof.
  intros Ha Hs. remember (ActExt a) as l eqn:El. revert a Ha El.
  induction Hs as [? ? ? ? H | ? ? ? ? ? | ? ? ? ? ? ? ? ? IHHs | ? ? ? ? ? ? ? ? IHHs | ? ? ? ? ? ? IHHs | ? ? ? ? ? ? IHHs | ? ? ? ? ? ? ? ? ? IHHs1 ? IHHs2 | ? ? ? ? ? ? ? ? ? IHHs1 ? IHHs2 | ? ? ? ? ? IHHs | ? ? ?] using prog_step_guard_ind; intros a0 Ha El; simplify_eq.
  - destruct (TransitionShapeForGuard _ _ _ _ H) as (𝜆 & Q0 & K & Hg & Hs0).
    exists 𝜆, Q0, K, 𝟘, 0, P'. split_and!; [|done|].
    + simpl. etrans; [by apply cgr_guard|]. apply cgr_par_nil_rev.
    + simpl. apply cgr_par_nil_rev.
  - done.
  - destruct (IHHs _ Ha eq_refl) as (𝜆 & P1 & K & R & n & Q1 & HP & Hg & HQ).
    exists 𝜆, P1, K, R, n, Q1. split_and!; [|done|done].
    etrans; [|exact HP]. by apply cgr_if_true.
  - destruct (IHHs _ Ha eq_refl) as (𝜆 & P1 & K & R & n & Q1 & HP & Hg & HQ).
    exists 𝜆, P1, K, R, n, Q1. split_and!; [|done|done].
    etrans; [|exact HP]. by apply cgr_if_false.
  - destruct (IHHs _ Ha eq_refl) as (𝜆 & P1 & K & R & n & Q1 & HP & Hg & HQ).
    exists 𝜆, P1, K, (R ∥ ren (Nat.add n) Q), n, Q1. split_and!; [|done|].
    + etrans; [by apply cgr_par|]. etrans; [apply cgr_res_scope_n|].
      apply cgr_resn, cgr_par_assoc.
    + etrans; [by apply cgr_par|]. etrans; [apply cgr_res_scope_n|].
      apply cgr_resn, cgr_par_assoc.
  - destruct (IHHs _ Ha eq_refl) as (𝜆 & P1 & K & R & n & Q1 & HP & Hg & HQ).
    exists 𝜆, P1, K, (R ∥ ren (Nat.add n) P), n, Q1. split_and!; [|done|].
    + etrans; [apply cgr_par_com|].
      etrans; [by apply cgr_par|]. etrans; [apply cgr_res_scope_n|].
      apply cgr_resn, cgr_par_assoc.
    + etrans; [apply cgr_par_com|].
      etrans; [by apply cgr_par|]. etrans; [apply cgr_res_scope_n|].
      apply cgr_resn, cgr_par_assoc.
  - assert (E : ren_lbl S (ActExt a0) = ActExt a0) by (destruct a0; simpl in *; done).
    destruct (IHHs _ Ha E) as (𝜆 & P1 & K & R & n & Q1 & HP & Hg & HQ).
    rewrite E in Hg.
    exists 𝜆, P1, K, R, (S n), Q1. split_and!; [by apply cgr_res|done|by apply cgr_res].
Qed.

Reserved Notation "⟨ ρ , P ⟩ ⟶[ s ] ⟨ ρ' , P' ⟩" (at level 70).

Section STS.
  Context `{QM : QuantumModel}.

  (* ** Silent transitions of the composition memory ∣ program *)

  Lemma comp_tau_inv ρ P s ρ' P' :
    ρ ∣ P ⟶{τ}[s] ρ' ∣ P' →
    (P ⟶{τ}[s] P' ∧ ρ' = ρ) ∨ (∃ a b, P ⟶{ActExt a}[s] P' ∧ ρ ⟶ₘ{b} ρ' ∧ 𝔻ₘₑₘ b a).
  Proof.
    intros Hp. inversion Hp as [? ? ? l ? Hm El | ? ? ? l ? Hq El | ? ? c1 c2 ? μ1 μ2 ? ? Hm Hq Hs Hc]; subst.
    - destruct (mem_step_choice _ _ _ _ Hm) as (_ & b & ->). discriminate.
    - destruct l; [discriminate |]. by left.
    - destruct (mem_step_choice _ _ _ _ Hm) as (-> & _).
      rewrite (cmul_eps_l_inv _ _ Hc). right. by exists μ2, μ1.
  Qed.

  Lemma comp_tau_right ρ P s P' : P ⟶{τ}[s] P' → ρ ∣ P ⟶{τ}[s] ρ ∣ P'.
  Proof. intros Hp. exact (par_right mem_step prog_step sync ρ P s τ P' Hp). Qed.

  Lemma comp_tau_sync ρ P s a P' b ρ' :
    P ⟶{ActExt a}[s] P' → ρ ⟶ₘ{b} ρ' → 𝔻ₘₑₘ b a → ρ ∣ P ⟶{τ}[s] ρ' ∣ P'.
  Proof. intros Hp Hm Hs. eapply par_sync; [exact Hm | exact Hp | exact Hs | constructor]. Qed.

  (* ** The reduction semantics *)

  Inductive sts : St → proc → choice → St → proc → Prop :=
  | sts_com ρ t c e v t' P K :
      eval e = Some v →
      ⟨ρ, t ∶ c ! e ∥ ((t' ∶ c ? ∙ P) + K)⟩ ⟶[⦗t, t'⦘] ⟨ρ, 𝟘 ∥ P ⟦ v ⟧⟩
  | sts_tau ρ t P K :
      ⟨ρ, ((t ∶ 𝛕 ∙ P) + K)⟩ ⟶[t] ⟨ρ, P⟩
  | sts_op ρ t E es qs P K :
      eval_qubits es = Some qs →
      ⟨ρ, ((t ∶ E ⦅es⦆ ∙ P) + K)⟩ ⟶[t] ⟨sop_apply E qs ρ, P⟩
  | sts_init ρ t es qs P K :
      eval_qubits es = Some qs →
      ⟨ρ, ((t ∶ init ⦅es⦆ ∙ P) + K)⟩ ⟶[t] ⟨init_apply qs ρ, P⟩
  | sts_meas ρ t M es qs (k : Out (meas_of M qs)) P K :
      eval_qubits es = Some qs →
      ⟨ρ, ((t ∶ M ⦅es ▷⦆ ∙ P) + K)⟩ ⟶[t] ⟨M ⦅qs⦆[k] · ρ, P ⟦ VNat (code _ k) ⟧⟩
  | sts_rec ρ t X P :
      ⟨ρ, t ∶ rec X ∙ P⟩ ⟶[t] ⟨ρ, P ⦃ t ∶ rec X ∙ P // X ⦄⟩
  | sts_par ρ P s ρ' P' Q :
      ⟨ρ, P⟩ ⟶[s] ⟨ρ', P'⟩ → ⟨ρ, P ∥ Q⟩ ⟶[s] ⟨ρ', P' ∥ Q⟩
  | sts_res ρ P s ρ' P' :
      ⟨ρ, P⟩ ⟶[s] ⟨ρ', P'⟩ → ⟨ρ, ν P⟩ ⟶[s] ⟨ρ', ν P'⟩
  | sts_cong ρ P P1 s ρ' Q1 Q :
      P ≡* P1 → ⟨ρ, P1⟩ ⟶[s] ⟨ρ', Q1⟩ → Q1 ≡* Q → ⟨ρ, P⟩ ⟶[s] ⟨ρ', Q⟩
  where "⟨ ρ , P ⟩ ⟶[ s ] ⟨ ρ' , P' ⟩" := (sts ρ P s ρ' P') : lqccs_scope.

  Lemma sts_resn n ρ P s ρ' P' : ⟨ρ, P⟩ ⟶[s] ⟨ρ', P'⟩ → ⟨ρ, Ѵ n P⟩ ⟶[s] ⟨ρ', Ѵ n P'⟩.
  Proof. intros Hs. induction n; simpl; [done|]. by apply sts_res. Qed.

  (* ** From the LTS to the STS *)

  (* A communication between an output under [n] restrictions and an input
      under [m] restrictions: the restrictions are extruded one by one. *)
  Lemma Com_shapes ρ n :
    ∀ m c e v t t' P1 K R R', eval e = Some v →
    ⟨ρ, Ѵ n (t ∶ (ren_chan (Nat.add n) c) ! e ∥ R)
        ∥ Ѵ m (((t' ∶ (ren_chan (Nat.add m) c) ? ∙ P1) + K) ∥ R')⟩
      ⟶[⦗t, t'⦘] ⟨ρ, Ѵ n (𝟘 ∥ R) ∥ Ѵ m (P1 ⟦ v ⟧ ∥ R')⟩.
  Proof.
    induction n as [|n IHn]; intros m.
    - induction m as [|m IHm]; intros c e v t t' P1 K R R' He; cbn [Ѵ].
      + rewrite !ren_chan_add_0.
        eapply sts_cong; [apply cgr_par_inversion| |apply cgr_par_inversion].
        apply sts_par. by apply sts_com.
      + eapply sts_cong.
        * etrans; [apply cgr_par_com|].
          etrans; [apply cgr_res_scope_rev|]. apply cgr_res, cgr_par_com.
        * apply sts_res. cbn [ren gren]. rewrite ren_chan_add_0.
          specialize (IHm (ren_chan S c) e v t t' P1 K (ren S R) R' He). cbn [Ѵ] in IHm.
          rewrite ren_chan_add_0, ren_chan_add_S in IHm. exact IHm.
        * etrans; [apply cgr_res, cgr_par_com|].
          change (𝟘 ∥ ren S R) with (ren S (𝟘 ∥ R)).
          etrans; [apply cgr_res_scope|]. apply cgr_par_com.
    - intros c e v t t' P1 K R R' He. cbn [Ѵ].
      eapply sts_cong.
      + apply cgr_res_scope_rev.
      + apply sts_res. rewrite ren_resn. cbn [ren gren prefix_ren].
        rewrite ren_chan_liftn, <- ren_chan_add_S.
        apply (IHn m (ren_chan S c) e v t t' (ren (liftn m S) P1) (gren (liftn m S) K) R
                 (ren (liftn m S) R') He).
      + rewrite <- (proj1 ren_subst).
        replace (Ѵ m (ren (liftn m S) (P1 ⟦ v ⟧) ∥ ren (liftn m S) R'))
          with (ren S (Ѵ m (P1 ⟦ v ⟧ ∥ R'))) by (rewrite ren_resn; done).
        apply cgr_res_scope.
  Qed.

  (* A silent transition of the program is a reduction. *)
  Lemma Taus_Implies_Reduction ρ P s P' : P ⟶{τ}[s] P' → ⟨ρ, P⟩ ⟶[s] ⟨ρ, P'⟩.
  Proof.
    intros Hp. remember (τ : Labels prog_action) as l eqn:El. revert El.
    induction Hp as [g s l P' Hg | t c e v He | e P Q s l P' He Hp IH | e P Q s l Q' He Hp IH
                   | P Q s l P' Hp IH | P Q s l Q' Hp IH
                   | P Q t t' c v P' Q' HpP _ HpQ _ | P Q t t' c v P' Q' HpP _ HpQ _
                   | P s l P' Hp IH | t X P] using prog_step_guard_ind; intros El; subst.
    - destruct (TransitionShapeForGuard _ _ _ _ Hg) as (𝜆 & Q & K & Hcg & Hs).
      eapply sts_cong; [apply cgr_guard, Hcg| |reflexivity].
      inversion Hs; subst. apply sts_tau.
    - discriminate.
    - eapply sts_cong; [by apply cgr_if_true | by apply IH | reflexivity].
    - eapply sts_cong; [by apply cgr_if_false | by apply IH | reflexivity].
    - apply sts_par. by apply IH.
    - eapply sts_cong; [apply cgr_par_com | apply sts_par; by apply IH | apply cgr_par_com].
    - destruct (TransitionShapeForOutput _ _ _ _ _ HpP) as (t0 & e & R & n & He & Et & HP1 & HP2).
      destruct (TransitionShapeForInput _ _ _ _ _ HpQ) as (t0' & P1 & K & R' & m & Et' & HQ1 & HQ2).
      simplify_eq.
      eapply sts_cong; [by apply cgr_fullpar | by apply Com_shapes | symmetry; by apply cgr_fullpar].
    - destruct (TransitionShapeForInput _ _ _ _ _ HpP) as (t0 & P1 & K & R & n & Et & HP1 & HP2).
      destruct (TransitionShapeForOutput _ _ _ _ _ HpQ) as (t0' & e & R' & m & He & Et' & HQ1 & HQ2).
      simplify_eq. rewrite cpair_comm.
      eapply sts_cong.
      + etrans; [apply cgr_par_com|]. by apply cgr_fullpar.
      + by apply Com_shapes.
      + etrans; [apply cgr_par_com|]. symmetry. by apply cgr_fullpar.
    - apply sts_res. by apply IH.
    - apply sts_rec.
  Qed.

  (* A quantum action of the program answered by the memory is a reduction. *)
  Lemma Quantum_Implies_Reduction ρ P s a P' b ρ' :
    P ⟶{ActExt a}[s] P' → ρ ⟶ₘ{b} ρ' → 𝔻ₘₑₘ b a → ⟨ρ, P⟩ ⟶[s] ⟨ρ', P'⟩.
  Proof.
    intros Hp Hm Hd. assert (Ha : quant_action a) by (by destruct Hd).
    destruct (TransitionShapeForQuantum _ _ _ _ Ha Hp) as (𝜆 & P1 & K & R & n & Q1 & HP & Hg & HQ).
    eapply sts_cong; [exact HP| |symmetry; exact HQ].
    apply sts_resn, sts_par.
    inversion Hd; subst; inversion Hm; subst; inversion Hg; subst.
    - by apply sts_op.
    - by apply sts_meas.
    - by apply sts_init.
  Qed.

  Lemma Internal_Implies_Reduction ρ P s ρ' P' :
    ρ ∣ P ⟶{τ}[s] ρ' ∣ P' → ⟨ρ, P⟩ ⟶[s] ⟨ρ', P'⟩.
  Proof.
    intros Hc. destruct (comp_tau_inv _ _ _ _ _ Hc) as [(Hp & ->)|(a & b & Hp & Hm & Hd)].
    - by apply Taus_Implies_Reduction.
    - by eapply Quantum_Implies_Reduction.
  Qed.

  (* ** From the STS to the LTS *)

  Lemma Reduction_Implies_Internal ρ P s ρ' Q :
    ⟨ρ, P⟩ ⟶[s] ⟨ρ', Q⟩ → ∃ Q', ρ ∣ P ⟶{τ}[s] ρ' ∣ Q' ∧ Q' ≡* Q.
  Proof.
    induction 1 as [ρ t c e v t' P K He | ρ t P K | ρ t E es qs P K Hq | ρ t es qs P K Hq
                   | ρ t M es qs k P K Hq | ρ t X P
                   | ρ P s ρ' P' Q _ (P'' & Hc & HP)
                   | ρ P s ρ' P' _ (P'' & Hc & HP)
                   | ρ P P1 s ρ' Q1 Q Hcg _ (Q1' & Hc & HQ) Hcg'].
    - exists (𝟘 ∥ P ⟦ v ⟧). split; [|reflexivity]. apply comp_tau_right.
      eapply pr_syncL; [by apply pr_send | apply pr_sumL, pr_recv].
    - exists P. split; [|reflexivity]. apply comp_tau_right.
      apply pr_sumL, pr_tau.
    - exists P. split; [|reflexivity].
      eapply comp_tau_sync; [by apply pr_sumL, pr_op | apply (me_sop ρ (sop_act E qs)) | constructor].
    - exists P. split; [|reflexivity].
      eapply comp_tau_sync; [by apply pr_sumL, pr_init | apply (me_sop ρ (init_act qs)) | constructor].
    - exists (P ⟦ VNat (code _ k) ⟧). split; [|reflexivity].
      eapply comp_tau_sync; [by apply pr_sumL, pr_meas | apply me_meas | constructor].
    - exists (P ⦃ t ∶ rec X ∙ P // X ⦄). split; [|reflexivity]. apply comp_tau_right, pr_rec.
    - exists (P'' ∥ Q). split; [|by apply cgr_par].
      destruct (comp_tau_inv _ _ _ _ _ Hc) as [(Hp & ->)|(a & b & Hp & Hm & Hd)].
      + apply comp_tau_right. by apply pr_parL.
      + eapply comp_tau_sync; [by apply pr_parL | exact Hm | exact Hd].
    - exists (ν P''). split; [|by apply cgr_res].
      destruct (comp_tau_inv _ _ _ _ _ Hc) as [(Hp & ->)|(a & b & Hp & Hm & Hd)].
      + apply comp_tau_right. by apply pr_res.
      + eapply comp_tau_sync; [|exact Hm | exact Hd].
        apply pr_res. by rewrite (sync_lbl_ren _ _ Hd).
    - assert (Hf : fwd P1 P) by (apply cgr_bisim; by symmetry).
      destruct (comp_tau_inv _ _ _ _ _ Hc) as [(Hp & ->)|(a & b & Hp & Hm & Hd)];
        destruct (Hf _ _ _ Hp) as (Q' & Hp' & HQ'); exists Q'.
      + split; [by apply comp_tau_right|]. etrans; [symmetry; exact HQ'|]. etrans; [exact HQ|exact Hcg'].
      + split; [by eapply comp_tau_sync|]. etrans; [symmetry; exact HQ'|]. etrans; [exact HQ|exact Hcg'].
  Qed.

  (* ** The Harmony lemma *)

  Theorem harmony_composition ρ P s ρ' Q :
    ⟨ρ, P⟩ ⟶[s] ⟨ρ', Q⟩ ↔ ∃ Q', ρ ∣ P ⟶{τ}[s] ρ' ∣ Q' ∧ Q' ≡* Q.
  Proof.
    split; [apply Reduction_Implies_Internal|].
    intros (Q' & Hc & HQ).
    eapply sts_cong; [reflexivity | by apply Internal_Implies_Reduction | exact HQ].
  Qed.

  (* The same statement on the LTS given directly on the configurations. *)
  Theorem harmony ρ P s ρ' Q :
    ⟨ρ, P⟩ ⟶[s] ⟨ρ', Q⟩ ↔ ∃ Q', ⟨ρ, P⟩ ⟶{τ}[s] ⟨ρ', Q'⟩ ∧ Q' ≡* Q.
  Proof.
    rewrite harmony_composition.
    split; intros (Q' & Hc & HQ); exists Q'; (split; [by apply pre_harmony|done]).
  Qed.
End STS.

Notation "⟨ ρ , P ⟩ ⟶[ s ] ⟨ ρ' , P' ⟩" := (sts ρ P s ρ' P') (at level 70) : lqccs_scope.
(* end hide *)
