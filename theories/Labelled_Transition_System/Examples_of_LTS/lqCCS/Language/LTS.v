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
(* * lqCCS: the three LTSs and the parallel composition of LTSs

    - [conf_step]: the configuration LTS [⟨ρ, P⟩ -λ->_s ⟨ρ', P'⟩] (Figure 1);
    - [prog_step]: the program LTS, where quantum operations are requests to
      the memory (Figure 2);
    - [mem_step]: the memory LTS (Figure 3);
    - [par_step] ([L1 ∣[sync] L2]): the parallel composition of two LTSs
      with choices, for a synchronisation predicate [sync].

    A restriction [ν P] binds the index [0]: the action [λ] of [ν P] is the
    action [λ] with its indices shifted ([ren_lbl S λ]) of [P], so that no
    action on the index [0] goes through (rule [pr_res], as [lts_res_ext] of
    VACCS).  The choice of a synchronisation is the unordered pair of its two
    tags ([cpair]). *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list sets numbers.
From TestingTheory Require Import ActTau.
From TestingTheory Require Import lqCCS.Harmony_Lemma.Lifted lqCCS.Harmony_Lemma.Paths lqCCS.Harmony_Lemma.States lqCCS.Language.Quantum.
From TestingTheory Require Import lqCCS.Language.Syntax.

#[local] Open Scope lqccs_scope.

(* ** Choices [s ::= ε | t | {t, t'}] and their product *)

Inductive choice : Type :=
| CEps
| CTag (t : tag)
| CPair (t t' : tag).

(* The unordered pair [{t, t'}], as a sorted pair. *)
Definition cpair (t t' : tag) : choice := CPair (Nat.min t t') (Nat.max t t').

Lemma cpair_comm t t' : cpair t t' = cpair t' t.
Proof. unfold cpair. by rewrite Nat.min_comm, Nat.max_comm. Qed.

Inductive cmul : choice → choice → choice → Prop :=
| cmul_eps_l c : cmul CEps c c
| cmul_eps_r c : cmul c CEps c
| cmul_tags t t' : cmul (CTag t) (CTag t') (cpair t t').

(* ** Parallel composition of two LTSs with choices *)

Section Parallel.
  Context {S1 S2 A1 A2 : Type}.
  Variable lts1 : S1 → choice → Labels A1 → S1 → Prop.
  Variable lts2 : S2 → choice → Labels A2 → S2 → Prop.
  Variable sync : A1 → A2 → Prop.

  Definition lbl_inl (l : Labels A1) : Labels (A1 + A2) :=
    match l with ActExt μ => ActExt (inl μ) | τ => τ end.
  Definition lbl_inr (l : Labels A2) : Labels (A1 + A2) :=
    match l with ActExt μ => ActExt (inr μ) | τ => τ end.

  Inductive par_step : S1 * S2 → choice → Labels (A1 + A2) → S1 * S2 → Prop :=
  | par_left s1 s2 c l s1' :
      lts1 s1 c l s1' → par_step (s1, s2) c (lbl_inl l) (s1', s2)
  | par_right s1 s2 c l s2' :
      lts2 s2 c l s2' → par_step (s1, s2) c (lbl_inr l) (s1, s2')
  | par_sync s1 s2 c1 c2 c μ1 μ2 s1' s2' :
      lts1 s1 c1 (ActExt μ1) s1' → lts2 s2 c2 (ActExt μ2) s2' →
      sync μ1 μ2 → cmul c1 c2 c →
      par_step (s1, s2) c τ (s1', s2').
End Parallel.

Notation "L1 ∣[ R ] L2" := (par_step L1 L2 R) (at level 60).

(* ** The program LTS *)

Inductive prog_action : Type :=
| PrOut (c : channel) (v : val)
| PrIn (c : channel) (v : val)
| PrOp (E : sop) (qs : list qubit)
| PrMeas (M : meas) (qs : list qubit) (n : nat)
| PrInit (qs : list qubit).

Definition chan_action (a : prog_action) : Prop :=
  ∃ c v, a = PrOut c v ∨ a = PrIn c v.

(* Renaming of the channel of an action. *)
Definition ren_action (f : nat → nat) (a : prog_action) : prog_action :=
  match a with
  | PrOut c v => PrOut (ren_chan f c) v
  | PrIn c v => PrIn (ren_chan f c) v
  | _ => a
  end.

Definition ren_lbl (f : nat → nat) (l : Labels prog_action) : Labels prog_action :=
  match l with ActExt a => ActExt (ren_action f a) | τ => τ end.

Inductive prog_gstep : guard → choice → Labels prog_action → proc → Prop :=
| pg_tau t P :
    prog_gstep (PTau t ∙ P) (CTag t) τ P
| pg_recv t c v P :
    prog_gstep (PRecv t c ∙ P) (CTag t) (ActExt (PrIn c v)) (P ⟦ v ⟧)
| pg_op t E es qs P :
    eval_qubits es = Some qs →
    prog_gstep (POp t E es ∙ P) (CTag t) (ActExt (PrOp E qs)) P
| pg_meas t M es qs n P :
    eval_qubits es = Some qs →
    prog_gstep (PMeas t M es ∙ P) (CTag t) (ActExt (PrMeas M qs n)) (P ⟦ VNat n ⟧)
| pg_init t es qs P :
    eval_qubits es = Some qs →
    prog_gstep (PInit t es ∙ P) (CTag t) (ActExt (PrInit qs)) P
| pg_sumL g1 g2 s l P' :
    prog_gstep g1 s l P' → prog_gstep (g1 ⊕ g2) s l P'
| pg_sumR g1 g2 s l P' :
    prog_gstep g2 s l P' → prog_gstep (g1 ⊕ g2) s l P'.

Inductive prog_step : proc → choice → Labels prog_action → proc → Prop :=
| pr_guard g s l P' :
    prog_gstep g s l P' → prog_step (PG g) s l P'
| pr_send t c e v :
    eval e = Some v → prog_step (PSend t c e) (CTag t) (ActExt (PrOut c v)) 𝟘
| pr_iteT e P Q s l P' :
    eval e = Some (VBool true) → prog_step P s l P' → prog_step (PIte e P Q) s l P'
| pr_iteF e P Q s l Q' :
    eval e = Some (VBool false) → prog_step Q s l Q' → prog_step (PIte e P Q) s l Q'
| pr_parL P Q s l P' :
    prog_step P s l P' → prog_step (P ∥ Q) s l (P' ∥ Q)
| pr_parR P Q s l Q' :
    prog_step Q s l Q' → prog_step (P ∥ Q) s l (P ∥ Q')
| pr_syncL P Q t t' c v P' Q' :
    prog_step P (CTag t) (ActExt (PrOut c v)) P' → prog_step Q (CTag t') (ActExt (PrIn c v)) Q' →
    prog_step (P ∥ Q) (cpair t t') τ (P' ∥ Q')
| pr_syncR P Q t t' c v P' Q' :
    prog_step P (CTag t) (ActExt (PrIn c v)) P' → prog_step Q (CTag t') (ActExt (PrOut c v)) Q' →
    prog_step (P ∥ Q) (cpair t t') τ (P' ∥ Q')
| pr_res P s l P' :
    prog_step P s (ren_lbl S l) P' → prog_step (ν P) s l (ν P')
| pr_rec t X P :
    prog_step (PRec t X P) (CTag t) τ (P ⦃ PRec t X P // X ⦄).

(* ** The memory LTS and the synchronisation predicates *)

Inductive mem_action : Type :=
| MeSop (S : msop) (qs : list qubit)
| MeMeas (M : meas) (qs : list qubit) (n : nat).

(* [ℰ_U(q̃)‾ sync U(q̃)], [ℰ_init(q̃)‾ sync init(q̃)], [M(q̃)!m sync M(q̃)?m] *)
Inductive sync : mem_action → prog_action → Prop :=
| sync_op E qs : sync (MeSop (SGate E) qs) (PrOp E qs)
| sync_meas M qs n : sync (MeMeas M qs n) (PrMeas M qs n)
| sync_init qs : sync (MeSop SInit qs) (PrInit qs).

(* [c!v sync c?v] and [c?v sync c!v] *)
Inductive sync_chan : prog_action → prog_action → Prop :=
| sync_out_in c v : sync_chan (PrOut c v) (PrIn c v)
| sync_in_out c v : sync_chan (PrIn c v) (PrOut c v).

(* Between the system memory ∣ program and a program. *)
Inductive sync_sys : mem_action + prog_action → prog_action → Prop :=
| sync_sys_mem b a : sync b a → sync_sys (inl b) a
| sync_sys_chan a a' : sync_chan a a' → sync_sys (inr a) a'.

Section Memory.
  Context `{QM : QuantumModel}.

  Inductive mem_step : St → choice → Labels mem_action → St → Prop :=
  | me_sop ρ S qs :
      mem_step ρ CEps (ActExt (MeSop S qs)) (msop_apply S qs ρ)
  | me_meas ρ M qs (k : Out (meas_of M qs)) :
      mem_step ρ CEps (ActExt (MeMeas M qs (code _ k))) (meas_branch M qs k ρ).

  (* ** The configuration LTS *)

  Inductive conf_gstep (ρ : St) : guard → choice → Labels prog_action → St → proc → Prop :=
  | cg_tau t P :
      conf_gstep ρ (PTau t ∙ P) (CTag t) τ ρ P
  | cg_op t E es qs P :
      eval_qubits es = Some qs →
      conf_gstep ρ (POp t E es ∙ P) (CTag t) τ (sop_apply E qs ρ) P
  | cg_meas t M es qs (k : Out (meas_of M qs)) P :
      eval_qubits es = Some qs →
      conf_gstep ρ (PMeas t M es ∙ P) (CTag t) τ
        (meas_branch M qs k ρ) (P ⟦ VNat (code _ k) ⟧)
  | cg_init t es qs P :
      eval_qubits es = Some qs →
      conf_gstep ρ (PInit t es ∙ P) (CTag t) τ (init_apply qs ρ) P
  | cg_recv t c v P :
      conf_gstep ρ (PRecv t c ∙ P) (CTag t) (ActExt (PrIn c v)) ρ (P ⟦ v ⟧)
  | cg_sumL g1 g2 s l ρ' P' :
      conf_gstep ρ g1 s l ρ' P' → conf_gstep ρ (g1 ⊕ g2) s l ρ' P'
  | cg_sumR g1 g2 s l ρ' P' :
      conf_gstep ρ g2 s l ρ' P' → conf_gstep ρ (g1 ⊕ g2) s l ρ' P'.

  Inductive conf_step (ρ : St) : proc → choice → Labels prog_action → St → proc → Prop :=
  | co_guard g s l ρ' P' :
      conf_gstep ρ g s l ρ' P' → conf_step ρ (PG g) s l ρ' P'
  | co_send t c e v :
      eval e = Some v → conf_step ρ (PSend t c e) (CTag t) (ActExt (PrOut c v)) ρ 𝟘
  | co_iteT e P Q s l ρ' P' :
      eval e = Some (VBool true) → conf_step ρ P s l ρ' P' → conf_step ρ (PIte e P Q) s l ρ' P'
  | co_iteF e P Q s l ρ' Q' :
      eval e = Some (VBool false) → conf_step ρ Q s l ρ' Q' → conf_step ρ (PIte e P Q) s l ρ' Q'
  | co_parL P Q s l ρ' P' :
      conf_step ρ P s l ρ' P' → conf_step ρ (P ∥ Q) s l ρ' (P' ∥ Q)
  | co_parR P Q s l ρ' Q' :
      conf_step ρ Q s l ρ' Q' → conf_step ρ (P ∥ Q) s l ρ' (P ∥ Q')
  | co_syncL P Q t t' c v P' Q' :
      conf_step ρ P (CTag t) (ActExt (PrOut c v)) ρ P' →
      conf_step ρ Q (CTag t') (ActExt (PrIn c v)) ρ Q' →
      conf_step ρ (P ∥ Q) (cpair t t') τ ρ (P' ∥ Q')
  | co_syncR P Q t t' c v P' Q' :
      conf_step ρ P (CTag t) (ActExt (PrIn c v)) ρ P' →
      conf_step ρ Q (CTag t') (ActExt (PrOut c v)) ρ Q' →
      conf_step ρ (P ∥ Q) (cpair t t') τ ρ (P' ∥ Q')
  | co_res P s l ρ' P' :
      conf_step ρ P s (ren_lbl S l) ρ' P' → conf_step ρ (ν P) s l ρ' (ν P')
  | co_rec t X P :
      conf_step ρ (PRec t X P) (CTag t) τ ρ (P ⦃ PRec t X P // X ⦄).
End Memory.

(* ** Facts on the program LTS *)

Lemma prog_gstep_not_out g s c v P' : ¬ prog_gstep g s (ActExt (PrOut c v)) P'.
Proof.
  intros Hs. remember (ActExt (PrOut c v)) as l eqn:El. induction Hs; simplify_eq; auto.
Qed.

Lemma prog_gstep_ext_choice g s a P' : prog_gstep g s (ActExt a) P' → ∃ t, s = CTag t.
Proof. intros Hs. remember (ActExt a) as l eqn:El. induction Hs; simplify_eq; eauto. Qed.

Lemma ren_lbl_ext l : ∀ a, ren_lbl S l = ActExt a → ∃ a', l = ActExt a'.
Proof. destruct l; simpl; intros a Ha; simplify_eq; eauto. Qed.

Lemma prog_step_ext_choice P s a P' : prog_step P s (ActExt a) P' → ∃ t, s = CTag t.
Proof.
  intros Hs. remember (ActExt a) as l eqn:El. revert a El.
  induction Hs; intros a0 El; simplify_eq; eauto.
  by eapply prog_gstep_ext_choice.
Qed.

(* ** Renaming of the indices commutes with the transitions *)

Lemma ren_action_comp f g a : ren_action f (ren_action g a) = ren_action (f ∘ g) a.
Proof. destruct a; simpl; by rewrite ?ren_chan_comp. Qed.

Lemma ren_lbl_comp f g l : ren_lbl f (ren_lbl g l) = ren_lbl (f ∘ g) l.
Proof. destruct l; simpl; by rewrite ?ren_action_comp. Qed.

Lemma ren_action_ext f g a : (∀ i, f i = g i) → ren_action f a = ren_action g a.
Proof. intros H. destruct a; simpl; by rewrite ?(ren_chan_ext f g). Qed.

Lemma ren_lbl_ext_fun f g l : (∀ i, f i = g i) → ren_lbl f l = ren_lbl g l.
Proof. intros H. destruct l; simpl; by rewrite ?(ren_action_ext f g). Qed.

(* [ren_lbl (lift f) (ren_lbl S l) = ren_lbl S (ren_lbl f l)] *)
Lemma ren_lbl_lift_S f l : ren_lbl (lift f) (ren_lbl S l) = ren_lbl S (ren_lbl f l).
Proof. rewrite !ren_lbl_comp. by apply ren_lbl_ext_fun. Qed.

Lemma ren_action_inj f :
  (∀ i j, f i = f j → i = j) → ∀ a a', ren_action f a = ren_action f a' → a = a'.
Proof.
  intros Hf [c v|c v| | |] [c' v'|c' v'| | |]; simpl; intros [=]; subst; try done.
  all: f_equal; by eapply ren_chan_inj.
Qed.

Lemma ren_lbl_inj f :
  (∀ i j, f i = f j → i = j) → ∀ l l', ren_lbl f l = ren_lbl f l' → l = l'.
Proof.
  intros Hf [a|] [a'|]; simpl; intros [=]; try done. f_equal. by eapply ren_action_inj.
Qed.

Lemma prog_gstep_ren f g s l P' :
  prog_gstep g s l P' → prog_gstep (gren f g) s (ren_lbl f l) (ren f P').
Proof.
  intros Hs. induction Hs; simpl in *.
  - constructor.
  - rewrite (proj1 ren_subst). constructor.
  - by constructor.
  - rewrite (proj1 ren_subst). by constructor.
  - by constructor.
  - by apply pg_sumL.
  - by apply pg_sumR.
Qed.

Lemma prog_step_ren f P s l P' :
  prog_step P s l P' → prog_step (ren f P) s (ren_lbl f l) (ren f P').
Proof.
  intros Hs. revert f. induction Hs; intros f; simpl in *.
  - constructor. by apply prog_gstep_ren.
  - by constructor.
  - by apply pr_iteT.
  - by apply pr_iteF.
  - by apply pr_parL.
  - by apply pr_parR.
  - by eapply pr_syncL; [apply IHHs1|apply IHHs2].
  - by eapply pr_syncR; [apply IHHs1|apply IHHs2].
  - apply pr_res. rewrite <- ren_lbl_lift_S. apply IHHs.
  - rewrite (proj1 (ren_pr_subst X)). simpl. constructor.
Qed.

(* The converse, for an injective renaming. *)
Lemma prog_gstep_ren_inv f :
  (∀ i j, f i = f j → i = j) →
  ∀ g s l' X, prog_gstep (gren f g) s l' X →
  ∃ l P', l' = ren_lbl f l ∧ X = ren f P' ∧ prog_gstep g s l P'.
Proof.
  intros Hf g s l' X Hs. remember (gren f g) as G eqn:EG. revert g EG.
  induction Hs; intros g0 EG; destruct g0 as [es0| |𝜆0 P0|g1' g2']; simpl in EG; simplify_eq.
  all: try (destruct 𝜆0; simpl in EG; simplify_eq).
  - exists τ, P0. split_and!; [done|done|constructor].
  - exists (ActExt (PrIn c0 v)), (P0 ⟦ v ⟧).
    split_and!; [done|by rewrite (proj1 ren_subst)|constructor].
  - exists (ActExt (PrOp E0 qs)), P0. split_and!; [done|done|by constructor].
  - exists (ActExt (PrMeas M0 qs n)), (P0 ⟦ VNat n ⟧).
    split_and!; [done|by rewrite (proj1 ren_subst)|by constructor].
  - exists (ActExt (PrInit qs)), P0. split_and!; [done|done|by constructor].
  - destruct (IHHs g1' eq_refl) as (l0 & P'0 & -> & -> & Hg). exists l0, P'0. split_and!; [done|done|by apply pg_sumL].
  - destruct (IHHs g2' eq_refl) as (l0 & P'0 & -> & -> & Hg). exists l0, P'0. split_and!; [done|done|by apply pg_sumR].
Qed.

Lemma prog_step_ren_inv f :
  (∀ i j, f i = f j → i = j) →
  ∀ P s l' X, prog_step (ren f P) s l' X →
  ∃ l P', l' = ren_lbl f l ∧ X = ren f P' ∧ prog_step P s l P'.
Proof.
  intros Hf P s l' X Hs. remember (ren f P) as RP eqn:ER. revert f Hf P ER.
  induction Hs; intros f Hf P0 ER;
    destruct P0 as [t0 c0 e0|e0 P1 P2|P1 P2|P1|X0|t0 X0 P1|g0]; simpl in ER; simplify_eq.
  - destruct (prog_gstep_ren_inv f Hf _ _ _ _ H) as (l0 & P'0 & -> & -> & Hg).
    exists l0, P'0. split_and!; [done|done|by constructor].
  - exists (ActExt (PrOut c0 v)), 𝟘. split_and!; [done|done|by constructor].
  - destruct (IHHs f Hf P1 eq_refl) as (l0 & P'0 & -> & -> & Hp).
    exists l0, P'0. split_and!; [done|done|by apply pr_iteT].
  - destruct (IHHs f Hf P2 eq_refl) as (l0 & P'0 & -> & -> & Hp).
    exists l0, P'0. split_and!; [done|done|by apply pr_iteF].
  - destruct (IHHs f Hf P1 eq_refl) as (l0 & P'0 & -> & -> & Hp).
    exists l0, (P'0 ∥ P2). split_and!; [done|done|by apply pr_parL].
  - destruct (IHHs f Hf P2 eq_refl) as (l0 & P'0 & -> & -> & Hp).
    exists l0, (P1 ∥ P'0). split_and!; [done|done|by apply pr_parR].
  - destruct (IHHs1 f Hf P1 eq_refl) as (l1 & P1' & E1 & -> & Hp1).
    destruct (IHHs2 f Hf P2 eq_refl) as (l2 & P2' & E2 & -> & Hp2).
    destruct l1 as [[c1 v1|c1 v1| | |]|]; simpl in E1; simplify_eq.
    destruct l2 as [[c2 v2|c2 v2| | |]|]; simpl in E2; simplify_eq.
    assert (c1 = c2) by (eapply ren_chan_inj; [exact Hf|congruence]). subst.
    exists τ, (P1' ∥ P2'). split_and!; [done|done|by eapply pr_syncL].
  - destruct (IHHs1 f Hf P1 eq_refl) as (l1 & P1' & E1 & -> & Hp1).
    destruct (IHHs2 f Hf P2 eq_refl) as (l2 & P2' & E2 & -> & Hp2).
    destruct l1 as [[c1 v1|c1 v1| | |]|]; simpl in E1; simplify_eq.
    destruct l2 as [[c2 v2|c2 v2| | |]|]; simpl in E2; simplify_eq.
    assert (c1 = c2) by (eapply ren_chan_inj; [exact Hf|congruence]). subst.
    exists τ, (P1' ∥ P2'). split_and!; [done|done|by eapply pr_syncR].
  - destruct (IHHs (lift f) (lift_inj f Hf) P1 eq_refl) as (l0 & P'0 & E0 & -> & Hp).
    destruct l0 as [[[c0|[|i]] v0|[c0|[|i]] v0|E' qs|M qs n|qs0]|]; simpl in E0;
      destruct l as [[[c1|i1] v1|[c1|i1] v1|E1 qs1|M1 qs1 n1|qs2]|]; simpl in E0; simplify_eq.
    + exists (ActExt (PrOut (CName c0) v0)), (ν P'0). split_and!; [done|done|by apply pr_res].
    + exists (ActExt (PrOut (CIdx i) v0)), (ν P'0). split_and!; [done|done|by apply pr_res].
    + exists (ActExt (PrIn (CName c0) v0)), (ν P'0). split_and!; [done|done|by apply pr_res].
    + exists (ActExt (PrIn (CIdx i) v0)), (ν P'0). split_and!; [done|done|by apply pr_res].
    + exists (ActExt (PrOp E' qs)), (ν P'0). split_and!; [done|done|by apply pr_res].
    + exists (ActExt (PrMeas M qs n)), (ν P'0). split_and!; [done|done|by apply pr_res].
    + exists (ActExt (PrInit qs0)), (ν P'0). split_and!; [done|done|by apply pr_res].
    + exists τ, (ν P'0). split_and!; [done|done|by apply pr_res].
  - exists τ, (P1 ⦃ PRec t0 X0 P1 // X0 ⦄).
    split_and!; [done| |constructor]. rewrite (proj1 (ren_pr_subst X0)). done.
Qed.
(* end hide *)
