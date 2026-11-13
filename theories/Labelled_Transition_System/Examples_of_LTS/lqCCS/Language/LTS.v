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
From TestingTheory Require Import lqCCS.Language.Algebra lqCCS.Language.Quantum.
From TestingTheory Require Import lqCCS.Language.Syntax.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

(* ** Choices [s ::= ε | t | {t, t'}] and their product *)

Inductive choice : Type :=
| CEps
| CTag (t : tag)
| CPair (t t' : tag).

(* The unordered pair [{t, t'}], as a sorted pair. *)
Definition cpair (t t' : tag) : choice := CPair (Nat.min t t') (Nat.max t t').

Coercion CTag : tag >-> choice.
Notation "⦗ t , t' ⦘" := (cpair t t') (at level 0) : lqccs_scope.

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

Notation "c ! v" := (ActExt (PrOut c v)) (at level 30, v at level 9) : lqccs_scope.
Notation "c ? v" := (ActExt (PrIn c v)) (at level 30, v at level 9) : lqccs_scope.
Notation "E ⦅ qs ⦆" := (ActExt (PrOp E qs)) (at level 30) : lqccs_scope.
Notation "M ⦅ qs ⦆? n" := (ActExt (PrMeas M qs n)) (at level 30, n at level 9) : lqccs_scope.
Notation "'init' ⦅ qs ⦆" := (ActExt (PrInit qs)) (at level 30) : lqccs_scope.

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

Reserved Notation "P ⟶{ l }[ s ] P'" (at level 70).

Inductive prog_step : proc → choice → Labels prog_action → proc → Prop :=
| pr_tau t P :
    (t ∶ 𝛕 ∙ P) ⟶{τ}[t] P
| pr_recv t c v P :
    (t ∶ c ? ∙ P) ⟶{c ? v}[t] (P ⟦ v ⟧)
| pr_op t E es qs P :
    eval_qubits es = Some qs →
    (t ∶ E ⦅es⦆ ∙ P) ⟶{E ⦅qs⦆}[t] P
| pr_meas t M es qs n P :
    eval_qubits es = Some qs →
    (t ∶ M ⦅es ▷⦆ ∙ P) ⟶{M ⦅qs⦆? n}[t] (P ⟦ VNat n ⟧)
| pr_init t es qs P :
    eval_qubits es = Some qs →
    (t ∶ init ⦅es⦆ ∙ P) ⟶{init ⦅qs⦆}[t] P
| pr_sumL (g1 g2 : guard) s l P' :
    g1 ⟶{l}[s] P' → (g1 + g2) ⟶{l}[s] P'
| pr_sumR (g1 g2 : guard) s l P' :
    g2 ⟶{l}[s] P' → (g1 + g2) ⟶{l}[s] P'
| pr_send t c e v :
    eval e = Some v → t ∶ c ! e ⟶{c ! v}[t] 𝟘
| pr_iteT e P Q s l P' :
    eval e = Some (VBool true) → P ⟶{l}[s] P' → If e Then P Else Q ⟶{l}[s] P'
| pr_iteF e P Q s l Q' :
    eval e = Some (VBool false) → Q ⟶{l}[s] Q' → If e Then P Else Q ⟶{l}[s] Q'
| pr_parL P Q s l P' :
    P ⟶{l}[s] P' → P ∥ Q ⟶{l}[s] (P' ∥ Q)
| pr_parR P Q s l Q' :
    Q ⟶{l}[s] Q' → P ∥ Q ⟶{l}[s] (P ∥ Q')
| pr_syncL P Q (t t' : tag) c v P' Q' :
    P ⟶{c ! v}[t] P' → Q ⟶{c ? v}[t'] Q' →
    P ∥ Q ⟶{τ}[⦗t, t'⦘] (P' ∥ Q')
| pr_syncR P Q (t t' : tag) c v P' Q' :
    P ⟶{c ? v}[t] P' → Q ⟶{c ! v}[t'] Q' →
    P ∥ Q ⟶{τ}[⦗t, t'⦘] (P' ∥ Q')
| pr_res P s l P' :
    P ⟶{ren_lbl S l}[s] P' → ν P ⟶{l}[s] (ν P')
| pr_rec t X P :
    t ∶ rec X ∙ P ⟶{τ}[t] (P ⦃ t ∶ rec X ∙ P // X ⦄)
where "P ⟶{ l }[ s ] P'" := (prog_step P s l P') : lqccs_scope.

(* ** Transitions of a guard *)

Definition prog_gstep (g : guard) (s : choice) (l : Labels prog_action) (P' : proc) : Prop :=
  g ⟶{l}[s] P'.
Notation "g ⟶ᵍ{ l }[ s ] P'" := (prog_gstep g s l P') (at level 70, only parsing) : lqccs_scope.

(* Induction on a transition of a guard. *)
Lemma prog_gstep_ind (Q : guard → choice → Labels prog_action → proc → Prop) :
  (∀ t P, Q (t ∶ 𝛕 ∙ P) t τ P) →
  (∀ t c v P, Q (t ∶ c ? ∙ P) t (c ? v) (P ⟦ v ⟧)) →
  (∀ t E es qs P, eval_qubits es = Some qs → Q (t ∶ E ⦅es⦆ ∙ P) t (E ⦅qs⦆) P) →
  (∀ t M es qs n P, eval_qubits es = Some qs →
     Q (t ∶ M ⦅es ▷⦆ ∙ P) t (M ⦅qs⦆? n) (P ⟦ VNat n ⟧)) →
  (∀ t es qs P, eval_qubits es = Some qs → Q (t ∶ init ⦅es⦆ ∙ P) t (init ⦅qs⦆) P) →
  (∀ (g1 g2 : guard) s l P', g1 ⟶{l}[s] P' → Q g1 s l P' → Q (g1 + g2)%lq s l P') →
  (∀ (g1 g2 : guard) s l P', g2 ⟶{l}[s] P' → Q g2 s l P' → Q (g1 + g2)%lq s l P') →
  ∀ (g : guard) s l P', prog_gstep g s l P' → Q g s l P'.
Proof.
  intros Htau Hrecv Hop Hmeas Hinit HsumL HsumR g s l P' Hs. unfold prog_gstep in Hs.
  remember (PG g) as R eqn:ER. revert g ER.
  induction Hs; intros g0 ER; simplify_eq; eauto.
Qed.

(* Induction on a transition of a program, the guards being treated at once. *)
Lemma prog_step_guard_ind (Φ : proc → choice → Labels prog_action → proc → Prop) :
  (∀ (g : guard) s l P', prog_gstep g s l P' → Φ g s l P') →
  (∀ t c e v, eval e = Some v → Φ (t ∶ c ! e) t (c ! v) 𝟘) →
  (∀ e P Q s l P', eval e = Some (VBool true) → P ⟶{l}[s] P' → Φ P s l P' →
     Φ (If e Then P Else Q) s l P') →
  (∀ e P Q s l Q', eval e = Some (VBool false) → Q ⟶{l}[s] Q' → Φ Q s l Q' →
     Φ (If e Then P Else Q) s l Q') →
  (∀ P Q s l P', P ⟶{l}[s] P' → Φ P s l P' → Φ (P ∥ Q) s l (P' ∥ Q)) →
  (∀ P Q s l Q', Q ⟶{l}[s] Q' → Φ Q s l Q' → Φ (P ∥ Q) s l (P ∥ Q')) →
  (∀ P Q (t t' : tag) c v P' Q', P ⟶{c ! v}[t] P' → Φ P t (c ! v) P' →
     Q ⟶{c ? v}[t'] Q' → Φ Q t' (c ? v) Q' → Φ (P ∥ Q) ⦗t, t'⦘ τ (P' ∥ Q')) →
  (∀ P Q (t t' : tag) c v P' Q', P ⟶{c ? v}[t] P' → Φ P t (c ? v) P' →
     Q ⟶{c ! v}[t'] Q' → Φ Q t' (c ! v) Q' → Φ (P ∥ Q) ⦗t, t'⦘ τ (P' ∥ Q')) →
  (∀ P s l P', P ⟶{ren_lbl S l}[s] P' → Φ P s (ren_lbl S l) P' → Φ (ν P) s l (ν P')) →
  (∀ t X P, Φ (t ∶ rec X ∙ P) t τ (P ⦃ t ∶ rec X ∙ P // X ⦄)) →
  ∀ P s l P', P ⟶{l}[s] P' → Φ P s l P'.
Proof.
  intros Hg Hsend HiteT HiteF HparL HparR HsyncL HsyncR Hres Hrec P s l P' Hs.
  induction Hs; eauto; apply Hg; unfold prog_gstep; eauto using prog_step.
Qed.

(* ** The memory LTS and the synchronisation predicates *)

(* [c!v sync c?v] and [c?v sync c!v] *)
Inductive sync_chan : prog_action → prog_action → Prop :=
| sync_out_in c v : sync_chan (PrOut c v) (PrIn c v)
| sync_in_out c v : sync_chan (PrIn c v) (PrOut c v).

Reserved Notation "⟨ ρ , P ⟩ ⟶{ l }[ s ] ⟨ ρ' , P' ⟩" (at level 70).
Reserved Notation "ρ ⟶ₘ{ μ } ρ'" (at level 70).
Reserved Notation "⟨ ρ , P ⟩ ⟶ₘ{ μ } ⟨ ρ' , P' ⟩" (at level 70).
Reserved Notation "M ⦅ qs ⦆! n" (at level 30, n at level 9).

Section Memory.
  Context `{QM : QuantumModel}.

  Inductive mem_action : Type :=
  | MeSop (ℰ : Act)
  | MeMeas (M : meas) (qs : list qubit) (n : nat).

  Coercion MeSop : Act >-> mem_action.
  Notation "M ⦅ qs ⦆! n" := (MeMeas M qs n) : lqccs_scope.

  Inductive sync : mem_action → prog_action → Prop :=
  | sync_op E qs : sync (sop_act E qs) (PrOp E qs)
  | sync_meas M qs n : sync (M ⦅qs⦆! n) (PrMeas M qs n)
  | sync_init qs : sync (init_act qs) (PrInit qs).

  Inductive sync_sys : mem_action + prog_action → prog_action → Prop :=
  | sync_sys_mem b a : sync b a → sync_sys (inl b) a
  | sync_sys_chan a a' : sync_chan a a' → sync_sys (inr a) a'.

  Inductive mem_step : St → choice → Labels mem_action → St → Prop :=
  | me_sop ρ (ℰ : Act) :
      ρ ⟶ₘ{ℰ} (ℰ · ρ)
  | me_meas ρ M qs (k : Out (meas_of M qs)) :
      ρ ⟶ₘ{M ⦅qs⦆! (code _ k)} (M ⦅qs⦆[k] · ρ)
  where "ρ ⟶ₘ{ μ } ρ'" := (mem_step ρ CEps (ActExt (μ : mem_action)) ρ') : lqccs_scope.

  (* ** The configuration LTS *)

  Inductive conf_step (ρ : St) : proc → choice → Labels prog_action + mem_action → St → proc → Prop :=
  | co_tau t P :
      ⟨ρ, t ∶ 𝛕 ∙ P⟩ ⟶{τ}[t] ⟨ρ, P⟩
  | co_recv t c v P :
      ⟨ρ, t ∶ c ? ∙ P⟩ ⟶{c ? v}[t] ⟨ρ, P ⟦ v ⟧⟩
  | co_op t E es qs P :
      eval_qubits es = Some qs →
      ⟨ρ, t ∶ E ⦅es⦆ ∙ P⟩ ⟶{E ⦅qs⦆}[t] ⟨ρ, P⟩
  | co_meas t M es qs n P :
      eval_qubits es = Some qs →
      ⟨ρ, t ∶ M ⦅es ▷⦆ ∙ P⟩ ⟶{M ⦅qs⦆? n}[t] ⟨ρ, P ⟦ VNat n ⟧⟩
  | co_init t es qs P :
      eval_qubits es = Some qs →
      ⟨ρ, t ∶ init ⦅es⦆ ∙ P⟩ ⟶{init ⦅qs⦆}[t] ⟨ρ, P⟩
  | co_sumL (g1 g2 : guard) s l ρ' P' :
      ⟨ρ, g1⟩ ⟶{l}[s] ⟨ρ', P'⟩ → ⟨ρ, g1 + g2⟩ ⟶{l}[s] ⟨ρ', P'⟩
  | co_sumR (g1 g2 : guard) s l ρ' P' :
      ⟨ρ, g2⟩ ⟶{l}[s] ⟨ρ', P'⟩ → ⟨ρ, g1 + g2⟩ ⟶{l}[s] ⟨ρ', P'⟩
  | co_send t c e v :
      eval e = Some v → ⟨ρ, t ∶ c ! e⟩ ⟶{c ! v}[t] ⟨ρ, 𝟘⟩
  | co_iteT e P Q s l ρ' P' :
      eval e = Some (VBool true) → ⟨ρ, P⟩ ⟶{l}[s] ⟨ρ', P'⟩ → ⟨ρ, If e Then P Else Q⟩ ⟶{l}[s] ⟨ρ', P'⟩
  | co_iteF e P Q s l ρ' Q' :
      eval e = Some (VBool false) → ⟨ρ, Q⟩ ⟶{l}[s] ⟨ρ', Q'⟩ → ⟨ρ, If e Then P Else Q⟩ ⟶{l}[s] ⟨ρ', Q'⟩
  | co_parL P Q s l ρ' P' :
      ⟨ρ, P⟩ ⟶{l}[s] ⟨ρ', P'⟩ → ⟨ρ, P ∥ Q⟩ ⟶{l}[s] ⟨ρ', P' ∥ Q⟩
  | co_parR P Q s l ρ' Q' :
      ⟨ρ, Q⟩ ⟶{l}[s] ⟨ρ', Q'⟩ → ⟨ρ, P ∥ Q⟩ ⟶{l}[s] ⟨ρ', P ∥ Q'⟩
  | co_syncL P Q (t t' : tag) c v P' Q' :
      ⟨ρ, P⟩ ⟶{c ! v}[t] ⟨ρ, P'⟩ →
      ⟨ρ, Q⟩ ⟶{c ? v}[t'] ⟨ρ, Q'⟩ →
      ⟨ρ, P ∥ Q⟩ ⟶{τ}[⦗t, t'⦘] ⟨ρ, P' ∥ Q'⟩
  | co_syncR P Q (t t' : tag) c v P' Q' :
      ⟨ρ, P⟩ ⟶{c ? v}[t] ⟨ρ, P'⟩ →
      ⟨ρ, Q⟩ ⟶{c ! v}[t'] ⟨ρ, Q'⟩ →
      ⟨ρ, P ∥ Q⟩ ⟶{τ}[⦗t, t'⦘] ⟨ρ, P' ∥ Q'⟩
  | co_res P s l ρ' P' :
      ⟨ρ, P⟩ ⟶{ren_lbl S l}[s] ⟨ρ', P'⟩ → ⟨ρ, ν P⟩ ⟶{l}[s] ⟨ρ', ν P'⟩
  | co_rec t X P :
      ⟨ρ, t ∶ rec X ∙ P⟩ ⟶{τ}[t] ⟨ρ, P ⦃ t ∶ rec X ∙ P // X ⦄⟩
  | co_mem_sop P (ℰ : Act) :
      ⟨ρ, P⟩ ⟶ₘ{ℰ} ⟨ℰ · ρ, P⟩
  | co_mem_meas P M qs (k : Out (meas_of M qs)) :
      ⟨ρ, P⟩ ⟶ₘ{M ⦅qs⦆! (code _ k)} ⟨M ⦅qs⦆[k] · ρ, P⟩
  | co_opCom P s E qs ρ' P' :
      ⟨ρ, P⟩ ⟶{E ⦅qs⦆}[s] ⟨ρ, P'⟩ →
      ⟨ρ, P⟩ ⟶ₘ{sop_act E qs} ⟨ρ', P⟩ →
      ⟨ρ, P⟩ ⟶{τ}[s] ⟨ρ', P'⟩
  | co_measCom P s M qs n ρ' P' :
      ⟨ρ, P⟩ ⟶{M ⦅qs⦆? n}[s] ⟨ρ, P'⟩ →
      ⟨ρ, P⟩ ⟶ₘ{M ⦅qs⦆! n} ⟨ρ', P⟩ →
      ⟨ρ, P⟩ ⟶{τ}[s] ⟨ρ', P'⟩
  | co_initCom P s qs ρ' P' :
      ⟨ρ, P⟩ ⟶{init ⦅qs⦆}[s] ⟨ρ, P'⟩ →
      ⟨ρ, P⟩ ⟶ₘ{init_act qs} ⟨ρ', P⟩ →
      ⟨ρ, P⟩ ⟶{τ}[s] ⟨ρ', P'⟩
  where "⟨ ρ , P ⟩ ⟶{ l }[ s ] ⟨ ρ' , P' ⟩" := (conf_step ρ P s (inl l) ρ' P') : lqccs_scope
  and "⟨ ρ , P ⟩ ⟶ₘ{ μ } ⟨ ρ' , P' ⟩" := (conf_step ρ P CEps (inr (μ : mem_action)) ρ' P') : lqccs_scope.
End Memory.

Notation "M ⦅ qs ⦆! n" := (MeMeas M qs n) : lqccs_scope.
Notation "ρ ⟶ₘ{ μ } ρ'" := (mem_step ρ CEps (ActExt (μ : mem_action)) ρ')
  (at level 70, only parsing) : lqccs_scope.
Notation "ρ ⟶ₘ{ μ } ρ'" := (mem_step ρ CEps (ActExt μ) ρ')
  (at level 70, only printing) : lqccs_scope.
Notation "⟨ ρ , P ⟩ ⟶{ l }[ s ] ⟨ ρ' , P' ⟩" := (conf_step ρ P s (inl l) ρ' P') (at level 70) : lqccs_scope.
Notation "⟨ ρ , P ⟩ ⟶ₘ{ μ } ⟨ ρ' , P' ⟩" := (conf_step ρ P CEps (inr (μ : mem_action)) ρ' P')
  (at level 70, only parsing) : lqccs_scope.
Notation "⟨ ρ , P ⟩ ⟶ₘ{ μ } ⟨ ρ' , P' ⟩" := (conf_step ρ P CEps (inr μ) ρ' P')
  (at level 70, only printing) : lqccs_scope.
Notation "'𝔻ₘₑₘ'" := sync : lqccs_scope.
Notation "ρ ∣ P ⟶{ l }[ s ] ρ' ∣ P'" :=
  (par_step mem_step prog_step sync (ρ, P) s l (ρ', P'))
  (at level 70, P at level 25, ρ' at level 25, P' at level 25) : lqccs_scope.

(* ** Facts on the program LTS *)

Lemma prog_gstep_not_out (g : guard) s c v P' : ¬ g ⟶{c ! v}[s] P'.
Proof.
  intros Hs. remember (c ! v) as l eqn:El. change (prog_gstep g s l P') in Hs. induction Hs using prog_gstep_ind; simplify_eq; auto.
Qed.

Lemma ren_lbl_ext l : ∀ a, ren_lbl S l = ActExt a → ∃ a', l = ActExt a'.
Proof. destruct l; simpl; intros a Ha; simplify_eq; eauto. Qed.

Lemma prog_step_ext_choice P s a P' : P ⟶{ActExt a}[s] P' → ∃ t, s = CTag t.
Proof.
  intros Hs. remember (ActExt a) as l eqn:El. revert a El.
  induction Hs; intros a0 El; simplify_eq; eauto.
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

Lemma prog_step_ren f P s l P' :
  P ⟶{l}[s] P' → ren f P ⟶{ren_lbl f l}[s] (ren f P').
Proof.
  intros Hs. revert f. induction Hs as [t P | t c v P | t E es qs P Hq | t M es qs n P Hq | t es qs P Hq | g1 g2 s l P' Hgs IH | g1 g2 s l P' Hgs IH | t c e v He | e P Q s l P' He Hp IH | e P Q s l Q' He Hp IH | P Q s l P' Hp IH | P Q s l Q' Hp IH | P Q t t' c v P' Q' Hp1 IH1 Hp2 IH2 | P Q t t' c v P' Q' Hp1 IH1 Hp2 IH2 | P s l P' Hp IH | t X P]; intros f; simpl in *.
  - constructor.
  - rewrite (proj1 ren_subst). constructor.
  - by constructor.
  - rewrite (proj1 ren_subst). by constructor.
  - by constructor.
  - apply pr_sumL, IH.
  - apply pr_sumR, IH.
  - by constructor.
  - by apply pr_iteT.
  - by apply pr_iteF.
  - by apply pr_parL.
  - by apply pr_parR.
  - by eapply pr_syncL; [apply IH1|apply IH2].
  - by eapply pr_syncR; [apply IH1|apply IH2].
  - apply pr_res. rewrite <- ren_lbl_lift_S. apply IH.
  - rewrite (proj1 (ren_pr_subst X)). simpl. constructor.
Qed.

(* The converse, for an injective renaming. *)
Lemma prog_step_ren_inv f :
  (∀ i j, f i = f j → i = j) →
  ∀ P s l' X, ren f P ⟶{l'}[s] X →
  ∃ l P', l' = ren_lbl f l ∧ X = ren f P' ∧ P ⟶{l}[s] P'.
Proof.
  intros Hf P s l' X Hs. remember (ren f P) as RP eqn:ER. revert f Hf P ER.
  induction Hs as [t P | t c v P | t E es qs P Hq | t M es qs n P Hq | t es qs P Hq | g1 g2 s l P' Hgs IH | g1 g2 s l P' Hgs IH | t c e v Hev | e P Q s l P' Hev Hst IH | e P Q s l Q' Hev Hst IH | P Q s l P' Hst IH | P Q s l Q' Hst IH | P Q t t' c v P' Q' Hst1 IH1 Hst2 IH2 | P Q t t' c v P' Q' Hst1 IH1 Hst2 IH2 | P s l P' Hst IH | t X P]; intros f Hf P0 ER;
    destruct P0 as [t0 c0 e0|e0 P1 P2|P1 P2|P1|X0|t0 X0 P1|g0]; simpl in ER; simplify_eq.
  all: try (destruct g0 as [es0| |𝜆0 P0|g1' g2']; simpl in *; simplify_eq).
  all: try (destruct 𝜆0; simpl in *; simplify_eq).
  - exists τ, P0. split_and!; [done|done|constructor].
  - exists (c0 ? v), (P0 ⟦ v ⟧).
    split_and!; [done|by rewrite (proj1 ren_subst)|constructor].
  - exists (E0 ⦅qs⦆), P0. split_and!; [done|done|by constructor].
  - exists (M0 ⦅qs⦆? n), (P0 ⟦ VNat n ⟧).
    split_and!; [done|by rewrite (proj1 ren_subst)|by constructor].
  - exists (init ⦅qs⦆), P0. split_and!; [done|done|by constructor].
  - destruct (IH f Hf (PG g1') eq_refl) as (l0 & P'0 & -> & -> & Hg). exists l0, P'0. split_and!; [done|done|by apply pr_sumL].
  - destruct (IH f Hf (PG g2') eq_refl) as (l0 & P'0 & -> & -> & Hg). exists l0, P'0. split_and!; [done|done|by apply pr_sumR].
  - exists (c0 ! v), 𝟘. split_and!; [done|done|by constructor].
  - destruct (IH f Hf P1 eq_refl) as (l0 & P'0 & -> & -> & Hp).
    exists l0, P'0. split_and!; [done|done|by apply pr_iteT].
  - destruct (IH f Hf P2 eq_refl) as (l0 & P'0 & -> & -> & Hp).
    exists l0, P'0. split_and!; [done|done|by apply pr_iteF].
  - destruct (IH f Hf P1 eq_refl) as (l0 & P'0 & -> & -> & Hp).
    exists l0, (P'0 ∥ P2). split_and!; [done|done|by apply pr_parL].
  - destruct (IH f Hf P2 eq_refl) as (l0 & P'0 & -> & -> & Hp).
    exists l0, (P1 ∥ P'0). split_and!; [done|done|by apply pr_parR].
  - destruct (IH1 f Hf P1 eq_refl) as (l1 & P1' & E1 & -> & Hp1).
    destruct (IH2 f Hf P2 eq_refl) as (l2 & P2' & E2 & -> & Hp2).
    destruct l1 as [[c1 v1|c1 v1| | |]|]; simpl in E1; simplify_eq.
    destruct l2 as [[c2 v2|c2 v2| | |]|]; simpl in E2; simplify_eq.
    assert (c1 = c2) by (eapply ren_chan_inj; [exact Hf|congruence]). subst.
    exists τ, (P1' ∥ P2'). split_and!; [done|done|by eapply pr_syncL].
  - destruct (IH1 f Hf P1 eq_refl) as (l1 & P1' & E1 & -> & Hp1).
    destruct (IH2 f Hf P2 eq_refl) as (l2 & P2' & E2 & -> & Hp2).
    destruct l1 as [[c1 v1|c1 v1| | |]|]; simpl in E1; simplify_eq.
    destruct l2 as [[c2 v2|c2 v2| | |]|]; simpl in E2; simplify_eq.
    assert (c1 = c2) by (eapply ren_chan_inj; [exact Hf|congruence]). subst.
    exists τ, (P1' ∥ P2'). split_and!; [done|done|by eapply pr_syncR].
  - destruct (IH (lift f) (lift_inj f Hf) P1 eq_refl) as (l0 & P'0 & E0 & -> & Hp).
    destruct l0 as [[[c0|[|i]] v0|[c0|[|i]] v0|E' qs|M qs n|qs0]|]; simpl in E0;
      destruct l as [[[c1|i1] v1|[c1|i1] v1|E1 qs1|M1 qs1 n1|qs2]|]; simpl in E0; simplify_eq.
    + exists ((CName c0) ! v0), (ν P'0). split_and!; [done|done|by apply pr_res].
    + exists ((CIdx i) ! v0), (ν P'0). split_and!; [done|done|by apply pr_res].
    + exists ((CName c0) ? v0), (ν P'0). split_and!; [done|done|by apply pr_res].
    + exists ((CIdx i) ? v0), (ν P'0). split_and!; [done|done|by apply pr_res].
    + exists (E' ⦅qs⦆), (ν P'0). split_and!; [done|done|by apply pr_res].
    + exists (M ⦅qs⦆? n), (ν P'0). split_and!; [done|done|by apply pr_res].
    + exists (init ⦅qs0⦆), (ν P'0). split_and!; [done|done|by apply pr_res].
    + exists τ, (ν P'0). split_and!; [done|done|by apply pr_res].
  - exists τ, (P1 ⦃ t0 ∶ rec X0 ∙ P1 // X0 ⦄).
    split_and!; [done| |constructor]. rewrite (proj1 (ren_pr_subst X0)). done.
Qed.
(* end hide *)
