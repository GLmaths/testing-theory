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
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Helper_substitution.De_Brujin_lemmas.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

(* ** Choices [s ::= ε | t | {t, t'}] and their product *)

Section LqP.
  Context `{LP : lqCCS_Parameters}.

Inductive choice : Type :=
| CEps
| CTag (t : tag)
| CPair (t t' : tag).

(* The unordered pair [{t, t'}], as a sorted pair. *)
Definition cpair (t t' : tag) : choice := CPair (Nat.min t t') (Nat.max t t').

Coercion CTag : tag >-> choice.
Notation "⦗ t , t' ⦘" := (cpair t t') (at level 0, format "⦗ t ,  t' ⦘") : lqccs_scope.

Lemma cpair_comm t t' : cpair t t' = cpair t' t.
Proof. unfold cpair. by rewrite Nat.min_comm, Nat.max_comm. Qed.

Inductive cmul : choice → choice → choice → Prop :=
| cmul_eps_l c : cmul CEps c c
| cmul_eps_r c : cmul c CEps c
| cmul_tags t t' : cmul (CTag t) (CTag t') ⦗t, t'⦘.

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

Notation "L1 ∣[ R ] L2" := (par_step L1 L2 R) (at level 60, format "L1  ∣[ R ]  L2").

(* ** The program LTS *)

Inductive prog_action : Type :=
| PrOut (c : channel) (v : val)
| PrIn (c : channel) (v : val)
| PrOp (E : sop) (qs : list qubit)
| PrMeas (M : meas) (qs : list qubit) (n : nat)
| PrInit (q : qubit).

Notation "c ! v" := (ActExt (PrOut c v)) (at level 30, v at level 9) : lqccs_scope.
Notation "c ? v" := (ActExt (PrIn c v)) (at level 30, v at level 9) : lqccs_scope.
Notation "E ⦅ qs ⦆" := (ActExt (PrOp E qs)) (at level 30, format "E  ⦅ qs ⦆") : lqccs_scope.
Notation "M ⦅ qs ⦆? n" := (ActExt (PrMeas M qs n)) (at level 30, n at level 9, format "M  ⦅ qs ⦆?  n") : lqccs_scope.
Notation "'init' ⦅ q ⦆" := (ActExt (PrInit q)) (at level 30, format "'init'  ⦅ q ⦆") : lqccs_scope.

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

Reserved Notation "P ⟶{ l }[ s ] P'" (at level 70, format "P  ⟶{ l }[ s ]  P'").
Reserved Notation "g ⟶ᵍ{ l }[ s ] P'" (at level 70, format "g  ⟶ᵍ{ l }[ s ]  P'").

(* ** Transitions of a program and of a guard *)

Inductive prog_step : proc → choice → Labels prog_action → proc → Prop :=
| pr_guard (g : guard) s l P' :
    g ⟶ᵍ{l}[s] P' → g ⟶{l}[s] P'
| pr_send t c e v :
    〚 e 〛 = v → t ∶ c ! e ⟶{c ! v}[t] 𝟘
| pr_iteT e P Q s l P' :
    〚 e 〛 = true → P ⟶{l}[s] P' → If e Then P Else Q ⟶{l}[s] P'
| pr_iteF e P Q s l Q' :
    〚 e 〛 = false → Q ⟶{l}[s] Q' → If e Then P Else Q ⟶{l}[s] Q'
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
| pr_rec t P :
    t ∶ rec ∙ P ⟶{τ}[t] (P ⁅ (t ∶ rec ∙ P)↑ ⁆ₚ)
with prog_gstep : guard → choice → Labels prog_action → proc → Prop :=
| pg_tau t P :
    (t ∶ 𝛕 ∙ P) ⟶ᵍ{τ}[t] P
| pg_recv t c v P :
    (t ∶ c ? ∙ P) ⟶ᵍ{c ? v}[t] (P ⁅ v ⁆ᵥ)
| pg_op t E es qs P :
    eval_qubits es = Some qs →
    (t ∶ E ⦅es⦆ ∙ P) ⟶ᵍ{E ⦅qs⦆}[t] P
| pg_meas t M es qs n P :
    eval_qubits es = Some qs →
    (t ∶ M ⦅es ▷⦆ ∙ P) ⟶ᵍ{M ⦅qs⦆? n}[t] (P ⁅ VNat n ⁆ᵥ)
| pg_init t e q P :
    eval_qubit e = Some q →
    (t ∶ e := |0⟩ ∙ P) ⟶ᵍ{init ⦅q⦆}[t] P
| pg_sumL (g1 g2 : guard) s l P' :
    g1 ⟶ᵍ{l}[s] P' → (g1 + g2) ⟶ᵍ{l}[s] P'
| pg_sumR (g1 g2 : guard) s l P' :
    g2 ⟶ᵍ{l}[s] P' → (g1 + g2) ⟶ᵍ{l}[s] P'
where "P ⟶{ l }[ s ] P'" := (prog_step P s l P') : lqccs_scope
and "g ⟶ᵍ{ l }[ s ] P'" := (prog_gstep g s l P') : lqccs_scope.

Lemma prog_step_guard (g : guard) s l P' : g ⟶{l}[s] P' ↔ g ⟶ᵍ{l}[s] P'.
Proof. split; [by inversion 1|apply pr_guard]. Qed.

Lemma pr_tau t P : (t ∶ 𝛕 ∙ P) ⟶{τ}[t] P.
Proof. apply pr_guard, pg_tau. Qed.

Lemma pr_recv t c v P : (t ∶ c ? ∙ P) ⟶{c ? v}[t] (P ⁅ v ⁆ᵥ).
Proof. apply pr_guard, pg_recv. Qed.

Lemma pr_op t E es qs P : eval_qubits es = Some qs → (t ∶ E ⦅es⦆ ∙ P) ⟶{E ⦅qs⦆}[t] P.
Proof. intros H. by apply pr_guard, pg_op. Qed.

Lemma pr_meas t M es qs n P :
  eval_qubits es = Some qs → (t ∶ M ⦅es ▷⦆ ∙ P) ⟶{M ⦅qs⦆? n}[t] (P ⁅ VNat n ⁆ᵥ).
Proof. intros H. by apply pr_guard, pg_meas. Qed.

Lemma pr_init t e q P : eval_qubit e = Some q → (t ∶ e := |0⟩ ∙ P) ⟶{init ⦅q⦆}[t] P.
Proof. intros H. by apply pr_guard, pg_init. Qed.

Lemma pr_sumL (g1 g2 : guard) s l P' : g1 ⟶{l}[s] P' → (g1 + g2) ⟶{l}[s] P'.
Proof. intros H%prog_step_guard. by apply pr_guard, pg_sumL. Qed.

Lemma pr_sumR (g1 g2 : guard) s l P' : g2 ⟶{l}[s] P' → (g1 + g2) ⟶{l}[s] P'.
Proof. intros H%prog_step_guard. by apply pr_guard, pg_sumR. Qed.

(* ** The memory LTS and the synchronisation predicates *)

(* [c!v sync c?v] and [c?v sync c!v] *)
Inductive sync_chan : prog_action → prog_action → Prop :=
| sync_out_in c v : sync_chan (PrOut c v) (PrIn c v)
| sync_in_out c v : sync_chan (PrIn c v) (PrOut c v).

Reserved Notation "⟨ ρ , P ⟩ ⟶{ l }[ s ] ⟨ ρ' , P' ⟩" (at level 70, format "⟨ ρ ,  P ⟩  ⟶{ l }[ s ]  ⟨ ρ' ,  P' ⟩").
Reserved Notation "ρ ⟶ₘ{ μ } ρ'" (at level 70, format "ρ  ⟶ₘ{ μ }  ρ'").
Reserved Notation "⟨ ρ , P ⟩ ⟶ₘ{ μ } ⟨ ρ' , P' ⟩" (at level 70, format "⟨ ρ ,  P ⟩  ⟶ₘ{ μ }  ⟨ ρ' ,  P' ⟩").
Reserved Notation "M ⦅ qs ⦆! n" (at level 30, n at level 9, format "M  ⦅ qs ⦆!  n").

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
  | sync_init q : sync (init_act q) (PrInit q).

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
      ⟨ρ, t ∶ c ? ∙ P⟩ ⟶{c ? v}[t] ⟨ρ, P ⁅ v ⁆ᵥ⟩
  | co_op t E es qs P :
      eval_qubits es = Some qs →
      ⟨ρ, t ∶ E ⦅es⦆ ∙ P⟩ ⟶{E ⦅qs⦆}[t] ⟨ρ, P⟩
  | co_meas t M es qs n P :
      eval_qubits es = Some qs →
      ⟨ρ, t ∶ M ⦅es ▷⦆ ∙ P⟩ ⟶{M ⦅qs⦆? n}[t] ⟨ρ, P ⁅ VNat n ⁆ᵥ⟩
  | co_init t e q P :
      eval_qubit e = Some q →
      ⟨ρ, t ∶ e := |0⟩ ∙ P⟩ ⟶{init ⦅q⦆}[t] ⟨ρ, P⟩
  | co_sumL (g1 g2 : guard) s l ρ' P' :
      ⟨ρ, g1⟩ ⟶{l}[s] ⟨ρ', P'⟩ → ⟨ρ, g1 + g2⟩ ⟶{l}[s] ⟨ρ', P'⟩
  | co_sumR (g1 g2 : guard) s l ρ' P' :
      ⟨ρ, g2⟩ ⟶{l}[s] ⟨ρ', P'⟩ → ⟨ρ, g1 + g2⟩ ⟶{l}[s] ⟨ρ', P'⟩
  | co_send t c e v :
      〚 e 〛 = v → ⟨ρ, t ∶ c ! e⟩ ⟶{c ! v}[t] ⟨ρ, 𝟘⟩
  | co_iteT e P Q s l ρ' P' :
      〚 e 〛 = true → ⟨ρ, P⟩ ⟶{l}[s] ⟨ρ', P'⟩ → ⟨ρ, If e Then P Else Q⟩ ⟶{l}[s] ⟨ρ', P'⟩
  | co_iteF e P Q s l ρ' Q' :
      〚 e 〛 = false → ⟨ρ, Q⟩ ⟶{l}[s] ⟨ρ', Q'⟩ → ⟨ρ, If e Then P Else Q⟩ ⟶{l}[s] ⟨ρ', Q'⟩
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
  | co_rec t P :
      ⟨ρ, t ∶ rec ∙ P⟩ ⟶{τ}[t] ⟨ρ, P ⁅ (t ∶ rec ∙ P)↑ ⁆ₚ⟩
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
  | co_initCom P s q ρ' P' :
      ⟨ρ, P⟩ ⟶{init ⦅q⦆}[s] ⟨ρ, P'⟩ →
      ⟨ρ, P⟩ ⟶ₘ{init_act q} ⟨ρ', P⟩ →
      ⟨ρ, P⟩ ⟶{τ}[s] ⟨ρ', P'⟩
  where "⟨ ρ , P ⟩ ⟶{ l }[ s ] ⟨ ρ' , P' ⟩" := (conf_step ρ P s (inl l) ρ' P') : lqccs_scope
  and "⟨ ρ , P ⟩ ⟶ₘ{ μ } ⟨ ρ' , P' ⟩" := (conf_step ρ P CEps (inr (μ : mem_action)) ρ' P') : lqccs_scope.
End Memory.

Notation "M ⦅ qs ⦆! n" := (MeMeas M qs n) : lqccs_scope.
Notation "ρ ⟶ₘ{ μ } ρ'" := (mem_step ρ CEps (ActExt (μ : mem_action)) ρ')
  (at level 70, only parsing) : lqccs_scope.
Notation "ρ ⟶ₘ{ μ } ρ'" := (mem_step ρ CEps (ActExt μ) ρ')
  (at level 70, only printing, format "ρ  ⟶ₘ{ μ }  ρ'") : lqccs_scope.
Notation "⟨ ρ , P ⟩ ⟶{ l }[ s ] ⟨ ρ' , P' ⟩" := (conf_step ρ P s (inl l) ρ' P') (at level 70, format "⟨ ρ ,  P ⟩  ⟶{ l }[ s ]  ⟨ ρ' ,  P' ⟩") : lqccs_scope.
Notation "⟨ ρ , P ⟩ ⟶ₘ{ μ } ⟨ ρ' , P' ⟩" := (conf_step ρ P CEps (inr (μ : mem_action)) ρ' P')
  (at level 70, only parsing) : lqccs_scope.
Notation "⟨ ρ , P ⟩ ⟶ₘ{ μ } ⟨ ρ' , P' ⟩" := (conf_step ρ P CEps (inr μ) ρ' P')
  (at level 70, only printing, format "⟨ ρ ,  P ⟩  ⟶ₘ{ μ }  ⟨ ρ' ,  P' ⟩") : lqccs_scope.
Notation "'𝔻ₘₑₘ'" := sync : lqccs_scope.
Notation "ρ ∣ P ⟶{ l }[ s ] ρ' ∣ P'" :=
  (par_step mem_step prog_step sync (ρ, P) s l (ρ', P'))
  (at level 70, P at level 25, ρ' at level 25, P' at level 25, format "ρ  ∣  P  ⟶{ l }[ s ]  ρ'  ∣  P'") : lqccs_scope.

(* ** Facts on the program LTS *)

Lemma prog_gstep_not_out (g : guard) s c v P' : ¬ g ⟶{c ! v}[s] P'.
Proof.
  intros Hs%prog_step_guard. remember (c ! v) as l eqn:El. induction Hs; simplify_eq; auto.
Qed.

Lemma prog_gstep_tag g s l P' : g ⟶ᵍ{l}[s] P' → ∃ t, s = CTag t.
Proof. induction 1; eauto. Qed.

Lemma prog_step_ext_choice P s a P' : P ⟶{ActExt a}[s] P' → ∃ t, s = CTag t.
Proof.
  intros Hs. remember (ActExt a) as l eqn:El. revert a El.
  induction Hs as [g s l P' Hg| | | | | | | | |]; intros a0 El; simplify_eq; eauto using prog_gstep_tag.
Qed.

End LqP.

Notation "⦗ t , t' ⦘" := (cpair t t') (at level 0, format "⦗ t ,  t' ⦘") : lqccs_scope.
Notation "L1 ∣[ R ] L2" := (par_step L1 L2 R) (at level 60, format "L1  ∣[ R ]  L2").
Notation "c ! v" := (ActExt (PrOut c v)) (at level 30, v at level 9) : lqccs_scope.
Notation "c ? v" := (ActExt (PrIn c v)) (at level 30, v at level 9) : lqccs_scope.
Notation "E ⦅ qs ⦆" := (ActExt (PrOp E qs)) (at level 30, format "E  ⦅ qs ⦆") : lqccs_scope.
Notation "M ⦅ qs ⦆? n" := (ActExt (PrMeas M qs n)) (at level 30, n at level 9, format "M  ⦅ qs ⦆?  n") : lqccs_scope.
Notation "'init' ⦅ q ⦆" := (ActExt (PrInit q)) (at level 30, format "'init'  ⦅ q ⦆") : lqccs_scope.
Reserved Notation "P ⟶{ l }[ s ] P'" (at level 70, format "P  ⟶{ l }[ s ]  P'").
Reserved Notation "g ⟶ᵍ{ l }[ s ] P'" (at level 70, format "g  ⟶ᵍ{ l }[ s ]  P'").
Notation "g ⟶ᵍ{ l }[ s ] P'" := (prog_gstep g s l P') : lqccs_scope.
Notation "P ⟶{ l }[ s ] P'" := (prog_step P s l P') : lqccs_scope.
Reserved Notation "⟨ ρ , P ⟩ ⟶{ l }[ s ] ⟨ ρ' , P' ⟩" (at level 70, format "⟨ ρ ,  P ⟩  ⟶{ l }[ s ]  ⟨ ρ' ,  P' ⟩").
Reserved Notation "ρ ⟶ₘ{ μ } ρ'" (at level 70, format "ρ  ⟶ₘ{ μ }  ρ'").
Reserved Notation "⟨ ρ , P ⟩ ⟶ₘ{ μ } ⟨ ρ' , P' ⟩" (at level 70, format "⟨ ρ ,  P ⟩  ⟶ₘ{ μ }  ⟨ ρ' ,  P' ⟩").
Reserved Notation "M ⦅ qs ⦆! n" (at level 30, n at level 9, format "M  ⦅ qs ⦆!  n").
Notation "M ⦅ qs ⦆! n" := (MeMeas M qs n) : lqccs_scope.
Notation "ρ ⟶ₘ{ μ } ρ'" := (mem_step ρ CEps (ActExt (μ : mem_action)) ρ')
  (at level 70, only parsing) : lqccs_scope.
Notation "ρ ⟶ₘ{ μ } ρ'" := (mem_step ρ CEps (ActExt μ) ρ')
  (at level 70, only printing, format "ρ  ⟶ₘ{ μ }  ρ'") : lqccs_scope.
Notation "⟨ ρ , P ⟩ ⟶{ l }[ s ] ⟨ ρ' , P' ⟩" := (conf_step ρ P s (inl l) ρ' P') (at level 70, format "⟨ ρ ,  P ⟩  ⟶{ l }[ s ]  ⟨ ρ' ,  P' ⟩") : lqccs_scope.
Notation "⟨ ρ , P ⟩ ⟶ₘ{ μ } ⟨ ρ' , P' ⟩" := (conf_step ρ P CEps (inr (μ : mem_action)) ρ' P')
  (at level 70, only parsing) : lqccs_scope.
Notation "⟨ ρ , P ⟩ ⟶ₘ{ μ } ⟨ ρ' , P' ⟩" := (conf_step ρ P CEps (inr μ) ρ' P')
  (at level 70, only printing, format "⟨ ρ ,  P ⟩  ⟶ₘ{ μ }  ⟨ ρ' ,  P' ⟩") : lqccs_scope.
Notation "'𝔻ₘₑₘ'" := sync : lqccs_scope.
Notation "ρ ∣ P ⟶{ l }[ s ] ρ' ∣ P'" :=
  (par_step mem_step prog_step sync (ρ, P) s l (ρ', P'))
  (at level 70, P at level 25, ρ' at level 25, P' at level 25, format "ρ  ∣  P  ⟶{ l }[ s ]  ρ'  ∣  P'") : lqccs_scope.

(* end hide *)
