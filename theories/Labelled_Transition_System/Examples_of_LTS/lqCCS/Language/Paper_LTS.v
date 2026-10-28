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
From stdpp Require Import base countable decidable list.
From TestingTheory Require Import lqCCS.Harmony_Lemma.Lifted lqCCS.Harmony_Lemma.Paths lqCCS.Harmony_Lemma.States pMust_almost_sure lqCCS.Language.Quantum.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.Program.

#[local] Open Scope lqccs_scope.

Inductive prog_action : Type :=
| PrOut (c : chan) (v : val)
| PrIn (c : chan) (v : val)
| PrOp (E : sop) (qs : list qubit)
| PrMeas (M : meas) (qs : list qubit) (n : nat).

Inductive prog_label : Type :=
| PrTau (s : Sched)
| PrAct (t : tag) (a : prog_action).

Definition chan_action (a : prog_action) : Prop :=
  ∃ c v, a = PrOut c v ∨ a = PrIn c v.

Definition chan_label (c : chan) (l : prog_label) : Prop :=
  ∃ t v, l = PrAct t (PrOut c v) ∨ l = PrAct t (PrIn c v).

Inductive prog_gstep : guard → prog_label → proc → Prop :=
| pg_tau t P :
    prog_gstep (PTau t ∙ P) (PrTau (STag t)) P
| pg_recv t c x v P :
    prog_gstep (PRecv t c x ∙ P) (PrAct t (PrIn c v)) (P ⟦ v // x ⟧)
| pg_op t E es qs P :
    eval_qubits es = Some qs →
    prog_gstep (POp t E es ∙ P) (PrAct t (PrOp E qs)) P
| pg_meas t M es x qs n P :
    eval_qubits es = Some qs →
    prog_gstep (PMeas t M es x ∙ P) (PrAct t (PrMeas M qs n)) (P ⟦ VNat n // x ⟧)
| pg_sumL g1 g2 l P' :
    prog_gstep g1 l P' → prog_gstep (g1 ⊕ g2) l P'
| pg_sumR g1 g2 l P' :
    prog_gstep g2 l P' → prog_gstep (g1 ⊕ g2) l P'.

Inductive prog_step : proc → prog_label → proc → Prop :=
| pr_guard g l P' :
    prog_gstep g l P' → prog_step (PG g) l P'
| pr_send t c e v :
    eval e = Some v → prog_step (PSend t c e) (PrAct t (PrOut c v)) 𝟘
| pr_iteT e P Q l P' :
    eval e = Some (VBool true) → prog_step P l P' → prog_step (PIte e P Q) l P'
| pr_iteF e P Q l Q' :
    eval e = Some (VBool false) → prog_step Q l Q' → prog_step (PIte e P Q) l Q'
| pr_parL P Q l P' :
    prog_step P l P' → prog_step (P ∥ Q) l (P' ∥ Q)
| pr_parR P Q l Q' :
    prog_step Q l Q' → prog_step (P ∥ Q) l (P ∥ Q')
| pr_syncL P Q t t' c v P' Q' :
    prog_step P (PrAct t (PrOut c v)) P' → prog_step Q (PrAct t' (PrIn c v)) Q' →
    prog_step (P ∥ Q) (PrTau (SPair t t')) (P' ∥ Q')
| pr_syncR P Q t t' c v P' Q' :
    prog_step P (PrAct t (PrIn c v)) P' → prog_step Q (PrAct t' (PrOut c v)) Q' →
    prog_step (P ∥ Q) (PrTau (SPair t t')) (P' ∥ Q')
| pr_res P c l P' :
    ¬ chan_label c l → prog_step P l P' → prog_step (P \ c) l (P' \ c).

Inductive mem_action : Type :=
| MeOp (E : sop) (qs : list qubit)
| MeMeas (M : meas) (qs : list qubit) (n : nat).

Inductive sync : mem_action → prog_action → Prop :=
| sync_op E qs : sync (MeOp E qs) (PrOp E qs)
| sync_meas M qs n : sync (MeMeas M qs n) (PrMeas M qs n).

Inductive par_label : Type :=
| ParProg (l : prog_label)
| ParMem (b : mem_action).

Section Paper_LTS.
  Context `{QM : QuantumModel}.

  Inductive mem_step : St → mem_action → St → Prop :=
  | me_op ρ E qs :
      mem_step ρ (MeOp E qs) (sop_apply E qs ρ)
  | me_meas ρ M qs (k : Out (meas_of M qs)) :
      mem_step ρ (MeMeas M qs (code _ k)) (meas_branch M qs k ρ).

  Inductive par_step : St * proc → par_label → St * proc → Prop :=
  | par_mem ρ ρ' P b :
      mem_step ρ b ρ' → par_step (ρ, P) (ParMem b) (ρ', P)
  | par_prog ρ P l P' :
      prog_step P l P' → par_step (ρ, P) (ParProg l) (ρ, P')
  | par_sync ρ ρ' P P' t a b :
      prog_step P (PrAct t a) P' → mem_step ρ b ρ' → sync b a →
      par_step (ρ, P) (ParProg (PrTau (STag t))) (ρ', P').

  Inductive conf_gstep (ρ : St) : guard → prog_label → St → proc → Prop :=
  | cg_tau t P :
      conf_gstep ρ (PTau t ∙ P) (PrTau (STag t)) ρ P
  | cg_op t E es qs P :
      eval_qubits es = Some qs →
      conf_gstep ρ (POp t E es ∙ P) (PrTau (STag t)) (sop_apply E qs ρ) P
  | cg_meas t M es x qs (k : Out (meas_of M qs)) P :
      eval_qubits es = Some qs →
      conf_gstep ρ (PMeas t M es x ∙ P) (PrTau (STag t))
        (meas_branch M qs k ρ) (P ⟦ VNat (code _ k) // x ⟧)
  | cg_recv t c x v P :
      conf_gstep ρ (PRecv t c x ∙ P) (PrAct t (PrIn c v)) ρ (P ⟦ v // x ⟧)
  | cg_sumL g1 g2 l ρ' P' :
      conf_gstep ρ g1 l ρ' P' → conf_gstep ρ (g1 ⊕ g2) l ρ' P'
  | cg_sumR g1 g2 l ρ' P' :
      conf_gstep ρ g2 l ρ' P' → conf_gstep ρ (g1 ⊕ g2) l ρ' P'.

  Inductive conf_step (ρ : St) : proc → prog_label → St → proc → Prop :=
  | cs_guard g l ρ' P' :
      conf_gstep ρ g l ρ' P' → conf_step ρ (PG g) l ρ' P'
  | cs_send t c e v :
      eval e = Some v → conf_step ρ (PSend t c e) (PrAct t (PrOut c v)) ρ 𝟘
  | cs_iteT e P Q l ρ' P' :
      eval e = Some (VBool true) → conf_step ρ P l ρ' P' → conf_step ρ (PIte e P Q) l ρ' P'
  | cs_iteF e P Q l ρ' Q' :
      eval e = Some (VBool false) → conf_step ρ Q l ρ' Q' → conf_step ρ (PIte e P Q) l ρ' Q'
  | cs_parL P Q l ρ' P' :
      conf_step ρ P l ρ' P' → conf_step ρ (P ∥ Q) l ρ' (P' ∥ Q)
  | cs_parR P Q l ρ' Q' :
      conf_step ρ Q l ρ' Q' → conf_step ρ (P ∥ Q) l ρ' (P ∥ Q')
  | cs_syncL P Q t t' c v P' Q' :
      conf_step ρ P (PrAct t (PrOut c v)) ρ P' → conf_step ρ Q (PrAct t' (PrIn c v)) ρ Q' →
      conf_step ρ (P ∥ Q) (PrTau (SPair t t')) ρ (P' ∥ Q')
  | cs_syncR P Q t t' c v P' Q' :
      conf_step ρ P (PrAct t (PrIn c v)) ρ P' → conf_step ρ Q (PrAct t' (PrOut c v)) ρ Q' →
      conf_step ρ (P ∥ Q) (PrTau (SPair t t')) ρ (P' ∥ Q')
  | cs_res P c l ρ' P' :
      ¬ chan_label c l → conf_step ρ P l ρ' P' → conf_step ρ (P \ c) l ρ' (P' \ c).
End Paper_LTS.
(* end hide *)
