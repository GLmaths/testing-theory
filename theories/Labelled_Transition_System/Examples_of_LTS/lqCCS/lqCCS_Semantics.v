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
(* * lqCCS: the density operator semantics

    The semantics of Figure 9 of Ceragioli, Gadducci, Lomurno, Tedeschi
    (arXiv:2604.23756), for a single weighted process [ρ • P]: it steps to a
    quantum distribution of processes.  Quantum operations are silent steps
    that change the weight; a measurement splits it into its branches.

    This is the reference semantics: [lqCCS_Harmony.v] shows that the
    composition [(Prog, Mem) ∥ Test] of [lqCCS_Composition.v] has the same
    silent steps as [ρ • (P ∥ Q)].

    Only the single-element rules are given (the last three rules of
    Figure 9, deadlock and convex combination, are the lifting [dstep] of
    [pMust_almost_sure.v]).  Outputs are asynchronous, as in the syntax. *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list.
From TestingTheory Require Import Lifted Paths States pMust_almost_sure lqCCS_Quantum.
From TestingTheory Require Import lqCCS_Syntax lqCCS_Program lqCCS_Composition.
Section Semantics.
  Context `{QM : QuantumModel}.

  (* Steps of a weighted guard. *)
  Inductive qgstep (ρ : St) : guard → plbl → dist proc → Prop :=
  | qg_tau t P :
      qgstep ρ (GPre (PTau t) P) (LTau (STag t)) (dpoint P ρ)
  | qg_taupair t t' P :
      qgstep ρ (GPre (PTauPair t t') P) (LTau (SPair t t')) (dpoint P ρ)
  | qg_op t E es qs P :
      eval_qubits es = Some qs →
      qgstep ρ (GPre (POp t E es) P) (LTau (STag t)) (dpoint P (sop_apply E qs ρ))
  | qg_meas t M es x qs P :
      eval_qubits es = Some qs →
      qgstep ρ (GPre (PMeas t M es x) P) (LTau (STag t))
        (meas_dist M qs ρ (λ k, subst P x (VNat k)))
  | qg_recv t c x v P :
      qgstep ρ (GPre (PRecv t c x) P) (LAct t (AIn c v)) (dpoint (subst P x v) ρ)
  | qg_sumL g1 g2 l Δ :
      qgstep ρ g1 l Δ → qgstep ρ (GSum g1 g2) l Δ
  | qg_sumR g1 g2 l Δ :
      qgstep ρ g2 l Δ → qgstep ρ (GSum g1 g2) l Δ.

  Inductive qstep (ρ : St) : proc → plbl → dist proc → Prop :=
  | qs_guard g l Δ :
      qgstep ρ g l Δ → qstep ρ (PG g) l Δ
  | qs_send t c e v :
      eval e = Some v →
      qstep ρ (PSend t c e) (LAct t (AOut c v)) (dpoint (PG (GNil [])) ρ)
  | qs_iteT e P Q l Δ :
      eval e = Some (VBool true) → qstep ρ P l Δ → qstep ρ (PIte e P Q) l Δ
  | qs_iteF e P Q l Δ :
      eval e = Some (VBool false) → qstep ρ Q l Δ → qstep ρ (PIte e P Q) l Δ
  | qs_parL P Q l Δ :
      qstep ρ P l Δ →
      qstep ρ (PPar P Q) l (dmap (λ P', PPar P' Q) Δ)
  | qs_parR P Q l Δ :
      qstep ρ Q l Δ →
      qstep ρ (PPar P Q) l (dmap (λ Q', PPar P Q') Δ)
  | qs_syncL P Q t t' c v P' Q' :
      qstep ρ P (LAct t (AOut c v)) (dpoint P' ρ) →
      qstep ρ Q (LAct t' (AIn c v)) (dpoint Q' ρ) →
      qstep ρ (PPar P Q) (LTau (SPair t t')) (dpoint (PPar P' Q') ρ)
  | qs_syncR P Q t t' c v P' Q' :
      qstep ρ P (LAct t (AIn c v)) (dpoint P' ρ) →
      qstep ρ Q (LAct t' (AOut c v)) (dpoint Q' ρ) →
      qstep ρ (PPar P Q) (LTau (SPair t t')) (dpoint (PPar P' Q') ρ)
  | qs_res P c l Δ :
      ¬ on_chan c l → qstep ρ P l Δ →
      qstep ρ (PRes P c) l (dmap (λ P', PRes P' c) Δ).
End Semantics.
(* end hide *)
