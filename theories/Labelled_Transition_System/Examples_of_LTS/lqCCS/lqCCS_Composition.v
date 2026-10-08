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

(** * lqCCS: (Prog, Mem) ∥ Test

    The system observed by must-testing.  A program [P] runs with the quantum
    memory [ρ]; an observer [Q] runs in parallel.  The observer has *no
    memory of its own*: its quantum operations are requests to the same
    memory, exactly as the program's.  In lqCCS this is the configuration
    [⌊ρ, P ∥ Q⌉]; keeping the two sides apart lets the observer language and
    the memory model vary.

    Configurations are pairs [(P, Q)]; the memory is the *weight* of a
    configuration in a quantum distribution (Section 6 of arXiv:2604.23756),
    so a measurement step goes to a distribution, one component per outcome,
    weighted by the unnormalised branch [M_k(ρ)].

    Steps of the composition, each selected by a scheduler:
    - a silent step of [P] or of [Q] (including their internal
      synchronisations);
    - a request of [P] or of [Q] to the memory: a superoperator, or a
      measurement whose outcomes the requester all accepts;
    - a communication between [P] and [Q].  A received qubit must exist in
      the memory; that the receiver does not already own it is checked by the
      program LTS (rule Recv). *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list.
From TestingTheory Require Import Lifted Paths States pMust_almost_sure pMust_smyth lqCCS_Quantum.
From TestingTheory Require Import lqCCS_Syntax lqCCS_Program.

Notation conf := (proc * proc)%type.

Section Composition.
  Context `{QM : QuantumModel}.

  (** The measurement of [M] on [qs] as a distribution: the outcome [k] goes
      to [f k] with weight [M_k(ρ)]. *)
  Definition meas_dist {C} (M : meas) (qs : list qubit) (ρ : St)
    (f : nat → C) : dist C :=
    dsum (map (λ k, dpoint (f (code _ k)) (meas_branch M qs k ρ))
              (outs (meas_of M qs))).

  Inductive cstep (ρ : St) : conf → Sched → dist conf → Prop :=
  (** silent steps *)
  | cs_tauL P Q s P' :
      pstep P (LTau s) P' → cstep ρ (P, Q) s (dpoint (P', Q) ρ)
  | cs_tauR P Q s Q' :
      pstep Q (LTau s) Q' → cstep ρ (P, Q) s (dpoint (P, Q') ρ)
  (** superoperators *)
  | cs_opL P Q t E qs P' :
      pstep P (LAct t (AOp E qs)) P' →
      cstep ρ (P, Q) (STag t) (dpoint (P', Q) (sop_apply E qs ρ))
  | cs_opR P Q t E qs Q' :
      pstep Q (LAct t (AOp E qs)) Q' →
      cstep ρ (P, Q) (STag t) (dpoint (P, Q') (sop_apply E qs ρ))
  (** measurements *)
  | cs_measL P Q t M qs x P' :
      pstep P (LAct t (AMeas M qs x)) P' →
      cstep ρ (P, Q) (STag t) (meas_dist M qs ρ (λ k, (subst P' x (VNat k), Q)))
  | cs_measR P Q t M qs x Q' :
      pstep Q (LAct t (AMeas M qs x)) Q' →
      cstep ρ (P, Q) (STag t) (meas_dist M qs ρ (λ k, (P, subst Q' x (VNat k))))
  (** communications between the program and the observer *)
  | cs_comLR P Q t t' c v P' Q' :
      pstep P (LAct t (AOut c v)) P' → pstep Q (LAct t' (AIn c v)) Q' →
      cstep ρ (P, Q) (SPair t t') (dpoint (P', Q') ρ)
  | cs_comRL P Q t t' c v P' Q' :
      pstep P (LAct t (AIn c v)) P' → pstep Q (LAct t' (AOut c v)) Q' →
      cstep ρ (P, Q) (SPair t t') (dpoint (P', Q') ρ).

  (** The observer has succeeded. *)
  Definition conf_good (C : conf) : Prop := good C.2.

  #[global] Instance conf_good_dec C : Decision (conf_good C).
  Proof. unfold conf_good. apply _. Defined.

  (** The initial distribution of [P] in memory [ρ] tested by [Q]. *)
  Definition compose_lq (Pρ : proc * St) (Q : proc) : dist conf :=
    dpoint (Pρ.1, Q) Pρ.2.
End Composition.

(** ** lqCCS as a scheduled system, and its two must preorders

    A process under test is a program with its initial memory [(P, ρ)]; an
    observer is a program alone. *)

#[global] Instance lqCCS_SchedSts `{QuantumModel} : SchedSts conf Sched :=
  {| sstep := cstep; psuccess := conf_good |}.

#[global] Instance lqCCS_pTesting `{QuantumModel} : pTesting (proc * St) proc conf Sched :=
  {| compose := compose_lq |}.

Definition lq_pre_as `{QuantumModel} (p q : proc * St) : Prop := p ⊑ₐₛ q.
Definition lq_pre_sm `{QuantumModel} (p q : proc * St) : Prop := p ⊑ₛₘ q.
