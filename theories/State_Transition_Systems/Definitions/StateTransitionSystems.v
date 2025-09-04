(*
   Copyright (c) 2024 Nomadic Labs
   Copyright (c) 2024 Paul Laforgue <paul.laforgue@nomadic-labs.com>
   Copyright (c) 2024 Léo Stefanesco <leo.stefanesco@mpi-sws.org>
   Copyright (c) 2025 Gaëtan Lopez <glopez@irif.fr>

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

From Coq.Unicode Require Import Utf8.
From stdpp Require Import countable.
From Must Require Import ActTau gLts FiniteImageLTS.

(**************************************** State Transition System ******************************)

(* Definition of a State Transition System (STS) *)
Class Sts (P: Type) := MkSts {
    sts_step: P → P → Prop;
    sts_state_eqdec: EqDecision P;
    sts_step_decidable: RelDecision sts_step;

    sts_refuses: P → Prop;
    sts_refuses_decidable p : Decision (sts_refuses p);
    sts_refuses_spec1 p : ¬ sts_refuses p → { q | sts_step p q };
    sts_refuses_spec2 p : { q | sts_step p q } → ¬ sts_refuses p;
}.
#[global] Existing Instance sts_state_eqdec.
#[global] Existing Instance sts_step_decidable.
#[global] Existing Instance sts_refuses_decidable.

(* State Transition Systems are Labelled Transition Systems *)

Definition istep `{gLts A} p q := lts_step p τ q.

#[global]
Program Instance sts_of_lts {P A} `{H : ExtAction A} (M: gLts P A): Sts P :=
  {|
    sts_step := istep;
    sts_refuses s := lts_refuses s τ;
  |}.
Next Obligation. intros ??????. apply _. Defined.
Next Obligation. intros ??????. by apply lts_refuses_spec1. Qed.
Next Obligation. intros ??????. by apply lts_refuses_spec2. Qed.

Section sts_executions.
  Context `{Sts P}.

  CoInductive max_exec_from: P → Type :=
  | MExStop x (Hrefuses: sts_refuses x): max_exec_from x
  | MExStep x x' (Hstep: sts_step x x') (η: max_exec_from x'): max_exec_from x.

  CoInductive iexec_from: P → Type :=
  | IExStep x x' (Hstep: sts_step x x') (η: iexec_from x'): iexec_from x.

  Inductive finexec_from: P → Type :=
  | FExSingl x : finexec_from x
  | FExStep x x' (Hstep: bool_decide (sts_step x x')) (η: finexec_from x'): finexec_from x.

  Definition iexec_from_first {x:P} (η: iexec_from x) :=
    match η with IExStep x _ _ _ => x end.

  Record iexec := MkExec {
    iex_start: P;
    iex: iexec_from iex_start;
  }.

  Definition ex_cons x η (Hstep: sts_step x η.(iex_start)) : iexec :=
    MkExec x (IExStep _ _ Hstep η.(iex)).

  Inductive finexec :=
  | FinExNil: finexec
  | FinExNonNil x (ρ: finexec_from x): finexec.

  Definition fex_cons x p :=
    match p with
    | FinExNil => Some $ FinExNonNil x (FExSingl x)
    | FinExNonNil y p =>
        match decide (sts_step x y) with
        | right _ => None
        | left Hstep => Some $ FinExNonNil _ $ FExStep x y (bool_decide_pack _ Hstep) p
        end
    end.

  Fixpoint iex_take_from (n: nat) {x} (η: iexec_from x) : finexec_from x :=
    match n with
    | 0 => FExSingl x
    | S n => match η with IExStep x x' Hstep η' =>
             let p' := iex_take_from n η' in
             FExStep x x' (bool_decide_pack _ Hstep) p'
            end
    end.

  Fixpoint mex_take_from (n: nat) {x} (η: max_exec_from x) : option (finexec_from x) :=
    match n with
    | 0 => Some $ FExSingl x
    | S n => match η with
            | MExStop x Hrefuses => None
            | MExStep x x' Hstep η' =>
                let p' := mex_take_from n η' in
                (λ p', FExStep x x' (bool_decide_pack _ Hstep) p') <$> p'
            end
    end.

  Definition iex_take (n: nat) (η: iexec) : finexec :=
    match n with
    | 0 => FinExNil
    | S n => FinExNonNil η.(iex_start) (iex_take_from n η.(iex))
    end.

  Lemma iex_fex_take_from n {x y η} Hstep:
    iex_take_from (1+n) (IExStep x y Hstep η) = FExStep x y (bool_decide_pack _ Hstep) (iex_take_from n η).
  Proof. revert x y η Hstep. induction n as [|n IHn]; intros x y η Hstep; easy. Qed.

  Lemma iex_fex_take n {x η} Hstep:
    Some $ iex_take (1+n) (ex_cons x η Hstep) = fex_cons x (iex_take n η).
  Proof.
    case n; simpl; [easy|].
    intros ?. destruct (decide (sts_step x (iex_start η))); [|easy].
    do 3 f_equal. assert (ProofIrrel $ bool_decide (sts_step x (iex_start η))) by apply _. naive_solver.
  Qed.

  Fixpoint iex_snoc_from x (ex1: finexec_from x) (a: P) : option (finexec_from x) :=
    match ex1 with
    | FExSingl x =>
        if decide (sts_step x a)
        then Some (FExStep x _ ltac:(eauto) (FExSingl a))
        else None
    | FExStep x x' Hstep η =>
        match iex_snoc_from x' η a with
        | None => None
        | Some p => Some(FExStep x x' Hstep p)
        end
    end.

  Definition iex_snoc (ex1: finexec) (a: P) : option finexec :=
    match ex1 with
    | FinExNil => Some (FinExNonNil _ (FExSingl a))
    | FinExNonNil x η =>
        match iex_snoc_from x η a with
        | None => None
        | Some η => Some (FinExNonNil x η)
        end
    end.

  Fixpoint fex_from_last {x} (p: finexec_from x) : P :=
    match p with
    | FExSingl y => y
    | FExStep _ y _ p' => fex_from_last p'
    end.

  Definition fex_last (p: finexec) : option P :=
    match p with
    | FinExNil => None
    | FinExNonNil _ p' => Some $ fex_from_last p'
    end.

  Definition fex_first (p: finexec) : option P :=
    match p with
    | FinExNil => None
    | FinExNonNil x _ => Some x
    end.

  Lemma fex_snoc_from_valid_last x z ρ:
    sts_step (fex_from_last ρ) z →
    is_Some (iex_snoc_from x ρ z).
  Proof.
    revert z. induction ρ as [| y t Hbstep ρ IH]; intros z Hstep; simpl in *.
    - by destruct (decide (sts_step x z)).
    - by destruct (IH _ Hstep) as [? ->].
  Qed.

  Lemma fex_snoc_valid_last ex y z:
    fex_last ex = Some y →
    sts_step y z →
    is_Some (iex_snoc ex z).
  Proof.
    case ex; [easy|]. simpl. intros ??? Hstep. simplify_eq.
    by destruct (fex_snoc_from_valid_last _ _ _ Hstep) as [? ->].
  Qed.

  Definition finex_singl x := FinExNonNil x (FExSingl x).

  Definition iexec_from_tail {x:P} (η: iexec_from x) : iexec :=
    match η with IExStep x x' _ η => MkExec x' η end.

  Lemma iex_snoc_step x η1 η2 a:
    iex_snoc_from x η1 a = Some η2 →
    fex_from_last η2 = a ∧ sts_step (fex_from_last η1) (fex_from_last η2).
  Proof.
    revert η2 a; induction η1 as [|b c Hstep η1 IHη]; intros η2 a.
    - simpl. destruct (decide (sts_step x a)); [injection 1; intros ?; simplify_eq|]; easy.
    - simpl. destruct (iex_snoc_from c η1 a) as [p|] eqn:Heq;
        [injection 1; intros ?; simplify_eq|easy].
      simpl. by destruct (IHη _ _ Heq) as [??].
  Qed.
End sts_executions.


Class CountableSts P `{Sts P} := MkCsts {
    csts_states_countable: Countable P;
    csts_next_states_countable: ∀ x, Countable (dsig (fun y => sts_step x y));
}.
#[global] Existing Instance csts_states_countable.
#[global] Existing Instance csts_next_states_countable.

#[global]
Instance csts_of_clts {P A} `{gLts P A} (M: CountablegLts P A): CountableSts P.
Proof.
  apply MkCsts.
  - exact clts_states_countable.
  - intros ?. apply clts_next_states_countable.
Defined.