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
(* * lqCCS: denotational semantics of programs

    The denotation of a program is a set of super-operators on the quantum
    memory, in the spirit of Feng and Xu, /Verification of Nondeterministic
    Quantum Programs/ (ASPLOS 2023): a measurement sums its outcomes, a
    nondeterministic choice is a union.  Nondeterminism is resolved by the
    choices of the tagged semantics: [den P w F] says that [F] is a result
    of [P] under the word of choices [w], the same word for every branch of
    a measurement (the /lifted/ model of Feng and Xu, the admissible
    schedulers of lqCCS).  Several transitions with the same choice (the
    same tag twice) give several results, hence a relation.  Recursion is
    unfolded by the silent transition of the program LTS, as the syntactic
    approximations of Unruh, Valiron and Ying (/Reasoning about Parameterized
    Recursive Quantum Programs/, Lemma 3.3): [w] bounds the depth.

    - a program without internal move ([stable]) is finished: [one];
    - a program still running when [w] is exhausted gives nothing: [zero];
    - a silent move keeps the memory; a request composes with the operation
      of the memory; a measurement sums over its outcomes
      [Σ_k F_k ⋅ M_k] ([meas_sum]);
    - a choice that is not enabled is skipped ([den_stay]).

    [⟦P⟧] is the union over all words.  [den_cgr]: congruent programs have
    the same denotation. *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list.
From TestingTheory Require Import ActTau.
From TestingTheory Require Import lqCCS.Language.Algebra lqCCS.Language.Quantum.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.LTS lqCCS.Language.Congruence.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

Section Den.
  Context `{QM : QuantumModel}.

  (* ** Internal actions: silent moves and requests the memory can serve *)

  Inductive internal : Labels prog_action → Prop :=
  | int_tau : internal τ
  | int_op U qs : internal (ActExt (PrOp U qs))
  | int_init qs : internal (ActExt (PrInit qs))
  | int_meas M qs (k : Out (meas_of M qs)) : internal (ActExt (PrMeas M qs (code _ k))).

  (* No internal move: the program is finished (or deadlocked). *)
  Definition stable (P : proc) : Prop := ∀ s l P', prog_step P s l P' → ¬ internal l.

  Definition enabled (P : proc) (s : choice) : Prop := ∃ l P', prog_step P s l P' ∧ internal l.

  (* [Σ_k F_k ⋅ M_k], the results [F_k] being listed as the outcomes. *)
  Definition meas_sum (M : meas) (qs : list qubit) (Fs : list T) : T :=
    sum (zip_with (λ k F, F ⋅ kraus (meas_of M qs) k) (outs (meas_of M qs)) Fs).

  (* ** The denotation under a word of choices *)

  Inductive den : proc → list choice → T → Prop :=
  | den_nil_stable P : stable P → den P [] one
  | den_nil_run P : ¬ stable P → den P [] zero
  | den_stable P s w : stable P → den P (s :: w) one
  | den_stay P s w F : ¬ stable P → ¬ enabled P s → den P w F → den P (s :: w) F
  | den_tau P s w P' F : prog_step P s τ P' → den P' w F → den P (s :: w) F
  | den_op P t w U qs P' F :
      prog_step P (CTag t) (ActExt (PrOp U qs)) P' → den P' w F →
      den P (CTag t :: w) (F ⋅ act (sop_act U qs))
  | den_init P t w qs P' F :
      prog_step P (CTag t) (ActExt (PrInit qs)) P' → den P' w F →
      den P (CTag t :: w) (F ⋅ act (init_act qs))
  | den_meas P t w M qs (PFs : list (proc * T)) :
      Forall2 (λ k pf, prog_step P (CTag t) (ActExt (PrMeas M qs (code _ k))) pf.1 ∧ den pf.1 w pf.2)
        (outs (meas_of M qs)) PFs →
      den P (CTag t :: w) (meas_sum M qs (map snd PFs)).

  (* [⟦P⟧], the union over all words. *)
  Definition denot (P : proc) (F : T) : Prop := ∃ w, den P w F.

  (* ** Congruent programs have the same denotation *)

  Lemma stable_cgr P Q : P ≡* Q → stable P → stable Q.
  Proof.
    intros Hc Hs s l Q' Hq Hi. assert (Hf : fwd Q P) by (apply cgr_bisim; by symmetry).
    destruct (Hf _ _ _ Hq) as (P' & Hp & _). by apply (Hs _ _ _ Hp).
  Qed.

  Lemma enabled_cgr P Q s : P ≡* Q → enabled P s → enabled Q s.
  Proof.
    intros Hc (l & P' & Hp & Hi). pose proof (cgr_bisim _ _ Hc) as Hf.
    destruct (Hf _ _ _ Hp) as (Q' & Hq & _). by exists l, Q'.
  Qed.

  Lemma den_cgr w : ∀ P Q F, P ≡* Q → den P w F → den Q w F.
  Proof.
    induction w as [|s w IH]; intros P Q F Hc Hd;
      inversion Hd as [? Hs|? Hs|? ? ? Hs|? ? ? ? Hs He Hd'|? ? ? P' ? Hp Hd'|? t ? U qs P' ? Hp Hd'
                       |? t ? qs P' ? Hp Hd'|? t ? M qs PFs Hf]; subst.
    - apply den_nil_stable. by eapply stable_cgr.
    - apply den_nil_run. intros Hs'. apply (stable_cgr Q P) in Hs'; [done|by symmetry].
    - apply den_stable. by eapply stable_cgr.
    - apply den_stay; [| |by apply IH with P].
      + intros Hs'. apply (stable_cgr Q P) in Hs'; [done|by symmetry].
      + intros He'. apply (enabled_cgr Q P) in He'; [done|by symmetry].
    - destruct (cgr_bisim _ _ Hc _ _ _ Hp) as (Q' & Hq & HQ).
      eapply den_tau; [exact Hq|]. by apply IH with P'.
    - destruct (cgr_bisim _ _ Hc _ _ _ Hp) as (Q' & Hq & HQ).
      eapply den_op; [exact Hq|]. by apply IH with P'.
    - destruct (cgr_bisim _ _ Hc _ _ _ Hp) as (Q' & Hq & HQ).
      eapply den_init; [exact Hq|]. by apply IH with P'.
    - assert (Hall : ∀ (ks : list (Out (meas_of M qs))) PFs,
        Forall2 (λ k pf, prog_step P (CTag t) (ActExt (PrMeas M qs (code _ k))) pf.1 ∧ den pf.1 w pf.2) ks PFs →
        ∃ PFs', Forall2 (λ k pf, prog_step Q (CTag t) (ActExt (PrMeas M qs (code _ k))) pf.1 ∧ den pf.1 w pf.2) ks PFs'
                ∧ map snd PFs' = map snd PFs).
      { intros ks PFs0 Hf0. induction Hf0 as [|k pf ks' PFs' (Hp & Hd') _ (PFs'' & Hf'' & E)].
        - by exists [].
        - destruct (cgr_bisim _ _ Hc _ _ _ Hp) as (Q' & Hq & HQ).
          exists ((Q', pf.2) :: PFs''). split; [|simpl; congruence].
          constructor; [|done]. split; [done|]. simpl. by apply IH with pf.1. }
      destruct (Hall _ _ Hf) as (PFs' & Hf' & E). rewrite <- E. by apply den_meas.
  Qed.

  Theorem denot_cgr P Q F : P ≡* Q → denot P F ↔ denot Q F.
  Proof.
    intros Hc. split; intros (w & Hd); exists w; [by eapply den_cgr|].
    eapply den_cgr; [by symmetry|done].
  Qed.
End Den.

Notation "⟦ P ⟧" := (denot P) (at level 0) : lqccs_scope.
Notation "⟦ P ⟧[ w ]" := (den P w) (at level 0) : lqccs_scope.
(* end hide *)
