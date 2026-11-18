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
From stdpp Require Import base gmultiset countable decidable list.
From TestingTheory Require Import ActTau.
From TestingTheory Require Import lqCCS.General_definition.Algebra lqCCS.quantum_mem.Syntax.
From TestingTheory Require Import lqCCS.lqCCS_prog.Syntax lqCCS.Helper.De_Brujin_lemmas lqCCS.General_definition.Parallel_choice_LTS lqCCS.quantum_mem.LTS lqCCS.lqCCS_prog.LTS lqCCS.lqCCS_par_Qmem.LTS lqCCS.lqCCS_process.LTS.LTS lqCCS.Helper.Conf_labels lqCCS.Helper.Label_lemmas lqCCS.lqCCS_prog.Congruence.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

Section Denotational.
  Context `{lqP : lqCCS_Parameters}.

Reserved Notation "⟦ P ⟧" (at level 0, format "⟦ P ⟧").
Reserved Notation "⟦ P ⟧[ w ]" (at level 0, format "⟦ P ⟧[ w ]").

Section Den.
  Context `{QM : QuantumModel}.

  (* ** Internal actions: silent moves and requests the memory can serve *)

  Inductive internal : Labels prog_action → Prop :=
  | int_tau : internal τ
  | int_op U qs : internal (⦅qs⦆ ! U)
  | int_init q : internal (reinit q)
  | int_meas M qs n : n ∈ outs (meas_of M qs) → internal (M ⦅qs⦆? n).

  (* No internal move: the program is finished (or deadlocked). *)
  Definition stable (P : prog) : Prop := ∀ k 𝜆 P', P ⟶ₚ{𝜆}[k] P' → ¬ internal 𝜆.

  Definition enabled (P : prog) (k : choice) : Prop := ∃ 𝜆 P', P ⟶ₚ{𝜆}[k] P' ∧ internal 𝜆.

  (* [Σ_k F_k ⋅ M_k], the results [F_k] being listed as the outcomes. *)
  Definition meas_sum (M : meas) (qs : list qubit) (Fs : list T) : T :=
    sum (zip_with (λ n F, F ⋅ kraus (meas_of M qs) n) (outs (meas_of M qs)) Fs).

  (* ** The denotation under a word of choices *)

  Inductive den : prog → list choice → T → Prop :=
  | den_nil_stable P : stable P → ⟦P⟧[[]] one
  | den_nil_run P : ¬ stable P → ⟦P⟧[[]] zero
  | den_stable P k w : stable P → ⟦P⟧[k :: w] one
  | den_stay P k w F : ¬ stable P → ¬ enabled P k → ⟦P⟧[w] F → ⟦P⟧[k :: w] F
  | den_tau P k w P' F : P ⟶ₚ{τ}[k] P' → ⟦P'⟧[w] F → ⟦P⟧[k :: w] F
  | den_op P t w U qs P' F :
      P ⟶ₚ{⦅qs⦆ ! U}[{[+ t +]}] P' → ⟦P'⟧[w] F →
      ⟦P⟧[{[+ t +]} :: w] (F ⋅ act (sop_act U qs))
  | den_init P t w q P' F :
      P ⟶ₚ{reinit q}[{[+ t +]}] P' → ⟦P'⟧[w] F →
      ⟦P⟧[{[+ t +]} :: w] (F ⋅ act (init_act q))
  | den_meas P t w M qs (PFs : list (prog * T)) :
      Forall2 (λ n pf, P ⟶ₚ{M ⦅qs⦆? n}[{[+ t +]}] pf.1 ∧ ⟦pf.1⟧[w] pf.2)
        (outs (meas_of M qs)) PFs →
      ⟦P⟧[{[+ t +]} :: w] (meas_sum M qs (map snd PFs))
  where "⟦ P ⟧[ w ]" := (den P w) : lqccs_scope.

  (* [⟦P⟧], the union over all words. *)
  Definition denot (P : prog) (F : T) : Prop := ∃ w, ⟦P⟧[w] F.

  Notation "⟦ P ⟧" := (denot P) : lqccs_scope.

  (* ** Congruent programs have the same denotation *)

  Lemma stable_cgr P Q : P ≡* Q → stable P → stable Q.
  Proof.
    intros Hc Hs k 𝜆 Q' Hq Hi.
    destruct (Congruence_Respects_Transition P _ _ Q' (ex_intro _ Q (conj Hc Hq))) as (P' & Hp & _).
    by apply (Hs _ _ _ Hp).
  Qed.

  Lemma enabled_cgr P Q k : P ≡* Q → enabled P k → enabled Q k.
  Proof.
    intros Hc (𝜆 & P' & Hp & Hi).
    destruct (Congruence_Respects_Transition Q _ _ P' (ex_intro _ P (conj (symmetry Hc) Hp))) as (Q' & Hq & _).
    by exists 𝜆, Q'.
  Qed.

  Lemma den_cgr w : ∀ P Q F, P ≡* Q → ⟦P⟧[w] F → ⟦Q⟧[w] F.
  Proof.
    induction w as [|k w IH]; intros P Q F Hc Hd;
      inversion Hd as [? Hs|? Hs|? ? ? Hs|? ? ? ? Hs He Hd'|? ? ? P' ? Hp Hd'|? t ? U qs P' ? Hp Hd'
                       |? t ? qs P' ? Hp Hd'|? t ? M qs PFs Hf]; subst.
    - apply den_nil_stable. by eapply stable_cgr.
    - apply den_nil_run. intros Hs'. apply (stable_cgr Q P) in Hs'; [done|by symmetry].
    - apply den_stable. by eapply stable_cgr.
    - apply den_stay; [| |by apply IH with P].
      + intros Hs'. apply (stable_cgr Q P) in Hs'; [done|by symmetry].
      + intros He'. apply (enabled_cgr Q P) in He'; [done|by symmetry].
    - destruct (Congruence_Respects_Transition Q _ _ _ (ex_intro _ P (conj (symmetry Hc) Hp))) as (Q' & Hq & HQ).
      symmetry in HQ.
      eapply den_tau; [exact Hq|]. by apply IH with P'.
    - destruct (Congruence_Respects_Transition Q _ _ _ (ex_intro _ P (conj (symmetry Hc) Hp))) as (Q' & Hq & HQ).
      symmetry in HQ.
      eapply den_op; [exact Hq|]. by apply IH with P'.
    - destruct (Congruence_Respects_Transition Q _ _ _ (ex_intro _ P (conj (symmetry Hc) Hp))) as (Q' & Hq & HQ).
      symmetry in HQ.
      eapply den_init; [exact Hq|]. by apply IH with P'.
    - assert (Hall : ∀ (ns : list (nat)) PFs,
        Forall2 (λ n pf, P ⟶ₚ{M ⦅qs⦆? n}[{[+ t +]}] pf.1 ∧ ⟦pf.1⟧[w] pf.2) ns PFs →
        ∃ PFs', Forall2 (λ n pf, Q ⟶ₚ{M ⦅qs⦆? n}[{[+ t +]}] pf.1 ∧ ⟦pf.1⟧[w] pf.2) ns PFs'
                ∧ map snd PFs' = map snd PFs).
      { intros ns PFs0 Hf0. induction Hf0 as [|n pf ns' PFs' (Hp & Hd') _ (PFs'' & Hf'' & E)].
        - by exists [].
        - destruct (Congruence_Respects_Transition Q _ _ _ (ex_intro _ P (conj (symmetry Hc) Hp))) as (Q' & Hq & HQ).
      symmetry in HQ.
          exists ((Q', pf.2) :: PFs''). split; [|simpl; congruence].
          constructor; [|done]. split; [done|]. simpl. by apply IH with pf.1. }
      destruct (Hall _ _ Hf) as (PFs' & Hf' & E). rewrite <- E. by apply den_meas.
  Qed.

  Theorem denot_cgr P Q F : P ≡* Q → ⟦P⟧ F ↔ ⟦Q⟧ F.
  Proof.
    intros Hc. split; intros (w & Hd); exists w; [by eapply den_cgr|].
    eapply den_cgr; [by symmetry|done].
  Qed.
End Den.

Notation "⟦ P ⟧" := (denot P) (at level 0, format "⟦ P ⟧") : lqccs_scope.
Notation "⟦ P ⟧[ w ]" := (den P w) (at level 0, format "⟦ P ⟧[ w ]") : lqccs_scope.

End Denotational.

Notation "⟦ P ⟧" := (denot P) (at level 0, format "⟦ P ⟧") : lqccs_scope.
Notation "⟦ P ⟧[ w ]" := (den P w) (at level 0, format "⟦ P ⟧[ w ]") : lqccs_scope.

(* end hide *)
