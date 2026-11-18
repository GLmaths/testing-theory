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
(* begin hide *)
(* * lqCCS: choices and the parallel composition of tagged LTSs *)

From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base gmultiset countable decidable numbers.
From TestingTheory Require Import ActTau.
From TestingTheory Require Import lqCCS.Language.Syntax.

(* ** Choices [s ::= ε | t | {t, t'}] *)

Notation choice := (gmultiset tag).

Lemma choice_tag_inj t t' : ({[+ t +]} : choice) = {[+ t' +]} → t = t'.
Proof.
  intros E. apply (f_equal (multiplicity t)) in E. rewrite !multiplicity_singleton in E.
  repeat case_decide; first [done|lia|congruence].
Qed.

Lemma choice_tag_neq_eps t : ({[+ t +]} : choice) ≠ ∅.
Proof.
  intros E. apply (f_equal (multiplicity t)) in E. rewrite multiplicity_singleton, multiplicity_empty in E.
  case_decide; [lia|congruence].
Qed.

Lemma choice_pair_neq_tag t t' k : ({[+ t; t' +]} : choice) ≠ {[+ k +]}.
Proof. intros E. apply (f_equal base.size) in E. rewrite gmultiset_size_disj_union, !gmultiset_size_singleton in E. lia. Qed.

Lemma choice_pair_neq_eps t t' : ({[+ t; t' +]} : choice) ≠ ∅.
Proof.
  intros E. apply (f_equal (multiplicity t)) in E.
  rewrite multiplicity_disj_union, !multiplicity_singleton, multiplicity_empty in E.
  repeat case_decide; first [lia|congruence].
Qed.

Lemma choice_pair_eq t t' u u' :
  ({[+ t; t' +]} : choice) = {[+ u; u' +]} → (t = u ∧ t' = u') ∨ (t = u' ∧ t' = u).
Proof.
  intros E.
  assert (Hu : t ∈ ({[+ u; u' +]} : choice)).
  { rewrite <- E. apply gmultiset_elem_of_disj_union. left. by apply gmultiset_elem_of_singleton. }
  apply gmultiset_elem_of_disj_union in Hu as [Hu|Hu]; apply gmultiset_elem_of_singleton in Hu as ->.
  - left. split; [done|]. apply choice_tag_inj. by apply (inj ({[+ u +]} ⊎.)).
  - right. split; [done|]. apply choice_tag_inj. rewrite (comm (⊎) {[+ u +]}) in E.
    by apply (inj ({[+ u' +]} ⊎.)).
Qed.

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
  | par_sync s1 s2 c1 c2 μ1 μ2 s1' s2' :
      lts1 s1 c1 (ActExt μ1) s1' → lts2 s2 c2 (ActExt μ2) s2' →
      sync μ1 μ2 →
      par_step (s1, s2) (c1 ⊎ c2) τ (s1', s2').
End Parallel.

Declare Scope par_scope.
Delimit Scope par_scope with par.

Notation "p ∣ q" := (p, q) (at level 60) : par_scope.

(* end hide *)
