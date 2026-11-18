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
From TestingTheory Require Import lqCCS.lqCCS_prog.Syntax.

(* ** Choices [k ::= ε | t | {t, t'}] *)

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

Lemma choice_pair_neq_tag t1 t2 t3 : ({[+ t1; t2 +]} : choice) ≠ {[+ t3 +]}.
Proof. intros E. apply (f_equal base.size) in E. rewrite gmultiset_size_disj_union, !gmultiset_size_singleton in E. lia. Qed.

Lemma choice_pair_neq_eps t t' : ({[+ t; t' +]} : choice) ≠ ∅.
Proof.
  intros E. apply (f_equal (multiplicity t)) in E.
  rewrite multiplicity_disj_union, !multiplicity_singleton, multiplicity_empty in E.
  repeat case_decide; first [lia|congruence].
Qed.

Lemma choice_pair_eq t1 t2 t3 t4 :
  ({[+ t1; t2 +]} : choice) = {[+ t3; t4 +]} → (t1 = t3 ∧ t2 = t4) ∨ (t1 = t4 ∧ t2 = t3).
Proof.
  intros E.
  assert (Hu : t1 ∈ ({[+ t3; t4 +]} : choice)).
  { rewrite <- E. apply gmultiset_elem_of_disj_union. left. by apply gmultiset_elem_of_singleton. }
  apply gmultiset_elem_of_disj_union in Hu as [Hu|Hu]; apply gmultiset_elem_of_singleton in Hu as ->.
  - left. split; [done|]. apply choice_tag_inj. by apply (inj ({[+ t3 +]} ⊎.)).
  - right. split; [done|]. apply choice_tag_inj. rewrite (comm (⊎) {[+ t3 +]}) in E.
    by apply (inj ({[+ t4 +]} ⊎.)).
Qed.

(* ** Parallel composition of two LTSs with choices *)

Section Parallel.
  Context {S1 S2 A1 A2 : Type}.
  Variable lts1 : S1 → choice → Labels A1 → S1 → Prop.
  Variable lts2 : S2 → choice → Labels A2 → S2 → Prop.
  Variable sync : A1 → A2 → Prop.

  Definition lbl_inl (𝜆 : Labels A1) : Labels (A1 + A2) :=
    match 𝜆 with ActExt μ => ActExt (inl μ) | τ => τ end.
  Definition lbl_inr (𝜆 : Labels A2) : Labels (A1 + A2) :=
    match 𝜆 with ActExt μ => ActExt (inr μ) | τ => τ end.

  Inductive par_step : S1 * S2 → choice → Labels (A1 + A2) → S1 * S2 → Prop :=
  | par_left k1 k2 c 𝜆 k1' :
      lts1 k1 c 𝜆 k1' → par_step (k1, k2) c (lbl_inl 𝜆) (k1', k2)
  | par_right k1 k2 c 𝜆 k2' :
      lts2 k2 c 𝜆 k2' → par_step (k1, k2) c (lbl_inr 𝜆) (k1, k2')
  | par_sync k1 k2 c1 c2 μ1 μ2 k1' k2' :
      lts1 k1 c1 (ActExt μ1) k1' → lts2 k2 c2 (ActExt μ2) k2' →
      sync μ1 μ2 →
      par_step (k1, k2) (c1 ⊎ c2) τ (k1', k2').
End Parallel.

Declare Scope par_scope.
Delimit Scope par_scope with par.

Notation "p ∣ q" := (p, q) (at level 60) : par_scope.

(* end hide *)
