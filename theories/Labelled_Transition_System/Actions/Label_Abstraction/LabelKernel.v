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

From Stdlib.Unicode Require Import Utf8.
From Stdlib Require Import Relations.Relation_Definitions Classes.RelationClasses.
From stdpp Require Import base tactics.
(* begin hide *)
Section Kernel.
  Context {A : Type}.

  Definition sym_part (R : relation A) : relation A := λ μ μ', R μ μ' ∧ R μ' μ.

  Definition rel_ker (S : relation A) : relation A := λ μ μ', ∀ ν, S μ ν ↔ S μ' ν.

  Lemma rel_ker_equivalence (S : relation A) : Equivalence (rel_ker S).
  Proof.
    split.
    - intros μ ν. done.
    - intros μ μ' h ν. symmetry. apply h.
    - intros μ μ' μ'' h1 h2 ν. etransitivity; [apply h1 | apply h2].
  Qed.

  Lemma rel_ker_sub (S : relation A) : Reflexive S → ∀ μ μ', rel_ker S μ μ' → S μ μ'.
  Proof. intros hr μ μ' h. by apply h. Qed.

  Lemma sym_part_equivalence (R : relation A) `{!PreOrder R} : Equivalence (sym_part R).
  Proof.
    split.
    - intros μ. split; reflexivity.
    - intros μ μ' [h1 h2]. by split.
    - intros μ μ' μ'' [h1 h2] [h3 h4]. split; by etransitivity.
  Qed.
End Kernel.

Section Join.
  Context {A : Type} (Rt Rp : relation A).

  Definition LA_S : relation A := λ μ ν, ∃ u, sym_part Rt μ u ∧ Rp u ν.

  Lemma LA_S_left `{!PreOrder Rt} μ μ' ν : sym_part Rt μ μ' → LA_S μ' ν → LA_S μ ν.
  Proof.
    intros [h1 h2] (u & [h3 h4] & hp). exists u. split; [split; by etransitivity | done].
  Qed.

  Lemma LA_S_right `{!Transitive Rp} μ u ν : LA_S μ u → Rp u ν → LA_S μ ν.
  Proof. intros (w & hw & hp) h. exists w. split; [done | by etransitivity]. Qed.

  Lemma LA_S_refl `{!Reflexive Rt, !Reflexive Rp} μ : LA_S μ μ.
  Proof. exists μ. split; [split | ]; reflexivity. Qed.
End Join.

Section Kernel2.
  Context {A : Type} (Rt RpP RpQ : relation A).

  Definition LA_S2 : relation A := λ μ ν, LA_S Rt RpP μ ν ∧ LA_S Rt RpQ μ ν.

  Definition LA_K : relation A := rel_ker LA_S2.

  Lemma LA_K_equivalence : Equivalence LA_K.
  Proof. apply rel_ker_equivalence. Qed.

  Context `{!PreOrder Rt, !PreOrder RpP, !PreOrder RpQ}.

  Lemma LA_K_sub μ μ' : LA_K μ μ' → LA_S2 μ μ'.
  Proof. apply rel_ker_sub. intros μ0. split; exists μ0; (split; [split | ]); reflexivity. Qed.

  Lemma LA_test_K μ μ' : sym_part Rt μ μ' → LA_K μ μ'.
  Proof.
    intros he ν. assert (he' : sym_part Rt μ' μ) by (destruct he; by split).
    split; intros [hP hQ]; split; eapply LA_S_left; eassumption.
  Qed.

  Lemma LA_K_largest (R : relation A) `{!Equivalence R} :
    (∀ μ μ', sym_part Rt μ μ' → R μ μ') →
    (∀ μ μ', R μ μ' → LA_S2 μ μ') →
    ∀ μ μ', R μ μ' → LA_K μ μ'.
  Proof.
    intros htest hsub.
    assert (dir : ∀ μ1 μ2 ν, R μ1 μ2 → LA_S2 μ2 ν → LA_S2 μ1 ν).
    { intros μ1 μ2 ν h [(u & hu & hp) (u' & hu' & hq)]. split.
      - apply (LA_S_right Rt RpP μ1 u ν); [| exact hp].
        apply (hsub μ1 u). etransitivity; [exact h | by apply htest].
      - apply (LA_S_right Rt RpQ μ1 u' ν); [| exact hq].
        apply (hsub μ1 u'). etransitivity; [exact h | by apply htest]. }
    intros μ μ' h ν. split; intros hs.
    - apply (dir μ' μ); [by symmetry | exact hs].
    - apply (dir μ μ'); [exact h | exact hs].
  Qed.

  Lemma LA_K_iff μ μ' :
    LA_K μ μ' ↔
      (∀ u, sym_part Rt μ' u → LA_S2 μ u) ∧ (∀ u, sym_part Rt μ u → LA_S2 μ' u).
  Proof.
    assert (half : ∀ μ1 μ2 ν, (∀ u, sym_part Rt μ2 u → LA_S2 μ1 u) →
                   LA_S2 μ2 ν → LA_S2 μ1 ν).
    { intros μ1 μ2 ν hm [(u & hu & hp) (u' & hu' & hq)]. split.
      - exact (LA_S_right Rt RpP μ1 u ν (proj1 (hm u hu)) hp).
      - exact (LA_S_right Rt RpQ μ1 u' ν (proj2 (hm u' hu')) hq). }
    split.
    - intros h. split; intros u hu.
      + apply (h u). split; exists u; (split; [exact hu | reflexivity]).
      + apply (h u). split; exists u; (split; [exact hu | reflexivity]).
    - intros [h1 h2] ν. split; intros hs.
      + exact (half μ' μ ν h2 hs).
      + exact (half μ μ' ν h1 hs).
  Qed.
End Kernel2.
(* end hide *)
