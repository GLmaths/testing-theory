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

From stdpp Require Import gmap gmultiset.

(** Multiset helpers. *)

Lemma gmultiset_eq_drop_l `{Countable A} (m1 m2 m3 : gmultiset A) : m1 ⊎ m2 = m1 ⊎ m3 -> m2 = m3.
Proof. eapply gmultiset_disj_union_inj_1. Qed.

Lemma gmultiset_eq_pop_l `{Countable A} (m1 m2 m3 : gmultiset A) : m2 = m3 -> m1 ⊎ m2 = m1 ⊎ m3.
Proof. intro. subst. eauto. Qed.

Lemma gmultiset_neq_s `{Countable A} (m : gmultiset A) a : m ≠ {[+ a +]} ⊎ m.
Proof. by multiset_solver. Qed.

Lemma gmultiset_mono `{Countable A} (m : gmultiset A) a b : {[+ a +]} ⊎ m = {[+ b +]} ⊎ m -> a = b.
Proof. intros eq. eapply gmultiset_disj_union_inj_2 in eq.
       eapply gmultiset_singleton_subseteq. multiset_solver. Qed.

Lemma gmultiset_elements_singleton_inv `{Countable A} (m : gmultiset A) a :
  elements m = [a] -> m = {[+ a +]}.
Proof.
  intros eq.
  induction m using gmultiset_ind.
  + multiset_solver.
  + induction m using gmultiset_ind.
    ++ replace ({[+ x +]} ⊎ ∅) with ({[+ x +]} : gmultiset A) in *.
       assert (a = x); subst.
       eapply gmultiset_elem_of_singleton.
       eapply gmultiset_elem_of_elements. rewrite eq. set_solver.
       set_solver. multiset_solver.
    ++ exfalso.
       assert (length (elements ({[+ x +]} ⊎ ({[+ x0 +]} ⊎ m))) = length [a]) by now rewrite eq.
       rewrite 2 gmultiset_elements_disj_union in H0.
       rewrite 2 gmultiset_elements_singleton in H0.
       simpl in H0. lia.
Qed.

Lemma neq_multi_nil `{Countable A} (m : gmultiset A) a : {[+ a +]} ⊎ m ≠ ∅.
Proof. multiset_solver. Qed.

Lemma gmultiset_not_elem_of_multiplicity `{Countable A} x (g : gmultiset A) :
  x ∉ g <-> multiplicity x g = 0.
Proof. multiset_solver. Qed.