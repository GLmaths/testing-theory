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
(* * LTSs with choices, equipped with an equivalence that respects the
    transitions, in the style of [gLtsEq] *)

From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base.
From TestingTheory Require Import ActTau.
From TestingTheory Require Import lqCCS.General_definition.Choice_LTS.

Class Choice_LTS_eq (S C A : Type) :=
  MkChoice_LTS_eq {
      clts_eq_clts :: Choice_LTS S C A;
      clts_eq_rel : S → S → Prop;
      clts_eq_rel_eq :: Equivalence clts_eq_rel;
      clts_eq_spec p k 𝜆 q :
        (∃ r, clts_eq_rel p r ∧ clts_step r k 𝜆 q) → (∃ r, clts_step p k 𝜆 r ∧ clts_eq_rel r q);
    }.

Arguments clts_eq_rel {S C A _} _ _.

Definition clts_sc `{Choice_LTS_eq X C A} (p : X) (k : C) (𝜆 : Labels A) (q : X) : Prop :=
  ∃ r, clts_step p k 𝜆 r ∧ clts_eq_rel r q.

Definition sc_clts `{Choice_LTS_eq X C A} (p : X) (k : C) (𝜆 : Labels A) (q : X) : Prop :=
  ∃ r, clts_eq_rel p r ∧ clts_step r k 𝜆 q.

Infix "⋍" := clts_eq_rel (at level 70) : choice_lts_scope.
Notation "P ⟶{ 𝜆 }[ k ] . ⋍ Q" := (clts_sc P k 𝜆 Q)
  (at level 70, format "P  ⟶{ 𝜆 }[ k ]  .  ⋍  Q") : choice_lts_scope.
Notation "P ⋍ . ⟶{ 𝜆 }[ k ] Q" := (sc_clts P k 𝜆 Q)
  (at level 70, format "P  ⋍  .  ⟶{ 𝜆 }[ k ]  Q") : choice_lts_scope.

Lemma clts_eq_respects `{Choice_LTS_eq X C A} p k 𝜆 q : sc_clts p k 𝜆 q → clts_sc p k 𝜆 q.
Proof. apply clts_eq_spec. Qed.

(* end hide *)
