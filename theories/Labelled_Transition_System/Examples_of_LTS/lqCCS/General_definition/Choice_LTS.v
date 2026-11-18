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
(* * LTSs whose transitions carry a choice *)

From Stdlib.Unicode Require Import Utf8.
From TestingTheory Require Import ActTau.

Class Choice_LTS (S C A : Type) :=
  MkChoice_LTS {
      clts_step : S → C → Labels A → S → Prop;
    }.

Arguments clts_step {S C A _} _ _ _ _.

Declare Scope choice_lts_scope.
Delimit Scope choice_lts_scope with clts.

Notation "P ⟶{ 𝜆 }[ k ] P'" := (clts_step P k 𝜆 P')
  (at level 70, format "P  ⟶{ 𝜆 }[ k ]  P'") : choice_lts_scope.
Notation "P ↛{ 𝜆 }[ k ] P'" := (¬ clts_step P k 𝜆 P')
  (at level 70, format "P  ↛{ 𝜆 }[ k ]  P'") : choice_lts_scope.

(* end hide *)
