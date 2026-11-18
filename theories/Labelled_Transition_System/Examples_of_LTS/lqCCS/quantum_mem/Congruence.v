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

(* * The quantum memory: its congruence is the equality *)

From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base relations.
From TestingTheory Require Import lqCCS.General_definition.Algebra lqCCS.lqCCS_prog.Syntax.

Definition mem_cgr `{StAlg} : relation St := eq.

Notation "ρ ≡ₘ ρ'" := (mem_cgr ρ ρ') (at level 70) : lqccs_scope.

#[global] Instance mem_cgr_equivalence `{StAlg} : Equivalence mem_cgr.
Proof. unfold mem_cgr. apply _. Qed.