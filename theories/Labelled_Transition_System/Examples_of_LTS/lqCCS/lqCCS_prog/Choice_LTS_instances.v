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

(* * Rocq instances for : the program LTS is an LTS with choices and structural congruence *)

From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base gmultiset list relations.
From TestingTheory Require Import ActTau.
From TestingTheory Require Import lqCCS.General_definition.Choice_LTS lqCCS.General_definition.Choice_LTS_eq.
From TestingTheory Require Import lqCCS.General_definition.Parallel_choice_LTS.
From TestingTheory Require Import lqCCS.lqCCS_prog.Syntax lqCCS.lqCCS_prog.LTS lqCCS.lqCCS_prog.Congruence.

#[local] Open Scope lqccs_scope.

#[global] Instance lqCCS_prog_clts `{lqP : lqCCS_Parameters} : Choice_LTS prog choice prog_action :=
  {| clts_step := prog_step |}.

Lemma lqCCS_prog_clts_step `{lqP : lqCCS_Parameters} P k 𝜆 P' :
  (P ⟶{𝜆}[k] P')%clts ↔ P ⟶ₚ{𝜆}[k] P'.
Proof. done. Qed.

#[global] Program Instance lqCCS_prog_clts_eq `{lqP : lqCCS_Parameters} : Choice_LTS_eq prog choice prog_action :=
  {| clts_eq_rel := cgr |}.
Next Obligation. intros lqP p k 𝜆 q H. by apply Congruence_Respects_Transition. Qed.