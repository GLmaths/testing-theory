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

From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base tactics countable.
From TestingTheory Require Import ActTau InputOutputActions PAL_Syntax
  Applicative_process_algebra PAL_Template_LTS.

(* * The two LTSs of PAL coincide

   [Applicative_process_algebra.lts_step] and [PAL_Template_LTS.lts_step_t]
   have the same labels (tuples of values) and the same transitions; in
   particular the same τ-transitions. Both are built on [PAL_Syntax]. *)

Section PAL_Tau.
  Context (Val : Type) `{Countable Val}.

  Notation old := (Applicative_process_algebra.lts_step Val).
  Notation new := (lts_step_t Val).

  Lemma co_t_comp_act mu : co_t Val mu = comp_act Val mu.
  Proof. by destruct mu. Qed.

  Lemma new_old p α q : new p α q → old p α q.
  Proof.
    induction 1; try rewrite co_t_comp_act in *; eauto using Applicative_process_algebra.lts_step.
  Qed.

  Lemma old_new p α q : old p α q → new p α q.
  Proof.
    induction 1; try rewrite <- co_t_comp_act in *; eauto using lts_step_t.
  Qed.

  Theorem step_iff p α q : new p α q ↔ old p α q.
  Proof. split; [apply new_old | apply old_new]. Qed.

  (** The τ-transitions coincide. *)
  Theorem tau_iff p q : new p τ q ↔ old p τ q.
  Proof. apply step_iff. Qed.
End PAL_Tau.
