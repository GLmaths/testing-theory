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
(* * lqCCS: the congruence of the composition [ρ ∣ P], equality on the memory
    and structural congruence on the program *)

From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base relations.
From TestingTheory Require Import lqCCS.quantum_mem.Algebra lqCCS.quantum_mem.Congruence.
From TestingTheory Require Import lqCCS.lqCCS_prog.Syntax lqCCS.lqCCS_prog.Congruence.

#[local] Open Scope lqccs_scope.

Section LqP.
  Context `{LP : lqCCS_Parameters} `{SA : StAlg}.

  Definition par_cgr : relation (St * proc) := λ c c', c.1 ≡ₘ c'.1 ∧ c.2 ≡* c'.2.

  #[global] Instance par_cgr_equivalence : Equivalence par_cgr.
  Proof.
    split.
    - intros c. split; reflexivity.
    - intros c c' [Hm Hp]. split; by symmetry.
    - intros c c' c'' [Hm Hp] [Hm' Hp']. split; by etrans.
  Qed.
End LqP.

Notation "c ≡ᶜ* c'" := (par_cgr c c') (at level 70) : lqccs_scope.

(* end hide *)
