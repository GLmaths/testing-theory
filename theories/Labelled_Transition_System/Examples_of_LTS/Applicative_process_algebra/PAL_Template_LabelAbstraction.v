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
From stdpp Require Import base tactics decidable countable list.
From TestingTheory Require Import ActTau gLts Subset_Act InputOutputActions
  LabelAbstraction PAL_Syntax PAL_Template_LTS.

(* * Label abstractions of the alternative LTS of PAL

   The labels are tuples of values, and [≈ᴛᴇꜱᴛ] and [≈ᴘʀᴏ] are equality. *)

Section PAL_T_LA.
  Context (Val : Type) `{Countable Val}.

  Notation term := (term Val).
  Notation PALT_Act := (PALT_Act Val).

  #[local] Existing Instance PALT_gLts.

  Lemma R_eq_test_spec (μ μ' : PALT_Act) : μ = μ' → (𝐏 μ : subset_of term) ⊆ 𝐏 μ'.
  Proof. by intros <-. Qed.

  Lemma R_eq_prog_spec (μ μ' : PALT_Act) : μ = μ' → (co𝐏 μ : subset_of term) ⊆ co𝐏 μ'.
  Proof. by intros <-. Qed.

  #[global] Instance gLtsLAtest_PALT : @gLtsLAtest term PALT_Act (PALT_ExtAction Val) (PALT_gLts Val) :=
    {| LA_test := eq;
       LA_test_eq := eq_equivalence;
       LA_test_dec := PALT_Act_eqdec Val;
       LA_test_spec := R_eq_test_spec |}.

  #[global] Instance gLtsLAprog_PALT : @gLtsLAprog term PALT_Act (PALT_ExtAction Val) (PALT_gLts Val) :=
    {| LA_prog := eq;
       LA_prog_eq := eq_equivalence;
       LA_prog_dec := PALT_Act_eqdec Val;
       LA_prog_spec := R_eq_prog_spec |}.
End PAL_T_LA.
