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
From stdpp Require Import base tactics decidable countable gmap.
From TestingTheory Require Import ActTau gLts Subset_Act InputOutputActions DefinitionAS
  PAL_Syntax PAL_Template_LTS PAL_Template_Congruence.

(* * Label abstraction of the alternative LTS of PAL, as in [DefinitionAS]

   The labels are tuples of values, and [Φ] and [𝝳] are the identity. This
   abstraction is not finitary as soon as [Val] is infinite ([in(?x).𝟘]
   accepts every one-field tuple); making it finitary is left for later. *)

Section PAL_T_Abs.
  Context (Val : Type) `{Countable Val}.

  Notation term := (term Val).
  Notation PALT_Act := (PALT_Act Val).

  Definition Φᴘᴀʟ (μ : PALT_Act) : PALT_Act := μ.
  Definition 𝝳ᴘᴀʟ (μ : PALT_Act) : PALT_Act := μ.

  #[global] Instance AbsPALT :
    @AbsAction term term PALT_Act PALT_Act PALT_Act (PALT_ExtAction Val) Φᴘᴀʟ 𝝳ᴘᴀʟ (PALT_gLts Val) (PALT_gLtsEq Val).
  Proof.
    split.
    - intros t β β' _ _ eq mem. cbv [Φᴘᴀʟ] in eq. by subst.
    - intros p β β' _ _ eq mem. cbv [𝝳ᴘᴀʟ Φᴘᴀʟ] in eq. by subst.
  Qed.
End PAL_T_Abs.
