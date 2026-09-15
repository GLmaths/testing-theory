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
From stdpp Require Import base tactics decidable countable.
From TestingTheory Require Import ActTau gLts Subset_Act DefinitionAS
  PAL_Syntax PAL_Alt_LTS PAL_Alt_Congruence PAL_Alt_Phi.

(* * Label abstraction of the alternative LTS of PAL, as in [DefinitionAS]

   [Φᴀᴘᴀʟ] ([PAL_Alt_Phi.v]) maps a label to its event, and [𝝳ᴇᴠ] is the
   identity on events. Condition (1) is [Φ_test_spec], and condition (2)
   holds as [𝝳ᴇᴠ] is injective.

   This abstraction is not finitary, and no abstraction of these labels is:
   the co-actions of [in(?x).𝟘] have pairwise distinct events [EvOut ⟨v⟩]
   ([PAL_Alt_Abs.Φ_coR_p_formal], [PAL_Alt_Abs.prog_spec_injective], and
   [PAL_Label_Dilemma.no_labelling] for any labelling). *)

Section PAL_Alt_AbsAction.
  Context (Val : Type) `{Countable Val}.

  Notation term := (term Val).
  Notation Event := (Event Val).

  Definition 𝝳ᴇᴠ (e : Event) : Event := e.

  #[global] Instance AbsPALA :
    @AbsAction term term Event Event (PALA_Act Val) (PALA_ExtAction Val) (Φᴀᴘᴀʟ Val) 𝝳ᴇᴠ
      (PALA_gLts Val) (PALA_gLtsEq Val).
  Proof.
    split.
    - intros t β β' _ _ e h. exact (Φ_test_spec Val t β β' e h).
    - intros p β β' _ _ e h. unfold 𝝳ᴇᴠ in e. by rewrite <- e.
  Qed.
End PAL_Alt_AbsAction.
