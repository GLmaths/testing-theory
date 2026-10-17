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
From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base tactics decidable countable.
From TestingTheory Require Import ActTau gLts Subset_Act DefinitionAS
  PAL_Syntax PAL_Alt_LTS PAL_Alt_Congruence PAL_Alt_Phi.
(* * Label abstraction of the alternative LTS of PAL, as in [DefinitionAS]

   [αᴛᴀᴘᴀʟ] ([PAL_Alt_Phi.v]) maps a label to its event, and [αᴘᴇᴠ] is the
   identity on events. Condition (1) is [αᴛᴇꜱᴛ_test_spec], and condition (2)
   holds as [αᴘᴇᴠ] is injective.

   This abstraction is not finitary, and no abstraction of these labels is:
   the co-actions of [in(?x).𝟘] have pairwise distinct events [EvOut ⟨v⟩]
   ([PAL_Alt_Abs.αᴛᴇꜱᴛ_coR_p_formal], [PAL_Alt_Abs.prog_spec_injective], and
   [PAL_Label_Dilemma.no_labelling] for any labelling). *)

Section PAL_Alt_AbsAction.
  Context (Val : Type) `{Countable Val}.

  Notation term := (term Val).
  Notation Event := (Event Val).

  Definition αᴘᴇᴠ (e : Event) : Event := e.

  #[global] Instance AbsPALA :
    AbsAction (gLtsP := (PALA_gLts Val)) (gLtsT := (PALA_gLtsEq Val)) term term (αᴛᴀᴘᴀʟ Val) αᴘᴇᴠ.
  Proof.
    split.
    - intros t β β' _ _ e h. exact (αᴛᴇꜱᴛ_test_spec Val t β β' e h).
    - intros p β β' _ _ e h. unfold αᴘᴇᴠ in e. by rewrite <- e.
  Qed.
End PAL_Alt_AbsAction.
(* end hide *)
