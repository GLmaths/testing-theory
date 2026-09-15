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
From stdpp Require Import base countable.
From TestingTheory Require Import ActTau gLts Bisimulation Lts_OBA Lts_FW Lts_OBA_FB FiniteImageLTS
  coFiniteImage InteractionBetweenLts Testing_Predicate DefinitionAS CompletenessASco TestSpecBridge
  PAL_Syntax PAL_Alt_LTS PAL_Alt_Congruence PAL_Alt_Phi PAL_Alt_AbsAction PAL_Good PAL_Alt_Tests
  PAL_Alt_TestSpec.

(* * What the alternative LTS of PAL provides for [EquivalenceASco]

   [EquivalenceASco.equivalence_fw_acc_set_and_must_i_co] states
   [p ⊑ₘᵤₛₜᵢ q ↔ p ≼꜀ₒ₋ₐₛ q]. Every hypothesis of its section is available
   here, and the only missing one is [FinitaryAbsAction].

   That one is not a gap to be filled: [𝝳 (Φ (coR p))] is infinite for
   [in(?x).𝟘] whatever [𝝳] ([PAL_Alt_Abs.prog_spec_injective] with
   [PAL_Alt_Abs.Φ_coR_p_formal]), and no labelling of PAL does better
   ([PAL_Label_Dilemma.no_labelling]). What is finite is [Φ (R p)]
   ([PAL_Alt_Phi.abs_R_spec]), the events of the process itself. *)

Section PAL_Alt_CoTraceHypotheses.
  Context (Val : Type) `{Countable Val} `{!Inhabited Val}.

  Notation term := (term Val).

  (** The LTS of processes and of tests. *)
  Definition hyp_CountablegLts : CountablegLts term (PALA_Act Val) := _.
  Definition hyp_gLtsOba : gLtsOba term (H := PALA_ExtAction Val) := _.
  Definition hyp_coFiniteImage : coFiniteImagegLts term (PALA_Act Val) := _.
  Definition hyp_gLtsObaFW : gLtsObaFW term (PALA_Act Val) := _.
  Definition hyp_gLtsObaFB : gLtsObaFB term (PALA_Act Val) := _.
  Definition hyp_Prop_of_Inter : Prop_of_Inter term term (PALA_Act Val) dual := _.

  (** The testing predicate and the events. *)
  Definition hyp_Testing_Predicate : Testing_Predicate (good_PAL Val) (PALA_gLtsEq Val) := _.
  Definition hyp_Countable_PreAct : Countable (Event Val) := _.

  (** The label abstraction, without finiteness. *)
  Definition hyp_AbsAction :
    @AbsAction term term (Event Val) (Event Val) (PALA_Act Val) (PALA_ExtAction Val)
      (Φᴀᴘᴀʟ Val) (𝝳ᴇᴠ Val) (PALA_gLts Val) (PALA_gLtsEq Val) := AbsPALA Val.

  (** The tests, in the co variants of the classes ([TestSpecBridge]). *)
  Definition hyp_test_convergence_spec : CompletenessASco.test_convergence_spec (t_conv Val) :=
    test_convergence_spec_of_plain (t_conv_convergence_spec Val).

  Definition hyp_test_co_acceptance_set_spec :
    CompletenessASco.test_co_acceptance_set_spec (Event Val) (ta Val)
      (λ x, 𝝳ᴇᴠ Val (Φᴀᴘᴀʟ Val x)) :=
    test_co_acceptance_set_spec_of_plain (ta_co_acceptance_set_spec Val).
End PAL_Alt_CoTraceHypotheses.
