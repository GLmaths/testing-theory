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

From TestingTheory Require Import ActTau gLts Bisimulation InteractionBetweenLts
  Testing_Predicate May DefinitionTI MayTestSpec EquivalenceTI
  DefinitionTIco EquivalenceTIco
  VCCS_Instance VCCS_Good VCCS_test_trace_gen_may.

(** * The May preorder is trace inclusion, for VCCS

    [VCCS_gLtsOBAFW] ([VCCS_Instance.v]) already makes [proc] a forwarder
    LTS on its own — no [▷ ∅] lift needed, unlike the feedback calculi
    (VACCS/ACCS, see [VACCS_May_Characterization.v]) — so this is a direct
    instance of [equivalence_ti_fw]/[equivalence_ti_co_fw], self-testing
    ([Interaction_between_parallel_VCCS] already supplies
    [Prop_of_Inter proc proc dual]). Both the plain and co-trace
    characterisations reuse the very same [gen_may]/[VCCS_may_test_spec] —
    [EquivalenceTIco.v]'s theorems take exactly the same [gen]/[may_test_spec]
    typeclasses as [EquivalenceTI.v]'s, so no separate generator is needed. *)

Notation "p ᴠᴄᴄꜱ⊑ₘₐᵧ q" := (p ⊑ₘₐᵧ q) (at level 70).

Section VCCS_May_Corollary.

Context `{VP : VCCS_Parameters}.

Corollary may_iff_trace_inclusion_VCCS (p q : proc) :
  p ᴠᴄᴄꜱ⊑ₘₐᵧ q <-> p ≼ₜᵢ q.
Proof.
  eapply (equivalence_ti_fw (gen := gen_may)).
Qed.

Corollary may_iff_co_trace_inclusion_VCCS (p q : proc) :
  p ᴠᴄᴄꜱ⊑ₘₐᵧ q <-> p ≼꜀ₒ₋ₜᵢ q.
Proof.
  eapply (equivalence_ti_co_fw (gen := gen_may)).
Qed.

End VCCS_May_Corollary.
