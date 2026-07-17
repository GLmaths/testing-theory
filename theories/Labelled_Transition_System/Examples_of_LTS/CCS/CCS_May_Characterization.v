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
  VCCS_Instance VCCS_Good VCCS_test_trace_gen_may VCCS_May_Characterization.

(** * The May preorder is trace inclusion, for CCS

    CCS is VCCS with a trivial [Value] — [gen_may]/[VCCS_may_test_spec] and
    [equivalence_ti_fw] were already built generically over [VCCS_Parameters]
    ([VCCS_test_trace_gen_may.v]/[VCCS_May_Characterization.v]), so the CCS
    characterisation is a direct specialisation, exactly as
    [CCS_Must_Characterization.v] specialises the Must side. *)

Section CCS_May_Corollary.

Local Instance CCS_Parameters : VCCS_Parameters :=
  { Channel := nat;
    Value := unit;
    O := tt}.

Corollary may_iff_trace_inclusion_CCS (p q : proc) :
  p ⊑ₘₐᵧ q <-> p ≼ₜᵢ q.
Proof.
  eapply may_iff_trace_inclusion_VCCS.
Qed.

Corollary may_iff_co_trace_inclusion_CCS (p q : proc) :
  p ⊑ₘₐᵧ q <-> p ≼꜀ₒ₋ₜᵢ q.
Proof.
  eapply may_iff_co_trace_inclusion_VCCS.
Qed.

End CCS_May_Corollary.
