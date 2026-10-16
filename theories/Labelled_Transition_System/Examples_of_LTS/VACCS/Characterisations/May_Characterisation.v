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

From stdpp Require Import gmap gmultiset.
From TestingTheory Require Import ActTau gLts Bisimulation InteractionBetweenLts
  Testing_Predicate May DefinitionTI MayTestSpec EquivalenceTI InputOutputActions
  DefinitionTIco EquivalenceTIco
  ForwarderConstruction MultisetLTSConstruction Lts_OBA_FB Lts_Finite_Non_Blocking_Chain
  FiniteImageLTS VACCS.Language.gLts_Instance VACCS_Good VACCS.Testing.test_trace_gen_may.

(** ******* The May preorder is trace inclusion, for VACCS *)

Notation "p ᴠᴀᴄᴄꜱ⊑ₘₐᵧ q" := (p ⊑ₘₐᵧ q) (at level 70).

Section VACCS_May_Corollary.

Context `{VP : VACCS_Parameters}.

Corollary may_iff_trace_inclusion_VACCS (p q : proc) :
  p ᴠᴀᴄᴄꜱ⊑ₘₐᵧ q <-> (p, ∅ : MO (ExtAct TypeOfActions)) ≼ₜᵢ (q, ∅ : MO (ExtAct TypeOfActions)).
Proof.
  eapply (equivalence_ti_fb (gen := gen_may)).
Qed.

Corollary may_iff_co_trace_inclusion_VACCS (p q : proc) :
  p ᴠᴀᴄᴄꜱ⊑ₘₐᵧ q <-> (p, ∅ : MO (ExtAct TypeOfActions)) ≼꜀ₒ₋ₜᵢ (q, ∅ : MO (ExtAct TypeOfActions)).
Proof.
  eapply (equivalence_ti_co_trace_fb (gen := gen_may)).
Qed.

End VACCS_May_Corollary.
