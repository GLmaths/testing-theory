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
From stdpp Require Import base countable gmap.
From TestingTheory Require Import ActTau gLts Bisimulation SyncActions Must RelationKernel
  Label_Abstraction.LabelAbstraction DefinitionASrel EquivalenceASco
  PAL.Language.Syntax PAL.Language.LTS PAL.Language.Phi PAL.Language.AbsAction PAL.Language.Congruence PAL_Good PAL.Testing.Must_Preorder
  PAL.Testing.Tests PAL.Testing.Test_Spec PAL.Testing.CoTrace_Hypotheses PAL.Language.Label_Abstraction PAL.Testing.Class_Tests.

#[local] Hint Mode ExtAction ! : typeclass_instances.

Theorem PAL_Alt_equivalence (p q : term nat) :
  p ᴘᴀʟ⊑ₘᵤₛₜᵢ q ↔ p ≼꜀ₒ₋ₐₛ[ ρ[𝔸ᴘᴀʟ] ] q.
Proof.
  exact (@equivalence_fw_acc_set_and_must_i_co_trace (term nat) (good_PAL nat) (term nat) _
           (PALA_ExtAction nat) (PALA_gLtsEq nat) (hyp_coFiniteImage nat) (PALA_gLtsEq nat)
           (hyp_gLtsOba nat) (hyp_Testing_Predicate nat) (hyp_Prop_of_Inter nat)
           (t_conv nat) (hyp_test_convergence_spec nat)
           (LtsFW.LtsFW_of_gLtsObaFW (H0 := hyp_gLtsObaFW nat))
           𝔸ᴘᴀʟ Dichotomic_PAL ta_𝔸 ta_𝔸_spec p q).
Qed.
(* end hide *)
