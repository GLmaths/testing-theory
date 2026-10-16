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
From stdpp Require Import base countable.
From TestingTheory Require Import ActTau gLts Bisimulation SyncActions Must DefinitionAS DefinitionASco SoundnessASco
  PAL_Syntax PAL_Alt_LTS PAL_Alt_Phi PAL_Alt_AbsAction PAL_Alt_Congruence PAL_Good PAL_Must
  PAL_Alt_Completeness.

#[local] Hint Mode ExtAction ! : typeclass_instances.
#[local] Hint Mode gLtsEq ! - - : typeclass_instances.
#[local] Hint Mode SyncAction - ! - - : typeclass_instances.

Theorem PAL_Alt_soundness (p q : term) :
  p ≼꜀ₒ₋ₐₛ q → p ᴘᴀʟ⊑ₘᵤₛₜᵢ q.
Proof.
  exact (soundness_fw_co (outcome := good_PAL nat) p q).
Qed.

Theorem PAL_Alt_equivalence (p q : term) :
  p ᴘᴀʟ⊑ₘᵤₛₜᵢ q ↔ p ≼꜀ₒ₋ₐₛ q.
Proof. split; [apply PAL_Alt_completeness | apply PAL_Alt_soundness]. Qed.
(* end hide *)
