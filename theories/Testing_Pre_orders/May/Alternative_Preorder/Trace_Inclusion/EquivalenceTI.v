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

From stdpp Require Import decidable.
From TestingTheory Require Import ActTau gLts Bisimulation Lts_OBA Lts_OBA_FB Lts_FW
    Testing_Predicate InteractionBetweenLts FiniteImageLTS Lts_Finite_Non_Blocking_Chain
    MultisetLTSConstruction ForwarderConstruction May DefinitionTI MayTestSpec SoundnessTI CompletenessTI.
(** **** The May preorder is trace inclusion *)

(** **** Equivalence, for forwarders *)

Theorem equivalence_ti_fw `{
  gLtsObaFWP : @gLtsObaFW P A H gLtsEqP gLtsObaP,
  gLtsObaFWQ : @gLtsObaFW Q A H gLtsEqQ gLtsObaQ,
  gLtsT : !gLtsEq T H, gLtsObaT : !gLtsOba T _, !Testing_Predicate outcome _} {unique_nb : UniqueDual A}

  {_ : Prop_of_Inter P T A A dual}
  {_ : Prop_of_Inter Q T A A dual}

  {gen : trace A -> T} {gspec : may_test_spec gen}

  (p : P) (q : Q) :
  p ⊑ₘₐᵧ q <-> p ≼ₜᵢ q.
Proof.
  split.
  - eapply completeness_ti_fw.
  - eapply soundness_ti_fw.
Qed.

(** **** Equivalence, for feedback LTSs *)

Theorem equivalence_ti_fb `{
    @gLtsObaFB P A H gLtsEqP gLtsObaP, !FiniteNonBlockingChain_LtsOba P, !FiniteImagegLts P A,
    @gLtsObaFB Q A H gLtsEqQ gLtsObaQ, !FiniteNonBlockingChain_LtsOba Q, !FiniteImagegLts Q A,
    @gLtsObaFB T A H gLtsEqT gLtsObaT, !FiniteNonBlockingChain_LtsOba T, !Testing_Predicate outcome _} {unique_nb : UniqueDual A}

  {_ : Prop_of_Inter P (MO A) A A fw_inter}
  {_ : Prop_of_Inter (P * MO A) T A A dual}
  {_ : Prop_of_Inter P T A A dual}

  {_ : Prop_of_Inter Q (MO A) A A fw_inter}
  {_ : Prop_of_Inter (Q * MO A) T A A dual}
  {_ : Prop_of_Inter Q T A A dual}

  {gen : trace A -> T} {gspec : may_test_spec gen}

  (p : P) (q : Q) :
  p ⊑ₘₐᵧ q <-> (p, ∅ : MO A) ≼ₜᵢ (q, ∅ : MO A).
Proof.
  split.
  - eapply completeness_ti_fb.
  - eapply soundness_ti_fb.
Qed.

(** **** Corollary: the induced equivalences coincide *)

Corollary may_equiv_iff_same_traces `{
  gLtsObaFWP : @gLtsObaFW P A H gLtsEqP gLtsObaP,
  gLtsObaFWQ : @gLtsObaFW Q A H gLtsEqQ gLtsObaQ,
  gLtsT : !gLtsEq T H, gLtsObaT : !gLtsOba T _, !Testing_Predicate outcome _} {unique_nb : UniqueDual A}

  {_ : Prop_of_Inter P T A A dual}
  {_ : Prop_of_Inter Q T A A dual}

  {gen : trace A -> T} {gspec : may_test_spec gen}

  (p : P) (q : Q) :
  (p ⊑ₘₐᵧ q /\ q ⊑ₘₐᵧ p) <-> (∀ s, traces p s <-> traces q s).
Proof.
  split.
  - intros (hpq & hqp) s. split.
    + now eapply (equivalence_ti_fw p q).
    + now eapply (equivalence_ti_fw q p).
  - intro hsame. split.
    + eapply equivalence_ti_fw. intros s hs. now eapply hsame.
    + eapply equivalence_ti_fw. intros s hs. now eapply hsame.
Qed.