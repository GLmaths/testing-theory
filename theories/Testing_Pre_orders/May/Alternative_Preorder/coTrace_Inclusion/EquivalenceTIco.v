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

From stdpp Require Import decidable.
From TestingTheory Require Import ActTau gLts Bisimulation Lts_OBA Lts_OBA_FB Lts_FW
    coWeakTransition Testing_Predicate InteractionBetweenLts FiniteImageLTS Lts_Finite_Output_Chain
    MultisetLTSConstruction ForwarderConstruction May DefinitionTI CompletenessTI DefinitionTIco
    SoundnessTIco CompletenessTIco.

(** * The May preorder is co-trace inclusion

      [p ⊑ₘₐᵧ q  ↔  p ≼꜀ₒ₋ₜᵢ q]

    Mirrors [EquivalenceTI.v]: soundness needs nothing of the LTSs,
    completeness needs the forwarder axioms in full. As in
    [CompletenessTIco.v], completeness here is a thin wrapper around
    the plain [completeness_ti_fw]/[completeness_ti_fb], not a
    re-derivation. *)

(** ** Equivalence, for forwarders *)

Theorem equivalence_ti_co_fw `{
  gLtsObaFWP : @gLtsObaFW P A H gLtsEqP gLtsObaP,
  gLtsObaFWQ : @gLtsObaFW Q A H gLtsEqQ gLtsObaQ,
  gLtsT : !gLtsEq T H, gLtsObaT : !gLtsOba T, !Testing_Predicate outcome _}

  {_ : Prop_of_Inter P T A dual}
  {_ : Prop_of_Inter Q T A dual}

  {gen : trace A -> T} {gspec : may_test_spec gen}

  (p : P) (q : Q) :
  p ⊑ₘₐᵧ q <-> p ≼꜀ₒ₋ₜᵢ q.
Proof.
  split.
  - eapply completeness_ti_co_fw.
  - eapply soundness_ti_co_fw.
Qed.

(** ** Equivalence, for feedback LTSs, through the forwarder construction *)

Theorem equivalence_ti_co_fb `{
    @gLtsObaFB P A H gLtsEqP gLtsObaP, !FiniteOutputChain_LtsOba P, !FiniteImagegLts P A,
    @gLtsObaFB Q A H gLtsEqQ gLtsObaQ, !FiniteOutputChain_LtsOba Q, !FiniteImagegLts Q A,
    @gLtsObaFB T A H gLtsEqT gLtsObaT, !FiniteOutputChain_LtsOba T, !Testing_Predicate outcome _}

  {_ : Prop_of_Inter P (MO A) A fw_inter}
  {_ : Prop_of_Inter (P * MO A) T A dual}
  {_ : Prop_of_Inter P T A dual}

  {_ : Prop_of_Inter Q (MO A) A fw_inter}
  {_ : Prop_of_Inter (Q * MO A) T A dual}
  {_ : Prop_of_Inter Q T A dual}

  {gen : trace A -> T} {gspec : may_test_spec gen}

  (p : P) (q : Q) :
  p ⊑ₘₐᵧ q <-> (p, ∅ : MO A) ≼꜀ₒ₋ₜᵢ (q, ∅ : MO A).
Proof.
  split.
  - eapply completeness_ti_co_fb.
  - eapply soundness_ti_co_fb.
Qed.

(** ** Corollary: the induced equivalences coincide *)

Corollary may_equiv_iff_same_cotraces `{
  gLtsObaFWP : @gLtsObaFW P A H gLtsEqP gLtsObaP,
  gLtsObaFWQ : @gLtsObaFW Q A H gLtsEqQ gLtsObaQ,
  gLtsT : !gLtsEq T H, gLtsObaT : !gLtsOba T, !Testing_Predicate outcome _}

  {_ : Prop_of_Inter P T A dual}
  {_ : Prop_of_Inter Q T A dual}

  {gen : trace A -> T} {gspec : may_test_spec gen}

  (p : P) (q : Q) :
  (p ⊑ₘₐᵧ q /\ q ⊑ₘₐᵧ p) <-> (∀ s, traces_co p s <-> traces_co q s).
Proof.
  split.
  - intros (hpq & hqp) s. split.
    + now eapply (equivalence_ti_co_fw p q).
    + now eapply (equivalence_ti_co_fw q p).
  - intro hsame. split.
    + eapply equivalence_ti_co_fw. intros s hs. now eapply hsame.
    + eapply equivalence_ti_co_fw. intros s hs. now eapply hsame.
Qed.
