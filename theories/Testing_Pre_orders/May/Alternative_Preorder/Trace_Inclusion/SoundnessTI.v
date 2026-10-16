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

From Stdlib.Lists Require Import List.
From stdpp Require Import decidable.
From TestingTheory Require Import ActTau gLts Bisimulation Lts_OBA_FB Lts_FW Testing_Predicate InteractionBetweenLts FiniteImageLTS Lts_Finite_Non_Blocking_Chain MultisetLTSConstruction ForwarderConstruction May LiftMay DefinitionTI.
(** ***** Soundness of the trace-inclusion preorder for May *)

(** ****** Soundness, for arbitrary LTSs *)

Section Soundness_ti.

Context `{gLtsP : @gLts P A H, gLtsQ : !gLts Q H}.
Context {unique_nb : UniqueDual A}.
Context `{gLtsT : !gLtsEq T H, !Testing_Predicate outcome gLtsT}.
Context {PInter : Prop_of_Inter P T A A dual}.
Context {QInter : Prop_of_Inter Q T A A dual}.

Theorem soundness_ti (p : P) (q : Q) : p ≼ₜᵢ q -> p ⊑ₘₐᵧ q.
Proof.
  intros hti t hm.
  eapply may_to_wt in hm as (s & p' & t' & wS & wC & happy).
  destruct (hti s (ex_intro _ p' wS)) as (q' & wQ).
  eapply wt_to_may; eauto.
Qed.

End Soundness_ti.

(** ***** Soundness, for forwarders *)

Theorem soundness_ti_fw `{
  gLtsObaFWP : @gLtsObaFW P A H gLtsEqP gLtsObaP,
  gLtsObaFWQ : @gLtsObaFW Q A H gLtsEqQ gLtsObaQ,
  gLtsT : !gLtsEq T H, !Testing_Predicate outcome gLtsT} {unique_nb : UniqueDual A}

  {_ : Prop_of_Inter P T A A dual}
  {_ : Prop_of_Inter Q T A A dual}

  (p : P) (q : Q) :
  p ≼ₜᵢ q -> p ⊑ₘₐᵧ q.
Proof. eapply soundness_ti. Qed.

(** ****** Soundness, for feedback LTSs *)

Theorem soundness_ti_fb `{
    @gLtsObaFB P A H gLtsEqP gLtsObaP, !FiniteNonBlockingChain_LtsOba P, !FiniteImagegLts P A,
    @gLtsObaFB Q A H gLtsEqQ gLtsObaQ, !FiniteNonBlockingChain_LtsOba Q, !FiniteImagegLts Q A,
    @gLtsObaFB T A H gLtsEqT gLtsObaT, !FiniteNonBlockingChain_LtsOba T, !Testing_Predicate outcome _} {unique_nb : UniqueDual A}

  {_ : Prop_of_Inter P (MO A) A A fw_inter}
  {_ : Prop_of_Inter (P * MO A) T A A dual}
  {_ : Prop_of_Inter P T A A dual}

  {_ : Prop_of_Inter Q (MO A) A A fw_inter}
  {_ : Prop_of_Inter (Q * MO A) T A A dual}
  {_ : Prop_of_Inter Q T A A dual}

  (p : P) (q : Q) :
  (p, ∅ : MO A) ≼ₜᵢ (q, ∅ : MO A) -> p ⊑ₘₐᵧ q.
Proof.
  intro hti.
  eapply lift_fw_ctx_pre.
  eapply soundness_ti. exact hti.
Qed.