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

From Stdlib.Lists Require Import List.
From stdpp Require Import base decidable.
From TestingTheory Require Import ActTau gLts Bisimulation Lts_OBA Lts_OBA_FB Lts_FW WeakTransitions
    coWeakTransition Testing_Predicate InteractionBetweenLts FiniteImageLTS Lts_Finite_Output_Chain
    MultisetLTSConstruction ForwarderConstruction May LiftMay DefinitionTI CompletenessTI DefinitionTIco.

(** * Completeness of the co-trace-inclusion preorder for May

      [p ⊑ₘₐᵧ q  →  p ≼꜀ₒ₋ₜᵢ q]   (for forwarders)

    Unlike [SoundnessTIco.v], this is *not* a mechanical [⟹[s] → ⟹ᶜᵒ[s]]
    port of [CompletenessTI.v] — that file's [completeness_core] builds
    a canonical test [gen (coₜ s)] and is saturated with [coₜ]/
    [unique_nb] throughout (peeling dual pairs off a literal co-trace).
    Redoing that machinery Forall2-dual style would mean rebuilding
    most of [InteractionBetweenLts.v]'s search infrastructure for no
    mathematical gain (see the [unique_nb] removal writeup for
    [gLtsMBCoFinite] — the same trap applies here).

    Instead, [completeness_ti_co_fw] is a thin wrapper around the
    *unchanged* [completeness_ti_fw] from [CompletenessTI.v]: [traces_co
    p s] only asserts that [p] performs *some* trace pointwise-dual to
    [s] ([cowt_to_wt_dual]), so we recover that literal trace [s'],
    hand it to the plain completeness theorem to get [q] performing
    [s'] too, and convert back to [q ⟹ᶜᵒ[s] q'] along the very same
    dual witness ([wt_to_cowt_dual]). Neither bridge lemma needs
    [unique_nb] — [Forall2 dual] carries the witness explicitly instead
    of recomputing it — so this file never invokes [unique_nb] itself,
    even though the plain completeness theorem it reuses internally
    does (to build its canonical test, an orthogonal concern). *)

(** ** Completeness, for forwarders *)

Theorem completeness_ti_co_fw `{
  gLtsObaFWP : @gLtsObaFW P A H gLtsEqP gLtsObaP,
  gLtsObaFWQ : @gLtsObaFW Q A H gLtsEqQ gLtsObaQ,
  gLtsT : !gLtsEq T H, gLtsObaT : !gLtsOba T, !Testing_Predicate outcome _}

  {_ : Prop_of_Inter P T A dual}
  {_ : Prop_of_Inter Q T A dual}

  {gen : trace A -> T} {gspec : may_test_spec gen}

  (p : P) (q : Q) :
  p ⊑ₘₐᵧ q -> p ≼꜀ₒ₋ₜᵢ q.
Proof.
  intros hctx s (p' & wSco).
  (* [p] co-answers [s] along some literal dual witness [s'] *)
  eapply cowt_to_wt_dual in wSco as (s' & hforall & wS).
  (* plain completeness: [q] performs that very same literal trace [s'] *)
  destruct (completeness_ti_fw p q hctx s' (ex_intro _ p' wS)) as (q' & wQ).
  (* convert back to a co-answer of [s], along the same dual witness [s'] *)
  exists q'. eapply wt_to_cowt_dual; [exact wQ | exact hforall].
Qed.

(** ** Completeness, for feedback LTSs, through the forwarder construction

    Same wrapping strategy, built on top of the unchanged
    [completeness_ti_fb] rather than re-deriving the forwarder lift. *)

Theorem completeness_ti_co_fb `{
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
  p ⊑ₘₐᵧ q -> (p, ∅ : MO A) ≼꜀ₒ₋ₜᵢ (q, ∅ : MO A).
Proof.
  intros hctx s (p' & wSco).
  eapply cowt_to_wt_dual in wSco as (s' & hforall & wS).
  destruct (completeness_ti_fb p q hctx s' (ex_intro _ p' wS)) as (q' & wQ).
  exists q'. eapply wt_to_cowt_dual; [exact wQ | exact hforall].
Qed.
