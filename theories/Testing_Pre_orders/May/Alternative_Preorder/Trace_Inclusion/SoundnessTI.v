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
From stdpp Require Import decidable.
From TestingTheory Require Import gLts Bisimulation Lts_OBA_FB Lts_FW Testing_Predicate InteractionBetweenLts FiniteImageLTS Lts_Finite_Output_Chain MultisetLTSConstruction ForwarderConstruction May LiftMay DefinitionTI.

(** * Soundness of the trace-inclusion preorder for May

    Soundness: the alternative (behavioural) preorder implies the contextual one,

      [p ≼ₜᵢ q  →  p ⊑ₘₐᵧ q].

    The argument is purely about traces. If [p] passes a test [t], then by
    [may_to_wt] the pair [(p, t)] has a successful computation whose server
    projection is some trace [s], the client following the co-trace [coₜ s].
    Trace inclusion hands us the *same* trace [s] on the [q] side, and [wt_to_may]
    replays the very same computation with [q] in place of [p] — the client [t] is
    untouched, so it still reaches the same successful state. *)

(** ** Soundness, for arbitrary LTSs *)

Section Soundness_ti.

Context `{gLtsP : @gLts P A H, gLtsQ : !gLts Q H}.
Context `{gLtsT : !gLtsEq T H, !Testing_Predicate outcome gLtsT}.
(* non-generalising binders: the [gLts] instances are [gLtsP], [gLtsQ], [gLtsT] *)
Context {PInter : Prop_of_Inter P T A dual}.
Context {QInter : Prop_of_Inter Q T A dual}.

Theorem soundness_ti (p : P) (q : Q) : p ≼ₜᵢ q -> p ⊑ₘₐᵧ q.
Proof.
  intros hti t hm.
  (* the successful computation of [p] against [t] yields a trace [s] of [p],
     the client [t] answering with the co-trace [coₜ s] *)
  eapply may_to_wt in hm as (s & p' & t' & wS & wC & happy).
  (* trace inclusion: [q] performs the same trace [s] *)
  destruct (hti s (ex_intro _ p' wS)) as (q' & wQ).
  (* replay the computation, with the very same client run *)
  eapply wt_to_may; eauto.
Qed.

End Soundness_ti.

(** ** Soundness, for forwarders

    The statement asked for: [p] and [q] live in forwarder LTSs ([gLtsObaFW]).
    The forwarder axioms are not needed for soundness — they are what completeness
    relies on, in order to build a test out of a trace — so this is a direct
    instance of [soundness_ti] above. *)

Theorem soundness_ti_fw `{
  gLtsObaFWP : @gLtsObaFW P A H gLtsEqP gLtsObaP,
  gLtsObaFWQ : @gLtsObaFW Q A H gLtsEqQ gLtsObaQ,
  gLtsT : !gLtsEq T H, !Testing_Predicate outcome gLtsT}

  {_ : Prop_of_Inter P T A dual}
  {_ : Prop_of_Inter Q T A dual}

  (p : P) (q : Q) :
  p ≼ₜᵢ q -> p ⊑ₘₐᵧ q.
Proof. eapply soundness_ti. Qed.

(** ** Soundness, for feedback LTSs, through the forwarder construction

    An LTS satisfying only the feedback axioms ([gLtsObaFB]) is not a forwarder,
    so [soundness_ti_fw] does not apply to it directly. But it can be turned into
    one: [toFW gLtsP] equips [P * MO A] with a [gLtsObaFW] structure
    ([toFWObaFW]), and the forwarder construction is transparent for [may]
    ([may_iff_may_fw] : [p may_pass t <-> (p, ∅) may_pass t]), hence for the
    contextual preorder itself ([lift_fw_ctx_pre]).

    So it suffices to compare the *lifted* processes [(p, ∅)] and [(q, ∅)] by
    trace inclusion to conclude about [p] and [q]. *)

Theorem soundness_ti_fb `{
    @gLtsObaFB P A H gLtsEqP gLtsObaP, !FiniteOutputChain_LtsOba P, !FiniteImagegLts P A,
    @gLtsObaFB Q A H gLtsEqQ gLtsObaQ, !FiniteOutputChain_LtsOba Q, !FiniteImagegLts Q A,
    @gLtsObaFB T A H gLtsEqT gLtsObaT, !FiniteOutputChain_LtsOba T, !Testing_Predicate outcome _}

  {_ : Prop_of_Inter P (MO A) A fw_inter}
  {_ : Prop_of_Inter (P * MO A) T A dual}
  {_ : Prop_of_Inter P T A dual}

  {_ : Prop_of_Inter Q (MO A) A fw_inter}
  {_ : Prop_of_Inter (Q * MO A) T A dual}
  {_ : Prop_of_Inter Q T A dual}

  (p : P) (q : Q) :
  (p, ∅ : MO A) ≼ₜᵢ (q, ∅ : MO A) -> p ⊑ₘₐᵧ q.
Proof.
  intro hti.
  (* [may] is preserved by the forwarder construction, so it is enough to prove
     the contextual preorder on the lifted processes *)
  eapply lift_fw_ctx_pre.
  (* [(p, ∅)] and [(q, ∅)] live in forwarder LTSs: apply the general soundness *)
  eapply soundness_ti. exact hti.
Qed.
