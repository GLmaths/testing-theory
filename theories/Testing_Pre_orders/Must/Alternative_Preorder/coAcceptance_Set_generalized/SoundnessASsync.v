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

(** * Soundness for the co-acceptance-set preorder, for two alphabets

    [SoundnessASco.v] with the co-steps of [coWeakSync.v].  A set of processes
    is tested by one observer, and the set's meta-steps are indexed by /test/
    actions ([coSetLTSConstruction.v]). *)

From Stdlib Require ssreflect Setoid.
From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From Stdlib.Program Require Import Wf Equality.
From Stdlib.Wellfounded Require Import Inverse_Image.

From stdpp Require Import base countable finite gmap list decidable.

From TestingTheory Require Import ActTau InFiniteSetHelper InListPropHelper.
From TestingTheory Require Import gLts SyncActions UnionAction UnionSync SyncForwarder Bisimulation Lts_OBA
  Lts_Finite_Output_Chain Lts_FW Lts_OBA_FB Lts_CN
  Subset_Act Termination Convergence WeakTransitions Testing_Predicate
  StateTransitionSystems InteractionBetweenLts
  Must.
From TestingTheory Require Import SoundnessASco coWeakSync FiniteImageLTS coFiniteImage coSetLTSConstruction DefinitionAS DefinitionASco coWeakTransition coConvergence.


(** ** Soundness on forwarders, for two alphabets

    [gLtsCNenabledSync Q] is built from the forwarder axioms and put
    in scope as a local instance — leaving it to be discharged by [Unshelve],
    as [SoundnessASco.v] does, makes elaboration search for an instance that
    is not there yet, and that search does not terminate in reasonable
    space. *)

Section SoundnessFW_sync.

Context {P Q T FinA PreAct Aproc Atest : Type}.
Context `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest} `{FS : !FwSync Aproc Atest}.
Context (Φ : Atest → FinA) (𝝳 : FinA → PreAct).
Context (outcome : T → Prop).
Context `{gLtsEqT : !gLtsEq T Ht} `{TP : !Testing_Predicate outcome gLtsEqT}.
Context `{gLtsEqP : !gLtsEq P ExtAction_fw} `{SYP : !Prop_of_Inter P T (Aproc + Atest) Atest sync}
        `{CFIP : !coFiniteImagegLts P Atest}.
Context `{gLtsEqQ : !gLtsEq Q ExtAction_fw} `{gLtsObaQ : !gLtsOba Q} `{FWQ : !gLtsObaFWSync Q Aproc Atest}
        `{SYQ : !Prop_of_Inter Q T (Aproc + Atest) Atest sync}
        `{CFIQ : !coFiniteImagegLts Q Atest}.
Context `{AbsPT : !@AbsAction P T FinA PreAct Atest Ht Φ 𝝳 (Aproc + Atest) ExtAction_fw _ _ SyncAction_fw}.
Context `{AbsQT : !@AbsAction Q T FinA PreAct Atest Ht Φ 𝝳 (Aproc + Atest) ExtAction_fw _ _ SyncAction_fw}.

#[local] Instance CN_of_FW : gLtsCNenabledSync Q (Aproc + Atest) Atest.
Proof.
  apply MkgLtsCNenabledSync. intros q1 η nb.
  destruct (fw_boomerang_total q1 η nb) as (μ & q2 & hsy & l & _).
  by exists (inl μ), q2.
Qed.

Lemma soundness_fw_co_sync (p : P) (q : Q) :
  p ≼꜀ₒ₋ₐₛ q →
  p ⊆ₘᵤₛₜᵢ q.
Proof. by eapply (soundness_co_nb_enabled_co outcome Φ 𝝳). Qed.

End SoundnessFW_sync.
