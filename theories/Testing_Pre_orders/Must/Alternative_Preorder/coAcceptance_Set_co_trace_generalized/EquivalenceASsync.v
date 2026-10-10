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

(* * The co-acceptance-set characterisation, for two alphabets

    [EquivalenceASco.v]'s [FWⁿ] section for two alphabets.  The observers,
    and the co-traces, live on [Atest].  The processes are forwarders over
    [Aproc ⊎ Atest ⊎ cobar Atest] ([MemForwarder.v]): they satisfy
    [gLtsFWMem], i.e. [boomerang], [feedback] and [delay] at the observer's
    emissions, receiving the message as [inr (cobar η)] and giving it back as
    [inr (msg η)].  Nothing is asked of [sync].

    The [Lⁿ] section, for arbitrary processes over [Aproc], goes through
    [LiftMem.lift_fw_ctx_pre]: the forwarder [toFw] of [ForwarderMem.v] stores
    the test's pending outputs as [msg η], over [Atest]. *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable finite gmap list.

From TestingTheory Require Import ActTau gLts SyncActions MemAction InteractionUnion MemForwarder Bisimulation Lts_OBA
  Lts_OBA_FB Lts_FW Subset_Act Termination WeakTransitions
  coWeakSync FiniteImageLTS coFiniteImage coSetLTSConstruction Testing_Predicate StateTransitionSystems InteractionBetweenLts
  Must Completeness CompletenessASco
  DefinitionAS DefinitionASco CompletenessASsync SoundnessASsync
  coWeakTransition coConvergence
  Lts_Finite_Output_Chain MultisetLTSConstruction ForwarderMem LiftMem.

#[local] Hint Mode ExtAction ! : typeclass_instances.

Section PreorderSync.

Context {P Q T FinA PreAct Aproc Atest : Type}.
Context `{CC : Countable PreAct}.
Context `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest} `{SA : !SyncAction Aproc Atest}.
Context (Φ : Atest → FinA) (𝝳 : FinA → PreAct).
Context (outcome : T → Prop).

Context `{gLtsEqT : !gLtsEq T Ht} `{gLtsObaT : !gLtsOba T} `{!gLtsObaFB T Atest}.
Context `{TP : !Testing_Predicate outcome gLtsEqT}.

Context `{gLtsEqP : !gLtsEq P (@ExtAction_sum Aproc (MemAct Atest) Hp (@ExtAction_mem Atest Ht))} `{FWP : !gLtsFWMem P Aproc Atest}.
Context `{SYP : !Prop_of_Inter P T (Aproc + MemAct Atest) Atest sync} `{CFIP : !coFiniteImagegLts P Atest}.
Context `{FAP : !@FinitaryAbsAction P T FinA PreAct Atest Ht Φ 𝝳 (Aproc + MemAct Atest) ExtAction_sum _ _ SyncAction_mem _ _}.

Context `{gLtsEqQ : !gLtsEq Q (@ExtAction_sum Aproc (MemAct Atest) Hp (@ExtAction_mem Atest Ht))} `{FWQ : !gLtsFWMem Q Aproc Atest}.
Context `{SYQ : !Prop_of_Inter Q T (Aproc + MemAct Atest) Atest sync} `{CFIQ : !coFiniteImagegLts Q Atest}.
Context `{FAQ : !@FinitaryAbsAction Q T FinA PreAct Atest Ht Φ 𝝳 (Aproc + MemAct Atest) ExtAction_sum _ _ SyncAction_mem _ _}.

Context (tconv : list Atest → T) `{!test_convergence_spec tconv}.
Context (ta : gset PreAct → list Atest → T)
        `{!test_co_acceptance_set_spec PreAct ta (fun x => 𝝳 (Φ x))}.

(* ** The co-acceptance-set preorder is the must preorder, on forwarders *)

Theorem equivalence_fw_acc_set_and_must_i_sync_co_trace (p : P) (q : Q) :
  p ⊆ₘᵤₛₜᵢ q ↔
  p ≼꜀ₒ₋ₐₛ q.
Proof.
  split.
  - intros hpre.
    by eapply (completeness_fw_co_sync (tconv := tconv) (ta := ta)).
  - intros hpre.
    by eapply (soundness_fw_co_sync Φ 𝝳 outcome).
Qed.

End PreorderSync.

Section PreorderSyncLifted.

Context {P Q T FinA PreAct Aproc Atest : Type}.
Context `{CC : Countable PreAct}.
Context `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest} `{SA : !SyncAction Aproc Atest}.
Context (Φ : Atest → FinA) (𝝳 : FinA → PreAct).
Context (outcome : T → Prop).

Context `{gLtsEqT : !gLtsEq T Ht} `{gLtsObaT : !gLtsOba T} `{!gLtsObaFB T Atest}
        `{!FiniteOutputChain_LtsOba T}.
Context `{TP : !Testing_Predicate outcome gLtsEqT}.

Context `{gLtsEqP : !gLtsEq P Hp}.
Context `{PIP : !Prop_of_Inter P (MO (MemAct Atest)) Aproc (MemAct Atest) fw_inter_mem}.
Context `{PIPT : !Prop_of_Inter P T Aproc Atest sync}.
Context `{gLtsEqQ : !gLtsEq Q Hp}.
Context `{PIQ : !Prop_of_Inter Q (MO (MemAct Atest)) Aproc (MemAct Atest) fw_inter_mem}.
Context `{PIQT : !Prop_of_Inter Q T Aproc Atest sync}.

#[local] Existing Instance toFwEq.

Context `{SYP : !Prop_of_Inter (P * MO (MemAct Atest)) T (Aproc + MemAct Atest) Atest sync}
        `{CFIP : !coFiniteImagegLts (P * MO (MemAct Atest)) Atest}.
Context `{FAP : !@FinitaryAbsAction (P * MO (MemAct Atest)) T FinA PreAct Atest Ht Φ 𝝳
                  (Aproc + MemAct Atest) ExtAction_sum _ _ SyncAction_mem _ _}.
Context `{SYQ : !Prop_of_Inter (Q * MO (MemAct Atest)) T (Aproc + MemAct Atest) Atest sync}
        `{CFIQ : !coFiniteImagegLts (Q * MO (MemAct Atest)) Atest}.
Context `{FAQ : !@FinitaryAbsAction (Q * MO (MemAct Atest)) T FinA PreAct Atest Ht Φ 𝝳
                  (Aproc + MemAct Atest) ExtAction_sum _ _ SyncAction_mem _ _}.

Context (tconv : list Atest → T) `{!test_convergence_spec tconv}.
Context (ta : gset PreAct → list Atest → T)
        `{!test_co_acceptance_set_spec PreAct ta (fun x => 𝝳 (Φ x))}.

Theorem equivalence_acc_set_and_must_i_sync_co_trace (p : P) (q : Q) :
  ctx_pre (gLtsT := gLtsEqT) p q ↔
  (p, ∅ : MO (MemAct Atest)) ≼꜀ₒ₋ₐₛ (q, ∅ : MO (MemAct Atest)).
Proof.
  rewrite (lift_fw_ctx_pre outcome).
  exact (equivalence_fw_acc_set_and_must_i_sync_co_trace Φ 𝝳 outcome tconv ta _ _).
Qed.

End PreorderSyncLifted.
(* end hide *)
