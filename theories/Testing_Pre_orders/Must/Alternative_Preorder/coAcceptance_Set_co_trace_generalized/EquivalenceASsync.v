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
(* * The co-acceptance-set characterisation, for two alphabets

    The [FWⁿ] characterisation for two alphabets.  The observers,
    and the co-traces, live on [Atest].  The processes are forwarders over
    [Aproc ⊎ Atest ⊎ cobar Atest] ([MemForwarder.v]): they satisfy
    [gLtsFWMem], i.e. [boomerang], [feedback] and [delay] at the observer's
    emissions, receiving the message as [inr (cobar η)] and giving it back as
    [inr (msg η)].  Nothing is asked of [sync].

    The [Lⁿ] section, for arbitrary processes over [Aproc], goes through
    [LiftMem.lift_fw_ctx_pre]: the forwarder [toFw] of [ForwarderMem.v] stores
    the test's pending outputs as [msg η], over [Atest]. *)
(* end hide *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From Stdlib Require Import Relations.Relation_Definitions Classes.RelationClasses.
From stdpp Require Import base countable decidable finite gmap list.

From TestingTheory Require Import ActTau gLts SyncActions MemAction InteractionUnion MemForwarder Bisimulation Lts_OBA
  Lts_OBA_FB Lts_FW Subset_Act Termination WeakTransitions
  coWeakSync FiniteImageLTS coFiniteImage coSetLTSConstruction Testing_Predicate StateTransitionSystems InteractionBetweenLts
  Must CompletenessASsync
  DefinitionASrel CompletenessASsync SoundnessASsync
  coWeakTransition coConvergence
  Lts_Finite_Non_Blocking_Chain MultisetLTSConstruction ForwarderMem LiftMem
  Label_Abstraction.LabelAbstraction LabelAdmissible LabelAdmissibleFw.
(* begin hide *)
#[local] Hint Mode ExtAction ! : typeclass_instances.

Section PreorderSync.

Context {P Q T PreAct Aproc Atest : Type}.
Context `{CC : Countable PreAct}.
Context `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest} `{SA : !SyncAction Aproc Atest}.
Context (Γ : Atest → PreAct).
Context (outcome : T → Prop).

Context `{gLtsEqT : !gLtsEq T Ht} `{gLtsObaT : !gLtsOba T _} `{!gLtsObaFB T Atest}.
Context `{TP : !Testing_Predicate outcome gLtsEqT}.

Context `{gLtsEqP : !gLtsEq P (@ExtAction_sum Aproc (MemAct Atest) Hp (@ExtAction_mem Atest Ht))} `{FWP : !gLtsFWMem P Aproc Atest}.
Context `{SYP : !Prop_of_Inter P T (Aproc + MemAct Atest) Atest sync} `{CFIP : !coFiniteImagegLts P Atest}.
Context `{FAP : !FinitaryAbsActionG (Aproc := (Aproc + MemAct Atest)) (Hp := ExtAction_sum) (SA := SyncAction_mem) P T (Γ : Atest → PreAct)}.

Context `{gLtsEqQ : !gLtsEq Q (@ExtAction_sum Aproc (MemAct Atest) Hp (@ExtAction_mem Atest Ht))} `{FWQ : !gLtsFWMem Q Aproc Atest}.
Context `{SYQ : !Prop_of_Inter Q T (Aproc + MemAct Atest) Atest sync} `{CFIQ : !coFiniteImagegLts Q Atest}.
Context `{FAQ : !FinitaryAbsActionG (Aproc := (Aproc + MemAct Atest)) (Hp := ExtAction_sum) (SA := SyncAction_mem) Q T (Γ : Atest → PreAct)}.

Context (tconv : list Atest → T) `{!test_convergence_spec tconv}.
Context (ta : gset PreAct → list Atest → T)
        `{!test_co_acceptance_set_spec ta Γ}.

Theorem equivalence_fw_acc_set_and_must_i_sync_co_trace (p : P) (q : Q) :
  p ⊆ₘᵤₛₜᵢ q ↔
  p ≼ᴳ[ Γ ] q.
Proof.
  split.
  - intros hpre.
    by eapply (completeness_fw_co_sync (tconv := tconv) (ta := ta)).
  - intros hpre.
    by eapply (soundness_fw_co_sync Γ outcome).
Qed.

End PreorderSync.

Section PreorderSyncLifted.

Context {P Q T PreAct Aproc Atest : Type}.
Context `{CC : Countable PreAct}.
Context `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest} `{SA : !SyncAction Aproc Atest}.
Context (Γ : Atest → PreAct).
Context (outcome : T → Prop).

Context `{gLtsEqT : !gLtsEq T Ht} `{gLtsObaT : !gLtsOba T _} `{!gLtsObaFB T Atest}
        `{!FiniteNonBlockingChain_LtsOba T}.
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
Context `{FAP : !FinitaryAbsActionG (Aproc := (Aproc + MemAct Atest)) (Hp := ExtAction_sum) (SA := SyncAction_mem) (P * MO (MemAct Atest)) T (Γ : Atest → PreAct)}.
Context `{SYQ : !Prop_of_Inter (Q * MO (MemAct Atest)) T (Aproc + MemAct Atest) Atest sync}
        `{CFIQ : !coFiniteImagegLts (Q * MO (MemAct Atest)) Atest}.
Context `{FAQ : !FinitaryAbsActionG (Aproc := (Aproc + MemAct Atest)) (Hp := ExtAction_sum) (SA := SyncAction_mem) (Q * MO (MemAct Atest)) T (Γ : Atest → PreAct)}.

Context (tconv : list Atest → T) `{!test_convergence_spec tconv}.
Context (ta : gset PreAct → list Atest → T)
        `{!test_co_acceptance_set_spec ta Γ}.

Theorem equivalence_acc_set_and_must_i_sync_co_trace (p : P) (q : Q) :
  ctx_pre (gLtsT := gLtsEqT) p q ↔
  (p, ∅ : MO (MemAct Atest)) ≼ᴳ[ Γ ] (q, ∅ : MO (MemAct Atest)).
Proof.
  rewrite (lift_fw_ctx_pre outcome).
  exact (equivalence_fw_acc_set_and_must_i_sync_co_trace Γ outcome tconv ta _ _).
Qed.

End PreorderSyncLifted.

Section PreorderRel.

Context {P Q T Aproc Atest : Type}.
Context `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest} `{SA : !SyncAction Aproc Atest}.
Context (R : relation Atest) `{!Equivalence R} `{!RelDecision R}.
Context (outcome : T → Prop).

Context `{gLtsEqT : !gLtsEq T Ht} `{gLtsObaT : !gLtsOba T _} `{!gLtsObaFB T Atest}.
Context `{TP : !Testing_Predicate outcome gLtsEqT}.

Context `{gLtsEqP : !gLtsEq P (@ExtAction_sum Aproc (MemAct Atest) Hp (@ExtAction_mem Atest Ht))} `{FWP : !gLtsFWMem P Aproc Atest}.
Context `{SYP : !Prop_of_Inter P T (Aproc + MemAct Atest) Atest sync} `{CFIP : !coFiniteImagegLts P Atest}.
Context `{AdmP : !@LA_admissible P T (Aproc + MemAct Atest) ExtAction_sum _ Atest Ht _ SyncAction_mem R}.
Context `{FinP : !@FinitaryLA P (Aproc + MemAct Atest) ExtAction_sum _ Atest Ht SyncAction_mem R _ _}.

Context `{gLtsEqQ : !gLtsEq Q (@ExtAction_sum Aproc (MemAct Atest) Hp (@ExtAction_mem Atest Ht))} `{FWQ : !gLtsFWMem Q Aproc Atest}.
Context `{SYQ : !Prop_of_Inter Q T (Aproc + MemAct Atest) Atest sync} `{CFIQ : !coFiniteImagegLts Q Atest}.
Context `{AdmQ : !@LA_admissible Q T (Aproc + MemAct Atest) ExtAction_sum _ Atest Ht _ SyncAction_mem R}.
Context `{FinQ : !@FinitaryLA Q (Aproc + MemAct Atest) ExtAction_sum _ Atest Ht SyncAction_mem R _ _}.

Context (tconv : list Atest → T) `{!test_convergence_spec tconv}.
Context (ta : gset (LA_quotient R) → list Atest → T)
        `{!test_co_acceptance_set_spec ta (LA_class R)}.

#[local] Instance FAP_rel : FinitaryAbsActionG (Aproc := (Aproc + MemAct Atest)) (Hp := ExtAction_sum) (SA := SyncAction_mem) P T (LA_class R) :=
  FinitaryAbsActionG_of_LA R AdmP FinP.

#[local] Instance FAQ_rel : FinitaryAbsActionG (Aproc := (Aproc + MemAct Atest)) (Hp := ExtAction_sum) (SA := SyncAction_mem) Q T (LA_class R) :=
  FinitaryAbsActionG_of_LA R AdmQ FinQ.

Theorem equivalence_fw_rel_and_must_i_sync_co_trace (p : P) (q : Q) :
  p ⊆ₘᵤₛₜᵢ q ↔
  p ≼ᴿ[ R ] q.
Proof.
  rewrite (bhv_pre_r_iff_g R).
  exact (equivalence_fw_acc_set_and_must_i_sync_co_trace (LA_class R) outcome tconv ta p q).
Qed.

End PreorderRel.

Section PreorderRelLifted.

Context {P Q T Aproc Atest : Type}.
Context `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest} `{SA : !SyncAction Aproc Atest}.
Context (R : relation Atest) `{!Equivalence R} `{!RelDecision R}.
Context (outcome : T → Prop).

Context `{gLtsEqT : !gLtsEq T Ht} `{gLtsObaT : !gLtsOba T _} `{!gLtsObaFB T Atest}
        `{!FiniteNonBlockingChain_LtsOba T}.
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
Context `{AdmP : !@LA_admissible (P * MO (MemAct Atest)) T (Aproc + MemAct Atest) ExtAction_sum _
                    Atest Ht _ SyncAction_mem R}.
Context `{FinP : !@FinitaryLA (P * MO (MemAct Atest)) (Aproc + MemAct Atest) ExtAction_sum _
                    Atest Ht SyncAction_mem R _ _}.
Context `{SYQ : !Prop_of_Inter (Q * MO (MemAct Atest)) T (Aproc + MemAct Atest) Atest sync}
        `{CFIQ : !coFiniteImagegLts (Q * MO (MemAct Atest)) Atest}.
Context `{AdmQ : !@LA_admissible (Q * MO (MemAct Atest)) T (Aproc + MemAct Atest) ExtAction_sum _
                    Atest Ht _ SyncAction_mem R}.
Context `{FinQ : !@FinitaryLA (Q * MO (MemAct Atest)) (Aproc + MemAct Atest) ExtAction_sum _
                    Atest Ht SyncAction_mem R _ _}.

Context (tconv : list Atest → T) `{!test_convergence_spec tconv}.
Context (ta : gset (LA_quotient R) → list Atest → T)
        `{!test_co_acceptance_set_spec ta (LA_class R)}.

Theorem equivalence_rel_and_must_i_sync_co_trace (p : P) (q : Q) :
  ctx_pre (gLtsT := gLtsEqT) p q ↔
  (p, ∅ : MO (MemAct Atest)) ≼ᴿ[ R ] (q, ∅ : MO (MemAct Atest)).
Proof.
  rewrite (lift_fw_ctx_pre outcome).
  exact (equivalence_fw_rel_and_must_i_sync_co_trace R outcome tconv ta _ _).
Qed.

End PreorderRelLifted.

Section PreorderRelProcesses.

Context {P Q T Aproc Atest : Type}.
Context `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest} `{SA : !SyncAction Aproc Atest}.
Context (R : relation Atest) `{!Equivalence R} `{!RelDecision R}.
Context (outcome : T → Prop).

Context `{gLtsEqT : !gLtsEq T Ht} `{gLtsObaT : !gLtsOba T _} `{!gLtsObaFB T Atest}
        `{!FiniteNonBlockingChain_LtsOba T}.
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
Context `{SYQ : !Prop_of_Inter (Q * MO (MemAct Atest)) T (Aproc + MemAct Atest) Atest sync}
        `{CFIQ : !coFiniteImagegLts (Q * MO (MemAct Atest)) Atest}.

Context (AdmP : @LA_admissible P T Aproc Hp _ Atest Ht _ SA R).
Context (FinP : @FinitaryLA P Aproc Hp _ Atest Ht SA R _ _).
Context (AdmQ : @LA_admissible Q T Aproc Hp _ Atest Ht _ SA R).
Context (FinQ : @FinitaryLA Q Aproc Hp _ Atest Ht SA R _ _).

Context (AdmM : LA_admissible_mem (T := T) R).
Context (co_rep : Atest → list Atest).
Context (co_rep_sub : ∀ η x, non_blocking η → x ∈ co_rep η → dual η x).
Context (co_rep_cover : ∀ η β, non_blocking η → dual η β → ∃ x, x ∈ co_rep η ∧ R β x).

Context (tconv : list Atest → T) `{!test_convergence_spec tconv}.
Context (ta : gset (LA_quotient R) → list Atest → T)
        `{!test_co_acceptance_set_spec ta (LA_class R)}.

Definition AdmP_fw := LA_admissible_fw (P := P) R AdmP AdmM.
Definition AdmQ_fw := LA_admissible_fw (P := Q) R AdmQ AdmM.
Definition FinP_fw := FinitaryLA_fw (P := P) R co_rep co_rep_sub co_rep_cover FinP.
Definition FinQ_fw := FinitaryLA_fw (P := Q) R co_rep co_rep_sub co_rep_cover FinQ.
#[local] Existing Instances AdmP_fw AdmQ_fw FinP_fw FinQ_fw.

Theorem equivalence_rel_and_must_i_sync_co_trace_proc (p : P) (q : Q) :
  ctx_pre (gLtsT := gLtsEqT) p q ↔
  (p, ∅ : MO (MemAct Atest)) ≼ᴿ[ R ] (q, ∅ : MO (MemAct Atest)).
Proof. exact (equivalence_rel_and_must_i_sync_co_trace R outcome tconv ta p q). Qed.

End PreorderRelProcesses.
(* end hide *)
