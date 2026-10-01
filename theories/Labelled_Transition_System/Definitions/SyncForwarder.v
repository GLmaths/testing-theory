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

(** * Forwarders over [Aproc ⊎ Atest]

    The forwarder's memory receives the observer's messages as /process/
    actions and gives them back under the observer's own names.  For an
    emission [η : Atest] of the observer and a process reception [μ] that
    matches it ([fsync μ η]):

    - [fw_boomerang]: [p1 ⟶[inl μ] p2 ⟶[inr η] p1];
    - [fw_feedback]: giving [inr η] back and then receiving it with [inl μ]
      is a τ, or nothing;
    - [fw_inr_output]: the forwarder's [Atest] actions are emissions only —
      it never receives under an observer's name.

    Only the observer's emissions are concerned: nothing is asked about
    process actions that no observer emission names. *)

From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base countable decidable.
From TestingTheory Require Import ActTau gLts SyncActions UnionAction UnionSync
  Bisimulation Lts_OBA.

Class gLtsObaFWSync (P Aproc Atest : Type)
  `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest} `{FS : !FwSync Aproc Atest}
  `{gLtsEqP : !gLtsEq P ExtAction_fw} `{gLtsObaP : !gLtsOba P} :=
  MkgLtsObaFWSync {
      fw_boomerang p1 (η : Atest) (μ : Aproc) :
        non_blocking η → fsync μ η →
        ∃ p2, p1 ⟶[inl μ] p2 ∧ p2 ⟶[inr η] p1;
      fw_feedback {p1 p2 p3} (η : Atest) (μ : Aproc) :
        non_blocking η → fsync μ η →
        p1 ⟶[inr η] p2 → p2 ⟶[inl μ] p3 → p1 ⟶⋍ p3 ∨ p1 ⋍ p3;
      fw_inr_output p (η : Atest) p' : p ⟶[inr η] p' → non_blocking η;
    }.

Section FwSyncFacts.

Context {P Aproc Atest : Type}.
Context `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest} `{FS : !FwSync Aproc Atest}.
Context `{gLtsEqP : !gLtsEq P ExtAction_fw} `{gLtsObaP : !gLtsOba P}.
Context `{!gLtsObaFWSync P Aproc Atest}.

(** A forwarder never does an [Atest] reception, so what it does that
    synchronises with an emission of the observer is a process action. *)
Lemma fw_sync_inl (η : Atest) (β : Aproc + Atest) p p' :
  non_blocking η → sync β η → p ⟶[β] p' → ∃ μ, β = inl μ ∧ fsync μ η.
Proof.
  intros nb hsy l. destruct β as [μ | η'].
  - by exists μ.
  - exfalso. eapply (dual_blocks η' η nb); [exact hsy |].
    by eapply fw_inr_output.
Qed.

(** [fw_boomerang], with the reception given by [fsync_total]. *)
Lemma fw_boomerang_total p1 (η : Atest) : non_blocking η →
  ∃ μ p2, sync (inl μ : Aproc + Atest) η ∧ p1 ⟶[inl μ] p2 ∧ p2 ⟶[inr η] p1.
Proof.
  intros nb. destruct (fsync_total η nb) as (μ & hμ).
  destruct (fw_boomerang p1 η μ nb hμ) as (p2 & l1 & l2).
  by exists μ, p2.
Qed.

(** [fw_feedback], for any action that synchronises with [η]. *)
Lemma sync_fwd_feedback {p1 p2 p3} (η : Atest) (β : Aproc + Atest) :
  non_blocking η → sync β η →
  p1 ⟶[inr η] p2 → p2 ⟶[β] p3 → p1 ⟶⋍ p3 ∨ p1 ⋍ p3.
Proof.
  intros nb hsy l1 l2.
  destruct (fw_sync_inl η β p2 p3 nb hsy l2) as (μ & -> & hμ).
  by eapply fw_feedback.
Qed.

End FwSyncFacts.
