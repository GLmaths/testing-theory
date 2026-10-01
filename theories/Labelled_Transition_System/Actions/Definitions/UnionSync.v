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

(** * Forwarders over [Aproc ⊎ Atest] against observers over [Atest]

    A process and an observer are linked by [fsync : Aproc → Atest → Prop],
    which says which process action matches which observer action.  The
    processes of the characterisation are /forwarders/: their memory receives
    what the observer emits and hands it back under the observer's own names.
    So they act on both alphabets, [Aproc ⊎ Atest], while the observers — and
    the co-traces — act on [Atest] only.

    - [ExtAction_fw] is the forwarder's alphabet: the union, with [fsync]
      linking its two halves ([UnionAction.v]);
    - [SyncAction_fw] is how a forwarder meets an observer: the duality of the
      union, seen from [Atest] —
      [inl μ] with [η] when [fsync μ η], and [inr η'] with [η] when
      [dual η' η].

    The laws asked of [fsync]: decidability and polarity, which the union
    alphabet needs, and totality on the observer's emissions, so that the
    forwarder's memory can receive every message as a /process/ action
    [inl μ] ([SyncForwarder.v]). *)

From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base countable decidable.
From TestingTheory Require Import ActTau gLts SyncActions UnionAction.

Class FwSync (Aproc Atest : Type) `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest} :=
  MkFwSync {
      fsync : Aproc → Atest → Prop;
      fsync_dec :: RelDecision fsync;
      fsync_polarity μ η : fsync μ η →
        (non_blocking η → ¬ non_blocking μ) ∧ (non_blocking μ → ¬ non_blocking η);
      (** Every emission of the observer can be received by a process. *)
      fsync_total η : non_blocking η → { μ | fsync μ η };
  }.

Arguments fsync {Aproc Atest}%_type_scope {Hp Ht} {FwSync} _ _.

Section FwSyncFacts.

Context {Aproc Atest : Type}.
Context `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest} `{FS : !FwSync Aproc Atest}.

(** The forwarder's alphabet. *)
#[global] Instance ExtAction_fw : ExtAction (Aproc + Atest) :=
  ExtAction_union fsync fsync_dec fsync_polarity.

(** How a forwarder meets an observer. *)
#[global] Instance SyncAction_fw : SyncAction (Aproc + Atest) Atest :=
  {| sync a η := union_dual fsync a (inr η);
     sync_dec a η := union_dual_dec fsync fsync_dec a (inr η) |}.

(** An emission [η] of the observer is, for the forwarder, the action [inr η]:
    what synchronises with [η] is exactly the duals of [inr η], and [inr η]
    synchronises with every dual of [η]. *)
Lemma inr_spec (η : Atest) : non_blocking η →
    non_blocking (inr η : Aproc + Atest)
  ∧ (∀ a : Aproc + Atest, sync a η ↔ dual a (inr η))
  ∧ (∀ ν, dual ν η → sync (inr η : Aproc + Atest) ν).
Proof.
  intros nb. split_and!.
  - exact nb.
  - intros a. split; intro h; exact h.
  - intros ν hd. simpl. by symmetry.
Qed.

End FwSyncFacts.
