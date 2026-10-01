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

(** * Synchronising two alphabets

    A relation [sync : Aproc → Atest → Prop] saying which action of a process
    matches which action of an observer.  This file has the conditions the
    characterisation proofs need of it; the composition of the two LTSs is in
    [InteractionBetweenLts.v]. *)

From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base countable decidable.
From TestingTheory Require Import ActTau gLts.

(** ** The synchronisation itself

    [sync] is a *field*, not a parameter: it is to the pair [(Aproc, Atest)]
    what [dual] is to [A] in [ExtAction].  That is what makes [p ⊆ₘᵤₛₜᵢ q]
    mean something — the must preorder carries the synchronisation, it is not
    recovered by guessing a relation.

    Nothing is asked of it here: the composition of two LTSs and the co-trace
    machinery work for any decidable relation.  The laws that the
    characterisation needs come from the forwarder setting ([UnionSync.v]),
    where the process alphabet is [Aproc ⊎ Atest]. *)

Class SyncAction (Aproc Atest : Type)
  `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest} :=
  MkSyncAction {
      sync : Aproc → Atest → Prop;
      sync_dec :: RelDecision sync;
  }.

Arguments sync {Aproc Atest}%_type_scope {Hp Ht} {SyncAction} _ _.

(* Deliberately *not* a global instance: it would make every search for
   [SyncAction ?A ?A] succeed, and the searches that go through it (a [gLts]
   on [gset P], say) then regress without bound.  The one-alphabet
   development is in the same situation with [coFiniteImagegLts], which has
   no generic instance either.  Pass it where it is meant. *)
Definition SyncAction_of_dual `{H : ExtAction A} : SyncAction A A :=
  {| sync := dual; sync_dec := dual_dec |}.

(* In the one-alphabet development the synchronisation is [dual].  It is
   found automatically, but only for two copies of the same, known alphabet:
   a search for [SyncAction ?A ?A] with [?A] unknown is left alone, which is
   what keeps the regress described above away. *)
#[global] Hint Extern 10 (SyncAction ?A ?A) =>
  lazymatch goal with
  | |- SyncAction ?A ?A => assert_fails (is_evar A); exact SyncAction_of_dual
  end : typeclass_instances.

(* With [sync = dual], [sync] is symmetric, as [dual] is: proofs of the
   one-alphabet development can keep using [symmetry]. *)
#[global] Instance sync_of_dual_sym `{H : ExtAction A} :
  Symmetric (@sync A A H H SyncAction_of_dual) := duo_sym.
