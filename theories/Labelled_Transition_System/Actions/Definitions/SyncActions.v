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

(** **** Synchronising two alphabets *)

From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base countable decidable.
From TestingTheory Require Import ActTau gLts.

(** ******* The synchronisation itself *)

Class SyncAction (Aproc Atest : Type)
  `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest} :=
  MkSyncAction {
      sync : Aproc → Atest → Prop;
      sync_dec :: RelDecision sync;
  }.

Arguments sync {Aproc Atest}%_type_scope {Hp Ht} {SyncAction} _ _.

Definition SyncAction_of_dual `{H : ExtAction A} : SyncAction A A :=
  {| sync := dual; sync_dec := dual_dec |}.

(** ******* In the one-alphabet development the synchronisation is [dual].  *)
#[global] Hint Extern 10 (SyncAction ?A ?A) =>
  lazymatch goal with
  | |- SyncAction ?A ?A => assert_fails (is_evar A); exact SyncAction_of_dual
  end : typeclass_instances.

(** ******* With [sync = dual], [sync] is symmetric, as [dual] is: proofs of the
   one-alphabet development can keep using [symmetry]. *)
#[global] Instance sync_of_dual_sym `{H : ExtAction A} :
  Symmetric (@sync A A H H SyncAction_of_dual) := duo_sym.