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

(** * One alphabet out of two: [Aproc ⊎ Atest]

    A forwarder talking to an observer over another alphabet acts on both: its
    process part on [Aproc], its memory on [Aproc] (what it stores) and on
    [Atest] (what it hands to the observer, under the observer's names).  So
    the natural alphabet of the whole setting is the disjoint union, with a
    duality that extends the two given ones by the synchronisation:

    - [inl μ] and [inl μ'] are dual when [μ] and [μ'] are, in [Aproc];
    - [inr η] and [inr η'] are dual when [η] and [η'] are, in [Atest];
    - [inl μ] and [inr η] are dual when [sync μ η].

    Every [ExtAction] law then holds under *one* condition on [sync], its
    polarity: it pairs an offer with a consumption.  In particular
    [exists_dual] needs nothing from [sync] — each side supplies its own duals
    — so there is no coherence, naming or partner-existence law here.  With
    this alphabet the whole one-alphabet development applies as it stands. *)

From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base countable decidable.
From TestingTheory Require Import ActTau gLts.

Section Union.

Context {Aproc Atest : Type}.
Context `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest}.
Context (sync : Aproc → Atest → Prop) (sync_dec : ∀ μ η, Decision (sync μ η)).
#[local] Existing Instance sync_dec.

(** The only law: a synchronisation pairs an offer with a consumption. *)
Context (sync_polarity : ∀ μ η, sync μ η →
           (non_blocking η → ¬ non_blocking μ) ∧ (non_blocking μ → ¬ non_blocking η)).

Definition union_nb (a : Aproc + Atest) : Prop :=
  match a with inl μ => non_blocking μ | inr η => non_blocking η end.

Definition union_dual (a b : Aproc + Atest) : Prop :=
  match a, b with
  | inl μ, inl μ' => dual μ μ'
  | inr η, inr η' => dual η η'
  | inl μ, inr η  => sync μ η
  | inr η, inl μ  => sync μ η
  end.

#[local] Instance union_nb_dec a : Decision (union_nb a).
Proof. destruct a; simpl; apply _. Defined.

#[local] Instance union_dual_dec a b : Decision (union_dual a b).
Proof. destruct a, b; simpl; apply _. Defined.

Lemma union_dual_sym : Symmetric union_dual.
Proof.
  intros [μ | η] [μ' | η'] h; simpl in *; try done; by symmetry.
Qed.

Lemma union_dual_blocks β η :
  union_nb η → union_dual β η → ¬ union_nb β.
Proof.
  destruct β as [μ | η0], η as [μ' | η']; simpl; intros nb hd.
  - by eapply dual_blocks.
  - (* [inl μ] against the observer's offer [η'] *)
    by apply (proj1 (sync_polarity μ η' hd)).
  - (* the observer's [η0] against the process's offer [μ'] *)
    by apply (proj2 (sync_polarity μ' η0 hd)).
  - by eapply dual_blocks.
Qed.

Definition union_exists_dual (a : Aproc + Atest) : { b | union_dual a b } :=
  match a with
  | inl μ => exist _ (inl (co μ)) (proj2_sig (exists_dual μ))
  | inr η => exist _ (inr (co η)) (proj2_sig (exists_dual η))
  end.

(* Not a global instance: [sync] is an explicit parameter, and an instance of
   [ExtAction (_ + _)] would be tried on every sum type. *)
Definition ExtAction_union : ExtAction (Aproc + Atest) :=
  {| eqdec := _;
     countable := _;
     non_blocking := union_nb;
     non_blocking_dec := union_nb_dec;
     dual := union_dual;
     dual_dec := union_dual_dec;
     dual_blocks := union_dual_blocks;
     duo_sym := union_dual_sym;
     exists_dual := union_exists_dual |}.

End Union.
