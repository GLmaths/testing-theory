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

(** * Core Erlang: the testing predicate

    Core Erlang has no success operator, so one is added: the inert expression
    [✓ₑ] ([ETick]).  A system reports success when one of its processes /is/
    [✓ₑ] — that is, when the process [⟨p, n, ✓ₑ⟩] is in the pool.  An observer
    is then an ordinary system, and it reports success by reducing one of its
    processes to [✓ₑ], typically in the body of a [receive] clause.

    [✓ₑ] has no transition: success is irreversible, and the observer reporting
    it keeps neither computation nor messages of its own. *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list numbers gmultiset.
From TestingTheory Require Import ActTau InputOutputActions gLts Bisimulation
  Testing_Predicate Erlang_Syntax Erlang_LTS Erlang_Instance.

Section Erlang_Good.

Context `{EP : Erlang_Program}.

Definition is_tick (c : comp) : bool :=
  match c with CProc _ _ ETick => true | _ => false end.

Definition good_Erl (S : sys) : Prop := existsb is_tick (elements S) = true.

Lemma good_Erl_spec S : good_Erl S ↔ ∃ c, c ∈ S ∧ is_tick c = true.
Proof.
  unfold good_Erl. split.
  - intros (c & hin & ht)%existsb_exists. exists c. split; [| done].
    by apply gmultiset_elem_of_elements, list_elem_of_In.
  - intros (c & hin & ht). apply existsb_exists. exists c. split; [| done].
    by apply list_elem_of_In, gmultiset_elem_of_elements.
Qed.

Lemma good_Erl_tick p n S : good_Erl (⟨p, n, ✓ₑ⟩ ⊎ S).
Proof.
  apply good_Erl_spec. exists (CProc p n ETick).
  split; [multiset_solver | done].
Qed.

#[global] Instance good_Erl_dec S : Decision (good_Erl S).
Proof. unfold good_Erl. apply _. Defined.

(** A message in transit is not a success, so releasing one changes nothing. *)
#[global] Instance Erl_Good : Testing_Predicate good_Erl Erl_gLtsEq.
Proof.
  split.
  - apply _.
  - intros S T hg heq. change (S = T) in heq. by subst.
  - intros S T η nb hl hg.
    destruct nb as (a & ->). apply erl_out_shape in hl as (p & v & -> & ->).
    apply good_Erl_spec in hg as (c & hin & ht). apply good_Erl_spec. exists c.
    split; [| done].
    destruct c as [p' n e | p' v']; [multiset_solver | by inversion ht].
  - intros S T η nb hl hg.
    destruct nb as (a & ->). apply erl_out_shape in hl as (p & v & -> & ->).
    apply good_Erl_spec in hg as (c & hin & ht). apply good_Erl_spec. exists c.
    split; [multiset_solver | done].
Defined.

End Erlang_Good.
