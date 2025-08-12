(*
   Copyright (c) 2024 Nomadic Labs
   Copyright (c) 2024 Paul Laforgue <paul.laforgue@nomadic-labs.com>
   Copyright (c) 2024 Léo Stefanesco <leo.stefanesco@mpi-sws.org>
   Copyright (c) 2025 Gaëtan Lopez <glopez@irif.fr>

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

From Coq.Unicode Require Import Utf8.
From stdpp Require Import base countable.
From Must Require Import gLts Bisimulation Lts_OBA.


(******************************************** Termination ***************************************************)

(* Inductive definition of terminate. *)

Reserved Notation "p ⤓" (at level 1).

Inductive terminate `{gLts P A} (p : P) : Prop :=
| tstep : (∀ q, p ⟶ q -> q ⤓) -> p ⤓

where "p ⤓" := (terminate p).

Global Hint Constructors terminate:mdb.

(* Intensionnal definition of termination *)
Inductive terminate_i`{gLts P A} (p : P) : Prop :=
| t_refuses' : p ↛ -> terminate_i p
| tstep' : (exists p', p ⟶ p') -> (∀ q, p ⟶ q -> terminate_i q) -> terminate_i p.


(* Intensionnal definition of termination and extensionnal definition is the same *)


Lemma terminate_i_to_terminate `{gLtsP : gLts P A} (p : P) : terminate_i p -> p ⤓.
Proof.
  intro Hyp. induction Hyp as [| p witness spec Ind].
  + constructor. intros q l. exfalso. eapply lts_refuses_spec2; eauto.
  + eapply tstep; eauto.
Qed.

Lemma terminate_to_terminate_i `{gLtsP : gLts P A} (p : P) : p ⤓ -> terminate_i p .
Proof.
  intro Hyp. induction Hyp as [p Hyp1 Hyp2].
  destruct (decide (p ↛)) as [refuses | not_refuses].
  + eapply t_refuses'. assumption.
  + eapply tstep'. eapply lts_refuses_spec1 in not_refuses. 
    destruct not_refuses as (p' & tr).
    ++ exists p'; eauto.
    ++ intro p'. intro tr. eapply Hyp2. assumption.
Qed.

Lemma terminate_i_equal_terminate' `{gLtsP : gLts P A} (p : P) : p ⤓ <-> terminate_i p .
Proof.
  split ; [eapply terminate_to_terminate_i | eapply terminate_i_to_terminate].
Qed.


(*************************************** Properties on termination **************************************)

(* On LTS *)

Lemma terminate_if_refuses `{gLts P A} p : p ↛ -> p ⤓.
Proof. intro st. constructor. intros q l. exfalso. eapply lts_refuses_spec2; eauto. Qed.

Lemma terminate_preserved_by_lts_tau `{gLts P A} p q : p ⤓ -> p ⟶ q -> q ⤓.
Proof. by inversion 1; eauto. Qed.

(* On LTS with a bisimulation *)

Lemma terminate_preserved_by_eq `{gLtsEq P A} {p q} : p ⤓ -> p ⋍ q -> q ⤓.
Proof.
  intros ht. revert q.
  induction ht. intros.
  eapply tstep.
  intros q' l.
  edestruct eq_spec as (r & h2 & h3). eauto.
  eapply H3; eauto.
Qed.

Lemma terminate_preserved_by_eq2 `{gLtsEq P A} {p q} : p ⋍ q -> p ⤓ -> q ⤓.
Proof. intros. eapply terminate_preserved_by_eq; eauto. Qed.

(* On LTS with OBA axioms *)

Lemma terminate_preserved_by_lts_non_blocking_action `{gLtsOba P A} {p q η} : 
    non_blocking η  -> p ⟶[ η ] q -> p ⤓ -> q ⤓.
Proof.
  intros nb l ht. revert q η nb l.
  induction ht as [p Hyp1 Hyp2].
  intros q a nb l1.
  eapply tstep. intros q' l2.
  destruct (lts_oba_non_blocking_action_delay nb l1 l2) as (t & l3 & l4); eauto.
  destruct l4 as (q0 & l0 & eq0).
  eapply terminate_preserved_by_eq.
  eapply Hyp2. eapply l3. eapply nb. eapply l0. eassumption.
Qed.
