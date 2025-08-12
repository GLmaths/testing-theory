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
From stdpp Require Import countable.
From Must Require Import ActTau gLts.

Class gLtsEq (P A : Type) `{gLts P A} := {
    (* Equivalence relation *)
    eq_rel : P → P → Prop;
    eq_rel_eq : Equivalence eq_rel;

    (* The relation is a bissimulation *)
    eq_spec p q (α : Act A) :
    (exists r, eq_rel p r /\ r ⟶{α} q) 
      → (exists r, p ⟶{α} r /\ eq_rel r q);
  }.

#[global] Instance rel_equivalence `{gLtsEq P A }: Equivalence eq_rel.
  by exact eq_rel_eq.
Defined.

Infix "⋍" := eq_rel (at level 70).

Definition lts_sc `{gLts P A, !gLtsEq P A} p α q := exists r, p ⟶{α} r /\ r ⋍ q.

Notation "p ⟶⋍ q" := (lts_sc p τ q) (at level 30, format "p  ⟶⋍  q").
Notation "p ⟶⋍{ α } q" := (lts_sc p α q) (at level 30, format "p  ⟶⋍{ α }  q").
Notation "p ⟶⋍[ μ ] q" := (lts_sc p (ActExt μ) q) (at level 30, format "p  ⟶⋍[ μ ]  q").


(* Bisimulation properties *)

Lemma mk_lts_eq `{gLtsEq P A} {p α q} : p ⟶{α} q  → p ⟶⋍{α} q.
Proof. intro. exists q; split. eauto. reflexivity. Qed.

Lemma refuses_preserved_by_eq `{gLtsEq P A} {p q μ} : p ↛[ μ ] -> p ⋍ q -> q ↛[ μ ].
Proof.
  intros stable_p eq. destruct (decide (q ↛[μ])) as [ tauto | imp].
  + eauto.
  + eapply lts_refuses_spec1 in imp as (q' & HypTr).
    edestruct (eq_spec p q') as (p' & HypTr' & eq'); eauto.
    assert( ¬ p ↛[μ] ). { eapply lts_refuses_spec2; eauto. }
    contradiction.
Qed.

Lemma accepts_preserved_by_eq `{gLtsEq P A} {p q μ} : ¬ p ↛[ μ ] -> p ⋍ q -> ¬ q ↛[ μ ].
Proof.
  intros stable_p eq. symmetry in eq.
  eapply lts_refuses_spec1 in stable_p as (p' & HypTr').
  edestruct (eq_spec q p') as (q' & HypTr'' & eq'') ; eauto.
  eapply lts_refuses_spec2; eauto.
Qed.

Lemma stable_preserved_by_eq `{gLtsEq P A} p q : p ↛ -> p ⋍ q -> q ↛.
Proof.
  intros heq hst.
  destruct (lts_refuses_decidable q τ). eassumption.
  eapply lts_refuses_spec1 in n as (q' & hl).
  edestruct (eq_spec p q') as (p' & hl' & heq'). eauto.
  exfalso. eapply lts_refuses_spec2; eauto.
Qed.

