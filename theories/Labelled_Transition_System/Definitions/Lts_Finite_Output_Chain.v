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

From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import gmap gmultiset.
From TestingTheory Require Import ForAllHelper MultisetHelper gLts Bisimulation Lts_OBA.

(** ** Each program has a MailBox, which is finite and counts occurences of Value *)

Class FiniteOutputChain_LtsOba P {A} `{H : ExtAction A} `{gLtsObaP : !@gLtsOba P A H gLtsEqP} :=
  MkOba {
      (* Multiset of non-blocking action from a process *)
      lts_oba_mo (p : P) : gmultiset A;

      (* Axioms on multiset of non-blocking action*)
      lts_oba_mo_spec_bis1 p1 η p2 :
      non_blocking η → p1 ⟶[ η ] p2 
        → η ∈ lts_oba_mo p1; 
      lts_oba_mo_spec_bis2 p1 η : 
      η ∈ lts_oba_mo p1 
        → {p2 | (non_blocking η /\ p1 ⟶[ η ] p2 ) } ; 

      (* Finite mailbox *)
      lts_oba_mo_spec2 p η : 
      forall q, non_blocking η → p ⟶[ η ] q 
        → lts_oba_mo p = {[+ η +]} ⊎ lts_oba_mo q;
    }.


(** *** Relationship between mailbox and non-blocking actions *)

Lemma lts_oba_mo_non_blocking_spec1 `{FiniteOutputChain_LtsOba P A} {p η} : 
  η ∈ lts_oba_mo p → non_blocking η.
Proof.
  intro mem. apply lts_oba_mo_spec_bis2 in mem as (p2 & nb & tr). exact nb.
Qed.

Lemma lts_oba_mo_non_blocking_contra `{FiniteOutputChain_LtsOba P A} {p β} : 
  blocking β → β ∉ lts_oba_mo p.
Proof.
  intros not_nb mem. apply lts_oba_mo_non_blocking_spec1 in mem. contradiction.
Qed.

Lemma not_in_mb_to_not_eq' `{FiniteOutputChain_LtsOba P A} {μ p}: 
  μ ∉ lts_oba_mo p 
  -> Forall (NotEq μ) (elements (lts_oba_mo p)).
Proof.
  induction (lts_oba_mo p) using gmultiset_ind.
  + constructor.
  + intro not_in_mem.
    eapply simpl_P_in_l. split.
    ++ intro. subst. set_solver.
    ++ assert (μ ∉ g). set_solver. now eapply IHg.
Qed.


(** *** Properties on LTS with OBA axioms *)

Lemma lts_oba_mo_eq `{FiniteOutputChain_LtsOba P A} {p q} :
  p ⋍ q → lts_oba_mo p = lts_oba_mo q.
Proof.
  remember (lts_oba_mo p) as hmo.
  revert p q Heqhmo.
  induction hmo using gmultiset_ind; intros p q Heqhmo heq.
  - eapply leibniz_equiv. intros η.
    rewrite multiplicity_empty.
    destruct (non_blocking_dec η).
    destruct (decide (q ↛[η])) as [refuses | accepts ].
    + destruct (decide (η ∈ lts_oba_mo q)).
      ++ eapply lts_oba_mo_spec_bis2 in e as (t & hl).
         eapply lts_refuses_spec2 in refuses. multiset_solver. destruct hl. now exists t.
      ++ destruct (multiplicity η (lts_oba_mo q)) eqn:eq; multiset_solver.
    + eapply lts_refuses_spec1 in accepts as (t & hl).
      assert (p ⟶⋍[η] t) as (u & hlu & hequ).
      { eapply eq_spec. eexists; split; eauto. }
      eapply lts_oba_mo_spec_bis1 in hlu. multiset_solver. assumption.
    + eapply lts_oba_mo_non_blocking_contra in n. instantiate (1 := q) in n. multiset_solver.
  - assert {t | non_blocking x /\ p ⟶[x] t} as (t & nb & hlt).
    { eapply lts_oba_mo_spec_bis2. multiset_solver. }
    assert (q ⟶⋍[x] t) as (u & hlu & hequ).
    { symmetry in heq. eapply eq_spec ; eauto. }
    eapply lts_oba_mo_spec2 in hlu, hlt.
    assert (x ∈ lts_oba_mo q) as mem by multiset_solver.
    eapply gmultiset_disj_union_difference' in mem.
    rewrite hlu.
    assert (hmo = lts_oba_mo t).
    { eapply gmultiset_disj_union_inj_1. etrans; eassumption. }
    eapply gmultiset_eq_pop_l. eapply IHhmo. eassumption. now symmetry. assumption. assumption.
Qed.


