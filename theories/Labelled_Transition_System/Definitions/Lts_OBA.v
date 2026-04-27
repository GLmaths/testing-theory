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
From TestingTheory Require Import ForAllHelper MultisetHelper gLts Bisimulation.

(** ** Lts that respects the axioms NB-DELAY , NB-CONFLUENCE, NB-TAU, NB-DETERMINACY and BACKWARDS-NB-DETERMINACY *)

Class gLtsOba P {A} `{H : ExtAction A} {Rel : gLtsEq P H} :=
  MkOba {
      (* Selinger axioms. *)
      lts_oba_non_blocking_action_delay {p q r η α} :
      non_blocking η → p ⟶[ η ] q → q ⟶{ α } r 
        → (∃ t, p ⟶{α} t /\ t ⟶⋍[ η ] r) ;
      lts_oba_non_blocking_action_confluence {p q1 q2 η μ} :
      non_blocking η → μ ≠ η → p ⟶[ η ] q1 → p ⟶[ μ ] q2 
        → ∃ r, q1 ⟶[ μ ] r /\ q2 ⟶⋍[ η ] r ; 
      lts_oba_non_blocking_action_tau {p q1 q2 η} :
      non_blocking η → p ⟶[ η ] q1 → p ⟶ q2 
        → (∃ t, q1 ⟶ t /\ q2 ⟶⋍[ η ] t) \/ (∃ β, (dual β η) /\ q1 ⟶⋍[ β ] q2) ; 
      lts_oba_non_blocking_action_deter {p1 p2 p3 η} :
      non_blocking η → p1 ⟶[ η ] p2 → p1 ⟶[ η ] p3 
        → p2 ⋍ p3 ;
      (* Extra axiom, it would be nice to remove it, not used that much. *)
      lts_oba_non_blocking_action_deter_inv {p1 p2 q1 q2} η :
      non_blocking η → p1 ⟶[ η ] q1 → p2 ⟶[ η ] q2 → q1 ⋍ q2 
        → p1 ⋍ p2
    }.

(** *** Relationship between `co_nba`, `non_blocking` and `dual` *)

Definition exist_co_nba `{ExtAction A} (β : A) := 
    exists (η : A), (non_blocking η /\ dual β η).

Lemma co_nb_to_nb `{ExtAction A} l : Forall non_blocking (coₜ l) -> Forall exist_co_nba l.
Proof.
  intros.
  induction l.
  + constructor.
  + constructor. simpl in *. inversion H0; subst.
    exists (co a). split; eauto. exact (proj2_sig (exists_dual a)).
    simpl in *. inversion H0; subst. eapply IHl. eauto.
Qed.

Lemma EquivDef_inv1 `{ExtAction A} (s1 : list A) :
  Forall exist_co_nba s1 
    → (exists s3, Forall non_blocking s3 /\ Forall2 dual s1 s3).
Proof.
  induction s1 as [| ɣ l HypInd].
  - exists []. split. eauto. eapply Forall2_nil.
  - intro his. inversion his as [|? ? (η & nb & duo) Hyp2] ; subst.
    apply HypInd in Hyp2 as (s3 & all_nb & all_dual).
    exists (η :: s3). split.
    + apply Forall_cons; auto.
    + apply Forall2_cons ; auto.
Qed.

Lemma EquivDef_inv2 `{ExtAction A} (s1 : list A) :
  (exists s3, Forall non_blocking s3 /\ Forall2 dual s1 s3)
    → Forall exist_co_nba s1.
Proof.
  induction s1; intro Hyp.
  - apply Forall_nil.
  - destruct Hyp as (s3 & all_nb & all_duo). induction s3 as [|η s3 ].
    + inversion all_duo.
    + inversion all_nb; subst. inversion all_duo; subst. 
      apply Forall_cons. 
      * exists η. split; auto.
      * apply IHs1. exists s3. split; auto.
Qed.

Lemma EquivDef `{ExtAction A} (s1 : list A) : 
  (exists s3, Forall non_blocking s3 /\ Forall2 dual s1 s3) ↔ Forall exist_co_nba s1.
Proof.
  split. 
  * apply EquivDef_inv2.
  * apply EquivDef_inv1.
Qed.

(** *** Properties on gLtsOBA *)

Lemma refuses_tau_preserved_by_lts_non_blocking_action `{gLtsOba P A} p q η : 
  non_blocking η → p ↛ → p ⟶[ η ] q → q ↛.
Proof.
  intros nb st l.
  destruct (decide (q ↛)) as [ refuses | accepts ]. 
  + exact refuses. 
  + eapply lts_refuses_spec1 in accepts as (t & l').
    destruct (lts_oba_non_blocking_action_delay nb l l') as (r & l1 & l2).
    assert (¬ p ↛).
    { eapply lts_refuses_spec2; eauto. } 
    contradiction.
Qed.

Lemma lts_different_action_preserved_by_lts_non_blocking_action `{gLtsOba P A} p q η μ :
  non_blocking η → μ ≠ η →
  (exists t, p ⟶[μ] t) → p ⟶[η] q → (exists t, q ⟶[μ] t).
Proof.
  intros nb neq (t & hl1) hl2.
  edestruct (lts_oba_non_blocking_action_confluence nb neq hl2 hl1) as (r & l1 & l2). eauto.
Qed.

Lemma refuses_action_preserved_by_lts_non_blocking_action `{gLtsOba P A} p q η μ :
  non_blocking η →
  p ↛[μ] → p ⟶[η] q → q ↛[μ] .
Proof.
  intros nb st l.
  destruct (decide (q ↛[μ])) as [ refuses | accepts ].
  + exact refuses. 
  + eapply lts_refuses_spec1 in accepts as (t & l').
    destruct (lts_oba_non_blocking_action_delay nb l l') as (r & l1 & l2).
    assert (¬ p ↛[μ]).
    { eapply lts_refuses_spec2; eauto. } 
    contradiction.
Qed.