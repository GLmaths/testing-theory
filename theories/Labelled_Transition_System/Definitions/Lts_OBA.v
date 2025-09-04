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
From stdpp Require Import gmap gmultiset.
From Must Require Import ForAllHelper MultisetHelper gLts Bisimulation.

Class gLtsOba (P A : Type) `{H : ExtAction A}
            {LtsP : @gLts P A H} {Rel : @gLtsEq P A H LtsP} :=
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

      (* Selinger axioms. *)
      lts_oba_non_blocking_action_delay {p q r η α} :
      non_blocking η → p ⟶[ η ] q → q ⟶{ α } r 
        → (∃ t, p ⟶{α} t /\ t ⟶⋍[ η ] r) ;
      lts_oba_non_blocking_action_confluence {p q1 q2 η μ} :
      non_blocking η → μ ≠ η → p ⟶[ η ] q1 → p ⟶[ μ ] q2 
        → ∃ r, q1 ⟶[ μ ] r /\ q2 ⟶⋍[ η ] r ; 
      lts_oba_non_blocking_action_tau {p q1 q2 η} :
      non_blocking η → p ⟶[ η ] q1 → p ⟶ q2 
        → (∃ t, q1 ⟶ t /\ q2 ⟶⋍[ η ] t) \/ (∃ μ, (dual η μ) /\ q1 ⟶⋍[ μ ] q2) ; 
      lts_oba_non_blocking_action_deter {p1 p2 p3 η} :
      non_blocking η → p1 ⟶[ η ] p2 → p1 ⟶[ η ] p3 
        → p2 ⋍ p3 ;
      (* Extra axiom, it would be nice to remove it, not used that much. *)
      lts_oba_non_blocking_action_deter_inv {p1 p2 q1 q2} η :
      non_blocking η → p1 ⟶[ η ] q1 → p2 ⟶[ η ] q2 → q1 ⋍ q2 
        → p1 ⋍ p2
    }.


(* Signification between mailbox and non_blocking *)

Lemma lts_oba_mo_non_blocking_spec1 `{gLtsOba P A} {p η} : 
  η ∈ lts_oba_mo p → non_blocking η.
Proof.
  intro mem. apply lts_oba_mo_spec_bis2 in mem as (p2 & nb & tr). exact nb.
Qed.

Lemma lts_oba_mo_non_blocking_contra `{gLtsOba P A} {p ɣ} : 
  blocking ɣ → ɣ ∉ lts_oba_mo p.
Proof.
  intros not_nb mem. apply lts_oba_mo_non_blocking_spec1 in mem. contradiction.
Qed.

Lemma BlockingAction_are_not_non_blocking `{gLtsOba P A} {η ɣ} : 
  non_blocking η → blocking ɣ → ɣ ≠ η.
Proof.
  intros nb1 nb2 eq. rewrite eq in nb2. contradiction.
Qed.

Lemma not_in_mb_to_not_eq' `{gLtsOba P A} {μ p}: 
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

(* Relation between co_nba, non_blocking and dual *)

Definition exist_co_nba (* {A : Type} `{ExtAct A}  *)
      `{ExtAction A} (ɣ : A) := exists (η : A), (non_blocking η /\ dual η ɣ).

Lemma EquivDef_inv1 `{ExtAction A} (s1 : list A) :
  Forall exist_co_nba s1 
    → (exists s3, Forall non_blocking s3 /\ Forall2 dual s3 s1).
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
  (exists s3, Forall non_blocking s3 /\ Forall2 dual s3 s1)
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
  (exists s3, Forall non_blocking s3 /\ Forall2 dual s3 s1) ↔ Forall exist_co_nba s1.
Proof.
  split. 
  * apply EquivDef_inv2.
  * apply EquivDef_inv1.
Qed.


(* Properties on LTS with OBA axioms *)

Lemma lts_oba_mo_eq `{gLtsOba P A} {p q} :
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