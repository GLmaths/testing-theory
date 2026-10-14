(* begin hide *)
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
(* end hide *)

From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import countable.
From TestingTheory Require Import ActTau.



(* ** LTSs with non-blocking actions [gLts] *)


Class gLts (P : Type) {A : Type} (EA : ExtAction A) :=
  MkgLts {
      lts_step: P → Labels A → P → Prop;
      lts_state_eqdec: EqDecision P;

      lts_step_decidable a α b : Decision (lts_step a α b);

      lts_performs : P → Labels A → Prop;
      lts_performs_decidable p α : Decision (lts_performs p α);
      lts_performs_spec1 p α : lts_performs p α → { q | lts_step p α q };
      lts_performs_spec2 p α : { q | lts_step p α q } → lts_performs p α;
    }.

Arguments gLts P {_} EA.

#[global] Existing Instance lts_state_eqdec.
#[global] Existing Instance lts_step_decidable.
#[global] Existing Instance lts_performs_decidable.

Notation "p ⟶ q"      := (lts_step p τ q) (at level 30, format "p  ⟶  q").
Notation "p ⟶{ α } q" := (lts_step p α q) (at level 30, format "p  ⟶{ α }  q").
Notation "p ⟶[ μ ] q" := (lts_step p (ActExt μ) q) (at level 30, format "p  ⟶[ μ ]  q").

Notation "p ⟶"      := (lts_performs p τ) (at level 30, format "p  ⟶").
Notation "p ⟶{ α }" := (lts_performs p α) (at level 30, format "p  ⟶{ α }").
Notation "p ⟶[ μ ]" := (lts_performs p (ActExt μ)) (at level 30, format "p  ⟶[ μ ]").

Notation "p ↛"      := (¬ lts_performs p τ) (at level 30, format "p  ↛").
Notation "p ↛{ α }" := (¬ lts_performs p α) (at level 30, format "p  ↛{ α }").
Notation "p ↛[ μ ]" := (¬ lts_performs p (ActExt μ)) (at level 30, format "p  ↛[ μ ]").



(* ** Properties on `gLts`*)


Definition lts_exists_duo_decidable : 
forall (A : Type) (H : ExtAction A) {unique_nb : UniqueDual A} μ, Decision (∃ η' : A, non_blocking η' ∧ dual μ η').
Proof.
intros. destruct (decide (non_blocking μ)) as [nb | not_nb].
  + right. intro Hyp. destruct Hyp as (μ' & nb' & duo').
    assert (blocking μ).
    eapply dual_blocks; eauto. contradiction.
  + destruct (decide (non_blocking (co μ))) as [nb' | not_nb'].
    ++ left. exists (co μ) ; eauto.
       split. eauto. exact (proj2_sig (exists_dual μ)).
    ++ right. intro imp. destruct imp as (η'' & nb'' & duo).
       assert (η'' = co μ).
       { eapply unique_nb; eauto. } subst.
       contradiction.
Defined.

#[global] Instance lts_exists_duo_decidable_inst `{ExtAction A} {unique_nb : UniqueDual A} μ 
  : Decision (∃ η', non_blocking η' /\ dual μ η').
Proof. exact (lts_exists_duo_decidable A H μ). Defined.


Lemma dual_is_involutive `{ExtAction A} {unique_nb : UniqueDual A} μ : μ = (co (co μ)).
Proof.
  assert (dual μ (co μ)) as duo.
  { exact (proj2_sig (exists_dual μ)). }
  symmetry in duo.
  eapply unique_nb.
  exact duo.
Qed.

Lemma dual_trace_is_involutive `{ExtAction A} {unique_nb : UniqueDual A} s : s = (coₜ (coₜ s)).
Proof.
  induction s.
  + simpl ; eauto.
  + rewrite map_cons. rewrite map_cons. rewrite<- IHs at 1. f_equal.
    eapply dual_is_involutive.
Qed.

Lemma simpl_co_trace_singleton `{ExtAction A} {unique_nb : UniqueDual A} l η : coₜ l = [η] -> l = [co η].
Proof.
  intro. destruct l.
  + simpl in *. inversion H0.
  + simpl in *. inversion H0; subst. f_equal. rewrite<- dual_is_involutive. eauto.
    eapply map_eq_nil in H3. subst. simpl. eauto.
Qed.

Lemma dual_traces `{ExtAction A} s : Forall2 dual s (coₜ s).
Proof.
  induction s.
  + simpl. eauto.
  + simpl. constructor.
    exact (proj2_sig (exists_dual a)).
    exact IHs.
Qed.


Lemma BlockingAction_are_not_non_blocking `{H : ExtAction A} {η β} : 
  non_blocking η → blocking β → β ≠ η.
Proof.
  intros nb1 nb2 eq. rewrite eq in nb2. contradiction.
Qed.

