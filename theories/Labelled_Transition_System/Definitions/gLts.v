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
From Must Require Import ActTau.


(* Extra Hypothesis on External Actions *)

Class ExtAction (A : Type) :=
  MkExtAction {
      eqdec: EqDecision A;
      countable: Countable A;
      non_blocking : A → Prop;
      non_blocking_dec a : Decision (non_blocking a);
      dual : A → A → Prop;
      dual_dec a b: Decision (dual a b);

      (* Co-action of a non-blocking action is blocking, otherwise infinite non-blocking action sequence in FW *)
      dual_blocks ɣ η :
      non_blocking η → dual ɣ η→ 
        ¬ non_blocking ɣ ;

      (* Without dual, an action isn't observable *)
      exists_dual μ : { η | dual μ η};

      (* Unique non-blocking action *)
      unique_nb η β: non_blocking η → dual β η → η = proj1_sig (exists_dual β);

      (* Handy Hypothesis *)
      (* nb_not_nb η1 η2 ɣ : non_blocking η1 → dual η1 ɣ → dual η2 ɣ → non_blocking η2; *)
      duo_sym : Symmetric dual;
      (* Can we derive these hypothesis ?*)
    }.
#[global] Existing Instance eqdec.
#[global] Existing Instance countable.
#[global] Existing Instance non_blocking_dec.
#[global] Existing Instance dual_dec.
#[global] Existing Instance duo_sym.

Notation "'co' β" := (proj1_sig (exists_dual β)) (at level 30).

Definition blocking `{ExtAction A} (β : A) := ¬ non_blocking β.

Class gLts (P A : Type) `{ExtAction A} :=
  MkgLts {
      lts_step: P → Act A → P → Prop;
      lts_state_eqdec: EqDecision P;

      lts_step_decidable a α b : Decision (lts_step a α b);

      lts_refuses : P → Act A → Prop;
      lts_refuses_decidable p α : Decision (lts_refuses p α);
      lts_refuses_spec1 p α : ¬ lts_refuses p α → { q | lts_step p α q };
      lts_refuses_spec2 p α : { q | lts_step p α q } → ¬ lts_refuses p α;
    }.
#[global] Existing Instance lts_state_eqdec.
#[global] Existing Instance lts_step_decidable.
#[global] Existing Instance lts_refuses_decidable. 

Notation "p ⟶ q"      := (lts_step p τ q) (at level 30, format "p  ⟶  q").
Notation "p ⟶{ α } q" := (lts_step p α q) (at level 30, format "p  ⟶{ α }  q").
Notation "p ⟶[ μ ] q" := (lts_step p (ActExt μ) q) (at level 30, format "p  ⟶[ μ ]  q").

Notation "p ↛"      := (lts_refuses p τ) (at level 30, format "p  ↛").
Notation "p ↛{ α }" := (lts_refuses p α) (at level 30, format "p  ↛{ α }").
Notation "p ↛[ μ ]" := (lts_refuses p (ActExt μ)) (at level 30, format "p  ↛[ μ ]").

Definition lts_exists_duo_decidable : 
forall (A : Type) (H : ExtAction A) μ, Decision (∃ η' : A, non_blocking η' ∧ dual μ η').
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
Qed.

#[global] Instance lts_exists_duo_decidable_inst `{ExtAction A} μ 
  : Decision (∃ η', non_blocking η' /\ dual μ η').
Proof. exact (lts_exists_duo_decidable A H μ). Qed.

