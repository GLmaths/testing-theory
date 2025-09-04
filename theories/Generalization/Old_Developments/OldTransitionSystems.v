(*
   Copyright (c) 2024 Nomadic Labs
   Copyright (c) 2024 Paul Laforgue <paul.laforgue@nomadic-labs.com>
   Copyright (c) 2024 Léo Stefanesco <leo.stefanesco@mpi-sws.org>

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
From stdpp Require Import countable gmap finite decidable gmultiset.
From Must Require Import InputOutputActions ActTau.

Class Label (L: Type) :=
  MkLabel {
      label_eqdec: EqDecision L;
      label_countable: Countable L;
    }.
#[global] Existing Instance label_eqdec.
#[global] Existing Instance label_countable.

Class Lts (A L : Type) `{Label L} :=
  MkLts {
      lts_step: A → ActIO L → A → Prop;
      lts_state_eqdec: EqDecision A;

      lts_step_decidable a α b : Decision (lts_step a α b);

      lts_outputs : A -> gset L;
      lts_outputs_spec1 p1 (x : L) p2 : lts_step p1 (ActExt (ActOut x)) p2 -> x ∈ lts_outputs p1;
      lts_outputs_spec2 p1 x : x ∈ lts_outputs p1 -> {p2 | lts_step p1 (ActExt (ActOut x)) p2};

      lts_stable: A → ActIO L → Prop;
      lts_stable_decidable p α : Decision (lts_stable p α);
      lts_stable_spec1 p α : ¬ lts_stable p α → { q | lts_step p α q };
      lts_stable_spec2 p α : { q | lts_step p α q } → ¬ lts_stable p α;
    }.
#[global] Existing Instance lts_state_eqdec.
#[global] Existing Instance lts_step_decidable.
#[global] Existing Instance lts_stable_decidable.

Notation "p ⇾ q"      := (lts_step p τ q) (at level 30, format "p  ⇾  q").
Notation "p ⇾{ α } q" := (lts_step p α q) (at level 30, format "p  ⇾{ α }  q").
Notation "p ⇾[ μ ] q" := (lts_step p (ActExt μ) q) (at level 30, format "p  ⇾[ μ ]  q").

Notation "p ⥇"      := (lts_stable p τ) (at level 30, format "p  ⥇").
Notation "p ⥇{ α }" := (lts_stable p α) (at level 30, format "p  ⥇{ α }").
Notation "p ⥇[ μ ]" := (lts_stable p (ActExt μ)) (at level 30, format "p  ⥇[ μ ]").

Class FiniteLts A L `{Lts A L} :=
  MkFlts {
      folts_states_countable: Countable A;
      folts_next_states_finite p α : Finite (dsig (fun q => lts_step p α q));
}.

#[global] Existing Instance folts_states_countable.
#[global] Existing Instance folts_next_states_finite.

Class LtsEq (A L : Type) `{Lts A L} := {
    (* todo: use Equivalence *)
    eq_rel : A -> A -> Prop;
    eq_rel_refl p : eq_rel p p;
    eq_symm p q : eq_rel p q -> eq_rel q p;
    eq_trans p q r : eq_rel p q -> eq_rel q r -> eq_rel p r;
    (* reference: L 1.4.15 p.51 Sangiorgi pi-book *)
    eq_spec p q (α : ActIO L) : (exists r, eq_rel p r /\ r ⇾{α} q) -> (exists r, p ⇾{α} r /\ eq_rel r q);
  }.

Add Parametric Relation `{Lts A L, ! LtsEq A L} : A eq_rel
    reflexivity proved by (eq_rel_refl)
    symmetry proved by (eq_symm)
    transitivity proved by (eq_trans)
    as sc_proc_rel.

Infix "≈" := eq_rel (at level 70).

Definition lts_sc `{Lts A L, !LtsEq A L} p α q := exists r, p ⇾{α} r /\ r ≈ q.

Notation "p ⇾≈ q" := (lts_sc p τ q) (at level 30, format "p  ⇾≈  q").
Notation "p ⇾≈{ α } q" := (lts_sc p α q) (at level 30, format "p  ⇾≈{ α }  q").
Notation "p ⇾≈[ μ ] q" := (lts_sc p (ActExt μ) q) (at level 30, format "p  ⇾≈[ μ ]  q").

Class LtsOba (A L : Type) `{Lts A L, !LtsEq A L} :=
  MkOBA {
      (* Multiset of outputs *)
      lts_oba_mo p : gmultiset L;
      lts_oba_mo_spec1 p a : a ∈ lts_oba_mo p <-> a ∈ lts_outputs p;
      lts_oba_mo_spec2 p a : forall q, p ⇾[ActOut a] q -> lts_oba_mo p = {[+ a +]} ⊎ lts_oba_mo q;
      (* Selinger axioms. *)
      lts_oba_output_commutativity {p q r a α} :
      p ⇾[ActOut a] q -> q ⇾{α} r -> (∃ t, p ⇾{α} t /\ t ⇾≈[ActOut a] r) ;
      lts_oba_output_confluence {p q1 q2 a μ} :
      μ ≠ ActOut a -> p ⇾[ActOut a] q1 -> p ⇾[μ] q2 ->
      ∃ r, q1 ⇾[μ] r /\ q2 ⇾≈[ActOut a] r ;
      lts_oba_output_tau {p q1 q2 a} :
      p ⇾[ActOut a] q1 -> p ⇾ q2 -> (∃ t, q1 ⇾ t /\ q2 ⇾≈[ActOut a] t) \/ q1 ⇾≈[ActIn a] q2 ;
      lts_oba_output_deter {p1 p2 p3 a} :
      p1 ⇾[ActOut a] p2 -> p1 ⇾[ActOut a] p3 -> p2 ≈ p3 ;
      (* Extra axiom, it would be nice to remove it, not used that much. *)
      lts_oba_output_deter_inv {p1 p2 q1 q2} a :
      p1 ⇾[ActOut a] q1 -> p2 ⇾[ActOut a] q2 -> q1 ≈ q2 -> p1 ≈ p2
    }.

Class LtsObaFB (A L: Type) `{LtsOba A L} :=
  MkLtsObaFB {
      lts_oba_fb_feedback {p1 p2 p3 a} : p1 ⇾[ActOut a] p2 -> p2 ⇾[ActIn a] p3 -> p1 ⇾≈ p3
    }.

Class LtsObaFW (A L : Type) `{LtsOba A L} :=
  MkLtsObaFW {
      lts_oba_fw_forward p1 a : ∃ p2, p1 ⇾[ActIn a] p2 /\ p2 ⇾[ActOut a] p1 ;
      lts_oba_fw_feedback {p1 p2 p3 a} : p1 ⇾[ActOut a] p2 -> p2 ⇾[ActIn a] p3 -> p1 ⇾≈ p3 \/ p1 ≈ p3 ;
    }.