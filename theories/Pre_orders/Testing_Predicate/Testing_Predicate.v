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
From Coq.Program Require Import Equality.
From stdpp Require Import finite gmap decidable.
From Must Require Import ActTau gLts Bisimulation Lts_OBA Subset_Act WeakTransitions CodePurification
    StateTransitionSystems InteractionBetweenLts Convergence Termination FiniteImageLTS.

Class Testing_Predicate (P A : Type) (attaboy : P -> Prop) `{gLts P A, !gLtsEq P A} := {
    attaboy_decidable e : Decision (attaboy e);
    attaboy_preserved_by_eq (p : P) q : attaboy p -> p ⋍ q -> attaboy q;
    attaboy_preserved_by_lts_non_blocking_action p q η : non_blocking η -> p ⟶[η] q -> attaboy p -> attaboy q;
    attaboy_preserved_by_lts_non_blocking_action_converse p q η : non_blocking η -> p ⟶[η] q -> attaboy q -> attaboy p;
}.

#[global] Instance attaboy_dec `{Testing_Predicate P A attaboy} e : Decision (attaboy e).
Proof. eapply attaboy_decidable. Defined.

Lemma unattaboy_preserved_by_lts_non_blocking_action `{gLtsOba P A, !Testing_Predicate P A attaboy} p q η :
  non_blocking η -> p ⟶[η] q -> ~ attaboy p -> ~ attaboy q.
Proof.
  intros nb l1 hp hq.
  eapply hp. eapply attaboy_preserved_by_lts_non_blocking_action_converse; eauto with mdb.
Qed.

Lemma unattaboy_preserved_by_lts_non_blocking_action_converse `{gLtsOba P A, !Testing_Predicate P A attaboy} p q η :
  non_blocking η -> p ⟶[η] q -> ~ attaboy q -> ~ attaboy p.
Proof.
  intros nb l1 hp hq.
  eapply hp. eapply attaboy_preserved_by_lts_non_blocking_action; eauto with mdb.
Qed.

Lemma unattaboy_preserved_by_wt_non_blocking_action 
  `{gLtsOba P A, !Testing_Predicate P A attaboy} 
  r1 r2 s :
  Forall non_blocking s -> r1 ↛ -> ~ attaboy r1 -> r1 ⟹[s] r2 -> ~ attaboy r2.
Proof.
  intros s_spec hst hng hw.
  induction hw; eauto.
  - eapply lts_refuses_spec2 in hst. now exfalso. eauto.
  - inversion s_spec; subst.
    inversion s_spec; subst.
    eapply IHhw. eassumption.
    eapply refuses_tau_preserved_by_lts_non_blocking_action; eauto.
    eapply unattaboy_preserved_by_lts_non_blocking_action; eauto.
Qed.

Lemma unattaboy_preserved_by_eq `{gLtsOba P A, !Testing_Predicate P A attaboy} p q :
  ~ attaboy p -> q ⋍ p -> ~ attaboy q.
Proof.
  intros not_happy eq. intro happy.
  eapply attaboy_preserved_by_eq in happy; eauto with mdb.
Qed.

Lemma woutpout_preserves_attaboy `{gLtsOba P A, !Testing_Predicate P A attaboy} e m e':
  attaboy e -> e ⟿{m} e'
    -> attaboy e'.
Proof.
  intros happy stripped.
  induction stripped.
  + eapply attaboy_preserved_by_eq; eauto.
  + eapply IHstripped. eapply attaboy_preserved_by_lts_non_blocking_action; eauto.
Qed.

Lemma woutpout_preserves_attaboy_converse `{gLtsOba P A, !Testing_Predicate P A attaboy} e m e':
  attaboy e' -> e ⟿{m} e'
    -> attaboy e.
Proof.
  intros happy stripped. induction stripped.
  + symmetry in eq. eapply attaboy_preserved_by_eq; eauto.
  + eapply attaboy_preserved_by_lts_non_blocking_action_converse. eassumption. eassumption.
    now eapply IHstripped.
Qed.

