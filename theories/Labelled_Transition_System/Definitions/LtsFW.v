(* begin hide *)
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
(* end hide *)
(* begin hide *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base tactics decidable.
From TestingTheory Require Import ActTau gLts SyncActions Bisimulation Lts_OBA Lts_FW
  WeakTransitions Termination.

Class LtsFW (P A : Type) `{H : ExtAction A} `{gLtsEqP : !gLtsEq P H} :=
  MkLtsFW {
      lfw_boomerang (p : P) (η : A) :
        non_blocking η → ∃ p', p ⟶[co η] p' ∧ p' ⟶[η] p;
      lfw_feedback (p1 p2 p3 : P) (η μ : A) :
        non_blocking η → dual μ η →
        p1 ⟶[η] p2 → p2 ⟶[μ] p3 → p1 ⟶⋍ p3 ∨ p1 ⋍ p3;
      lfw_delay (p q r : P) (η : A) 𝜆 :
        non_blocking η → p ⟶[η] q → q ⟶{𝜆} r →
        ∃ t, p ⟶{𝜆} t ∧ t ⟶⋍[η] r;
    }.

Arguments LtsFW P A {H gLtsEqP}.

#[global] Instance LtsFW_of_gLtsObaFW `{@gLtsObaFW P A H gLtsEqP gLtsObaP} : LtsFW P A.
Proof.
  constructor.
  - intros p η nb. destruct (boomerang p η (co η)) as (p' & hb).
    destruct (hb nb) as (l1 & l2); [symmetry; exact (proj2_sig (exists_dual η)) |].
    by exists p'.
  - intros p1 p2 p3 η μ nb duo l1 l2. by eapply fwd_feedback.
  - intros p q r η 𝜆 nb l1 l2. by eapply nb_delay.
Qed.

Section LtsFW_facts.

Context `{H : ExtAction A} `{gLtsEqP : !gLtsEq P H} `{FW : !LtsFW P A}.

Lemma co_dual (η : A) : dual (co η) η.
Proof. symmetry. exact (proj2_sig (exists_dual η)). Qed.

Lemma lfw_delay_wt_nil {p q r : P} (η : A) :
  non_blocking η → p ⟶⋍[η] q → q ⟹ r →
  ∃ t, p ⟹ t ∧ t ⟶⋍[η] r.
Proof.
  intros nb l w.
  remember ([] : trace A) as s0 eqn:Hs.
  revert p nb l Hs.
  induction w as [ x | s1 x y z lt w IH | μ s1 x y z lt w IH ];
    intros p0 nb (p' & hl & heq) Hs.
  - exists p0. split; [eapply wt_nil |].
    exists p'. split; [exact hl | exact heq].
  - assert (p' ⟶⋍ y) as (r0 & hlr & heqr).
    { eapply eq_spec. exists x. split; [exact heq | exact lt]. }
    destruct (lfw_delay p0 p' r0 η τ nb hl hlr) as (r' & l1 & (t' & l2 & heqt')).
    destruct (IH r' nb
                (ex_intro _ t' (conj l2 (transitivity heqt' heqr))) Hs)
      as (r1 & w1 & sc).
    exists r1. split; [eapply wt_tau; [exact l1 | exact w1] | exact sc].
  - discriminate.
Qed.

Lemma lfw_terminate_preserved {p q : P} (η : A) :
  non_blocking η → p ⟶[η] q → p ⤓ → q ⤓.
Proof.
  intros nb l ht. revert q l.
  induction ht as [p Hyp1 Hyp2].
  intros q l1.
  eapply tstep. intros q' l2.
  destruct (lfw_delay p q q' η τ nb l1 l2) as (t & l3 & (q0 & l0 & eq0)).
  eapply terminate_preserved_by_eq; [| exact eq0].
  by eapply Hyp2.
Qed.

End LtsFW_facts.
(* end hide *)
