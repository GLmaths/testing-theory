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
From stdpp Require Import countable finite gmultiset.

Inductive Forall2 {A : Type} {B : Type} (P : A → B → Prop) : list A → list B → Prop :=
    Forall2_nil : Forall2 P [] [] 
    | Forall2_cons : ∀ (x : A) (y : B) (la : list A) (lb : list B), P x y → Forall2 P la lb → Forall2 P (x :: la) (y :: lb).

Lemma Forall2_app {A B : Type} P (s1 s3 : list A) (s2 s4 : list B) : 
  Forall2 P s1 s2 -> Forall2 P s3 s4 
    -> Forall2 P (s1 ++ s3) (s2 ++ s4).
Proof.
  dependent induction s1; dependent induction s2; 
  dependent induction s3; dependent induction s4; intros Hyp1 Hyp2 ; simpl in *; 
      eauto; try now inversion Hyp1; try now inversion Hyp2.
  + rewrite app_nil_r. rewrite app_nil_r. eauto.
  + constructor. inversion Hyp1; subst ; auto. apply IHs1.
    ++ inversion Hyp1; subst; auto.
    ++ auto.
Qed.

Definition Eq {A : Type} (s1 : A) (s2 : A) := s1 = s2.
Definition NotEq {A : Type} (s1 : A) (s2 : A) := s1 ≠ s2.

Lemma are_actions_preserved_by_perm {A Pp} (s1 s2 : list A) :
  s1 ≡ₚ s2 -> Forall Pp s1 
    -> Forall Pp s2.
Proof. intros hp hos. eapply Permutation_Forall; eauto. Qed.

Lemma simpl_P_in_l `{EqDecision A} `{Countable A} {P : A -> Prop} (η : A) (m : gmultiset A): 
  Forall P (elements ({[+ η +]} ⊎ m)) <-> P η /\ Forall P (elements m).
Proof.
  split.
  + assert ((elements ({[+ η +]} ⊎ m)) ≡ₚ elements ({[+ η +]} : gmultiset A) ++ (elements m)).
  eapply gmultiset_elements_disj_union.
  intro. assert (Forall P (elements (gmultiset_singleton η) ++ elements m)) as Hyp.
  eapply are_actions_preserved_by_perm; eauto.
  assert (elements (gmultiset_singleton η) = [η]) as eq.
  eapply gmultiset_elements_singleton. rewrite eq in Hyp. simpl in *.
  inversion Hyp. subst. split; eauto.
  + intros (PHyp & FHyp).
    assert (Forall P (η :: elements m)). econstructor; eauto.
    eapply are_actions_preserved_by_perm. symmetry. eapply gmultiset_elements_disj_union.
    assert (elements (gmultiset_singleton η) = [η]) as eq.
    eapply gmultiset_elements_singleton. unfold singletonMS. rewrite eq. simpl in *. eauto.
Qed.
