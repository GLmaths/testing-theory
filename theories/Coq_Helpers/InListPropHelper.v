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
From Coq.Logic Require Import ProofIrrelevance. 
From stdpp Require Import list finite gmap gmultiset.

Lemma sig_eq {A} (P : A → Prop) (x y : sig P) :
  proj1_sig x = proj1_sig y → x = y.
Proof.
  destruct x as [x Px]; simpl.
  destruct y as [y Py]; simpl.
  intros ->.
  rewrite (proof_irrelevance _ Px Py); trivial.
Qed.

Section in_list_finite.
  Context `{!EqDecision A}.
  Context {P : A → Prop} `{!∀ x : A, ProofIrrel (P x)} `{∀ x, Decision (P x)}.

  Program Fixpoint Forall_to_sig (l : list A) : Forall P l → list (sig P) :=
    match l as u return Forall P u → list (sig P) with
    | [] => λ _, []
    | a :: l' => λ Hal, (exist P a _) :: Forall_to_sig l' _
    end.
  Next Obligation. intros ??? Hal. inversion Hal. by simplify_eq. Qed.
  Next Obligation. intros ??? Hal. by inversion Hal; simplify_eq. Qed.

  Lemma elem_of_Forall_to_sig_1 l HPl x : x ∈ Forall_to_sig l HPl → `x ∈ l.
  Proof.
    revert HPl; induction l as [|a l IHl]; simpl; intros HPl Hx.
    - by apply elem_of_nil in Hx.
    - apply elem_of_cons; apply elem_of_cons in Hx as [->|]; simpl in *; eauto.
  Qed.


  Lemma elem_of_Forall_to_sig_2 l HPl x :
    x ∈ l → ∃ Hx, x ↾ Hx ∈ Forall_to_sig l HPl.
  Proof.
    revert HPl; induction l as [|a l IHl]; simpl; intros HPl Hx.
    - by apply elem_of_nil in Hx.
    - inversion HPl as [|? ? Ha HPl']; simplify_eq.
      apply elem_of_cons in Hx as [->|]; simpl in *.
      + exists Ha; apply elem_of_cons; left; apply sig_eq; done.
      + edestruct IHl as [Hx Hxl]; first done.
        exists Hx; apply elem_of_cons; eauto.
  Qed.

  Lemma Forall_to_sig_NoDup (l : list A) HPl : NoDup l → NoDup (Forall_to_sig l HPl).
  Proof.
    revert HPl; induction l as [|a l IHl]; simpl;
      intros HPl; first by constructor.
    inversion 1; inversion HPl; simplify_eq.
    constructor; last by apply IHl.
    intros ?%elem_of_Forall_to_sig_1; done.
  Qed.

  Lemma in_list_finite (l : list A) : (∀ x, P x → x ∈ l) → Finite {x : A | P x}.
  Proof.
    intros Hl.
    assert (Forall P (filter P (remove_dups l))) as Hels.
    { apply Forall_forall. intros ?. rewrite<- elem_of_list_In. rewrite elem_of_list_filter ; tauto. }
    refine {| enum := Forall_to_sig (filter P (remove_dups (l : list A))) Hels |}.
    - eapply Forall_to_sig_NoDup. eapply list_relations.NoDup_filter.
      eapply NoDup_remove_dups.
    - intros x.
      edestruct (elem_of_Forall_to_sig_2 _ Hels) as [Hx' ?].
      { apply elem_of_list_filter; split; first apply (proj2_sig x).
        apply elem_of_remove_dups, Hl; apply (proj2_sig x). }
      replace x with (`x ↾ Hx'); last by apply sig_eq.
      done.
  Qed.

End in_list_finite.