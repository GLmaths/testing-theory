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
From stdpp Require Import list finite gmap gmultiset.

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
      + exists Ha; apply elem_of_cons; left; apply (sig_eq_pi _); done.
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

  Definition in_list_finite (l : list A) : (∀ x, P x → x ∈ l) → Finite {x : A | P x}.
  Proof.
    intros Hl.
    assert (Forall P (filter P (remove_dups l))) as Hels.
    { apply Forall_forall. intros ?. rewrite<- list_elem_of_In. rewrite list_elem_of_filter ; tauto. }
    refine {| enum := Forall_to_sig (filter P (remove_dups (l : list A))) Hels |}.
    - eapply Forall_to_sig_NoDup. eapply list.NoDup_filter.
      eapply NoDup_remove_dups.
    - intros x.
      edestruct (elem_of_Forall_to_sig_2 _ Hels) as [Hx' ?].
      { apply list_elem_of_filter; split; first apply (proj2_sig x).
        apply elem_of_remove_dups, Hl; apply (proj2_sig x). }
      replace x with (`x ↾ Hx'); last by apply (sig_eq_pi _).
      done.
  Defined.

  Definition list_finite (l : list A) : (∀ x, P x ↔ x ∈ l) → Finite {x : A | P x}.
  Proof.
    intros Hl.
    assert (Forall P (remove_dups l)) as Hels.
    { apply Forall_forall. intros x hx. rewrite <- list_elem_of_In in hx.
      apply Hl. eapply elem_of_remove_dups. exact hx. }
    refine {| enum := Forall_to_sig (remove_dups l) Hels |}.
    - apply Forall_to_sig_NoDup, NoDup_remove_dups.
    - intros x.
      edestruct (elem_of_Forall_to_sig_2 _ Hels (`x)) as [Hx' ?].
      { apply elem_of_remove_dups, Hl, (proj2_sig x). }
      replace x with (`x ↾ Hx'); last by apply (sig_eq_pi _).
      done.
  Defined.

End in_list_finite.

Section gset_finite.
  Context `{Countable A}.

  Definition gset_decision (S : gset A) (Q : A → Prop) (HS : ∀ x, x ∈ S ↔ Q x) :
    ∀ x, Decision (Q x) :=
    λ x, match decide (x ∈ S) with
         | left h => left (proj1 (HS x) h)
         | right h => right (λ hq, h (proj2 (HS x) hq))
         end.

  Lemma gset_decision_Forall (S : gset A) (Q : A → Prop) (HS : ∀ x, x ∈ S ↔ Q x) :
    Forall (λ x, @bool_decide (Q x) (gset_decision S Q HS x)) (elements S).
  Proof.
    apply Forall_forall. intros x Hx%list_elem_of_In%elem_of_elements.
    apply bool_decide_pack, HS, Hx.
  Qed.

  Definition gset_finite (S : gset A) (Q : A → Prop) (HS : ∀ x, x ∈ S ↔ Q x) :
    Finite (@dsig A Q (gset_decision S Q HS)).
  Proof.
    refine {| enum := Forall_to_sig (elements S) (gset_decision_Forall S Q HS) |}.
    - apply Forall_to_sig_NoDup, NoDup_elements.
    - intros x.
      edestruct (elem_of_Forall_to_sig_2 _ (gset_decision_Forall S Q HS) (`x)) as [Hx' ?].
      { apply elem_of_elements, HS. exact (bool_decide_unpack _ (proj2_sig x)). }
      destruct x as [x hx]. simpl in *.
      replace hx with Hx' by apply proof_irrel.
      done.
  Defined.

End gset_finite.

Lemma elem_of_map_list {A B} (f : A -> B) (l : list A) (x : B) :
  x ∈ map f l <-> exists y, x = f y /\ y ∈ l.
Proof.
  induction l as [|y l IH]; simpl.
  - split; [intros h; inversion h | intros (z & _ & h); inversion h].
  - rewrite elem_of_cons, IH. split.
    + intros [-> | (z & -> & hz)]; [exists y | exists z]; rewrite elem_of_cons; auto.
    + intros (z & -> & [-> | hz]%elem_of_cons); [left | right; exists z]; auto.
Qed.

Lemma elem_of_flat_map_list {A B} (F : A -> list B) (l : list A) (x : B) :
  x ∈ flat_map F l <-> exists a, a ∈ l /\ x ∈ F a.
Proof.
  induction l as [|a l IH]; simpl.
  - split; [intros h; inversion h | intros (b & h & _); inversion h].
  - rewrite elem_of_app, IH. split.
    + intros [h | (b & hb & h)]; [exists a | exists b]; rewrite elem_of_cons; auto.
    + intros (b & [-> | hb]%elem_of_cons & h); [left | right; exists b]; auto.
Qed.

Lemma elem_of_list_prod_iff {A B} (l : list A) (k : list B) (x : A * B) :
  x ∈ list_prod l k <-> x.1 ∈ l /\ x.2 ∈ k.
Proof. rewrite <- list_cprod_list_prod. apply list_elem_of_cprod. Qed.
