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
(* * lqCCS: tags of programs

    The tags of a program with the kind of the prefix they tag.  They only
    decrease along the steps: a tested program keeps its tags apart from
    those of the observer. *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list.
From TestingTheory Require Import ActTau.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.LTS lqCCS.Testing.Scheduled.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

(* ** Tags with their kinds *)

Inductive okind : Type := KTau | KOut | KIn | KOp | KMeas | KInit | KRec.

#[global] Instance okind_eq_dec : EqDecision okind.
Proof. solve_decision. Defined.

Definition prefix_tagged (𝜆 : prefix) : tag * okind :=
  match 𝜆 with
  | PTau t => (t, KTau)
  | PRecv t _ => (t, KIn)
  | POp t _ _ => (t, KOp)
  | PMeas t _ _ => (t, KMeas)
  | PInit t _ => (t, KInit)
  end.

Fixpoint tagged (P : proc) : list (tag * okind) :=
  match P with
  | PSend t _ _ => [(t, KOut)]
  | PIte _ P Q | P ∥ Q => tagged P ++ tagged Q
  | ν P => tagged P
  | PVar _ => []
  | PRec t _ P => (t, KRec) :: tagged P
  | PG g => gtagged g
  end
with gtagged (g : guard) : list (tag * okind) :=
  match g with
  | GNil _ | ① => []
  | 𝜆 ∙ P => prefix_tagged 𝜆 :: tagged P
  | (g1 + g2)%lq => gtagged g1 ++ gtagged g2
  end.

Definition tags (P : proc) : list tag := map fst (tagged P).

Lemma prefix_tagged_subst k v 𝜆 : prefix_tagged (prefix_subst k v 𝜆) = prefix_tagged 𝜆.
Proof. by destruct 𝜆. Qed.

Lemma prefix_tagged_shift k 𝜆 : prefix_tagged (prefix_shift k 𝜆) = prefix_tagged 𝜆.
Proof. by destruct 𝜆. Qed.

Lemma prefix_tagged_ren f 𝜆 : prefix_tagged (prefix_ren f 𝜆) = prefix_tagged 𝜆.
Proof. by destruct 𝜆. Qed.

Lemma tagged_subst k v P : tagged (subst k v P) = tagged P
with gtagged_gsubst k v g : gtagged (gsubst k v g) = gtagged g.
Proof.
  - destruct P; simpl; try done; try (by rewrite !tagged_subst); try apply gtagged_gsubst.
  - destruct g; simpl; try done; try (by rewrite !gtagged_gsubst).
    by rewrite prefix_tagged_subst, tagged_subst.
Qed.

Lemma tagged_shiftv k P : tagged (shiftv k P) = tagged P
with gtagged_gshiftv k g : gtagged (gshiftv k g) = gtagged g.
Proof.
  - destruct P; simpl; try done; try (by rewrite !tagged_shiftv); try apply gtagged_gshiftv.
  - destruct g; simpl; try done; try (by rewrite !gtagged_gshiftv).
    by rewrite prefix_tagged_shift, tagged_shiftv.
Qed.

Lemma tagged_ren f P : tagged (ren f P) = tagged P
with gtagged_gren f g : gtagged (gren f g) = gtagged g.
Proof.
  - destruct P; simpl; try done; try (by rewrite !tagged_ren); try apply gtagged_gren.
  - destruct g; simpl; try done; try (by rewrite !gtagged_gren).
    by rewrite prefix_tagged_ren, tagged_ren.
Qed.

Lemma tagged_shiftv_iter n P : tagged (Nat.iter n (shiftv 0) P) = tagged P.
Proof. induction n as [|n IH]; simpl; [done|]. by rewrite tagged_shiftv. Qed.

Lemma tagged_pr_subst X P Q x :
  x ∈ tagged (P ⦃ Q // X ⦄) → x ∈ tagged P ∨ x ∈ tagged Q
with gtagged_gpr_subst X g Q x :
  x ∈ gtagged (gpr_subst X g Q) → x ∈ gtagged g ∨ x ∈ tagged Q.
Proof.
  - destruct P; simpl; intros Hx.
    + by left.
    + apply elem_of_app in Hx as [Hx|Hx]; apply tagged_pr_subst in Hx as [Hx|Hx]; auto;
        left; apply elem_of_app; auto.
    + apply elem_of_app in Hx as [Hx|Hx]; apply tagged_pr_subst in Hx as [Hx|Hx]; auto;
        left; apply elem_of_app; auto.
    + apply tagged_pr_subst in Hx as [Hx|Hx]; [by left|]. right. by rewrite tagged_ren in Hx.
    + case_decide; [by right|]. by left.
    + case_decide; [by left|]. apply elem_of_cons in Hx as [->|Hx]; [left; by left|].
      apply tagged_pr_subst in Hx as [Hx|Hx]; [left; by right|by right].
    + by apply (gtagged_gpr_subst X).
  - destruct g; simpl; intros Hx.
    + by left.
    + by left.
    + apply elem_of_cons in Hx as [->|Hx]; [left; by left|].
      apply tagged_pr_subst in Hx as [Hx|Hx]; [left; by right|]. right. by rewrite tagged_shiftv_iter in Hx.
    + apply elem_of_app in Hx as [Hx|Hx]; apply gtagged_gpr_subst in Hx as [Hx|Hx]; auto;
        left; apply elem_of_app; auto.
Qed.

(* Along a step, the tags of a program only decrease. *)
Lemma prog_step_tagged P s l P' x : prog_step P s l P' → x ∈ tagged P' → x ∈ tagged P.
Proof.
  intros Hs. induction Hs as [g s l P' Hg| | | | | | | | | ] using prog_step_guard_ind; simpl; intros Hx.
  - induction Hg using prog_gstep_ind; simpl in *; try (apply elem_of_app; auto; fail).
    + by right.
    + rewrite tagged_subst in Hx. by right.
    + by right.
    + rewrite tagged_subst in Hx. by right.
    + by right.
  - by apply elem_of_nil in Hx.
  - apply elem_of_app. auto.
  - apply elem_of_app. auto.
  - apply elem_of_app in Hx as [Hx|Hx]; apply elem_of_app; auto.
  - apply elem_of_app in Hx as [Hx|Hx]; apply elem_of_app; auto.
  - apply elem_of_app in Hx as [Hx|Hx]; apply elem_of_app; auto.
  - apply elem_of_app in Hx as [Hx|Hx]; apply elem_of_app; auto.
  - auto.
  - apply tagged_pr_subst in Hx as [Hx|Hx]; [by right|done].
Qed.

Lemma prog_step_tags P s l P' t : prog_step P s l P' → t ∈ tags P' → t ∈ tags P.
Proof.
  intros Hs Ht. unfold tags in *. apply list_elem_of_fmap in Ht as (x & -> & Hx).
  apply list_elem_of_fmap. exists x. split; [done|]. by eapply prog_step_tagged.
Qed.

(* The tags of a choice. *)
Definition choice_tags (s : choice) : list tag :=
  match s with CEps => [] | CTag t => [t] | CPair t t' => [t; t'] end.

Lemma cpair_tags u t t' : u ∈ choice_tags (cpair t t') → u = t ∨ u = t'.
Proof.
  unfold cpair. simpl. intros Hu. apply elem_of_cons in Hu as [->|Hu].
  - destruct (Nat.min_spec t t') as [[_ ->]|[_ ->]]; auto.
  - apply elem_of_cons in Hu as [->|Hu]; [|by apply elem_of_nil in Hu].
    destruct (Nat.max_spec t t') as [[_ ->]|[_ ->]]; auto.
Qed.

(* The tags of the choice of a step belong to the program. *)
Lemma prog_step_choice_tags P s l P' u :
  prog_step P s l P' → u ∈ choice_tags s → u ∈ tags P.
Proof.
  intros Hs. induction Hs as [g s l P' Hg| | | | | | | | | ] using prog_step_guard_ind; unfold tags; simpl; intros Hu.
  - induction Hg using prog_gstep_ind; simpl in *.
    all: try (apply list_elem_of_singleton in Hu; subst; by left).
    + rewrite map_app. apply elem_of_app. left. by apply IHHg.
    + rewrite map_app. apply elem_of_app. right. by apply IHHg.
  - apply list_elem_of_singleton in Hu. subst. by left.
  - rewrite map_app. apply elem_of_app. left. by apply IHHs.
  - rewrite map_app. apply elem_of_app. right. by apply IHHs.
  - rewrite map_app. apply elem_of_app. left. by apply IHHs.
  - rewrite map_app. apply elem_of_app. right. by apply IHHs.
  - rewrite map_app. apply elem_of_app. destruct (cpair_tags _ _ _ Hu) as [-> | ->].
    + left. apply IHHs1. by left.
    + right. apply IHHs2. by left.
  - rewrite map_app. apply elem_of_app. destruct (cpair_tags _ _ _ Hu) as [-> | ->].
    + left. apply IHHs1. by left.
    + right. apply IHHs2. by left.
  - by apply IHHs.
  - apply list_elem_of_singleton in Hu. subst. by left.
Qed.
(* end hide *)
