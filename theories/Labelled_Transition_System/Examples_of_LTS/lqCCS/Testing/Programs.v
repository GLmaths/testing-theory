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

    The tags of a program with the kind of the prefix they tag.  Up to
    their generation, they only decrease along the steps: a tested program
    keeps its tags apart from those of the observer. *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base gmultiset countable decidable list propset.
From TestingTheory Require Import ActTau.
From TestingTheory Require Import lqCCS.lqCCS_prog.Syntax lqCCS.Helper_substitution.De_Brujin_lemmas lqCCS.General_definition.Parallel_choice_LTS lqCCS.quantum_mem.LTS lqCCS.lqCCS_prog.LTS lqCCS.lqCCS_par_Qmem.LTS lqCCS.lqCCS_process.LTS.LTS lqCCS.Helper_substitution.Label_lemmas lqCCS.Testing.Scheduled lqCCS.Testing.Observer_predicates lqCCS.Helper_substitution.Tag_lemmas.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

(* ** Tags along the transitions *)

Section LqP.
  Context `{LP : lqCCS_Parameters}.

Lemma prog_step_tagged P s l P' x :
  P ⟶ₚ{l}[s] P' → x ∈ tagged (tren tag_base P') → x ∈ tagged (tren tag_base P).
Proof.
  intros Hs. induction Hs as [g s l P' Hg| | | | | | | | | ]; simpl; intros Hx.
  - induction Hg; simpl in *; try (apply elem_of_app; auto; fail).
    + by right.
    + rewrite (proj1 tren_subst), tagged_subst in Hx. by right.
    + by right.
    + rewrite (proj1 tren_subst), tagged_subst in Hx. by right.
    + by right.
  - by apply elem_of_nil in Hx.
  - apply elem_of_app. auto.
  - apply elem_of_app. auto.
  - apply elem_of_app in Hx as [Hx|Hx]; apply elem_of_app; auto.
  - apply elem_of_app in Hx as [Hx|Hx]; apply elem_of_app; auto.
  - apply elem_of_app in Hx as [Hx|Hx]; apply elem_of_app; auto.
  - apply elem_of_app in Hx as [Hx|Hx]; apply elem_of_app; auto.
  - auto.
  - rewrite (proj1 tren_pr_subst) in Hx. apply tagged_pr_subst in Hx as [Hx|Hx]; [by right|].
    simpl in Hx. by rewrite tag_base_up, tren_base_up in Hx.
Qed.

(* The tags a program may come to have: those of the roots of its tags. *)
Definition otags (P : proc) : propset tag := {[ t | tag_base t ∈ tags (tren tag_base P) ]}.

Lemma tags_otags P t : t ∈ tags P → t ∈ otags P.
Proof.
  unfold otags, tags. intros (x & -> & Hx)%list_elem_of_fmap. apply elem_of_PropSet.
  rewrite tagged_tren. apply list_elem_of_fmap. exists (tag_base x.1, x.2). split; [done|].
  apply list_elem_of_fmap. by exists x.
Qed.

Lemma prog_step_otags P s l P' t : P ⟶ₚ{l}[s] P' → t ∈ otags P' → t ∈ otags P.
Proof.
  unfold otags, tags. intros Hs Ht. rewrite elem_of_PropSet in Ht |- *.
  apply list_elem_of_fmap in Ht as (x & E & Hx). apply list_elem_of_fmap. exists x. split; [done|].
  by eapply prog_step_tagged.
Qed.

Lemma choice_pair_elem u t t' : u ∈ ({[+ t; t' +]} : choice) → u = t ∨ u = t'.
Proof. rewrite gmultiset_elem_of_disj_union, !gmultiset_elem_of_singleton. tauto. Qed.

(* The tags of the choice of a step belong to the program. *)
Lemma prog_step_choice_tags P s l P' u :
  P ⟶ₚ{l}[s] P' → u ∈ s → u ∈ tags P.
Proof.
  intros Hs. induction Hs as [g s l P' Hg| | | | | | | | | ]; unfold tags; simpl; intros Hu.
  - induction Hg; simpl in *.
    all: try (apply gmultiset_elem_of_singleton in Hu; subst; by left).
    + rewrite map_app. apply elem_of_app. left. by apply IHHg.
    + rewrite map_app. apply elem_of_app. right. by apply IHHg.
  - apply gmultiset_elem_of_singleton in Hu. subst. by left.
  - rewrite map_app. apply elem_of_app. left. by apply IHHs.
  - rewrite map_app. apply elem_of_app. right. by apply IHHs.
  - rewrite map_app. apply elem_of_app. left. by apply IHHs.
  - rewrite map_app. apply elem_of_app. right. by apply IHHs.
  - rewrite map_app. apply elem_of_app. destruct (choice_pair_elem _ _ _ Hu) as [-> | ->].
    + left. by apply IHHs1, gmultiset_elem_of_singleton.
    + right. by apply IHHs2, gmultiset_elem_of_singleton.
  - rewrite map_app. apply elem_of_app. destruct (choice_pair_elem _ _ _ Hu) as [-> | ->].
    + left. by apply IHHs1, gmultiset_elem_of_singleton.
    + right. by apply IHHs2, gmultiset_elem_of_singleton.
  - by apply IHHs.
  - apply gmultiset_elem_of_singleton in Hu. subst. by left.
Qed.

End LqP.

(* end hide *)
