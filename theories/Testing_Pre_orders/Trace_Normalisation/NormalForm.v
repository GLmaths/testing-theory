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

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From Stdlib.Program Require Import Equality.
From stdpp Require Import base countable list decidable finite gmap gmultiset.
From TestingTheory Require Import ActTau gLts.

(** * Traces in normal form (combinatorial core)

    This file contains the purely combinatorial part of the normalisation of
    traces described in the ESOP'25 submission (file [traces_normal_form.tex]),
    generalised to the setting of [gLts]: instead of the two classes of actions
    "input"/"output" we work with an arbitrary classification of actions into
    three classes,

    - [CNB]  the non-blocking actions (the outputs of the original work),
    - [CIN]  the blocking actions that have a non-blocking co-action
             (the inputs of the original work),
    - [COP]  the remaining actions, that is the blocking actions whose
             co-actions are blocking as well; those are *opaque*, they commute
             with nothing.

    The normalisation of a trace [s] forgets the order of the actions inside a
    maximal run of consecutive actions of the same (non-opaque) class, and it
    keeps the order of the runs.  Contrary to the original development a
    normalised trace is *not* turned back into a list of actions: it is a list
    of multisets, each of them tagged by the class of its elements.  Opaque
    actions are recorded as singleton runs that never merge, so that they act
    as separators.

    When there are no opaque actions, this run-length encoding carries exactly
    the same information as the sequence of pairs
    [(I_0, M_0), (I_1, M_1), ..., (I_n, M_n)] of the original work: a pair
    [(I_k, M_k)] is the run of inputs [I_k] immediately followed by the run of
    outputs [M_k], and a new pair is started precisely when an output is
    followed by an input.  For instance, writing [a] for an input and [ā] for
    an output,

      normalisation of  [c a b̄ d̄ d̄ a ē f̄ e]
        = CIN {c, a}, CNB {b̄, d̄, d̄}, CIN {a}, CNB {ē, f̄}, CIN {e}

    which is the reading of [({c,a},{b̄,d̄,d̄}), ({a},{ē,f̄}), ({e},∅)].
    Contrary to the original development, the normalised trace is kept as a
    list of multisets: it is never turned back into a list of actions.

    The file is parametric in the classifier [cls]; it is instantiated on
    traces in [Normalisation.v] and on co-traces in [NormalisationCo.v]. *)

(** ** Classes of actions *)

Inductive act_class := CNB | CIN | COP.

#[global] Instance act_class_eq_dec : EqDecision act_class.
Proof. solve_decision. Defined.

(** A small compatibility lemma between [In] (from the standard library, used
    by [Forall_forall]) and [∈] (from stdpp). *)
Lemma elem_of_of_In {B : Type} (l : list B) (x : B) : In x l -> x ∈ l.
Proof.
  induction l as [| y l IH]; simpl; [contradiction |].
  intros [heq | h]; eapply elem_of_cons.
  - left. now symmetry.
  - right. now eapply IH.
Qed.

(** A few list helpers, stated here to avoid the name clashes between the
    standard library and stdpp. *)

Lemma Forall_weaken {B : Type} (Q R : B -> Prop) (u : list B) :
  (forall x, Q x -> R x) -> Forall Q u -> Forall R u.
Proof. intro h. induction 1; constructor; auto. Qed.

Lemma Forall_app_2 {B : Type} (Q : B -> Prop) (l1 l2 : list B) :
  Forall Q l1 -> Forall Q l2 -> Forall Q (l1 ++ l2).
Proof. induction 1; simpl; [auto | constructor; auto]. Qed.

Lemma Forall_app_inv {B : Type} (Q : B -> Prop) (l1 l2 : list B) :
  Forall Q (l1 ++ l2) -> Forall Q l1 /\ Forall Q l2.
Proof.
  induction l1 as [| x l1 IH]; simpl; intro h.
  - split; [constructor | exact h].
  - eapply Forall_cons_1 in h as (hx & h). destruct (IH h) as (h1 & h2).
    split; [constructor; assumption | exact h2].
Qed.

Lemma length_filter_0 {B : Type} (Q : B -> Prop) `{!forall x, Decision (Q x)} (u : list B) :
  Forall (fun x => ¬ Q x) u -> length (filter Q u) = 0.
Proof.
  induction 1 as [| x u hx hu IH]; simpl; [reflexivity |].
  rewrite filter_cons_False by exact hx. exact IH.
Qed.

Lemma Forall_filter_self {B : Type} (Q : B -> Prop) `{!forall x, Decision (Q x)} (u : list B) :
  Forall Q (filter Q u).
Proof.
  induction u as [| x u IH]; simpl; [constructor |].
  destruct (decide (Q x)) as [h | h].
  - rewrite filter_cons_True by exact h. constructor; assumption.
  - rewrite filter_cons_False by exact h. exact IH.
Qed.

Lemma length_app' {B : Type} (l1 l2 : list B) :
  length (l1 ++ l2) = length l1 + length l2.
Proof. induction l1; simpl; [reflexivity | now rewrite IHl1]. Qed.

Lemma filter_filter_eq {B : Type} (Q R : B -> Prop)
  `{!forall x, Decision (Q x)} `{!forall x, Decision (R x)} (u : list B) :
  (forall x, Q x -> R x) -> filter Q (filter R u) = filter Q u.
Proof.
  intro h. induction u as [| x u IH]; [reflexivity |].
  destruct (decide (R x)) as [hr | hr].
  - rewrite (filter_cons_True R x u hr).
    destruct (decide (Q x)) as [hq | hq].
    + rewrite (filter_cons_True Q x (filter R u) hq), (filter_cons_True Q x u hq).
      now f_equal.
    + rewrite (filter_cons_False Q x (filter R u) hq), (filter_cons_False Q x u hq).
      exact IH.
  - rewrite (filter_cons_False R x u hr).
    rewrite (filter_cons_False Q x u); [exact IH | intro hq; exact (hr (h x hq))].
Qed.

(** ** Normalised traces *)

(** A block is a class together with the multiset of the actions of that class
    occurring in a maximal run. *)
Definition nblock (A : Type) `{ExtAction A} : Type := (act_class * gmultiset A)%type.

Definition ntrace (A : Type) `{ExtAction A} : Type := list (nblock A).

Section NormalForm.

  Context `{EA : ExtAction A}.

  (** The classification of actions.  Everything below only depends on [cls]. *)
  Variable cls : A -> act_class.

  (** *** The normalisation function *)

  (** [ncons μ σ] adds [μ] in front of the normalised trace [σ]: it is merged
      with the first block of [σ] when they have the same, non opaque, class,
      and it opens a new block otherwise. *)
  Definition ncons (μ : A) (σ : ntrace A) : ntrace A :=
    match σ with
    | (c , M) :: σ' =>
        if decide (cls μ = c /\ cls μ ≠ COP)
        then (c , {[+ μ +]} ⊎ M) :: σ'
        else (cls μ , {[+ μ +]}) :: σ
    | [] => [ (cls μ , {[+ μ +]}) ]
    end.

  Fixpoint nform (s : trace A) : ntrace A :=
    match s with
    | [] => []
    | μ :: s' => ncons μ (nform s')
    end.

  (** [nlin σ] is the canonical linearisation of [σ]: inside each block the
      actions are listed in the canonical order of [elements]. *)
  Fixpoint nlin (σ : ntrace A) : trace A :=
    match σ with
    | [] => []
    | (_ , M) :: σ' => elements M ++ nlin σ'
    end.

  Lemma nform_app s1 s2 : nform (s1 ++ s2) = foldr ncons (nform s2) s1.
  Proof. induction s1 as [| μ s1 IH]; simpl; [reflexivity | now rewrite IH]. Qed.

  (** *** Well-formedness *)

  Definition block_wf (b : nblock A) : Prop :=
    match b with (c , M) => M ≠ ∅ /\ forall μ, μ ∈ M -> cls μ = c end.

  Definition nf_wf (σ : ntrace A) : Prop := Forall block_wf σ.

  Lemma nf_wf_ncons μ σ : nf_wf σ -> nf_wf (ncons μ σ).
  Proof.
    intro hwf. destruct σ as [| (c , M) σ']; simpl.
    - constructor; [| constructor]. split; [multiset_solver |].
      intros ν hν. assert (hνμ : ν = μ) by multiset_solver. now rewrite hνμ.
    - inversion hwf as [| b σ0 hb hσ']; subst.
      destruct (decide (cls μ = c /\ cls μ ≠ COP)) as [(heq & _) | hne].
      + constructor; [| exact hσ'].
        destruct hb as (hne0 & hall). split; [multiset_solver |].
        intros ν hν. eapply gmultiset_elem_of_disj_union in hν as [hν | hν].
        * assert (hνμ : ν = μ) by multiset_solver. rewrite hνμ. exact heq.
        * now eapply hall.
      + constructor; [| exact hwf]. split; [multiset_solver |].
        intros ν hν. assert (hνμ : ν = μ) by multiset_solver. now rewrite hνμ.
  Qed.

  Lemma nf_wf_nform s : nf_wf (nform s).
  Proof.
    induction s as [| μ s IH]; simpl; [constructor | now eapply nf_wf_ncons].
  Qed.

  (** *** Equivalence of traces up to swapping consecutive actions of the same
      (non-opaque) class *)

  Inductive tequiv : trace A -> trace A -> Prop :=
  | te_refl s : tequiv s s
  | te_trans s t u : tequiv s t -> tequiv t u -> tequiv s u
  | te_swap s1 μ ν s2 :
    cls μ = cls ν -> cls μ ≠ COP ->
    tequiv (s1 ++ μ :: ν :: s2) (s1 ++ ν :: μ :: s2).

  (* hints are added after the section *)

  Lemma tequiv_sym s t : tequiv s t -> tequiv t s.
  Proof.
    induction 1 as [ s | s t u h1 IH1 h2 IH2 | s1 μ ν s2 heq hne ].
    - constructor.
    - eapply te_trans; eassumption.
    - eapply te_swap; [now symmetry | now rewrite <- heq].
  Qed.

  Lemma tequiv_app_l u s t : tequiv s t -> tequiv (u ++ s) (u ++ t).
  Proof.
    induction 1 as [ s | s t v h1 IH1 h2 IH2 | s1 μ ν s2 heq hne ].
    - constructor.
    - eapply te_trans; eassumption.
    - rewrite 2 app_assoc. eapply te_swap; eassumption.
  Qed.

  Lemma tequiv_app_r u s t : tequiv s t -> tequiv (s ++ u) (t ++ u).
  Proof.
    induction 1 as [ s | s t v h1 IH1 h2 IH2 | s1 μ ν s2 heq hne ].
    - constructor.
    - eapply te_trans; eassumption.
    - rewrite <- 2 app_assoc. simpl. eapply te_swap; eassumption.
  Qed.

  Lemma tequiv_cons μ s t : tequiv s t -> tequiv (μ :: s) (μ :: t).
  Proof. intro h. eapply (tequiv_app_l [μ]) in h. exact h. Qed.

  (** Inside a run of actions of a same non-opaque class every permutation is
      reachable by consecutive swaps. *)
  Lemma tequiv_perm_class c s1 s2 u v :
    c ≠ COP -> Forall (fun μ => cls μ = c) s1 -> s1 ≡ₚ s2 ->
    tequiv (u ++ s1 ++ v) (u ++ s2 ++ v).
  Proof.
    intros hc hall hp. revert u hall.
    induction hp as [| μ l1 l2 hp IH | μ ν l | l1 l2 l3 hp1 IH1 hp2 IH2 ]; intros u hall.
    - constructor.
    - eapply Forall_cons_1 in hall as (hμ & hl1).
      specialize (IH (u ++ [μ]) hl1).
      rewrite <- !app_assoc in IH. simpl in IH. exact IH.
    - eapply Forall_cons_1 in hall as (hν & hrest).
      eapply Forall_cons_1 in hrest as (hμ & hl).
      simpl. eapply te_swap; [now rewrite hν, hμ | now rewrite hν].
    - eapply te_trans.
      + eapply IH1. exact hall.
      + eapply IH2. eapply (Permutation_Forall hp1). exact hall.
  Qed.

  (** *** [nform] is invariant under [tequiv] *)

  Lemma ncons_comm μ ν σ :
    cls μ = cls ν -> cls μ ≠ COP -> ncons μ (ncons ν σ) = ncons ν (ncons μ σ).
  Proof.
    intros heq hne.
    assert (hne' : cls ν ≠ COP) by now rewrite <- heq.
    destruct σ as [| (c , M) σ' ]; simpl.
    - rewrite 2 decide_True by (split; [now rewrite heq | assumption]).
      rewrite heq. f_equal. f_equal. multiset_solver.
    - destruct (decide (cls ν = c /\ cls ν ≠ COP)) as [ (heqc & _) | hnc ];
        destruct (decide (cls μ = c /\ cls μ ≠ COP)) as [ (heqc' & _) | hnc' ];
        simpl.
      + rewrite 2 decide_True by (split; assumption).
        f_equal. f_equal. multiset_solver.
      + exfalso. eapply hnc'. split; [now rewrite heq | assumption].
      + exfalso. eapply hnc. split; [now rewrite <- heq | assumption].
      + rewrite 2 decide_True by (split; [congruence | assumption]).
        rewrite heq. f_equal. f_equal. multiset_solver.
  Qed.

  Lemma nform_tequiv s t : tequiv s t -> nform s = nform t.
  Proof.
    induction 1 as [ s | s t u h1 IH1 h2 IH2 | s1 μ ν s2 heq hne ].
    - reflexivity.
    - now transitivity (nform t).
    - rewrite 2 nform_app. simpl. now rewrite ncons_comm.
  Qed.

  (** *** A trace is [tequiv] to the linearisation of its normal form *)

  Lemma nlin_ncons μ σ :
    nf_wf σ -> tequiv (μ :: nlin σ) (nlin (ncons μ σ)).
  Proof.
    intro hwf. destruct σ as [| (c , M) σ' ]; simpl.
    - rewrite gmultiset_elements_singleton. constructor.
    - eapply Forall_cons_1 in hwf as (hb & hσ'). destruct hb as (hne0 & hall).
      destruct (decide (cls μ = c /\ cls μ ≠ COP)) as [ (heqc & hnc) | hnc ]; simpl.
      + eapply (tequiv_perm_class c (μ :: elements M) (elements ({[+ μ +]} ⊎ M)) [] (nlin σ')).
        * now rewrite <- heqc.
        * constructor; [exact heqc |].
          eapply Forall_forall. intros ν hν. eapply hall.
          rewrite <- gmultiset_elem_of_elements. now eapply elem_of_of_In.
        * rewrite gmultiset_elements_disj_union, gmultiset_elements_singleton.
          reflexivity.
      + rewrite gmultiset_elements_singleton. constructor.
  Qed.

  Lemma tequiv_nform s : tequiv s (nlin (nform s)).
  Proof.
    induction s as [| μ s IH]; simpl; [constructor |].
    eapply te_trans.
    - eapply tequiv_cons, IH.
    - eapply nlin_ncons, nf_wf_nform.
  Qed.

  (** Two traces with the same normal form are related by [tequiv]. *)
  Lemma tequiv_of_nform s t : nform s = nform t -> tequiv s t.
  Proof.
    intro heq. eapply te_trans; [eapply tequiv_nform |].
    rewrite heq. eapply tequiv_sym, tequiv_nform.
  Qed.

  Corollary nform_iff_tequiv s t : nform s = nform t <-> tequiv s t.
  Proof. split; [eapply tequiv_of_nform | eapply nform_tequiv]. Qed.

  (** *** Canonicity *)

  Lemma nform_nlin_nform s : nform (nlin (nform s)) = nform s.
  Proof. symmetry. eapply nform_tequiv, tequiv_nform. Qed.

  Lemma tequiv_perm s t : tequiv s t -> s ≡ₚ t.
  Proof.
    induction 1 as [ s | s t u h1 IH1 h2 IH2 | s1 μ ν s2 heq hne ].
    - reflexivity.
    - etransitivity; eassumption.
    - eapply Permutation_app_head. constructor.
  Qed.

  Corollary nlin_nform_perm s : nlin (nform s) ≡ₚ s.
  Proof. symmetry. eapply tequiv_perm, tequiv_nform. Qed.

  Corollary nlin_nform_length s : length (nlin (nform s)) = length s.
  Proof. eapply Permutation_length, nlin_nform_perm. Qed.

End NormalForm.

(** ** Transporting [tequiv] along a renaming of the actions

    Used to relate the normalisation of co-traces with the normalisation of
    traces, through the involution [co]. *)
Lemma tequiv_map {A B : Type} (f : A -> B) (c1 : A -> act_class) (c2 : B -> act_class) s t :
  (forall μ, c2 (f μ) = c1 μ) -> tequiv c1 s t -> tequiv c2 (map f s) (map f t).
Proof.
  intro hf. induction 1 as [ s | s t u h1 IH1 h2 IH2 | s1 μ ν s2 heq hne ].
  - constructor.
  - eapply te_trans; eassumption.
  - rewrite 2 map_app. simpl. eapply te_swap.
    + now rewrite 2 hf.
    + now rewrite hf.
Qed.


(** ** Counting inversions

    In order to show that the normal form of a trace is the least element of
    its equivalence class for the preorder on traces of [Normalisation.v], we
    count, for two predicates [Pl] and [Pr], the pairs of positions [i < j]
    such that the [i]-th action satisfies [Pl] and the [j]-th one [Pr].  Such a
    count is left unchanged by a swap of two consecutive actions that does not
    destroy such a pair, and it never increases when actions are erased. *)

Definition bit (Q : Prop) `{!Decision Q} : nat := if decide Q then 1 else 0.

Section Inversions.

  Context {B : Type}.
  Context (Pl Pr : B -> Prop).
  Context `{!forall x, Decision (Pl x)} `{!forall x, Decision (Pr x)}.

  Fixpoint inv_cnt (s : list B) : nat :=
    match s with
    | [] => 0
    | μ :: s' => bit (Pl μ) * length (filter Pr s') + inv_cnt s'
    end.

  Lemma length_filter_cons (Q : B -> Prop) `{!forall x, Decision (Q x)} x s :
    length (filter Q (x :: s)) = bit (Q x) + length (filter Q s).
  Proof.
    unfold bit. destruct (decide (Q x)) as [h | h].
    - rewrite filter_cons_True by exact h. reflexivity.
    - rewrite filter_cons_False by exact h. reflexivity.
  Qed.

  Lemma length_filter_app (Q : B -> Prop) `{!forall x, Decision (Q x)} l1 l2 :
    length (filter Q (l1 ++ l2)) = length (filter Q l1) + length (filter Q l2).
  Proof.
    induction l1 as [| x l1 IH]; simpl; [reflexivity |].
    rewrite 2 length_filter_cons, IH. lia.
  Qed.

  Lemma inv_cnt_app s1 s2 :
    inv_cnt (s1 ++ s2)
    = inv_cnt s1 + length (filter Pl s1) * length (filter Pr s2) + inv_cnt s2.
  Proof.
    induction s1 as [| μ s1 IH]; simpl; [lia |].
    rewrite IH, length_filter_app, length_filter_cons.
    unfold bit. destruct (decide (Pl μ)); simpl; lia.
  Qed.

  (** The part of the count that a swap of two consecutive actions leaves
      untouched. *)
  Definition inv_ctx (s1 : list B) (x y : B) (s2 : list B) : nat :=
    inv_cnt s1
    + length (filter Pl s1) * (bit (Pr x) + bit (Pr y) + length (filter Pr s2))
    + (bit (Pl x) + bit (Pl y)) * length (filter Pr s2)
    + inv_cnt s2.

  Lemma inv_cnt_middle s1 x y s2 :
    inv_cnt (s1 ++ x :: y :: s2) = inv_ctx s1 x y s2 + bit (Pl x) * bit (Pr y).
  Proof.
    unfold inv_ctx.
    rewrite inv_cnt_app. simpl.
    rewrite 2 length_filter_cons. lia.
  Qed.

  Lemma inv_ctx_sym s1 x y s2 : inv_ctx s1 x y s2 = inv_ctx s1 y x s2.
  Proof. unfold inv_ctx. lia. Qed.

  (** A swap never increases the count as soon as it does not create an
      inversion. *)
  Lemma inv_cnt_swap_le s1 x y s2 :
    ¬ (Pl y /\ Pr x) -> inv_cnt (s1 ++ y :: x :: s2) <= inv_cnt (s1 ++ x :: y :: s2).
  Proof.
    intro hno. rewrite 2 inv_cnt_middle, (inv_ctx_sym s1 y x s2).
    assert (bit (Pl y) * bit (Pr x) = 0) as heq.
    { unfold bit. destruct (decide (Pl y)); destruct (decide (Pr x)); [| lia..].
      exfalso. eapply hno. split; assumption. }
    rewrite heq. lia.
  Qed.

  (** and it strictly decreases it when it destroys one. *)
  Lemma inv_cnt_swap_lt s1 x y s2 :
    ¬ (Pl y /\ Pr x) -> Pl x -> Pr y ->
    inv_cnt (s1 ++ y :: x :: s2) < inv_cnt (s1 ++ x :: y :: s2).
  Proof.
    intros hno hx hy. rewrite 2 inv_cnt_middle, (inv_ctx_sym s1 y x s2).
    assert (bit (Pl y) * bit (Pr x) = 0) as heq.
    { unfold bit. destruct (decide (Pl y)); destruct (decide (Pr x)); [| lia..].
      exfalso. eapply hno. split; assumption. }
    rewrite heq. unfold bit. rewrite 2 decide_True by assumption. lia.
  Qed.

  Lemma inv_cnt_drop2 s1 x y s2 :
    inv_cnt (s1 ++ s2) <= inv_cnt (s1 ++ x :: y :: s2).
  Proof.
    rewrite inv_cnt_middle. unfold inv_ctx.
    rewrite inv_cnt_app. lia.
  Qed.

  (** Erasing a whole factor never increases the count. *)
  Lemma inv_cnt_erase s1 u s2 :
    inv_cnt (s1 ++ s2) <= inv_cnt (s1 ++ u ++ s2).
  Proof. rewrite !inv_cnt_app, length_filter_app. lia. Qed.

  (** A count vanishes as soon as one of the two predicates is never
      satisfied. *)
  Lemma inv_cnt_0_l u : Forall (fun x => ¬ Pl x) u -> inv_cnt u = 0.
  Proof.
    induction 1 as [| x u hx hu IH]; simpl; [reflexivity |].
    unfold bit. rewrite decide_False by exact hx. lia.
  Qed.

  Lemma inv_cnt_0_r u : Forall (fun x => ¬ Pr x) u -> inv_cnt u = 0.
  Proof.
    induction 1 as [| x u hx hu IH]; simpl; [reflexivity |].
    rewrite (length_filter_0 Pr u hu), IH. lia.
  Qed.


End Inversions.

Arguments inv_cnt {B} Pl Pr {_ _} s.

(** ** Redexes of a binary relation on consecutive actions

    The feedback rule of the preorders on traces and on co-traces erases two
    *consecutive* actions related by a binary relation [R].  Two such redexes
    can never overlap when [R x y] forbids [R y z] -- which is the case for the
    feedback, by [dual_blocks] -- so the erasure is an orthogonal rewriting
    system: the redexes are pairwise disjoint and the erasures commute.  We
    only need here that a trace can be reduced to one without redexes. *)

Section Redex.

  Context {B : Type} (R : B -> B -> Prop) `{!forall x y, Decision (R x y)}.

  Definition no_redex (t : list B) : Prop :=
    forall s1 x y s2, t = s1 ++ x :: y :: s2 -> ¬ R x y.

  Lemma no_redex_short (t : list B) : length t <= 1 -> no_redex t.
  Proof.
    intros hl s1 x y s2 heq hr. subst t.
    rewrite length_app' in hl. simpl in hl. lia.
  Qed.

  Fixpoint has_redex (s : list B) : bool :=
    match s with
    | x :: ((y :: _) as s') => if decide (R x y) then true else has_redex s'
    | _ => false
    end.

  Lemma has_redex_true s :
    has_redex s = true -> exists s1 x y s2, s = s1 ++ x :: y :: s2 /\ R x y.
  Proof.
    induction s as [| x s IH]; [discriminate |].
    destruct s as [| y s']; [discriminate |].
    simpl. destruct (decide (R x y)) as [hr | hr].
    - intros _. exists [], x, y, s'. split; [reflexivity | exact hr].
    - intro h. destruct (IH h) as (s1 & a & b & s2 & heq & hab).
      exists (x :: s1), a, b, s2. split; [now rewrite heq | exact hab].
  Qed.

  Lemma has_redex_false s : has_redex s = false -> no_redex s.
  Proof.
    induction s as [| x s IH].
    - intros _. eapply no_redex_short. simpl. lia.
    - destruct s as [| y s'].
      + intros _. eapply no_redex_short. simpl. lia.
      + simpl. destruct (decide (R x y)) as [hr | hr]; [discriminate |].
        intros h s1 a b s2 heq.
        destruct s1 as [| c s1]; simpl in heq; injection heq.
        * intros heq2 hb ha. subst a. subst b. exact hr.
        * intros heq2 _. exact (IH h s1 a b s2 heq2).
  Qed.

End Redex.

Arguments no_redex {B} R t.
Arguments has_redex {B} R {_} s.

(** ** A combinatorial preorder on traces

    The three families of rearrangements that the alternative characterisations
    of the testing preorders enjoy -- delaying an action of class [CNB],
    anticipating an action of class [CIN], and erasing a factor -- only depend
    on the classification of the actions.  We isolate here the combinatorial
    content that they share, so that the corresponding facts on traces and on
    co-traces are two instances of the same statements.

    The key point is that the number of pairs of actions that are still in the
    "wrong" order, added to the length of the trace, never increases along
    these rearrangements, and strictly decreases unless the rearrangement is a
    swap of two consecutive actions of the same class -- which is exactly what
    the normalisation quotients by.  This is the argument of Proposition 4.7 of
    Boreale, De Nicola and Pugliese, *Trace and Testing Equivalence on
    Asynchronous Processes* (Inform. and Comput. 172, 2002), where the measure
    is written [d(.)]. *)

Section Measure.

  Context `{EA : ExtAction A}.
  Variable cls : A -> act_class.

  Definition inv_nb (s : list A) : nat :=
    inv_cnt (fun μ => cls μ = CNB) (fun μ => cls μ ≠ CNB) s.

  Definition inv_in (s : list A) : nat :=
    inv_cnt (fun μ => cls μ ≠ CIN) (fun μ => cls μ = CIN) s.

  Definition tmeasure (s : list A) : nat := length s + inv_nb s + inv_in s.

  Lemma length_middle_swap (s1 : list A) (x y : A) s2 :
    length (s1 ++ x :: y :: s2) = length (s1 ++ y :: x :: s2).
  Proof. rewrite 2 length_app'. reflexivity. Qed.

  (** *** Effect of the three rearrangements on the measure *)

  Lemma tmeasure_delay s1 x y s2 :
    cls x = CNB -> tmeasure (s1 ++ y :: x :: s2) <= tmeasure (s1 ++ x :: y :: s2).
  Proof.
    intro hx. unfold tmeasure, inv_nb, inv_in.
    pose proof (length_middle_swap s1 x y s2).
    assert (inv_cnt (fun μ => cls μ = CNB) (fun μ => cls μ ≠ CNB) (s1 ++ y :: x :: s2)
            <= inv_cnt (fun μ => cls μ = CNB) (fun μ => cls μ ≠ CNB) (s1 ++ x :: y :: s2)).
    { eapply inv_cnt_swap_le. intros (h1 & h2). exact (h2 hx). }
    assert (inv_cnt (fun μ => cls μ ≠ CIN) (fun μ => cls μ = CIN) (s1 ++ y :: x :: s2)
            <= inv_cnt (fun μ => cls μ ≠ CIN) (fun μ => cls μ = CIN) (s1 ++ x :: y :: s2)).
    { eapply inv_cnt_swap_le. intros (h1 & h2). rewrite hx in h2. discriminate. }
    lia.
  Qed.

  Lemma tmeasure_delay_lt s1 x y s2 :
    cls x = CNB -> cls y ≠ CNB ->
    tmeasure (s1 ++ y :: x :: s2) < tmeasure (s1 ++ x :: y :: s2).
  Proof.
    intros hx hy. unfold tmeasure, inv_nb, inv_in.
    pose proof (length_middle_swap s1 x y s2).
    assert (inv_cnt (fun μ => cls μ = CNB) (fun μ => cls μ ≠ CNB) (s1 ++ y :: x :: s2)
            < inv_cnt (fun μ => cls μ = CNB) (fun μ => cls μ ≠ CNB) (s1 ++ x :: y :: s2)).
    { eapply inv_cnt_swap_lt; [intros (h1 & h2); exact (h2 hx) | exact hx | exact hy]. }
    assert (inv_cnt (fun μ => cls μ ≠ CIN) (fun μ => cls μ = CIN) (s1 ++ y :: x :: s2)
            <= inv_cnt (fun μ => cls μ ≠ CIN) (fun μ => cls μ = CIN) (s1 ++ x :: y :: s2)).
    { eapply inv_cnt_swap_le. intros (h1 & h2). rewrite hx in h2. discriminate. }
    lia.
  Qed.

  Lemma tmeasure_anticipate s1 x y s2 :
    cls y = CIN -> tmeasure (s1 ++ y :: x :: s2) <= tmeasure (s1 ++ x :: y :: s2).
  Proof.
    intro hy. unfold tmeasure, inv_nb, inv_in.
    pose proof (length_middle_swap s1 x y s2).
    assert (inv_cnt (fun μ => cls μ = CNB) (fun μ => cls μ ≠ CNB) (s1 ++ y :: x :: s2)
            <= inv_cnt (fun μ => cls μ = CNB) (fun μ => cls μ ≠ CNB) (s1 ++ x :: y :: s2)).
    { eapply inv_cnt_swap_le. intros (h1 & h2). rewrite hy in h1. discriminate. }
    assert (inv_cnt (fun μ => cls μ ≠ CIN) (fun μ => cls μ = CIN) (s1 ++ y :: x :: s2)
            <= inv_cnt (fun μ => cls μ ≠ CIN) (fun μ => cls μ = CIN) (s1 ++ x :: y :: s2)).
    { eapply inv_cnt_swap_le. intros (h1 & h2). exact (h1 hy). }
    lia.
  Qed.

  Lemma tmeasure_anticipate_lt s1 x y s2 :
    cls y = CIN -> cls x ≠ CIN ->
    tmeasure (s1 ++ y :: x :: s2) < tmeasure (s1 ++ x :: y :: s2).
  Proof.
    intros hy hx. unfold tmeasure, inv_nb, inv_in.
    pose proof (length_middle_swap s1 x y s2).
    assert (inv_cnt (fun μ => cls μ = CNB) (fun μ => cls μ ≠ CNB) (s1 ++ y :: x :: s2)
            <= inv_cnt (fun μ => cls μ = CNB) (fun μ => cls μ ≠ CNB) (s1 ++ x :: y :: s2)).
    { eapply inv_cnt_swap_le. intros (h1 & h2). rewrite hy in h1. discriminate. }
    assert (inv_cnt (fun μ => cls μ ≠ CIN) (fun μ => cls μ = CIN) (s1 ++ y :: x :: s2)
            < inv_cnt (fun μ => cls μ ≠ CIN) (fun μ => cls μ = CIN) (s1 ++ x :: y :: s2)).
    { eapply inv_cnt_swap_lt; [intros (h1 & h2); exact (h1 hy) | exact hx | exact hy]. }
    lia.
  Qed.

  Lemma tmeasure_erase s1 u s2 :
    u ≠ [] -> tmeasure (s1 ++ s2) < tmeasure (s1 ++ u ++ s2).
  Proof.
    intro hu. unfold tmeasure, inv_nb, inv_in.
    pose proof (inv_cnt_erase (fun μ => cls μ = CNB) (fun μ => cls μ ≠ CNB) s1 u s2).
    pose proof (inv_cnt_erase (fun μ => cls μ ≠ CIN) (fun μ => cls μ = CIN) s1 u s2).
    rewrite 2 length_app', length_app'.
    assert (length u ≠ 0) by (destruct u; [now exfalso | simpl; lia]).
    lia.
  Qed.

  (** *** The combinatorial preorder *)

  Inductive cls_pre : list A -> list A -> Prop :=
  | cp_refl s : cls_pre s s
  | cp_trans s t u : cls_pre s t -> cls_pre t u -> cls_pre s u
  | cp_delay s1 x y s2 :
    cls x = CNB -> cls_pre (s1 ++ x :: y :: s2) (s1 ++ y :: x :: s2)
  | cp_anticipate s1 x y s2 :
    cls y = CIN -> cls_pre (s1 ++ x :: y :: s2) (s1 ++ y :: x :: s2)
  (* Erasure always removes an action of class [CNB], possibly together with a
     factor that follows it: this covers both the deletion of a single
     non-blocking action and the feedback, which erases a non-blocking action
     together with one of its co-actions. *)
  | cp_erase s1 x u s2 :
    cls x = CNB -> cls_pre (s1 ++ x :: u ++ s2) (s1 ++ s2).

  Lemma cls_pre_of_tequiv s t : tequiv cls s t -> cls_pre s t.
  Proof.
    induction 1 as [ s | s t u h1 IH1 h2 IH2 | s1 μ ν s2 heq hne ].
    - constructor.
    - eapply cp_trans; eassumption.
    - destruct (cls μ) eqn:hμ.
      + eapply cp_delay. exact hμ.
      + eapply cp_anticipate. now rewrite <- heq.
      + now exfalso.
  Qed.

  Lemma cls_pre_measure s t : cls_pre s t -> tmeasure t <= tmeasure s.
  Proof.
    induction 1 as [ s | s t u h1 IH1 h2 IH2 | s1 x y s2 hx | s1 x y s2 hy | s1 x u s2 hx ].
    - reflexivity.
    - etransitivity; eassumption.
    - now eapply tmeasure_delay.
    - now eapply tmeasure_anticipate.
    - assert (hne : x :: u ≠ []) by (intro heq; discriminate heq).
      pose proof (tmeasure_erase s1 (x :: u) s2 hne) as hlt.
      replace ((x :: u) ++ s2) with (x :: u ++ s2) in hlt by reflexivity. lia.
  Qed.

  (** A step that does not decrease the measure is a swap of two consecutive
      actions of a same, non opaque, class. *)
  Lemma cls_pre_measure_tequiv s t :
    cls_pre s t -> tmeasure t = tmeasure s -> tequiv cls s t.
  Proof.
    induction 1 as [ s | s t u h1 IH1 h2 IH2 | s1 x y s2 hx | s1 x y s2 hy | s1 x u s2 hx ];
      intro hm.
    - constructor.
    - pose proof (cls_pre_measure _ _ h1). pose proof (cls_pre_measure _ _ h2).
      eapply te_trans; [eapply IH1 | eapply IH2]; lia.
    - destruct (decide (cls y = CNB)) as [ hy | hy ].
      + eapply te_swap; [now rewrite hx, hy | rewrite hx; discriminate].
      + exfalso. pose proof (tmeasure_delay_lt s1 x y s2 hx hy). lia.
    - destruct (decide (cls x = CIN)) as [ hx | hx ].
      + eapply te_swap; [now rewrite hx, hy | rewrite hx; discriminate].
      + exfalso. pose proof (tmeasure_anticipate_lt s1 x y s2 hy hx). lia.
    - exfalso.
      assert (hne : x :: u ≠ []) by (intro heq; discriminate heq).
      pose proof (tmeasure_erase s1 (x :: u) s2 hne) as hlt.
      replace ((x :: u) ++ s2) with (x :: u ++ s2) in hlt by reflexivity. lia.
  Qed.

  (** The normal form is a complete invariant of the equivalence induced by the
      preorder: it is the canonical representative of the class of a trace.
      This is Proposition 4.7 of Boreale, De Nicola and Pugliese. *)
  Theorem nform_iff_cls_pre s t :
    nform cls s = nform cls t <-> (cls_pre s t /\ cls_pre t s).
  Proof.
    split.
    - intro heq. split; eapply cls_pre_of_tequiv;
        [now eapply tequiv_of_nform | eapply tequiv_sym; now eapply tequiv_of_nform].
    - intros (h1 & h2). eapply nform_tequiv, cls_pre_measure_tequiv; [exact h1 |].
      pose proof (cls_pre_measure _ _ h1). pose proof (cls_pre_measure _ _ h2). lia.
  Qed.

  (** *** Simplified traces

      No rule of [cls_pre] applies any more, up to the reversible swaps, to a
      trace that has no action of class [CNB] and whose actions of class [CIN]
      all come first.  Erasing all the [CNB] actions and pulling the [CIN] ones
      to the front produces such a trace, [csimpl]. *)

  Definition csimpl (s : list A) : list A :=
    filter (fun μ => cls μ = CIN) s ++ filter (fun μ => cls μ = COP) s.

  Lemma csimpl_no_nb s : Forall (fun μ => cls μ ≠ CNB) (csimpl s).
  Proof.
    unfold csimpl. eapply Forall_app_2.
    - eapply (Forall_weaken (fun μ => cls μ = CIN)); [| eapply Forall_filter_self].
      intros x hx. rewrite hx. discriminate.
    - eapply (Forall_weaken (fun μ => cls μ = COP)); [| eapply Forall_filter_self].
      intros x hx. rewrite hx. discriminate.
  Qed.

  Lemma tmeasure_csimpl s : tmeasure (csimpl s) = length (csimpl s).
  Proof.
    assert (k1 : Forall (fun μ => ¬ (cls μ ≠ CIN)) (filter (fun μ => cls μ = CIN) s)).
    { eapply (Forall_weaken (fun μ => cls μ = CIN)); [| eapply Forall_filter_self].
      intros x hx. rewrite hx. intro hne. now eapply hne. }
    assert (k2 : Forall (fun μ => ¬ (cls μ = CIN)) (filter (fun μ => cls μ = COP) s)).
    { eapply (Forall_weaken (fun μ => cls μ = COP)); [| eapply Forall_filter_self].
      intros x hx. rewrite hx. discriminate. }
    assert (h1 : inv_nb (csimpl s) = 0).
    { unfold inv_nb. eapply inv_cnt_0_l. exact (csimpl_no_nb s). }
    assert (h2 : inv_in (csimpl s) = 0).
    { unfold inv_in, csimpl. rewrite inv_cnt_app.
      rewrite (inv_cnt_0_l _ _ _ k1), (inv_cnt_0_r _ _ _ k2), (length_filter_0 _ _ k1).
      lia. }
    unfold tmeasure. lia.
  Qed.

  (** No rule can erase or permute anything in a trace without [CNB] actions,
      except the reversible swaps. *)
  Lemma cls_pre_no_nb u t : cls_pre u t ->
    Forall (fun μ => cls μ ≠ CNB) u ->
    Forall (fun μ => cls μ ≠ CNB) t /\ length t = length u.
  Proof.
    induction 1
      as [ s | s t v h1 IH1 h2 IH2 | s1 x y s2 hx | s1 x y s2 hy | s1 x u' s2 hx ];
      intro hu.
    - split; [exact hu | reflexivity].
    - destruct (IH1 hu) as (hv1 & l1). destruct (IH2 hv1) as (hv2 & l2).
      split; [exact hv2 | lia].
    - exfalso. eapply Forall_app_inv in hu as (_ & hu2).
      eapply Forall_cons_1 in hu2 as (hx' & _). exact (hx' hx).
    - assert (hp : (s1 ++ x :: y :: s2) ≡ₚ (s1 ++ y :: x :: s2))
        by (eapply Permutation_app_head; constructor).
      split.
      + eapply (Permutation_Forall hp). exact hu.
      + eapply Permutation_length. now symmetry.
    - exfalso. eapply Forall_app_inv in hu as (_ & hu2).
      eapply Forall_cons_1 in hu2 as (hx' & _). exact (hx' hx).
  Qed.

  (** A trace is *simplified* when nothing below it in the preorder is
      strictly smaller. *)
  Definition cls_min (u : list A) : Prop :=
    forall t, cls_pre u t -> tmeasure t = tmeasure u.

  Lemma cls_min_of_no_nb u :
    Forall (fun μ => cls μ ≠ CNB) u -> tmeasure u = length u -> cls_min u.
  Proof.
    intros hu hm t hpre.
    destruct (cls_pre_no_nb u t hpre hu) as (_ & hl).
    pose proof (cls_pre_measure _ _ hpre) as hle.
    unfold tmeasure in *. lia.
  Qed.

  Lemma csimpl_filter_no_nb s :
    csimpl (filter (fun μ => cls μ ≠ CNB) s) = csimpl s.
  Proof.
    unfold csimpl. f_equal; eapply filter_filter_eq.
    - intros x hx. rewrite hx. discriminate.
    - intros x hx. rewrite hx. discriminate.
  Qed.

  Corollary cls_min_csimpl s : cls_min (csimpl s).
  Proof. eapply cls_min_of_no_nb; [eapply csimpl_no_nb | eapply tmeasure_csimpl]. Qed.

  (** *** Sorted traces

      Without the deletion law, nothing is ever erased and the least traces are
      the *sorted* ones: the actions of class [CIN] first, then the opaque
      ones, then the non-blocking ones.  Such a trace is a permutation of the
      original one, and it carries no feedback at all, since a feedback needs a
      [CNB] action *before* a [CIN] one. *)

  Definition tsort (s : list A) : list A :=
    filter (fun μ => cls μ = CIN) s ++ filter (fun μ => cls μ = COP) s
      ++ filter (fun μ => cls μ = CNB) s.

  Lemma perm_middle2 (l1 l2 : list A) (x : A) : l1 ++ x :: l2 ≡ₚ x :: (l1 ++ l2).
  Proof. symmetry. eapply Permutation_middle. Qed.

  Lemma perm_middle3 (l1 l2 l3 : list A) (x : A) :
    l1 ++ l2 ++ x :: l3 ≡ₚ x :: (l1 ++ l2 ++ l3).
  Proof. rewrite app_assoc, perm_middle2, <- app_assoc. reflexivity. Qed.

  Lemma tsort_perm s : tsort s ≡ₚ s.
  Proof.
    induction s as [| x s IH]; [reflexivity |]. unfold tsort in *.
    destruct (cls x) eqn:e.
    - rewrite (filter_cons_False (fun ν => cls ν = CIN) x s) by (rewrite e; discriminate).
      rewrite (filter_cons_False (fun ν => cls ν = COP) x s) by (rewrite e; discriminate).
      rewrite (filter_cons_True (fun ν => cls ν = CNB) x s e).
      rewrite perm_middle3, IH. reflexivity.
    - rewrite (filter_cons_True (fun ν => cls ν = CIN) x s e).
      rewrite (filter_cons_False (fun ν => cls ν = COP) x s) by (rewrite e; discriminate).
      rewrite (filter_cons_False (fun ν => cls ν = CNB) x s) by (rewrite e; discriminate).
      rewrite <- app_comm_cons, IH. reflexivity.
    - rewrite (filter_cons_False (fun ν => cls ν = CIN) x s) by (rewrite e; discriminate).
      rewrite (filter_cons_True (fun ν => cls ν = COP) x s e).
      rewrite (filter_cons_False (fun ν => cls ν = CNB) x s) by (rewrite e; discriminate).
      rewrite <- app_comm_cons, perm_middle2, IH. reflexivity.
  Qed.

  Corollary length_tsort s : length (tsort s) = length s.
  Proof. eapply Permutation_length, tsort_perm. Qed.

  Lemma tmeasure_ge_length u : length u <= tmeasure u.
  Proof. unfold tmeasure. lia. Qed.

  Lemma tmeasure_tsort s : tmeasure (tsort s) = length (tsort s).
  Proof.
    assert (hcin : Forall (fun μ => cls μ = CIN) (filter (fun μ => cls μ = CIN) s))
      by eapply Forall_filter_self.
    assert (hcop : Forall (fun μ => cls μ = COP) (filter (fun μ => cls μ = COP) s))
      by eapply Forall_filter_self.
    assert (hcnb : Forall (fun μ => cls μ = CNB) (filter (fun μ => cls μ = CNB) s))
      by eapply Forall_filter_self.
    (* the negated forms that the counting lemmas expect *)
    assert (n1 : Forall (fun μ => ¬ (cls μ = CNB)) (filter (fun μ => cls μ = CIN) s)).
    { eapply (Forall_weaken (fun μ => cls μ = CIN)); [| exact hcin]. intros x hx. rewrite hx. discriminate. }
    assert (n2 : Forall (fun μ => ¬ (cls μ = CNB)) (filter (fun μ => cls μ = COP) s)).
    { eapply (Forall_weaken (fun μ => cls μ = COP)); [| exact hcop]. intros x hx. rewrite hx. discriminate. }
    assert (n3 : Forall (fun μ => ¬ (cls μ ≠ CNB)) (filter (fun μ => cls μ = CNB) s)).
    { eapply (Forall_weaken (fun μ => cls μ = CNB)); [| exact hcnb]. intros x hx. rewrite hx.
      intro hne. now eapply hne. }
    assert (m1 : Forall (fun μ => ¬ (cls μ ≠ CIN)) (filter (fun μ => cls μ = CIN) s)).
    { eapply (Forall_weaken (fun μ => cls μ = CIN)); [| exact hcin]. intros x hx. rewrite hx.
      intro hne. now eapply hne. }
    assert (m2 : Forall (fun μ => ¬ (cls μ = CIN)) (filter (fun μ => cls μ = COP) s)).
    { eapply (Forall_weaken (fun μ => cls μ = COP)); [| exact hcop]. intros x hx. rewrite hx. discriminate. }
    assert (m3 : Forall (fun μ => ¬ (cls μ = CIN)) (filter (fun μ => cls μ = CNB) s)).
    { eapply (Forall_weaken (fun μ => cls μ = CNB)); [| exact hcnb]. intros x hx. rewrite hx. discriminate. }
    assert (h1 : inv_nb (tsort s) = 0).
    { unfold inv_nb, tsort. rewrite 2 inv_cnt_app.
      rewrite (inv_cnt_0_l _ _ _ n1), (inv_cnt_0_l _ _ _ n2), (inv_cnt_0_r _ _ _ n3).
      rewrite (length_filter_0 _ _ n1), (length_filter_0 _ _ n2). lia. }
    assert (h2 : inv_in (tsort s) = 0).
    { unfold inv_in, tsort. rewrite 2 inv_cnt_app.
      rewrite (inv_cnt_0_l _ _ _ m1), (inv_cnt_0_r _ _ _ m2), (inv_cnt_0_r _ _ _ m3).
      rewrite (length_filter_0 _ _ m1), (length_filter_0 _ _ m3). lia. }
    unfold tmeasure. lia.
  Qed.

  (** The measure is constant on the class of a trace. *)
  Corollary tmeasure_nform s : tmeasure (nlin (nform cls s)) = tmeasure s.
  Proof.
    assert (h1 : cls_pre s (nlin (nform cls s)))
      by (eapply cls_pre_of_tequiv, tequiv_nform).
    assert (h2 : cls_pre (nlin (nform cls s)) s)
      by (eapply cls_pre_of_tequiv, tequiv_sym, tequiv_nform).
    pose proof (cls_pre_measure _ _ h1). pose proof (cls_pre_measure _ _ h2). lia.
  Qed.

End Measure.

Arguments inv_nb {A} cls s.
Arguments inv_in {A} cls s.
Arguments tmeasure {A} cls s.
Arguments cls_pre {A} cls s t.
Arguments csimpl {A} cls s.
Arguments cls_min {A} cls u.
Arguments tsort {A} cls s.

Arguments ncons {A _} cls μ σ.
Arguments nform {A _} cls s.
Arguments nlin {A _} σ.
Arguments block_wf {A _} cls b.
Arguments nf_wf {A _} cls σ.
Arguments tequiv {A} cls s t.

(** * Two classifiers that split the actions the same way

    [nform] only ever compares the class of an action with the class of the
    block it may join, and refuses to merge [COP]: it depends on the classifier
    only through the *partition* it induces, and through which part is [COP].
    Two classifiers agreeing on those two things -- even if they permute the
    names [CNB] and [CIN] -- therefore produce the same blocks, hence the same
    normalised trace. *)

Section SameShape.

  Context `{H : !ExtAction A}.
  Variables cls cls' : A -> act_class.
  Hypothesis hcop : forall x, cls x = COP <-> cls' x = COP.
  Hypothesis hpart : forall x y, cls x = cls y <-> cls' x = cls' y.

  Lemma ncons_same_shape (μ : A) (σ σ' : ntrace A) :
    nf_wf cls σ -> nf_wf cls' σ' -> map snd σ = map snd σ' ->
    map snd (ncons cls μ σ) = map snd (ncons cls' μ σ').
  Proof.
    intros hw hw' hs.
    destruct σ as [| (c, M) σ0]; destruct σ' as [| (c', M') σ0'];
      simpl in hs; try discriminate; simpl.
    - reflexivity.
    - injection hs as hM hs0. subst M'.
      inversion hw as [| b0 t0 hb hrest]; subst.
      inversion hw' as [| b0' t0' hb' hrest']; subst.
      destruct hb as (hne & hall). destruct hb' as (hne' & hall').
      destruct (gmultiset_choose M hne) as (x & hx).
      assert (ec : cls x = c) by (eapply hall; exact hx).
      assert (ec' : cls' x = c') by (eapply hall'; exact hx).
      destruct (decide (cls μ = c /\ cls μ ≠ COP)) as [(e1 & e2) | hn];
        destruct (decide (cls' μ = c' /\ cls' μ ≠ COP)) as [(f1 & f2) | fn]; simpl.
      + now rewrite hs0.
      + exfalso. eapply fn. split.
        * rewrite <- ec'. eapply hpart. rewrite ec. exact e1.
        * intro k. eapply e2. eapply hcop. exact k.
      + exfalso. eapply hn. split.
        * rewrite <- ec. eapply hpart. rewrite ec'. exact f1.
        * intro k. eapply f2. eapply hcop. exact k.
      + now rewrite hs0.
  Qed.

  Lemma nform_same_shape s : map snd (nform cls s) = map snd (nform cls' s).
  Proof.
    induction s as [| μ s IH]; simpl; [reflexivity |].
    eapply ncons_same_shape; [eapply nf_wf_nform | eapply nf_wf_nform | exact IH].
  Qed.

  Lemma nlin_shape (σ σ' : ntrace A) : map snd σ = map snd σ' -> nlin σ = nlin σ'.
  Proof.
    revert σ'. induction σ as [| (c, M) σ IH]; intros [| (c', M') σ'] hs;
      simpl in hs; try discriminate; simpl; [reflexivity |].
    injection hs as -> hs0. rewrite (IH σ' hs0). reflexivity.
  Qed.

  Theorem nlin_nform_same s : nlin (nform cls s) = nlin (nform cls' s).
  Proof. eapply nlin_shape, nform_same_shape. Qed.

End SameShape.
