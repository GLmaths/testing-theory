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

From Stdlib Require ssreflect Setoid.
From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From Stdlib.Wellfounded Require Import Inverse_Image.

From Stdlib.Program Require Import Wf Equality.
From stdpp Require Import base list countable decidable finite gmap gmultiset.
From TestingTheory Require Import MultisetHelper ActTau gLts Bisimulation FiniteImageLTS Lts_OBA Lts_FW Lts_OBA_FB 
    InListPropHelper.

(**************************************** LTS of Sets *************************************)


Lemma exists_forall_in {B} (ps : list B) (P : B -> Prop) (Q : B -> Prop)
  (h : forall p, p ∈ ps -> P p \/ Q p) : Exists P ps \/ Forall Q ps.
Proof.
  induction ps as [|p ?]. eauto.
  destruct IHps; destruct (h p); eauto; set_solver.
Qed.

Lemma exists_forall_in_gset `{Countable A} (ps : gset A) (P : A -> Prop) (Q : A -> Prop)
  (h : forall p, p ∈ ps -> P p \/ Q p) : (exists p, p ∈ ps /\ P p)\/ (forall p, p ∈ ps -> Q p).
Proof.
  induction ps using set_ind_L. set_solver.
  destruct IHps; destruct (h x); eauto; set_solver.
Qed.

Definition all_blocking_action_ext `{!ExtAction A} (μ : A) := False.

#[global] Program Instance all_blocking_action_dec `{!ExtAction A} μ :
    Decision (all_blocking_action_ext μ).
Next Obligation.
  intros. right. intro imp. inversion imp.
Defined.

(* #[global] Program Instance ExtAction_Blocking `{!ExtAction A} : ExtAction A:=
   {| non_blocking η := all_blocking_action_ext η ;
      dual μ1 μ2 := dual μ1 μ2 |}.
Next Obligation.
  intros ? ? ? ? nb ; simpl in *. inversion nb.
Defined.
Next Obligation.
 intros A H μ; simpl in *.
 intros μ' duo. eapply unique_nb in duo. subst.
 symmetry. exact (proj2_sig (exists_dual μ)).
Defined.
Next Obligation.
  intros. exists (proj1_sig (exists_dual μ)).
  exact (proj2_sig (exists_dual μ)).
Defined.
Next Obligation.
  intros. unfold ExtAction_Blocking_obligation_3.
  simpl in *. eapply unique_nb. eauto.
Defined. *)

#[global] Program Instance SET_LTS `(gLtsP : @gLts P A H) `{!FiniteImagegLts P A} : @gLts (gset P) A H. (* ExtAction_Blocking *)
Next Obligation.
  intros. destruct X.
  + exact (H1 = lts_extaction_set_from_pset H0 μ /\ H1 ≠ ∅).
  + exact (H1 = lts_tau_set_from_pset H0 /\ H1 ≠ ∅).
Defined.
Next Obligation.
  intros; simpl in *. unfold SET_LTS_obligation_1.
  destruct α.
  - destruct (decide (b = lts_extaction_set_from_pset a μ /\ b ≠ ∅)).
    + left. eauto.
    + right. eauto.
  - destruct (decide (b = lts_tau_set_from_pset a /\ b ≠ ∅)).
    + left. eauto.
    + right. eauto.
Qed.
Next Obligation.
  intros. exact (forall p, p ∈ H0 -> lts_refuses p X).
Defined.
Next Obligation.
  intros. simpl in *. unfold SET_LTS_obligation_3.
  destruct α.
  - assert (forall p', p' ∈ p -> (¬ lts_refuses p' (ActExt μ) \/ lts_refuses p' (ActExt μ))) as Hyp.
    { intros. destruct (decide (p' ↛[μ])); [right|left];eauto. }
    (* destruct (exists_forall_in_gset p _ _ Hyp). *) admit.
  - assert (forall p', p' ∈ p -> (¬ lts_refuses p' τ \/ lts_refuses p' τ)) as Hyp.
    { intros. destruct (decide (p' ↛)); [right|left];eauto. }
    (* destruct (exists_forall_in_gset p _ _ Hyp). *) admit.
Admitted.
Next Obligation.
  unfold SET_LTS_obligation_3.
  unfold SET_LTS_obligation_1. intros. destruct α.
  - assert (forall p', p' ∈ p -> (¬ lts_refuses p' (ActExt μ) \/ lts_refuses p' (ActExt μ))) as Hyp.
    { intros. destruct (decide (p' ↛[μ])); [right|left];eauto. }
    exists (lts_extaction_set_from_pset p μ). split; eauto.
    destruct (exists_forall_in_gset p _ _ Hyp).
    + destruct H1 as (p' & Hyp' & Hyp'').
      intro. eapply lts_refuses_spec1 in Hyp'' as (p'' & Hyp''').
      assert (p'' ∈ lts_extaction_set_from_pset p μ).
      { destruct (lts_extaction_set_from_pset_ispec p μ). eauto. }
      rewrite H1 in H2. inversion H2.
    + contradiction.
  - assert (forall p', p' ∈ p -> (¬ lts_refuses p' τ \/ lts_refuses p' τ)) as Hyp.
    { intros. destruct (decide (p' ↛)); [right|left];eauto. }
    exists (lts_tau_set_from_pset p). split; eauto.
    destruct (exists_forall_in_gset p _ _ Hyp).
    + destruct H1 as (p' & Hyp' & Hyp'').
      intro. eapply lts_refuses_spec1 in Hyp'' as (p'' & Hyp''').
      assert (p'' ∈ lts_tau_set_from_pset p).
      { destruct (lts_tau_set_from_pset_ispec p). eauto. }
      rewrite H1 in H2. inversion H2.
    + contradiction.
Qed.
Next Obligation.
  unfold SET_LTS_obligation_3.
  unfold SET_LTS_obligation_1. intros.
  destruct α.
  - intro. destruct H0 as (p' & Hyp1 & Hyp2). subst.
    remember (lts_extaction_set_from_pset p μ).
    induction g using set_ind_L.
    + eapply Hyp2. reflexivity.
    + assert (x ∈ lts_extaction_set_from_pset p μ) as Hyp by set_solver.
      destruct (lts_extaction_set_from_pset_ispec p μ) as (Hyp'1 & Hyp'2).
      unfold lts_extaction_set_from_pset_spec1 in Hyp'1.
      unfold lts_extaction_set_from_pset_spec2 in Hyp'2.
      eapply Hyp'1 in Hyp as (p'0 & in_Set & Tr).
      eapply H1 in in_Set. eapply lts_refuses_spec2; eauto.
  - intro. destruct H0 as (p' & Hyp1 & Hyp2). subst.
    remember (lts_tau_set_from_pset p).
    induction g using set_ind_L.
    + eapply Hyp2. reflexivity.
    + assert (x ∈ lts_tau_set_from_pset p) as Hyp by set_solver.
      destruct (lts_tau_set_from_pset_ispec p) as (Hyp'1 & Hyp'2).
      unfold lts_tau_set_from_pset_spec1 in Hyp'1.
      unfold lts_tau_set_from_pset_spec2 in Hyp'2.
      eapply Hyp'1 in Hyp as (p'0 & in_Set & Tr).
      eapply H1 in in_Set. eapply lts_refuses_spec2 ; eauto.
Qed.


(************** Properties of toSet(L) ***************)

Lemma empty_refuses_all_action `{gLts P A} `{!FiniteImagegLts P A} α : (∅ : gset P) ↛{α}.
Proof.
  intros p Imp. inversion Imp.
Qed.

Definition eq_rel_set `{gLtsEq P A} `{!FiniteImagegLts P A} (X Y : gset P) :=
 (forall x, x ∈ X -> exists y, y ∈ Y ∧ eq_rel x y) ∧
 (forall y, y ∈ Y -> exists x, x ∈ X ∧ eq_rel y x).

Infix "⋍ₛₑₜ" := eq_rel_set (at level 70).

Global Instance symmetric_eq_rel_set `{gLtsEq P A} `{!FiniteImagegLts P A}:
 Symmetric eq_rel_set.
Proof. intros x y. unfold eq_rel_set. intuition. Qed.

Global Instance reflexive_eq_rel_set `{gLtsEq P A} `{!FiniteImagegLts P A}:
 Reflexive eq_rel_set.
Proof. intro X; split; intros x Hx; exists x; intuition. reflexivity. reflexivity. Qed.

Global Instance transitive_eq_rel_set `{gLtsEq P A} `{!FiniteImagegLts P A}:
 Transitive eq_rel_set.
Proof. intros X Y Z eq1 eq2. split; intros x Hx.
  + eapply eq1 in Hx as (y' & mem & eq).
    eapply eq2 in mem as (z'' & mem'' & eq'').
    exists z''. split. eauto. etrans; eauto.
  + eapply eq2 in Hx as (y' & mem & eq).
    eapply eq1 in mem as (z'' & mem'' & eq'').
    exists z''. split. eauto. etrans; eauto.
Qed.

Global Instance equivalence_eq_rel_set `{gLtsEq P A} `{!FiniteImagegLts P A}:
 Equivalence eq_rel_set.
Proof.
  split.
  + exact reflexive_eq_rel_set.
  + exact symmetric_eq_rel_set.
  + exact transitive_eq_rel_set.
Qed.

Global Instance equiv_eq_rel_set `{gLtsEq P A} `{!FiniteImagegLts P A}:
 Proper ((≡) ==> (≡) ==> (impl)) eq_rel_set.
Proof.
intros X X' HX Y Y' HY Heq. split; intros x Hx.
- apply HX, Heq in Hx as (y & Hy & Heq'). apply HY in Hy. eauto.
- apply HY, Heq in Hx as (y & Hy & Heq'). apply HX in Hy. eauto.
Qed.

Global Instance proper_singleton_elem_eq_rel_set
  `{gLtsEq P A} `{!FiniteImagegLts P A}:
  Proper ((eq_rel) ==> (eq_rel_set)) singleton.
Proof.
  intros x y Hx. split; intros x' Hx'%elem_of_singleton;
  subst x'; [exists y|exists x]; split; eauto; try apply elem_of_singleton; trivial.
  now symmetry.
Qed.

Lemma inv_eq_empty `{gLtsEq P A} `{!FiniteImagegLts P A} Y : ∅ ⋍ₛₑₜ Y -> Y = ∅.
Proof.
  intros (Hyp1 & Hyp2).
  destruct Y using set_ind_L.
  + reflexivity.
  + assert (x ∈ {[x]} ∪ X) as Imp by set_solver.
    eapply (Hyp2 x) in Imp as (x' & mem & eq).
    inversion mem.
Qed.

Lemma inv_eq_non_empty `{gLtsEq P A} `{!FiniteImagegLts P A} X Y : X ≠ ∅ -> X ⋍ₛₑₜ Y -> Y ≠ ∅.
Proof.
  intros non_empty equiv.
  intro Imp. subst. symmetry in equiv.
  eapply inv_eq_empty in equiv. subst. eauto.
Qed.

Lemma ext_action_equiv_set `{gLtsEq P A} `{!FiniteImagegLts P A} X μ Y :
  X ⋍ₛₑₜ Y -> lts_extaction_set_from_pset X μ ⋍ₛₑₜ lts_extaction_set_from_pset Y μ.
Proof.
  intros equiv.
  destruct X using set_ind_L.
  + eapply inv_eq_empty in equiv. subst. reflexivity.
  + split.
    - intros p' hyp. destruct (lts_extaction_set_from_pset_ispec ({[x]} ∪ X) μ) as (spec1 & spec2).
      eapply spec1 in hyp as (p & mem & tr). destruct equiv as (Hyp_equiv1 & Hyp_equiv2).
      eapply Hyp_equiv1 in mem as (q & mem' & equiv'). edestruct (eq_spec q p') as (q' & tr'' & equiv'').
      exists p; split; eauto. symmetry. eauto. exists q'. split.
      * simpl. unfold lts_extaction_set_from_pset. eapply elem_of_union_list.
        exists (list_to_set (lts_extaction_set q μ)). split.
        ++ apply list_elem_of_fmap. exists q. split; eauto. eapply elem_of_elements. eauto.
        ++ simpl. eapply elem_of_list_to_set.
           eapply lts_extaction_set_spec. exact tr''.
      * symmetry. exact equiv''.
    - intros p' hyp. destruct (lts_extaction_set_from_pset_ispec Y μ) as (spec1 & spec2).
      eapply spec1 in hyp as (p & mem & tr). destruct equiv as (Hyp_equiv1 & Hyp_equiv2).
      eapply Hyp_equiv2 in mem as (q & mem' & equiv'). edestruct (eq_spec q p') as (q' & tr'' & equiv'').
      exists p; split; eauto. symmetry. eauto. exists q'. split.
      * simpl. unfold lts_extaction_set_from_pset. eapply elem_of_union_list.
        exists (list_to_set (lts_extaction_set q μ)). split.
        ++ apply list_elem_of_fmap. exists q. split; eauto. eapply elem_of_elements. eauto.
        ++ simpl. eapply elem_of_list_to_set.
           eapply lts_extaction_set_spec. exact tr''.
      * symmetry. exact equiv''.
Qed.

Lemma tau_action_equiv_set `{gLtsEq P A} `{!FiniteImagegLts P A} X Y :
  X ⋍ₛₑₜ Y -> lts_tau_set_from_pset X ⋍ₛₑₜ lts_tau_set_from_pset Y.
Proof.
  intros equiv.
  destruct X using set_ind_L.
  + eapply inv_eq_empty in equiv. subst. reflexivity.
  + split.
    - intros p' hyp. destruct (lts_tau_set_from_pset_ispec ({[x]} ∪ X)) as (spec1 & spec2).
      eapply spec1 in hyp as (p & mem & tr). destruct equiv as (Hyp_equiv1 & Hyp_equiv2).
      eapply Hyp_equiv1 in mem as (q & mem' & equiv'). edestruct (eq_spec q p') as (q' & tr'' & equiv'').
      exists p; split; eauto. symmetry. eauto. exists q'. split.
      * simpl. unfold lts_tau_set_from_pset. eapply elem_of_union_list.
        exists (list_to_set (lts_tau_set q)). split.
        ++ apply list_elem_of_fmap. exists q. split; eauto. eapply elem_of_elements. eauto.
        ++ simpl. eapply elem_of_list_to_set.
           eapply lts_tau_set_spec. exact tr''.
      * symmetry. exact equiv''.
    - intros p' hyp. destruct (lts_tau_set_from_pset_ispec Y) as (spec1 & spec2).
      eapply spec1 in hyp as (p & mem & tr). destruct equiv as (Hyp_equiv1 & Hyp_equiv2).
      eapply Hyp_equiv2 in mem as (q & mem' & equiv'). edestruct (eq_spec q p') as (q' & tr'' & equiv'').
      exists p; split; eauto. symmetry. eauto. exists q'. split.
      * simpl. unfold lts_tau_set_from_pset. eapply elem_of_union_list.
        exists (list_to_set (lts_tau_set q)). split.
        ++ apply list_elem_of_fmap. exists q. split; eauto. eapply elem_of_elements. eauto.
        ++ simpl. eapply elem_of_list_to_set.
           eapply lts_tau_set_spec. exact tr''.
      * symmetry. exact equiv''.
Qed.

Lemma simulation_eq_set_rel `{gLtsEq P A} `{!FiniteImagegLts P A} X Y α Z :
  X ⋍ₛₑₜ Y ∧ Y ⟶{α} Z → ∃ Y', X  ⟶{α} Y' ∧ Y' ⋍ₛₑₜ Z.
Proof.
  intros (eq & tr).
  destruct α.
  + destruct tr as (ext_action_set & non_empty). subst.
    exists (lts_extaction_set_from_pset X μ).
    split.
    - split.
      * eauto.
      * eapply (ext_action_equiv_set X μ) in eq. intro Imp.
        rewrite Imp in eq. eapply inv_eq_empty in eq. eauto.
    - eapply ext_action_equiv_set; eauto.
  + destruct tr as (tau_set & non_empty). subst.
    exists (lts_tau_set_from_pset X).
    split.
    - split.
      * eauto.
      * eapply (tau_action_equiv_set X) in eq. intro Imp.
        rewrite Imp in eq. eapply inv_eq_empty in eq. eauto.
    - eapply tau_action_equiv_set; eauto.
Qed.

#[global] Program Instance SET_LTS_eq `(gLtsEqP : @gLtsEq P A H) `{!FiniteImagegLts P A} : @gLtsEq (gset P) A H:=
  {| eq_rel := eq_rel_set |}.
Next Obligation.
  intros ? ? ? ? ? ? ? ? (Z & Hyp). eapply simulation_eq_set_rel;eauto.
Qed.

(* Set of a LTS respects OBA axioms , because empty set = non_blocking_action *)

#[global] Program Instance SET_LTS_gLtsOba `(gLtsEqP : @gLtsEq P A H) `{!FiniteImagegLts P A} 
  {ext_prop : forall μ, non_blocking μ -> all_blocking_action_ext μ} : @gLtsOba (gset P) A H (SET_LTS_eq gLtsEqP):=
  {| lts_oba_mo p := empty |}.
Next Obligation.
  intros ? ? ? ? ? ? ? ? ? nb. eapply ext_prop in nb. inversion nb.
Qed.
Next Obligation.
  intros ? ? ? ? ? ? ? ? mem. simpl in *. exists ∅. set_solver.
Qed.
Next Obligation.
  intros ? ? ? ? ? ? ? ? ? nb. eapply ext_prop in nb. inversion nb.
Qed.
Next Obligation.
  intros ? ? ? ? ? ? ? ? ? ? ? nb. eapply ext_prop in nb. inversion nb.
Qed.
Next Obligation.
  intros ? ? ? ? ? ? ? ? ? ? ? nb. eapply ext_prop in nb. inversion nb.
Qed.
Next Obligation.
  intros ? ? ? ? ? ? ? ? ? ? nb. eapply ext_prop in nb. inversion nb.
Qed.
Next Obligation.
  intros ? ? ? ? ? ? ? ? ? ? nb. eapply ext_prop in nb. inversion nb.
Qed.
Next Obligation.
  intros ? ? ? ? ? ? ? ? ? ? ? nb. eapply ext_prop in nb. inversion nb.
Qed.

(* Set of a LTS respects FB axioms , because empty set = non_blocking_action *)

#[global] Program Instance SET_LTS_gLtsObaFB `(gLtsEqP : @gLtsEq P A H) `{!FiniteImagegLts P A} 
  {ext_prop : forall μ, non_blocking μ -> all_blocking_action_ext μ} 
  : @gLtsObaFB (gset P) A H (SET_LTS_eq gLtsEqP) (@SET_LTS_gLtsOba P A H gLtsEqP _ ext_prop ). 
Next Obligation.
  intros ? ? ? ? ? ? ? ? ? ? ? nb. eapply ext_prop in nb. inversion nb.
Qed.

(* Set of a LTS respects FW axioms , because empty set = non_blocking_action *)

#[global] Program Instance SET_LTS_gLtsObaFW `(gLtsEqP : @gLtsEq P A H) `{!FiniteImagegLts P A} 
  {ext_prop : forall μ, non_blocking μ -> all_blocking_action_ext μ} 
  : @gLtsObaFW (gset P) A H (SET_LTS_eq gLtsEqP) (@SET_LTS_gLtsOba P A H gLtsEqP _ ext_prop ). 
Next Obligation.
  intros ? ? ? ? ? ? ? ? ?. exists empty. intro nb. eapply ext_prop in nb. inversion nb.
Qed.
Next Obligation.
  intros ? ? ? ? ? ? ? ? ? ? ? nb. eapply ext_prop in nb. inversion nb.
Qed.

(********************************** toSet is a Finite Image LTS ************************)

#[global] Program Instance gLtsMBFinite `{@FiniteImagegLts P A H gLtsP}
  : @FiniteImagegLts (gset P) A H (SET_LTS gLtsP).
Next Obligation. 
  intros ? ? ? ? ? X α.
  destruct α as [μ | ].
  + simpl. eapply (in_list_finite ([lts_extaction_set_from_pset X μ])).
    intros P' h%bool_decide_unpack. destruct h as (eq & not_empty). subst.
    set_solver.
  + simpl. eapply (in_list_finite ([lts_tau_set_from_pset X])).
    intros P' h%bool_decide_unpack. destruct h as (eq & not_empty). subst.
    set_solver.
Qed.


(******************************* toSet construction ************************************)

