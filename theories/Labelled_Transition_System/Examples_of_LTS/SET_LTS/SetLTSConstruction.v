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
From Stdlib.Strings Require Import String.
From Stdlib Require Import Relations.

From stdpp Require Import base countable finite gmap list gmultiset strings.

From Stdlib.Program Require Import Wf Equality.
From stdpp Require Import base list countable decidable finite gmap gmultiset.
From TestingTheory Require Import MultisetHelper ActTau gLts Bisimulation FiniteImageLTS Lts_OBA Lts_FW Lts_OBA_FB 
    InListPropHelper Lts_Finite_Output_Chain InFiniteSetHelper WeakTransitions.

(**************************************** LTS of Sets *************************************)

Definition all_blocking_action_ext `{!ExtAction A} (μ : A) := False.

#[global] Program Instance all_blocking_action_dec `{!ExtAction A} μ :
    Decision (all_blocking_action_ext μ).
Next Obligation.
  intros. right. intro imp. inversion imp.
Defined.

(* Program Instance ExtAction_Blocking {A : Type} (H : ExtAction A) : ExtAction A:=
   {| non_blocking η := all_blocking_action_ext η ;
      dual μ1 μ2 := dual μ1 μ2;
      duo_sym :=duo_sym ;
      exists_dual μ := exists_dual μ;
      unique_nb η β := unique_nb η β;|}.
Next Obligation.
  intros ? ? ? ? nb ; simpl in *. inversion nb.
Defined. *)

#[global] Program Instance SET_LTS `(gLtsP : !@gLts P A H)`{FiniteP : !@FiniteImagegLts P A H gLtsP} : 
  gLts (gset P) H.
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
  pose proof (decide (∃ x, x ∈ p ∧ ¬ x ↛{α})) as Hdec.
  destruct Hdec as [Hex | Hnot].
  + right. intro. destruct Hex as (p' & mem & tr).
    eapply H0 in mem. contradiction.
  + left. intros. destruct (decide (p0 ↛{α})).
    - eauto.
    - assert (∃ x : P, x ∈ p ∧ ¬ x ↛{α}).
      { exists p0. split ;eauto. }
      contradiction.
Qed.
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

Global Instance reflexive_eq_rel_set `{gLtsEq P A} `{!FiniteImagegLts P A}:
 Reflexive eq_rel_set.
Proof. intro X; split; intros x Hx; exists x; intuition. reflexivity. reflexivity. Qed.

Global Instance symmetric_eq_rel_set `{gLtsEq P A} `{!FiniteImagegLts P A}:
 Symmetric eq_rel_set.
Proof. intros x y. unfold eq_rel_set. intuition. Qed.

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
  {ext_prop : forall μ, non_blocking μ -> all_blocking_action_ext μ} : @gLtsOba (gset P) A H (SET_LTS_eq gLtsEqP).
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

(* Set of a LTS respects FiniteOuputChain axioms , because empty set = non_blocking_action *)

#[global] Program Instance SET_LTS_FiniteOutputChain `(gLtsEqP : @gLtsEq P A H) `{!FiniteImagegLts P A} 
  {ext_prop : forall μ, non_blocking μ -> all_blocking_action_ext μ} : @FiniteOutputChain_LtsOba (gset P) A H (SET_LTS_eq gLtsEqP) (@SET_LTS_gLtsOba P A H gLtsEqP _ ext_prop ):=
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

(******************************* toSet Properties ************************************)

From TestingTheory Require Import Termination.

Lemma tau_set_determinacy `{gLtsP : @gLts P A H} `{!FiniteImagegLts P A} X Y :
  X ⟶ Y -> Y = lts_tau_set_from_pset X.
Proof.
  intro tr. destruct tr; eauto.
Qed.

Lemma ext_action_set_determinacy `{gLtsP : @gLts P A H} `{!FiniteImagegLts P A} X μ Y :
  X ⟶[μ] Y -> Y = lts_extaction_set_from_pset X μ.
Proof.
  intro tr. destruct tr; eauto.
Qed.

Lemma empty_set_termination `{gLtsP : @gLts P A H} `{!FiniteImagegLts P A} : ∅ ⤓.
Proof.
  constructor. intros X tr.
  destruct tr as (eq & not_empty).
  subst. unfold lts_tau_set_from_pset in not_empty.
  rewrite elements_empty in not_empty. simpl in *.
  exfalso. set_solver.
Qed.

Lemma empty_set_stable `{gLtsP : @gLts P A H} `{!FiniteImagegLts P A} α : ∅ ↛{ α }.
Proof.
  destruct α.
  + intro. intro Imp. inversion Imp.
  + intro. intro Imp. inversion Imp.
Qed.

Lemma empty_set_stable_wk `{gLtsP : @gLts P A H} `{!FiniteImagegLts P A} s ps : ps ≠ ∅ -> ¬ ∅ ⟹[s] ps.
Proof.
  intros not_empty imp. inversion imp; subst.
  + set_solver.
  + eapply (@lts_refuses_spec2 (gset P));eauto. eapply empty_set_stable.
  + eapply (@lts_refuses_spec2 (gset P));eauto. eapply empty_set_stable.
Qed.

Lemma empty_set_stable_wk_inv `{gLtsP : @gLts P A H} `{!FiniteImagegLts P A} s ps ps' : ps' = ∅ -> ps ⟹[s] ps' -> ps = ∅.
Proof.
  intros eq_empty wk_tr. revert eq_empty. dependent induction wk_tr.
  + eauto.
  + intro. eapply IHwk_tr in eq_empty. subst.
    inversion l; eauto. set_solver.
  + intro. eapply IHwk_tr in eq_empty. subst.
    inversion l; eauto. set_solver.
Qed.

Lemma empty_set_stable_wk_inv_nil `{gLtsP : @gLts P A H} `{!FiniteImagegLts P A} s ps : ps ⟹[s] ∅ -> ps = ∅.
Proof.
  eapply empty_set_stable_wk_inv; eauto.
Qed.

Lemma empty_set_stable_wk_not_emp_list `{gLtsP : @gLts P A H} `{!FiniteImagegLts P A} a s ps : ¬ ∅ ⟹[a :: s] ps.
Proof.
  intro imp.
  inversion imp; subst.
  + eapply (@lts_refuses_spec2 (gset P));eauto. eapply empty_set_stable.
  + eapply (@lts_refuses_spec2 (gset P));eauto. eapply empty_set_stable.
Qed.

Lemma empty_set_stable_wk_not_emp_list_inv `{gLtsP : @gLts P A H} `{!FiniteImagegLts P A} a s ps : ¬ ps ⟹[a :: s] ∅.
Proof.
  destruct ps using set_ind_L.
  + intro imp. eapply empty_set_stable_wk_not_emp_list;eauto.
  + intro imp. eapply empty_set_stable_wk_inv_nil in imp; set_solver.
Qed.

Lemma empty_set_wk_determinacy `{gLtsP : @gLts P A H} `{!FiniteImagegLts P A} ps : ∅ ⟹ ps -> ps = ∅.
Proof.
  intro imp. inversion imp.
  + subst. eauto.
  + subst. exfalso. eapply (@lts_refuses_spec2 (gset P));eauto. eapply empty_set_stable.
Qed.

Lemma termination_sub `{gLtsP : @gLts P A H} `{!FiniteImagegLts P A}
  ps :
  ps ⤓
    -> forall qs, qs ⊆ ps
      -> qs ⤓.
Proof.
  intros hmx. dependent induction hmx.
  constructor. intros. eapply H1. 
  set (q' := lts_tau_set_from_pset_ispec qs).
  destruct q'.
  split.
  + reflexivity.
  + destruct (set_choose_or_empty q) as [(q' & l')|].
    - intro eq_nil. destruct H3 as (eq & eq').
      subst. eapply H4 in l' as (p' & mem' & tr').
      eapply H2 in mem'. destruct (lts_tau_set_from_pset_ispec p) as (Hyp1 & Hyp2).
      eapply Hyp2 in mem'. eapply mem' in tr'. set_solver.
    - destruct H3. set_solver.
  + intro p'. intro mem. destruct H3 as (eq & eq'). subst.
    destruct (lts_tau_set_from_pset_ispec qs) as (Hyp1 & Hyp2).
    eapply Hyp1 in mem as (p'' & mem & eq). eapply H2 in mem.
    destruct (lts_tau_set_from_pset_ispec p) as (Hyp'1 & Hyp'2).
    eapply Hyp'2; eauto.
Qed.

Lemma termination_sum `{gLtsP : @gLts P A H} `{!FiniteImagegLts P A} (X : gset P) (Y : gset P) : X ⤓ -> Y ⤓ -> (X ∪ Y) ⤓.
Proof.
  intros conv1 conv2. revert Y conv2.
  dependent induction conv1.
  intros ps2 hmx2.
  constructor. intros.
  set (Y := lts_tau_set_from_pset p).
  set (Z := lts_tau_set_from_pset ps2).
  assert (q ⊆ lts_tau_set_from_pset p ∪ lts_tau_set_from_pset ps2).
    { intros q' mem. destruct H2 as (eq1 & eq2). subst.
      destruct (lts_tau_set_from_pset_ispec (p ∪ ps2)) as (Hyp1 & Hyp2).
      eapply Hyp1 in mem as (q0 & mem & l).
      eapply elem_of_union in mem. destruct mem.
      eapply elem_of_union. left. eapply lts_tau_set_from_pset_ispec; eassumption.
      eapply elem_of_union. right. eapply lts_tau_set_from_pset_ispec; eassumption. }
  (* assert (q ⊆ lts_tau_set_from_pset p ∪ lts_tau_set_from_pset ps2) as dup;eauto *)
  assert ( lts_tau_set_from_pset p ∪ lts_tau_set_from_pset ps2 ⊆ q ) as PrimHyp.
  { intro. intro. eapply elem_of_union in H4.
    destruct H4.
    ++ destruct H2 as (eq & not_empty). subst.
       destruct (lts_tau_set_from_pset_ispec (p)) as (Hyp1 & Hyp2).
       eapply Hyp1 in H4 as (p'' & mem & tr).
       assert (p'' ∈ p ∪ ps2) by set_solver.
       eapply lts_tau_set_from_pset_ispec. exact H2.
       eauto.
    ++ destruct H2 as (eq & not_empty). subst.
       destruct (lts_tau_set_from_pset_ispec ps2) as (Hyp1 & Hyp2).
       eapply Hyp1 in H4 as (p'' & mem & tr).
       assert (p'' ∈ p ∪ ps2) by set_solver.
       eapply lts_tau_set_from_pset_ispec. exact H2.
       eauto. }
  assert (q = lts_tau_set_from_pset p ∪ lts_tau_set_from_pset ps2) as HypPrim2.
  { set_solver. }
  (* eapply lem_dec in H3 as (Y' & Z' & Y_spec' & Z_spec' & eq). *)
  assert (lts_tau_set_from_pset p ⊆ lts_tau_set_from_pset p) as Y_spec'.
  { set_solver. }
  assert (lts_tau_set_from_pset ps2 ⊆ lts_tau_set_from_pset ps2) as Z_spec'.
  { set_solver. }
  assert (lts_tau_set_from_pset p ∪ lts_tau_set_from_pset ps2 ≡ q) as eq.
  { set_solver. } clear HypPrim2.
  remember (lts_tau_set_from_pset p) as Y_'.
  remember (lts_tau_set_from_pset ps2) as Z_'.
  destruct Y_' using set_ind_L.
    + destruct Z_' using set_ind_L.
      ++ exfalso. destruct H2.
         set_solver.
      ++ assert (lts_tau_set_from_pset p = ∅) by set_solver.
         assert (lts_tau_set_from_pset ps2 = q) by set_solver. subst.
         inversion hmx2; subst. 
         destruct H2; subst. eapply H6. split.
         +++ eapply leibniz_equiv. split.
             ++++ eauto.
             ++++ eauto.
         +++ set_solver.
    + destruct Z_' using set_ind_L.
      ++ assert (lts_tau_set_from_pset p = q) by set_solver.
         assert (p ⤓) by eauto with mdb.
         inversion H5; subst. eapply H6. split.
         +++ destruct H2. subst. intros. destruct (lts_tau_set_from_pset_ispec p) as (Hyp1 & Hyp2).
             eapply leibniz_equiv. split.
             ++++ eauto.
             ++++ eauto.
         +++ set_solver.
      ++ subst.
         replace q with (({[x]} ∪ X) ∪ ({[x0]} ∪ X0)) by set_solver.
         eapply H1. split.
         +++ eauto.
         +++ set_solver.
         +++ inversion hmx2; subst.
             eapply H6. split.
             eauto. set_solver.
Qed.

Lemma termination_forall `{gLtsP : @gLts P A H} `{!FiniteImagegLts P A} (ps : gset P) :
  (forall (p : P), p ∈ ps -> {[p]} ⤓) -> ps ⤓.
Proof.
  intro hm.
  induction ps using set_ind_L.
  - intros. eapply empty_set_termination.
  - destruct (set_choose_or_empty X).
    + eapply termination_sum; set_solver.
    + assert (X = ∅) by set_solver.
      rewrite H2, union_empty_r_L. set_solver.
Qed.

Lemma termination_set_if_termination `{gLtsP : @gLts P A H} `{!FiniteImagegLts P A} (p : P) : p ⤓ -> {[ p ]} ⤓.
Proof.
  intro hm. dependent induction hm.
  constructor. intros.
  eapply termination_forall. intros.
  destruct H2 as (eq & eq'). subst. unfold lts_tau_set_from_pset in H3.
  rewrite elements_singleton in H3. simpl in *.
  assert (list_to_set (lts_tau_set p) ∪ (∅ : gset P) = list_to_set (lts_tau_set p)) as eq by set_solver.
  rewrite eq in H3. eapply elem_of_list_to_set in H3. eapply lts_tau_set_spec in H3.
  eapply H1. eauto.
Qed.

Lemma termination_if_termination_set_helper  `{gLtsP : @gLts P A H} `{!FiniteImagegLts P A} (ps : gset P) :
  ps ⤓
    -> forall p, p ∈ ps
      -> p ⤓.
Proof.
  intro hm. dependent induction hm.
  intros p' mem. constructor.
  intros p'' tr .
  eapply H1.
  + split. reflexivity. eapply lts_tau_set_from_pset_ispec in tr; set_solver.
  + eapply lts_tau_set_from_pset_ispec; set_solver.
Qed.

Lemma termination_if_termination_set  `{gLtsP : @gLts P A H} `{!FiniteImagegLts P A} (p : P) :
  {[ p ]} ⤓
    -> p ⤓.
Proof. intros. eapply termination_if_termination_set_helper; set_solver. Qed.

Lemma termination_set_iff_termination `{gLtsP : @gLts P A H} `{!FiniteImagegLts P A} (p : P):
  p ⤓ <-> {[ p ]} ⤓.
Proof. split; [eapply termination_set_if_termination | eapply termination_if_termination_set]. Qed.

Lemma termination_set_for_all `{gLtsP : @gLts P A H} `{!FiniteImagegLts P A} (X : gset P) :
  (forall p, p ∈ X -> p ⤓)
      -> X ⤓.
Proof.
  intros hm. eapply termination_forall.
  intros. eapply hm in H0. eapply termination_set_iff_termination in H0. eauto.
Qed.

Lemma termination_set_iff_termination_forall `{gLtsP : @gLts P A H} `{!FiniteImagegLts P A} (X : gset P) :
  (forall p, p ∈ X -> p ⤓) <-> X ⤓.
Proof.
  intros.
  split. now eapply termination_set_for_all.
  now eapply termination_if_termination_set_helper.
Qed.

From TestingTheory Require Import Convergence.

Lemma empty_set_conv `{gLtsP : @gLts P A H} `{!FiniteImagegLts P A} s : ∅ ⇓ s.
Proof.
  induction s.
  + constructor. eapply empty_set_termination.
  + constructor.
    * eapply empty_set_termination.
    * intros. exfalso. eapply empty_set_stable_wk_not_emp_list;eauto.
Qed.

Lemma wk_tr_inv `{gLtsP : @gLts P A H} `{!FiniteImagegLts P A} ps s qs  : ps ⟹[s] qs -> forall q, q ∈ qs -> exists p, (p : P) ⟹[s] (q : P) /\ p ∈ ps .
Proof.
  intro Hyp.
  dependent induction Hyp.
  + intros. exists q. split;eauto. constructor; eauto.
  + intros. eapply IHHyp in H0 as (p' & wk_tr & mem).
    destruct l as (eq & non_empty).
    subst. eapply (lts_tau_set_from_pset_ispec p) in mem as (p'' & mem' & tr).
    exists p''. split;eauto. eapply wt_tau;eauto.
  + intros. eapply IHHyp in H0 as (p' & wk_tr & mem).
    destruct l as (eq & non_empty).
    subst. eapply (lts_extaction_set_from_pset_ispec p μ ) in mem as (p'' & mem' & tr).
    exists p''. split;eauto. eapply wt_act;eauto.
Qed.

Lemma convergence_set_if_convergence_forall `{gLtsP : @gLts P A H} `{!FiniteImagegLts P A} (ps : gset P) s :
  (forall (p : P), p ∈ ps -> p ⇓ s) -> ps ⇓ s.
Proof.
  revert ps.
  dependent induction s.
  + constructor. eapply termination_set_for_all. intros; eauto.
    assert (p ⇓ []).
    { eapply H0. eauto. }
    inversion H2; eauto.
  + intros. constructor.
    ++ eapply termination_set_for_all.
       intros. assert (p ⇓ a :: s).
       { eapply H0; eauto. }
       inversion H2. subst ;eauto.
    ++ intros. eapply IHs.
       intros. eapply wk_tr_inv in H1 as (p' & wk_tr & eq) ;eauto.
       eapply H0 in eq. inversion eq; subst. eapply H6;eauto.
Qed.

Lemma witness_wk_tr `{gLtsP : @gLts P A H} `{!FiniteImagegLts P A} ps p s q : p ⟹[s] q -> p ∈ ps -> (exists qs, ps ⟹[s] qs /\ q ∈ qs).
Proof.
  intro wk_tr. revert ps. dependent induction wk_tr.
  + intros. exists ps. split;eauto. constructor.
  + intros. eapply lts_tau_set_from_pset_ispec in l as eq;eauto.
    eapply IHwk_tr in eq as (qs' & wk_tr' & mem);eauto.
    exists qs'. split;eauto. eapply wt_tau;eauto. split;eauto.
    intro. eapply lts_tau_set_from_pset_ispec in l as eq;eauto.
    rewrite H1 in eq. inversion eq.
  + intros. assert (q ∈ (lts_extaction_set_from_pset ps μ)).
    { eapply lts_extaction_set_from_pset_ispec;eauto. }
    eapply IHwk_tr in H1 as (qs' & wk_tr' & mem).
    exists qs'. split ;eauto. eapply wt_act;eauto.
    split;eauto. intro. assert (q ∈ (lts_extaction_set_from_pset ps μ)).
    { eapply lts_extaction_set_from_pset_ispec;eauto. }
    rewrite H1 in H2. inversion H2.
Qed.

Lemma convergence_forall_if_convergence_set `{gLtsP : @gLts P A H} `{!FiniteImagegLts P A} (ps : gset P) s :
  ps ⇓ s -> forall p, p ∈ ps -> p ⇓ s.
Proof.
  (* intro hm. dependent induction hm. *)
  unfold trace in s. revert ps.
  dependent induction s.
  + intros ps hm p mem. inversion hm; subst. constructor.
    eapply termination_set_iff_termination_forall;eauto.
  + intros. inversion H0; subst.
    constructor. eapply termination_set_iff_termination_forall;eauto.
    intros. assert (exists qs, ps ⟹{a} qs /\ q ∈ qs) as (qs & wk_tr & mem).
    { eapply witness_wk_tr; eauto. }
    eapply H6 in wk_tr.
    eapply IHs;eauto.
Qed.

Lemma convergence_set_iff_convergence_forall `{gLtsP : @gLts P A H} `{!FiniteImagegLts P A} (ps : gset P) s :
  (forall (p : P), p ∈ ps -> p ⇓ s) <-> ps ⇓ s.
Proof.
  intros; split; [ eapply convergence_set_if_convergence_forall | eapply convergence_forall_if_convergence_set].
Qed.

