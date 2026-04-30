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
From Stdlib.Program Require Import Wf Equality.
From Stdlib.Wellfounded Require Import Inverse_Image.


From stdpp Require Import base countable finite gmap list finite base decidable finite gmap.

From TestingTheory Require Import gLts Bisimulation Lts_OBA Lts_Finite_Output_Chain Lts_FW Lts_OBA_FB Lts_CN
      Must Subset_Act InteractionBetweenLts ParallelLTSConstruction ForwarderConstruction 
      Termination Convergence FiniteImageLTS WeakTransitions Lift Testing_Predicate DefinitionAS MultisetLTSConstruction.
From TestingTheory Require Import ActTau InFiniteSetHelper SetLTSConstruction.

(** * Soundness *)

Inductive mustx `{EA : !ExtAction A} `{gLtsT : !gLtsEq T EA} `{TP : @Testing_Predicate T A EA outcome _}
  `{gLtsP : @gLts P A EA, !FiniteImagegLts P A} {Hinter : @Prop_of_Inter P T A dual EA gLtsP _}
  (X : gset P) (t : T) : Prop :=
| mx_now (hh : outcome t) : mustx X t
| mx_step
    (nh : ¬ outcome t)
    (ex : forall (p : P), p ∈ X -> ∃ p', inter_step (p, t) τ p')
    (pt : forall X',
        lts_tau_set_from_pset_spec1 X X' -> X' ≠ ∅ ->
        mustx X' t)
    (et : forall (t' : T), t ⟶ t' -> mustx X t')
    (com : forall (t' : T) μ1 μ2 (X' : gset P),
        dual μ1 μ2 ->
        t ⟶[μ2] t' ->
        wt_set_from_pset_spec1 X [μ1] X' ->
        X' ≠ ∅ ->
        mustx X' t')
  : mustx X t.

#[global] Hint Constructors mustx:mdb.
Global Notation "X 'must_pass_x' t" := (mustx X t) (at level 70).

Section Must_for_sets.

Context `{EA : !ExtAction A}.
Context `{gLtsT : !gLtsEq T EA}.
Context `{TP : @Testing_Predicate T A EA outcome _}.

Context `{gLtsP : @gLts P A EA, !FiniteImagegLts P A}.
Context `{Hinter : @Prop_of_Inter P T A dual EA gLtsP _}.

(** ** Must predicate for Sets *)

Lemma mx_sub X t :
  X must_pass_x t
    -> forall X', X' ⊆ X
      -> X' must_pass_x t.
Proof.
  intros hmx. dependent induction hmx.
  - eauto with mdb.
  - intros qs sub.
    apply mx_step; eauto with mdb.
    + intros qs' hs hneq_nil.
      set (X' := lts_tau_set_from_pset_ispec X).
      destruct X'.
      eapply H; eauto with mdb.
      ++ destruct (set_choose_or_empty qs') as [(q' & l'%hs)|].
         intro eq_nil. destruct l' as (q & mem%sub & l%H3); set_solver.
         set_solver.
      ++ intros p (q & mem%sub & l)%hs. eauto.
    + intros t' μ μ' qs' hle duo hwqs hneq_nil.
      eapply (H1 t' μ μ'); eauto. intros p' mem%hwqs. set_solver.
Qed.

Lemma mx_mem X t :
  X must_pass_x t
    -> forall p, p ∈ X
      -> mustx {[ p ]} t.
Proof. intros hmx p mem. eapply mx_sub; set_solver. Qed.

Lemma mustx_terminate_unoutcome X t :
  X must_pass_x t
    -> outcome t \/ forall p, p ∈ X -> p ⤓.
Proof.
  intros hmx.
  induction hmx.
  - now left.
  - right.
    intros p mem.
    eapply tstep. intros p' l.
    edestruct (H {[p']}); [exists p; set_solver| | |]; set_solver.
Qed.

Lemma mustx_terminate_unoutcome' X (t : T) :
  X must_pass_x t
        -> ¬ outcome t -> forall p, p ∈ X -> p ⤓.
Proof.
  intros hmx not_happy p mem.
  dependent induction hmx.
  + contradiction.
  + eapply tstep.
    intros q tr. eapply H; eauto.
    assert (h1 : lts_tau_set_from_pset_spec1 X {[q]}).
    exists p. assert (q0 = q);subst. set_solver. split; eauto. eauto.
    set_solver. set_solver.
Qed.

Lemma unoutcome_acnv_mu X t t' :
  X must_pass_x t
    -> forall μ μ' p, p ∈ X
      -> dual μ μ'
        -> t ⟶[μ'] t'
          -> ¬ outcome t -> ¬ outcome t' -> p ⇓ [μ].
Proof.
  intros hmx μ μ' p mem inter l not_happy not_happy'.
  dependent induction hmx.
  - contradiction.
  - edestruct mustx_terminate_unoutcome as [happy | finish].
    + eauto with mdb.
    + contradiction.
    + edestruct mustx_terminate_unoutcome; eauto with mdb. contradiction.
      eapply cnv_act. eauto.
      intros q w.
      assert (h1 : wt_set_from_pset_spec1 X [μ] {[q]}).
      exists p. split; set_solver.
      assert (h2 : {[q]} ≠ (∅ : gset P)) by set_solver.
      set (hm := com t' μ μ' {[ q ]} inter l h1 h2).
      destruct (mustx_terminate_unoutcome _ _ hm).
      +++ contradiction.
      +++ eapply cnv_nil. eapply H3. set_solver.
Qed.

Lemma must_mu_either_outcome_cnv X t t' :
  X must_pass_x t
    -> forall μ μ' p, p ∈ X
      -> dual μ μ'
        -> t ⟶[μ'] t'
          -> outcome t \/ outcome t' (* ajout par rapport à Input/Output *)
                       \/ p ⇓ [μ].
Proof.
  intros hmx μ μ' p mem inter l.
  destruct (decide (outcome t)); destruct (decide (outcome t')).
  + left; eauto.
  + left; eauto.
  + right; eauto.
  + right. right. eapply unoutcome_acnv_mu; eauto.
Qed.

(* to rework , why ?*)
Lemma mx_sum X X' t : mustx X t
    -> X' must_pass_x t
      -> (X ∪ X') must_pass_x t.
Proof.
  intros hmx1 hmx2. revert X' hmx2.
  dependent induction hmx1. eauto with mdb.
  intros ps2 hmx2.
  eapply mx_step.
  - eassumption.
  - intros p mem.
    eapply elem_of_union in mem.
    destruct mem.
    eapply ex; eassumption.
    inversion hmx2; subst. contradiction.
    eapply ex0; eassumption.
  - intros.
    set (Y := lts_tau_set_from_pset X).
    set (Z := lts_tau_set_from_pset ps2).
    assert (X' ⊆ lts_tau_set_from_pset X ∪ lts_tau_set_from_pset ps2).
    { intros q mem. eapply H2 in mem as (q0 & mem & l).
      eapply elem_of_union in mem. destruct mem.
      eapply elem_of_union. left. eapply lts_tau_set_from_pset_ispec; eassumption.
      eapply elem_of_union. right. eapply lts_tau_set_from_pset_ispec; eassumption. }
    eapply lem_dec in H4 as (Y' & Z' & Y_spec' & Z_spec' & eq).
    remember Y' as Y_'.
    remember Z' as Z_'.
    destruct Y_' using set_ind_L.
    + destruct Z_' using set_ind_L.
      ++ exfalso.
         assert (exists p, p ∈ X') as (p & mem).
         destruct X' using set_ind_L. contradiction.
         exists x. set_solver.
         eapply H2 in mem as (p0 & mem & l).
         eapply elem_of_union in mem. destruct mem.
         eapply lts_tau_set_from_pset_ispec in l; set_solver.
         eapply lts_tau_set_from_pset_ispec in l; set_solver.
      ++ assert (Y' = ∅) by set_solver.
         assert (Z' = X') by set_solver. subst.
         inversion hmx2; subst. set_solver.
         eapply pt0. intros t' mem. eapply lts_tau_set_from_pset_ispec. set_solver. set_solver.
    + destruct Z_' using set_ind_L.
      ++ assert (Y' = X') by set_solver.
         assert (mustx X t) by eauto with mdb.
         inversion H6; subst. set_solver.
         eapply pt0. intros t' mem. eapply lts_tau_set_from_pset_ispec. set_solver. set_solver.
      ++ subst.
         replace X' with (({[x]} ∪ X0) ∪ ({[x0]} ∪ X1)) by set_solver.
         eapply H.
         +++ intros t' mem. apply lts_tau_set_from_pset_ispec. set_solver.
         +++ set_solver.
         +++ inversion hmx2; subst.
             ++++ now contradiction nh.
             ++++ eapply pt0. intros t' mem. eapply lts_tau_set_from_pset_ispec. set_solver. set_solver.
  - intros t' l. eapply H0; eauto with mdb.
    inversion hmx2; subst; eauto with mdb. contradiction.
  - intros t' μ μ' ps' duo l ps'_spec neq_nil.
    destruct (outcome_decidable t'); eauto with mdb.
    assert (HAX : forall p, p ∈ X -> p ⇓ [μ]).
    intros p0 mem0.
    eapply cnv_act. edestruct (mustx_terminate_unoutcome X); eauto with mdb.
    contradiction.
    intros p' hw. eapply cnv_nil.
    edestruct (mustx_terminate_unoutcome {[p']}). eapply com; eauto.
    intros j memj. eapply elem_of_singleton_1 in memj. subst.
    exists p0. split; eauto. set_solver.
    set_solver.
    set (Y := wt_s_set_from_pset X [μ] HAX).
    assert (HAX2 : forall p, p ∈ ps2 -> p ⇓ [μ]).
    intros p0 mem0.
    eapply cnv_act. edestruct (mustx_terminate_unoutcome ps2); eauto with mdb.
    contradiction.
    intros p' hw. eapply cnv_nil.
    edestruct (mustx_terminate_unoutcome {[p']}).
    inversion hmx2; subst. contradiction. eapply com0; eauto.
    intros j memj. eapply elem_of_singleton_1 in memj. subst.
    exists p0. split; eauto. set_solver. set_solver.
    set (Z := wt_s_set_from_pset ps2 [μ] HAX2).
    assert (ps' ⊆ Y ∪ Z).
    intros q mem. eapply ps'_spec in mem as (q0 & mem & l').
    eapply elem_of_union in mem. destruct mem.
    eapply elem_of_union. left. eapply wt_s_set_from_pset_ispec; eassumption.
    eapply elem_of_union. right. eapply wt_s_set_from_pset_ispec; eassumption.
    eapply lem_dec in H2 as (Y0 & Z0 & Y_spec0 & Z_spec0 & eq).
    destruct Y0 using set_ind_L.
    + destruct Z0 using set_ind_L.
      ++ exfalso.
         assert (exists p, p ∈ ps') as (p & mem).
         destruct ps' using set_ind_L. contradiction.
         exists x. set_solver.
         eapply ps'_spec in mem as (p0 & mem & l').
         eapply elem_of_union in mem.
         destruct mem; eapply (wt_s_set_from_pset_ispec X [μ] HAX) in l'; set_solver.
      ++ inversion hmx2; subst. now contradict nh.
         eapply com0. eassumption. eassumption. intros t'' mem.
         eapply (wt_s_set_from_pset_ispec ps2 [μ] HAX2).
         set_solver. set_solver.
    + destruct Z0 using set_ind_L.
      ++ inversion hmx2; subst.
         +++ now contradict nh.
         +++ eapply com. eassumption. eassumption. intros t'' mem.
             eapply (wt_s_set_from_pset_ispec X [μ] HAX).
             set_solver. set_solver.
      ++ replace ps' with (({[x]} ∪ X0) ∪ ({[x0]} ∪ X1)) by set_solver.
         eapply H1; eauto with mdb.
         +++ intros t'' mem.
             eapply (wt_s_set_from_pset_ispec X [μ] HAX).
             set_solver.
         +++ set_solver.
         +++ inversion hmx2; subst.
             ++++ now contradict nh.
             ++++ eapply com0. eassumption. eassumption.
                  intros t'' mem.
                  eapply (wt_s_set_from_pset_ispec ps2 [μ] HAX2).
                  set_solver. set_solver.
Qed.

Lemma mx_forall X t :
  X ≠ ∅
    -> (forall p, p ∈ X -> {[p]} must_pass_x t)
      -> X must_pass_x t.
Proof.
  intros neq_nil hm.
  induction X using set_ind_L.
  - set_solver.
  - destruct (set_choose_or_empty X).
    + eapply mx_sum; set_solver.
    + assert (X = ∅) by set_solver.
      rewrite H1, union_empty_r_L. set_solver.
Qed.

Lemma wt_nil_mx:
  forall p1 p2 t, {[ p1 ]} must_pass_x t
    -> p1 ⟹ p2 -> {[ p2 ]} must_pass_x t.
Proof.
  intros p1 p2 e hmx wt.
  dependent induction wt; subst; eauto with mdb.
  inversion hmx; subst; eauto with mdb.
  eapply IHwt; eauto with mdb.
  eapply pt; eauto with mdb.
  intros p2 mem. replace q with p2 in * by set_solver.
  exists p; set_solver.
Qed.

Lemma wt_mu_mx  p1 p2 t t' μ μ':
  dual μ μ' -> ¬ outcome t -> mustx {[ p1 ]} t
    -> t ⟶[μ'] t' -> p1 ⟹{μ} p2 -> {[p2]} must_pass_x t'.
Proof.
  intros duo nh hmx l w.
  inversion hmx; subst.
  - contradiction.
  - eapply com; eauto with mdb. exists p1. set_solver.
Qed.

Lemma must_set_if_must  (p : P) (t : T) : p must_pass t -> {[ p ]} must_pass_x t.
Proof.
  intro hm. dependent induction hm.
  - eauto with mdb.
  - eapply mx_step.
    + eassumption.
    + set_solver.
    + intros ps' hs hneq_nil.
      unfold lts_tau_set_from_pset_spec1 in hs.
      eapply mx_forall; set_solver.
    + eauto with mdb.
    + intros e' μ μ' X' duo hle hws hneq_nil.
      unfold wt_set_from_pset_spec1 in hws.
      eapply mx_forall. eassumption.
      intros.
      edestruct hws as (p' & mem%elem_of_singleton_1 & w); subst; eauto.
      inversion w; subst; eauto with mdb.
      eapply wt_mu_mx; eauto with mdb.
      eapply wt_nil_mx; eauto with mdb.
Qed.

Lemma must_if_must_set_helper  (X : gset P) (t : T) :
  X must_pass_x t
    -> forall p, p ∈ X
      -> p must_pass t.
Proof.
  intro hm. dependent induction hm.
  - eauto with mdb.
  - intros p mem. eapply m_step.
    + eassumption.
    + set_solver.
    + intros p' hl.
      set (X' := list_to_set (lts_tau_set p) : gset P).
      assert (p' ∈ X').
      eapply lts_tau_set_spec, elem_of_list_to_set in hl; eauto.
      eapply (H X'); eauto.
      intros p0 mem0%elem_of_list_to_set%lts_tau_set_spec. set_solver. set_solver.
    + eauto with mdb.
    + intros p' e' μ μ' duo hlp hle.
      set (X' := list_to_set (
                     map proj1_sig (enum $ dsig (lts_step p (ActExt μ)))
                   ) : gset P).
      assert (p' ∈ X').
      eapply elem_of_list_to_set, list_elem_of_fmap; eauto.
      exists (dexist p' hlp). split. eauto. eapply elem_of_enum.
      eapply (H1 e' μ μ' X'). eassumption. eassumption.
      intros p0 mem0%elem_of_list_to_set.
      eapply list_elem_of_fmap in mem0 as ((r & l) & eq & mem'). subst.
      exists p. split; eauto.
      eapply wt_act.
      eapply bool_decide_unpack. eauto. eapply wt_nil. set_solver. set_solver.
Qed.

Lemma must_if_must_set  (p : P) (t : T) :
  {[ p ]} must_pass_x t
    -> p must_pass t.
Proof. intros. eapply must_if_must_set_helper; set_solver. Qed.

Lemma must_set_iff_must  (p : P) (t : T) :
  p must_pass t <-> mustx {[ p ]} t.
Proof. split; [eapply must_set_if_must | eapply must_if_must_set]. Qed.

Lemma must_set_for_all  (X : gset P) (t : T) :
  X ≠ ∅
    -> (forall p, p ∈ X -> p must_pass t)
      -> X must_pass_x t.
Proof.
  intros xneq_nil hm.
  destruct (outcome_decidable t).
  - now eapply mx_now.
  - eapply mx_step.
    + eassumption.
    + intros p h%hm. inversion h. contradiction. eassumption.
    + intros X' xspec' xneq_nil'.
      eapply mx_forall. eassumption.
      intros p' (p0 & mem%hm & hl)%xspec'. eapply must_set_iff_must.
      inversion mem; eauto with mdb.
    + intros t' hl.
      eapply mx_forall. eassumption.
      intros p' mem%hm. eapply must_set_iff_must.
      inversion mem; eauto with mdb. contradiction.
    + intros t' μ μ' X' duo hle xspec' xneq_nil'.
      eapply mx_forall. eassumption.
      intros p' (p0 & h%hm & hl)%xspec'. eapply must_set_iff_must.
      eapply must_preserved_by_wt_synch_if_notoutcome; eauto.
Qed.

Lemma must_set_iff_must_for_all  (X : gset P) (t : T) :
  X ≠ ∅ -> (forall p, p ∈ X -> p must_pass t) <-> X must_pass_x t.
Proof.
  intros.
  split. now eapply must_set_for_all.
  now eapply must_if_must_set_helper.
Qed.

End Must_for_sets.

(** ** Contextual preorder for sets *)


Section Must_preorder_for_sets.
Context `{EA : !ExtAction A}.
Context `{gLtsT : !gLtsEq T EA}.
Context `{TP : @Testing_Predicate T A EA outcome _}.

Context `{gLtsP : @gLts P A EA, !FiniteImagegLts P A}.
Context `{HinterP : !Prop_of_Inter P T A dual}.
Context `{gLtsQ : @gLts Q A EA, !FiniteImagegLts Q A}.
Context `{HinterQ : !Prop_of_Inter Q T A dual}.

Definition ctx_pre__x 
  (X : gset P) (Y : gset Q) 
  := forall (t : T), X must_pass_x t -> Y must_pass_x t.

Notation "X ⊑ₛₑₜ_ₘᵤₛₜᵢ Y" := (ctx_pre__x X Y) (at level 70).
Notation "X ⋢ₛₑₜ_ₘᵤₛₜᵢ Y" := (¬ ctx_pre X Y) (at level 70).


(** ** Equivalence between the must preorder and the must preorder on sets *)
Lemma must_set_singleton_iff (p : P) (q : Q) :
  p ⊑ₘᵤₛₜᵢ q <-> {[ p ]} ⊑ₛₑₜ_ₘᵤₛₜᵢ {[ q ]}.
Proof.
  split.
  - intro must_hyp. intros t Hyp_set_p.
    eapply must_if_must_set in Hyp_set_p.
    eapply must_hyp in Hyp_set_p as Hyp_set_q.
    eapply must_set_if_must in Hyp_set_q. exact Hyp_set_q.
  - intro set_must_hyp. intros t Hyp_p.
    eapply must_set_if_must in Hyp_p.
    eapply set_must_hyp in Hyp_p as Hyp_q.
    eapply must_if_must_set in Hyp_q. exact Hyp_q.
Qed.

End Must_preorder_for_sets.

#[global] Hint Unfold ctx_pre__x : mdb.
Global Notation "X ⊑ₛₑₜ_ₘᵤₛₜᵢ Y" := (ctx_pre__x X Y) (at level 70).
Global Notation "X ⋢ₛₑₜ_ₘᵤₛₜᵢ Y" := (¬ ctx_pre X Y) (at level 70).

Inductive mustx_alt `{EA : !ExtAction A} `{gLtsT : !gLtsEq T EA} `{TP : @Testing_Predicate T A EA outcome _}
  `{gLtsP : @gLts P A EA, !FiniteImagegLts P A} {Hinter : @Prop_of_Inter P T A dual EA gLtsP _}
  (X : gset P) (t : T) : Prop :=
| mx_now_alt (hh : outcome t) : mustx_alt X t
| mx_step_alt
    (nh : ¬ outcome t)
    (ex : forall (p : P), p ∈ X -> ∃ p', inter_step (p, t) τ p')
    (pt : forall X',
        X ⟶ X' ->
        mustx_alt X' t)
    (et : forall (t' : T), t ⟶ t' -> mustx_alt X t')
    (com : forall (t' : T) μ1 μ2 (X' : gset P),
        dual μ1 μ2 ->
        t ⟶[μ2] t' ->
        X ⟹{μ1} X' ->
        mustx_alt X' t')
  : mustx_alt X t.

#[global] Hint Constructors mustx_alt:mdb.
Global Notation "X 'must_alt_pass_x' t" := (mustx_alt X t) (at level 70).

Lemma mustx_alt_iff_mustx_alt `{EA : !ExtAction A} `{gLtsT : !gLtsEq T EA} `{TP : @Testing_Predicate T A EA outcome _}
  `{gLtsP : @gLts P A EA, !FiniteImagegLts P A} {Hinter : @Prop_of_Inter P T A dual EA gLtsP _}
  (X : gset P) (t : T) :
  X must_pass_x t <-> X must_alt_pass_x t.
Proof.
  split.
  - intro hmx. dependent induction hmx; eauto.
    + constructor ;eauto.
    + eapply mx_step_alt; eauto.
      * intros. destruct H2;eauto. subst.
        assert (lts_tau_set_from_pset_spec1 X (lts_tau_set_from_pset X)).
        { eapply lts_tau_set_from_pset_ispec. }
        eauto.
      * intros.
        assert (wt_set_from_pset_spec1 X [μ1] X').
        { intro. intro mem. eapply wk_tr_inv in H4 as (p & wk_tr & mem'); eauto. }
        eauto. eapply H1;eauto.
        destruct X' using set_ind_L. 
        ++ intro. eapply empty_set_stable_wk_not_emp_list_inv;eauto.
        ++ set_solver.
  - intro hmx. dependent induction hmx; eauto.
    + constructor ;eauto.
    + eapply mx_step; eauto.
      * intros. assert (X' ⊆ lts_tau_set_from_pset X).
        { intros p' mem'. eapply H2 in mem' as (p & mem & tr).
          eapply lts_tau_set_from_pset_ispec;eauto. }
        assert (lts_tau_set_from_pset X  ≠ ∅ ) by set_solver.
        assert (X ⟶ lts_tau_set_from_pset X).
        { split ;eauto. }
        eapply H in H6. eapply mx_sub;eauto.
      * intros. induction X' using set_ind_L.
        ++ set_solver.
        ++ eapply must_set_for_all. set_solver.
           intros. eapply elem_of_union in H7. destruct H7.
           -- revert p H7. eapply must_set_iff_must_for_all;eauto.
              assert (x ∈ ({[x]} ∪ X0)) by set_solver.
              eapply H4 in H7 as (p' & mem & tr).
              eapply witness_wk_tr in tr as (qs & wk_tr & mem'); eauto.
              assert ({[x]} ⊆ qs) by set_solver.
              eapply mx_sub;eauto.
           -- revert p H7. destruct X0 using set_ind_L.
              ** intros. inversion H7.
              ** eapply must_set_iff_must_for_all;eauto.
                 set_solver.
                 assert (wt_set_from_pset_spec1 X [μ1] ({[x0]} ∪ X0)).
                 { intros p mem. assert (p ∈ ({[x]} ∪ ({[x0]} ∪ X0))) by set_solver.
                   eapply H4 in H8. eauto. }
                 eapply IHX'. eauto. set_solver.
Qed.

(** ** Condition on convergence *)

Definition bhv_pre_cond1__x `{gLtsP : @gLts P A EA, !FiniteImagegLts P A}
  `{gLtsQ : @gLts Q A EA, !FiniteImagegLts Q A}
  (X : gset P) (Y : gset Q) :=
  forall s, (forall p, p ∈ X -> p ⇓ s) -> (forall q, q ∈ Y -> q ⇓ s).

Global Notation "X ₁≼ₛₑₜ_ₐₛ Y" := (bhv_pre_cond1__x X Y) (at level 70).

(** ** Condition on acceptance sets *)

Definition bhv_pre_cond2__x
  `{gLtsP : @gLts P A EA, !FiniteImagegLts P A}
  `{gLtsQ : @gLts Q A EA, !FiniteImagegLts Q A}
  `{gLtsT : @gLtsEq T A EA}
  `{AbsPT : @AbsAction P T FinA PreAct A EA Φ 𝝳P _ _}
  `{AbsQT : @AbsAction Q T FinA PreAct A EA Φ 𝝳Q _ _}
  (X : gset P) (Y : gset Q) :=
  forall q s q', q ∈ Y ->
    q ⟹[s] q' -> q' ↛ ->
    (forall p, p ∈ X -> p ⇓ s) ->
    exists p, p ∈ X /\ exists p', p ⟹[s] p' /\ p' ↛ /\ (⌈ (𝝳P ∘ Φ) ⌉ (coR p') ⊆ ⌈ (𝝳Q ∘ Φ) ⌉ (coR q')).

Global Notation "X ₂≼ₛₑₜ_ₐₛ Y" := (bhv_pre_cond2__x X Y) (at level 70).


(** ** Alternative preorder on sets *)

Definition bhv_pre__x 
  `{gLtsP : @gLts P A EA, !FiniteImagegLts P A}
  `{gLtsQ : @gLts Q A EA, !FiniteImagegLts Q A}
  `{gLtsT : @gLtsEq T A EA}
  `{AbsPT : @AbsAction P T FinA PreAct A EA Φ 𝝳P _ _}
  `{AbsQT : @AbsAction Q T FinA PreAct A EA Φ 𝝳Q _ _}
    (X : gset P) (Y : gset Q) :=
      (X ₁≼ₛₑₜ_ₐₛ Y /\ X ₂≼ₛₑₜ_ₐₛ Y).

Global Notation "X ≼ₛₑₜ_ₐₛ  Y" := (bhv_pre__x X Y) (at level 70).

#[global] Hint Unfold bhv_pre_cond1__x bhv_pre_cond2__x : mdb.

Section Acceptance_Set_preorder_for_sets.

Context `{EA : !ExtAction A}.
Context `{gLtsEqT : !gLtsEq T EA}.
Context `{TP : @Testing_Predicate T A EA outcome _}.

Context `{gLtsP : @gLts P A EA, !FiniteImagegLts P A}.
Context `{HinterP : !Prop_of_Inter P T A dual}.
Context `{gLtsQ : @gLts Q A EA, !FiniteImagegLts Q A}.
Context `{HinterQ : !Prop_of_Inter Q T A dual}.

Context `{AbsPT : @AbsAction P T FinA PreAct A EA Φ 𝝳P _ _}.
Context `{AbsQT : @AbsAction Q T FinA PreAct A EA Φ 𝝳Q _ _}.

Lemma bhvleqone_preserved_by_reduction
  (X : gset P) (Y Y' : gset Q) :
  X ₁≼ₛₑₜ_ₐₛ Y -> lts_tau_set_from_pset_spec1 Y Y' -> Y' ≠ ∅ -> X ₁≼ₛₑₜ_ₐₛ Y'.
Proof.
  intros halt1 l not_empty s mem.
  intros. eapply l in H as (q' & mem' & tr').
  eapply cnv_preserved_by_lts_tau; eauto.
Qed.

Lemma bhvleqone_preserved_by_reduction_lts
  (X : gset P) (Y Y' : gset Q) :
  X ₁≼ₛₑₜ_ₐₛ Y -> Y ⟶ Y' -> Y' ≠ ∅ -> X ₁≼ₛₑₜ_ₐₛ Y'.
Proof.
  intros; eapply bhvleqone_preserved_by_reduction;eauto.
  destruct H0. subst. eapply lts_tau_set_from_pset_ispec.
Qed.

Lemma bhvleqone_preserved_by_external_action
  (X X' : gset P) μ (Y Y' : gset Q) (htp : forall p, p ∈ X -> terminate p) :
  X ₁≼ₛₑₜ_ₐₛ Y -> wt_set_from_pset_spec X [μ] X'  -> wt_set_from_pset_spec1 Y [μ] Y' -> Y' ≠ ∅ -> X' ₁≼ₛₑₜ_ₐₛ Y'.
Proof.
  intros hleq hws l not_empty s hcnv. intros.
  eapply l in H as (q' & mem' & wk_tr).
  eapply cnv_preserved_by_wt_act;eauto.
  eapply hleq.
  intros p mem''. eapply cnv_act.
  + eapply htp; eauto.
  + intros. eapply hcnv, hws; eassumption.
  + exact mem'.
Qed.

Lemma bhvleqone_preserved_by_external_action_lts
  (X X' : gset P) μ (Y Y' : gset Q) (htp : forall p, p ∈ X -> terminate p) :
  X ₁≼ₛₑₜ_ₐₛ Y -> wt_set_from_pset_spec X [μ] X'  -> Y ⟹{μ} Y' -> X' ₁≼ₛₑₜ_ₐₛ Y'.
Proof.
  intros. eapply bhvleqone_preserved_by_external_action; eauto.
  intros q' mem'. eapply wk_tr_inv in mem' as (p' & hyp1 & hyp2).
  eauto. eauto. intro. subst. eapply empty_set_stable_wk_not_emp_list_inv;eauto.
Qed.

Lemma alt_set_singleton_iff 
  (p : P) (q : Q) : ({[ p ]} : gset P) ≼ₛₑₜ_ₐₛ ({[ q ]} : gset Q) <->  p ≼ₐₛ q.  
Proof.
  split.
  - intros (hbhv1 & hbhv2). split.
    + intros s mem. eapply hbhv1. set_solver. set_solver.
    + intros s q' w st hcnv. edestruct hbhv2; set_solver.
  - intros (h1 & h2). split.
    + intros s mem. intros q' mem'.
      assert (q' = q) by set_solver. subst. eapply h1. set_solver.
    + intros q' s q'' w st hcnv.
      assert (q' = q) by set_solver. subst. intros.
      exists p. edestruct h2 ; set_solver.
Qed.

Lemma bhvx_preserved_by_reduction
  (X : gset P) (Y Y' : gset Q) : lts_tau_set_from_pset_spec1 Y Y' -> Y' ≠ ∅ -> X ≼ₛₑₜ_ₐₛ Y -> X ≼ₛₑₜ_ₐₛ Y'.
Proof.
  intros l not_empty (halt1 & halt2).
  split.
  - intros s mem. intros.
    eapply l in H as (q' & tr & mem'). eapply cnv_preserved_by_lts_tau; eauto.
  - (* bhvleqtwo_preserved_by_reduction *)
    intros q' s q'' w st hcnv. intro hyp_conv.
    eapply l in w as (q & mem & tr).
    destruct (halt2 q s q'') as (p' & mem' & p'' & hw & hst) (* & sub0) *); eauto with mdb.
Qed.

Lemma bhvx_preserved_by_reduction_lts
  (X : gset P) (Y Y' : gset Q) : Y ⟶ Y' -> X ≼ₛₑₜ_ₐₛ Y -> X ≼ₛₑₜ_ₐₛ Y'.
Proof.
  intros. destruct H. subst. eapply bhvx_preserved_by_reduction;eauto.
  eapply lts_tau_set_from_pset_ispec.
Qed.

Lemma bhvx_preserved_by_external_action
  (X X' : gset P) μ (Y Y' : gset Q) (htp : forall p, p ∈ X -> terminate p) :
  wt_set_from_pset_spec1 Y [μ] Y' -> Y' ≠ ∅
    -> wt_set_from_pset_spec X [μ] X'
      -> X ≼ₛₑₜ_ₐₛ Y
        -> X' ≼ₛₑₜ_ₐₛ Y'.
Proof.
  intros lts__q not_empty ps1_spec (halt1 & halt2). split.
  - eapply bhvleqone_preserved_by_external_action; eauto.
  - (* bhvleqtwo_preserved_by_ext_action *)
    intros q s q0 mem wt st hcnv. assert (wt_set_from_pset_spec1 Y [μ] Y') as tr'';eauto.
    eapply tr'' in mem as (q' & mem' & tr_ext);eauto.
    edestruct (halt2 q' (μ :: s) q0) as (t & mem'' & p0 & p1 & wta__t & sub); eauto with mdb.
    eapply wt_push_left; eauto.
    eapply convergence_set_iff_convergence_forall. eapply convergence_set_if_convergence_forall.
    intros p'' mem1. eapply cnv_act; eauto.
    intros q1 wk_tr. eapply ps1_spec in wk_tr .
    eapply hcnv; eassumption. eauto.
    eapply wt_pop in p1 as (r & w1 & w2).
    exists r. repeat split. eapply ps1_spec; eassumption. eauto.
Qed.

Lemma bhvx_preserved_by_external_action_lts
  (X X' : gset P) μ (Y Y' : gset Q) (htp : forall p, p ∈ X -> terminate p) :
  Y ⟹{μ} Y'
    -> wt_set_from_pset_spec X [μ] X'
      -> X ≼ₛₑₜ_ₐₛ Y
        -> X' ≼ₛₑₜ_ₐₛ Y'.
Proof.
  intros. eapply bhvx_preserved_by_external_action;eauto.
  + intros q mem. eapply wk_tr_inv in mem as (q' & wk_tr & eq).
    eauto. eauto.
  + intro. subst. eapply empty_set_stable_wk_not_emp_list_inv;eauto.
Qed.

Lemma bhvx_preserved_by_external_action_tr
  (X X' : gset P) μ (Y Y' : gset Q) (htp : forall p, p ∈ X -> terminate p) :
  lts_extaction_set_from_pset_spec1  Y μ Y' -> Y' ≠ ∅
    -> wt_set_from_pset_spec X [μ] X'
      -> X ≼ₛₑₜ_ₐₛ Y
        -> X' ≼ₛₑₜ_ₐₛ Y'.
Proof.
  intros. eapply bhvx_preserved_by_external_action;eauto.
  intros q mem. eapply H in mem as (p' & ext_tr & mem).
  eapply lts_to_wt in mem. eauto.
Qed.

Lemma bhvx_preserved_by_external_action_tr_lts
  (X X' : gset P) μ (Y Y' : gset Q) (htp : forall p, p ∈ X -> terminate p) :
  Y ⟶[μ] Y'
    -> wt_set_from_pset_spec X [μ] X'
      -> X ≼ₛₑₜ_ₐₛ Y
        -> X' ≼ₛₑₜ_ₐₛ Y'.
Proof.
  intros. destruct H. subst. 
  eapply bhvx_preserved_by_external_action_tr; eauto.
  eapply lts_extaction_set_from_pset_ispec.
Qed.

Lemma reverse_trace_inclusion
  (X : gset P) (Y Y' : gset Q) μ
  : X ≼ₛₑₜ_ₐₛ Y -> (forall p, p ∈ X -> p ⇓ [μ]) ->
    wt_set_from_pset_spec1 Y [μ] Y' -> Y' ≠ ∅ -> exists X', X ⟹{μ} X'.
Proof.
  intros (h1 & h2) hcnv hl not_empty.
  assert (hqt : Y' ⤓).
  { eapply termination_set_for_all. intros.
    eapply hl in H as (q'' & mem & wt_tr).
    eapply cnv_terminate, cnv_preserved_by_wt_act;eauto. }
  assert (exists Y'', wt_set_from_pset_spec1 Y [μ] Y'' /\ Y'' ↛ /\ Y'' ≠ ∅) as (q0 & wq0 & stq0 & not_empty').
  { eapply terminate_then_wt_refuses in hqt as (q0 & w0 & st0). exists q0.
    split; eauto. intros q mem. eapply wk_tr_inv in w0 as (q'' & wt_tr & mem'');eauto.
    eapply hl in mem'' as (p'' & mem''' & wt_tr'''). exists p''. split;eauto. eapply wt_push_nil_right;eauto.
    split ;eauto. intro. subst. eapply empty_set_stable_wk_inv_nil in w0. subst. set_solver. }
  destruct q0 using set_ind_L.
  + set_solver.
  + assert (x ∈ ({[x]} ∪ X0)) as mem by set_solver.
    eapply wq0 in mem as ( q & mem & wk_tr).
    destruct (h2 q [μ] x mem wk_tr) as (p1 & mem1 & p0 & wp0 & stp0) (* & subp0) *).
    - unfold lts_refuses in stq0. simpl in *. 
      unfold SetLTSConstruction.SET_LTS_obligation_3 in stq0.
      eapply stq0. set_solver.
    - eauto.
    - eapply witness_wk_tr in wp0 as (ps' & wk_tr' & mem'); eauto. 
    (* * set_solver. *)
Qed.

Lemma reverse_trace_inclusion_tr
  (X : gset P) (Y Y' : gset Q) μ
  : X ≼ₛₑₜ_ₐₛ Y -> (forall p, p ∈ X -> p ⇓ [μ]) ->
    lts_extaction_set_from_pset_spec1 Y μ Y' -> Y' ≠ ∅ -> exists X', X ⟹{μ} X'.
Proof.
  intros. eapply reverse_trace_inclusion;eauto. 
  intros q mem. eapply H1 in mem as (q' & mem & tr).
  eapply lts_to_wt in tr. eauto.
Qed.

Lemma reverse_trace_inclusion_lts
  (X : gset P) (Y Y' : gset Q) μ
  : X ≼ₛₑₜ_ₐₛ Y -> (forall p, p ∈ X -> p ⇓ [μ]) ->
    Y ⟹{μ} Y' -> exists X', X ⟹{μ} X'.
Proof.
  intros. eapply reverse_trace_inclusion;eauto. intros q mem.
  eapply wk_tr_inv in H1 as (q'' & wt_tr & mem'); eauto.
  intro. subst. eapply empty_set_stable_wk_not_emp_list_inv;eauto.
Qed.

Lemma reverse_trace_inclusion_tr_lts
  (X : gset P) (Y Y' : gset Q) μ
  : X ≼ₛₑₜ_ₐₛ Y -> (forall p, p ∈ X -> p ⇓ [μ]) ->
    Y ⟶[μ] Y' -> exists X', X ⟹{μ} X'.
Proof.
  intros. eapply reverse_trace_inclusion_lts ;eauto.
  eapply lts_to_wt; eauto.
Qed.

Lemma communication_enabled (p : P) p' (q : Q) (t : T) t' μ :
      p ⟶[co μ] p'-> t ⟶[μ] t' -> ⌈ (𝝳P ∘ Φ) ⌉ (coR p) ⊆ ⌈ (𝝳Q ∘ Φ) ⌉ (coR q)
        -> exists μ' q' t'', q ⟶[co μ'] q'/\ t ⟶[μ'] t''.
Proof.
  intros tr tr_co sub.
  destruct (decide (non_blocking μ)) as [nb | not_nb].
  + eapply (co_non_blocking_enabled q μ) in nb as (q' & tr'); eauto.
    symmetry. exact (proj2_sig(exists_dual μ)).
  + assert (μ ∈ coR p) as some_co_action_of_p.
    { exists (co μ). repeat split; eauto.
      eapply lts_refuses_spec2;eauto.
      symmetry. exact (proj2_sig(exists_dual μ)). }
    eapply (map_gamma_of_action (𝝳P ∘ Φ)) in some_co_action_of_p as mem.
    eapply sub in mem. destruct mem as (μ' & mem & eq).
    
    assert ((𝝳Q ∘ Φ) μ' ∈ ⌈ 𝝳P ∘ Φ ⌉ coR p) as Hyp.
    { rewrite<- eq. eapply (map_gamma_of_action);eauto. }
    assert ((𝝳Q ∘ Φ) μ' ∈ ⌈ 𝝳P ∘ Φ ⌉ coR p) as Hyp';eauto.
    destruct Hyp as (μ'' & tr' & eq').
    assert ((𝝳P ∘ Φ) μ = (𝝳P ∘ Φ) μ'').
    { etrans. eauto. eauto. }
    assert (Φ μ ∈ ⌈ Φ ⌉ coR p).
    { eapply (map_gamma_of_action Φ). eauto. }
    assert (blocking μ'').
    { destruct tr' as (μ'''' & not_stable & duo & b);eauto. }
    eapply (abstraction_prog_spec p) in H ;eauto.
    
    
  (* intros tr tr_co sub.
  destruct (decide (non_blocking μ)) as [nb | not_nb].
  + eapply (co_non_blocking_enabled q μ) in nb as (q' & tr'); eauto.
    symmetry. exact (proj2_sig(exists_dual μ)).
  + assert (μ ∈ coR p) as some_co_action_of_p.
    { exists (co μ). repeat split; eauto.
      eapply lts_refuses_spec2;eauto.
      symmetry. exact (proj2_sig(exists_dual μ)). }
    eapply (map_gamma_of_action (𝝳 ∘ Φ)) in some_co_action_of_p as mem.
    eapply sub in mem. destruct mem as (μ' & mem & eq).
    eapply (map_gamma_of_action Φ) in mem as eq'. symmetry in eq.
    (* The next line uses a property of delta *)
    eapply (abstraction_prog_spec q) in eq' ;eauto.
    destruct eq' as (μ'' & mem' & eq'). destruct mem' as (μ''' & tr' & duo & b).
    (* The next line uses the property of phi *)
    assert (μ'' ∈ R t) as Tr_Test.
    { eapply abstraction_test_spec in eq';eauto. apply lts_refuses_spec2. eauto. }
    eapply lts_refuses_spec1 in Tr_Test as (t'' & Tr'').
    eapply lts_refuses_spec1 in tr' as (q' & tr').
    exists μ''. exists q'. exists t''. split ;eauto.
    eapply unique_nb in duo. subst. rewrite<- dual_is_involutive.
    exact tr'. destruct mem as (μ'' & Tr'' & duo & nb). exact nb. *)
Admitted.

End Acceptance_Set_preorder_for_sets.


Section SoundnessAS.

Context `{EA : !ExtAction A}.
Context `{gLtsEqT : !gLtsEq T EA}.
Context `{TP : @Testing_Predicate T A EA outcome _}.

Context `{gLtsP : @gLts P A EA, !FiniteImagegLts P A}.
Context `{!Prop_of_Inter P T A dual}.
Context `{gLtsQ : @gLts Q A EA, !FiniteImagegLts Q A, !gLtsCNenabled Q A}.
Context `{!Prop_of_Inter Q T A dual}.

Context `{AbsPT : @AbsAction P T FinA PreAct A EA Φ 𝝳P _ _}.
Context `{AbsQT : @AbsAction Q T FinA PreAct A EA Φ 𝝳Q _ _}.

Lemma unoutcome_must_st_nleqx (X : gset P) (Y : gset Q) (t : T):
  ¬ outcome t
    -> X must_pass_x t
      -> (∃ q, q ∈ Y /\ (q, t) ↛)
        -> ¬ X ₂≼ₛₑₜ_ₐₛ Y.
Proof.
  intros not_happy all_must (q & mem' & refuses_tau_q) hbhv2.

  assert (q ↛) as stable_q.
  { destruct (lts_refuses_decidable q τ) as [refuses_q | not_refuses_q].
    - exact refuses_q.
    - exfalso. eapply lts_refuses_spec1 in not_refuses_q as (q' & l).
      eapply (lts_refuses_spec2 (q ▷ t)); eauto. exists (q' ▷ t). eapply ParLeft. exact l. }

  assert (htX : ∀ p : P, p ∈ X → p ⇓ []).
  { destruct (mustx_terminate_unoutcome X t all_must) as [|htps]; eauto with mdb. contradiction. }

  destruct (hbhv2 q [] q mem' (wt_nil q) stable_q htX) as (p & mem & p' & wp & stp' & sub).

  assert (mustx {[ p' ]} t) as must_p'.
  { eapply (wt_nil_mx p). eapply (mx_sub X t all_must). set_solver. eassumption. }

  destruct must_p'; eauto.
  edestruct (ex p') as ((p'' , t'') & HypTr). now eapply elem_of_singleton.

  inversion HypTr as [? ? ? ? tau_left | ? ? ? ? tau_right | ? ? ? ? ? ? ? act_left act_right]; subst.
  - eapply lts_refuses_spec2 in stp'; eauto.
  - destruct (lts_refuses_decidable t τ) as [refuses_t | not_refuses_t].
    + eapply lts_refuses_spec2 in refuses_t. eauto. eauto with mdb.
    + eapply (lts_refuses_spec2 (q ▷ t)); eauto.
      exists (q , t''). eapply ParRight; eauto.
  - assert (μ1 = co μ2). { eapply unique_nb; eauto. symmetry; eauto. } subst.
    eapply communication_enabled in act_left as (μ'1 & q' & t''' & tr1 & tr2); eauto.
    eapply (lts_refuses_spec2 (q ▷ t)); eauto. exists (q', t''').
    eapply (ParSync (co μ'1)); eauto. symmetry. exact (proj2_sig(exists_dual μ'1)).
Qed.

Lemma stability_nbhvleqtwo
  (X : gset P) (Y : gset Q) t :
  ¬ outcome t
    -> X must_pass_x t
      -> X ₂≼ₛₑₜ_ₐₛ Y
        -> forall (q : Q), q ∈ Y -> ∃ q', (q, t) ⟶{τ} q'.
Proof.
  intros nhg hmx hleq q mem.
  destruct (lts_refuses_decidable (q, t) τ).
  - exfalso. apply (unoutcome_must_st_nleqx X Y t nhg hmx); eauto.
  - eapply lts_refuses_spec1 in n as (t' & hl). eauto.
Qed.



(** ** Soundness for sets *)
Lemma soundnessx
  (X : gset P) (Y : gset Q) :
  X ≼ₛₑₜ_ₐₛ Y  -> X ⊑ₛₑₜ_ₘᵤₛₜᵢ Y.
Proof.
  intros (halt1 & halt2) t hmx. revert Y halt1 halt2.
  dependent induction hmx; intros.
  - eauto with mdb.
  - destruct (mustx_terminate_unoutcome X t ltac:(eauto with mdb));
    [contradiction|].
    assert (q_conv : Y ⤓).
    eapply cnv_terminate , convergence_set_if_convergence_forall , halt1; intros; eapply cnv_nil.
    destruct (mustx_terminate_unoutcome X t); eauto with mdb.
    induction q_conv as [q tq IHq_conv].
    eapply mx_step.
    + eassumption.
    + eapply (stability_nbhvleqtwo X); eauto with mdb.
    + intros q' l not_empty. eapply IHq_conv.
      * eassumption.
      * eapply bhvleqone_preserved_by_reduction;eauto.
      * eapply bhvx_preserved_by_reduction;eauto.
        split ;eauto.
    + intros e' hle. eapply H0; eauto with mdb.
    + intros t' μ μ' q' inter lt lq.
      destruct (decide (outcome t')).
      * eapply mx_now_alt. assumption.
      * assert (HA : forall p, p ∈ X -> p ⇓ [μ]).
        { intros; eapply unoutcome_acnv_mu; eauto with mdb. }
        set (ts := wt_s_set_from_pset X [μ] HA).
        set (ts_spec := wt_s_set_from_pset_ispec X [μ] HA).
        assert ((exists p, p ∈ ts) \/ ts ≡ ∅)%stdpp as [neq_nil | eq_nil]
          by (eapply set_choose_or_empty).
        -- eapply H1; eauto with mdb.
           ++ destruct ts_spec; eauto with mdb. admit.
(*            ++ intro eq_nil. destruct neq_nil as (t'' & mem).
              replace ts with (wt_s_set_from_pset X [μ] HA) in mem; eauto.
              subst. rewrite eq_nil in mem. inversion mem. *)
           ++ eapply bhvleqone_preserved_by_external_action. eauto. ; eauto with mdb.
           ++ eapply bhvx_preserved_by_external_action; eauto with mdb.
              split; eauto.
        -- edestruct (reverse_trace_inclusion X q q' (μ)) as (X' & u); eauto.
           split; eauto.
           --- (* eassumption. *) admit.
           --- assert (X' ⊆ ts) as mem.
               { admit. }
               
               (* { d edestruct (u X' ltac:(set_solver)) as (r & mem & hw).
             eapply ts_spec; eauto. }
           set_solver. *)
Admitted.

(** ** Soundness for sets *)
Lemma soundnessx
  (X : gset P) (Y : gset Q) :
  X ≼ₛₑₜ_ₐₛ Y  -> X ⊑ₛₑₜ_ₘᵤₛₜᵢ Y.
Proof.
  intros (halt1 & halt2) t hmx. revert Y halt1 halt2.
  dependent induction hmx; intros.
  - eauto with mdb.
  - destruct (mustx_terminate_unoutcome X t ltac:(eauto with mdb));
    [contradiction|].
    assert (q_conv : Y ⤓).
    eapply cnv_terminate , convergence_set_if_convergence_forall , halt1; intros; eapply cnv_nil.
    destruct (mustx_terminate_unoutcome X t); eauto with mdb.
    induction q_conv as [q tq IHq_conv].
    eapply mx_step.
    + eassumption.
    + eapply (stability_nbhvleqtwo X); eauto with mdb.
    + intros q' l not_empty. eapply IHq_conv.
      * (* eassumption. *) admit.
      * eapply bhvleqone_preserved_by_reduction;eauto. (* eassumption. *) admit.
      * eapply bhvx_preserved_by_reduction;eauto.
        -- (* eassumption. *) admit.
        -- split ;eauto.
    + intros e' hle. eapply H0; eauto with mdb.
    + intros t' μ μ' q' inter lt lq not_empty.
      destruct (decide (outcome t')).
      * eapply mx_now. assumption.
      * assert (HA : forall p, p ∈ X -> p ⇓ [μ]).
        { intros; eapply unoutcome_acnv_mu; eauto with mdb. }
        set (ts := wt_s_set_from_pset X [μ] HA).
        set (ts_spec := wt_s_set_from_pset_ispec X [μ] HA).
        assert ((exists p, p ∈ ts) \/ ts ≡ ∅)%stdpp as [neq_nil | eq_nil]
          by (eapply set_choose_or_empty).
        -- eapply H1; eauto with mdb.
           ++ destruct ts_spec; eauto with mdb.
           ++ intro eq_nil. destruct neq_nil as (t'' & mem).
              replace ts with (wt_s_set_from_pset X [μ] HA) in mem; eauto.
              subst. rewrite eq_nil in mem. inversion mem.
           ++ eapply bhvleqone_preserved_by_external_action; eauto with mdb.
              (* eassumption. *) admit.
           ++ eapply bhvx_preserved_by_external_action; eauto with mdb.
              --- (* eassumption. *) admit.
              --- split; eauto.
        -- edestruct (reverse_trace_inclusion X q q' (μ)) as (X' & u); eauto.
           split; eauto.
           --- (* eassumption. *) admit.
           --- assert (X' ⊆ ts) as mem.
               { admit. }
               
               (* { d edestruct (u X' ltac:(set_solver)) as (r & mem & hw).
             eapply ts_spec; eauto. }
           set_solver. *)
Admitted.

End SoundnessAS.

Lemma soundness_co_nb_enabled `{
  gLtsEqP : @gLtsEq P A H, !FiniteImagegLts P A,
  gLtsQ : !gLtsEq Q H, !gLtsCNenabled Q A, !FiniteImagegLts Q A,
  gLtsT : !gLtsEq T H, !Testing_Predicate outcome _}
  
  `{AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳 _ _ }
  `{AbsQT : @AbsAction Q T FinA PreAct A H Φ 𝝳 _ _ }

  `{!Prop_of_Inter P T A dual}
  `{!Prop_of_Inter Q T A dual}

  (p : P) (q : Q) : p ≼ₐₛ q -> p ⊑ₘᵤₛₜᵢ q.
Proof.
  intros halt e hm.
  eapply must_set_iff_must.
  eapply (soundnessx ({[p]} : gset P)).
  now eapply alt_set_singleton_iff.
  now eapply must_set_iff_must.
Qed.


Lemma soundness_fw `{
  gLtsEqP : @gLtsEq P A H, !FiniteImagegLts P A,
  gLtsEqQ : @gLtsEq Q A H, !FiniteImagegLts Q A, gLtsObaQ : !gLtsOba Q, !gLtsObaFW Q A,
  gLtsT : !gLtsEq T H, !Testing_Predicate outcome _}

  `{AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳 _ _ }
  `{AbsQT : @AbsAction Q T FinA PreAct A H Φ 𝝳 _ _ }

  `{!Prop_of_Inter P T A dual}
  `{!Prop_of_Inter Q T A dual}

  (p : P) (q : Q) : p ≼ₐₛ q -> p ⊑ₘᵤₛₜᵢ q.
Proof.
  eapply soundness_co_nb_enabled.
  (* FW is co-non-blocking enabled *)
  Unshelve.
  eapply MkgLtsCNenabled. intros.
  destruct (lts_oba_fw_forward p1 η β) as (t & l1 & l2) ; eauto.
Qed.

(** ** Soundness for LTSs that can be lifted to forwarders *)
Lemma soundness 
  `{@gLtsObaFB P A H gLtsEqP gLtsObaP, !FiniteOutputChain_LtsOba P, !FiniteImagegLts P A}
  `{@gLtsObaFB Q A H gLtsEqQ gLtsObaQ, !FiniteOutputChain_LtsOba Q, !FiniteImagegLts Q A}
  `{@gLtsObaFB T A H gLtsEqT gLtsObaT, !FiniteOutputChain_LtsOba T, !FiniteImagegLts T A}

  `{ !Testing_Predicate outcome _}

  {_ : Prop_of_Inter P T A dual}
  {_ : Prop_of_Inter Q T A dual}

  {_ : @Prop_of_Inter P (mb A) A fw_inter H _ MbgLts}
  {_ : @Prop_of_Inter (P * mb A) T A dual H (inter_lts fw_inter) _}

  {_ : @Prop_of_Inter Q (mb A) A fw_inter H _ MbgLts}
  {_ : @Prop_of_Inter (Q * mb A) T A dual H (inter_lts fw_inter) _}

  `{AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳 _ _ }
  `{AbsQT : @AbsAction Q T FinA PreAct A H Φ 𝝳 _ _ }

  (p : P) (q : Q) : p ▷ ∅ ≼ₐₛ q ▷ ∅ -> p ⊑ₘᵤₛₜᵢ q.
Proof.
  intros halt t hm.
  eapply Lift.must_iff_must_fw in hm.
  eapply Lift.must_iff_must_fw.
  now eapply (soundness_fw (p ▷ ∅) (q ▷ ∅)).
Qed.



