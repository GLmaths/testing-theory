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

From Must Require Import gLts Bisimulation Lts_OBA Lts_FW Lts_OBA_FB
      Must Subset_Act InteractionBetweenLts ParallelLTSConstruction ForwarderConstruction MultisetLTSConstruction
      Termination Convergence FiniteImageLTS WeakTransitions Lift Testing_Predicate DefinitionAS.
From Must Require Import ActTau.

(* ************************************************************ *)

Inductive mustx `{
  gLtsP : gLts P, !FiniteImagegLts P A, 
  gLtsT : !gLts T EA, !gLtsEq T EA, !Testing_Predicate T A outcome}

  `{Prop_of_Inter P T A dual}

  (ps : gset P) (t : T) : Prop :=
| mx_now (hh : outcome t) : mustx ps t
| mx_step
    (nh : ¬ outcome t)
    (ex : forall (p : P), p ∈ ps -> ∃ p', inter_step (p, t) τ p')
    (pt : forall ps',
        lts_tau_set_from_pset_spec1 ps ps' -> ps' ≠ ∅ ->
        mustx ps' t)
    (et : forall (t' : T), t ⟶ t' -> mustx ps t')
    (com : forall (t' : T) μ1 μ2 (ps' : gset P),
        dual μ1 μ2 ->
        lts_step t (ActExt μ2) t' ->
        wt_set_from_pset_spec1 ps [μ1] ps' -> 
        ps' ≠ ∅ ->
        mustx ps' t')
  : mustx ps t.

#[global] Hint Constructors mustx:mdb.

Notation "X 'must_pass_x' t" := (mustx X t) (at level 70).

Lemma mx_sub `{
  gLtsP : gLts P, !FiniteImagegLts P A,
  gLtsT : !gLts T EA, !gLtsEq T EA, !Testing_Predicate T A outcome}

  `{!Prop_of_Inter P T A dual}

  ps t : 
  mustx ps t 
    -> forall qs, qs ⊆ ps 
      -> mustx qs t.
Proof.
  intros hmx. dependent induction hmx.
  - eauto with mdb.
  - intros qs sub.
    eapply mx_step; eauto with mdb.
    + intros qs' hs hneq_nil.
      set (ps' := lts_tau_set_from_pset_ispec ps).
      destruct ps'.
      eapply H; eauto with mdb.
      ++ destruct (set_choose_or_empty qs') as [(q' & l'%hs)|].
         intro eq_nil. destruct l' as (q & mem%sub & l%H3); set_solver.
         set_solver.
      ++ intros p (q & mem%sub & l)%hs. eauto.
    + intros t' μ μ' qs' hle duo hwqs hneq_nil.
      eapply (H1 t' μ μ'); eauto. intros p' mem%hwqs. set_solver.
Qed.

Lemma mx_mem `{
  gLtsP : gLts P, !FiniteImagegLts P A,
  gLtsT : !gLts T EA, !gLtsEq T EA, !Testing_Predicate T A outcome} 

  `{!Prop_of_Inter P T A dual}

  ps t : 
  mustx ps t 
    -> forall p, p ∈ ps 
      -> mustx {[ p ]} t.
Proof. intros hmx p mem. eapply mx_sub; set_solver. Qed.

Lemma lem_dec `{Countable A} (X Y Z : gset A) :
    X ⊆ Y ∪ Z 
      -> exists Y' Z', Y' ⊆ Y /\ Z' ⊆ Z /\ (Y' ∪ Z' ≡ X)%stdpp.
Proof.
  induction X using set_ind_L; intros sub.
  - exists ∅, ∅. set_solver.
  - assert (sub0 : X ⊆ Y ∪ Z) by set_solver.
    destruct (IHX sub0) as (Y0 & Z0 & sub1 & sub2 & eq).
    assert (mem_dec : x ∈ Y \/ x ∈ Z). set_solver.
    destruct mem_dec.
    + exists ({[x]} ∪ Y0), Z0. set_solver.
    + exists Y0, ({[x]} ∪ Z0). set_solver.
Qed.

Lemma mustx_terminate_unoutcome `{
  gLtsP : gLts P, !FiniteImagegLts P A,
  gLtsT : !gLts T EA, !gLtsEq T EA, !Testing_Predicate T A outcome}

  `{!Prop_of_Inter P T A dual}

  ps t : 
  mustx ps t 
    -> outcome t \/ forall p, p ∈ ps -> p ⤓.
Proof.
  intros hmx.
  induction hmx.
  - now left.
  - right.
    intros p mem.
    eapply tstep. intros p' l.
    edestruct (H {[p']}); [exists p; set_solver| | |]; set_solver.
Qed.

Lemma mustx_terminate_unoutcome' `{
  gLtsP : gLts P, !FiniteImagegLts P A, 
  gLtsT : !gLts T EA, !gLtsEq T EA, !Testing_Predicate T A outcome}

  `{!Prop_of_Inter P T A dual}

  ps (t : T) :
  mustx ps t
        -> ¬ outcome t -> forall p, p ∈ ps -> p ⤓.
Proof.
  intros hmx not_happy p mem.
  dependent induction hmx.
  + contradiction.
  + eapply tstep.
    intros q tr. eapply H; eauto.
    assert (h1 : lts_tau_set_from_pset_spec1 ps {[q]}).
    exists p. assert (q0 = q);subst. set_solver. split; eauto. eauto.
    set_solver. set_solver.
Qed.

Lemma unoutcome_acnv_mu `{
  gLtsP : gLts P, !FiniteImagegLts P A, 
  gLtsT : !gLts T EA, !gLtsEq T EA, !Testing_Predicate T A outcome}

  `{!Prop_of_Inter P T A dual}

  ps t t' :
  mustx ps t 
    -> forall μ μ' p, p ∈ ps 
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
      assert (h1 : wt_set_from_pset_spec1 ps [μ] {[q]}).
      exists p. split; set_solver.
      assert (h2 : {[q]} ≠ (∅ : gset P)) by set_solver.
      set (hm := com t' μ μ' {[ q ]} inter l h1 h2).
      destruct (mustx_terminate_unoutcome _ _ hm).
      +++ contradiction.
      +++ eapply cnv_nil. eapply H3. set_solver.
Qed.

Lemma must_mu_either_outcome_cnv `{
  gLtsP : gLts P, !FiniteImagegLts P A, 
  gLtsT : !gLts T EA, !gLtsEq T EA, !Testing_Predicate T A outcome}

  `{!Prop_of_Inter P T A dual}

  ps t t' :
  mustx ps t
    -> forall μ μ' p, p ∈ ps 
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
Lemma mx_sum `{
  gLtsP : gLts P A, !FiniteImagegLts P A, 
  gLtsT : !gLts T EA, !gLtsEq T EA, !Testing_Predicate T A outcome}

  `{!Prop_of_Inter P T A dual}

  ps1 ps2 t : mustx ps1 t 
    -> mustx ps2 t
      -> mustx (ps1 ∪ ps2) t.
Proof.
  intros hmx1 hmx2. revert ps2 hmx2.
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
    set (Y := lts_tau_set_from_pset ps).
    set (Z := lts_tau_set_from_pset ps2).
    assert (ps' ⊆ lts_tau_set_from_pset ps ∪ lts_tau_set_from_pset ps2).
    intros q mem. eapply H2 in mem as (q0 & mem & l).
    eapply elem_of_union in mem. destruct mem.
    eapply elem_of_union. left. eapply lts_tau_set_from_pset_ispec; eassumption.
    eapply elem_of_union. right. eapply lts_tau_set_from_pset_ispec; eassumption.
    eapply lem_dec in H4 as (Y' & Z' & Y_spec' & Z_spec' & eq).
    remember Y' as Y_'.
    remember Z' as Z_'.
    destruct Y_' using set_ind_L.
    + destruct Z_' using set_ind_L.
      ++ exfalso.
         assert (exists p, p ∈ ps') as (p & mem).
         destruct ps' using set_ind_L. contradiction.
         exists x. set_solver.
         eapply H2 in mem as (p0 & mem & l).
         eapply elem_of_union in mem. destruct mem.
         eapply lts_tau_set_from_pset_ispec in l; set_solver.
         eapply lts_tau_set_from_pset_ispec in l; set_solver.
      ++ assert (Y' = ∅) by set_solver.
         assert (Z' = ps') by set_solver. subst.
         inversion hmx2; subst. set_solver.
         eapply pt0. intros t' mem. eapply lts_tau_set_from_pset_ispec. set_solver. set_solver.
    + destruct Z_' using set_ind_L.
      ++ assert (Y' = ps') by set_solver.
         assert (mustx ps t) by eauto with mdb.
         inversion H6; subst. set_solver.
         eapply pt0. intros t' mem. eapply lts_tau_set_from_pset_ispec. set_solver. set_solver.
      ++ subst.
         replace ps' with (({[x]} ∪ X) ∪ ({[x0]} ∪ X0)) by set_solver.
         eapply H.
         intros t' mem. apply lts_tau_set_from_pset_ispec. set_solver. set_solver.
         inversion hmx2; subst. now contradiction nh.
         eapply pt0.
         intros t' mem. eapply lts_tau_set_from_pset_ispec. set_solver. set_solver.
  - intros t' l. eapply H0; eauto with mdb.
    inversion hmx2; subst; eauto with mdb. contradiction.
  - intros t' μ μ' ps' duo l ps'_spec neq_nil.
    destruct (outcome_decidable t'); eauto with mdb.
    assert (HAps : forall p, p ∈ ps -> p ⇓ [μ]).
    intros p0 mem0.
    eapply cnv_act. edestruct (mustx_terminate_unoutcome ps); eauto with mdb.
    contradiction.
    intros p' hw. eapply cnv_nil.
    edestruct (mustx_terminate_unoutcome {[p']}). eapply com; eauto.
    intros j memj. eapply elem_of_singleton_1 in memj. subst.
    exists p0. split; eauto. set_solver.
    set_solver.
    set (Y := wt_s_set_from_pset ps [μ] HAps).
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
         destruct mem; eapply (wt_s_set_from_pset_ispec ps [μ] HAps) in l'; set_solver.
      ++ inversion hmx2; subst. now contradict nh.
         eapply com0. eassumption. eassumption. intros t'' mem.
         eapply (wt_s_set_from_pset_ispec ps2 [μ] HAX2).
         set_solver. set_solver.
    + destruct Z0 using set_ind_L.
      ++ inversion hmx2; subst. now contradict nh.
         eapply com. eassumption. eassumption. intros t'' mem.
         eapply (wt_s_set_from_pset_ispec ps [μ] HAps).
         set_solver. set_solver.
      ++ replace ps' with (({[x]} ∪ X) ∪ ({[x0]} ∪ X0)) by set_solver.
         eapply H1; eauto with mdb.
         intros t'' mem.
         eapply (wt_s_set_from_pset_ispec ps [μ] HAps).
         set_solver. set_solver.
         inversion hmx2; subst. now contradict nh.
         eapply com0. eassumption. eassumption.
         intros t'' mem.
         eapply (wt_s_set_from_pset_ispec ps2 [μ] HAX2).
         set_solver. set_solver.
Qed.

Lemma mx_forall `{
  gLtsP : gLts P, !FiniteImagegLts P A,
  gLtsT : !gLts T EA, !gLtsEq T EA, !Testing_Predicate T A outcome} 

  `{!Prop_of_Inter P T A dual}

  ps t :
  ps ≠ ∅ 
    -> (forall p, p ∈ ps -> mustx {[p]} t) 
      -> mustx ps t.
Proof.
  intros neq_nil hm.
  induction ps using set_ind_L.
  - set_solver.
  - destruct (set_choose_or_empty X).
    eapply mx_sum; set_solver.
    assert (X = ∅) by set_solver.
    rewrite H1, union_empty_r_L. set_solver.
Qed.

Lemma wt_nil_mx `{
  gLtsP : gLts P, !FiniteImagegLts P A,
  gLtsT : !gLts T EA, !gLtsEq T EA, !Testing_Predicate T A outcome}

  `{!Prop_of_Inter P T A dual} :

  forall p1 p2 e, mustx {[ p1 ]} e 
    -> p1 ⟹ p2 -> mustx {[ p2 ]} e.
Proof.
  intros p1 p2 e hmx wt.
  dependent induction wt; subst; eauto with mdb.
  inversion hmx; subst; eauto with mdb.
  eapply IHwt; eauto with mdb.
  eapply pt; eauto with mdb.
  intros p2 mem. replace q with p2 in * by set_solver.
  exists p; set_solver.
Qed.

Lemma wt_mu_mx `{
  gLtsP : gLts P A, !FiniteImagegLts P A,
  gLtsT : !gLts T EA, !gLtsEq T EA, !Testing_Predicate T A outcome}

  `{!Prop_of_Inter P T A dual}

  p1 p2 t t' μ μ':
  dual μ μ' -> ¬ outcome t -> mustx {[ p1 ]} t 
    -> t ⟶[μ'] t' -> p1 ⟹{μ} p2 -> mustx {[p2]} t'.
Proof.
  intros duo nh hmx l w.
  inversion hmx; subst.
  - contradiction.
  - eapply com; eauto with mdb. exists p1. set_solver.
Qed.

Lemma must_set_if_must `{
  gLtsP : gLts P, !FiniteImagegLts P A, 
  gLtsT : !gLtsEq T EA, !Testing_Predicate T A outcome}

  `{!Prop_of_Inter P T A dual}

  (p : P) (t : T) : p must_pass t -> mustx {[ p ]} t.
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

Lemma must_if_must_set_helper `{
  gLtsP : gLts P, !FiniteImagegLts P A,
  gLtsT : !gLtsEq T EA, !Testing_Predicate T A outcome}

  `{!Prop_of_Inter P T A dual}

  (ps : gset P) (t : T) : 
  mustx ps t 
    -> forall p, p ∈ ps 
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
      eapply elem_of_list_to_set, elem_of_list_fmap; eauto.
      exists (dexist p' hlp). split. eauto. eapply elem_of_enum.
      eapply (H1 e' μ μ' X'). eassumption. eassumption.
      intros p0 mem0%elem_of_list_to_set.
      eapply elem_of_list_fmap in mem0 as ((r & l) & eq & mem'). subst.
      exists p. split; eauto.
      eapply wt_act.
      eapply bool_decide_unpack. eauto. eapply wt_nil. set_solver. set_solver.
Qed.

Lemma must_if_must_set `{
  gLtsP : gLts P, !FiniteImagegLts P A,
  gLtsT : !gLtsEq T EA, !Testing_Predicate T A outcome}

  `{!Prop_of_Inter P T A dual}

  (p : P) (t : T) : 
  mustx {[ p ]} t 
    -> p must_pass t.
Proof. intros. eapply must_if_must_set_helper; set_solver. Qed.

Lemma must_set_iff_must `{
  gLtsP : gLts P, !FiniteImagegLts P A,
  gLtsT : !gLtsEq T EA, !Testing_Predicate T A outcome}

  `{!Prop_of_Inter P T A dual}

  (p : P) (t : T) : 
  p must_pass t <-> mustx {[ p ]} t.
Proof. split; [eapply must_set_if_must | eapply must_if_must_set]. Qed.

Lemma must_set_for_all `{
  gLtsP : gLts P, !FiniteImagegLts P A,
  gLtsT : !gLtsEq T EA, !Testing_Predicate T A outcome}

  `{!Prop_of_Inter P T A dual}

  (X : gset P) (t : T) : 
  X ≠ ∅ 
    -> (forall p, p ∈ X -> p must_pass t) 
      -> mustx X t.
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

Lemma must_set_iff_must_for_all `{
  gLtsP : gLts P, !FiniteImagegLts P A,
  gLtsT : !gLtsEq T EA, !Testing_Predicate T A outcome}

  `{!Prop_of_Inter P T A dual}

  (X : gset P) (t : T) : 
  X ≠ ∅ -> (forall p, p ∈ X -> p must_pass t) <-> mustx X t.
Proof.
  intros.
  split. now eapply must_set_for_all.
  now eapply must_if_must_set_helper.
Qed.

Definition ctx_pre__x `{
  gLtsP : @gLts P A H, !FiniteImagegLts P A,
  gLtsQ : !gLts Q H, !FiniteImagegLts Q A,
  gLtsT : ! gLtsEq T H, !Testing_Predicate T A outcome}

  `{!Prop_of_Inter P T A dual}
  `{!Prop_of_Inter Q T A dual}

  (X : gset P) (Y : gset Q) 
  := forall (t : T), X must_pass_x t -> Y must_pass_x t.

Global Hint Unfold ctx_pre__x : mdb.

Notation "X ⊑ₛₑₜ_ₘᵤₛₜᵢ Y" := (ctx_pre__x X Y) (at level 70).
Notation "X ⋢ₛₑₜ_ₘᵤₛₜᵢ Y" := (¬ ctx_pre X Y) (at level 70).

Lemma must_set_singleton_iff `{
  gLtsP : @gLts P A H, !FiniteImagegLts P A,
  gLtsQ : !gLts Q H, !FiniteImagegLts Q A,
  gLtsT : ! gLtsEq T H, !Testing_Predicate T A outcome}

  `{!Prop_of_Inter P T A dual}
  `{!Prop_of_Inter Q T A dual}

  (p : P) (q : Q) : 
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

(**************************************************************)

Definition bhv_pre_cond1__x `{FiniteImagegLts P A, FiniteImagegLts Q A} (ps : gset P) (q : Q) :=
  forall s, (forall p, p ∈ ps -> p ⇓ s) -> q ⇓ s.

Notation "ps ≼ₓ1 q" := (bhv_pre_cond1__x ps q) (at level 70).

Definition bhv_pre_cond2__x `{
  @FiniteImagegLts P A H gLtsP, PreAP : @PreExtAction P A H FinA PreA PreA_eq PreA_countable 𝝳  Φ gLtsP,
  @FiniteImagegLts Q A H gLtsQ, PreAQ : @PreExtAction Q A H FinA PreA PreA_eq PreA_countable 𝝳  Φ gLtsQ}
  (ps : gset P) (q : Q) :=
  forall s q',
    q ⟹[s] q' -> q' ↛ ->
    (forall p, p ∈ ps -> p ⇓ s) ->
    exists p, p ∈ ps /\ exists p', p ⟹[s] p' /\ p' ↛ /\ (pre_co_actions_of p' ⊆ pre_co_actions_of q').

Notation "ps ≼ₓ2 q" := (bhv_pre_cond2__x ps q) (at level 70).

#[global] Hint Unfold bhv_pre_cond1__x bhv_pre_cond2__x : mdb.

Definition bhv_pre__x `{
  @FiniteImagegLts P A H gLtsP, PreAP : @PreExtAction P A H FinA PreA PreA_eq PreA_countable 𝝳  Φ gLtsP,
  @FiniteImagegLts Q A H gLtsQ, PreAQ : @PreExtAction Q A H FinA PreA PreA_eq PreA_countable 𝝳  Φ gLtsQ}
    (ps : gset P) (q : Q) := 
      (ps ≼ₓ1 q /\ ps ≼ₓ2 q).
(* ≼ₐₛ *)

Notation "ps ≼ₓ q" := (bhv_pre__x ps q) (at level 70).

Lemma alt_set_singleton_iff `{
  @FiniteImagegLts P A H gLtsP, PreAP : @PreExtAction P A H FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP,
  @FiniteImagegLts Q A H gLtsQ, PreAQ : @PreExtAction Q A H FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsQ}
  (p : P) (q : Q) : p ≼ₐₛ q <-> {[ p ]} ≼ₓ q.
Proof.
  split.
  - intros (hbhv1 & hbhv2). split.
    + intros s mem. eapply hbhv1. set_solver.
    + intros s q' w st hcnv. edestruct hbhv2; set_solver.
  - intros (h1 & h2). split.
    + intros s mem. eapply h1. set_solver.
    + intros s q' w st hcnv. edestruct h2 ; set_solver.
Qed.

Lemma bhvleqone_preserved_by_reduction `{
  @FiniteImagegLts P A H gLtsP, 
  @FiniteImagegLts Q A H gLtsQ} 
  (ps : gset P) (q q' : Q) :
  ps ≼ₓ1 q -> q ⟶ q' -> ps ≼ₓ1 q'.
Proof. intros halt1 l s mem. eapply cnv_preserved_by_lts_tau; eauto. Qed.

Lemma bhvx_preserved_by_reduction `{
  @FiniteImagegLts P A H gLtsP, PreAP : @PreExtAction P A H FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP,
  @FiniteImagegLts Q A H gLtsQ, PreAQ : @PreExtAction Q A H FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsQ}
  (ps : gset P) (q q' : Q) : q ⟶ q' -> ps ≼ₓ q -> ps ≼ₓ q'.
Proof.
  intros l (halt1 & halt2).
  split.
  - intros s mem. eapply cnv_preserved_by_lts_tau; eauto.
  - (* bhvleqone_preserved_by_reduction *)
    intros s q'' w st hcnv.
    destruct (halt2 s q'') as (p' & mem & p'' & hw & hst) (* & sub0) *); eauto with mdb.
Qed.

Lemma bhvleqone_preserved_by_external_action `{
  @FiniteImagegLts P A H gLtsP, 
  @FiniteImagegLts Q A H gLtsQ}
  (ps0 ps1 : gset P) μ (q q' : Q) (htp : forall p, p ∈ ps0 -> terminate p) :
  ps0 ≼ₓ1 q -> wt_set_from_pset_spec ps0 [μ] ps1  -> q ⟶[μ] q' -> ps1 ≼ₓ1 q'.
Proof.
  intros hleq hws l s hcnv.
  eapply cnv_preserved_by_wt_act.
  eapply hleq.
  intros p mem'. eapply cnv_act.
  + eapply htp; eauto.
  + intros. eapply hcnv, hws; eassumption.
  + eauto with mdb.
Qed.

Lemma bhvx_preserved_by_external_action `{
  @FiniteImagegLts P A H gLtsP, PreAP : @PreExtAction P A H FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP,
  @FiniteImagegLts Q A H gLtsQ, PreAQ : @PreExtAction Q A H FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsQ}
  (ps0 : gset P) (q : Q) μ ps1 q' (htp : forall p, p ∈ ps0 -> terminate p) :
  q ⟶[μ] q' 
    -> wt_set_from_pset_spec ps0 [μ] ps1 
      -> ps0 ≼ₓ q 
        -> ps1 ≼ₓ q'.
Proof.
  intros lts__q ps1_spec (halt1 & halt2). split.
  - eapply bhvleqone_preserved_by_external_action; eauto.
  - (* bhvleqtwo_preserved_by_reduction *)
    intros s q0 wt st hcnv.
    edestruct (halt2 (μ :: s) q0) as (t & mem & p0 & p1 & wta__t & sub); eauto with mdb.
    intros p' mem'. eapply cnv_act; eauto.
    intros p'' mem1. eapply hcnv, ps1_spec; eassumption.
    eapply wt_pop in p1 as (r & w1 & w2).
    exists r. repeat split. eapply ps1_spec; eassumption. eauto.
Qed.

Lemma reverse_trace_inclusion `{
  @FiniteImagegLts P A H gLtsP, PreAP : @PreExtAction P A H FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP,
  @FiniteImagegLts Q A H gLtsQ, PreAQ : @PreExtAction Q A H FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsQ}
  (ps : gset P) (q q' : Q) μ
  : ps ≼ₓ q -> (forall p, p ∈ ps -> p ⇓ [μ]) ->
    q ⟶[μ] q' -> exists p', wt_set_from_pset_spec1 ps [μ] {[ p' ]}.
Proof.
  intros (h1 & h2) hcnv hl.
  assert (exists q0, q ⟹{μ} q0 /\ q0 ↛) as (q0 & wq0 & stq0).
  assert (hqt : q' ⤓). eapply cnv_terminate, cnv_preserved_by_wt_act.
  eapply h1, hcnv. eauto with mdb.
  eapply terminate_then_wt_refuses in hqt as (q0 & w0 & st0).
  exists q0; eauto with mdb.
  destruct (h2 [μ] q0 wq0 stq0 hcnv) as (p1 & mem1 & p0 & wp0 & stp0) (* & subp0) *).
  exists p0. intros p1' mem. replace p1' with p0 by set_solver. eauto.
Qed.

Lemma unoutcome_must_st_nleqx `{
  gLtsEqP : @gLtsEq P A H, !FiniteImagegLts P A, gLtsObaP : !gLtsOba P, !gLtsObaFW P A,
  PreAP : !@PreExtAction P A H FinA PreA PreA_eq PreA_countable 𝝳 Φ _,
  gLtsEqQ : @gLtsEq Q A H, !FiniteImagegLts Q A, gLtsObaQ : !gLtsOba Q, !gLtsObaFW Q A,
  PreAQ : !@PreExtAction Q A H FinA PreA PreA_eq PreA_countable 𝝳 Φ _,
  gLtsT : !gLtsEq T H, !Testing_Predicate T A outcome}

  `{AbT : @AbsAction A H T FinA _ Φ}

  `{!Prop_of_Inter P T A dual}
  `{!Prop_of_Inter Q T A dual}

  (X : gset P) (q : Q) (t : T): 
  ¬ outcome t 
    -> mustx X t 
      -> (q, t) ↛
        -> ¬ X ≼ₓ2 q.
Proof.
  intros not_happy all_must refuses_tau_q hbhv2.

  assert (q ↛) as stable_q.
  { destruct (lts_refuses_decidable q τ) as [refuses_q | not_refuses_q].
    - exact refuses_q.
    - exfalso. eapply lts_refuses_spec1 in not_refuses_q as (q' & l).
      eapply (lts_refuses_spec2 (q ▷ t)); eauto. exists (q' ▷ t). eapply ParLeft. exact l. }

  assert (htX : ∀ p : P, p ∈ X → p ⇓ []).
  { destruct (mustx_terminate_unoutcome X t all_must) as [|htps]; eauto with mdb. contradiction. }

  destruct (hbhv2 [] q (wt_nil q) stable_q htX) as (p & mem & p' & wp & stp' & sub).

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
  - destruct (decide (non_blocking μ2)) as [nb | not_nb].
    + destruct (lts_oba_fw_forward q μ2 μ1) as (q'' & Hyp).
      eapply Hyp in nb as (tr1 & tr2); eauto.
      eapply (lts_refuses_spec2 (q ▷ t)); eauto. exists (q'', t'').
      eapply ParSync; eauto.
    + assert (μ2 ∈ co_actions_of p') as some_co_action_of_p.
      { exists μ1. repeat split; eauto.
        eapply lts_refuses_spec2;eauto. }
      (* The next line uses a property of delta *)
      eapply preactions_of_fin_test_spec1 in some_co_action_of_p.
      eapply preactions_of_spec in some_co_action_of_p.
      eapply sub in some_co_action_of_p.
      eapply preactions_of_spec in some_co_action_of_p.
      (* The next line uses a property of delta *)
      eapply preactions_of_fin_test_spec2 in some_co_action_of_p as (μ' & mem' & eq').
      destruct mem' as (μ'1 & Tr & duo & b).
      assert (¬ t ↛[μ']) as Tr_Test.
      (* The next line uses the property of phi *)
      { eapply abstraction_test_spec. exact not_nb. exact b. exact eq'. apply lts_refuses_spec2. eauto. }
      eapply lts_refuses_spec1 in Tr_Test as (t' & Tr').
      eapply lts_refuses_spec1 in Tr as (q' & Tr).
      eapply (lts_refuses_spec2 (q,t)). exists (q', t').
      eapply ParSync; eauto. eauto.
Qed.

Lemma stability_nbhvleqtwo `{
  gLtsEqP : @gLtsEq P A H, !FiniteImagegLts P A, gLtsObaP : !gLtsOba P, !gLtsObaFW P A,
  PreAP : !@PreExtAction P A H FinA PreA PreA_eq PreA_countable 𝝳 Φ _,
  gLtsEqQ : @gLtsEq Q A H, !FiniteImagegLts Q A, gLtsObaQ : !gLtsOba Q, !gLtsObaFW Q A,
  PreAQ : !@PreExtAction Q A H FinA PreA PreA_eq PreA_countable 𝝳 Φ _,
  gLtsT : !gLtsEq T H, !Testing_Predicate T A outcome}

  `{AbT : @AbsAction A H T FinA _ Φ}

  `{!Prop_of_Inter P T A dual}
  `{!Prop_of_Inter Q T A dual}

  (X : gset P) (q : Q) t : 
  ¬ outcome t 
    -> mustx X t
      -> X ≼ₓ2 q
        -> exists q', (q, t) ⟶{τ} q'.
Proof.
  intros nhg hmx hleq.
  destruct (lts_refuses_decidable (q, t) τ).
  - exfalso. apply (unoutcome_must_st_nleqx X q t nhg hmx); eauto.
  - eapply lts_refuses_spec1 in n as (t' & hl). eauto.
Qed.

Lemma soundnessx `{
  gLtsEqP : @gLtsEq P A H, !FiniteImagegLts P A, gLtsObaP : !gLtsOba P, !gLtsObaFW P A,
  PreAP : !@PreExtAction P A H FinA PreA PreA_eq PreA_countable 𝝳 Φ _,
  gLtsEqQ : @gLtsEq Q A H, !FiniteImagegLts Q A, gLtsObaQ : !gLtsOba Q, !gLtsObaFW Q A,
  PreAQ : !@PreExtAction Q A H FinA PreA PreA_eq PreA_countable 𝝳 Φ _,
  gLtsT : !gLtsEq T H, !Testing_Predicate T A outcome}

  `{AbT : @AbsAction A H T FinA _ Φ}

  `{!Prop_of_Inter P T A dual}
  `{!Prop_of_Inter Q T A dual}

  (ps : gset P) (t : T) : 
  mustx ps t 
    -> forall (q : Q), ps ≼ₓ q 
      -> q must_pass t.
Proof.
  intros hmx q (halt1 & halt2).
  dependent induction hmx.
  - eauto with mdb.
  - destruct (mustx_terminate_unoutcome ps t ltac:(eauto with mdb)).
    contradiction.
    assert (q_conv : q ⤓).
    eapply cnv_terminate, halt1; intros; eapply cnv_nil.
    destruct (mustx_terminate_unoutcome ps t); eauto with mdb.
    induction q_conv as [q tq IHq_conv].
    eapply m_step.
    + eassumption.
    + eapply (stability_nbhvleqtwo ps); eauto with mdb.
    + intros q' l. eapply IHq_conv.
      ++ eassumption.
      ++ eapply bhvleqone_preserved_by_reduction; eauto.
      ++ eauto with mdb.
    + intros e' hle. eapply H1; eassumption.
    + intros q' e' μ μ' inter le lq.
      destruct (decide (outcome e')).
      ++ eapply m_now. assumption.
      ++ assert (HA : forall p, p ∈ ps -> p ⇓ [μ]).
         intros; eapply unoutcome_acnv_mu; eauto with mdb.
         set (ts := wt_s_set_from_pset ps [μ] HA).
         set (ts_spec := wt_s_set_from_pset_ispec ps [μ] HA).
         assert ((exists p, p ∈ ts) \/ ts ≡ ∅)%stdpp as [neq_nil | eq_nil]
          by (eapply set_choose_or_empty).
         eapply H2; eauto with mdb.
         destruct ts_spec. eassumption.
         intro eq_nil. destruct neq_nil as (t' & mem).
         replace ts with (wt_s_set_from_pset ps [μ] HA) in mem; eauto.
         subst. rewrite eq_nil in mem. inversion mem.
         eapply bhvleqone_preserved_by_external_action; eauto with mdb.
         eapply bhvx_preserved_by_external_action; eauto with mdb. split; eauto.
         exfalso.
         edestruct (reverse_trace_inclusion ps q q' (μ)) as (p' & u); eauto. split; eauto.
         assert (p' ∈ ts) as mem.
         edestruct (u p' ltac:(set_solver)) as (r & mem & hw).
         eapply ts_spec; eauto.
         set_solver.
Qed.

Lemma soundness_fw `{
  gLtsEqP : @gLtsEq P A H, !FiniteImagegLts P A, gLtsObaP : !gLtsOba P, !gLtsObaFW P A,
  PreAP : !@PreExtAction P A H FinA PreA PreA_eq PreA_countable 𝝳 Φ _,
  gLtsEqQ : @gLtsEq Q A H, !FiniteImagegLts Q A, gLtsObaQ : !gLtsOba Q, !gLtsObaFW Q A,
  PreAQ : !@PreExtAction Q A H FinA PreA PreA_eq PreA_countable 𝝳 Φ _,
  gLtsT : !gLtsEq T H, !Testing_Predicate T A outcome}

  `{AbT : @AbsAction A H T FinA _ Φ}

  `{!Prop_of_Inter P T A dual}
  `{!Prop_of_Inter Q T A dual}

  (p : P) (q : Q) : p ≼ₐₛ q -> p ⊑ₘᵤₛₜᵢ q.
Proof.
  intros halt e hm.
  eapply (soundnessx {[p]}).
  now eapply must_set_iff_must. now eapply alt_set_singleton_iff.
Qed.

Lemma soundness 
  `{@gLtsObaFB P A H gLtsEqP gLtsObaP, !FiniteImagegLts P A}
  `{@gLtsObaFB Q A H gLtsEqQ gLtsObaQ, !FiniteImagegLts Q A}
  `{@gLtsObaFB T A H gLtsEqT gLtsObaT, !FiniteImagegLts T A}

  `{ !Testing_Predicate T A outcome }

  `{AbT : @AbsAction A H T FinA _ Φ}

  {_ : Prop_of_Inter P T A dual}
  {_ : Prop_of_Inter Q T A dual}

  {_ : @Prop_of_Inter P (mb A) A fw_inter H _ MbgLts}
  {_ : @Prop_of_Inter (P * mb A) T A dual H (inter_lts fw_inter) _}

  {_ : @Prop_of_Inter Q (mb A) A fw_inter H _ MbgLts}
  {_ : @Prop_of_Inter (Q * mb A) T A dual H (inter_lts fw_inter) _}

  `{PreAP : @PreExtAction (P * mb A) A H  FinA PreA PreA_eq PreA_countable 𝝳 Φ (inter_lts fw_inter),
    PreAQ : @PreExtAction (Q * mb A) A H  FinA PreA PreA_eq PreA_countable 𝝳 Φ (inter_lts fw_inter)}
  (p : P) (q : Q) : p ▷ ∅ ≼ₐₛ q ▷ ∅ -> p ⊑ₘᵤₛₜᵢ q.
Proof.
  intros halt t hm.
  eapply Lift.must_iff_must_fw in hm.
  eapply Lift.must_iff_must_fw.
  now eapply (soundness_fw (p ▷ ∅) (q ▷ ∅)).
Qed.
