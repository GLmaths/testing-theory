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

From Stdlib Require ssreflect Setoid.
From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From Stdlib.Program Require Import Wf Equality.
From Stdlib.Wellfounded Require Import Inverse_Image.

From stdpp Require Import base countable finite gmap list finite base decidable finite gmap.

From TestingTheory Require Import gLts Bisimulation Lts_OBA Lts_Finite_Output_Chain Lts_FW Lts_OBA_FB Lts_CN
      Must Subset_Act InteractionBetweenLts ParallelLTSConstruction ForwarderConstruction
      Termination Convergence WeakTransitions Lift Testing_Predicate DefinitionAS MultisetLTSConstruction.
From TestingTheory Require Import ActTau InFiniteSetHelper InListPropHelper.
From TestingTheory Require Import coWeakTransition coConvergence
      FiniteImageLTS coFiniteImage coSetLTSConstruction DefinitionASco.

(** * Soundness for the co-acceptance-set preorder *)


Inductive mustx `{EA : !ExtAction A} `{gLtsT : !gLtsEq T EA} `{TP : @Testing_Predicate T A EA outcome _}
  `{gLtsP : @gLts P A EA, !Countable P} {Hinter : @Prop_of_Inter P T A dual EA gLtsP _}
  (X : gset P) (t : T) : Prop :=
| mx_now (hh : outcome t) : mustx X t
| mx_step
    (nh : ¬ outcome t)
    (ex : forall (p : P), p ∈ X -> ∃ p', inter_step (p, t) τ p')
    (pt : forall X',
        lts_tau_set_from_pset_spec1 X X' -> X' ≠ ∅ ->
        mustx X' t)
    (et : forall (t' : T), t ⟶ t' -> mustx X t')
    (com : forall (t' : T) μ (X' : gset P),
        t ⟶[μ] t' ->
        cowt_set_from_pset_spec1 X μ X'->
        X' ≠ ∅ ->
        mustx X' t')
  : mustx X t.

#[global] Hint Constructors mustx:mdb.
Global Notation "X 'must_pass_x' t" := (mustx X t) (at level 70).

Section Must_for_sets.

Context `{EA : !ExtAction A}.
Context `{gLtsT : !gLtsEq T EA}.
Context `{TP : @Testing_Predicate T A EA outcome _}.
Context `{gLtsP : @gLts P A EA, !coFiniteImagegLts P A}.
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
      set (X' := cowt_tau_set_from_pset_ispec X).
      destruct X'.
      eapply H; eauto with mdb.
      ++ destruct (set_choose_or_empty qs') as [(q' & l'%hs)|].
         intro eq_nil. destruct l' as (q & mem%sub & l%H3); set_solver.
         set_solver.
      ++ intros p (q & mem%sub & l)%hs. eauto.
    + intros t' μ qs' hle hwqs hneq_nil.
      eapply (H1 t' μ); eauto. intros p' mem%hwqs. set_solver.
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
    -> forall μ p, p ∈ X
        -> t ⟶[μ] t'
          -> ¬ outcome t -> ¬ outcome t' -> p ⇓ᶜᵒ [μ].
Proof.
  intros hmx μ p mem l not_happy not_happy'.
  dependent induction hmx.
  - contradiction.
  - edestruct mustx_terminate_unoutcome as [happy | finish].
    + eauto with mdb.
    + contradiction.
    + edestruct mustx_terminate_unoutcome; eauto with mdb.
      * contradiction.
      * eapply cocnv_act.
        -- eauto.
        -- intros q w.
           assert (h1 : cowt_set_from_pset_spec1 X μ {[q]}).
           { exists p. split; set_solver. }
           assert (h2 : {[q]} ≠ (∅ : gset P)) by set_solver.
           set (hm := com t' μ {[ q ]} l h1 h2).
           destruct (mustx_terminate_unoutcome _ _ hm).
           +++ contradiction.
           +++ eapply cocnv_nil. eapply H3. set_solver.
Qed.

Lemma must_mu_either_outcome_cnv X t t' :
  X must_pass_x t
    -> forall μ p, p ∈ X
        -> t ⟶[μ] t'
          -> outcome t \/ outcome t' (* ajout par rapport à Input/Output *)
                       \/ p ⇓ᶜᵒ [μ].
Proof.
  intros hmx μ p mem l.
  destruct (decide (outcome t)); destruct (decide (outcome t')).
  + left; eauto.
  + left; eauto.
  + right; eauto.
  + right. right. eapply unoutcome_acnv_mu; eauto.
Qed.

(* to rework , why ?*)
Lemma mx_sum X X' t : X must_pass_x t
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
    set (Y := cowt_tau_set_from_pset X).
    set (Z := cowt_tau_set_from_pset ps2).
    assert (X' ⊆ cowt_tau_set_from_pset X ∪ cowt_tau_set_from_pset ps2).
    { intros q mem. eapply H2 in mem as (q0 & mem & l).
      eapply elem_of_union in mem. destruct mem.
      eapply elem_of_union. left. eapply cowt_tau_set_from_pset_ispec; eassumption.
      eapply elem_of_union. right. eapply cowt_tau_set_from_pset_ispec; eassumption. }
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
         eapply cowt_tau_set_from_pset_ispec in l; set_solver.
         eapply cowt_tau_set_from_pset_ispec in l; set_solver.
      ++ assert (Y' = ∅) by set_solver.
         assert (Z' = X') by set_solver. subst.
         inversion hmx2; subst. set_solver.
         eapply pt0. intros t' mem. eapply cowt_tau_set_from_pset_ispec. set_solver. set_solver.
    + destruct Z_' using set_ind_L.
      ++ assert (Y' = X') by set_solver.
         assert (mustx X t) by eauto with mdb.
         inversion H6; subst. set_solver.
         eapply pt0. intros t' mem. eapply cowt_tau_set_from_pset_ispec. set_solver. set_solver.
      ++ subst.
         replace X' with (({[x]} ∪ X0) ∪ ({[x0]} ∪ X1)) by set_solver.
         eapply H.
         +++ intros t' mem. apply cowt_tau_set_from_pset_ispec. set_solver.
         +++ set_solver.
         +++ inversion hmx2; subst.
             ++++ now contradiction nh.
             ++++ eapply pt0. intros t' mem. eapply cowt_tau_set_from_pset_ispec. set_solver. set_solver.
  - intros t' l. eapply H0; eauto with mdb.
    inversion hmx2; subst; eauto with mdb. contradiction.
  - intros t' μ ps' l ps'_spec neq_nil.
    destruct (outcome_decidable t'); eauto with mdb.
    assert (HAX : forall p, p ∈ X -> p ⇓ᶜᵒ [μ]).
    intros p0 mem0.
    eapply cocnv_act. edestruct (mustx_terminate_unoutcome X); eauto with mdb.
    contradiction.
    intros p' hw. eapply cocnv_nil.
    edestruct (mustx_terminate_unoutcome {[p']}). eapply com; eauto.
    intros j memj. eapply elem_of_singleton_1 in memj. subst.
    exists p0. split; eauto. set_solver.
    set_solver.
    set (Y := cowt_s_set_from_pset X μ HAX).
    assert (HAX2 : forall p, p ∈ ps2 -> p ⇓ᶜᵒ [μ]).
    intros p0 mem0.
    eapply cocnv_act. edestruct (mustx_terminate_unoutcome ps2); eauto with mdb.
    contradiction.
    intros p' hw. eapply cocnv_nil.
    edestruct (mustx_terminate_unoutcome {[p']}).
    inversion hmx2; subst. contradiction. eapply com0; eauto.
    intros j memj. eapply elem_of_singleton_1 in memj. subst.
    exists p0. split; eauto. set_solver. set_solver.
    set (Z := cowt_s_set_from_pset ps2 μ HAX2).
    assert (ps' ⊆ Y ∪ Z).
    intros q mem. eapply ps'_spec in mem as (q0 & mem & l').
    eapply elem_of_union in mem. destruct mem.
    eapply elem_of_union. left. eapply cowt_s_set_from_pset_ispec; eassumption.
    eapply elem_of_union. right. eapply cowt_s_set_from_pset_ispec; eassumption.
    eapply lem_dec in H2 as (Y0 & Z0 & Y_spec0 & Z_spec0 & eq).
    destruct Y0 using set_ind_L.
    + destruct Z0 using set_ind_L.
      ++ exfalso.
         assert (exists p, p ∈ ps') as (p & mem).
         destruct ps' using set_ind_L. contradiction.
         exists x. set_solver.
         eapply ps'_spec in mem as (p0 & mem & l').
         eapply elem_of_union in mem.
         destruct mem; eapply cowt_s_set_from_pset_ispec in l'; set_solver.
      ++ inversion hmx2; subst.
         +++ now contradict nh.
         +++ eapply com0. eassumption. intros t'' mem.
             eapply (cowt_s_set_from_pset_ispec ps2 μ HAX2).
             set_solver. set_solver.
             Unshelve.
             exact HAX.
             exact HAX2.
    + destruct Z0 using set_ind_L.
      ++ inversion hmx2; subst.
         +++ now contradict nh.
         +++ eapply com. eassumption. intros t'' mem.
             eapply (cowt_s_set_from_pset_ispec X μ HAX).
             set_solver. set_solver.
      ++ replace ps' with (({[x]} ∪ X0) ∪ ({[x0]} ∪ X1)) by set_solver.
         eapply H1; eauto with mdb.
         +++ intros t'' mem.
             eapply (cowt_s_set_from_pset_ispec X μ HAX).
             set_solver.
         +++ set_solver.
         +++ inversion hmx2; subst.
             ++++ now contradict nh.
             ++++ eapply com0. eassumption.
                  intros t'' mem.
                  eapply (cowt_s_set_from_pset_ispec ps2 μ HAX2).
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
    + eapply mx_sum.
      * eapply hm. set_solver.
      * eapply IHX.
        -- set_solver.
        -- intros. eapply hm. set_solver.
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

Lemma wt_nil_mx_set (X : gset P) (X' : gset P) t :
  X must_pass_x t
    -> wt_set_from_pset_spec1 X [] X' -> X' must_pass_x t.
Proof.
  intros hmx wt_tr.
  destruct (set_choose_or_empty X') as [(x'&mem)|Hemp].
  - eapply mx_forall.
    + set_solver.
    + intros p' mem'.
      eapply wt_tr in mem' as (p&mem''&w).
      eapply wt_nil_mx.
      * eapply mx_mem; eauto.
      * exact w.
  - assert (X' = ∅) by set_solver.
    subst.
    clear wt_tr.
    induction hmx.
    + now eapply mx_now.
    + eapply mx_step.
      * eassumption.
      * intros p mem.
        inversion mem.
      * intros Y hY hYne.
        exfalso. apply hYne.
        apply leibniz_equiv. intros y. split; [|set_solver].
        intros mem. eapply hY in mem as (p' & mem_imp & tr). set_solver.
      * intros t' l.
        eapply H0; eauto.
      * intros t' μ Y l hY hYne.
        exfalso. apply hYne.
        apply leibniz_equiv. intros y. split; [|set_solver].
        intros mem. eapply hY in mem as (p' & mem_imp & tr). set_solver.
Qed.

Lemma co_wt_mu_mx p1 p2 t t' μ :
  ¬ outcome t -> {[ p1 ]} must_pass_x t
    -> t ⟶[μ] t' -> p1 ⟹ᶜᵒ{μ} p2 -> {[p2]} must_pass_x t'.
Proof.
  intros nh hmx l w.
  inversion hmx; subst.
  - contradiction.
  - eapply com; eauto with mdb. exists p1. set_solver.
Qed.

Lemma wt_mu_mx_set X X' t t' μ :
  ¬ outcome t -> X must_pass_x t
    -> t ⟶[μ] t' -> cowt_set_from_pset_spec1 X μ X' -> X' ≠ ∅ -> X' must_pass_x t'.
Proof.
  intros nh hmx l w hne.
  inversion hmx; subst.
  - contradiction.
  - eapply com; eauto.
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
    + intros e' μ X' hle hws hneq_nil.
      unfold wt_set_from_pset_spec1 in hws.
      eapply mx_forall. eassumption.
      intros.
      edestruct hws as (p' & mem%elem_of_singleton_1 & w); subst; eauto.
      inversion w; subst; eauto with mdb.
      eapply co_wt_mu_mx; eauto with mdb.
      eapply wt_nil_mx.
      eapply H1; eauto.
      eapply cowt_iff_wt_nil; eauto.
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
      set (X' := list_to_set (cowt_tau_set  p) : gset P).
      assert (p' ∈ X').
      eapply cowt_tau_set_spec , elem_of_list_to_set in hl; eauto.
      eapply (H X'); eauto.
      intros p0 mem0%elem_of_list_to_set%cowt_tau_set_spec . set_solver. set_solver.
    + eauto with mdb.
    + intros p' e' μ μ' duo hlp hle.
      assert (Finite (dsig (λ q : P, dual μ μ' ∧ p ⟶[μ] q))).
      { unfold dsig.
        eapply (in_list_finite (map proj1_sig (enum (dsig (fun q => exists α', dual α' μ' /\ p ⟶[α'] q))))).
        intros q Hq. eapply bool_decide_unpack in Hq.
        eapply list_elem_of_fmap.
        exists (dexist q (ex_intro _ μ (conj duo (proj2 Hq)))).
        split; [reflexivity | eapply elem_of_enum]. }
      set (X' := list_to_set (
                     map proj1_sig (enum $ dsig (fun q => dual μ μ' /\ p ⟶[μ] q))
                   ) : gset P).
      assert (p' ∈ X').
      eapply elem_of_list_to_set, list_elem_of_fmap; eauto.
      assert (hlp' : dual μ μ' /\ p ⟶[μ] p'). eexists; eauto.
      exists (dexist p' hlp'). split. eauto. eapply elem_of_enum.
      eapply (H1 e' μ' X'). eassumption.
      intros p0 mem0%elem_of_list_to_set.
      eapply list_elem_of_fmap in mem0 as ((r & l) & eq & mem'). subst.
      exists p. split; eauto.
      eapply cowt_act. eauto.
      assert (mem'' : dual μ μ' /\ p ⟶[μ] r ).
      { eapply bool_decide_unpack. eauto. }
      destruct mem'' as (duo'' & tr''). exact tr''.
      eapply cowt_nil. set_solver. set_solver.
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
    + intros t' μ X' hle xspec' xneq_nil'.
      eapply mx_forall. eassumption.
      intros p' (p0 & h%hm & hl)%xspec'. eapply must_set_iff_must.
      eapply cowt_to_wt_dual in hl as (s' & duo & wk_tr).
      inversion duo;subst. symmetry in H1.
      eapply must_preserved_by_wt_synch_if_notoutcome ; eauto.
      inversion H3;subst;eauto.
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

Context `{gLtsP : @gLts P A EA, !coFiniteImagegLts P A}.
Context `{HinterP : !Prop_of_Inter P T A dual}.
Context `{gLtsQ : @gLts Q A EA, !coFiniteImagegLts Q A}.
Context `{HinterQ : !Prop_of_Inter Q T A dual}.

Definition ctx_pre__x
  (X : gset P) (Y : gset Q)
  := forall (t : T), X must_pass_x t -> Y must_pass_x t.
Notation "X ⊑ₛₑₜ_ₘᵤₛₜᵢ Y" := (ctx_pre__x X Y) (at level 70).
Notation "X ⋢ₛₑₜ_ₘᵤₛₜᵢ Y" := (¬ ctx_pre X Y) (at level 70).

Lemma set_must_union_right
  (X : gset P) (Y Y' : gset Q) : X ⊑ₛₑₜ_ₘᵤₛₜᵢ Y -> X ⊑ₛₑₜ_ₘᵤₛₜᵢ Y' ->  X ⊑ₛₑₜ_ₘᵤₛₜᵢ (Y ∪ Y').
Proof.
  intros Hyp1 Hyp2.
  intros t h_must.
  - eapply mx_sum.
    + eapply Hyp1; eauto.
    + eapply Hyp2; eauto.
Qed.

Lemma set_must_empty (X : gset P) : X ⊑ₛₑₜ_ₘᵤₛₜᵢ ∅.
Proof.
  intros t h_must.
  induction h_must.
  + now eapply mx_now.
  + eapply mx_step;eauto.
    * intros p mem. inversion mem.
    * intros. destruct X' using set_ind_L.
      - exfalso. eapply H3;eauto.
      - assert (x ∈ {[x]} ∪ X0) as mem'' by set_solver.
        eapply H2 in mem'' as (p' & mem_imp & tr). inversion mem_imp.
    * intros. destruct X' using set_ind_L.
      - exfalso. eapply H4;eauto.
      - assert (x ∈ {[x]} ∪ X0) as mem'' by set_solver.
        eapply H3 in mem'' as (p' & mem_imp & tr). inversion mem_imp.
Qed.

Lemma set_must_union_left_rev
  (X : gset P) (Y Y' : gset Q) : X ⊑ₛₑₜ_ₘᵤₛₜᵢ (Y ∪ Y') -> X ⊑ₛₑₜ_ₘᵤₛₜᵢ Y.
Proof.
  intros Hyp t h_must.
  induction Y using set_ind_L.
  - eapply set_must_empty;eauto.
  - eapply Hyp in h_must. eapply must_set_for_all. set_solver.
    intros. eapply must_if_must_set_helper in h_must.
    set_solver. set_solver.
Qed.

Lemma set_must_union_right_rev
  (X : gset P) (Y Y' : gset Q) : X ⊑ₛₑₜ_ₘᵤₛₜᵢ (Y ∪ Y') -> X ⊑ₛₑₜ_ₘᵤₛₜᵢ Y'.
Proof.
  intros Hyp t h_must.
  induction Y' using set_ind_L.
  - eapply set_must_empty;eauto.
  - eapply Hyp in h_must. eapply must_set_for_all. set_solver.
    intros. eapply must_if_must_set_helper in h_must.
    set_solver. set_solver.
Qed.

Lemma set_must_sub
  (X : gset P) (Y : gset Q) : X ⊑ₛₑₜ_ₘᵤₛₜᵢ Y -> forall Y', Y' ⊆ Y ->  X ⊑ₛₑₜ_ₘᵤₛₜᵢ Y'.
Proof.
  intros Hyp Y' sub t h_must.
  destruct Y' using set_ind_L.
  + eapply set_must_empty;eauto.
  + eapply Hyp in h_must. eapply must_set_for_all. set_solver.
    intros. eapply must_if_must_set_helper in h_must.
    set_solver. set_solver.
Qed.

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
Notation "X ⊑ₛₑₜ_ₘᵤₛₜᵢ Y" := (ctx_pre__x X Y) (at level 70).
Notation "X ⋢ₛₑₜ_ₘᵤₛₜᵢ Y" := (¬ ctx_pre X Y) (at level 70).

(* The relation ⊑ₛₑₜ_ₘᵤₛₜᵢ is reflexive *)
#[global] Instance set_must_refl
  `{EA : !ExtAction A} `{gLtsT : !gLtsEq T EA} `{TP : @Testing_Predicate T A EA outcome _}
  `{gLtsP : @gLts P A EA, !coFiniteImagegLts P A} {Hinter : @Prop_of_Inter P T A dual EA gLtsP _} : Reflexive ctx_pre__x.
Proof. intros X t h_must. eauto. Qed.

(* The relation ⊑ₛₑₜ_ₘᵤₛₜᵢ is transitive *)
#[global] Instance set_must_transitive
  `{EA : !ExtAction A} `{gLtsT : !gLtsEq T EA} `{TP : @Testing_Predicate T A EA outcome _}
  `{gLtsP : @gLts P A EA, !coFiniteImagegLts P A} {Hinter : @Prop_of_Inter P T A dual EA gLtsP _} : Transitive ctx_pre__x.
Proof.
  intros X Y Z hcgr1 hcgr2. intros t h_must.
  eapply hcgr2. eapply hcgr1; eauto.
Qed.

(* The relation ⊑ₛₑₜ_ₘᵤₛₜᵢ is a preorder *)
#[global] Instance set_must_x_preorder
  `{EA : !ExtAction A} `{gLtsT : !gLtsEq T EA} `{TP : @Testing_Predicate T A EA outcome _}
  `{gLtsP : @gLts P A EA, !coFiniteImagegLts P A} {Hinter : @Prop_of_Inter P T A dual EA gLtsP _} : PreOrder ctx_pre__x.
Proof.
  split.
  + exact set_must_refl.
  + exact set_must_transitive.
Qed.

Notation "X ≂ₛₑₜ_ₘᵤₛₜᵢ Y" := (Y ⊑ₛₑₜ_ₘᵤₛₜᵢ X /\ X ⊑ₛₑₜ_ₘᵤₛₜᵢ Y) (at level 70).

(** ** [mustx_alt] — the one piece of [mustx]'s apparatus that *does* need a
    co-variant: its [com] case is where the (map-[coₜ]-free) design pays off.
    Mirrors [mustx]'s own two-label ([wt_set_from_pset_spec1 X [μ1] X'] +
    [dual μ1 μ2]) style, but with a single [μ] via [cowt_set_from_pset_spec1]
    (itself just [wt_set_from_pset_spec1]'s pattern rebuilt on [⟹ᶜᵒ]) — this
    keeps the bridge to [mustx] a direct, per-element one (no need to route
    through [toSET]'s "exact union" semantics, which only obscures the
    already-immediate correspondence). The bridge itself needs [dual]'s
    global uniqueness ([unique_nb], unrestricted to non-blocking actions
    despite the name — see [gLts.v]) once, to turn the existential dual
    witness [cowt_set_from_pset_spec1] hides back into the single fixed label
    [wt_set_from_pset_spec1] needs; this is a legitimate external use of a
    real class law, unlike baking [unique_nb]/canonical [co] into [cowt]'s
    own definition (which stays fully dual-relational, per
    [[co_trace_files_dual_bridge]]). *)

(* [mustx_alt_co]'s own [pt] field uses the set LTS ([toSET], [X ⟶ X'] on
   [gset P]) — the piece the header comment (top of file) calls out as the
   one place [mustx]'s apparatus structurally needs [FiniteImagegLts] for
   [SetLTSConstruction.toSET]. *)
(*
Inductive mustx_alt_co `{EA : !ExtAction A} `{gLtsT : !gLtsEq T EA} `{TP : @Testing_Predicate T A EA outcome _}
  `{gLtsP : @gLts P A EA, !FiniteImagegLts P A} {Hinter : @Prop_of_Inter P T A dual EA gLtsP _}
  (X : gset P) (t : T) : Prop :=
| mx_now_alt_co (hh : outcome t) : mustx_alt_co X t
| mx_step_alt_co
    (nh : ¬ outcome t)
    (ex : forall (p : P), p ∈ X -> ∃ p', inter_step (p, t) τ p')
    (pt : forall X',
        X ⟶ X' ->
        mustx_alt_co X' t)
    (et : forall (t' : T), t ⟶ t' -> mustx_alt_co X t')
    (com : forall (t' : T) μ (X' : gset P),
        t ⟶[μ] t' ->
        X ⟹ᶜᵒ{μ} X' ->
        mustx_alt_co X' t')
  : mustx_alt_co X t.

#[global] Hint Constructors mustx_alt_co:mdb.
Global Notation "X 'must_alt_pass_x_co' t" := (mustx_alt_co X t) (at level 70).
*)

(* [mustx_iff_mustx_alt_co] bridges [mustx] to [mustx_alt_co] — depends on
   the (now commented-out) set-LTS-based [mustx_alt_co]. *)
(*
Section MustxIffMustxAltCo.

(* This bridge lemma needs [mustx] (⇒ [coFiniteImagegLts P A]) and
   [mustx_alt_co] (⇒ [FiniteImagegLts P A], for its toSET-based [pt] case)
   simultaneously on the *same* [X : gset P] — so the two [Countable P]
   sources must be the same term, not two independent postulates (see
   [[bang_vs_bare_class_binder]]-style clash risk). [coFiniteImagegLts P A]
   is taken as primary and [FiniteImagegLts P A] is derived locally via
   [FiniteImagegLts_of_coFiniteImagegLts], sharing the countable field by
   construction. Any caller supplying the *same* [coFiniteImagegLts P A]
   term for both this lemma and [mustx_alt_co]'s own use gets a matching
   derived instance automatically (it's a pure function of that term). *)
Context `{EA : !ExtAction A}.
Context `{gLtsT : !gLtsEq T EA}.
Context `{TP : @Testing_Predicate T A EA outcome _}.
Context `{gLtsP : @gLts P A EA, !coFiniteImagegLts P A}.
#[local] Instance MustxIffMustxAltCo_FI_PP : FiniteImagegLts P A 
    := FiniteImagegLts_of_coFiniteImagegLts _.
Context `{Hinter : @Prop_of_Inter P T A dual EA gLtsP _}.

Lemma mustx_iff_mustx_alt_co
  (X : gset P) (t : T) :
  X must_pass_x t <-> X must_alt_pass_x_co t.
Proof.
  split.
  - intro hmx. dependent induction hmx; eauto.
    + constructor ;eauto.
    + eapply mx_step_alt_co; eauto.
      * intros. destruct H2;eauto. subst.
        assert (lts_tau_set_from_pset_spec1 X (cowt_tau_set_from_pset X)).
        { eapply cowt_tau_set_from_pset_ispec. }
        eauto.
      * intros t' μ X' hle hws.
        eapply (H1 t' (co μ) μ X'); eauto.
        -- symmetry. exact (proj2_sig (exists_dual μ)).
        -- intros q mem. eapply hws in mem as (p & mem & w).
           eapply cowt_to_wt_dual in w as (s' & hf & w').
           assert (Hy : exists y, s' = [y] /\ dual μ y).
           { inversion hf as [| ? y ? ? duo hf2]; subst. inversion hf2; subst. eauto. }
           destruct Hy as (y & -> & duo).
           assert (y = co μ) by (eapply unique_nb; exact duo).
           subst. exists p. eauto.
  - intro hmx. dependent induction hmx; eauto.
    + constructor ;eauto.
    + eapply mx_step; eauto.
      * intros. assert (X' ⊆ cowt_tau_set_from_pset X).
        { intros p' mem'. eapply H2 in mem' as (p & mem & tr).
          eapply cowt_tau_set_from_pset_ispec;eauto. }
        assert (cowt_tau_set_from_pset X  ≠ ∅ ) by set_solver.
        assert (X ⟶ cowt_tau_set_from_pset X).
        { split ;eauto. }
        eapply H in H6. eapply mx_sub;eauto.
      * intros t' μ1 μ2 X' duo hle hws hneq.
        eapply (H1 t' μ2 X'); eauto.
        intros q mem. eapply hws in mem as (p & mem & w).
        exists p. split; eauto. eapply wt_to_cowt_dual with (s' := [μ1]); eauto.
        constructor; [symmetry; exact duo | constructor].
Qed.

End MustxIffMustxAltCo.
*)

(** ** Condition on convergence *)

Definition bhv_pre_co_cond1__x `{gLtsP : @gLts P A EA, !Countable P}
  `{gLtsQ : @gLts Q A EA, !Countable Q}
  (X : gset P) (Y : gset Q) :=
  forall s, (forall p, p ∈ X -> p ⇓ᶜᵒ s) -> (forall q, q ∈ Y -> q ⇓ᶜᵒ s).

Global Notation "X ₁≼꜀ₒ₋ₛₑₜ_ₐₛ Y" := (bhv_pre_co_cond1__x X Y) (at level 70).

(** ** Condition on acceptance sets *)

Definition bhv_pre_co_cond2__x
  `{gLtsP : @gLts P A EA, !Countable P}
  `{gLtsQ : @gLts Q A EA, !Countable Q}
  `{gLtsT : @gLtsEq T A EA}
  `{AbsPT : @AbsAction P T FinA PreAct A EA Φ 𝝳P _ _}
  `{AbsQT : @AbsAction Q T FinA PreAct A EA Φ 𝝳Q _ _}
  (X : gset P) (Y : gset Q) :=
  forall q s q', q ∈ Y ->
    q ⟹ᶜᵒ[s] q' -> q' ↛ ->
    (forall p, p ∈ X -> p ⇓ᶜᵒ s) ->
    exists p, p ∈ X /\ exists p', p ⟹ᶜᵒ[s] p' /\ p' ↛ /\ (⌈ (𝝳P ∘ Φ) ⌉ (coR p') ⊆ ⌈ (𝝳Q ∘ Φ) ⌉ (coR q')).

Global Notation "X ₂≼꜀ₒ₋ₛₑₜ_ₐₛ Y" := (bhv_pre_co_cond2__x X Y) (at level 70).

(** ** Alternative preorder on sets *)

Definition bhv_pre_co__x
  `{gLtsP : @gLts P A EA, !Countable P}
  `{gLtsQ : @gLts Q A EA, !Countable Q}
  `{gLtsT : @gLtsEq T A EA}
  `{AbsPT : @AbsAction P T FinA PreAct A EA Φ 𝝳P _ _}
  `{AbsQT : @AbsAction Q T FinA PreAct A EA Φ 𝝳Q _ _}
    (X : gset P) (Y : gset Q) :=
      (X ₁≼꜀ₒ₋ₛₑₜ_ₐₛ Y /\ X ₂≼꜀ₒ₋ₛₑₜ_ₐₛ Y).

Global Notation "X ≼꜀ₒ₋ₛₑₜ_ₐₛ Y" := (bhv_pre_co__x X Y) (at level 70).

(** ** Acceptance-set preorder properties, co variant

    Mirrors [Acceptance_Set_preorder_for_sets] (Soundness.v), scoped down to
    the lemmas [soundnessx_co] actually needs. No [FiniteImagegLts P/Q A]
    anywhere: every lemma body here only ever needs a *bare* [Countable
    P]/[Countable Q] for the [cowt_set_from_pset_spec1/spec2] obligations —
    not even [coFiniteImagegLts] is needed here (in particular
    [reverse_trace_inclusion_co]'s witness set is built directly as a
    singleton [{[p']}] from [bhv_pre_co_cond2__x]'s own match, sidestepping
    the constructive [cowt_s_set_from_pset] entirely). Kept on bare
    [!Countable P/Q] (matching [bhv_pre_co_cond1__x]/[bhv_pre_co_cond2__x]/
    [bhv_pre_co__x] above) rather than [coFiniteImagegLts P/Q A]: since
    [coFiniteImagegLts]'s own [Countable] field is declared with [::]
    (a genuine sub-instance projection, see [coFiniteImage.v]), any
    [Countable P] resolved here from a caller's ambient [coFiniteImagegLts
    P A] (e.g. [SoundnessAS_co]'s own [soundnessx_co]) is *the same term*
    by construction — no clash risk, unlike two independently-postulated
    [Countable P] siblings would have. *)

Section Acceptance_Set_preorder_for_sets_co.

Context `{EA : !ExtAction A}.
Context `{gLtsEqT : !gLtsEq T EA}.

Context `{gLtsP : @gLts P A EA, !Countable P}.
Context `{AbsPT : @AbsAction P T FinA PreAct A EA Φ 𝝳P _ _}.

Context `{gLtsQ : @gLts Q A EA, !Countable Q}.
Context `{AbsQT : @AbsAction Q T FinA PreAct A EA Φ 𝝳Q _ _}.

Lemma alt_set_singleton_iff_co
  (p : P) (q : Q) : ({[ p ]} : gset P) ≼꜀ₒ₋ₛₑₜ_ₐₛ ({[ q ]} : gset Q) <->  p ≼꜀ₒ₋ₐₛ q.
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

Lemma bhvleqone_preserved_by_reduction_co
  (X : gset P) (Y Y' : gset Q) :
  X ₁≼꜀ₒ₋ₛₑₜ_ₐₛ Y -> lts_tau_set_from_pset_spec1 Y Y' -> X ₁≼꜀ₒ₋ₛₑₜ_ₐₛ Y'.
Proof.
  intros halt1 l s mem.
  intros. eapply l in H as (q' & mem' & tr').
  eapply cocnv_preserved_by_lts_tau; eauto.
Qed.

(* Uses the set LTS ([toSET], [Y ⟶ Y'] on [gset Q]). *)
(*
Lemma bhvleqone_preserved_by_reduction_lts_co
  (X : gset P) (Y Y' : gset Q) :
  X ₁≼꜀ₒ₋ₛₑₜ_ₐₛ Y -> Y ⟶ Y' -> X ₁≼꜀ₒ₋ₛₑₜ_ₐₛ Y'.
Proof.
  intros; eapply bhvleqone_preserved_by_reduction_co;eauto.
  destruct H0. subst. eapply cowt_tau_set_from_pset_ispec.
Qed.
*)

Lemma bhvx_preserved_by_reductions_co
  (X : gset P) (Y Y' : gset Q) : wt_set_from_pset_spec1 Y [] Y' -> X ≼꜀ₒ₋ₛₑₜ_ₐₛ Y -> X ≼꜀ₒ₋ₛₑₜ_ₐₛ Y'.
Proof.
  intros l (halt1 & halt2).
  split.
  - intros s mem. intros.
    eapply l in H as (q' & tr & mem').
    eapply cocnv_preserved_by_cowt_nil; eauto.
    eapply cowt_iff_wt_nil; eauto.
  - intros q' s q'' mem w st hcnv.
    eapply l in mem as (q & mem2 & tr).
    destruct (halt2 q s q'') as (p' & mem' & p'' & hw & hst); eauto with mdb.
    eapply cowt_push_nil_left;eauto. eapply cowt_iff_wt_nil; eauto.
Qed.

Lemma bhvx_preserved_by_reduction_co
  (X : gset P) (Y Y' : gset Q) : lts_tau_set_from_pset_spec1 Y Y' -> X ≼꜀ₒ₋ₛₑₜ_ₐₛ Y -> X ≼꜀ₒ₋ₛₑₜ_ₐₛ Y'.
Proof.
  intros l (halt1 & halt2).
  eapply bhvx_preserved_by_reductions_co;eauto.
  intros q' mem'. eapply l in mem' as (q'' & mem'' & wt_tr'').
  exists q''. split; eauto. eapply lts_to_wt_tau;eauto. split ;eauto.
Qed.

(* Uses the set LTS ([toSET], [Y ⟶ Y'] on [gset Q]). *)
(*
Lemma bhvx_preserved_by_reduction_lts_co
  (X : gset P) (Y Y' : gset Q) : Y ⟶ Y' -> X ≼꜀ₒ₋ₛₑₜ_ₐₛ Y -> X ≼꜀ₒ₋ₛₑₜ_ₐₛ Y'.
Proof.
  intros. eapply bhvx_preserved_by_reductions_co;eauto.
  destruct H. subst. intros q'' mem''.
  destruct (cowt_tau_set_from_pset_ispec Y) as (Hyp1 & Hyp2).
  eapply Hyp1 in mem'' as (q & mem & wt_tr).
  exists q. split ;eauto. eapply lts_to_wt_tau;eauto.
Qed.
*)

Lemma bhvleqone_preserved_by_external_action_co
  (X X' : gset P) μ (Y Y' : gset Q) (htp : forall p, p ∈ X -> terminate p) :
  X ₁≼꜀ₒ₋ₛₑₜ_ₐₛ Y -> cowt_set_from_pset_spec X μ X'  -> cowt_set_from_pset_spec1 Y μ Y' -> X' ₁≼꜀ₒ₋ₛₑₜ_ₐₛ Y'.
Proof.
  intros hleq hws l s hcnv. intros.
  eapply l in H as (q' & mem' & wk_tr).
  eapply cocnv_preserved_by_cowt_act;eauto.
  eapply hleq.
  intros p mem''. eapply cocnv_act.
  + eapply htp; eauto.
  + intros. eapply hcnv, hws; eassumption.
  + exact mem'.
Qed.

Lemma bhvx_preserved_by_external_action_co
  (X X' : gset P) μ (Y Y' : gset Q) (htp : forall p, p ∈ X -> terminate p) :
  cowt_set_from_pset_spec1 Y μ Y'
    -> cowt_set_from_pset_spec X μ X'
      -> X ≼꜀ₒ₋ₛₑₜ_ₐₛ Y
        -> X' ≼꜀ₒ₋ₛₑₜ_ₐₛ Y'.
Proof.
  intros lts__q ps1_spec (halt1 & halt2). split.
  - eapply bhvleqone_preserved_by_external_action_co; eauto.
  - intros q s q0 mem wt st hcnv. assert (cowt_set_from_pset_spec1 Y μ Y') as tr'';eauto.
    eapply tr'' in mem as (q' & mem' & tr_ext);eauto.
    edestruct (halt2 q' (μ :: s) q0) as (t & mem'' & p0 & p1 & wta__t & sub); eauto with mdb.
    + eapply cowt_push_left; eauto.
    + intros p'' mem1. eapply cocnv_act.
      * eapply htp; eauto.
      * intros q1 wk_tr. destruct ps1_spec as (ps1s1 & ps1s2).
        eapply ps1s2 in wk_tr; eauto.
    + eapply cowt_pop in p1 as (r & w1 & w2).
      exists r. repeat split. destruct ps1_spec as (ps1s1 & ps1s2). eapply ps1s2; eassumption. eauto.
Qed.

Lemma reverse_trace_inclusion_co
  (X : gset P) (Y Y' : gset Q) μ
  : X ≼꜀ₒ₋ₛₑₜ_ₐₛ Y -> (forall p, p ∈ X -> p ⇓ᶜᵒ [μ]) ->
    cowt_set_from_pset_spec1 Y μ Y' -> Y' ≠ ∅ ->
    exists X', cowt_set_from_pset_spec1 X μ X' /\ X' ≠ ∅.
Proof.
  intros (h1 & h2) hcnv hl not_empty.
  destruct (set_choose_L Y' not_empty) as (q0 & mem0).
  eapply hl in mem0 as (q & mem & w).
  assert (hq0 : q0 ⤓).
  { eapply equiv_cotermination.
    eapply cocnv_preserved_by_cowt_act.
    - eapply h1; eauto.
    - exact w. }
  destruct (terminate_then_wt_refuses q0 hq0) as (q0' & wq0 & stq0).
  assert (w' : q ⟹ᶜᵒ[[μ]] q0').
  { eapply cowt_push_nil_right; eauto. eapply cowt_iff_wt_nil; eauto. }
  edestruct (h2 q [μ] q0' mem w' stq0 hcnv) as (p & memp & p' & wp & stp & sub).
  exists ({[ p' ]}).
  split.
  - intros q1 mem1. exists p. split; eauto. assert (q1 = p') by set_solver. subst. exact wp.
  - set_solver.
Qed.

End Acceptance_Set_preorder_for_sets_co.

(** ** Communication-enabling property, co variant

    [communication_enabled] itself needs no co-analogue: it reasons purely
    about single LTS steps ([⟶]) and the [dual]/[coR]/[Φ]/[𝝳] apparatus,
    none of which is co- or plain-specific — copied verbatim, exactly like
    [mustx]. Keeps [𝝳] SHARED between P and Q (not split into 𝝳P/𝝳Q): a
    prior finding in this session showed the proof genuinely needs the two
    sides to share one delta.

    Stated with an explicit [dual μ1 μ2] rather than a hardcoded [co μ] on
    either side — [cn_enabled]/[coR] are already fully general (take/give
    an arbitrary dual witness, not the canonical one specifically), so the
    whole proof goes through without ever invoking [unique_nb]/[co]:
    [dual]'s witnesses are used exactly as given, never pinned down to the
    canonical one. Diverges from [communication_enabled] (the original,
    plain, `co`-hardcoded version) for this reason; the caller
    ([unoutcome_must_st_nleqx_co]) correspondingly drops the
    [assert (μ1 = co μ2)] step it would otherwise need. *)

Section Properties_for_soundness_co.

Context `{EA : !ExtAction A}.
Context `{gLtsT : !gLtsEq T EA}.
Context `{TP : @Testing_Predicate T A EA outcome _}.

Context `{gLtsP : @gLts P A EA}.
Context `{HinterP : !Prop_of_Inter P T A dual}.
Context `{gLtsQ : @gLts Q A EA}.
Context `{HinterQ : !Prop_of_Inter Q T A dual}.

Context `{AbsPT : @AbsAction P T FinA PreAct A EA Φ 𝝳 _ _}.
Context `{AbsQT : @AbsAction Q T FinA PreAct A EA Φ 𝝳 _ _}.

Context `{!gLtsCNenabled Q A}.

Lemma communication_enabled_co (p : P) p' (q : Q) (t : T) t' μ1 μ2 :
      dual μ1 μ2 -> p ⟶[μ1] p' -> t ⟶[μ2] t' -> ⌈ (𝝳 ∘ Φ) ⌉ (coR p) ⊆ ⌈ (𝝳 ∘ Φ) ⌉ (coR q)
        -> exists ν1 ν2 q' t'', dual ν1 ν2 /\ q ⟶[ν1] q' /\ t ⟶[ν2] t''.
Proof.
  intros duo tr tr_co sub.
  destruct (decide (non_blocking μ2)) as [nb | not_nb].
  + eapply (cn_enabled q μ2 μ1) in nb as (q' & tr'); [| symmetry; exact duo].
    exists μ1, μ2, q', t'. eauto.
  + assert (μ2 ∈ coR p) as some_co_action_of_p.
    { exists μ1. repeat split; eauto.
      eapply lts_refuses_spec2;eauto. }
    eapply (map_gamma_of_action (𝝳 ∘ Φ)) in some_co_action_of_p as mem.
    eapply sub in mem. destruct mem as (μ' & mem & eq).
    eapply (map_gamma_of_action Φ) in mem as eq'. symmetry in eq.
    eapply (abstraction_prog_spec q) in eq' ;eauto.
    2:{ destruct mem as (ν & hmem & hdual & hblock). eauto. }
    destruct eq' as (μ'' & mem' & eq'). destruct mem' as (μ''' & tr' & duo2 & b).
    assert (μ'' ∈ R t) as Tr_Test.
    { eapply abstraction_test_spec in eq';eauto. apply lts_refuses_spec2. eauto. }
    eapply lts_refuses_spec1 in Tr_Test as (t'' & Tr'').
    eapply lts_refuses_spec1 in tr' as (q' & tr').
    exists μ''', μ'', q', t''. eauto.
Qed.

End Properties_for_soundness_co.

(** ** Soundness for sets, co variant *)

Section SoundnessAS_co.

Context `{EA : !ExtAction A}.
Context `{gLtsEqT : !gLtsEq T EA}.
Context `{TP : @Testing_Predicate T A EA outcome _}.

(* [mustx] is used on both sides ([X must_pass_x t] directly, and
   [Y must_pass_x t] via [mustx_iff_mustx_alt_co]/[mustx_alt_co] inside
   [soundnessx_co]) — needs only [coFiniteImagegLts]. No [FiniteImagegLts]
   instance (local or global) is needed in this section any more: the only
   lemmas here that ever needed it ([unoutcome_must_st_nleqx_co],
   [stability_nbhvleqtwo_co], via [bhv_pre_co_cond2__x]) are unused now
   that their only caller ([soundnessx_co]) is commented out (set-LTS-based
   — see that comment), so they're commented out too, below. *)
Context `{gLtsP : @gLts P A EA, !coFiniteImagegLts P A}.
Context `{!Prop_of_Inter P T A dual}.
Context `{gLtsQ : @gLts Q A EA, !coFiniteImagegLts Q A, !gLtsCNenabled Q A}.
Context `{!Prop_of_Inter Q T A dual}.

Context `{AbsPT : @AbsAction P T FinA PreAct A EA Φ 𝝳 _ _}.
Context `{AbsQT : @AbsAction Q T FinA PreAct A EA Φ 𝝳 _ _}.

(* Both need [FiniteImagegLts P/Q A] (via [bhv_pre_co_cond2__x]) and are
   unused now that their only caller, [soundnessx_co], is commented out. *)

Lemma unoutcome_must_st_nleqx_co (X : gset P) (Y : gset Q) (t : T):
  ¬ outcome t
    -> X must_pass_x t
      -> (∃ q, q ∈ Y /\ (q, t) ↛)
        -> ¬ X ₂≼꜀ₒ₋ₛₑₜ_ₐₛ Y.
Proof.
  intros not_happy all_must (q & mem' & refuses_tau_q) hbhv2.
  assert (q ↛) as stable_q.
  { destruct (lts_refuses_decidable q τ) as [refuses_q | not_refuses_q].
    - exact refuses_q.
    - exfalso. eapply lts_refuses_spec1 in not_refuses_q as (q' & l).
      eapply (lts_refuses_spec2 (q ▷ t)); eauto. exists (q' ▷ t). eapply ParLeft. exact l. }
  assert (htX : ∀ p : P, p ∈ X → p ⇓ᶜᵒ []).
  { destruct (mustx_terminate_unoutcome X t all_must) as [|htps]; eauto with mdb. contradiction. }
  assert (w0 : q ⟹ᶜᵒ[[]] q). { eapply cowt_iff_wt_nil. eauto with mdb. }
  destruct (hbhv2 q [] q mem' w0 stable_q htX) as (p & mem & p' & wp & stp' & sub).
  assert (mustx {[ p' ]} t) as must_p'.
  { eapply (wt_nil_mx p). eapply (mx_sub X t all_must). set_solver.
    eapply cowt_iff_wt_nil. eassumption. }
  destruct must_p'; eauto.
  edestruct (ex p') as ((p'' , t'') & HypTr). now eapply elem_of_singleton.
  inversion HypTr as [? ? ? ? tau_left | ? ? ? ? tau_right | ? ? ? ? ? ? ? act_left act_right]; subst.
  - eapply lts_refuses_spec2 in stp'; eauto.
  - destruct (lts_refuses_decidable t τ) as [refuses_t | not_refuses_t].
    + eapply lts_refuses_spec2 in refuses_t. eauto. eauto with mdb.
    + eapply (lts_refuses_spec2 (q ▷ t)); eauto.
      exists (q , t''). eapply ParRight; eauto.
  - eapply communication_enabled_co in act_left as (ν1 & ν2 & q' & t''' & duo & tr1 & tr2); eauto.
    eapply (lts_refuses_spec2 (q ▷ t)); eauto. exists (q', t''').
    eapply (ParSync ν1); eauto.
Qed.

Lemma stability_nbhvleqtwo_co
  (X : gset P) (Y : gset Q) t :
  ¬ outcome t
    -> X must_pass_x t
      -> X ₂≼꜀ₒ₋ₛₑₜ_ₐₛ Y
        -> forall (q : Q), q ∈ Y -> ∃ q', (q, t) ⟶{τ} q'.
Proof.
  intros nhg hmx hleq q mem.
  destruct (lts_refuses_decidable (q, t) τ).
  - exfalso. apply (unoutcome_must_st_nleqx_co X Y t nhg hmx); eauto.
  - eapply lts_refuses_spec1 in n as (t' & hl). eauto.
Qed.

Lemma unoutcome_acnv_mu_co (X : gset P) (t t' : T) :
  X must_pass_x t
    -> forall μ p, p ∈ X
      -> t ⟶[μ] t'
          -> ¬ outcome t -> ¬ outcome t' -> p ⇓ᶜᵒ [μ].
Proof.
  intros hmx μ p mem l not_happy not_happy'.
  dependent induction hmx.
  - contradiction.
  - edestruct (mustx_terminate_unoutcome X t) as [happy | finish]; eauto with mdb.
    contradiction.
    eapply cocnv_act. eauto.
    intros q w.
    assert (h1 : cowt_set_from_pset_spec1 X μ {[q]}).
    exists p. split; set_solver.
    assert (h2 : {[q]} ≠ (∅ : gset P)) by set_solver.
    set (hm := com t' μ {[ q ]} l h1 h2).
    destruct (mustx_terminate_unoutcome _ _ hm).
    + contradiction.
    + eapply cocnv_nil. eapply H2. set_solver.
Qed.

(** ** Soundness for sets *)

Lemma soundnessx_co
  (X : gset P) (Y : gset Q) :
  X ≼꜀ₒ₋ₛₑₜ_ₐₛ Y  -> X ⊑ₛₑₜ_ₘᵤₛₜᵢ Y.
Proof.
  intros (halt1 & halt2) t hmx. revert Y halt1 halt2.
  dependent induction hmx; intros Y halt1 halt2.
  - eauto with mdb.
  - assert (HX0 : forall p, p ∈ X -> p ⇓ᶜᵒ []).
    { intros p mem. eapply cocnv_nil.
      destruct (mustx_terminate_unoutcome X t ltac:(eauto with mdb)) as [c|h]; [contradiction|].
      eauto. }
    assert (HYterm : forall q, q ∈ Y -> q ⤓).
    { intros q mem. eapply equiv_cotermination. eapply halt1; eauto. }
    assert (Y_conv : Y ⤓).
    { eapply co_termination_set_for_all. exact HYterm. }
    assert (Hbuild : forall Y0,
      Y0 ⤓ ->
      X ₁≼꜀ₒ₋ₛₑₜ_ₐₛ Y0 -> X ₂≼꜀ₒ₋ₛₑₜ_ₐₛ Y0 -> mustx Y0 t).
    { intros Y0 conv0. induction conv0 as [Y0 tY0 IHY0]. intros hb1 hb2.
      eapply mx_step.
      - eauto.
      - eapply stability_nbhvleqtwo_co; eauto with mdb.
      - intros Y0' hspec1 hne.
        set (Y0full := cowt_tau_set_from_pset Y0).
        destruct (cowt_tau_set_from_pset_ispec Y0) as (Y0full_spec1 & Y0full_spec2).
        destruct (decide (Y0full = ∅)) as [Hemp | Hnemp].
        + exfalso. assert (Y0' ⊆ Y0full) as Hsub0.
          { intros q memq. destruct (hspec1 q memq) as (p & memp & lstep).
            eapply Y0full_spec2; eauto. }
          set_solver.
        + assert (hstep0 : Y0 ⟶ Y0full) by (split; [reflexivity | exact Hnemp]).
          specialize (IHY0 Y0full hstep0).
          destruct (bhvx_preserved_by_reduction_co X Y0 Y0full Y0full_spec1 (conj hb1 hb2))
            as (hb1full & hb2full).
          specialize (IHY0 hb1full hb2full).
          assert (Y0' ⊆ Y0full) as Hsub0.
          { intros q memq. destruct (hspec1 q memq) as (p & memp & lstep).
            eapply Y0full_spec2; eauto. }
          eapply mx_sub; eauto.
      - intros t' l. eapply H0; eauto with mdb.
      - intros t' μ Y0' ltr lcowtspec hne.
        destruct (decide (outcome t')) as [ot'|not_ot'].
        + eapply mx_now; assumption.
        + assert (HA : forall p, p ∈ X -> p ⇓ᶜᵒ [μ]).
          { intros; eapply unoutcome_acnv_mu_co; eauto with mdb. }
          destruct (cowt_s_set_from_pset_ispec X μ HA) as (Xfull_spec1 & Xfull_spec2).
          set (Xfull := cowt_s_set_from_pset X μ HA) in *.
          assert (htX : forall p, p ∈ X -> terminate p).
          { destruct (mustx_terminate_unoutcome X t ltac:(eauto with mdb)) as [c|h]; [contradiction|exact h]. }
          edestruct (reverse_trace_inclusion_co X Y0 Y0' μ (conj hb1 hb2) HA lcowtspec hne)
            as (X'' & X''spec1 & X''ne).
          assert (X'' ⊆ Xfull) as Hsub.
          { intros q memq. destruct (X''spec1 q memq) as (p & memp & wpq).
            eapply Xfull_spec2; eauto. }
          assert (Xfull_ne : Xfull ≠ ∅) by set_solver.
          destruct (bhvx_preserved_by_external_action_co X Xfull μ Y0 Y0' htX lcowtspec
            (conj Xfull_spec1 Xfull_spec2) (conj hb1 hb2)) as (hb1' & hb2').
          eapply (H1 t' μ Xfull ltr Xfull_spec1 Xfull_ne); eauto. }
    eapply Hbuild; eauto with mdb.
Qed.

End SoundnessAS_co.

Section SoundnessCoNbEnabled.

Context `{gLtsP : @gLtsEq P A H, !coFiniteImagegLts P A}.
Context `{gLtsQ : !gLtsEq Q H, !gLtsCNenabled Q A, !coFiniteImagegLts Q A}.
Context `{gLtsT : !gLtsEq T H, !Testing_Predicate outcome _}.

Context `{AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳 _ _ }.
Context `{AbsQT : @AbsAction Q T FinA PreAct A H Φ 𝝳 _ _ }.

Context `{!Prop_of_Inter P T A dual}.
Context `{!Prop_of_Inter Q T A dual}.

Lemma soundness_co_nb_enabled_co
  (p : P) (q : Q) : p ≼꜀ₒ₋ₐₛ q -> p ⊑ₘᵤₛₜᵢ q.
Proof.
  intros halt e hm.
  eapply must_set_iff_must.
  eapply (soundnessx_co ({[p]} : gset P)).
  now eapply alt_set_singleton_iff_co.
  now eapply must_set_iff_must.
Qed.

End SoundnessCoNbEnabled.

(* Depends on [soundness_co_nb_enabled_co] (now proven above) — the
   [gLtsCNenabled Q A] instance it needs is derived after the fact, via
   [Unshelve], from [gLtsObaFW Q A]'s [boomerang] property. *)
Lemma soundness_fw_co `{
  gLtsEqP : @gLtsEq P A H, !coFiniteImagegLts P A,
  gLtsEqQ : @gLtsEq Q A H, !coFiniteImagegLts Q A, gLtsObaQ : !gLtsOba Q, !gLtsObaFW Q A,
  gLtsT : !gLtsEq T H, !Testing_Predicate outcome _}

  `{AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳 _ _ }
  `{AbsQT : @AbsAction Q T FinA PreAct A H Φ 𝝳 _ _ }

  `{!Prop_of_Inter P T A dual}
  `{!Prop_of_Inter Q T A dual}

  (p : P) (q : Q) : p ≼꜀ₒ₋ₐₛ q -> p ⊑ₘᵤₛₜᵢ q.
Proof.
  eapply soundness_co_nb_enabled_co.
  Unshelve.
  eapply MkgLtsCNenabled. intros.
  destruct (boomerang p1 η β) as (t & l1 & l2) ; eauto. symmetry;eauto.
Qed.

(** ** Soundness for LTSs that can be lifted to forwarders, co variant *)
(* Depends on [soundness_fw_co] (below), which depends on
   [soundness_co_nb_enabled_co]/[soundnessx_co] (set-LTS-based). *)
(*
Lemma soundness_co
  `{@gLtsObaFB P A H gLtsEqP gLtsObaP, !FiniteOutputChain_LtsOba P, !FiniteImagegLts P A}
  `{@gLtsObaFB Q A H gLtsEqQ gLtsObaQ, !FiniteOutputChain_LtsOba Q, !FiniteImagegLts Q A}
  `{@gLtsObaFB T A H gLtsEqT gLtsObaT, !FiniteOutputChain_LtsOba T, !FiniteImagegLts T A}

  `{ !Testing_Predicate outcome _}

  {_ : Prop_of_Inter P T A dual}
  {_ : Prop_of_Inter Q T A dual}

  {_ : @Prop_of_Inter P (MO A) A fw_inter H _ MbgLts}
  {_ : @Prop_of_Inter (P * MO A) T A dual H (inter_lts fw_inter) _}

  {_ : @Prop_of_Inter Q (MO A) A fw_inter H _ MbgLts}
  {_ : @Prop_of_Inter (Q * MO A) T A dual H (inter_lts fw_inter) _}

  (* [soundness_fw_co], applied below at the forwarder-pair types [P * MO
     A]/[Q * MO A], now needs [coFiniteImagegLts] at that level. Unlike
     [FiniteImagegLts (P * MO A) A] (auto-derived from [FiniteImagegLts P
     A] by [ForwarderConstruction.v]'s [gLtsMBFinite] instance), no such
     forwarder-pair instance exists yet for [coFiniteImagegLts] (same gap
     noted in [EquivalenceASco.v]/[CompletenessASco.v]), so it is assumed
     directly here. *)
  `{!coFiniteImagegLts (P * MO A) A}
  `{!coFiniteImagegLts (Q * MO A) A}

  `{AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳 _ _ }
  `{AbsQT : @AbsAction Q T FinA PreAct A H Φ 𝝳 _ _ }

  (p : P) (q : Q) : p ▷ ∅ ≼꜀ₒ₋ₐₛ q ▷ ∅ -> p ⊑ₘᵤₛₜᵢ q.
Proof.
  intros halt t hm.
  eapply Lift.must_iff_must_fw in hm.
  eapply Lift.must_iff_must_fw.
  now eapply (soundness_fw_co (p ▷ ∅) (q ▷ ∅)).
Qed.
*)
