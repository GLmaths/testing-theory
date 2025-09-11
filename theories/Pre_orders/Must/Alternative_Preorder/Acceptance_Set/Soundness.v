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

From Coq Require ssreflect Setoid.
From Coq.Unicode Require Import Utf8.
From Coq.Lists Require Import List.
Import ListNotations.
From Coq.Program Require Import Wf Equality.
From Coq.Wellfounded Require Import Inverse_Image.
From Coq.Logic Require Import JMeq ProofIrrelevance.

From stdpp Require Import base countable finite gmap list finite base decidable finite gmap.

From Must Require Import gLts Bisimulation Lts_OBA Lts_FW Lts_OBA_FB
      Must Subset_Act InteractionBetweenLts ParallelLTSConstruction ForwarderConstruction MultisetLTSConstruction
      Termination Convergence FiniteImageLTS WeakTransitions Lift.
From Must Require Import ActTau.

(* ************************************************************ *)

Inductive mustx `{
  gLtsP : @gLts P A H, !FiniteImagegLts P A, 
  gLtsE : !gLts E A, !gLtsEq E A, !Good E A good}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (ps : gset P) (e : E) : Prop :=
| mx_now (hh : good e) : mustx ps e
| mx_step
    (nh : ¬ good e)
    (ex : forall (p : P), p ∈ ps -> ∃ t, inter_step (p, e) τ t)
    (pt : forall ps',
        lts_tau_set_from_pset_spec1 ps ps' -> ps' ≠ ∅ ->
        mustx ps' e)
    (et : forall (e' : E), e ⟶ e' -> mustx ps e')
    (com : forall (e' : E) μ1 μ2 (ps' : gset P),
        parallel_inter μ1 μ2 ->
        lts_step e (ActExt μ2) e' ->
        wt_set_from_pset_spec1 ps [μ1] ps' -> 
        ps' ≠ ∅ ->
        mustx ps' e')
  : mustx ps e.

#[global] Hint Constructors mustx:mdb.

Lemma mx_sub `{
  gLtsP : gLts P A, !FiniteImagegLts P A,
  gLtsE : !gLts E A, !gLtsEq E A, !Good E A good}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  ps e : 
  mustx ps e 
    -> forall qs, qs ⊆ ps 
      -> mustx qs e.
Proof.
  intros hmx. dependent induction hmx.
  - eauto with mdb.
  - intros qs sub.
    eapply mx_step; eauto with mdb.
    + intros qs' hs hneq_nil.
      set (ps' := lts_tau_set_from_pset_ispec ps).
      destruct ps'.
      eapply H1; eauto with mdb.
      ++ destruct (set_choose_or_empty qs') as [(q' & l'%hs)|].
         intro eq_nil. destruct l' as (q & mem%sub & l%H5); set_solver.
         set_solver.
      ++ intros p (q & mem%sub & l)%hs. eauto.
    + intros e' μ μ' qs' hle duo hwqs hneq_nil.
      eapply (H3 e' μ μ'); eauto. intros p' mem%hwqs. set_solver.
Qed.

Lemma mx_mem `{
  gLtsP : gLts P A, !FiniteImagegLts P A,
  gLtsE : !gLts E A, !gLtsEq E A, !Good E A good} 

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  ps e : 
  mustx ps e 
    -> forall p, p ∈ ps 
      -> mustx {[ p ]} e.
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

Lemma mustx_terminate_ungood `{
  gLtsP : gLts P A, !FiniteImagegLts P A,
  gLtsE : !gLts E A, !gLtsEq E A, !Good E A good}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  ps e : 
  mustx ps e 
    -> good e \/ forall p, p ∈ ps -> p ⤓.
Proof.
  intros hmx.
  induction hmx.
  - now left.
  - right.
    intros p mem.
    eapply tstep. intros p' l.
    edestruct (H1 {[p']}); [exists p; set_solver| | |]; set_solver.
Qed.

Lemma mustx_terminate_ungood' `{
  @gLtsOba P A H gLtsP EP, !FiniteImagegLts P A, 
  gLtsE : !gLts E A, !gLtsEq E A, !Good E A good}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  ps e :
  mustx ps e
        -> forall p, p ∈ ps -> ¬ good e -> p ⤓.
Proof.
  intros hmx p mem not_happy.
  dependent induction hmx.
  + contradiction.
  + eapply tstep.
    intros q tr. eapply H2; eauto.
    assert (h1 : lts_tau_set_from_pset_spec1 ps {[q]}).
    exists p. assert (q0 = q);subst. set_solver. split; eauto. eauto.
    set_solver. set_solver.
Qed.


Lemma ungood_acnv_mu `{
  @gLtsOba P A H gLtsP EP, !FiniteImagegLts P A, 
  gLtsE : !gLts E A, !gLtsEq E A, !Good E A good}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  ps e e' :
  mustx ps e 
    -> forall μ μ' p, p ∈ ps 
      -> parallel_inter μ μ'
        -> e ⟶[μ'] e' 
          -> ¬ good e -> ¬ good e' -> p ⇓ [μ].
Proof.
  intros hmx μ μ' p mem inter l not_happy not_happy'.
  dependent induction hmx.
  - contradiction.
  - edestruct mustx_terminate_ungood as [happy | finish].
    +  eauto with mdb.
    + contradiction.
    + destruct (decide (non_blocking μ)) as [nb | not_nb];
      destruct (decide (non_blocking μ')) as [nb' | not_nb'].
      ++ exfalso. eapply dual_blocks; eauto.
      ++ edestruct mustx_terminate_ungood; eauto with mdb. contradiction.
         eapply cnv_act. eauto.
         intros q w.
         eapply cnv_nil.
         eapply terminate_preserved_by_wt_non_blocking_action; eauto.
      ++ edestruct mustx_terminate_ungood; eauto with mdb. contradiction.
         eapply cnv_act. eauto.
         intros q w.
         assert (h1 : wt_set_from_pset_spec1 ps [μ] {[q]}).
         exists p. split; set_solver.
         assert (h2 : {[q]} ≠ (∅ : gset P)) by set_solver.
         set (hm := com e' μ μ' {[ q ]} inter l h1 h2).
         destruct (mustx_terminate_ungood _ _ hm).
         +++ contradict nh.
             eapply good_preserved_by_lts_non_blocking_action_converse; eassumption.
         +++ eapply cnv_nil. eapply H6. set_solver.
      ++ edestruct mustx_terminate_ungood; eauto with mdb. contradiction.
         eapply cnv_act. eauto.
         intros q w.
         assert (h1 : wt_set_from_pset_spec1 ps [μ] {[q]}).
         exists p. split; set_solver.
         assert (h2 : {[q]} ≠ (∅ : gset P)) by set_solver.
         set (hm := com e' μ μ' {[ q ]} inter l h1 h2).
         destruct (mustx_terminate_ungood _ _ hm).
         +++ contradiction.
         +++ eapply cnv_nil. eapply H6. set_solver.
Qed.

Lemma must_mu_either_good_cnv `{
  @gLtsOba P A H gLtsP EP, !FiniteImagegLts P A, 
  gLtsE : !gLts E A, !gLtsEq E A, !Good E A good}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  ps e e' :
  mustx ps e 
    -> forall μ μ' p, p ∈ ps 
      -> parallel_inter μ μ'
        -> e ⟶[μ'] e' 
          -> good e \/ good e' (* ajout par rapport à Input/Output *) \/ p ⇓ [μ].
Proof.
  intros hmx μ μ' p mem inter l.
  destruct (decide (good e)); destruct (decide (good e')).
  + left; eauto.
  + left; eauto.
  + right; eauto.
  + right. right. eapply ungood_acnv_mu; eauto.
Qed.

(* to rework , why ?*)
Lemma mx_sum `{
  gLtsP : gLts P A, !FiniteImagegLts P A, 
  gLtsE : !gLts E A, !gLtsEq E A, !Good E A good}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  ps1 ps2 e : mustx ps1 e 
    -> mustx ps2 e 
      -> mustx (ps1 ∪ ps2) e.
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
    intros q mem. eapply H4 in mem as (q0 & mem & l).
    eapply elem_of_union in mem. destruct mem.
    eapply elem_of_union. left. eapply lts_tau_set_from_pset_ispec; eassumption.
    eapply elem_of_union. right. eapply lts_tau_set_from_pset_ispec; eassumption.
    eapply lem_dec in H6 as (Y' & Z' & Y_spec' & Z_spec' & eq).
    remember Y' as Y_'.
    remember Z' as Z_'.
    destruct Y_' using set_ind_L.
    + destruct Z_' using set_ind_L.
      ++ exfalso.
         assert (exists p, p ∈ ps') as (p & mem).
         destruct ps' using set_ind_L. contradiction.
         exists x. set_solver.
         eapply H4 in mem as (p0 & mem & l).
         eapply elem_of_union in mem. destruct mem.
         eapply lts_tau_set_from_pset_ispec in l; set_solver.
         eapply lts_tau_set_from_pset_ispec in l; set_solver.
      ++ assert (Y' = ∅) by set_solver.
         assert (Z' = ps') by set_solver. subst.
         inversion hmx2; subst. set_solver.
         eapply pt0. intros t mem. eapply lts_tau_set_from_pset_ispec. set_solver. set_solver.
    + destruct Z_' using set_ind_L.
      ++ assert (Y' = ps') by set_solver.
         assert (mustx ps e) by eauto with mdb.
         inversion H8; subst. set_solver.
         eapply pt0. intros t mem. eapply lts_tau_set_from_pset_ispec. set_solver. set_solver.
      ++ subst.
         replace ps' with (({[x]} ∪ X) ∪ ({[x0]} ∪ X0)) by set_solver.
         eapply H1.
         intros t mem. apply lts_tau_set_from_pset_ispec. set_solver. set_solver.
         inversion hmx2; subst. now contradiction nh.
         eapply pt0.
         intros t mem. eapply lts_tau_set_from_pset_ispec. set_solver. set_solver.
  - intros e' l. eapply H2; eauto with mdb.
    inversion hmx2; subst; eauto with mdb. contradiction.
  - intros e' μ μ' ps' duo l ps'_spec neq_nil.
    destruct (good_decidable e'); eauto with mdb.
    assert (HAps : forall p, p ∈ ps -> p ⇓ [μ]).
    intros p0 mem0.
    eapply cnv_act. edestruct (mustx_terminate_ungood ps); eauto with mdb.
    contradiction.
    intros p' hw. eapply cnv_nil.
    edestruct (mustx_terminate_ungood {[p']}). eapply com; eauto.
    intros j memj. eapply elem_of_singleton_1 in memj. subst.
    exists p0. split; eauto. set_solver.
    set_solver.
    set (Y := wt_s_set_from_pset ps [μ] HAps).
    assert (HAX2 : forall p, p ∈ ps2 -> p ⇓ [μ]).
    intros p0 mem0.
    eapply cnv_act. edestruct (mustx_terminate_ungood ps2); eauto with mdb.
    contradiction.
    intros p' hw. eapply cnv_nil.
    edestruct (mustx_terminate_ungood {[p']}).
    inversion hmx2; subst. contradiction. eapply com0; eauto.
    intros j memj. eapply elem_of_singleton_1 in memj. subst.
    exists p0. split; eauto. set_solver. set_solver.
    set (Z := wt_s_set_from_pset ps2 [μ] HAX2).
    assert (ps' ⊆ Y ∪ Z).
    intros q mem. eapply ps'_spec in mem as (q0 & mem & l').
    eapply elem_of_union in mem. destruct mem.
    eapply elem_of_union. left. eapply wt_s_set_from_pset_ispec; eassumption.
    eapply elem_of_union. right. eapply wt_s_set_from_pset_ispec; eassumption.
    eapply lem_dec in H4 as (Y0 & Z0 & Y_spec0 & Z_spec0 & eq).
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
         eapply com0. eassumption. eassumption. intros t mem.
         eapply (wt_s_set_from_pset_ispec ps2 [μ] HAX2).
         set_solver. set_solver.
    + destruct Z0 using set_ind_L.
      ++ inversion hmx2; subst. now contradict nh.
         eapply com. eassumption. eassumption. intros t mem.
         eapply (wt_s_set_from_pset_ispec ps [μ] HAps).
         set_solver. set_solver.
      ++ replace ps' with (({[x]} ∪ X) ∪ ({[x0]} ∪ X0)) by set_solver.
         eapply H3; eauto with mdb.
         intros t mem.
         eapply (wt_s_set_from_pset_ispec ps [μ] HAps).
         set_solver. set_solver.
         inversion hmx2; subst. now contradict nh.
         eapply com0. eassumption. eassumption.
         intros t mem.
         eapply (wt_s_set_from_pset_ispec ps2 [μ] HAX2).
         set_solver. set_solver.
Qed.

Lemma mx_forall `{
  gLtsP : gLts P A, !FiniteImagegLts P A,
  gLtsE : !gLts E A, !gLtsEq E A, !Good E A good} 

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  ps e :
  ps ≠ ∅ 
    -> (forall p, p ∈ ps -> mustx {[p]} e) 
      -> mustx ps e.
Proof.
  intros neq_nil hm.
  induction ps using set_ind_L.
  - set_solver.
  - destruct (set_choose_or_empty X).
    eapply mx_sum; set_solver.
    assert (X = ∅) by set_solver.
    rewrite H3, union_empty_r_L. set_solver.
Qed.

Lemma wt_nil_mx `{
  gLtsP : gLts P A, !FiniteImagegLts P A,
  gLtsE : !gLts E A, !gLtsEq E A, !Good E A good}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE} :

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
  gLtsE : !gLts E A, !gLtsEq E A, !Good E A good}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  p1 p2 e e' μ μ':
  parallel_inter μ μ' -> ¬ good e -> mustx {[ p1 ]} e 
    -> e ⟶[μ'] e' -> p1 ⟹{μ} p2 -> mustx {[p2]} e'.
Proof.
  intros duo nh hmx l w.
  inversion hmx; subst.
  - contradiction.
  - eapply com; eauto with mdb. exists p1. set_solver.
Qed.

Lemma must_set_if_must `{
  gLtsP : gLts P A, !FiniteImagegLts P A, 
  gLtsE : !gLts E A, !gLtsEq E A, !Good E A good}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p : P) (e : E) : must p e -> mustx {[ p ]} e.
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
  gLtsP : gLts P A, !FiniteImagegLts P A,
  gLtsE : !gLts E A, !gLtsEq E A, !Good E A good}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (ps : gset P) (e : E) : 
  mustx ps e 
    -> forall p, p ∈ ps 
      -> must p e.
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
      eapply (H1 X'); eauto.
      intros p0 mem0%elem_of_list_to_set%lts_tau_set_spec. set_solver. set_solver.
    + eauto with mdb.
    + intros p' e' μ μ' duo hlp hle.
      set (X' := list_to_set (
                     map proj1_sig (enum $ dsig (lts_step p (ActExt μ)))
                   ) : gset P).
      assert (p' ∈ X').
      eapply elem_of_list_to_set, elem_of_list_fmap; eauto.
      exists (dexist p' hlp). split. eauto. eapply elem_of_enum.
      eapply (H3 e' μ μ' X'). eassumption. eassumption.
      intros p0 mem0%elem_of_list_to_set.
      eapply elem_of_list_fmap in mem0 as ((r & l) & eq & mem'). subst.
      exists p. split; eauto.
      eapply wt_act.
      eapply bool_decide_unpack. eauto. eapply wt_nil. set_solver. set_solver.
Qed.

Lemma must_if_must_set `{
  gLtsP : gLts P A, !FiniteImagegLts P A,
  gLtsE : !gLts E A, !gLtsEq E A, !Good E A good}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p : P) (e : E) : 
  mustx {[ p ]} e 
    -> must p e.
Proof. intros. eapply must_if_must_set_helper; set_solver. Qed.

Lemma must_set_iff_must `{
  gLtsP : gLts P A, !FiniteImagegLts P A,
  gLtsE : !gLts E A, !gLtsEq E A, !Good E A good}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p : P) (e : E) : 
  must p e <-> mustx {[ p ]} e.
Proof. split; [eapply must_set_if_must | eapply must_if_must_set]. Qed.

(* To move, also present in Completeness. *)
Lemma must_preserved_by_weak_nil_srv `{
  gLtsP : gLts P A,
  gLtsE : !gLts E A, !gLtsEq E A, !Good E A good}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p q : P) (e : E) : 
  must p e -> p ⟹ q -> must q e.
Proof.
  intros hm w.
  dependent induction w; eauto with mdb.
  eapply IHw; eauto.
  eapply must_preserved_by_lts_tau_srv; eauto.
Qed.

Lemma must_preserved_by_wt_synch_if_notgood `{
  gLtsP : gLts P A, 
  gLtsE : !gLts E A, ! gLtsEq E A, !Good E A good}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p p' : P) (r r' : E) (μ : A) (μ' : A):
  must p r 
    -> ¬ good r 
      -> parallel_inter μ μ'
        -> p ⟹{μ} p' 
          -> r ⟶[μ'] r' 
            -> must p' r'.
Proof.
  intros hm u duo hwp hwr.
  dependent induction hwp.
  - eapply IHhwp; eauto. eapply must_preserved_by_lts_tau_srv; eauto.
  - eapply must_preserved_by_weak_nil_srv; eauto.
    inversion hm. contradiction. eapply com.
    eassumption. eassumption. eassumption.
Qed.

Lemma must_set_for_all `{
  gLtsP : gLts P A, !FiniteImagegLts P A,
  gLtsE : !gLts E A, !gLtsEq E A, !Good E A good}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (X : gset P) (e : E) : 
  X ≠ ∅ 
    -> (forall p, p ∈ X -> must p e) 
      -> mustx X e.
Proof.
  intros xneq_nil hm.
  destruct (good_decidable e).
  - now eapply mx_now.
  - eapply mx_step.
    + eassumption.
    + intros p h%hm. inversion h. contradiction. eassumption.
    + intros X' xspec' xneq_nil'.
      eapply mx_forall. eassumption.
      intros p' (p0 & mem%hm & hl)%xspec'. eapply must_set_iff_must.
      inversion mem; eauto with mdb.
    + intros e' hl.
      eapply mx_forall. eassumption.
      intros p' mem%hm. eapply must_set_iff_must.
      inversion mem; eauto with mdb. contradiction.
    + intros e' μ μ' X' duo hle xspec' xneq_nil'.
      eapply mx_forall. eassumption.
      intros p' (p0 & h%hm & hl)%xspec'. eapply must_set_iff_must.
      eapply must_preserved_by_wt_synch_if_notgood; eauto.
Qed.

Lemma must_set_iff_must_for_all `{
  gLtsP : gLts P A, !FiniteImagegLts P A,
  gLtsE : !gLts E A, !gLtsEq E A, !Good E A good}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (X : gset P) (e : E) : 
  X ≠ ∅ -> (forall p, p ∈ X -> must p e) <-> mustx X e.
Proof.
  intros.
  split. now eapply must_set_for_all.
  now eapply must_if_must_set_helper.
Qed.


(* ************************************************************ *)

Definition bhv_pre_cond1__x `{FiniteImagegLts P A, FiniteImagegLts Q A} (ps : gset P) (q : Q) :=
  forall s, (forall p, p ∈ ps -> p ⇓ s) -> q ⇓ s.

Notation "ps ≼ₓ1 q" := (bhv_pre_cond1__x ps q) (at level 70).

Definition bhv_pre_cond2__x `{
  @FiniteImagegLts P A H gLtsP, PreAP : @PreExtAction A H P PreA 𝝳P gLtsP,
  @FiniteImagegLts Q A H gLtsQ, PreAQ : @PreExtAction A H Q PreA 𝝳Q gLtsQ}
  (ps : gset P) (q : Q) :=
  forall s q',
    q ⟹[s] q' -> q' ↛ ->
    (forall p, p ∈ ps -> p ⇓ s) ->
    exists p, p ∈ ps /\ exists p', p ⟹[s] p' /\ p' ↛ /\ (reduce_actions_of 𝝳P p' ⊆ reduce_actions_of 𝝳Q q').

Notation "ps ≼ₓ2 q" := (bhv_pre_cond2__x ps q) (at level 70).

#[global] Hint Unfold bhv_pre_cond1__x bhv_pre_cond2__x : mdb.

Notation "ps ≼ₓ q" := (bhv_pre_cond1__x ps q /\ bhv_pre_cond2__x ps q) (at level 70).

Lemma alt_set_singleton_iff `{
  @FiniteImagegLts P A H gLtsP, PreAP : @PreExtAction A H P PreA 𝝳P gLtsP,
  @FiniteImagegLts Q A H gLtsQ, PreAQ : @PreExtAction A H Q PreA 𝝳Q gLtsQ}
  (p : P) (q : Q) : p ≼ q <-> {[ p ]} ≼ₓ q.
Proof.
  split.
  - intros (hbhv1 & hbhv2). split.
    + intros s mem. eapply hbhv1. set_solver.
    + intros s q' w st hcnv. edestruct hbhv2; set_solver.
  - intros (h1 & h2). split.
    + intros s mem. eapply h1. set_solver.
    + intros s q' w st hcnv. edestruct h2 ; set_solver.
Qed.

Lemma bhvleqone_preserved_by_tau `{
  FiniteImagegLts P A, 
  FiniteImagegLts Q A} 
  (ps : gset P) (q q' : Q) :
  ps ≼ₓ1 q -> q ⟶ q' -> ps ≼ₓ1 q'.
Proof. intros halt1 l s mem. eapply cnv_preserved_by_lts_tau; eauto. Qed.

Lemma bhvx_preserved_by_tau `{
  @FiniteImagegLts P A H gLtsP, PreAP : @PreExtAction A H P PreA 𝝳P gLtsP,
  @FiniteImagegLts Q A H gLtsQ, PreAQ : @PreExtAction A H Q PreA 𝝳Q gLtsQ}
  (ps : gset P) (q q' : Q) : q ⟶ q' -> ps ≼ₓ q -> ps ≼ₓ q'.
Proof.
  intros l (halt1 & halt2).
  split.
  - intros s mem. eapply cnv_preserved_by_lts_tau; eauto.
  - intros s q'' w st hcnv.
    destruct (halt2 s q'') as (p' & mem & p'' & hw & hst) (* & sub0) *); eauto with mdb.
Qed.

Lemma bhvleqone_mu `{
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

Lemma bhvx_preserved_by_mu `{
  @FiniteImagegLts P A H gLtsP, PreAP : @PreExtAction A H P PreA 𝝳P gLtsP,
  @FiniteImagegLts Q A H gLtsQ, PreAQ : @PreExtAction A H Q PreA 𝝳Q gLtsQ}
  (ps0 : gset P) (q : Q) μ ps1 q' (htp : forall p, p ∈ ps0 -> terminate p) :
  q ⟶[μ] q' 
    -> wt_set_from_pset_spec ps0 [μ] ps1 
      -> ps0 ≼ₓ q 
        -> ps1 ≼ₓ q'.
Proof.
  intros lts__q ps1_spec (halt1 & halt2). split.
  - eapply bhvleqone_mu; eauto.
  -  intros s q0 wt st hcnv.
     edestruct (halt2 (μ :: s) q0) as (t & mem & p0 & p1 & wta__t & sub); eauto with mdb.
     intros p' mem'. eapply cnv_act; eauto.
     intros p'' mem1. eapply hcnv, ps1_spec; eassumption.
     eapply wt_pop in p1 as (r & w1 & w2).
     exists r. repeat split. eapply ps1_spec; eassumption. eauto.
Qed.

Lemma terminate_then_wt_refuses  `{gLts P A} p : 
  p ⤓ -> exists p', p ⟹ p' /\ p' ↛.
Proof.
  intros ht.
  induction ht.
  destruct (lts_refuses_decidable p τ).
  - exists p; eauto with mdb.
  - eapply lts_refuses_spec1 in n as (p'& l).
    destruct (H2 p' l) as (p0 & w0 & st0).
    exists p0; eauto with mdb.
Qed.

Lemma bhvx_mu_ex `{
  @FiniteImagegLts P A H gLtsP, PreAP : @PreExtAction A H P PreA 𝝳 gLtsP,
  @FiniteImagegLts Q A H gLtsQ, PreAQ : @PreExtAction A H Q PreA 𝝳 gLtsQ}
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

Lemma ungood_must_st_nleqx `{
  @gLtsObaFW P A H gLtsP gLtsEqP gLtsObaP, !FiniteImagegLts P A, PreAP : @PreExtAction A H P PreA 𝝳 gLtsP,
  @gLtsObaFW Q A H gLtsQ gLtsEqQ gLtsObaQ, !FiniteImagegLts Q A, PreAQ : @PreExtAction A H Q PreA 𝝳 gLtsQ,
  gLtsE : !gLts E A, !gLtsEq E A, !Good E A good}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}
  `{@Prop_of_Inter Q E A parallel_inter H gLtsQ gLtsE}
  
  (X : gset P) (q : Q) e : 
  ¬ good e 
    -> mustx X e 
      -> (q, e) ↛
        -> ¬ X ≼ₓ2 q.
Proof. 
  intros not_happy all_must refuses_tau_q hbhv2.

  assert (q ↛) as stable_q.
  { destruct (lts_refuses_decidable q τ) as [refuses_q | not_refuses_q].
    - exact refuses_q.
    - exfalso. eapply lts_refuses_spec1 in not_refuses_q as (q' & l).
      eapply (lts_refuses_spec2 (q ▷ e)); eauto. exists (q' ▷ e). eapply ParLeft. exact l. }

  assert (htX : ∀ p : P, p ∈ X → p ⇓ []).
  { destruct (mustx_terminate_ungood X e all_must) as [|htps]; eauto with mdb. contradiction. }

  destruct (hbhv2 [] q (wt_nil q) stable_q htX) as (p & mem & p' & wp & stp' & sub).

  assert (mustx {[ p' ]} e) as must_p'. 
  { eapply (wt_nil_mx p). eapply (mx_sub X e all_must). set_solver. eassumption. }

  destruct must_p'; eauto.
  edestruct (ex p') as ((p'' , e'') & HypTr). now eapply elem_of_singleton.

  inversion HypTr as [? ? ? ? tau_left | ? ? ? ? tau_right | ? ? ? ? ? ? ? act_left act_right]; subst.
  - eapply lts_refuses_spec2 in stp'; eauto.
  - destruct (lts_refuses_decidable e τ) as [refuses_e | not_refuses_e].
    + eapply lts_refuses_spec2 in refuses_e. eauto. eauto with mdb.
    + eapply (lts_refuses_spec2 (q ▷ e)); eauto.
      exists (q , e''). eapply ParRight; eauto.
  - destruct (decide (non_blocking μ2)) as [nb | not_nb].
    + destruct (lts_oba_fw_forward q μ2 μ1) as (q'' & Hyp).
      eapply Hyp in nb as (tr1 & tr2); eauto.
      eapply (lts_refuses_spec2 (q ▷ e)); eauto. exists (q'', e'').
      eapply ParSync; eauto.
    +  admit.
Qed.

Lemma stability_nbhvleqtwo `{
  @gLtsObaFW P A H gLtsP gLtsEqP gLtsObaP, !FiniteImagegLts P A, PreAP : @PreExtAction A H P PreA 𝝳 gLtsP,
  @gLtsObaFW Q A H gLtsQ gLtsEqQ gLtsObaQ, !FiniteImagegLts Q A, PreAQ : @PreExtAction A H Q PreA 𝝳 gLtsQ,
  gLtsE : !gLts E A, !gLtsEq E A, !Good E A good}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}
  `{@Prop_of_Inter Q E A parallel_inter H gLtsQ gLtsE}

  (X : gset P) (q : Q) e : 
  ¬ good e 
    -> mustx X e 
      -> X ≼ₓ2 q 
        -> exists t, (q, e) ⟶{τ} t.
Proof.
  intros nhg hmx hleq.
  destruct (lts_refuses_decidable (q, e) τ).
  - exfalso. apply (ungood_must_st_nleqx X q e nhg hmx); eauto.
  - eapply lts_refuses_spec1 in n as (t & hl). eauto.
Qed.

Lemma soundnessx `{
  @gLtsObaFW P A H gLtsP gLtsEqP gLtsObaP, !FiniteImagegLts P A, PreAP : @PreExtAction A H P PreA 𝝳 gLtsP,
  @gLtsObaFW Q A H gLtsQ gLtsEqQ gLtsObaQ, !FiniteImagegLts Q A, PreAQ : @PreExtAction A H Q PreA 𝝳 gLtsQ,
  @gLtsObaFB E A H gLtsE gLtsEqE gLtsObaE, !FiniteImagegLts E A, !Good E A good}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}
  `{@Prop_of_Inter Q E A parallel_inter H gLtsQ gLtsE}

  (ps : gset P) (e : E) : 
  mustx ps e 
    -> forall (q : Q), ps ≼ₓ q 
      -> must q e.
Proof.
  intros hmx q (halt1 & halt2).
  dependent induction hmx.
  - eauto with mdb.
  - destruct (mustx_terminate_ungood ps e ltac:(eauto with mdb)).
    contradiction.
    assert (q_conv : q ⤓).
    eapply cnv_terminate, halt1; intros; eapply cnv_nil.
    destruct (mustx_terminate_ungood ps e); eauto with mdb.
    induction q_conv as [q tq IHq_conv].
    eapply m_step.
    + eassumption.
    + eapply (stability_nbhvleqtwo ps); eauto with mdb.
    + intros q' l. eapply IHq_conv.
      ++ eassumption.
      ++ eapply bhvleqone_preserved_by_tau; eauto.
      ++ eauto with mdb.
    + intros e' hle. eapply H6; eassumption.
    + intros q' e' μ μ' inter le lq.
      destruct (decide (good e')).
      ++ eapply m_now. assumption.
      ++ assert (HA : forall p, p ∈ ps -> p ⇓ [μ]).
         intros; eapply ungood_acnv_mu; eauto with mdb.
         set (ts := wt_s_set_from_pset ps [μ] HA).
         set (ts_spec := wt_s_set_from_pset_ispec ps [μ] HA).
         assert ((exists p, p ∈ ts) \/ ts ≡ ∅)%stdpp as [neq_nil | eq_nil]
          by (eapply set_choose_or_empty).
         eapply H7; eauto with mdb.
         destruct ts_spec. eassumption.
         intro eq_nil. destruct neq_nil as (t & mem).
         replace ts with (wt_s_set_from_pset ps [μ] HA) in mem; eauto.
         subst. rewrite eq_nil in mem. inversion mem.
         eapply bhvleqone_mu; eauto with mdb.
         eapply bhvx_preserved_by_mu; eauto with mdb.
         exfalso.
         edestruct (bhvx_mu_ex ps q q' (μ)) as (p' & u); eauto.
         assert (p' ∈ ts) as mem.
         edestruct (u p' ltac:(set_solver)) as (r & mem & hw).
         eapply ts_spec; eauto.
         set_solver.
Qed.

Lemma soundness_fw `{
  @gLtsObaFW P A H gLtsP gLtsEqP V, !FiniteImagegLts P A, PreAP : @PreExtAction A H P PreA 𝝳 gLtsP,
  @gLtsObaFW Q A H gLtsQ gLtsEqQ T, !FiniteImagegLts Q A, PreAQ : @PreExtAction A H Q PreA 𝝳 gLtsQ,
  @gLtsObaFB E A H gLtsE gLtsEqE W, !FiniteImagegLts E A, !Good E A good }

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}
  `{@Prop_of_Inter Q E A parallel_inter H gLtsQ gLtsE}

  (p : P) (q : Q) : p ≼ q -> p ⊑ q.
Proof.
  intros halt e hm.
  eapply (soundnessx {[p]}).
  now eapply must_set_iff_must. now eapply alt_set_singleton_iff.
Qed.

Lemma soundness `{
  @gLtsObaFB P A H gLtsP gLtsEqP V, !FiniteImagegLts P A,
  @gLtsObaFB Q A H gLtsQ gLtsEqQ T, !FiniteImagegLts Q A,
  @gLtsObaFB E A H gLtsE gLtsEqE W, !FiniteImagegLts E A, !Good E A good }

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}
  `{@Prop_of_Inter Q E A parallel_inter H gLtsQ gLtsE}

  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}
  `{@Prop_of_Inter (P * mb A) E A parallel_inter H (inter_lts fw_inter) gLtsE}

  `{@Prop_of_Inter Q (mb A) A fw_inter H gLtsQ MbgLts}
  `{@Prop_of_Inter (Q * mb A) E A parallel_inter H (inter_lts fw_inter) gLtsE}

  `{PreAP : @PreExtAction A H (P * mb A) PreA 𝝳 (inter_lts fw_inter),
    PreAQ : @PreExtAction A H (Q * mb A) PreA 𝝳 (inter_lts fw_inter)}
  (p : P) (q : Q) : p ▷ ∅ ≼ q ▷ ∅ -> p ⊑ q.
Proof.
  intros halt e hm.
  eapply Lift.must_iff_must_fw in hm.
  eapply Lift.must_iff_must_fw.
  now eapply (soundness_fw (p ▷ ∅) (q ▷ ∅)).
Qed.
