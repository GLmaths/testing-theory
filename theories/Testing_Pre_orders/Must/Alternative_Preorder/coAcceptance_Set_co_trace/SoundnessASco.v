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

From TestingTheory Require Import SyncActions gLts Bisimulation Lts_OBA Lts_Finite_Output_Chain Lts_FW Lts_OBA_FB Lts_CN
      Must Subset_Act InteractionBetweenLts ParallelLTSConstruction ForwarderConstruction
      Termination Convergence WeakTransitions Lift Testing_Predicate DefinitionAS MultisetLTSConstruction StateTransitionSystems.
From TestingTheory Require Import ActTau InFiniteSetHelper InListPropHelper.
From TestingTheory Require Import coWeakTransition coConvergence DefinitionASco
      FiniteImageLTS coFiniteImage coSetLTSConstruction DefinitionASco.

(** * Soundness for the co-acceptance-set preorder

    Two alphabets throughout: the processes over [Aproc], the observers and
    the co-traces over [Atest], linked by [sync]; on one alphabet [sync] is
    [dual].  The computations of [p ∥ t] are any [ParStsSpec]. *)

(** ** Must for a set of processes *)

Inductive mustx `{
    gLtsP : @gLts P Aproc Hp, CP : !Countable P,
    gLtsT : ! @gLtsEq T Atest Ht, !Testing_Predicate outcome _,
    SA : !SyncAction Aproc Atest, STS : !ParSts P T gLtsP gLtsT, !ParStsSpec P T gLtsP gLtsT SA STS}
  (X : gset P) (t : T) : Prop :=
| mx_now (hh : outcome t) : mustx X t
| mx_step
    (nh : ¬ outcome t)
    (ex : ∀ (p : P), p ∈ X → ∃ y, sts_step (Sts := par_sts) (p, t) y)
    (pt : ∀ X',
        lts_tau_set_from_pset_spec1 X X' → X' ≠ ∅ →
        mustx X' t)
    (et : ∀ (t' : T), t ⟶ t' → mustx X t')
    (com : ∀ (t' : T) (η : Atest) (X' : gset P),
        t ⟶[η] t' →
        cowt_set_from_pset_spec1 X η X' →
        X' ≠ ∅ →
        mustx X' t')
  : mustx X t.

#[global] Hint Constructors mustx:mdb.
Global Notation "X 'must_pass_x' t" := (mustx X t) (at level 70).

Section Must_for_sets_sync.

Context {P T Aproc Atest : Type}.
Context `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest}.
Context `{gLtsP : !gLts P Hp}.
Context `{gLtsT : !gLtsEq T Ht}.
Context (outcome : T → Prop) `{TP : !Testing_Predicate outcome gLtsT}.
Context `{SA : !SyncAction Aproc Atest} `{STS : !ParSts P T gLtsP gLtsT} `{!ParStsSpec P T gLtsP gLtsT SA STS}.
Context `{CFI : !coFiniteImagegLts P Atest}.

(** ** Must predicate for sets *)

Lemma mx_sub X t :
  mustx X t → ∀ X', X' ⊆ X → mustx X' t.
Proof.
  intros hmx. dependent induction hmx.
  - intros. by apply mx_now.
  - intros qs sub.
    apply mx_step; eauto with mdb.
    + intros qs' hs hneq_nil.
      destruct (cowt_tau_set_from_pset_ispec X) as (Hspec1 & Hspec2).
      eapply H; eauto with mdb.
      ++ destruct (set_choose_or_empty qs') as [(q' & l'%hs) | hemp].
         +++ intro eq_nil. destruct l' as (q & mem%sub & l).
             assert (hin : q' ∈ cowt_tau_set_from_pset X)
               by (eapply Hspec2; [exact mem | exact l]).
             set_solver.
         +++ set_solver.
      ++ intros p (q & mem%sub & l)%hs. eapply Hspec2; [exact mem | exact l].
    + intros t' η qs' hle hwqs hneq_nil.
      eapply (H1 t' η); eauto. intros p' mem%hwqs. set_solver.
Qed.

Lemma mx_mem X t :
  mustx X t → ∀ p, p ∈ X → mustx ({[ p ]} : gset P) t.
Proof. intros hmx p mem. eapply mx_sub; set_solver. Qed.

Lemma mustx_terminate_unoutcome X t :
  mustx X t → outcome t ∨ ∀ p, p ∈ X → p ⤓.
Proof.
  intros hmx.
  induction hmx.
  - now left.
  - right.
    intros p mem.
    eapply tstep. intros p' l.
    edestruct (H {[p']}); [exists p; set_solver | | |]; set_solver.
Qed.

Lemma mustx_terminate_unoutcome' X (t : T) :
  mustx X t → ¬ outcome t → ∀ p, p ∈ X → p ⤓.
Proof.
  intros hmx not_happy p mem.
  dependent induction hmx.
  + contradiction.
  + eapply tstep.
    intros q tr. eapply H; eauto.
    assert (h1 : lts_tau_set_from_pset_spec1 X {[q]}).
    exists p. assert (q0 = q); subst. set_solver. split; eauto. eauto.
    set_solver. set_solver.
Qed.

Lemma unoutcome_acnv_mu X t t' :
  mustx X t →
  ∀ (η : Atest) p, p ∈ X → t ⟶[η] t' →
  ¬ outcome t → ¬ outcome t' → p ⇓ᶜᵒ [η].
Proof.
  intros hmx η p mem l not_happy not_happy'.
  dependent induction hmx.
  - contradiction.
  - assert (hmX : mustx X t) by (apply mx_step; assumption).
    destruct (mustx_terminate_unoutcome X t hmX) as [happy | finish].
    + contradiction.
    + eapply cocnv_act.
      -- by eapply finish.
      -- intros q w.
         assert (h1 : cowt_set_from_pset_spec1 X η {[q]}).
         { exists p. split; set_solver. }
         assert (h2 : {[q]} ≠ (∅ : gset P)) by set_solver.
         set (hm := com t' η {[ q ]} l h1 h2).
         destruct (mustx_terminate_unoutcome _ _ hm) as [happy' | finish'].
         +++ contradiction.
         +++ eapply cocnv_nil. eapply finish'. set_solver.
Qed.

Lemma must_mu_either_outcome_cnv X t t' :
  mustx X t →
  ∀ (η : Atest) p, p ∈ X → t ⟶[η] t' →
  outcome t ∨ outcome t' ∨ p ⇓ᶜᵒ [η].
Proof.
  intros hmx η p mem l.
  destruct (decide (outcome t)); destruct (decide (outcome t')).
  + left; eauto.
  + left; eauto.
  + right; eauto.
  + right. right. eapply unoutcome_acnv_mu; eauto.
Qed.

(** *** The union of two sets that pass an observer passes it *)

Lemma mx_sum X X' t : mustx X t → mustx X' t → mustx (X ∪ X') t.
Proof.
  intros hmx1 hmx2. revert X' hmx2.
  dependent induction hmx1.
  { intros. by apply mx_now. }
  intros ps2 hmx2.
  eapply mx_step.
  - eassumption.
  - intros p mem.
    eapply elem_of_union in mem.
    destruct mem.
    eapply ex; eassumption.
    inversion hmx2; subst. contradiction.
    eapply ex0; eassumption.
  - intros X' hs hne.
    assert (hsub : X' ⊆ cowt_tau_set_from_pset X ∪ cowt_tau_set_from_pset ps2).
    { intros q mem. eapply hs in mem as (q0 & mem & l).
      eapply elem_of_union in mem. destruct mem.
      eapply elem_of_union. left. eapply cowt_tau_set_from_pset_ispec; eassumption.
      eapply elem_of_union. right. eapply cowt_tau_set_from_pset_ispec; eassumption. }
    eapply lem_dec in hsub as (Y' & Z' & Y_spec' & Z_spec' & eq).
    remember Y' as Y_'. remember Z' as Z_'.
    destruct Y_' using set_ind_L.
    + destruct Z_' using set_ind_L.
      ++ exfalso. apply hne. set_solver.
      ++ assert (hY : Y' = ∅) by set_solver.
         assert (hZ : Z' = X') by set_solver. subst.
         inversion hmx2 as [hh | nh2 ex2 pt2 et2 com2]; subst; [contradiction |].
         eapply pt2; [| exact hne].
         intros q mem. eapply cowt_tau_set_from_pset_ispec. set_solver.
    + destruct Z_' using set_ind_L.
      ++ assert (hY : Y' = X') by set_solver.
         assert (hmX : mustx X t) by (apply mx_step; assumption).
         inversion hmX as [hh | nh1 ex1 pt1 et1 com1]; subst; [contradiction |].
         eapply pt1; [| exact hne].
         intros q mem. eapply cowt_tau_set_from_pset_ispec. set_solver.
      ++ subst.
         replace X' with (({[x]} ∪ X0) ∪ ({[x0]} ∪ X1)) by set_solver.
         eapply H.
         +++ intros q mem. eapply cowt_tau_set_from_pset_ispec. set_solver.
         +++ set_solver.
         +++ inversion hmx2 as [hh | nh2 ex2 pt2 et2 com2]; subst; [contradiction |].
             eapply pt2; [| set_solver].
             intros q mem. eapply cowt_tau_set_from_pset_ispec. set_solver.
  - intros t' l. eapply H0; [exact l |].
    inversion hmx2 as [hh | nh2 ex2 pt2 et2 com2]; subst; [contradiction | by eapply et2].
  - intros t' η ps' l ps'_spec neq_nil.
    destruct (decide (outcome t')); [by apply mx_now |].
    assert (HAX : ∀ p, p ∈ X → p ⇓ᶜᵒ [η]).
    { intros p0 mem0.
      eapply cocnv_act.
      - assert (hmX : mustx X t) by (apply mx_step; assumption).
        destruct (mustx_terminate_unoutcome X t hmX) as [happy | finish];
          [contradiction | by eapply finish].
      - intros p' hw. eapply cocnv_nil.
        assert (h1 : cowt_set_from_pset_spec1 X η {[p']}).
        { intros j memj. eapply elem_of_singleton_1 in memj. subst.
          exists p0. split; eauto. }
        assert (h2 : {[p']} ≠ (∅ : gset P)) by set_solver.
        destruct (mustx_terminate_unoutcome _ _ (com t' η {[p']} l h1 h2))
          as [happy' | finish']; [contradiction |].
        eapply finish'. set_solver. }
    assert (HAX2 : ∀ p, p ∈ ps2 → p ⇓ᶜᵒ [η]).
    { intros p0 mem0.
      inversion hmx2 as [hh | nh2 ex2 pt2 et2 com2]; subst; [contradiction |].
      eapply cocnv_act.
      - destruct (mustx_terminate_unoutcome ps2 t hmx2) as [happy | finish];
          [contradiction | by eapply finish].
      - intros p' hw. eapply cocnv_nil.
        assert (h1 : cowt_set_from_pset_spec1 ps2 η {[p']}).
        { intros j memj. eapply elem_of_singleton_1 in memj. subst.
          exists p0. split; eauto. }
        assert (h2 : {[p']} ≠ (∅ : gset P)) by set_solver.
        destruct (mustx_terminate_unoutcome _ _ (com2 t' η {[p']} l h1 h2))
          as [happy' | finish']; [contradiction |].
        eapply finish'. set_solver. }
    assert (hsub : ps' ⊆ cowt_s_set_from_pset X η HAX
                       ∪ cowt_s_set_from_pset ps2 η HAX2).
    { intros q mem. eapply ps'_spec in mem as (q0 & mem & l').
      eapply elem_of_union in mem. destruct mem.
      eapply elem_of_union. left. eapply cowt_s_set_from_pset_ispec; eassumption.
      eapply elem_of_union. right. eapply cowt_s_set_from_pset_ispec; eassumption. }
    eapply lem_dec in hsub as (Y0 & Z0 & Y_spec0 & Z_spec0 & eq).
    destruct Y0 using set_ind_L.
    + destruct Z0 using set_ind_L.
      ++ exfalso. apply neq_nil. set_solver.
      ++ inversion hmx2 as [hh | nh2 ex2 pt2 et2 com2]; subst; [contradiction |].
         eapply com2; [exact l | | exact neq_nil].
         intros q mem. eapply (cowt_s_set_from_pset_ispec ps2 η HAX2). set_solver.
    + destruct Z0 using set_ind_L.
      ++ eapply com; [exact l | | exact neq_nil].
         intros q mem. eapply (cowt_s_set_from_pset_ispec X η HAX). set_solver.
      ++ replace ps' with (({[x]} ∪ X0) ∪ ({[x0]} ∪ X1)) by set_solver.
         eapply H1; [exact l | | set_solver |].
         +++ intros q mem. eapply (cowt_s_set_from_pset_ispec X η HAX). set_solver.
         +++ inversion hmx2 as [hh | nh2 ex2 pt2 et2 com2]; subst; [contradiction |].
             eapply com2; [exact l | | set_solver].
             intros q mem. eapply (cowt_s_set_from_pset_ispec ps2 η HAX2). set_solver.
Qed.

(** *** From singletons to arbitrary sets, and back to [must] *)

Lemma mx_forall X t :
  X ≠ ∅ → (∀ p, p ∈ X → mustx ({[p]} : gset P) t) → mustx X t.
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
    + assert (heq : X = ∅) by set_solver.
      rewrite heq, union_empty_r_L. set_solver.
Qed.

Lemma wt_nil_mx :
  ∀ p1 p2 t, mustx ({[ p1 ]} : gset P) t → p1 ⟹ p2 →
    mustx ({[ p2 ]} : gset P) t.
Proof.
  intros p1 p2 e hmx wt.
  dependent induction wt; subst; [assumption |].
  inversion hmx as [hh | nh ex pt et com]; subst.
  - by apply mx_now.
  - eapply IHwt; [| reflexivity].
    eapply pt; [| set_solver].
    intros p2 mem. replace q with p2 in * by set_solver.
    exists p; set_solver.
Qed.

Lemma wt_nil_mx_set (X : gset P) (X' : gset P) t :
  mustx X t → wt_set_from_pset_spec1 X [] X' → mustx X' t.
Proof.
  intros hmx wt_tr.
  destruct (set_choose_or_empty X') as [(x' & mem) | Hemp].
  - eapply mx_forall.
    + set_solver.
    + intros p' mem'.
      eapply wt_tr in mem' as (p & mem'' & w).
      eapply wt_nil_mx.
      * eapply mx_mem; eauto.
      * exact w.
  - assert (heq : X' = ∅) by set_solver.
    subst. clear wt_tr.
    induction hmx.
    + now eapply mx_now.
    + eapply mx_step.
      * eassumption.
      * intros p mem. inversion mem.
      * intros Y hY hYne.
        exfalso. apply hYne.
        apply leibniz_equiv. intros y. split; [| set_solver].
        intros mem. eapply hY in mem as (p' & mem_imp & tr). set_solver.
      * intros t' l. eapply H0; eauto.
      * intros t' η Y l hY hYne.
        exfalso. apply hYne.
        apply leibniz_equiv. intros y. split; [| set_solver].
        intros mem. eapply hY in mem as (p' & mem_imp & tr). set_solver.
Qed.

Lemma co_wt_mu_mx p1 p2 t t' (η : Atest) :
  ¬ outcome t → mustx ({[ p1 ]} : gset P) t →
  t ⟶[η] t' → p1 ⟹ᶜᵒ[[η]] p2 → mustx ({[p2]} : gset P) t'.
Proof.
  intros nh hmx l w.
  inversion hmx; subst.
  - contradiction.
  - eapply com; eauto with mdb. exists p1. set_solver.
Qed.

Lemma wt_mu_mx_set X X' t t' (η : Atest) :
  ¬ outcome t → mustx X t →
  t ⟶[η] t' → cowt_set_from_pset_spec1 X η X' → X' ≠ ∅ →
  mustx X' t'.
Proof.
  intros nh hmx l w hne.
  inversion hmx; subst.
  - contradiction.
  - eapply com; eauto.
Qed.

Lemma must_set_if_must (p : P) (t : T) :
  p must_pass t → mustx ({[ p ]} : gset P) t.
Proof.
  intro hm. dependent induction hm.
  - by apply mx_now.
  - eapply mx_step.
    + eassumption.
    + set_solver.
    + intros ps' hs hneq_nil.
      unfold lts_tau_set_from_pset_spec1 in hs.
      eapply mx_forall; set_solver.
    + eauto with mdb.
    + intros e' η X' hle hws hneq_nil.
      eapply mx_forall. eassumption.
      intros.
      edestruct hws as (p' & mem%elem_of_singleton_1 & w); subst; eauto.
      inversion w; subst.
      ++ eapply co_wt_mu_mx; [exact nh | by eapply H | exact hle | eassumption].
      ++ eapply wt_nil_mx; [by eapply H1 | by eapply cowt_iff_wt_nil].
Qed.

Lemma must_if_must_set_helper (X : gset P) (t : T) :
  mustx X t → ∀ p, p ∈ X → p must_pass t.
Proof.
  intro hm. dependent induction hm.
  - intros. by apply m_now.
  - intros p mem. eapply m_step.
    + eassumption.
    + by eapply ex.
    + intros p' hl.
      set (X' := list_to_set (cowt_tau_set p) : gset P).
      assert (hin : p' ∈ X').
      { eapply cowt_tau_set_spec, elem_of_list_to_set in hl; eauto. }
      eapply (H X'); eauto.
      intros p0 mem0%elem_of_list_to_set%cowt_tau_set_spec. set_solver.
      set_solver.
    + intros t' hlt. eapply H0; [exact hlt | exact mem].
    + intros p' e' μ η hsy hlp hle.
      (* the [Finite] instance for the literal-[μ] successors, cut down from
         the class's dual image at [η] *)
      assert (hfin : Finite (dsig (λ q : P, sync μ η ∧ p ⟶[μ] q))).
      { unfold dsig.
        eapply (in_list_finite
                  (map proj1_sig
                     (enum (dsig (fun q => ∃ μ', sync μ' η ∧ p ⟶[μ'] q))))).
        intros q Hq. eapply bool_decide_unpack in Hq.
        eapply list_elem_of_fmap.
        exists (dexist q (ex_intro _ μ (conj hsy (proj2 Hq)))).
        split; [reflexivity | eapply elem_of_enum]. }
      set (X' := list_to_set
                   (map proj1_sig (enum $ dsig (fun q => sync μ η ∧ p ⟶[μ] q)))
                 : gset P).
      assert (hin : p' ∈ X').
      { eapply elem_of_list_to_set, list_elem_of_fmap.
        assert (hlp' : sync μ η ∧ p ⟶[μ] p') by (split; eauto).
        exists (dexist p' hlp'). split; [reflexivity | eapply elem_of_enum]. }
      eapply (H1 e' η X'); [exact hle | | set_solver | set_solver].
      intros p0 mem0%elem_of_list_to_set.
      eapply list_elem_of_fmap in mem0 as ((r & l) & eq & mem'). subst.
      exists p. split; [exact mem |].
      eapply cowt_act; [| | eapply cowt_nil].
      ++ exact hsy.
      ++ assert (mem'' : sync μ η ∧ p ⟶[μ] r) by (eapply bool_decide_unpack; eauto).
         by destruct mem'' as (_ & tr'').
Qed.

Lemma must_if_must_set (p : P) (t : T) :
  mustx ({[ p ]} : gset P) t → p must_pass t.
Proof. intros. eapply must_if_must_set_helper; set_solver. Qed.

Lemma must_set_iff_must (p : P) (t : T) :
  p must_pass t ↔ mustx ({[ p ]} : gset P) t.
Proof. split; [eapply must_set_if_must | eapply must_if_must_set]. Qed.

Lemma must_set_for_all (X : gset P) (t : T) :
  X ≠ ∅ → (∀ p, p ∈ X → p must_pass t) → mustx X t.
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
    + intros t' η X' hle xspec' xneq_nil'.
      eapply mx_forall. eassumption.
      intros p' (p0 & h%hm & hl)%xspec'. eapply must_set_iff_must.
      eapply cowt_to_wt in hl as (s' & hf & wk_tr).
      inversion hf as [| μ0 η0 s0 s1 hsy0 hf0]; subst.
      inversion hf0; subst.
      eapply must_preserved_by_wt_synch_if_notoutcome;
        [exact h | exact n | exact hsy0 | exact wk_tr | exact hle].
Qed.

Lemma must_set_iff_must_for_all (X : gset P) (t : T) :
  X ≠ ∅ → ((∀ p, p ∈ X → p must_pass t) ↔ mustx X t).
Proof.
  intros.
  split; [now eapply must_set_for_all | now eapply must_if_must_set_helper].
Qed.

End Must_for_sets_sync.

(** ** Contextual preorder for sets *)

(* As [ctx_pre] ([Must.v]): [outcome] and the instances are implicit. *)
Definition ctx_pre__x `{gLtsP : @gLts P Aproc Hp, CP : !Countable P,
    gLtsQ : !@gLts Q Aproc Hp, CQ : !Countable Q,
    gLtsT : !@gLtsEq T Atest Ht, !Testing_Predicate outcome _,
    SA : !SyncAction Aproc Atest,
    STSP : !ParSts P T gLtsP gLtsT, !ParStsSpec P T gLtsP gLtsT SA STSP,
    STSQ : !ParSts Q T gLtsQ gLtsT, !ParStsSpec Q T gLtsQ gLtsT SA STSQ}
  (X : gset P) (Y : gset Q) :=
  ∀ (t : T), mustx X t → mustx Y t.

Section Must_preorder_for_sets_sync.

Context {P Q T Aproc Atest : Type}.
Context `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest}.
Context `{gLtsT : !gLtsEq T Ht}.
Context (outcome : T → Prop) `{TP : !Testing_Predicate outcome gLtsT}.
Context `{SA : !SyncAction Aproc Atest}.
Context `{gLtsP : !gLts P Hp} `{STSP : !ParSts P T _ _} `{!ParStsSpec P T _ _ SA STSP}
        `{CFIP : !coFiniteImagegLts P Atest}.
Context `{gLtsQ : !gLts Q Hp} `{STSQ : !ParSts Q T _ _} `{!ParStsSpec Q T _ _ SA STSQ}
        `{CFIQ : !coFiniteImagegLts Q Atest}.

Notation "X ⊑ₛₑₜ_ₘᵤₛₜᵢ Y" := (ctx_pre__x X Y) (at level 70).

Lemma set_must_union_right (X : gset P) (Y Y' : gset Q) :
  X ⊑ₛₑₜ_ₘᵤₛₜᵢ Y → X ⊑ₛₑₜ_ₘᵤₛₜᵢ Y' → X ⊑ₛₑₜ_ₘᵤₛₜᵢ (Y ∪ Y').
Proof.
  intros Hyp1 Hyp2.
  intros t h_must.
  eapply mx_sum.
  + eapply Hyp1; eauto.
  + eapply Hyp2; eauto.
Qed.

Lemma set_must_empty (X : gset P) : X ⊑ₛₑₜ_ₘᵤₛₜᵢ ∅.
Proof.
  intros t h_must.
  induction h_must.
  + now eapply mx_now.
  + eapply mx_step.
    * exact nh.
    * intros p mem. inversion mem.
    * intros X' hs hne. destruct X' using set_ind_L.
      - exfalso. by apply hne.
      - assert (mem'' : x ∈ {[x]} ∪ X0) by set_solver.
        eapply hs in mem'' as (p' & mem_imp & tr). inversion mem_imp.
    * intros t' hlt. by eapply H0.
    * intros t' η X' hle hs hne. destruct X' using set_ind_L.
      - exfalso. by apply hne.
      - assert (mem'' : x ∈ {[x]} ∪ X0) by set_solver.
        eapply hs in mem'' as (p' & mem_imp & tr). inversion mem_imp.
Qed.

Lemma set_must_union_left_rev (X : gset P) (Y Y' : gset Q) :
  X ⊑ₛₑₜ_ₘᵤₛₜᵢ (Y ∪ Y') → X ⊑ₛₑₜ_ₘᵤₛₜᵢ Y.
Proof.
  intros Hyp t h_must.
  induction Y using set_ind_L.
  - eapply set_must_empty; eauto.
  - eapply Hyp in h_must. eapply must_set_for_all. set_solver.
    intros. eapply must_if_must_set_helper in h_must.
    set_solver. set_solver.
Qed.

Lemma set_must_union_right_rev (X : gset P) (Y Y' : gset Q) :
  X ⊑ₛₑₜ_ₘᵤₛₜᵢ (Y ∪ Y') → X ⊑ₛₑₜ_ₘᵤₛₜᵢ Y'.
Proof.
  intros Hyp t h_must.
  induction Y' using set_ind_L.
  - eapply set_must_empty; eauto.
  - eapply Hyp in h_must. eapply must_set_for_all. set_solver.
    intros. eapply must_if_must_set_helper in h_must.
    set_solver. set_solver.
Qed.

Lemma set_must_sub (X : gset P) (Y : gset Q) :
  X ⊑ₛₑₜ_ₘᵤₛₜᵢ Y → ∀ Y', Y' ⊆ Y → X ⊑ₛₑₜ_ₘᵤₛₜᵢ Y'.
Proof.
  intros Hyp Y' sub t h_must.
  destruct Y' using set_ind_L.
  + eapply set_must_empty; eauto.
  + eapply Hyp in h_must. eapply must_set_for_all. set_solver.
    intros. eapply must_if_must_set_helper in h_must.
    set_solver. set_solver.
Qed.

(** ** The set preorder on singletons is the process preorder *)

Lemma must_set_singleton_iff (p : P) (q : Q) :
  p ⊆ₘᵤₛₜᵢ q ↔ ({[ p ]} : gset P) ⊑ₛₑₜ_ₘᵤₛₜᵢ ({[ q ]} : gset Q).
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

End Must_preorder_for_sets_sync.

#[global] Hint Unfold ctx_pre__x : mdb.
Notation "X ⊑ₛₑₜ_ₘᵤₛₜᵢ Y" := (ctx_pre__x X Y) (at level 70).
Notation "X ⋢ₛₑₜ_ₘᵤₛₜᵢ Y" := (¬ ctx_pre__x X Y) (at level 70).

(** [⊑ₛₑₜ_ₘᵤₛₜᵢ] is a preorder. *)

Section Must_preorder_for_sets_instances.

Context {P T Aproc Atest : Type}.
Context `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest}.
Context `{gLtsT : !gLtsEq T Ht}.
Context (outcome : T → Prop) `{TP : !Testing_Predicate outcome gLtsT}.
Context `{SA : !SyncAction Aproc Atest}.
Context `{gLtsP : !gLts P Hp} `{STSP : !ParSts P T _ _} `{!ParStsSpec P T _ _ SA STSP}
        `{CFIP : !coFiniteImagegLts P Atest}.

(* The relation ⊑ₛₑₜ_ₘᵤₛₜᵢ is reflexive *)
#[global] Instance set_must_refl : Reflexive (ctx_pre__x : relation (gset P)).
Proof. intros X t h_must. exact h_must. Qed.

(* The relation ⊑ₛₑₜ_ₘᵤₛₜᵢ is transitive *)
#[global] Instance set_must_transitive : Transitive (ctx_pre__x : relation (gset P)).
Proof.
  intros X Y Z hcgr1 hcgr2. intros t h_must.
  eapply hcgr2. eapply hcgr1; eauto.
Qed.

(* The relation ⊑ₛₑₜ_ₘᵤₛₜᵢ is a preorder *)
#[global] Instance set_must_x_preorder : PreOrder (ctx_pre__x : relation (gset P)).
Proof.
  split.
  + exact set_must_refl.
  + exact set_must_transitive.
Qed.

End Must_preorder_for_sets_instances.

Notation "X ≂ₛₑₜ_ₘᵤₛₜᵢ Y" := (Y ⊑ₛₑₜ_ₘᵤₛₜᵢ X /\ X ⊑ₛₑₜ_ₘᵤₛₜᵢ Y) (at level 70).

(** ** The alternative preorder, on sets

    [mustx_alt_co] and its bridge are commented out in [SoundnessASco.v]
    (they are the one piece that would need the set LTS on the [P] side), so
    there is nothing to port for them. *)

Definition bhv_pre_co_cond1__x `{gLtsP : @gLts P Aproc Hp, !Countable P}
  `{gLtsQ : !@gLts Q Aproc Hp, !Countable Q}
  `{Ht : ExtAction A} `{SA : !SyncAction Aproc A}
  (X : gset P) (Y : gset Q) :=
  ∀ (s : trace A), (∀ p, p ∈ X → p ⇓ᶜᵒ s) → (∀ q, q ∈ Y → q ⇓ᶜᵒ s).

Global Notation "X ₁≼꜀ₒ₋ₛₑₜ_ₐₛ Y" := (bhv_pre_co_cond1__x X Y) (at level 70).

Definition bhv_pre_co_cond2__x
  `{gLtsP : @gLts P Aproc Hp, !Countable P}
  `{gLtsQ : !@gLts Q Aproc Hp, !Countable Q}
  `{gLtsT : @gLtsEq T A H} `{SA : !SyncAction Aproc A}
  `{AbsPT : !@AbsAction P T FinA PreAct A H Φ 𝝳P Aproc Hp gLtsP gLtsT SA}
  `{AbsQT : !@AbsAction Q T FinA PreAct A H Φ 𝝳Q Aproc Hp gLtsQ gLtsT SA}
  (X : gset P) (Y : gset Q) :=
  ∀ q s q', q ∈ Y →
    q ⟹ᶜᵒ[s] q' → q' ↛ →
    (∀ p, p ∈ X → p ⇓ᶜᵒ s) →
    ∃ p, p ∈ X ∧ ∃ p', p ⟹ᶜᵒ[s] p' ∧ p' ↛ ∧
           (⌈ (𝝳P ∘ Φ) ⌉ (coR p') ⊆ ⌈ (𝝳Q ∘ Φ) ⌉ (coR q')).

Global Notation "X ₂≼꜀ₒ₋ₛₑₜ_ₐₛ Y" := (bhv_pre_co_cond2__x X Y) (at level 70).

Definition bhv_pre_co__x
  `{gLtsP : @gLts P Aproc Hp, !Countable P}
  `{gLtsQ : !@gLts Q Aproc Hp, !Countable Q}
  `{gLtsT : @gLtsEq T A H} `{SA : !SyncAction Aproc A}
  `{AbsPT : !@AbsAction P T FinA PreAct A H Φ 𝝳P Aproc Hp gLtsP gLtsT SA}
  `{AbsQT : !@AbsAction Q T FinA PreAct A H Φ 𝝳Q Aproc Hp gLtsQ gLtsT SA}
  (X : gset P) (Y : gset Q) :=
  bhv_pre_co_cond1__x (A := A) X Y ∧ X ₂≼꜀ₒ₋ₛₑₜ_ₐₛ Y.

Global Notation "X ≼꜀ₒ₋ₛₑₜ_ₐₛ Y" := (bhv_pre_co__x X Y) (at level 70).

(** ** Acceptance-set preorder properties on sets *)

Section Acceptance_Set_preorder_for_sets_sync.

Context {P Q T FinA PreAct Aproc Atest : Type}.
Context `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest}.
Context `{gLtsEqT : !gLtsEq T Ht}.
Context `{gLtsP : !gLts P Hp} `{CP : !Countable P}.
Context `{gLtsQ : !gLts Q Hp} `{CQ : !Countable Q}.
Context `{SA : !SyncAction Aproc Atest}.
Context (Φ : Atest → FinA) (𝝳 : FinA → PreAct).
Context `{AbsPT : !@AbsAction P T FinA PreAct Atest Ht Φ 𝝳 Aproc Hp gLtsP gLtsEqT SA}.
Context `{AbsQT : !@AbsAction Q T FinA PreAct Atest Ht Φ 𝝳 Aproc Hp gLtsQ gLtsEqT SA}.

Notation "X '₁≼' Y" := (bhv_pre_co_cond1__x (A := Atest) X Y) (at level 70).
Notation "X '₂≼' Y" := (bhv_pre_co_cond2__x X Y) (at level 70).
Notation "X '≼' Y" := (bhv_pre_co__x X Y) (at level 70).

Lemma alt_set_singleton_iff_co (p : P) (q : Q) :
  ({[ p ]} : gset P) ≼ ({[ q ]} : gset Q) ↔
  p ≼꜀ₒ₋ₐₛ q.
Proof.
  split.
  - intros (hbhv1 & hbhv2). split.
    + intros s mem. eapply hbhv1. set_solver. set_solver.
    + intros s q' w st hcnv. edestruct hbhv2; set_solver.
  - intros (h1 & h2). split.
    + intros s mem. intros q' mem'.
      assert (heq : q' = q) by set_solver. subst. eapply h1. set_solver.
    + intros q' s q'' w st hcnv.
      assert (heq : q' = q) by set_solver. subst. intros.
      exists p. edestruct h2; set_solver.
Qed.

Lemma bhvleqone_preserved_by_reduction_co (X : gset P) (Y Y' : gset Q) :
  X ₁≼ Y → lts_tau_set_from_pset_spec1 Y Y' → X ₁≼ Y'.
Proof.
  intros halt1 l s mem.
  intros q memq. eapply l in memq as (q' & mem' & tr').
  eapply cocnv_preserved_by_lts_tau; eauto.
Qed.

Lemma bhvx_preserved_by_reductions_co (X : gset P) (Y Y' : gset Q) :
  wt_set_from_pset_spec1 Y [] Y' → X ≼ Y → X ≼ Y'.
Proof.
  intros l (halt1 & halt2).
  split.
  - intros s mem q memq.
    eapply l in memq as (q' & tr & mem').
    eapply cocnv_preserved_by_cowt_nil; eauto.
    eapply cowt_iff_wt_nil; eauto.
  - intros q' s q'' mem w st hcnv.
    eapply l in mem as (q & mem2 & tr).
    destruct (halt2 q s q'') as (p' & mem' & p'' & hw & hst); eauto with mdb.
    eapply cowt_push_nil_left; eauto. eapply cowt_iff_wt_nil; eauto.
Qed.

Lemma bhvx_preserved_by_reduction_co (X : gset P) (Y Y' : gset Q) :
  lts_tau_set_from_pset_spec1 Y Y' → X ≼ Y → X ≼ Y'.
Proof.
  intros l (halt1 & halt2).
  eapply bhvx_preserved_by_reductions_co; [| split; eauto].
  intros q' mem'. eapply l in mem' as (q'' & mem'' & wt_tr'').
  exists q''. split; eauto. eapply lts_to_wt_tau; eauto.
Qed.

Lemma bhvleqone_preserved_by_external_action_co
  (X X' : gset P) (η : Atest) (Y Y' : gset Q)
  (htp : ∀ p, p ∈ X → terminate p) :
  X ₁≼ Y → cowt_set_from_pset_spec X η X' →
  cowt_set_from_pset_spec1 Y η Y' → X' ₁≼ Y'.
Proof.
  intros hleq hws l s hcnv. intros q memq.
  eapply l in memq as (q' & mem' & wk_tr).
  eapply cocnv_preserved_by_cowt_act; eauto.
  eapply hleq.
  intros p mem''. eapply cocnv_act.
  + eapply htp; eauto.
  + intros. eapply hcnv, hws; eassumption.
  + exact mem'.
Qed.

Lemma bhvx_preserved_by_external_action_co
  (X X' : gset P) (η : Atest) (Y Y' : gset Q)
  (htp : ∀ p, p ∈ X → terminate p) :
  cowt_set_from_pset_spec1 Y η Y' →
  cowt_set_from_pset_spec X η X' →
  X ≼ Y → X' ≼ Y'.
Proof.
  intros lts__q ps1_spec (halt1 & halt2). split.
  - eapply bhvleqone_preserved_by_external_action_co; eauto.
  - intros q s q0 mem wt st hcnv.
    assert (tr'' : cowt_set_from_pset_spec1 Y η Y') by eauto.
    eapply tr'' in mem as (q' & mem' & tr_ext); eauto.
    edestruct (halt2 q' (η :: s) q0) as (t & mem'' & p0 & p1 & wta__t & sub); eauto with mdb.
    + eapply cowt_push_left; eauto.
    + intros p'' mem1. eapply cocnv_act.
      * eapply htp; eauto.
      * intros q1 wk_tr. destruct ps1_spec as (ps1s1 & ps1s2).
        eapply ps1s2 in wk_tr; eauto.
    + eapply cowt_pop in p1 as (r & w1 & w2).
      exists r. repeat split.
      destruct ps1_spec as (ps1s1 & ps1s2). eapply ps1s2; eassumption.
      eauto.
Qed.

Lemma reverse_trace_inclusion_co (X : gset P) (Y Y' : gset Q) (η : Atest) :
  X ≼ Y → (∀ p, p ∈ X → p ⇓ᶜᵒ [η]) →
  cowt_set_from_pset_spec1 Y η Y' → Y' ≠ ∅ →
  ∃ X', cowt_set_from_pset_spec1 X η X' ∧ X' ≠ ∅.
Proof.
  intros (h1 & h2) hcnv hl not_empty.
  destruct (set_choose_L Y' not_empty) as (q0 & mem0).
  eapply hl in mem0 as (q & mem & w).
  assert (hq0 : q0 ⤓).
  { eapply cocnv_terminate.
    eapply cocnv_preserved_by_cowt_act.
    - eapply h1; eauto.
    - exact w. }
  destruct (terminate_then_wt_refuses q0 hq0) as (q0' & wq0 & stq0).
  assert (w' : q ⟹ᶜᵒ[[η]] q0').
  { eapply cowt_push_nil_right; eauto. eapply cowt_iff_wt_nil; eauto. }
  edestruct (h2 q [η] q0' mem w' stq0 hcnv) as (p & memp & p' & wp & stp & sub).
  exists ({[ p' ]}).
  split.
  - intros q1 mem1. exists p. split; eauto.
    assert (heq : q1 = p') by set_solver. subst. exact wp.
  - set_solver.
Qed.

End Acceptance_Set_preorder_for_sets_sync.

(** ** Communication-enabling property *)

(** ** Communication-enabled processes

    What the soundness proof asks of [Q]: every emission of the observer can
    be received, by /some/ action that synchronises with it.  On one
    alphabet a forwarder has it by [boomerang] ([soundness_fw_co] below); on
    [Aproc ⊎ Atest] by [fw_boomerang] ([SoundnessASsync.v]). *)

Class gLtsCNenabledSync (P Aproc Atest : Type)
  `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest}
  `{gLtsP : !gLts P Hp} `{SA : !SyncAction Aproc Atest} :=
  MkgLtsCNenabledSync {
      sync_cn_enabled (p1 : P) (η : Atest) :
        non_blocking η → ∃ β p2, sync β η ∧ p1 ⟶[β] p2;
    }.

Section Properties_for_soundness_sync.

Context {P Q T FinA PreAct Aproc Atest : Type}.
Context `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest}.
Context `{gLtsT : !gLtsEq T Ht}.
Context (outcome : T → Prop) `{TP : !Testing_Predicate outcome gLtsT}.
Context `{SA : !SyncAction Aproc Atest}.
Context `{gLtsP : !gLts P Hp}.
Context `{gLtsQ : !gLts Q Hp} `{!gLtsCNenabledSync Q Aproc Atest}.
Context (Φ : Atest → FinA) (𝝳 : FinA → PreAct).
Context `{AbsPT : !@AbsAction P T FinA PreAct Atest Ht Φ 𝝳 Aproc Hp _ _ SA}.
Context `{AbsQT : !@AbsAction Q T FinA PreAct Atest Ht Φ 𝝳 Aproc Hp _ _ SA}.

(** In the non-blocking case, [q] receives the observer's emission [η] by
    [sync_cn_enabled] — with its own action, not necessarily [p]'s. *)

Lemma communication_enabled_co (p : P) p' (q : Q) (t : T) t' μ1 (η : Atest) :
  sync μ1 η → p ⟶[μ1] p' → t ⟶[η] t' →
  ⌈ (𝝳 ∘ Φ) ⌉ (coR p) ⊆ ⌈ (𝝳 ∘ Φ) ⌉ (coR q) →
  ∃ ν1 ν2 q' t'', sync ν1 ν2 ∧ q ⟶[ν1] q' ∧ t ⟶[ν2] t''.
Proof.
  intros hsy tr tr_co sub.
  destruct (decide (non_blocking η)) as [nb | not_nb].
  + destruct (sync_cn_enabled q η nb) as (β & q' & hsyq & tr').
    exists β, η, q', t'. eauto.
  + assert (hco : η ∈ coR p).
    { eapply coR_intro; [| exact hsy | exact not_nb].
      eapply lts_refuses_spec2. by eexists. }
    eapply (map_gamma_of_action (𝝳 ∘ Φ)) in hco as mem.
    eapply sub in mem. destruct mem as (η' & mem & eq).
    simpl in eq. symmetry in eq.
    pose proof mem as (? & ? & ? & bη'). rename mem into memq.
    assert (hmapq : Φ η' ∈ ⌈ Φ ⌉ (coR q))
      by (eapply map_gamma_of_action; exact memq).
    eapply (abstraction_prog_spec (AbsAction := AbsQT) q η' η bη' not_nb eq)
      in hmapq as (η'' & memq'' & eq'').
    destruct memq'' as (ν & hnref & hsyν & bη'').
    assert (Tr_Test : η'' ∈ R t).
    { eapply (abstraction_test_spec (AbsAction := AbsQT) t η η'' not_nb bη'' eq'').
      eapply lts_refuses_spec2. by eexists. }
    eapply lts_refuses_spec1 in Tr_Test as (t'' & Tr'').
    eapply lts_refuses_spec1 in hnref as (q' & tr').
    exists ν, η'', q', t''. eauto.
Qed.

End Properties_for_soundness_sync.

(** ** Soundness for sets *)

Section SoundnessAS_sync.

Context {P Q T FinA PreAct Aproc Atest : Type}.
Context `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest}.
Context `{gLtsEqT : !gLtsEq T Ht}.
Context (outcome : T → Prop) `{TP : !Testing_Predicate outcome gLtsEqT}.
Context `{SA : !SyncAction Aproc Atest}.
Context `{gLtsP : !gLts P Hp} `{STSP : !ParSts P T _ _} `{!ParStsSpec P T _ _ SA STSP}
        `{CFIP : !coFiniteImagegLts P Atest}.
Context `{gLtsQ : !gLts Q Hp} `{STSQ : !ParSts Q T _ _} `{!ParStsSpec Q T _ _ SA STSQ}
        `{CFIQ : !coFiniteImagegLts Q Atest} `{CN : !gLtsCNenabledSync Q Aproc Atest}.
Context (Φ : Atest → FinA) (𝝳 : FinA → PreAct).
Context `{AbsPT : !@AbsAction P T FinA PreAct Atest Ht Φ 𝝳 Aproc Hp _ _ SA}.
Context `{AbsQT : !@AbsAction Q T FinA PreAct Atest Ht Φ 𝝳 Aproc Hp _ _ SA}.

Notation "X '₁≼' Y" := (bhv_pre_co_cond1__x (A := Atest) X Y) (at level 70).
Notation "X '₂≼' Y" := (bhv_pre_co_cond2__x X Y) (at level 70).
Notation "X '≼' Y" := (bhv_pre_co__x X Y) (at level 70).

(** The composition is an [Sts], so "the composition is stuck" is
    [sts_refuses], not a [τ]-refusal of an LTS. *)

Lemma unoutcome_must_st_nleqx_co (X : gset P) (Y : gset Q) (t : T) :
  ¬ outcome t → mustx X t →
  (∃ q, q ∈ Y ∧ ¬ (∃ y, sts_step (Sts := par_sts) (q, t) y)) →
  ¬ (X ₂≼ Y).
Proof.
  intros not_happy all_must (q & mem' & refuses_tau_q) hbhv2.
  assert (stable_q : q ↛).
  { destruct (lts_refuses_decidable q τ) as [refuses_q | not_refuses_q].
    - exact refuses_q.
    - exfalso. eapply lts_refuses_spec1 in not_refuses_q as (q' & l).
      apply refuses_tau_q. exists (q', t). by apply par_step_left. }
  assert (htX : ∀ p, p ∈ X → p ⇓ᶜᵒ []).
  { destruct (mustx_terminate_unoutcome outcome X t all_must) as [hc | htps];
      [contradiction |].
    intros p mem. apply cocnv_nil. by apply htps. }
  assert (w0 : q ⟹ᶜᵒ q) by constructor.
  destruct (hbhv2 q [] q mem' w0 stable_q htX) as (p & mem & p' & wp & stp' & sub).
  assert (must_p' : mustx ({[ p' ]} : gset P) t).
  { eapply (wt_nil_mx outcome p). eapply (mx_sub outcome X t all_must).
    set_solver. eapply cowt_iff_wt_nil. eassumption. }
  destruct must_p'; [contradiction |].
  edestruct (ex p') as ((p'' , t'') & HypTr). now eapply elem_of_singleton.
  pose proof (par_view_of _ _ _ HypTr) as hv. inversion hv; subst.
  - eapply lts_refuses_spec2 in stp'; eauto.
  - apply refuses_tau_q. exists (q, t''). by apply par_step_right.
  - edestruct (communication_enabled_co Φ 𝝳 p' p'' q t t'' μ η hs l1 l2 sub)
      as (ν1 & ν2 & q' & t3 & hsy' & tr1 & tr2).
    apply refuses_tau_q. exists (q', t3). by eapply par_step_sync.
Qed.

Lemma stability_nbhvleqtwo_co (X : gset P) (Y : gset Q) t :
  ¬ outcome t → mustx X t → X ₂≼ Y →
  ∀ (q : Q), q ∈ Y → ∃ y, sts_step (Sts := par_sts) (q, t) y.
Proof.
  intros nhg hmx hleq q mem.
  destruct (decide (sts_refuses (Sts := par_sts) (q, t))) as [h | h].
  - exfalso.
    eapply (unoutcome_must_st_nleqx_co X Y t nhg hmx); [| exact hleq].
    exists q. split; [exact mem |].
    intros (y & hy).
    eapply (sts_refuses_spec2 (Sts := par_sts) (q, t)); [by exists y | exact h].
  - destruct (sts_refuses_spec1 (Sts := par_sts) (q, t) h) as (y & hy). by exists y.
Qed.

(** ** Soundness, on sets *)

Lemma soundnessx_co (X : gset P) (Y : gset Q) : X ≼ Y → ctx_pre__x X Y.
Proof.
  intros (halt1 & halt2) t hmx. revert Y halt1 halt2.
  dependent induction hmx; intros Y halt1 halt2.
  - intros. by apply mx_now.
  - assert (hmX : mustx X t) by (apply mx_step; assumption).
    assert (HX0 : ∀ p, p ∈ X → p ⇓ᶜᵒ []).
    { intros p mem. eapply cocnv_nil.
      destruct (mustx_terminate_unoutcome outcome X t hmX) as [c | h];
        [contradiction | by eapply h]. }
    assert (HYterm : ∀ q, q ∈ Y → q ⤓).
    { intros q mem. eapply cocnv_terminate. eapply halt1; eauto. }
    assert (Y_conv : Y ⤓).
    { eapply co_termination_set_for_all. exact HYterm. }
    assert (Hbuild : ∀ Y0, Y0 ⤓ → X ₁≼ Y0 → X ₂≼ Y0 → mustx Y0 t).
    { intros Y0 conv0. induction conv0 as [Y0 tY0 IHY0]. intros hb1 hb2.
      eapply mx_step.
      - exact nh.
      - eapply stability_nbhvleqtwo_co; [exact nh | exact hmX | exact hb2].
      - intros Y0' hspec1 hne.
        destruct (cowt_tau_set_from_pset_ispec Y0) as (Y0full_spec1 & Y0full_spec2).
        assert (Hsub0 : Y0' ⊆ cowt_tau_set_from_pset Y0).
        { intros q memq. destruct (hspec1 q memq) as (p & memp & lstep).
          eapply Y0full_spec2; eauto. }
        destruct (decide (cowt_tau_set_from_pset Y0 = ∅)) as [Hemp | Hnemp].
        + exfalso. set_solver.
        + assert (hstep0 : Y0 ⟶ cowt_tau_set_from_pset Y0)
            by (split; [reflexivity | exact Hnemp]).
          specialize (IHY0 _ hstep0).
          destruct (bhvx_preserved_by_reduction_co Φ 𝝳 X Y0 _ Y0full_spec1
                      (conj hb1 hb2)) as (hb1full & hb2full).
          specialize (IHY0 hb1full hb2full).
          eapply mx_sub; [exact IHY0 | exact Hsub0].
      - intros t' l. eapply H0; eauto.
      - intros t' η Y0' ltr lcowtspec hne.
        destruct (decide (outcome t')) as [ot' | not_ot'].
        + by eapply mx_now.
        + assert (HA : ∀ p, p ∈ X → p ⇓ᶜᵒ [η]).
          { intros p mem.
            eapply (unoutcome_acnv_mu outcome X t t' hmX η p mem ltr nh not_ot'). }
          destruct (cowt_s_set_from_pset_ispec X η HA)
            as (Xfull_spec1 & Xfull_spec2).
          assert (htX : ∀ p, p ∈ X → terminate p).
          { destruct (mustx_terminate_unoutcome outcome X t hmX) as [c | h];
              [contradiction | exact h]. }
          edestruct (reverse_trace_inclusion_co Φ 𝝳 X Y0 Y0' η
                       (conj hb1 hb2) HA lcowtspec hne) as (X2 & X2spec1 & X2ne).
          assert (Hsub : X2 ⊆ cowt_s_set_from_pset X η HA).
          { intros q memq. destruct (X2spec1 q memq) as (p & memp & wpq).
            eapply Xfull_spec2; eauto. }
          assert (Xfull_ne : cowt_s_set_from_pset X η HA ≠ ∅) by set_solver.
          destruct (bhvx_preserved_by_external_action_co Φ 𝝳 X
                      (cowt_s_set_from_pset X η HA) η Y0 Y0' htX lcowtspec
                      (conj Xfull_spec1 Xfull_spec2) (conj hb1 hb2)) as (hb1' & hb2').
          eapply (H1 t' η (cowt_s_set_from_pset X η HA) ltr Xfull_spec1 Xfull_ne);
            eauto. }
    eapply Hbuild; eauto.
Qed.

(** ** Soundness, on processes *)

Lemma soundness_co_nb_enabled_co (p : P) (q : Q) :
  p ≼꜀ₒ₋ₐₛ q →
  p ⊆ₘᵤₛₜᵢ q.
Proof.
  intros halt e hm.
  eapply (must_set_iff_must outcome).
  eapply (soundnessx_co ({[p]} : gset P)).
  now eapply alt_set_singleton_iff_co.
  now eapply (must_set_iff_must outcome).
Qed.

End SoundnessAS_sync.


(** ** Soundness on forwarders, one alphabet *)

Lemma soundness_fw_co `{
  gLtsEqP : @gLtsEq P A H, !coFiniteImagegLts P A,
  gLtsEqQ : @gLtsEq Q A H, !coFiniteImagegLts Q A, gLtsObaQ : !gLtsOba Q, !gLtsObaFW Q A,
  gLtsT : !gLtsEq T H, !Testing_Predicate outcome _}

  `{AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳 _ _ _ _ _ }
  `{AbsQT : @AbsAction Q T FinA PreAct A H Φ 𝝳 _ _ _ _ _ }

  `{!Prop_of_Inter P T A A dual}
  `{!Prop_of_Inter Q T A A dual}

  (p : P) (q : Q) : p ≼꜀ₒ₋ₐₛ q -> p ⊑ₘᵤₛₜᵢ q.
Proof.
  (* a forwarder receives every emission of the observer, by [boomerang] *)
  assert (CN : @gLtsCNenabledSync Q A A H H _ SyncAction_of_dual).
  { apply MkgLtsCNenabledSync. intros q1 η nb.
    destruct (boomerang q1 η (co η)) as (q2 & hb).
    destruct (hb nb) as (l & _); [symmetry; exact (proj2_sig (exists_dual η)) |].
    exists (co η), q2. split; [| exact l].
    symmetry; exact (proj2_sig (exists_dual η)). }
  eapply (soundness_co_nb_enabled_co _ _ _ (CN := CN)).
Qed.

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
  `{gLtsP : @gLts P A EA, !FiniteImagegLts P A} {Hinter : @Prop_of_Inter P T A A dual EA gLtsP EA _}
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
Context `{Hinter : @Prop_of_Inter P T A A dual EA gLtsP EA _}.

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

(** ** Soundness for LTSs that can be lifted to forwarders, co variant *)
(* Depends on [soundness_fw_co] (below), which depends on
   [soundness_co_nb_enabled_co]/[soundnessx_co] (set-LTS-based). *)
(*
Lemma soundness_co
  `{@gLtsObaFB P A H gLtsEqP gLtsObaP, !FiniteOutputChain_LtsOba P, !FiniteImagegLts P A}
  `{@gLtsObaFB Q A H gLtsEqQ gLtsObaQ, !FiniteOutputChain_LtsOba Q, !FiniteImagegLts Q A}
  `{@gLtsObaFB T A H gLtsEqT gLtsObaT, !FiniteOutputChain_LtsOba T, !FiniteImagegLts T A}

  `{ !Testing_Predicate outcome _}

  {_ : Prop_of_Inter P T A A dual}
  {_ : Prop_of_Inter Q T A A dual}

  {_ : @Prop_of_Inter P (MO A) A A fw_inter H _ H MbgLts}
  {_ : @Prop_of_Inter (P * MO A) T A A dual H (inter_lts fw_inter) H _}

  {_ : @Prop_of_Inter Q (MO A) A A fw_inter H _ H MbgLts}
  {_ : @Prop_of_Inter (Q * MO A) T A A dual H (inter_lts fw_inter) H _}

  (* [soundness_fw_co], applied below at the forwarder-pair types [P * MO
     A]/[Q * MO A], now needs [coFiniteImagegLts] at that level. Unlike
     [FiniteImagegLts (P * MO A) A] (auto-derived from [FiniteImagegLts P
     A] by [ForwarderConstruction.v]'s [gLtsMBFinite] instance), no such
     forwarder-pair instance exists yet for [coFiniteImagegLts] (same gap
     noted in [EquivalenceASco.v]/[CompletenessASco.v]), so it is assumed
     directly here. *)
  `{!coFiniteImagegLts (P * MO A) A}
  `{!coFiniteImagegLts (Q * MO A) A}

  `{AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳 _ _ _ _ _ }
  `{AbsQT : @AbsAction Q T FinA PreAct A H Φ 𝝳 _ _ _ _ _ }

  (p : P) (q : Q) : p ▷ ∅ ≼꜀ₒ₋ₐₛ q ▷ ∅ -> p ⊑ₘᵤₛₜᵢ q.
Proof.
  intros halt t hm.
  eapply Lift.must_iff_must_fw in hm.
  eapply Lift.must_iff_must_fw.
  now eapply (soundness_fw_co (p ▷ ∅) (q ▷ ∅)).
Qed.
*)
