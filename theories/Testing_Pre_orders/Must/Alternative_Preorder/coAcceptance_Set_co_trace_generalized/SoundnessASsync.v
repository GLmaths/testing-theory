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
(* * Soundness for the co-acceptance-set preorder, for two alphabets

    Uses the co-steps of [coWeakSync.v].  A set of processes
    is tested by one observer, and the set's meta-steps are indexed by /test/
    actions ([coSetLTSConstruction.v]). *)
(* end hide *)

From Stdlib Require ssreflect Setoid.
From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From Stdlib.Program Require Import Wf Equality.
From Stdlib.Wellfounded Require Import Inverse_Image.

From stdpp Require Import base countable finite gmap list finite base decidable finite gmap.

From TestingTheory Require Import SyncActions gLts Bisimulation Lts_OBA Lts_Finite_Non_Blocking_Chain Lts_FW Lts_OBA_FB Lts_CN
      Must Subset_Act InteractionBetweenLts ParallelLTSConstruction
      Termination Convergence WeakTransitions Testing_Predicate MultisetLTSConstruction StateTransitionSystems.
From TestingTheory Require Import ActTau InFiniteSetHelper InListPropHelper.
From TestingTheory Require Import coWeakTransition coConvergence
      FiniteImageLTS coFiniteImage coSetLTSConstruction DefinitionASrel Label_Abstraction.LabelAbstraction.

(* ** Must for a set of processes *)

Inductive mustx `{
    gLtsP : @gLts P Ap Hp, CP : !Countable P,
    gLtsT : ! @gLtsEq T At Ht, !Testing_Predicate outcome _,
    SA : !SyncAction Ap At, STS : !ParSts P T gLtsP gLtsT, !ParStsSpec P T gLtsP gLtsT SA STS}
  (X : gset P) (t : T) : Prop :=
| mx_now (hh : outcome t) : mustx X t
| mx_step
    (nh : ¬ outcome t)
    (ex : ∀ (p : P), p ∈ X → ∃ y, sts_step (Sts := par_sts) (p, t) y)
    (pt : ∀ X',
        lts_tau_set_from_pset_spec1 X X' → X' ≠ ∅ →
        mustx X' t)
    (et : ∀ (t' : T), t ⟶ t' → mustx X t')
    (com : ∀ (t' : T) (η : At) (X' : gset P),
        t ⟶[η] t' →
        cowt_set_from_pset_spec1 X η X' →
        X' ≠ ∅ →
        mustx X' t')
  : mustx X t.

#[global] Hint Constructors mustx:mdb.
Global Notation "X 'must_pass_x' t" := (mustx X t) (at level 70).

Section Must_for_sets_sync.

Context {P T Ap At : Type}.
Context `{Hp : ExtAction Ap} `{Ht : ExtAction At}.
Context `{gLtsP : !gLts P Hp}.
Context `{gLtsT : !gLtsEq T Ht}.
Context (outcome : T → Prop) `{TP : !Testing_Predicate outcome gLtsT}.
Context `{SA : !SyncAction Ap At} `{STS : !ParSts P T gLtsP gLtsT} `{!ParStsSpec P T gLtsP gLtsT SA STS}.
Context `{CFI : !coFiniteImagegLts P At}.

(* ** Must predicate for sets *)

Lemma mx_sub X t :
  X must_pass_x t → ∀ X', X' ⊆ X → X' must_pass_x t.
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
  X must_pass_x t → ∀ p, p ∈ X → ({[ p ]} : gset P) must_pass_x t.
Proof. intros hmx p mem. eapply mx_sub; set_solver. Qed.

Lemma mustx_terminate_unoutcome X t :
  X must_pass_x t → outcome t ∨ ∀ p, p ∈ X → p ⤓.
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
  X must_pass_x t → ¬ outcome t → ∀ p, p ∈ X → p ⤓.
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
  X must_pass_x t →
  ∀ (η : At) p, p ∈ X → t ⟶[η] t' →
  ¬ outcome t → ¬ outcome t' → p ⇓ᶜᵒ [η].
Proof.
  intros hmx η p mem l not_happy not_happy'.
  dependent induction hmx.
  - contradiction.
  - assert (hmX : X must_pass_x t) by (apply mx_step; assumption).
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
  X must_pass_x t →
  ∀ (η : At) p, p ∈ X → t ⟶[η] t' →
  outcome t ∨ outcome t' ∨ p ⇓ᶜᵒ [η].
Proof.
  intros hmx η p mem l.
  destruct (decide (outcome t)); destruct (decide (outcome t')).
  + left; eauto.
  + left; eauto.
  + right; eauto.
  + right. right. eapply unoutcome_acnv_mu; eauto.
Qed.

(* *** The union of two sets that pass an observer passes it *)

Lemma mx_sum X X' t : X must_pass_x t → X' must_pass_x t → (X ∪ X') must_pass_x t.
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
         assert (hmX : X must_pass_x t) by (apply mx_step; assumption).
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
      - assert (hmX : X must_pass_x t) by (apply mx_step; assumption).
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

(* *** From singletons to arbitrary sets, and back to [must] *)

Lemma mx_forall X t :
  X ≠ ∅ → (∀ p, p ∈ X → ({[p]} : gset P) must_pass_x t) → X must_pass_x t.
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
  ∀ p1 p2 t, ({[ p1 ]} : gset P) must_pass_x t → p1 ⟹ p2 →
    ({[ p2 ]} : gset P) must_pass_x t.
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
  X must_pass_x t → wt_set_from_pset_spec1 X [] X' → X' must_pass_x t.
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

Lemma co_wt_mu_mx p1 p2 t t' (η : At) :
  ¬ outcome t → ({[ p1 ]} : gset P) must_pass_x t →
  t ⟶[η] t' → p1 ⟹ᶜᵒ[[η]] p2 → ({[p2]} : gset P) must_pass_x t'.
Proof.
  intros nh hmx l w.
  inversion hmx; subst.
  - contradiction.
  - eapply com; eauto with mdb. exists p1. set_solver.
Qed.

Lemma wt_mu_mx_set X X' t t' (η : At) :
  ¬ outcome t → X must_pass_x t →
  t ⟶[η] t' → cowt_set_from_pset_spec1 X η X' → X' ≠ ∅ →
  X' must_pass_x t'.
Proof.
  intros nh hmx l w hne.
  inversion hmx; subst.
  - contradiction.
  - eapply com; eauto.
Qed.

Lemma must_set_if_must (p : P) (t : T) :
  p must_pass t → ({[ p ]} : gset P) must_pass_x t.
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
  X must_pass_x t → ∀ p, p ∈ X → p must_pass t.
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
  ({[ p ]} : gset P) must_pass_x t → p must_pass t.
Proof. intros. eapply must_if_must_set_helper; set_solver. Qed.

Lemma must_set_iff_must (p : P) (t : T) :
  p must_pass t ↔ ({[ p ]} : gset P) must_pass_x t.
Proof. split; [eapply must_set_if_must | eapply must_if_must_set]. Qed.

Lemma must_set_for_all (X : gset P) (t : T) :
  X ≠ ∅ → (∀ p, p ∈ X → p must_pass t) → X must_pass_x t.
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
  X ≠ ∅ → ((∀ p, p ∈ X → p must_pass t) ↔ X must_pass_x t).
Proof.
  intros.
  split; [now eapply must_set_for_all | now eapply must_if_must_set_helper].
Qed.

End Must_for_sets_sync.

(* ** Contextual preorder for sets *)

(* As [ctx_pre] ([Must.v]): [outcome] and the instances are implicit. *)
Definition ctx_pre__x `{gLtsP : @gLts P Ap Hp, CP : !Countable P,
    gLtsT : !@gLtsEq T At Ht, !Testing_Predicate outcome _,
    SA : !SyncAction Ap At,
    STSP : !ParSts P T gLtsP gLtsT, !ParStsSpec P T gLtsP gLtsT SA STSP}
  (X : gset P) (Y : gset P) :=
  ∀ (t : T), X must_pass_x t → Y must_pass_x t.

Section Must_preorder_for_sets_sync.

Context {P T Ap At : Type}.
Context `{Hp : ExtAction Ap} `{Ht : ExtAction At}.
Context `{gLtsT : !gLtsEq T Ht}.
Context (outcome : T → Prop) `{TP : !Testing_Predicate outcome gLtsT}.
Context `{SA : !SyncAction Ap At}.
Context `{gLtsP : !gLts P Hp} `{STSP : !ParSts P T _ _} `{!ParStsSpec P T _ _ SA STSP}
        `{CFIP : !coFiniteImagegLts P At}.

Notation "X ⊑ₛₑₜ_ₘᵤₛₜᵢ Y" := (ctx_pre__x X Y) (at level 70).

Lemma set_must_union_right (X : gset P) (Y Y' : gset P) :
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

Lemma set_must_union_left_rev (X : gset P) (Y Y' : gset P) :
  X ⊑ₛₑₜ_ₘᵤₛₜᵢ (Y ∪ Y') → X ⊑ₛₑₜ_ₘᵤₛₜᵢ Y.
Proof.
  intros Hyp t h_must.
  induction Y using set_ind_L.
  - eapply set_must_empty; eauto.
  - eapply Hyp in h_must. eapply must_set_for_all. set_solver.
    intros. eapply must_if_must_set_helper in h_must.
    set_solver. set_solver.
Qed.

Lemma set_must_union_right_rev (X : gset P) (Y Y' : gset P) :
  X ⊑ₛₑₜ_ₘᵤₛₜᵢ (Y ∪ Y') → X ⊑ₛₑₜ_ₘᵤₛₜᵢ Y'.
Proof.
  intros Hyp t h_must.
  induction Y' using set_ind_L.
  - eapply set_must_empty; eauto.
  - eapply Hyp in h_must. eapply must_set_for_all. set_solver.
    intros. eapply must_if_must_set_helper in h_must.
    set_solver. set_solver.
Qed.

Lemma set_must_sub (X : gset P) (Y : gset P) :
  X ⊑ₛₑₜ_ₘᵤₛₜᵢ Y → ∀ Y', Y' ⊆ Y → X ⊑ₛₑₜ_ₘᵤₛₜᵢ Y'.
Proof.
  intros Hyp Y' sub t h_must.
  destruct Y' using set_ind_L.
  + eapply set_must_empty; eauto.
  + eapply Hyp in h_must. eapply must_set_for_all. set_solver.
    intros. eapply must_if_must_set_helper in h_must.
    set_solver. set_solver.
Qed.

(* ** The set preorder on singletons is the process preorder *)

Lemma must_set_singleton_iff (p : P) (q : P) :
  p ⊆ₘᵤₛₜᵢ q ↔ ({[ p ]} : gset P) ⊑ₛₑₜ_ₘᵤₛₜᵢ ({[ q ]} : gset P).
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

(* [⊑ₛₑₜ_ₘᵤₛₜᵢ] is a preorder. *)

Section Must_preorder_for_sets_instances.

Context {P T Ap At : Type}.
Context `{Hp : ExtAction Ap} `{Ht : ExtAction At}.
Context `{gLtsT : !gLtsEq T Ht}.
Context (outcome : T → Prop) `{TP : !Testing_Predicate outcome gLtsT}.
Context `{SA : !SyncAction Ap At}.
Context `{gLtsP : !gLts P Hp} `{STSP : !ParSts P T _ _} `{!ParStsSpec P T _ _ SA STSP}
        `{CFIP : !coFiniteImagegLts P At}.

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

(* ** The alternative preorder, on sets

    [mustx_alt_co] and its bridge are commented out in [SoundnessASco.v]
    (they are the one piece that would need the set LTS on the [P] side), so
    there is nothing to port for them. *)

Definition convergence_preorder_on_co_trace_for_set `{gLtsP : @gLts P Ap Hp} `{!Countable P}
  `{Ht : ExtAction At} `{SA : !SyncAction Ap At}
  (X : gset P) (Y : gset P) :=
  ∀ (s : trace At), (∀ p, p ∈ X → p ⇓ᶜᵒ s) → (∀ q, q ∈ Y → q ⇓ᶜᵒ s).

Notation "X ꜀ₙᵥ≼ₛₑₜ₋꜀ₒ₋ₐₛ Y" := (convergence_preorder_on_co_trace_for_set X Y) (at level 70, format "X  ꜀ₙᵥ≼ₛₑₜ₋꜀ₒ₋ₐₛ  Y").

Definition acceptance_set_preorder_on_co_trace_for_set `{gLtsP : @gLts P Ap Hp} `{!Countable P}
  `{Ht : ExtAction At} `{SA : !SyncAction Ap At} {PreAct : Type} (Γ : At → PreAct)
  (X : gset P) (Y : gset P) :=
  ∀ q s q', q ∈ Y →
    q ⟹ᶜᵒ[s] q' → q' ↛ →
    (∀ p, p ∈ X → p ⇓ᶜᵒ s) →
    ∃ p, p ∈ X ∧ ∃ p', p ⟹ᶜᵒ[s] p' ∧ p' ↛ ∧
           (⌈ Γ ⌉ (coR p') ⊆ ⌈ Γ ⌉ (coR q')).

Notation "X ₐ꜀꜀≼ₛₑₜ₋꜀ₒ₋ₐₛ[ Γ ] Y" := (acceptance_set_preorder_on_co_trace_for_set Γ X Y) (at level 70, format "X  ₐ꜀꜀≼ₛₑₜ₋꜀ₒ₋ₐₛ[ Γ ]  Y").

Definition cnv_acceptance_set_preorder_on_co_trace_for_set `{gLtsP : @gLts P Ap Hp} `{!Countable P}
  `{Ht : ExtAction At} `{SA : !SyncAction Ap At} {PreAct : Type} (Γ : At → PreAct)
  (X : gset P) (Y : gset P) :=
  X ꜀ₙᵥ≼ₛₑₜ₋꜀ₒ₋ₐₛ Y ∧ X ₐ꜀꜀≼ₛₑₜ₋꜀ₒ₋ₐₛ[ Γ ] Y.

Notation "X ≼ₛₑₜ₋꜀ₒ₋ₐₛ[ Γ ] Y" := (cnv_acceptance_set_preorder_on_co_trace_for_set Γ X Y) (at level 70, format "X  ≼ₛₑₜ₋꜀ₒ₋ₐₛ[ Γ ]  Y").

(* ** Acceptance-set preorder properties on sets *)

Section Acceptance_Set_preorder_for_sets_sync.

Context {P PreAct Ap At : Type}.
Context `{Hp : ExtAction Ap} `{Ht : ExtAction At}.
Context `{gLtsP : !gLts P Hp} `{CP : !Countable P}.
Context `{SA : !SyncAction Ap At}.
Context (Γ : At → PreAct).


Lemma alt_set_singleton_iff_co (p : P) (q : P) :
  ({[ p ]} : gset P) ≼ₛₑₜ₋꜀ₒ₋ₐₛ[ Γ ] ({[ q ]} : gset P) ↔
  p ≼꜀ₒ₋ₐₛ[ Γ ] q.
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

Lemma bhvleqone_preserved_by_reduction_co (X : gset P) (Y Y' : gset P) :
  X ꜀ₙᵥ≼ₛₑₜ₋꜀ₒ₋ₐₛ Y → lts_tau_set_from_pset_spec1 Y Y' → X ꜀ₙᵥ≼ₛₑₜ₋꜀ₒ₋ₐₛ Y'.
Proof.
  intros halt1 l s mem.
  intros q memq. eapply l in memq as (q' & mem' & tr').
  eapply cocnv_preserved_by_lts_tau; eauto.
Qed.

Lemma bhvx_preserved_by_reductions_co (X : gset P) (Y Y' : gset P) :
  wt_set_from_pset_spec1 Y [] Y' → X ≼ₛₑₜ₋꜀ₒ₋ₐₛ[ Γ ] Y → X ≼ₛₑₜ₋꜀ₒ₋ₐₛ[ Γ ] Y'.
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

Lemma bhvx_preserved_by_reduction_co (X : gset P) (Y Y' : gset P) :
  lts_tau_set_from_pset_spec1 Y Y' → X ≼ₛₑₜ₋꜀ₒ₋ₐₛ[ Γ ] Y → X ≼ₛₑₜ₋꜀ₒ₋ₐₛ[ Γ ] Y'.
Proof.
  intros l (halt1 & halt2).
  eapply bhvx_preserved_by_reductions_co; [| split; eauto].
  intros q' mem'. eapply l in mem' as (q'' & mem'' & wt_tr'').
  exists q''. split; eauto. eapply lts_to_wt_tau; eauto.
Qed.

Lemma bhvleqone_preserved_by_external_action_co
  (X X' : gset P) (η : At) (Y Y' : gset P)
  (htp : ∀ p, p ∈ X → p ⤓) :
  X ꜀ₙᵥ≼ₛₑₜ₋꜀ₒ₋ₐₛ Y → cowt_set_from_pset_spec X η X' →
  cowt_set_from_pset_spec1 Y η Y' → X' ꜀ₙᵥ≼ₛₑₜ₋꜀ₒ₋ₐₛ Y'.
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
  (X X' : gset P) (η : At) (Y Y' : gset P)
  (htp : ∀ p, p ∈ X → p ⤓) :
  cowt_set_from_pset_spec1 Y η Y' →
  cowt_set_from_pset_spec X η X' →
  X ≼ₛₑₜ₋꜀ₒ₋ₐₛ[ Γ ] Y → X' ≼ₛₑₜ₋꜀ₒ₋ₐₛ[ Γ ] Y'.
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

Lemma reverse_trace_inclusion_co (X : gset P) (Y Y' : gset P) (η : At) :
  X ≼ₛₑₜ₋꜀ₒ₋ₐₛ[ Γ ] Y → (∀ p, p ∈ X → p ⇓ᶜᵒ [η]) →
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

(* ** Communication-enabling property *)

(* ** Communication-enabled processes

    What the soundness proof asks of [P]: every emission of the observer can
    be received, by /some/ action that synchronises with it.  On one
    alphabet a forwarder has it by [boomerang] ([soundness_fw_co] below); on
    [Ap ⊎ At] by [fw_boomerang] (below). *)

Section Properties_for_soundness_sync.

Context {P T Ap At : Type}.
Context `{Hp : ExtAction Ap} `{Ht : ExtAction At}.
Context `{gLtsT : !gLtsEq T Ht}.
Context `{SA : !SyncAction Ap At}.
Context `{gLtsP : !gLts P Hp}.
Context `{!gLtsCNenabled P Ap At}.
Context (𝔸 : Label_abstraction P T).

(* In the non-blocking case, [q] receives the observer's emission [η] by
    [cn_enabled] — with its own action, not necessarily [p]'s. *)

Lemma communication_enabled_co (p : P) p' (q : P) (t : T) t' μ1 (η : At) :
  sync μ1 η → p ⟶[μ1] p' → t ⟶[η] t' →
  ⌈ ρ[𝔸] ⌉ (coR p) ⊆ ⌈ ρ[𝔸] ⌉ (coR q) →
  ∃ μ3 μ4 q' t'', sync μ3 μ4 ∧ q ⟶[μ3] q' ∧ t ⟶[μ4] t''.
Proof.
  intros hsy tr tr_co sub.
  destruct (decide (non_blocking η)) as [nb | not_nb].
  + destruct (cn_enabled q η nb) as (β & q' & hsyq & tr').
    exists β, η, q', t'. eauto.
  + assert (hco : η ∈ coR p).
    { eapply coR_intro; [| exact hsy | exact not_nb].
      eapply lts_performs_spec2. by eexists. }
    eapply (map_gamma_of_action ρ[𝔸]) in hco as mem.
    eapply sub in mem. destruct mem as (η' & memq & eq).
    assert (acc : t ⟶[η]) by (eapply lts_performs_spec2; by eexists).
    apply (LA_class_proj (label_ker 𝔸)) in eq.
    apply rel_ker_sub in eq as (u & hu & hu''); [| intros μ; exists μ; split; reflexivity].
    pose proof (coR_reverse_inclusion u η' hu'' q memq) as (μ2 & hnref & hsyν & bη'').
    pose proof (Ready_set_inclusion η u hu t acc) as Tr_Test.
    rename u into η''.
    eapply lts_performs_spec1 in Tr_Test as (t'' & Tr'').
    eapply lts_performs_spec1 in hnref as (q' & tr').
    exists μ2, η'', q', t''. eauto.
Qed.

End Properties_for_soundness_sync.

(* ** Soundness for sets *)

Section SoundnessAS_sync.

Context {P T Ap At : Type}.
Context `{Hp : ExtAction Ap} `{Ht : ExtAction At}.
Context `{gLtsEqT : !gLtsEq T Ht}.
Context (outcome : T → Prop) `{TP : !Testing_Predicate outcome gLtsEqT}.
Context `{SA : !SyncAction Ap At}.
Context `{gLtsP : !gLts P Hp} `{STSP : !ParSts P T _ _} `{!ParStsSpec P T _ _ SA STSP}
        `{CFIP : !coFiniteImagegLts P At}.
Context `{CN : !gLtsCNenabled P Ap At}.
Context (𝔸 : Label_abstraction P T).

Lemma unoutcome_must_st_nleqx_co (X : gset P) (Y : gset P) (t : T) :
  ¬ outcome t → X must_pass_x t →
  (∃ q, q ∈ Y ∧ ¬ (∃ y, sts_step (Sts := par_sts) (q, t) y)) →
  ¬ (X ₐ꜀꜀≼ₛₑₜ₋꜀ₒ₋ₐₛ[ ρ[𝔸] ] Y).
Proof.
  intros not_happy all_must (q & mem' & refuses_tau_q) hbhv2.
  assert (stable_q : q ↛).
  { destruct (decide (q ⟶)) as [not_refuses_q | refuses_q].
    - exfalso. eapply lts_performs_spec1 in not_refuses_q as (q' & l).
      apply refuses_tau_q. exists (q', t). by apply par_step_left.
    - exact refuses_q. }
  assert (htX : ∀ p, p ∈ X → p ⇓ᶜᵒ []).
  { destruct (mustx_terminate_unoutcome outcome X t all_must) as [hc | htps];
      [contradiction |].
    intros p mem. apply cocnv_nil. by apply htps. }
  assert (w0 : q ⟹ᶜᵒ q) by constructor.
  destruct (hbhv2 q [] q mem' w0 stable_q htX) as (p & mem & p' & wp & stp' & sub).
  assert (must_p' : ({[ p' ]} : gset P) must_pass_x t).
  { eapply (wt_nil_mx outcome p). eapply (mx_sub outcome X t all_must).
    set_solver. eapply cowt_iff_wt_nil. eassumption. }
  destruct must_p'; [contradiction |].
  edestruct (ex p') as ((p'' , t'') & HypTr). now eapply elem_of_singleton.
  pose proof (par_view_of _ _ _ HypTr) as hv. inversion hv; subst.
  - exfalso; apply stp', lts_performs_spec2; eauto.
  - apply refuses_tau_q. exists (q, t''). by apply par_step_right.
  - edestruct (communication_enabled_co 𝔸 p' p'' q t t'' μ η hs l1 l2 sub)
      as (μ1 & μ2 & q' & t3 & hsy' & tr1 & tr2).
    apply refuses_tau_q. exists (q', t3). by eapply par_step_sync.
Qed.

Lemma stability_nbhvleqtwo_co (X : gset P) (Y : gset P) t :
  ¬ outcome t → X must_pass_x t → X ₐ꜀꜀≼ₛₑₜ₋꜀ₒ₋ₐₛ[ ρ[𝔸] ] Y →
  ∀ (q : P), q ∈ Y → ∃ y, sts_step (Sts := par_sts) (q, t) y.
Proof.
  intros nhg hmx hleq q mem.
  destruct (decide (sts_performs (Sts := par_sts) (q, t))) as [h | h].
  - destruct (sts_performs_spec1 (Sts := par_sts) (q, t) h) as (y & hy). by exists y.
  - exfalso.
    eapply (unoutcome_must_st_nleqx_co X Y t nhg hmx); [| exact hleq].
    exists q. split; [exact mem |].
    intros (y & hy).
    apply h, (sts_performs_spec2 (Sts := par_sts) (q, t)). by exists y.
Qed.

(* ** Soundness, on sets *)

Lemma soundnessx_co (X : gset P) (Y : gset P) : X ≼ₛₑₜ₋꜀ₒ₋ₐₛ[ ρ[𝔸] ] Y → X ⊑ₛₑₜ_ₘᵤₛₜᵢ Y.
Proof.
  intros (halt1 & halt2) t hmx. revert Y halt1 halt2.
  dependent induction hmx; intros Y halt1 halt2.
  - intros. by apply mx_now.
  - assert (hmX : X must_pass_x t) by (apply mx_step; assumption).
    assert (HX0 : ∀ p, p ∈ X → p ⇓ᶜᵒ []).
    { intros p mem. eapply cocnv_nil.
      destruct (mustx_terminate_unoutcome outcome X t hmX) as [c | h];
        [contradiction | by eapply h]. }
    assert (HYterm : ∀ q, q ∈ Y → q ⤓).
    { intros q mem. eapply cocnv_terminate. eapply halt1; eauto. }
    assert (Y_conv : Y ⤓).
    { eapply co_termination_set_for_all. exact HYterm. }
    assert (Hbuild : ∀ Y0, Y0 ⤓ → X ꜀ₙᵥ≼ₛₑₜ₋꜀ₒ₋ₐₛ Y0 → X ₐ꜀꜀≼ₛₑₜ₋꜀ₒ₋ₐₛ[ ρ[𝔸] ] Y0 → Y0 must_pass_x t).
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
          destruct (bhvx_preserved_by_reduction_co ρ[𝔸] X Y0 _ Y0full_spec1
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
          assert (htX : ∀ p, p ∈ X → p ⤓).
          { destruct (mustx_terminate_unoutcome outcome X t hmX) as [c | h];
              [contradiction | exact h]. }
          edestruct (reverse_trace_inclusion_co ρ[𝔸] X Y0 Y0' η
                       (conj hb1 hb2) HA lcowtspec hne) as (X2 & X2spec1 & X2ne).
          assert (Hsub : X2 ⊆ cowt_s_set_from_pset X η HA).
          { intros q memq. destruct (X2spec1 q memq) as (p & memp & wpq).
            eapply Xfull_spec2; eauto. }
          assert (Xfull_ne : cowt_s_set_from_pset X η HA ≠ ∅) by set_solver.
          destruct (bhvx_preserved_by_external_action_co ρ[𝔸] X
                      (cowt_s_set_from_pset X η HA) η Y0 Y0' htX lcowtspec
                      (conj Xfull_spec1 Xfull_spec2) (conj hb1 hb2)) as (hb1' & hb2').
          eapply (H1 t' η (cowt_s_set_from_pset X η HA) ltr Xfull_spec1 Xfull_ne);
            eauto. }
    eapply Hbuild; eauto.
Qed.

(* ** Soundness, on processes *)

Lemma soundness_co_nb_enabled_co (p : P) (q : P) :
  p ≼꜀ₒ₋ₐₛ[ ρ[𝔸] ] q →
  p ⊆ₘᵤₛₜᵢ q.
Proof.
  intros halt e hm.
  eapply (must_set_iff_must outcome).
  eapply (soundnessx_co ({[p]} : gset P)).
  now eapply alt_set_singleton_iff_co.
  now eapply (must_set_iff_must outcome).
Qed.

End SoundnessAS_sync.

From Stdlib Require ssreflect Setoid.
From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From Stdlib.Program Require Import Wf Equality.
From Stdlib.Wellfounded Require Import Inverse_Image.

From stdpp Require Import base countable finite gmap list decidable.

From TestingTheory Require Import ActTau InFiniteSetHelper InListPropHelper.
From TestingTheory Require Import gLts SyncActions MemAction InteractionUnion MemForwarder Bisimulation Lts_OBA
  Lts_Finite_Non_Blocking_Chain Lts_FW Lts_OBA_FB Lts_CN
  Subset_Act Termination Convergence WeakTransitions Testing_Predicate
  StateTransitionSystems InteractionBetweenLts
  Must.
From TestingTheory Require Import coWeakSync FiniteImageLTS coFiniteImage coSetLTSConstruction DefinitionASrel coWeakTransition coConvergence Label_Abstraction.LabelAbstraction.

#[local] Hint Mode ExtAction ! : typeclass_instances.


(* ** Soundness on forwarders, for two alphabets *)

Section SoundnessFW_sync.

Context {P T Ap At : Type}.
Context `{Hp : ExtAction Ap} `{Ht : ExtAction At} `{SA : !SyncAction Ap At}.
Context (outcome : T → Prop).
Context `{gLtsEqT : !gLtsEq T Ht} `{TP : !Testing_Predicate outcome gLtsEqT}.
Context `{gLtsEqP : !gLtsEq P (@ExtAction_sum Ap (MemAct At) Hp (@ExtAction_mem At Ht))} `{FWP : !gLtsFWMem P Ap At}
        `{SYP : !Prop_of_Inter P T (Ap + MemAct At) At sync}
        `{CFIP : !coFiniteImagegLts P At}.
Context (𝔸 : Label_abstraction (Hp := ExtAction_sum) (SA := SyncAction_mem) P T).

#[local] Instance CN_of_FW : gLtsCNenabled P (Ap + MemAct At) At.
Proof.
  apply MkgLtsCNenabled. intros q1 η nb.
  destruct (fw_boomerang_total q1 η nb) as (β & q2 & hsy & l & _).
  by exists β, q2.
Qed.

Lemma soundness_fw_co_sync (p : P) (q : P) :
  p ≼꜀ₒ₋ₐₛ[ ρ[𝔸] ] q →
  p ⊆ₘᵤₛₜᵢ q.
Proof. by eapply (soundness_co_nb_enabled_co outcome 𝔸). Qed.

End SoundnessFW_sync.
