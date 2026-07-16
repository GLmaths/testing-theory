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

From stdpp Require Import base countable finite gmap list gmultiset.

From TestingTheory Require Import ActTau gLts Bisimulation FiniteImageLTS coFiniteImage
    InListPropHelper WeakTransitions coWeakTransition Termination Convergence coConvergence.

(** ** [coToSET] — the "LTS of sets" of [SetLTSConstruction.v]'s [toSET],
    but sourced from [coFiniteImagegLts]/[cowt] instead of
    [FiniteImagegLts]/[wt]. Scoped down to exactly what
    [SoundnessASco.v]'s [soundnessx_co] needs: a [gLts (gset P) A]
    instance whose tau-step is [cowt_tau_set_from_pset] (coincides with
    [toSET]'s own tau-step on the nil case, [cowt_iff_wt_nil]), so that
    [terminate]/[⤓] becomes meaningful on [gset P] *natively* off
    [coFiniteImagegLts] — no [FiniteImagegLts P A] instance needed
    anywhere in this file. *)

(** *** Extaction-successors of a whole *set*, co version

    Mirrors [lts_extaction_set_from_pset]/[_ispec] (FiniteImageLTS.v) in
    shape, sourced from [cowt_extaction_set] (coFiniteImage.v) instead of
    [lts_extaction_set]. Unlike the plain version, this computes the
    *dual*-image at [μ] (states reachable via some action dual to [μ], not
    literal [μ]), matching [cowt_extaction_set]'s own shape — hence a new
    spec, not a reuse of [lts_extaction_set_from_pset_spec]. *)

Definition cowt_extaction_set_from_pset `{coFiniteImagegLts P A} (ps : gset P) μ : gset P :=
  ⋃ (map (fun p => list_to_set (cowt_extaction_set p μ)) (elements ps)).

Definition cowt_extaction_set_from_pset_spec1 `{Countable P} `{gLts P A}
  (ps : gset P) μ (qs : gset P) :=
  forall q, q ∈ qs -> exists p, p ∈ ps /\ exists μ', dual μ' μ /\ p ⟶[μ'] q.

Definition cowt_extaction_set_from_pset_spec2 `{Countable P} `{gLts P A}
  (ps : gset P) μ (qs : gset P) :=
  forall p q, p ∈ ps -> (exists μ', dual μ' μ /\ p ⟶[μ'] q) -> q ∈ qs.

Definition cowt_extaction_set_from_pset_spec `{Countable P} `{gLts P A}
  (ps : gset P) μ (qs : gset P) :=
  cowt_extaction_set_from_pset_spec1 ps μ qs /\ cowt_extaction_set_from_pset_spec2 ps μ qs.

Lemma cowt_extaction_set_from_pset_ispec `{coFiniteImagegLts P A}
  (ps : gset P) μ :
  cowt_extaction_set_from_pset_spec ps μ (cowt_extaction_set_from_pset ps μ).
Proof.
  split.
  - intros a mem.
    eapply elem_of_union_list in mem as (xs & mem1 & mem2).
    eapply list_elem_of_fmap in mem1 as (p & heq0 & mem1).
    subst. eapply elem_of_list_to_set in mem2.
    eapply cowt_extaction_set_spec in mem2.
    exists p. split; eauto. eapply elem_of_elements. eauto.
  - intros p q mem l.
    eapply elem_of_union_list.
    exists (list_to_set (cowt_extaction_set p μ)).
    split.
    + eapply list_elem_of_fmap. exists p. split; eauto. eapply elem_of_elements. eauto.
    + eapply elem_of_list_to_set. eapply cowt_extaction_set_spec. eauto.
Qed.

(** *** [coToSET] itself *)

#[global] Program Instance coToSET `(gLtsP : !@gLts P A H) `{coFP : !@coFiniteImagegLts P A H gLtsP} :
  gLts (gset P) H.
Next Obligation.
  intros. destruct X.
  + exact (H1 = cowt_extaction_set_from_pset H0 μ /\ H1 ≠ ∅).
  + exact (H1 = cowt_tau_set_from_pset H0 /\ H1 ≠ ∅).
Defined.
Next Obligation.
  intros; simpl in *. unfold coToSET_obligation_1.
  destruct α.
  - destruct (decide (b = cowt_extaction_set_from_pset a μ /\ b ≠ ∅)).
    + left. eauto.
    + right. eauto.
  - destruct (decide (b = cowt_tau_set_from_pset a /\ b ≠ ∅)).
    + left. eauto.
    + right. eauto.
Qed.
Next Obligation.
  intros. destruct X.
  + exact (forall p, p ∈ H0 -> forall μ', dual μ' μ -> lts_refuses p (ActExt μ')).
  + exact (forall p, p ∈ H0 -> lts_refuses p τ).
Defined.
Next Obligation.
  intros. simpl in *. unfold coToSET_obligation_3.
  destruct α as [μ|].
  - destruct (cowt_extaction_set_from_pset_ispec p μ) as (Espec1 & Espec2).
    destruct (decide (cowt_extaction_set_from_pset p μ = ∅)) as [Hemp | Hnemp].
    + left. intros p' mem μ' duo.
      destruct (lts_refuses_decidable p' (ActExt μ')); eauto.
      exfalso. eapply lts_refuses_spec1 in n as (q & tr).
      assert (q ∈ cowt_extaction_set_from_pset p μ) by (eapply Espec2; eauto).
      set_solver.
    + right. intro Hall.
      apply Hnemp. apply leibniz_equiv. intros q. split; [|set_solver].
      intros mem. eapply Espec1 in mem as (p' & memp & μ' & duo & tr).
      pose proof (Hall p' memp μ' duo) as memp'.
      exfalso. eapply (lts_refuses_spec2 p' (ActExt μ') (exist _ q tr)). eauto.
  - destruct (cowt_tau_set_from_pset_ispec p) as (Tspec1 & Tspec2).
    destruct (decide (cowt_tau_set_from_pset p = ∅)) as [Hemp | Hnemp].
    + left. intros p' mem.
      destruct (lts_refuses_decidable p' τ); eauto.
      exfalso. eapply lts_refuses_spec1 in n as (q & tr).
      assert (q ∈ cowt_tau_set_from_pset p) by (eapply Tspec2; eauto).
      set_solver.
    + right. intro Hall.
      apply Hnemp. apply leibniz_equiv. intros q. split; [|set_solver].
      intros mem. eapply Tspec1 in mem as (p' & memp & tr).
      eapply Hall in memp.
      exfalso. eapply (lts_refuses_spec2 p' τ (exist _ q tr)). eauto.
Qed.
Next Obligation.
  intros. simpl in *. unfold coToSET_obligation_3 in H0. unfold coToSET_obligation_1.
  destruct α as [μ|].
  - exists (cowt_extaction_set_from_pset p μ). split; eauto.
    intro Hemp.
    apply H0. intros p' mem μ' duo.
    destruct (lts_refuses_decidable p' (ActExt μ')); eauto.
    exfalso. eapply lts_refuses_spec1 in n as (q & tr).
    assert (q ∈ cowt_extaction_set_from_pset p μ) as Hin.
    { destruct (cowt_extaction_set_from_pset_ispec p μ) as (_ & Hspec2).
      eapply Hspec2; eauto. }
    set_solver.
  - exists (cowt_tau_set_from_pset p). split; eauto.
    intro Hemp.
    apply H0. intros p' mem.
    destruct (lts_refuses_decidable p' τ); eauto.
    exfalso. eapply lts_refuses_spec1 in n as (q & tr).
    assert (q ∈ cowt_tau_set_from_pset p) as Hin.
    { destruct (cowt_tau_set_from_pset_ispec p) as (_ & Hspec2).
      eapply Hspec2; eauto. }
    set_solver.
Qed.
Next Obligation.
  unfold coToSET_obligation_3, coToSET_obligation_1.
  intros. destruct α as [μ|].
  - destruct H0 as (X' & Heq & Hne). subst.
    intro Hall.
    apply Hne. apply leibniz_equiv. intros q. split; [|set_solver].
    intros mem. eapply cowt_extaction_set_from_pset_ispec in mem as (p' & memp & μ' & duo & tr).
    pose proof (Hall p' memp μ' duo) as memp'.
    exfalso. eapply (lts_refuses_spec2 p' (ActExt μ') (exist _ q tr)). eauto.
  - destruct H0 as (X' & Heq & Hne). subst.
    intro Hall.
    apply Hne. apply leibniz_equiv. intros q. split; [|set_solver].
    intros mem. eapply cowt_tau_set_from_pset_ispec in mem as (p' & memp & tr).
    eapply Hall in memp.
    exfalso. eapply (lts_refuses_spec2 p' τ (exist _ q tr)). eauto.
Qed.

(** ** Co-termination — mirrors [SetLTSConstruction.v]'s [empty_set_termination]
    through [termination_set_for_all] verbatim, sourced from [coToSET]/
    [cowt_tau_set_from_pset] instead of [toSET]/[lts_tau_set_from_pset].
    This is the piece [SoundnessASco.v]'s [soundnessx_co] actually needs:
    well-founding the [pt]-field recursion on the [Y]-side, natively off
    [coFiniteImagegLts Q A] — no [FiniteImagegLts Q A] anywhere. *)

Lemma co_empty_set_termination `{gLtsP : @gLts P A H} `{!coFiniteImagegLts P A} :
  (∅ : gset P) ⤓.
Proof.
  constructor. intros X tr.
  destruct tr as (eq & not_empty).
  subst. unfold cowt_tau_set_from_pset in not_empty.
  rewrite elements_empty in not_empty. simpl in *.
  exfalso. set_solver.
Qed.

Lemma co_termination_sum `{gLtsP : @gLts P A H} `{!coFiniteImagegLts P A}
  (X : gset P) (Y : gset P) :
  X ⤓ -> Y ⤓ -> (X ∪ Y) ⤓.
Proof.
  intros conv1 conv2. revert Y conv2.
  dependent induction conv1.
  intros ps2 hmx2.
  constructor. intros.
  assert (q ⊆ cowt_tau_set_from_pset p ∪ cowt_tau_set_from_pset ps2).
  { intros q' mem. destruct H2 as (eq1 & eq2). subst.
    destruct (cowt_tau_set_from_pset_ispec (p ∪ ps2)) as (Hyp1 & Hyp2).
    eapply Hyp1 in mem as (q0 & mem & l).
    eapply elem_of_union in mem. destruct mem.
    eapply elem_of_union. left. eapply cowt_tau_set_from_pset_ispec; eassumption.
    eapply elem_of_union. right. eapply cowt_tau_set_from_pset_ispec; eassumption. }
  assert (cowt_tau_set_from_pset p ∪ cowt_tau_set_from_pset ps2 ⊆ q) as PrimHyp.
  { intro. intro. eapply elem_of_union in H4.
    destruct H4.
    ++ destruct H2 as (eq & not_empty). subst.
       destruct (cowt_tau_set_from_pset_ispec (p)) as (Hyp1 & Hyp2).
       eapply Hyp1 in H4 as (p'' & mem & tr).
       assert (p'' ∈ p ∪ ps2) by set_solver.
       eapply cowt_tau_set_from_pset_ispec. exact H2.
       eauto.
    ++ destruct H2 as (eq & not_empty). subst.
       destruct (cowt_tau_set_from_pset_ispec ps2) as (Hyp1 & Hyp2).
       eapply Hyp1 in H4 as (p'' & mem & tr).
       assert (p'' ∈ p ∪ ps2) by set_solver.
       eapply cowt_tau_set_from_pset_ispec. exact H2.
       eauto. }
  assert (q = cowt_tau_set_from_pset p ∪ cowt_tau_set_from_pset ps2) as HypPrim2.
  { set_solver. }
  assert (cowt_tau_set_from_pset p ⊆ cowt_tau_set_from_pset p) as Y_spec'.
  { set_solver. }
  assert (cowt_tau_set_from_pset ps2 ⊆ cowt_tau_set_from_pset ps2) as Z_spec'.
  { set_solver. }
  assert (cowt_tau_set_from_pset p ∪ cowt_tau_set_from_pset ps2 ≡ q) as eq.
  { set_solver. } clear HypPrim2.
  remember (cowt_tau_set_from_pset p) as Y_'.
  remember (cowt_tau_set_from_pset ps2) as Z_'.
  destruct Y_' using set_ind_L.
    + destruct Z_' using set_ind_L.
      ++ exfalso. destruct H2.
         set_solver.
      ++ assert (cowt_tau_set_from_pset p = ∅) by set_solver.
         assert (cowt_tau_set_from_pset ps2 = q) by set_solver. subst.
         inversion hmx2; subst.
         destruct H2; subst. eapply H6. split.
         +++ eapply leibniz_equiv. split.
             ++++ eauto.
             ++++ eauto.
         +++ set_solver.
    + destruct Z_' using set_ind_L.
      ++ assert (cowt_tau_set_from_pset p = q) by set_solver.
         assert (p ⤓) by eauto with mdb.
         inversion H5; subst. eapply H6. split.
         +++ destruct H2. subst. intros. destruct (cowt_tau_set_from_pset_ispec p) as (Hyp1 & Hyp2).
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

Lemma co_termination_forall `{gLtsP : @gLts P A H} `{!coFiniteImagegLts P A} (ps : gset P) :
  (forall (p : P), p ∈ ps -> ({[p]} : gset P) ⤓)
    -> ps ⤓.
Proof.
  intro hm.
  induction ps using set_ind_L.
  - intros. eapply co_empty_set_termination.
  - destruct (set_choose_or_empty X).
    + eapply co_termination_sum; set_solver.
    + assert (X = ∅) by set_solver.
      rewrite H2, union_empty_r_L. set_solver.
Qed.

Lemma co_termination_set_if_termination `{gLtsP : @gLts P A H} `{!coFiniteImagegLts P A}
  (p : P) : p ⤓ -> ({[ p ]} : gset P) ⤓.
Proof.
  intro hm. dependent induction hm.
  constructor. intros.
  eapply co_termination_forall. intros.
  destruct H2 as (eq & eq'). subst. unfold cowt_tau_set_from_pset in H3.
  rewrite elements_singleton in H3. simpl in *.
  eapply elem_of_union in H3 as [H3 | H3].
  - eapply elem_of_list_to_set in H3. eapply cowt_tau_set_spec in H3.
    eapply H1. eauto.
  - set_solver.
Qed.

Lemma co_termination_if_termination_set_helper `{gLtsP : @gLts P A H} `{!coFiniteImagegLts P A}
  (ps : gset P) :
  ps ⤓
    -> forall p, p ∈ ps
      -> p ⤓.
Proof.
  intro hm. dependent induction hm.
  intros p' mem. constructor.
  intros p'' tr.
  eapply H1.
  + split. reflexivity. eapply cowt_tau_set_from_pset_ispec in tr; set_solver.
  + eapply cowt_tau_set_from_pset_ispec; set_solver.
Qed.

Lemma co_termination_if_termination_set `{gLtsP : @gLts P A H} `{!coFiniteImagegLts P A}
  (p : P) :
  ({[ p ]} : gset P) ⤓
    -> p ⤓.
Proof. intros. eapply co_termination_if_termination_set_helper; set_solver. Qed.

Lemma co_termination_set_iff_termination `{gLtsP : @gLts P A H} `{!coFiniteImagegLts P A}
  (p : P) :
  p ⤓ <-> ({[ p ]} : gset P) ⤓.
Proof. split; [eapply co_termination_set_if_termination | eapply co_termination_if_termination_set]. Qed.

Lemma co_termination_set_for_all `{gLtsP : @gLts P A H} `{!coFiniteImagegLts P A} (X : gset P) :
  (forall p, p ∈ X -> p ⤓)
      -> X ⤓.
Proof.
  intros hm. eapply co_termination_forall.
  intros. eapply hm in H0. eapply co_termination_set_iff_termination in H0. eauto.
Qed.

Lemma co_termination_set_iff_termination_forall `{gLtsP : @gLts P A H} `{!coFiniteImagegLts P A} (X : gset P) :
  (forall p, p ∈ X -> p ⤓) <-> X ⤓.
Proof.
  split. now eapply co_termination_set_for_all.
  now eapply co_termination_if_termination_set_helper.
Qed.

(** ** Co-convergence/co-trace on [coToSET]

    Mirrors [SetLTSConstruction.v]'s [empty_set_stable] through
    [convergence_set_iff_convergence_forall], sourced from [coToSET]
    instead of [toSET]. [⟹[s]]/[⇓s] below are the *plain*, generic
    [WeakTransitions.v]/[Convergence.v] relations instantiated at
    [coToSET] — the "co" is entirely carried by [coToSET]'s own step
    relation (a dual-image jump), not by a second co-layer on top. The
    individual-level ([P], not [gset P]) side of the bridge lemmas
    correspondingly uses [coWeakTransition.v]/[coConvergence.v]'s
    [⟹ᶜᵒ[s]]/[⇓ᶜᵒs] (built from [cowt_tau]/[cowt_act], matching exactly
    the plain-or-dual-labelled individual step each [coToSET] meta-step
    resolves to via [cowt_tau_set_from_pset_ispec]/
    [cowt_extaction_set_from_pset_ispec]) — *not* the plain individual
    [⟹[s]]/[⇓s] [SetLTSConstruction.v] uses, since a [coToSET] meta-step at
    label [μ] is witnessed by an individual step at some [μ'] dual to [μ],
    not at [μ] itself. *)

Lemma co_empty_set_stable `{gLtsP : @gLts P A H} `{!coFiniteImagegLts P A} α :
  (∅ : gset P) ↛{ α }.
Proof. destruct α; intros p mem; exfalso; set_solver. Qed.

Lemma co_empty_set_stable_wk_not_emp_list `{gLtsP : @gLts P A H} `{!coFiniteImagegLts P A}
  a s (ps : gset P) : ¬ (∅ : gset P) ⟹[a :: s] ps.
Proof.
  intro imp.
  inversion imp; subst.
  + eapply (@lts_refuses_spec2 (gset P)); eauto. eapply co_empty_set_stable.
  + eapply (@lts_refuses_spec2 (gset P)); eauto. eapply co_empty_set_stable.
Qed.

Lemma co_empty_set_conv `{gLtsP : @gLts P A H} `{!coFiniteImagegLts P A} s : (∅ : gset P) ⇓ s.
Proof.
  induction s.
  + constructor. eapply co_empty_set_termination.
  + constructor.
    * eapply co_empty_set_termination.
    * intros. exfalso. eapply co_empty_set_stable_wk_not_emp_list; eauto.
Qed.

Lemma co_wk_tr_inv `{gLtsP : @gLts P A H} `{!coFiniteImagegLts P A} ps s qs :
  ps ⟹[s] qs -> forall q, q ∈ qs -> exists p, (p : P) ⟹ᶜᵒ[s] (q : P) /\ p ∈ ps.
Proof.
  intro Hyp.
  dependent induction Hyp.
  + intros. exists q. split; eauto. constructor; eauto.
  + intros. eapply IHHyp in H0 as (p' & wk_tr & mem).
    destruct l as (eq & non_empty).
    subst. eapply (cowt_tau_set_from_pset_ispec p) in mem as (p'' & mem' & tr).
    exists p''. split; eauto. eapply cowt_tau; eauto.
  + intros. eapply IHHyp in H0 as (p' & wk_tr & mem).
    destruct l as (eq & non_empty).
    subst. destruct (cowt_extaction_set_from_pset_ispec p μ) as (Hspec1 & _).
    eapply Hspec1 in mem as (p'' & mem' & μ' & duo & tr).
    exists p''. split; eauto. eapply cowt_act; eauto.
Qed.

Lemma co_convergence_set_if_convergence_forall `{gLtsP : @gLts P A H} `{!coFiniteImagegLts P A}
  (ps : gset P) s :
  (forall (p : P), p ∈ ps -> p ⇓ᶜᵒ s) -> ps ⇓ s.
Proof.
  revert ps.
  dependent induction s.
  + constructor. eapply co_termination_set_for_all. intros; eauto.
    assert (p ⇓ᶜᵒ []).
    { eapply H0. eauto. }
    inversion H2; eauto.
  + intros. constructor.
    ++ eapply co_termination_set_for_all.
       intros. assert (p ⇓ᶜᵒ a :: s).
       { eapply H0; eauto. }
       inversion H2. subst; eauto.
    ++ intros. eapply IHs.
       intros. eapply co_wk_tr_inv in H1 as (p' & wk_tr & eq); eauto.
       eapply H0 in eq. inversion eq; subst. eapply H6; eauto.
Qed.

Lemma co_witness_wk_tr `{gLtsP : @gLts P A H} `{!coFiniteImagegLts P A} ps p0 s0 q0 :
  p0 ⟹ᶜᵒ[s0] q0 -> p0 ∈ ps -> (exists qs, ps ⟹[s0] qs /\ q0 ∈ qs).
Proof.
  intro wk_tr. revert ps.
  dependent induction wk_tr.
  + intros. exists ps. split; eauto. constructor.
  + intros. eapply cowt_tau_set_from_pset_ispec in l as eq; eauto.
    eapply IHwk_tr in eq as (qs' & wk_tr' & mem); eauto.
    exists qs'. split; eauto. eapply wt_tau; eauto. split; eauto.
    intro. eapply cowt_tau_set_from_pset_ispec in l as eq; eauto.
    rewrite H1 in eq. inversion eq.
  + intros. assert (q ∈ (cowt_extaction_set_from_pset ps μ)).
    { eapply cowt_extaction_set_from_pset_ispec; eauto. }
    eapply IHwk_tr in H1 as (qs' & wk_tr' & mem).
    exists qs'. split; eauto. eapply wt_act; eauto.
    split; eauto. intro. assert (q ∈ (cowt_extaction_set_from_pset ps μ)).
    { eapply cowt_extaction_set_from_pset_ispec; eauto. }
    rewrite H1 in H2. inversion H2.
Qed.

Lemma co_convergence_forall_if_convergence_set `{gLtsP : @gLts P A H} `{!coFiniteImagegLts P A}
  (ps : gset P) s :
  ps ⇓ s -> forall p, p ∈ ps -> p ⇓ᶜᵒ s.
Proof.
  unfold trace in s. revert ps.
  dependent induction s.
  + intros ps hm p mem. inversion hm; subst. constructor.
    eapply co_termination_set_iff_termination_forall; eauto.
  + intros. inversion H0; subst.
    constructor. eapply co_termination_set_iff_termination_forall; eauto.
    intros. assert (exists qs, ps ⟹{a} qs /\ q ∈ qs) as (qs & wk_tr & mem).
    { eapply co_witness_wk_tr; eauto. }
    eapply H6 in wk_tr.
    eapply IHs; eauto.
Qed.

Lemma co_convergence_set_iff_convergence_forall `{gLtsP : @gLts P A H} `{!coFiniteImagegLts P A}
  (ps : gset P) s :
  (forall (p : P), p ∈ ps -> p ⇓ᶜᵒ s) <-> ps ⇓ s.
Proof.
  split; [eapply co_convergence_set_if_convergence_forall | eapply co_convergence_forall_if_convergence_set].
Qed.
