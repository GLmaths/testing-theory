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

From stdpp Require Import base decidable gmap finite.
From Coq Require Import ssreflect.
From Coq.Program Require Import Equality.
From Must Require Import gLts Bisimulation Lts_OBA Lts_FW Lts_OBA_FB StateTransitionSystems Termination
    Must Bar CompletenessAS SoundnessAS Lift Subset_Act FiniteImageLTS WeakTransitions Convergence
    InteractionBetweenLts MultisetLTSConstruction ForwarderConstruction  ParallelLTSConstruction ActTau
    Testing_Predicate DefinitionAS MustE EquivalenceAS.
From stdpp Require Import gmultiset.

Section application.

  Lemma nil_refuses
  {Q A : Type} {H : ExtAction A}
  `{@gLtsOba Q A H gLtsQ gLtsEqQ}
  `{@Prop_of_Inter Q (mb A) A fw_inter H gLtsQ MbgLts}

  (q : Q) (h : forall α, q ↛{α}) (m : mb A) : 
  lts_refuses (q, m) τ.
  Proof.
    destruct (decide ((q, m) ↛)); eauto.
    eapply lts_refuses_spec1 in n as (q' & l').
    inversion l'; subst.
    + edestruct lts_refuses_spec2; eauto.
    + inversion l.
    + edestruct lts_refuses_spec2; eauto.
  Qed.

  Lemma nil_cnv
  {Q A : Type} {H : ExtAction A}
  `{@gLtsOba Q A H gLtsQ gLtsEqQ}
  `{@Prop_of_Inter Q (mb A) A fw_inter H gLtsQ MbgLts}
  (q : Q) (h : forall α, q ↛{α}) s m : 
  (q, m) ⇓ s.
  Proof.
    dependent induction s.
    - now eapply cnv_nil, terminate_if_refuses, nil_refuses.
    - eapply cnv_act.
      + now eapply terminate_if_refuses, nil_refuses.
      + intros (q', m') hw. inversion hw; subst.
        ++ exfalso. eapply (@lts_refuses_spec2 (Q * mb A)).
           eauto. now eapply nil_refuses.
        ++ inversion l; subst.
           +++ edestruct lts_refuses_spec2. eauto. eauto.
           +++ eapply cnv_preserved_by_wt_nil; eauto.
  Qed.

  CoInductive ionly_spec {P A : Type} {H : ExtAction A} 
    `{@gLtsOba P A H gLtsQ gLtsEqQ} (p : P) : Prop :=
  | mstep : (forall μ p', p ⟶[μ] p' -> exist_co_nba μ) 
        -> (forall α p', p ⟶{α} p' -> ionly_spec p') -> ionly_spec p.

  Lemma lts_non_blocking_ionly_spec {P A : Type}
        `{gLtsOba P A} (p : P) (pr : ionly_spec p) : dom (lts_oba_mo p) = ∅.
  Proof.
    eapply leibniz_equiv. intro a. split.
    + intros mem.
      eapply gmultiset_elem_of_dom in mem.
      eapply lts_oba_mo_spec_bis2 in mem as (p' & nb & l').
      destruct pr as (h1 & h2). eapply h1 in l' as (a' & nb' & duo').
      eapply dual_blocks in nb'; eauto.
      contradiction.
    + intro. set_solver.
Qed.

  Lemma lts_non_blocking_ionly_spec_wt_nil_empty_mb 
    {Q A : Type} {H : ExtAction A}
    `{M : @gLtsObaFB Q A H gLtsQ gLtsEqQ gLtsObaQ}
    `{@Prop_of_Inter Q (mb A) A fw_inter H gLtsQ MbgLts}
    p (pr : ionly_spec p) :
    (p, ∅) ⤓ -> forall t, (p, ∅) ⟹ t -> dom (lts_oba_mo t) = ∅.
  Proof.
    intros hpt p' hw.
    dependent induction hpt. dependent induction hw.
    - simpl.
      assert (disj_union (lts_oba_mo p) empty = (lts_oba_mo p)) as eq.
      multiset_solver. rewrite eq.
      now eapply lts_non_blocking_ionly_spec.
    - inversion l; subst.
      + destruct pr as (h1 & h2). eapply H2; eauto.
      + inversion l0.
      + exfalso. eapply (gmultiset_not_elem_of_empty μ2).
        assert (non_blocking μ2) as nb.
        destruct eq; eauto.
        eapply non_blocking_action_in_ms in nb; eauto.
        replace (∅ : gmultiset A) with ({[+ μ2 +]} ⊎ b2) by eauto. multiset_solver.
    Qed.

  Lemma lts_non_blocking_ionly_spec_wt_nil 
    {Q A : Type} {H : ExtAction A}
    `{M : @gLtsObaFB Q A H gLtsQ gLtsEqQ gLtsObaQ}
    `{@Prop_of_Inter Q (mb A) A fw_inter H gLtsQ MbgLts}
    n p (pr : ionly_spec p) m :
    (p, m) ⤓ -> size m = n -> forall t, (p, m) ⟹ t
      -> dom (lts_oba_mo t) ⊆ dom m.
  Proof.
    dependent induction n; subst; intro hpt; dependent induction hpt; intros heq p' hw.
    - eapply gmultiset_size_empty_inv in heq. subst.
      replace (dom (lts_oba_mo p')) with (∅ : gset A).
      + multiset_solver. 
      + symmetry. eapply lts_non_blocking_ionly_spec_wt_nil_empty_mb; eauto with mdb.
    - inversion hw; subst.
      + simpl. 
        intro μ. intro mem.
        eapply gmultiset_elem_of_dom in mem.
        eapply gmultiset_elem_of_disj_union in mem.
        destruct mem as [in_oba | in_mem].
        ++ eapply gmultiset_elem_of_dom. eapply gmultiset_elem_of_dom in in_oba.
           eapply lts_non_blocking_ionly_spec in pr.
           set_solver.
        ++ eapply gmultiset_elem_of_dom.
           eapply lts_mb_nb_with_nb_spec1 in in_mem as (nb & in_mem).
           exact in_mem.
      + destruct pr as (h1 & h2); inversion l; subst; eauto.
        ++ inversion l0.
        ++ assert (non_blocking μ2) as nb. destruct eq; eauto.
           eapply non_blocking_action_in_ms in nb; eauto; subst.
           eapply IHn in w; eauto with mdb.
           +++ intros b mem%w%gmultiset_elem_of_dom.
               eapply gmultiset_elem_of_dom.
               multiset_solver.
           +++ rewrite gmultiset_size_disj_union in heq. 
               rewrite gmultiset_size_singleton in heq. eauto.
  Qed.

  Lemma ionly_nil_leq2_wt_nil 
    {Q A : Type} {H : ExtAction A}
    `{M : @gLtsObaFB Q A H gLtsQ gLtsEqQ gLtsObaQ}
    `{@Prop_of_Inter Q (mb A) A fw_inter H gLtsQ MbgLts}
    n p (pr : ionly_spec p) m :
    (p, m) ⤓ -> size m = n -> exists t, (p, m) ⟹ t /\ t ↛ /\ dom (lts_oba_mo t) ⊆ dom m.
  Proof.
    intros ht heq. edestruct @terminate_then_wt_refuses as (t & hw & hst); eauto with mdb.
    exists t; split; eauto. split; eauto. eapply lts_non_blocking_ionly_spec_wt_nil; eauto.
  Qed.

  Lemma ionly_wt
    {Q A : Type} {H : ExtAction A}
    `{M : @gLtsOba Q A H gLtsQ gLtsEqQ}
    `{@Prop_of_Inter Q (mb A) A fw_inter H gLtsQ MbgLts}
    p (pr : ionly_spec p) m p' m' : 
    (p ▷ m) ⟹ (p' ▷ m') 
      -> ionly_spec p'.
  Proof.
    intro mem.
    dependent induction mem.
    + exact pr.
    + inversion l; subst.
      ++ destruct pr as (only_receive & Hyp). assert (ionly_spec a2).
         eapply Hyp; eauto. eapply IHmem; eauto.
      ++ inversion l0.
      ++ destruct eq as (nb & duo).
         assert (ionly_spec a2). destruct pr as (only_receive & Hyp).
         eapply Hyp; eauto. eapply IHmem; eauto.
  Qed.

 (*  Lemma ionly_nil_leq2 {P Q A : Type} `{
    @gLtsObaFB P A H gLtsP gLtsEqP gLtsObaP,
    @gLtsObaFB Q A H gLtsQ gLtsEqQ gLtsObaQ}

    `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}
    `{@Prop_of_Inter Q (mb A) A fw_inter H gLtsQ MbgLts}

    (p : P) (pr : ionly_spec p) (q : Q) m (h : forall α, q ↛{α}) : 
    (p, m) ≼₂ (q, m).
  Proof.
    intros s t hcnv hw hst.
    dependent induction hw.
    - inversion hcnv; subst.
      edestruct ionly_nil_leq2_wt_nil as (p' & hw & hst' & hsub); eauto.
      exists p'. split; eauto.
      split; eauto.
      intro μ. intro mem.
      destruct (decide (non_blocking μ)) as [nb | not_nb].
      + rename μ into η.
        eapply lts_refuses_spec1 in mem as (p'' & Tr).
        assert (η ∈ dom (lts_oba_mo p')) as mem'.
        eapply gmultiset_elem_of_dom. eapply lts_oba_mo_spec_bis1; eauto.
        eapply hsub in mem'. eapply lts_refuses_spec2.
        eapply gmultiset_elem_of_dom in mem'.
        assert (m = {[+ η +]} ⊎ (m ∖ {[+ η +]})) as eq'. multiset_solver.
        rewrite eq'.
        exists (q ▷ (m ∖ {[+ η +]})). eapply ParRight.
        eapply lts_multiset_minus; eauto.
      + destruct p' as (p' , m').
        assert (ionly_spec p') as Hyp. eapply ionly_wt; eauto.
        destruct Hyp as (only_receive & Hyp').
        eapply lts_refuses_spec1 in mem as ((p'' , m'') & Tr'').
        inversion Tr''; subst.
        ++ assert (exist_co_nba μ) as (η & nb & duo). eapply only_receive; eauto.
           eapply lts_refuses_spec2. exists (q ▷ ({[+ η +]} ⊎ m)).
           eapply ParRight. simpl in *. eapply lts_multiset_add; eauto.
        ++ eapply blocking_action_in_ms in not_nb as (eq' & duo' & nb') ; eauto ;subst.
           eapply lts_refuses_spec2. exists (q ▷ {[+ co μ +]} ⊎ m).
           eapply ParRight. eapply lts_multiset_add; eauto.
    - exfalso. eapply (@lts_refuses_spec2 (Q * mb A)). eauto. now eapply nil_refuses.
    - inversion hcnv; inversion l; subst.
      + exfalso. eapply (@lts_refuses_spec2 Q); eauto.
      + destruct (decide (non_blocking μ)) as [nb | not_nb].
        ++ assert (non_blocking μ). eauto.
           eapply non_blocking_action_in_ms in nb; eauto ; subst.
           edestruct (IHhw b2 p) as (t' & hw' & hst' & hsub'); eauto with mdb.
           eapply H8, wt_act. eapply ParRight.
           eapply lts_multiset_minus; eauto. eapply wt_nil.
           exists t'. split. eapply wt_act; eauto. eapply ParRight.
           eapply lts_multiset_minus;eauto. now split.
        ++ eapply blocking_action_in_ms in not_nb as (eq & duo & nb); eauto ; subst.
           edestruct (IHhw ({[+ co μ +]} ⊎ m) p) as (t' & hw' & hst' & hsub'); eauto.
           eapply H8, wt_act. eapply ParRight. eauto. eapply wt_nil.
           exists t'. split. eapply wt_act; eauto. eapply ParRight. eauto. now split.
  Qed.

  Lemma input_only_leq_nil {P Q A : Type} `{
    @gLtsObaFB P A H gLtsP gLtsEqP V, !FiniteImagegLts P A,
    @gLtsObaFB Q A H gLtsQ gLtsEqQ W, !FiniteImagegLts Q A,
    @gLtsObaFB E A H gLtsE gLtsEqE X, !FiniteImagegLts E A, !Testing_Predicate E A outcome, (∀ e : E, Decision (outcome e))}

    `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}
    `{@Prop_of_Inter Q E A parallel_inter H gLtsQ gLtsE}

    `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}
    `{@Prop_of_Inter (P * mb A) E A parallel_inter H (inter_lts fw_inter) gLtsE}

    `{@Prop_of_Inter Q (mb A) A fw_inter H gLtsQ MbgLts}
    `{@Prop_of_Inter (Q * mb A) E A parallel_inter H (inter_lts fw_inter) gLtsE}

    `{@gen_spec_conv  _ _ _ _ _ outcome _ co_of gen_conv, 
    @gen_spec_acc (P * mb A) (Q * mb A) _ _ _ _ _ outcome _ co_of gen_acc _ _}

    (p : P) (pr : ionly_spec p) (q : Q) (h : forall α, q ↛{α}) : 
    @pre_extensional _ _ _ _ _ outcome _ p q.
  Proof.
    now eapply equivalence_bhv_acc_ctx; split; intros ? ?; [eapply nil_cnv | eapply ionly_nil_leq2].
  Qed. *)

End application.
