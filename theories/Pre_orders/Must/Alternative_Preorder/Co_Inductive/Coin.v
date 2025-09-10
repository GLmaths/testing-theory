(*
   Copyright (c) 2024 Nomadic Labs
   Copyright (c) 2024 Paul Laforgue <paul.laforgue@nomadic-labs.com>
   Copyright (c) 2024 Léo Stefanesco <leo.stefanesco@mpi-sws.org>

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

Require ssreflect.
Require Import Coq.Unicode.Utf8.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Program.Equality.
Require Import Coq.Wellfounded.Inverse_Image.
Require Import Coq.Logic.JMeq.
Require Import Coq.Program.Wf Setoid.
Require Import Coq.Program.Equality.
From Coq.Logic Require Import ProofIrrelevance.
From stdpp Require Import base countable finite gmap list finite base decidable finite gmap.
From Must Require Import ActTau InputOutputActions gLts Bisimulation Lts_OBA Lts_OBA_FB Lts_FW FiniteImageLTS
            Subset_Act Must Soundness Completeness Equivalence StateTransitionSystems
              GeneralizeLtsOutputs Termination WeakTransitions Convergence  
               InteractionBetweenLts MultisetLTSConstruction ForwarderConstruction ParallelLTSConstruction .

CoInductive copre `{@FiniteImagegLts A L HL LtsP, @FiniteImagegLts B L HL LtsQ} (ps : gset A) (q : B) : Prop := {
    c_tau q' : q ⟶ q' -> copre ps q'
  ; c_now : (forall p, p ∈ ps -> p ⤓) -> q ↛ ->
            exists p p', p ∈ ps /\ p ⟹ p' /\ p' ↛ /\ lts_acc_set_of p' ⊆ lts_acc_set_of q
  ; c_step : forall μ q' ps', (forall p, p ∈ ps -> p ⇓ [μ]) ->
                         q ⟶[μ] q' -> wt_set_from_pset_spec ps [μ] ps' -> copre ps' q'
  ; c_cnv : (forall p, p ∈ ps -> p ⤓) -> q ⤓
  }.

Notation "p ⩽ q" := (copre p q) (at level 70).

Lemma copre_if_prex
  `{@FiniteImagegLts A L HL LtsP, @FiniteImagegLts B L HL LtsQ}
  (ps : gset A) (q : B) : ps ≼ₓ q -> ps ⩽ q.
Proof.
  revert ps q.
  cofix H2.
  intros ps q (hsub1 & hsub2).
  constructor.
  - intros q' l. eapply H2, bhvx_preserved_by_tau; eauto.
  - intros hterm hst.
    edestruct (hsub2 [] q) as (p' & hw & p'' & hstp' & stable & hsub0).
    eapply wt_nil. eassumption. intros p' mem. constructor.
    eapply hterm. eauto.
    exists p'. exists p''. repeat split; eauto.
  - intros μ q' ps' hcnv hw wtspec.
    eapply H2.
    eapply bhvx_preserved_by_mu; eauto.
    intros p0 mem0.
    edestruct (hcnv p0 mem0); eauto.
  - intros. edestruct (hsub1 []); eauto.
    intros. constructor. eauto.
Qed.

Lemma co_preserved_by_wt_nil
  `{@FiniteImagegLts A L HL LtsP, @FiniteImagegLts B L HL LtsQ}
  (ps : gset A) (q q' : B) : q ⟹ q' -> ps ⩽ q -> ps ⩽ q'.
Proof. intro hw. dependent induction hw; eauto. destruct 1. eauto. Qed.

Lemma prex1_if_copre
  `{@FiniteImagegLts A L HL LtsP, @FiniteImagegLts B L HL LtsQ}
  (ps : gset A) (q : B) : ps ⩽ q -> ps ≼ₓ1 q.
Proof.
  intros.
  intros s hcnv.
  revert ps q H1 hcnv.
  dependent induction s; intros ps q H1 hcnv; destruct H1.
  + constructor. eapply c_cnv0.
    intros. now destruct (hcnv p H1).
  +  assert (q ⤓) by (now eapply c_cnv0; intros; destruct (hcnv p H1)).
     assert (hcnv0 : ∀ p : A, p ∈ ps → p ⇓ [a]).
     intros p' mem'%hcnv.
     constructor. now destruct mem'.
     intros p1 hw1. inversion mem'; subst. eapply H6 in hw1. inversion hw1; subst.
     now constructor.
     now constructor.
     eapply cnv_act; eauto.
     intros q' hw.
     eapply wt_decomp_one in hw as (q0' & q1' & q1 & hlt & hw0').
     assert (hpre : ps ⩽ q). constructor; eauto.
     eapply IHs; eauto.
     ++ eapply co_preserved_by_wt_nil. eassumption.
        eapply (co_preserved_by_wt_nil ps q q0') in hpre. destruct hpre.
        eapply (c_step1 a q1'); eauto.
        eapply (wt_s_set_from_pset_ispec ps [a] hcnv0); eauto. eassumption.
     ++ intros p mem.
        edestruct (wt_s_set_from_pset_ispec ps [a] hcnv0).
        eapply H2 in mem as (p0 & hmem0%hcnv & hw0).
        inversion hmem0; subst. eauto.
Qed.

Lemma prex2_if_copre
  `{@FiniteImagegLts A L HL LtsP, @FiniteImagegLts B L HL LtsQ}
  (ps : gset A) (q : B) : ps ⩽ q -> ps ≼ₓ2 q.
Proof.
  revert ps q.
  intros ps q hsub s.
  revert ps q hsub.
  dependent induction s; intros ps q hsub.
  + intros q' hw hstq' hcnv.
    dependent induction hw; try rename p into q.
    ++ destruct hsub.
       edestruct c_now0.
       intros p0 mem0. edestruct (hcnv p0 mem0); eauto. eassumption.
       decompose record H1. repeat eexists;  eauto.
    ++ eapply IHhw; eauto. destruct hsub. eapply c_tau0. eassumption.
  + intros. rename a into μ.
    replace (μ :: s) with ([μ] ++ s) in H1 by eauto.
    eapply wt_split in H1 as (q0 & hw0 & hw1).
    eapply wt_decomp_one in hw0 as (q0' & q1' & q1 & hlt & hw0').
    assert (ps ⩽ q0') by (eapply co_preserved_by_wt_nil; eauto).
    assert (hcnv' : ∀ p : A, p ∈ ps → p ⇓ [μ]).
    intros. constructor. edestruct (H3 p H4); eauto.
    intros. constructor. eapply cnv_terminate.
    eapply cnv_preserved_by_wt_act; eauto.
    set (ps' := wt_s_set_from_pset ps [μ] hcnv').
    assert (ps ⩽ q0') by (eapply co_preserved_by_wt_nil; eauto).
    assert (ps' ⩽ q1'). destruct H1.
    eapply c_step0. eassumption. eassumption.
    eapply wt_s_set_from_pset_ispec.
    assert (ps' ⩽ q0) by (eapply co_preserved_by_wt_nil; eauto).
    edestruct (IHs ps' q0 H6 _ hw1 H2) 
    as (r & memr & p' & hwr & hst & hsub').
    intros.
    edestruct (wt_s_set_from_pset_ispec ps [μ] hcnv').
    eapply H8 in H7 as (p0  & hmem0 & hw0).
    eapply cnv_preserved_by_wt_act; eauto.
    edestruct (wt_s_set_from_pset_ispec ps [μ] hcnv').
    eapply H7 in memr as (p0  & hmem0 & hw0).
    exists p0. split. eassumption. exists p'. split.
    eapply wt_push_left; eassumption.
    split; eauto.
Qed.


Theorem eqx `{@FiniteImagegLts A L HL LtsP, @FiniteImagegLts B L HL LtsQ} (X : gset A) (q : B) :
  X ≼ₓ q <-> X ⩽ q.
Proof.
  split.
  - eapply copre_if_prex.
  - intros hco. split. now eapply prex1_if_copre. now eapply prex2_if_copre.
Qed.

Section eq_contextual.
  
  Context `{H : ExtAction A}.
  Context `{gLtsP : !gLts P A, !FiniteImagegLts P A}.
  Context `{gLtsQ : !gLts Q A, !FiniteImagegLts Q A}.
  Context `{gLtsE : !gLts E A, !FiniteImagegLts E A}.

  Context `{@gLtsObaFB P A H gLtsP gLtsEqP gLtsObaP}.
  Context `{@gLtsObaFB Q A H gLtsQ gLtsEqQ gLtsObaQ}.
  Context `{@gLtsObaFB E A H gLtsE gLtsEqE gLtsObaE}.

  Context `{good : E -> Prop}.
  Context `{good_dec : forall e, Decision (good e)}.
  Context `{!Good E A good}.

  (* ************************************************** *)
  Context `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}.
  Context `{@Prop_of_Inter Q E A parallel_inter H gLtsQ gLtsE}.
  Context `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}.
  Context `{@Prop_of_Inter (P * mb A) E A parallel_inter H (inter_lts fw_inter) gLtsE}.
  Context `{@Prop_of_Inter Q (mb A) A fw_inter H gLtsQ MbgLts}.
  Context `{@Prop_of_Inter (Q * mb A) E A parallel_inter H (inter_lts fw_inter) gLtsE}.

  Context `{igen_conv : @gen_spec_conv  _ _ _ _ _ good Good0 co_of gen_conv}.
  Context `{igen_acc : @gen_spec_acc (P * mb A) (Q * mb A) _ _ _ _ _ good Good0 co_of gen_acc _ _}.

  Theorem eq_ctx (p : P) (q : Q) :
    @pre_extensional P Q _ _ _ good _ p q <-> {[ p ▷ (∅ : mb A) ]} ⩽ q ▷ (∅ : mb A).
  Proof.
    rewrite <- eqx, <- alt_set_singleton_iff.
    now rewrite equivalence_bhv_acc_ctx.
  Qed.
End eq_contextual.
