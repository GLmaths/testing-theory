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

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Wellfounded Require Import Inverse_Image.
From Stdlib.Program Require Import Equality.

From stdpp Require Import base countable finite gmap list finite base decidable finite gmap.
From Coinduction Require Import all.

From TestingTheory Require Import
  ActTau Subset_Act gLts FiniteImageLTS Lts_OBA Lts_Finite_Output_Chain Lts_OBA_FB Lts_FW
  Termination Convergence WeakTransitions Bisimulation
  SetLTSConstruction
  InteractionBetweenLts MultisetLTSConstruction ForwarderConstruction ParallelLTSConstruction
  Lift StateTransitionSystems
  Testing_Predicate Must MustE 
  DefinitionAS Soundness Equivalence Completeness
  DefinitionMS EquivalenceMS DefinitionFMS EquivalenceFMS.

(* TODO: define me using the coinduction library *)

Record copre_ `{@FiniteImagegLts P A H gLtsP, @FiniteImagegLts Q A H gLtsQ}
  `{gLtsT : !gLtsEq T H}
  `{@AbsAction P T FinA PreAct A H Φ 𝝳P _ _ }
  `{@AbsAction Q T FinA PreAct A H Φ 𝝳Q _ _ }
  (FIX : gset P -> gset Q -> Prop) (X : gset P) (Y : gset Q) : Prop := {
    c_tau_ Y' : wt_set_from_pset_spec1 Y [] Y' -> FIX X Y'
  ; c_now_ : X ⤓ -> forall q , q ∈ Y -> q ↛ ->
            exists p, p ∈ X /\ exists p', p ⟹ p' /\ p' ↛ /\ ⌈ (𝝳P ∘ Φ) ⌉ (coR p') ⊆ ⌈ (𝝳Q ∘ Φ) ⌉ (coR q)
  ; c_step_ : forall μ Y' X', X ⇓ [μ] ->
                         wt_set_from_pset_spec1 Y [μ] Y' -> wt_set_from_pset_spec X [μ] X' -> FIX X' Y'
  ; c_cnv_ : X ⤓ -> Y ⤓
  }.
  #[global] Arguments c_tau_ {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FIX X Y}.
  #[global] Arguments c_now_ {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FIX X Y}.
  #[global] Arguments c_step_ {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FIX X Y}.
  #[global] Arguments c_cnv_ {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FIX X Y}.

Program Definition copre_m 
`{@FiniteImagegLts P A H gLtsP, @FiniteImagegLts Q A H gLtsQ}
`{gLtsT : !gLtsEq T H}
`{AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳P _ _ }
`{AbsQT : @AbsAction Q T FinA PreAct A H Φ 𝝳Q _ _ } : mon (gset P -> gset Q -> Prop) := 
{| body := (@copre_ P A H _ _ Q _ _ T _ _ _ Φ 𝝳P AbsPT 𝝳Q AbsQT) |} .
Next Obligation.
  intros F1 F2 HF X Y h; constructor.
  - intros; apply HF, h.(c_tau_); auto.
  - exact h.(c_now_).
  - intros; eapply HF, h.(c_step_); auto.
    + exact H2.
    + exact H3.
    + exact H4.
  - exact h.(c_cnv_).
Qed.

Definition copre `{@FiniteImagegLts P A H gLtsP, @FiniteImagegLts Q A H gLtsQ}
`{gLtsT : !gLtsEq T H}
`{AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳P _ _ }
`{AbsQT : @AbsAction Q T FinA PreAct A H Φ 𝝳Q _ _ } := 
gfp (@copre_m P A H _ _ Q _ _ T _ _ _ Φ 𝝳P AbsPT 𝝳Q AbsQT).

Notation "X ᶜᵒ≼ₜₒᵥᵥₑᵣ Y" := (copre X Y) (at level 70).

Section copre.
  Context `{@FiniteImagegLts P A H gLtsP, @FiniteImagegLts Q A H gLtsQ}.
  Context `{gLtsT : !gLtsEq T H}.
  Context `{AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳P _ _ }.
  Context `{AbsQT : @AbsAction Q T FinA PreAct A H Φ 𝝳Q _ _ }.

  Definition REL := gset P -> gset Q -> Prop.

  Lemma c_tau {X : gset P } { Y Y' : gset Q} : X ᶜᵒ≼ₜₒᵥᵥₑᵣ Y -> wt_set_from_pset_spec1 Y [] Y' -> X ᶜᵒ≼ₜₒᵥᵥₑᵣ Y' .
  Proof.
    intros h%(gfp_pfp copre_m) ; intros; now apply h.(c_tau_).
  Qed.

  Lemma c_tau' {PRE : Chain (@copre_m P A H _ _ Q _ _ T _ _ _ Φ 𝝳P AbsPT 𝝳Q AbsQT)} { X : gset P } { Y Y' : gset Q} :
    (@copre_m P A H _ _ Q _ _ T _ _ _ Φ 𝝳P AbsPT 𝝳Q AbsQT) (elem PRE) X Y -> wt_set_from_pset_spec1 Y [] Y' -> elem PRE X Y' .
  Proof.
    intros h Ht. now apply h.(c_tau_). Qed.

  Lemma c_now { X : gset P } { Y : gset Q}
    : X ᶜᵒ≼ₜₒᵥᵥₑᵣ Y
      -> X ⤓
      -> forall q , q ∈ Y -> q ↛
      -> exists p, p ∈ X
                /\ exists p', p ⟹ p'
                /\ p' ↛
                /\ ⌈ (𝝳P ∘ Φ) ⌉ (coR p') ⊆ ⌈ (𝝳Q ∘ Φ) ⌉ (coR q) .
  Proof.
    intros h%(gfp_pfp copre_m); intros.
    eapply h.(c_now_);eauto.
  Qed.

  Lemma c_step { X X' : gset P } { Y Y' : gset Q} {μ}
    : X ᶜᵒ≼ₜₒᵥᵥₑᵣ Y
      -> X ⇓ [μ]
      -> wt_set_from_pset_spec1 Y [μ] Y'
      -> wt_set_from_pset_spec X [μ] X'
      -> X' ᶜᵒ≼ₜₒᵥᵥₑᵣ Y' .
  Proof.
    intros h%(gfp_pfp copre_m); intros; now eapply h.(c_step_); eauto.
  Qed.

  Lemma c_cnv { X : gset P } { Y : gset Q}
    : X ᶜᵒ≼ₜₒᵥᵥₑᵣ Y
      -> X ⤓
      -> Y ⤓ .
  Proof.
    intros h%(gfp_pfp copre_m); intros; now eapply h.(c_cnv_); eauto.
  Qed.

  Lemma copre_if_prex (X : gset P) (Y : gset Q) : X ≼ₛₑₜ_ₐₛ Y -> X ᶜᵒ≼ₜₒᵥᵥₑᵣ Y.
  Proof.
    revert X Y; unfold copre.
    coinduction RR CIH.
    intros X Y (hsub1 & hsub2).
    constructor.
    - intros Y' l.
      eapply CIH, bhvx_preserved_by_reductions; eauto. split; eauto.
    - intros hterm q mem hst.
      destruct (hsub2 q [] q mem) as (p' & hw & hstp' & hsub0); eauto.
      + eapply wt_nil.
      + intros p' mem'; constructor.
        eapply termination_if_termination_set_helper;eauto.
    - intros μ Y' ps' hcnv hw wtspec.
      eapply CIH, bhvx_preserved_by_external_action; eauto.
      + inversion hcnv;subst. eapply termination_if_termination_set_helper;eauto.
      + split;eauto.
    - intro Hyp_conv. eapply equiv_termination.
      eapply equiv_termination in Hyp_conv.
      eapply convergence_set_if_convergence_forall.
      eapply hsub1. eapply convergence_forall_if_convergence_set;eauto.
  Qed.

  Lemma co_preserved_by_wt_nil
    (X : gset P) (Y Y' : gset Q) : wt_set_from_pset_spec1 Y [] Y' -> X ᶜᵒ≼ₜₒᵥᵥₑᵣ Y -> X ᶜᵒ≼ₜₒᵥᵥₑᵣ Y'.
  Proof.
    intros hw Hyp. eapply c_tau;eauto.
  Qed.


  Lemma prex1_if_copre (X : gset P) (Y : gset Q) : X ᶜᵒ≼ₜₒᵥᵥₑᵣ Y -> X ₁≼ₛₑₜ_ₐₛ Y.
  Proof.
    intros hpq s; revert X Y hpq.
    dependent induction s; intros X Y hpq hcnv.
    + eapply convergence_set_if_convergence_forall in hcnv.
      eapply convergence_forall_if_convergence_set.
      eapply equiv_termination. eapply (c_cnv hpq).
      eapply equiv_termination. exact hcnv.
    + assert (Y ⤓).
      { eapply convergence_set_if_convergence_forall in hcnv. inversion hcnv; subst.
      eapply (c_cnv hpq). eauto. }
      assert (hcnv0 : ∀ p : P, p ∈ X → p ⇓ [a]) by (intros; now eapply cnv_wk, hcnv).
      intros. eapply cnv_act; eauto. eapply termination_if_termination_set_helper;eauto.
      intros q' hw.
      eapply IHs.
      ++ eapply (c_step hpq); eauto.
         * eapply convergence_set_if_convergence_forall;eauto. 
         * intros q'' mem. exists q. split;eauto.
           instantiate (1:= {[ q' ]}) in mem.
           assert (q'' = q') by set_solver. subst. exact hw.
         * eapply (wt_s_set_from_pset_ispec X [a] hcnv0); eauto.
      ++ intros p mem.
         edestruct (wt_s_set_from_pset_ispec X [a] hcnv0) as (TrSet_hyp1 & TrSet_hyp2).
         eapply TrSet_hyp1 in mem as (p0 & hmem0%hcnv & hw0).
         inversion hmem0; subst. eauto.
      ++ set_solver.
  Qed.

  Lemma prex2_if_copre (X : gset P) (Y : gset Q) : X ᶜᵒ≼ₜₒᵥᵥₑᵣ Y -> X ₂≼ₛₑₜ_ₐₛ Y.
  Proof.
    intros hsub q s q' mem; revert X Y q q' mem hsub ; dependent induction s; intros X Y q q' mem hsub.
    + intros hw hstq' hcnv. revert X Y mem hsub hstq' hcnv.
      dependent induction hw;intros.
      * edestruct (c_now hsub).
        - eapply equiv_termination.
          eapply convergence_set_if_convergence_forall;eauto.
        - eassumption.
        - firstorder.
        - exists x. eauto.
      * eapply IHhw. 
        - eauto. 
        - instantiate (1:= {[ q ]}). set_solver.
        - apply (c_tau hsub); eauto.
          intros q'' mem''.
          assert (q'' = q) by set_solver. subst. exists p. split; eauto. eapply lts_to_wt_tau. eauto.
        - eauto.
        - eauto.
    + intros hqq' hq hcnv; rename a into μ.
      change (μ :: s) with ([μ] ++ s) in hqq'.
      eapply wt_split in hqq' as (q0 & hw0 & hw1).
      eapply wt_decomp_one in hw0 as (q0' & q1' & q1 & hlt & hw0').
      assert (X ᶜᵒ≼ₜₒᵥᵥₑᵣ {[ q0' ]}).
      { eapply co_preserved_by_wt_nil; eauto. intros q'' mem''.
        assert (q'' = q0') by set_solver. subst. eauto. }
      assert (hcnv' : ∀ p : P, p ∈ X → p ⇓ [μ]) by (intros; now eapply cnv_wk, hcnv).
      assert (∀ p : P, p ∈ X → p ⇓ [μ]) as hp_conv;eauto.
      eapply convergence_set_if_convergence_forall in hp_conv.
      set (X' := wt_s_set_from_pset X [μ] hcnv').
      assert (X' ᶜᵒ≼ₜₒᵥᵥₑᵣ {[ q1' ]}) as hpq''. {
        eapply c_step;eauto.
        + intros q''' mem'''. assert (q''' = q1') by set_solver. subst.
          exists q0'. split. set_solver. eapply lts_to_wt;eauto.
        + eapply wt_s_set_from_pset_ispec.
      }
      assert (X' ᶜᵒ≼ₜₒᵥᵥₑᵣ {[ q0 ]}) as hp'q.
      { eapply co_preserved_by_wt_nil; eauto. intros q''' mem'''.
        assert (q''' = q0) by set_solver. subst. exists q1'. split;eauto. set_solver.
      }
      edestruct (IHs X' ({[ q0 ]})) as (r & memr & p' & hwr & hst & hsub').
      * instantiate (1:= q0). set_solver.
      * eauto.
      * exact hw1.
      * exact hq.
      * intros p hp.
        edestruct (wt_s_set_from_pset_ispec X [μ] hcnv') as (TrSet_hyp1 & TrSet_hyp2).
        eapply TrSet_hyp1 in hp as (p0 & hmem0 & hw0).
        eapply cnv_preserved_by_wt_act; eauto.
      * edestruct (wt_s_set_from_pset_ispec X [μ] hcnv') as (TrSet_hyp1 & TrSet_hyp2).
        eapply TrSet_hyp1 in memr as (p0  & hmem0 & hw0).
        exists p0; split; [ auto | ].
        exists p'; split; [ | split; eauto ].
        eapply wt_push_left; eauto.
  Qed.


  Theorem eqx (X : gset P) (Y : gset Q) :
    X ≼ₛₑₜ_ₐₛ Y <-> X ᶜᵒ≼ₜₒᵥᵥₑᵣ Y.
  Proof.
    split; [ eapply copre_if_prex | ].
    intros hco; split; [ now eapply prex1_if_copre | now eapply prex2_if_copre ].
  Qed.
End copre.

Section must_co_inductive_acceptance_preorder.
  Context `{outcome : T -> Prop}.
  Context `{outcome_dec : forall t, Decision (outcome t)}.
  Context `{P : Type}.
  Context `{Q : Type}.
  Context `{H : !ExtAction A}.

  Context `{@gLtsOba P A H gLtsEqP, !FiniteImagegLts P A}.
  Context `{@gLtsOba Q A H gLtsEqQ, !FiniteImagegLts Q A}.
  Context `{@gLtsOba T A H gLtsEqT, !CountablegLts T A, !Testing_Predicate outcome _}.

  Context `{!Prop_of_Inter P T A dual}.
  Context `{!Prop_of_Inter Q T A dual}.

  Context `{CC : Countable PreAct}.
  Context `{@FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 _ _ _ _ }.
  Context `{@FinitaryAbsAction Q T FinA PreAct A H Φ 𝝳 _ _ _ _ }.

  Context `{tc_spec : @test_convergence_spec T _ _ _ outcome _ t_conv}.
  Context `{ta_spec : @test_co_acceptance_set_spec PreAct _ _ T _ _ _ outcome Testing_Predicate0 ta (fun x => 𝝳 (Φ x))}.

  (** * Main equivalence theorems *)

  Section FWⁿ.

  Context `{!gLtsObaFW P A}.
  Context `{!gLtsObaFW Q A}.
  Context `{!gLtsObaFB T A}.

  (** ** The co-inductive-tower characterisation on FW is equivalent to the extensional must preorder *)
  Corollary equivalence_fw_co_inductive_acceptance_and_must_e_singleton (p : P) (q : Q) :
    pre_extensional outcome p q <-> ({[ p ]} : gset P) ᶜᵒ≼ₜₒᵥᵥₑᵣ ({[ q ]} : gset Q).
  Proof.
    rewrite <- eqx. rewrite alt_set_singleton_iff.
    rewrite equivalence_fw_bhv_acc_ctx;eauto.
  Qed.
  
  (** ** The co-inductive-towercharacterisation on FW is equivalent to the inductive must preorder *)
  (* From TestingTheory Require Import Lts_CN.
  Corollary equivalence_fw_co_inductive_acceptance_and_must_i (X : gset P) (Y : gset Q) :
    X ≠ ∅ -> X ⊑ₛₑₜ_ₘᵤₛₜᵢ Y <-> (X : gset P) ᶜᵒ≼ₜₒᵥᵥₑᵣ (Y : gset Q).
  Proof.
    rewrite <- eqx. split. 
    + induction Y using set_ind_L.
      - intros. split.
        * intros s h_conv t mem. inversion mem.
        * intros q s q' mem. inversion mem.
      - intros H'. eapply alt_set_union_right.
        * eapply set_must_union_left_rev in H' as Hyp_Must;eauto.
          (* clear H5. *) clear H'. clear IHY. clear H6.
          induction X using set_ind_L.
          ++ exfalso. eapply H5. eauto. 
          ++ destruct X using set_ind_L.
             ** rewrite union_empty_r_L.
                rewrite union_empty_r_L in Hyp_Must.
                eapply alt_set_singleton_iff.
                eapply completeness_fw.
                eapply must_set_singleton_iff;eauto.
             ** eapply alt_set_union_l.
                eapply alt_set_singleton_iff.
                eapply completeness_fw.
                eapply must_set_singleton_iff.
                intros t hym_must. eapply Hyp_Must.
                eapply mx_sum.
             -- eauto.
             -- 
        * eapply IHY. eapply set_must_union_right_rev;eauto.
    + eapply soundnessx.
    Unshelve.
    eapply MkgLtsCNenabled. intros. edestruct boomerang as (x & Hyp);eauto.
    eapply Hyp in H6. exists x;eauto. destruct H6. eauto. symmetry. eauto.
  Admitted. *)

  Corollary equivalence_fw_co_inductive_acceptance_and_must_i_singleton (p : P) (q : Q) :
    p ⊑ₘᵤₛₜᵢ q <-> ({[ p ]} : gset P) ᶜᵒ≼ₜₒᵥᵥₑᵣ ({[ q ]} : gset Q).
  Proof.
    rewrite <- eqx.
    rewrite alt_set_singleton_iff.
    eapply equivalence_fw_acc_set_and_must_i.
  Qed.

  End FWⁿ.
  (** ---- *)
  Section Lⁿ.
  
  Context `{!Prop_of_Inter P (MO A) A fw_inter}.
  Context `{!Prop_of_Inter (P * MO A) T A dual}.
  Context `{!Prop_of_Inter Q (MO A) A fw_inter}.
  Context `{!Prop_of_Inter (Q * MO A) T A dual}.
  
  Context `{!gLtsObaFB P A, !FiniteOutputChain_LtsOba P}.
  Context `{!gLtsObaFB Q A, !FiniteOutputChain_LtsOba Q}.
  Context `{!gLtsObaFB T A, !FiniteOutputChain_LtsOba T}.

  (** ** The co-inductive-tower characterisation on toFW is equivalent to the inductive must preorder *)
  Corollary equivalence_co_inductive_acceptance_and_must_i_singleton (p : P) (q : Q) :
    p ⊑ₘᵤₛₜᵢ q <-> ({[ (p, ∅) ]} : gset (P * MO A)) ᶜᵒ≼ₜₒᵥᵥₑᵣ ({[ (q, ∅) ]} : gset (Q * MO A)).
  Proof.
    rewrite <- eqx. rewrite alt_set_singleton_iff.
    eapply equivalence_acc_set_and_must_i.
  Qed.

  (** ---- *)

  (** ** The co-inductive-tower characterisation on toFW is equivalent to the extensional must preorder *)
  Corollary equivalence_co_inductive_acceptance_and_must_e_singleton (p : P) (q : Q) :
    pre_extensional outcome p q <-> ({[ (p, ∅) ]} : gset (P * MO A)) ᶜᵒ≼ₜₒᵥᵥₑᵣ ({[ (q, ∅) ]} : gset (Q * MO A)).
  Proof.
    rewrite pre_extensional_eq.
    rewrite <- eqx. rewrite alt_set_singleton_iff.
    eapply equivalence_acc_set_and_must_i.
  Qed.

  End Lⁿ.

End must_co_inductive_acceptance_preorder.

Lemma coin_refl
  `{@FiniteImagegLts P A H gLtsP}
  `{gLtsT : !gLtsEq T H} `{AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳P _ _ }
  {PRE : Chain copre_m} {p : P} : elem PRE {[ p ]} {[ p ]}.
Proof.
  apply (gfp_chain PRE).
  eapply eqx.
  eapply alt_set_singleton_iff.
  firstorder.
Qed.

Global Instance Proper_elem 
  `{@FiniteImagegLts P A H gLtsP}
  `{gLtsT : !gLtsEq T H} `{AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳P _ _ }
  {PRE : Chain copre_m} :
  Proper ((≡) ==> (=) ==> (iff)) (elem PRE).
Proof.
  intros ?? HX ?? <-.
  now rewrite (leibniz_equiv _ _ HX).
Qed.

Global Instance Proper_lts_stable `{gLtsEq P A}:
  Proper ((eq_rel) ==> (=) ==> (impl)) lts_refuses.
Proof.
  intros p p' Heq α α' ? Hs; subst α'.
  case (decide (lts_refuses p' α)); trivial. intro Hf.
  apply lts_refuses_spec1 in Hf as (q & Hq).
  destruct (eq_spec p q α) as (r & Hr & Heqr).
  - eexists; split; eauto.
  - contradict Hs. apply lts_refuses_spec2. eexists; eauto.
Qed.

(* In the case of a Lts with equivalence relation, the right hand side can also
  be rewritten *)
(* Global Instance Proper_eq_rel 
  `{gLtsP : @gLtsEq P A H}
  `{!FiniteImagegLts P A} 
  `{gLtsT : !gLtsEq T H} `{AbsPT : !@AbsAction P T FinA PreAct A H Φ 𝝳P _ _ } 
   {PRE : Chain copre_m}:
  Proper ((≡) ==> (eq_rel) ==> (impl)) (elem PRE).
Proof.
  intros ?? HX ?? Heq. rewrite (leibniz_equiv _ _ HX). clear x HX.
  revert x0 y0 Heq y.
  apply tower; clear PRE.
  - intros P' HP h x0 y0 y Heq R HR; simpl in *; eapply HP; eauto. now apply Heq.
  - intros Hc Heq x0 y0 Hequiv y h. constructor.
    + intros q Hq.
      destruct (eq_spec x0 q τ) as (r & Hr & Heqr).
      * exists y0. split; trivial.
      * eapply Heq; eauto. now apply h.
    + intros hp hq. apply h.(c_now_) in hp as (p & p' & Hin & Hpp' & Hs' & Hinc).
      * exists p; exists p'. now setoid_rewrite <- Hequiv.
      * now setoid_rewrite Hequiv.
    + intros μ q' ps' Hcnv Hq' Hwts.
      destruct (eq_spec x0 q' (ActExt μ)) as (r & Hr & Heqr).
      * exists y0. split; trivial.
      * eapply Heq; eauto. eapply h.(c_step_) with μ; eauto.
    + intro ht. eapply terminate_preserved_by_eq2; eauto. now apply h.(c_cnv_).
Qed. *)

Lemma coin_union_l `{@FiniteImagegLts P A H gLtsP}
  `{gLtsT : !gLtsEq T H}
  `{AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳P _ _ }
  {PRE : Chain copre_m}
  : forall (X1 X2 : gset P) (Y : gset P), elem PRE X1 Y -> elem PRE (X1 ∪ X2) Y.
Proof.
  apply tower; clear PRE.
  - intros P' HP ??????; eapply HP; eauto.
  - intros PRE CIH X1 X2 q h.
    unfold copre_m, body.
    constructor.
    + intros q' hqq'; now apply CIH, h.(c_tau_).
    + intros hp q' mem hq.
      assert (hp_ : X1 ⤓).
      { eapply termination_set_for_all. intros ??. 
        eapply termination_if_termination_set_helper in hp;eauto.
        now eapply elem_of_union_l. }
      destruct (h.(c_now_) hp_ q' mem hq) as ( p & mem' & p' & pi & hpp' & out ).
      exists p. split. 
      * now eapply elem_of_union_l.
      * exists p'; split; eauto.
    + intros μ q' ps' hp hqq' hps'.
      assert (forall p, p ∈ X1 ∪ X2 -> p ⇓ [μ]) as hp'.
      { intros; eapply convergence_forall_if_convergence_set; eauto. }
      destruct (wt_set_union _ _ _ hp' hps') as (ps1 & ps2 & h1 & h2 & eq).
      rewrite eq. apply CIH.
      eapply h.(c_step_); [ | exact hqq' | exact h1 ].
      eapply convergence_set_if_convergence_forall.
      intros p i. eapply convergence_forall_if_convergence_set in hp;eauto. 
      now eapply elem_of_union_l.
    + intros hp.
      apply h.(c_cnv_). eapply termination_set_for_all.
      intros p i. eapply termination_if_termination_set_helper in hp; eauto.
      now eapply elem_of_union_l.
Qed.

Lemma coin_union_r `{@FiniteImagegLts P A H gLtsP}
  `{gLtsT : !gLtsEq T H}
  `{AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳P _ _ }
  {PRE : Chain copre_m}
  : forall (X1 X2 : gset P) (Y : gset P), elem PRE X2 Y -> elem PRE (X1 ∪ X2) Y.
Proof.
  apply tower; clear PRE.
  - intros P' HP ??????; eapply HP; eauto.
  - intros PRE CIH X1 X2 q h.
    unfold copre_m, body.
    constructor.
    + intros q' hqq'; now apply CIH, h.(c_tau_).
    + intros hp q' mem hq.
      assert (hp_ : X2 ⤓).
      { eapply termination_set_for_all. intros ??. 
        eapply termination_if_termination_set_helper in hp;eauto.
        now eapply elem_of_union_r. }
      destruct (h.(c_now_) hp_ q' mem hq) as (p & mem' & p' & pi & hpp' & out).
      exists p. split.
      * now apply elem_of_union_r.
      * exists p'. repeat split; eauto.
    + intros μ q' ps' hp hqq' hps'.
      assert (forall p, p ∈ X1 ∪ X2 -> p ⇓ [μ]) as hp'.
      { intros; eapply convergence_forall_if_convergence_set; eauto. }
      destruct (wt_set_union _ _ _ hp' hps') as (ps1 & ps2 & h1 & h2 & eq).
      rewrite eq. apply CIH.
      eapply h.(c_step_); [ | exact hqq' | exact h2 ].
      eapply convergence_set_if_convergence_forall.
      intros p i. eapply convergence_forall_if_convergence_set in hp;eauto.
      now eapply elem_of_union_r.
    + intros hp.
      apply h.(c_cnv_). eapply termination_set_for_all.
      intros p i. eapply termination_if_termination_set_helper in hp; eauto.
      now eapply elem_of_union_r.
Qed.

Lemma coin_elem_of `{@FiniteImagegLts P A H gLtsP}
  `{gLtsT : !gLtsEq T H}
  `{AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳P _ _ }
  {PRE : Chain copre_m} (p : P) X: p ∈ X -> elem PRE X {[p]}.
Proof.
  intro Hin. setoid_rewrite (union_difference_singleton_L p X Hin).
  apply coin_union_l, coin_refl.
Qed.

Lemma coin_choose `{@FiniteImagegLts P A H gLtsP}
  `{gLtsT : !gLtsEq T H}
  `{AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳P _ _ }
  {PRE : Chain copre_m}
  : forall {X : gset P} {Y : gset P} {p : P}, p ∈ X -> elem PRE {[p]} Y -> elem PRE X Y.
Proof.
  intros X q p Hin He.
  setoid_replace X with ({[p]} ∪ (X ∖ {[p]})) by now apply union_difference_singleton.
  now apply coin_union_l.
Qed.

Lemma copre_fw_inv_l `{@FiniteImagegLts P A H gLtsP}
  `{gLtsT : !gLtsEq T H}
  `{AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳P _ _ }
  `{@Prop_of_Inter P (MO A) A fw_inter H gLtsP MbgLts}
  {PRE : Chain (copre_m (P := P * MO A) (Q := P * MO A))} (p t: P):
  (∀ μ p', p ⟶{μ} p' <-> (p' = t /\ μ = τ)) ->
  forall M (X : gset (P * MO A)) (Y : gset (P * MO A)),
    elem PRE ({[t ▷ M]} ∪ {[p ▷ M]} ∪ X) Y
    -> elem PRE ({[p ▷ M]} ∪ X) Y.
Proof.
  intros Hinv; apply tower; clear PRE.
  - intros P' HP ??????; eapply HP; eauto.
  - intros PRE CIH M X Y Hq.
    assert (Hpt : (p ▷ M) ⟶ (t ▷ M)) by (apply ParLeft, Hinv; tauto).
    constructor.
    + intros q' Hq'.
      apply CIH, Hq, Hq'.
    + intros Ht (p' , m') mem' Hs.
      destruct Hq as [ _ Hq _ _].
      edestruct Hq as (p1 & Hin & p2 & Hcnv & Hs' & Hout).
      * eapply termination_set_for_all. intros p0 Hin. repeat rewrite elem_of_union in Hin.
        destruct Hin as [[Heqt | Heqp] | Hin].
        ++ apply elem_of_singleton_1 in Heqt. subst.
           apply terminate_preserved_by_lts_tau with (p ▷ M).
           -- eapply termination_if_termination_set_helper in Ht; eauto.
              set_tac.
           -- assumption.
        ++ apply elem_of_singleton_1 in Heqp. subst.
           eapply termination_if_termination_set_helper in Ht; eauto.
           set_tac.
        ++ eapply termination_if_termination_set_helper in Ht; eauto.
           set_tac.
      * exact mem'.
      * trivial.
      * repeat rewrite elem_of_union in Hin.
        destruct Hin as [[Heqt | Heqp] | Hin].
        ++ apply elem_of_singleton_1 in Heqt. subst.
           exists (p ▷ M). split.
           ** set_tac.
           ** exists p2. split; [ | split]. 
              -- apply wt_tau with (t ▷ M); assumption.
              -- apply Hs'.
              -- eapply Hout.
        ++ apply elem_of_singleton_1 in Heqp. subst.
           exists (p ▷ M). split.
           ** set_tac.
           ** exists p2. split; [ | split].
              -- exact Hcnv.
              -- exact Hs'.
              -- exact Hout.
        ++ exists p1. split.
           ** set_tac.
           ** exists p2; intuition.
    + intros μ qs' ps' Hμ1 Hμ2 Hwt. eapply Hq; [| eassumption |].
      * eapply convergence_set_if_convergence_forall. intros p0 Hin.
        repeat rewrite elem_of_union in Hin.
        destruct Hin as [[Heqt | Heqp] | Hin].
        ++ apply elem_of_singleton_1 in Heqt. subst.
           apply cnv_preserved_by_lts_tau with (p ▷ M).
           -- eapply convergence_forall_if_convergence_set in Hμ1;eauto.
              set_tac.
           -- assumption.
        ++ apply elem_of_singleton_1 in Heqp. subst.
           eapply convergence_forall_if_convergence_set in Hμ1;eauto.
           set_tac.
        ++ eapply convergence_forall_if_convergence_set in Hμ1;eauto.
           set_tac.
      * destruct Hwt as [Hwt1 Hwt2].
        split.
        ++ intros p' Hp'. destruct (Hwt1 p' Hp') as [p0 [Hin Hp0]].
           repeat rewrite elem_of_union in Hin. destruct Hin as [Heqt | Hin].
           -- apply elem_of_singleton_1 in Heqt. subst.
              exists (p ▷ M). split; [set_tac|assumption].
           -- exists p0. split; [set_tac|assumption].
        ++ intros p' p'' Hin Hμ.
           repeat rewrite elem_of_union in Hin.
           destruct Hin as [[Heqt | Heqp] | Hin].
           -- apply elem_of_singleton_1 in Heqt. subst.
              eapply Hwt2 with (p ▷ M); [set_tac|].
              apply wt_tau with (t ▷ M); assumption.
           -- apply elem_of_singleton_1 in Heqp. subst.
              eapply Hwt2 with (p ▷ M); [set_tac|assumption].
           -- eapply Hwt2 with p'; [set_tac|]. apply Hμ.
    + intros Ht. apply Hq. eapply termination_set_for_all. intros p0 Hin.
      repeat rewrite elem_of_union in Hin. destruct Hin as [[Heqt | Heqp] | Hin].
      * apply elem_of_singleton_1 in Heqt. subst.
        apply terminate_preserved_by_lts_tau with (p ▷ M).
        ++ eapply termination_if_termination_set_helper in Ht;eauto. set_tac.
        ++ now apply Hpt.
      * apply elem_of_singleton_1 in Heqp. subst.
        eapply termination_if_termination_set_helper in Ht;eauto. set_tac.
      * eapply termination_if_termination_set_helper in Ht;eauto. set_tac.
Qed.

Lemma copre_inv_l `{@FiniteImagegLts P A H gLtsP}
  `{gLtsT : !gLtsEq T H}
  `{AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳P _ _ }
  {PRE : Chain copre_m} (p : P) X t Y : (p ⟶ t) -> (forall μ p', p ⟹{μ} p' <-> t ⟹{μ} p') ->
  elem PRE ({[t]} ∪ X) Y -> elem PRE ({[p]} ∪ X) Y.
Proof.
  intros Hpt Hinv; revert Y.
  apply tower; clear PRE.
  - intros P' HP ????; eapply HP; eauto.
  - intros PRE CIH Y h.
    constructor.
    + intros Y' HY'.
      now apply CIH, h.(c_tau_).
    + intros Ht p'' mem'' Hs.
      edestruct h.(c_now_) as [ p1 [ hp [ p' [ hpp' [ hp' ho ] ] ] ]]; eauto.
      * eapply termination_set_for_all. intros p0 Hin.
        apply elem_of_union in Hin; destruct Hin as [Heqt | Hin].
        -- apply elem_of_singleton_1 in Heqt; subst.
           apply terminate_preserved_by_lts_tau with p; eauto.
           eapply termination_if_termination_set_helper in Ht;eauto. set_tac.
        -- eapply termination_if_termination_set_helper in Ht;eauto. set_tac.
      * apply elem_of_union in hp; destruct hp as [Heqt | Hin]. 
        ++ exists p. split.
           -- set_tac.
           -- exists p'. apply elem_of_singleton_1 in Heqt; subst.
              split; [ | split]. 
              ** now apply wt_tau with t.
              ** exact hp'.
              ** exact ho.
        ++ exists p1 ; intuition.
           -- set_tac.
           -- exists p'. split; [ | split]. 
              ** exact hpp'.
              ** exact hp'.
              ** exact ho.
    + intros μ q' ps' hμ hqq' w.
      eapply h.(c_step_); eauto.
      * eapply convergence_set_if_convergence_forall.
        intros p0 hin; apply elem_of_union in hin; destruct hin as [Heqt | Hin].
        -- apply elem_of_singleton_1 in Heqt; subst.
           apply cnv_preserved_by_lts_tau with p; eauto.
           eapply convergence_forall_if_convergence_set in hμ. exact hμ.
           set_tac.
        -- eapply convergence_forall_if_convergence_set in hμ. exact hμ.
           set_tac.
      * destruct w as [Hwt1 Hwt2]; split.
        -- intros p' Hp'.
           destruct (Hwt1 p' Hp') as [p0 [Hin Hp0]].
           apply elem_of_union in Hin; destruct Hin as [Heqt | Hin].
           ++ apply elem_of_singleton_1 in Heqt; subst.
              exists t; split; [set_tac|now apply Hinv].
           ++ exists p0. split; [set_tac|assumption].
        -- intros p' p'' Hin Hμ.
           apply elem_of_union in Hin; destruct Hin as [Heqt | Hin].
           ++ apply elem_of_singleton_1 in Heqt; subst.
              eapply Hwt2 with p; [set_tac|]; apply Hinv, Hμ.
           ++ eapply Hwt2 with p'; [set_tac|]; apply Hμ.
    + intros Ht.
      apply h.(c_cnv_); eapply termination_set_for_all; intros p0 Hin.
      apply elem_of_union in Hin; destruct Hin as [Heqt | Hin].
      * apply elem_of_singleton_1 in Heqt; subst.
        apply terminate_preserved_by_lts_tau with p; eauto.
        eapply termination_if_termination_set_helper in Ht;eauto. set_tac.
      * eapply termination_if_termination_set_helper in Ht;eauto. set_tac.
Qed.

(* Global Instance copre_eq_rel_l `{@gLtsOba P A H gLtsEqP} `{!FiniteImagegLts P A}
  `{PreAP : @PreExtAction P A H FinA PreA PreA_eq PreA_countable 𝝳 Φ _}
  {PRE : Chain copre_m}: Proper ((eq_rel_set) ==> (=) ==> (impl)) (elem PRE).
Proof.
  intros X X' HXX' q q' ?; subst q'.
  revert X X' q HXX'. apply tower; clear PRE.
  - intros P' HP ???????; eapply HP; eauto.
  - intros PRE CIH X X' q hXX' h.
    constructor.
    + intros q' Hq'.
      now apply CIH with (X := X), h.(c_tau_).
    + intros Ht Hs.
      destruct h.(c_now_) as [ p1 [ p' [ hp [ hpp' [ hp' ho ] ] ] ]]; eauto.
      * intros p0 Hin. apply hXX' in Hin as (p' & Hin & Heqp').
        apply (terminate_preserved_by_eq2 (symmetry Heqp')). now apply Ht.
      * apply hXX' in hp as (p'' & Hin & Heqp'').
        apply eq_spec_wt with (p' := p'') in hpp' as (r & Hr & Heqr); trivial.
        exists p''; exists r; repeat split; trivial; now rewrite Heqr.
    + intros μ q' ps' hμ hqq' w.
      apply (wt_set_from_pset_spec_eq_rel_set (symmetry hXX')) in w
        as (X'' & Heqps' & HXps''); [|trivial].
      apply CIH with ps''; [now symmetry|].
      eapply h.(c_step_); eauto.
      intros p Hp. apply hXX' in Hp as (p'' & Hin & Heqp'').
      rewrite Heqp''; auto with *.
    + intros Ht.
      apply h.(c_cnv_); intros p0 Hin.
      apply hXX' in Hin as (p'' & Hin & Heqp'').
      eapply terminate_preserved_by_eq2; [apply symmetry, Heqp''|auto with *].
Qed. *)