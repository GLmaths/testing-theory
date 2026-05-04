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
  ActTau Subset_Act gLts FiniteImageLTS Lts_OBA Lts_Finite_Output_Chain Lts_OBA_FB
  Termination Convergence WeakTransitions Bisimulation
  SetLTSConstruction
  InteractionBetweenLts MultisetLTSConstruction ForwarderConstruction ParallelLTSConstruction
  Lift StateTransitionSystems
  Testing_Predicate Must MustE 
  DefinitionAS Soundness Equivalence Completeness.

(* TODO: define me using the coinduction library *)

Section copre.
  Context `{@FiniteImagegLts P A H gLtsP, @FiniteImagegLts Q A H gLtsQ}.
  Context `{gLtsT : !gLtsEq T H}.
  Context `{@AbsAction P T FinA PreAct A H Φ 𝝳P _ _ }.
  Context `{@AbsAction Q T FinA PreAct A H Φ 𝝳Q _ _ }.

  Definition REL := gset P -> gset Q -> Prop.

  Record copre_ (FIX : REL) (ps : gset P) (qs : gset Q) : Prop := {
    c_tau_ qs' : wt_set_from_pset_spec1 qs [] qs' -> FIX ps qs'
  ; c_now_ : ps ⤓ -> forall q , q ∈ qs -> q ↛ ->
            exists p, p ∈ ps /\ exists p', p ⟹ p' /\ p' ↛ /\ ⌈ (𝝳P ∘ Φ) ⌉ (coR p') ⊆ ⌈ (𝝳Q ∘ Φ) ⌉ (coR q)
  ; c_step_ : forall μ qs' ps', ps ⇓ [μ] ->
                         wt_set_from_pset_spec1 qs [μ] qs' -> wt_set_from_pset_spec ps [μ] ps' -> FIX ps' qs'
  ; c_cnv_ : ps ⤓ -> qs ⤓
  }.
  #[global] Arguments c_tau_ {FIX ps qs}.
  #[global] Arguments c_now_ {FIX ps qs}.
  #[global] Arguments c_step_ {FIX ps qs}.
  #[global] Arguments c_cnv_ {FIX ps qs}.

  Program Definition copre_m : mon REL := {| body := copre_ |} .
  Next Obligation.
    intros F1 F2 HF ps qs h; constructor.
    - intros; apply HF, h.(c_tau_); auto.
    - exact h.(c_now_).
    - intros; eapply HF, h.(c_step_); auto.
      + exact H4.
      + exact H5.
      + exact H6.
    - exact h.(c_cnv_).
  Qed.

  Definition copre := gfp copre_m .

  Notation "ps ⩽ qs" := (copre ps qs) (at level 70).

  Lemma c_tau {ps qs qs'} : ps ⩽ qs -> wt_set_from_pset_spec1 qs [] qs' -> ps ⩽ qs' .
  Proof.
    intros h%(gfp_pfp copre_m); intros; now apply h.(c_tau_).
  Qed.

  Lemma c_tau' {PRE : Chain copre_m} {ps qs qs'} :
    copre_m (elem PRE) ps qs -> wt_set_from_pset_spec1 qs [] qs' -> elem PRE ps qs' .
  Proof.
    intros h Ht. now apply h.(c_tau_). Qed.

  Lemma c_now {ps qs}
    : ps ⩽ qs
      -> ps ⤓
      -> forall q , q ∈ qs -> q ↛
      -> exists p, p ∈ ps
                /\ exists p', p ⟹ p'
                /\ p' ↛
                /\ ⌈ (𝝳P ∘ Φ) ⌉ (coR p') ⊆ ⌈ (𝝳Q ∘ Φ) ⌉ (coR q) .
  Proof.
    intros h%(gfp_pfp copre_m); intros; now apply h.(c_now_).
  Qed.

  Lemma c_step {ps ps' qs qs' μ}
    : ps ⩽ qs
      -> ps ⇓ [μ]
      -> wt_set_from_pset_spec1 qs [μ] qs'
      -> wt_set_from_pset_spec ps [μ] ps'
      -> ps' ⩽ qs' .
  Proof.
    intros h%(gfp_pfp copre_m); intros; now eapply h.(c_step_); eauto.
  Qed.

  Lemma c_cnv {ps qs}
    : ps ⩽ qs
      -> ps ⤓
      -> qs ⤓ .
  Proof.
    intros h%(gfp_pfp copre_m); intros; now eapply h.(c_cnv_); eauto.
  Qed.

  Lemma copre_if_prex (ps : gset P) (qs : gset Q) : ps ≼ₛₑₜ_ₐₛ qs -> ps ⩽ qs.
  Proof.
    revert ps qs; unfold copre.
    coinduction RR CIH.
    intros ps qs (hsub1 & hsub2).
    constructor.
    - intros qs' l.
      eapply CIH, bhvx_preserved_by_reductions; eauto. split; eauto.
    - intros hterm q mem hst.
      destruct (hsub2 q [] q mem) as (p' & hw & hstp' & hsub0); eauto.
      + eapply wt_nil.
      + intros p' mem'; constructor.
        eapply termination_if_termination_set_helper;eauto.
    - intros μ qs' ps' hcnv hw wtspec.
      eapply CIH, bhvx_preserved_by_external_action; eauto.
      + inversion hcnv;subst. eapply termination_if_termination_set_helper;eauto.
      + split;eauto.
    - intro Hyp_conv. eapply equiv_termination.
      eapply equiv_termination in Hyp_conv.
      eapply convergence_set_if_convergence_forall.
      eapply hsub1. eapply convergence_forall_if_convergence_set;eauto.
  Qed.

  Lemma co_preserved_by_wt_nil
    (ps : gset P) (qs qs' : gset Q) : wt_set_from_pset_spec1 qs [] qs' -> ps ⩽ qs -> ps ⩽ qs'.
  Proof.
    intros hw Hyp. eapply c_tau;eauto.
  Qed.


  Lemma prex1_if_copre (ps : gset P) (qs : gset Q) : ps ⩽ qs -> ps ₁≼ₛₑₜ_ₐₛ qs.
  Proof.
    intros hpq s; revert ps qs hpq.
    dependent induction s; intros ps qs hpq hcnv.
    + eapply convergence_set_if_convergence_forall in hcnv.
      eapply convergence_forall_if_convergence_set.
      eapply equiv_termination. eapply (c_cnv hpq).
      eapply equiv_termination. exact hcnv.
    + assert (qs ⤓).
      { eapply convergence_set_if_convergence_forall in hcnv. inversion hcnv; subst.
      eapply (c_cnv hpq). eauto. }
      assert (hcnv0 : ∀ p : P, p ∈ ps → p ⇓ [a]) by (intros; now eapply cnv_wk, hcnv).
      intros. eapply cnv_act; eauto. eapply termination_if_termination_set_helper;eauto.
      intros q' hw.
      eapply IHs.
      ++ eapply (c_step hpq); eauto.
         * eapply convergence_set_if_convergence_forall;eauto. 
         * intros q'' mem. exists q. split;eauto.
           instantiate (1:= {[ q' ]}) in mem.
           assert (q'' = q') by set_solver. subst. exact hw.
         * eapply (wt_s_set_from_pset_ispec ps [a] hcnv0); eauto.
      ++ intros p mem.
         edestruct (wt_s_set_from_pset_ispec ps [a] hcnv0) as (TrSet_hyp1 & TrSet_hyp2).
         eapply TrSet_hyp1 in mem as (p0 & hmem0%hcnv & hw0).
         inversion hmem0; subst. eauto.
      ++ set_solver.
  Qed.

  Lemma prex2_if_copre (ps : gset P) (qs : gset Q) : ps ⩽ qs -> ps ₂≼ₛₑₜ_ₐₛ qs.
  Proof.
    intros hsub q s q' mem; revert ps qs q q' mem hsub ; dependent induction s; intros ps qs q q' mem hsub.
    + intros hw hstq' hcnv. revert ps qs mem hsub hstq' hcnv.
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
      assert (ps ⩽ {[ q0' ]}).
      { eapply co_preserved_by_wt_nil; eauto. intros q'' mem''.
        assert (q'' = q0') by set_solver. subst. eauto. }
      assert (hcnv' : ∀ p : P, p ∈ ps → p ⇓ [μ]) by (intros; now eapply cnv_wk, hcnv).
      assert (∀ p : P, p ∈ ps → p ⇓ [μ]) as hp_conv;eauto.
      eapply convergence_set_if_convergence_forall in hp_conv.
      set (ps' := wt_s_set_from_pset ps [μ] hcnv').
      assert (ps' ⩽ {[ q1' ]}) as hpq''. {
        eapply c_step;eauto.
        + intros q''' mem'''. assert (q''' = q1') by set_solver. subst.
          exists q0'. split. set_solver. eapply lts_to_wt;eauto.
        + eapply wt_s_set_from_pset_ispec.
      }
      assert (ps' ⩽ {[ q0 ]}) as hp'q.
      { eapply co_preserved_by_wt_nil; eauto. intros q''' mem'''.
        assert (q''' = q0) by set_solver. subst. exists q1'. split;eauto. set_solver.
      }
      edestruct (IHs ps' ({[ q0 ]})) as (r & memr & p' & hwr & hst & hsub').
      * instantiate (1:= q0). set_solver.
      * eauto.
      * exact hw1.
      * exact hq.
      * intros p hp.
        edestruct (wt_s_set_from_pset_ispec ps [μ] hcnv') as (TrSet_hyp1 & TrSet_hyp2).
        eapply TrSet_hyp1 in hp as (p0 & hmem0 & hw0).
        eapply cnv_preserved_by_wt_act; eauto.
      * edestruct (wt_s_set_from_pset_ispec ps [μ] hcnv') as (TrSet_hyp1 & TrSet_hyp2).
        eapply TrSet_hyp1 in memr as (p0  & hmem0 & hw0).
        exists p0; split; [ auto | ].
        exists p'; split; [ | split; eauto ].
        eapply wt_push_left; eauto.
  Qed.


  Theorem eqx (X : gset P) (Y : gset Q) :
    X ≼ₛₑₜ_ₐₛ Y <-> X ⩽ Y.
  Proof.
    split; [ eapply copre_if_prex | ].
    intros hco; split; [ now eapply prex1_if_copre | now eapply prex2_if_copre ].
  Qed.
End copre.

Notation "X ⩽ Y" := (copre X Y) (at level 70).

Section eq_contextual.
  Context `{outcome : T -> Prop}.
  Context `{outcome_dec : forall t, Decision (outcome t)}.
  Context `{P : Type}.
  Context `{Q : Type}.
  Context `{H : !ExtAction A}.

  Context `{@gLtsOba P A H gLtsEqP, !FiniteImagegLts P A}.
  Context `{@gLtsOba Q A H gLtsEqQ, !FiniteImagegLts Q A}.
  Context `{@gLtsOba T A H gLtsEqT, !FiniteImagegLts T A, !Testing_Predicate outcome _}.

  Context `{!Prop_of_Inter P T A dual}.
  Context `{!Prop_of_Inter Q T A dual}.

  Context `{!Prop_of_Inter P (mb A) A fw_inter}.
  Context `{!Prop_of_Inter (P * mb A) T A dual}.
  Context `{!Prop_of_Inter Q (mb A) A fw_inter}.
  Context `{!Prop_of_Inter (Q * mb A) T A dual}.

  Context `{CC : Countable PreAct}.
  Context `{@FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 _ _ _ _ }.
  Context `{@FinitaryAbsAction Q T FinA PreAct A H Φ 𝝳 _ _ _ _ }.

  Context `{tc_spec : @test_convergence_spec T _ _ _ outcome _ t_conv}.
  Context `{ta_spec : @test_co_acceptance_set_spec PreAct _ _ T _ _ _ outcome Testing_Predicate0 ta (fun x => 𝝳 (Φ x))}.

  Context `{!gLtsObaFB P A, !FiniteOutputChain_LtsOba P}.
  Context `{!gLtsObaFB Q A, !FiniteOutputChain_LtsOba Q}.
  Context `{!gLtsObaFB T A, !FiniteOutputChain_LtsOba T}.

  (* Theorem eq_ctx (p : P) (q : Q) :
    pre_extensional outcome p q <-> ({[ p ▷ (∅ : mb A) ]} : gset (P * mb A)) ⩽ ({[ q ▷ (∅ : mb A) ]} : gset (Q * mb A)).
  Proof.
    rewrite <- eqx, <- alt_set_singleton_iff.
    now rewrite equivalence_bhv_acc_ctx.
  Qed. *)
End eq_contextual.

(*
Lemma coin_refl `{@FiniteImagegLts P A H gLtsP}
  `{CC : Countable PreAct}
  `{!@FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 _ _ _ _ }
  {PRE : Chain copre_m} {p : P} : elem PRE {[ p ]} p.
Proof.
  apply (gfp_chain PRE).
  eapply eqx.
  eapply alt_set_singleton_iff.
  firstorder.
Qed.

Global Instance Proper_elem `{@FiniteImagegLts P A H gLtsP}
  `{PreAP : @PreExtAction P A H FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP}
  {PRE : Chain copre_m} :
  Proper ((≡) ==> (=) ==> (iff)) (elem PRE).
Proof.
  intros ?? HX ?? <-.
  now rewrite (leibniz_equiv _ _ HX).
Qed.

Global Instance Proper_lts_pre_co_actions `{gLtsOba P A}
  `{PreAP : @PreExtAction P A H FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP}:
  Proper ((eq_rel) ==> (=)) pre_co_actions_of.
Proof.
  intros μ μ' Heq. apply leibniz_equiv.
  intros x. split.
  - intro Hyp. admit.
  - intro Hyp. admit.
Admitted.

Global Instance Proper_lts_stable `{gLtsOba P A}:
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
Global Instance Proper_eq_rel `{@gLtsOba P A H gLtsEqP} `{!FiniteImagegLts P A}
  `{PreAP : @PreExtAction P A H FinA PreA PreA_eq PreA_countable 𝝳 Φ _}
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
Qed.

Lemma coin_union_l `{@FiniteImagegLts P A H gLtsP}
  `{PreAP : @PreExtAction P A H FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP}
  {PRE : Chain copre_m}
  : forall (X1 X2 : gset P) (q : P), elem PRE X1 q -> elem PRE (X1 ∪ X2) q.
Proof.
  apply tower; clear PRE.
  - intros P' HP ??????; eapply HP; eauto.
  - intros PRE CIH X1 X2 q h.
    unfold copre_m, body.
    constructor.
    + intros q' hqq'; now apply CIH, h.(c_tau_).
    + intros hp hq.
      assert (hp_ : ∀ p : P, p ∈ X1 → p ⤓) by (intros ??; now apply hp, elem_of_union_l).
      destruct (h.(c_now_) hp_ hq) as [ p [ p' [ pi [ hpp' out ] ] ]].
      exists p, p'; split; eauto.
      now apply elem_of_union_l.
    + intros μ q' ps' hp hqq' hps'.
      destruct (wt_set_union _ _ _ hp hps') as [ ps1 [ ps2 [ h1 [ h2 -> ] ] ] ].
      apply CIH.
      eapply h.(c_step_); [ | exact hqq' | exact h1 ].
      intros p i; now apply hp, elem_of_union_l.
    + intros hp.
      apply h.(c_cnv_).
      intros p i; now apply hp, elem_of_union_l.
Qed.

Lemma coin_union_r `{@FiniteImagegLts P A H gLtsP}
  `{PreAP : @PreExtAction P A H FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP}
  {PRE : Chain copre_m}
  : forall (X1 X2 : gset P) (q : P), elem PRE X2 q -> elem PRE (X1 ∪ X2) q.
Proof.
  apply tower; clear PRE.
  - intros P' HP ??????; eapply HP; eauto.
  - intros PRE CIH X1 X2 q h.
    unfold copre_m, body.
    constructor.
    + intros q' hqq'; now apply CIH, h.(c_tau_).
    + intros hp hq.
      assert (hp_ : ∀ p : P, p ∈ X2 → p ⤓) by (intros ??; now apply hp, elem_of_union_r).
      destruct (h.(c_now_) hp_ hq) as [ p [ p' [ pi [ hpp' out ] ] ]].
      exists p, p'; split; eauto.
      now apply elem_of_union_r.
    + intros μ q' ps' hp hqq' hps'.
      destruct (wt_set_union _ _ _ hp hps') as [ ps1 [ ps2 [ h1 [ h2 -> ] ] ] ].
      apply CIH.
      eapply h.(c_step_); [ | exact hqq' | exact h2 ].
      intros p i; now apply hp, elem_of_union_r.
    + intros hp.
      apply h.(c_cnv_).
      intros p i; now apply hp, elem_of_union_r.
Qed.

Lemma coin_elem_of `{@FiniteImagegLts P A H gLtsP}
  `{PreAP : @PreExtAction P A H FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP}
  {PRE : Chain copre_m} (p : P) X: p ∈ X -> elem PRE X p.
Proof.
intro Hin. setoid_rewrite (union_difference_singleton_L p X Hin).
apply coin_union_l, coin_refl.
Qed.

Lemma coin_choose `{@FiniteImagegLts P A H gLtsP}
  `{PreAP : @PreExtAction P A H FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP}
  {PRE : Chain copre_m}
  : forall {X : gset P} {q : P} {p : P}, p ∈ X -> elem PRE {[p]} q -> elem PRE X q.
Proof.
  intros X q p Hin He.
  setoid_replace X with ({[p]} ∪ (X ∖ {[p]})) by now apply union_difference_singleton.
  now apply coin_union_l.
Qed.

Lemma copre_fw_inv_l `{@FiniteImagegLts P A H gLtsP}
  `{PreAP : @PreExtAction P A H FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP}
  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}
  {PRE : Chain (copre_m (P := P * mb A) (Q := P * mb A))} (p t: P):
  (∀ μ p', p ⟶{μ} p' <-> (p' = t /\ μ = τ)) ->
  forall M (X : gset (P * mb A)) (q : P * mb A),
    elem PRE ({[t ▷ M]} ∪ {[p ▷ M]} ∪ X) q
    -> elem PRE ({[p ▷ M]} ∪ X) q.
Proof.
  intros Hinv; apply tower; clear PRE.
  - intros P' HP ??????; eapply HP; eauto.
  - intros PRE CIH M X q Hq.
    assert (Hpt : (p ▷ M) ⟶ (t ▷ M)) by (apply ParLeft, Hinv; tauto).
    constructor.
    + intros q' Hq'.
      apply CIH, Hq, Hq'.
    + intros Ht Hs.
      destruct Hq as [ _ Hq _ _].
      destruct Hq as (p1 & p2 & Hin & Hcnv & Hs' & Hout).
      * intros p0 Hin. repeat rewrite elem_of_union in Hin.
        destruct Hin as [[Heqt | Heqp] | Hin].
        ++ apply elem_of_singleton_1 in Heqt. subst.
           apply terminate_preserved_by_lts_tau with (p ▷ M).
           -- apply Ht. set_tac.
           -- assumption.
        ++ apply elem_of_singleton_1 in Heqp. subst.
           apply Ht. set_tac.
        ++ apply Ht. set_tac.
      * trivial.
      * repeat rewrite elem_of_union in Hin.
        destruct Hin as [[Heqt | Heqp] | Hin].
        ++ apply elem_of_singleton_1 in Heqt. subst.
           exists (p ▷ M). exists p2. split; [ | split;[ | split ] ].
           -- set_tac.
           -- apply wt_tau with (t ▷ M); assumption.
           -- apply Hs'.
           -- eapply Hout.
        ++ apply elem_of_singleton_1 in Heqp. subst.
           exists (p ▷ M). exists p2. split; [ | split;[ | split ] ].
           -- set_tac.
           -- exact Hcnv.
           -- exact Hs'.
           -- exact Hout.
        ++ exists p1. exists p2; intuition.
           apply elem_of_union_r. set_tac.
    + intros μ q' ps' Hμ1 Hμ2 Hwt. eapply Hq; [| eassumption |].
      * intros p0 Hin. repeat rewrite elem_of_union in Hin.
        destruct Hin as [[Heqt | Heqp] | Hin].
        ++ apply elem_of_singleton_1 in Heqt. subst.
           apply cnv_preserved_by_lts_tau with (p ▷ M).
           -- apply Hμ1. set_tac.
           -- assumption.
        ++ apply elem_of_singleton_1 in Heqp. subst. apply Hμ1. set_tac.
        ++ apply Hμ1. set_tac.
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
    + intros Ht. apply Hq. intros p0 Hin.
      repeat rewrite elem_of_union in Hin. destruct Hin as [[Heqt | Heqp] | Hin].
      * apply elem_of_singleton_1 in Heqt. subst.
        apply terminate_preserved_by_lts_tau with (p ▷ M).
        ++ apply Ht. set_tac.
        ++ now apply Hpt.
      * apply elem_of_singleton_1 in Heqp. subst.
        apply Ht. set_tac.
      * apply Ht. set_tac.
Qed.

Lemma copre_inv_l `{@FiniteImagegLts P A H gLtsP}
  `{PreAP : @PreExtAction P A H FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP}
  {PRE : Chain copre_m} (p : P) X t q : (p ⟶ t) -> (forall μ p', p ⟹{μ} p' <-> t ⟹{μ} p') ->
  elem PRE ({[t]} ∪ X) q -> elem PRE ({[p]} ∪ X) q.
Proof.
  intros Hpt Hinv; revert q.
  apply tower; clear PRE.
  - intros P' HP ????; eapply HP; eauto.
  - intros PRE CIH q h.
    constructor.
    + intros q' Hq'.
      now apply CIH, h.(c_tau_).
    + intros Ht Hs.
      destruct h.(c_now_) as [ p1 [ p' [ hp [ hpp' [ hp' ho ] ] ] ]]; eauto.
      * intros p0 Hin.
        apply elem_of_union in Hin; destruct Hin as [Heqt | Hin].
        -- apply elem_of_singleton_1 in Heqt; subst.
           apply terminate_preserved_by_lts_tau with p; eauto.
           apply Ht; set_tac.
        -- apply Ht; set_tac.
      * apply elem_of_union in hp; destruct hp as [Heqt | Hin].
        -- apply elem_of_singleton_1 in Heqt; subst.
           exists p, p'; repeat split; [ set_tac | | | ]; trivial.
           now apply wt_tau with t.
        -- exists p1, p'; intuition.
           now apply elem_of_union_r.
    + intros μ q' ps' hμ hqq' w.
      eapply h.(c_step_); eauto.
      * intros p0 hin; apply elem_of_union in hin; destruct hin as [Heqt | Hin].
        -- apply elem_of_singleton_1 in Heqt; subst.
           apply cnv_preserved_by_lts_tau with p; eauto.
           apply hμ; set_tac.
        -- apply hμ; set_tac.
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
      apply h.(c_cnv_); intros p0 Hin.
      apply elem_of_union in Hin; destruct Hin as [Heqt | Hin].
      * apply elem_of_singleton_1 in Heqt; subst.
        apply terminate_preserved_by_lts_tau with p; eauto.
        apply Ht; set_tac.
      * apply Ht; set_tac.
Qed.

Global Instance copre_eq_rel_l `{@gLtsOba P A H gLtsEqP} `{!FiniteImagegLts P A}
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
        as (ps'' & Heqps' & HXps''); [|trivial].
      apply CIH with ps''; [now symmetry|].
      eapply h.(c_step_); eauto.
      intros p Hp. apply hXX' in Hp as (p'' & Hin & Heqp'').
      rewrite Heqp''; auto with *.
    + intros Ht.
      apply h.(c_cnv_); intros p0 Hin.
      apply hXX' in Hin as (p'' & Hin & Heqp'').
      eapply terminate_preserved_by_eq2; [apply symmetry, Heqp''|auto with *].
Qed.
*)