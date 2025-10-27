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
    InteractionBetweenLts MultisetLTSConstruction ForwarderConstruction ParallelLTSConstruction ActTau
    Testing_Predicate DefinitionAS DefinitionMS MustE EquivalenceAS.

Section must_set_acc_set.
  Context `{P : Type}.
  Context `{Q : Type}.
  Context `{A : Type}.
  Context `{H : !ExtAction A}.
  Context `{gLtsP : !gLts P A, !FiniteImagegLts P A}.
  Context `{gLtsQ : !gLts Q A, !FiniteImagegLts Q A}.

  Context `{@gLtsObaFB P A H gLtsP gLtsEqP gLtsObaP}.
  Context `{@gLtsObaFB Q A H gLtsQ gLtsEqQ gLtsObaQ}.

  Context `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}.
  Context `{@Prop_of_Inter Q (mb A) A fw_inter H gLtsQ MbgLts}.

(*   Definition actions_acc 
  (p : P * mb A) s (h : p ⇓ s) : gset PreA := oas p s h. *)

  (* ************************************************** *)

  Lemma either_wperform_mu 
  (p : P * mb A) μ :
    p ⤓ -> (exists q, p ⟹{μ} q) \/ ~ (exists q, p ⟹{μ} q).
  Proof.
    intro ht. induction ht.
    destruct (lts_refuses_decidable p (ActExt μ)).
    - assert (∀ x, x ∈ enum (dsig (lts_step p τ)) -> (∃ q0, `x ⟹{μ} q0) \/ ~ (∃ q0, `x ⟹{μ} q0))
         as Hyp
        by (intros (x & mem) _; set_solver).
      edestruct (exists_forall_in _ _ _ Hyp) as [Hyp' | Hyp'].
      + eapply Exists_exists in Hyp' as ((q' & pr) & mem & (q0 & hw)).
        left. exists q0. eapply wt_tau; eauto. now eapply bool_decide_unpack.
      + right. intros (q' & hw). inversion hw; subst.
        ++ contradict Hyp'. intros n. rewrite Forall_forall in n.
           eapply (n (dexist q l0)). eapply elem_of_enum. eauto.
        ++ eapply (@lts_refuses_spec2 (P * mb A)); eauto.
    - left. eapply lts_refuses_spec1 in n as (q & l). eauto with mdb.
  Qed.

  Lemma either_wperform_mem (p : P * mb A) (G : gset A) (ht : p ⤓) :
    (exists μ p', μ ∈ G /\ p ⟹{μ} p') 
      \/ (forall μ p', μ ∈ G -> ~ p ⟹{μ} p').
  Proof.
    induction G using set_ind_L; [|destruct IHG, (either_wperform_mu p x)]; set_solver.
  Qed.

  Lemma either_wperform_mem_set
    (ps : gset (P * mb A)) (G : gset A) (ht : forall p, p ∈ ps -> p ⤓) :
    (exists p', p' ∈ ps /\ forall μ p0, μ ∈ G
      -> ~ p' ⟹{μ} p0) 
      \/ (forall p', p' ∈ ps -> exists μ p0, μ ∈ G /\ p' ⟹{μ} p0).
  Proof.
    induction ps using set_ind_L. 
    + set_solver. 
    + destruct IHps, (@either_wperform_mem x G); set_solver.
  Qed.

  Lemma either_MUST
      (p : P * mb A) (G : gset A) (hcnv : p ⇓ []) :
      p MUST G \/ ~ p MUST G.
  Proof.
    assert (∀ p0 : P * mb A, p0 ∈ wt_set p [] hcnv → p0 ⤓) as pre_Hyp.
    intros p0 mem0%wt_set_spec1. eapply cnv_terminate, cnv_preserved_by_wt_nil; eauto.
    destruct (either_wperform_mem_set (wt_set p [] hcnv) G) 
      as [Hyp|]; eauto.
    - right. intro hm. destruct Hyp as (p' & mem%wt_set_spec1%hm & nhw). set_solver.
    - left. intros p1 hw%(wt_set_spec2 _ p1 [] hcnv). set_solver.
  Qed.

  Lemma either_ex_nMUST_or_MUST
    (ps : gset (P * mb A)) (G : gset A)
      (ht : forall p, p ∈ ps -> p ⇓ []) :
    (exists p, p ∈ ps /\ ~ p MUST G) 
      \/ (forall p, p ∈ ps -> p MUST G).
  Proof.
    induction ps using set_ind_L; [|edestruct IHps, (either_MUST x G)]; set_solver.
  Qed.

  Lemma either_MUST__s
    (ps : gset (P * mb A)) (G : gset A)  :
    (forall p, p ∈ ps -> p ⇓ []) -> MUST__s ps G \/ ~ MUST__s ps G.
  Proof.
    intros. edestruct (either_ex_nMUST_or_MUST ps G) as [Hyp |]; eauto.
    right. intros hm. destruct Hyp as (p0 & mem0%hm & hnm). contradiction.
  Qed.

  Lemma nMusts_ex
    (ps : gset (P * mb A)) (G : gset A) :
    (forall p, p ∈ ps -> p ⇓ []) -> ~ MUST__s ps G 
    -> exists p, p ∈ ps /\ ~ p MUST G.
  Proof. intros. edestruct (either_ex_nMUST_or_MUST ps G); set_solver. Qed.

  Lemma nMust_ex
    (p : P * mb A) (G : gset A) (hcnv : p ⇓ []) 
    (hnm : ~ p MUST G) :
    exists p', p ⟹ p' /\ forall μ p0, μ ∈ G -> ~ p' ⟹{μ} p0.
  Proof.
    assert (∀ p0 : P * mb A, p0 ∈ wt_set p [] hcnv → p0 ⤓).
    intros p0 mem0%wt_set_spec1. eapply cnv_terminate, cnv_preserved_by_wt_nil; eauto.
    destruct (either_wperform_mem_set (wt_set p [] hcnv) G) as [Hyp|Hyp]; eauto.
    - destruct Hyp as (p' & mem'%wt_set_spec1 & nhw). set_solver.
    - edestruct hnm. intros p' mem. eapply Hyp. eapply wt_set_spec2; eauto.
  Qed.

  Lemma nMusts_nMust
  (p : P * mb A) (G : gset A) (hcnv : p ⇓ []) 
  (hnm : ~ MUST__s (wt_set p [] hcnv) G) : 
  ¬ p MUST G.
  Proof.
    intro hm. eapply hnm. intros p' mem0%wt_set_spec1.
    intros r hw. eapply hm. eapply wt_push_nil_left; eassumption.
  Qed.

(*   Lemma nMust_out_acc_ex 

    (p : P * mb A) pt G s hcnv :

    pt ∈ AFTER p s hcnv 
    -> ~ MUST pt (union_of_actions_without ((elements (wt_refuses_set p s hcnv)) , q')) ->
    exists p', pt ⟹ p' /\ p' ↛ /\ lts_acc_set_of p' ⊆ lts_acc_set_of q'.
  Proof.
    intros mem%wt_set_spec1 hnm.
    eapply nMust_ex in hnm as (p' & hw' & nhw).
    assert (ht': p' ⤓)
      by (eapply (cnv_wt_s_terminate p p' s hcnv), wt_push_nil_right; eauto).
    eapply terminate_then_wt_refuses in ht' as (p0 & hw0 & hst).
    exists p0. split. eapply wt_push_nil_left; eauto.
    split; eauto.
    intros μ mem_mu.
    assert (mem0 : μ ∈ actions_acc p s hcnv).
    eapply elem_of_union_list. eexists. split; eauto.
    eapply elem_of_list_fmap.
    exists p0. repeat split; eauto.
    eapply elem_of_elements, wt_refuses_set_spec2; split; eauto.
    eapply wt_push_nil_right, wt_push_nil_right; eauto.
    eapply lts_refuses_spec1 in mem_mu as (p'0 & HypTr).
    { destruct (decide (μ ∈ lts_acc_set_of q')).
      + eauto.
      + exfalso.
        eapply (nhw $ μ); eauto. unfold actions_acc in mem0.
        unfold oas in mem0. set_solver.
        eapply wt_push_nil_left; eauto with mdb. }
    constructor; eapply (cnv_wt_s_terminate p pt s hcnv); eauto.
  Qed. *)

(*   Lemma either_MUST_or_ex 
    (p : P * mb A) (q' : Q * mb A)  s hcnv :
    MUST__s (AFTER p s hcnv) (union_of_actions_without ((elements (wt_refuses_set p s hcnv)) , q'))
    \/ (exists p', p ⟹[s] p' /\ p' ↛ /\ lts_acc_set_of p' ⊆ lts_acc_set_of q').
  Proof.
    assert (h1 : forall p0, p0 ∈ AFTER p s hcnv → p0 ⇓ []).
    intros p0 mem0. eapply cnv_nil, cnv_wt_s_terminate; eauto.
    eapply (wt_set_spec1 _ _ _ _ mem0).
    destruct (either_MUST__s (AFTER p s hcnv) ((elements (wt_refuses_set p s hcnv)) , q')) 
        as [ |Hyp].
    + eauto.
    + left. eauto.
    + right.
      eapply nMusts_ex in Hyp as (pt & mem & hnm); eauto.
      eapply nMust_out_acc_ex in hnm as (pt' & hw & hst & hsub); eauto.
      exists pt'. split; eauto. eapply wt_push_nil_right; eauto. now eapply wt_set_spec1 in mem.
  Qed. *)

(*   Lemma Must_out_acc_npre 
    (p : P * mb A) (q q' : Q * mb A) s hcnv :
    q ⇓ s -> q ⟹[s] q' -> q' ↛ ->
    MUST__s (AFTER p s hcnv) (actions_acc p s hcnv ∖ lts_acc_set_of q') ->
    ~ p ≾₂ q.
  Proof.
    intros hcnv' hw hst hm pre2.
    set (G := actions_acc p s hcnv ∖ lts_acc_set_of q').
    assert (exists μ t, μ ∈ G /\ q' ⟹{μ} t) as (μ & t & mem & hw').
    eapply (pre2 s hcnv hcnv'); eauto. eapply wt_set_spec2; eauto. eapply wt_nil.
    eapply elem_of_difference in mem as (mem & nmem).
    (* assert (exists p', p' ⟶[ μ ]).
    assert (is_output μ) as (a & heq). *)
    eapply elem_of_union_list in mem as (X & mem1 & mem2).
    eapply elem_of_list_fmap in mem1 as (r & heq & mem1). subst.
    (* eapply elem_of_map in mem2 as (a & heq & mem2). exists a. assumption. *)
    assert { r' | r ⟶[ μ ] r'} as (r' & HypTr). eapply lts_refuses_spec1. eauto.
    inversion hw'; subst.
    eapply lts_refuses_spec2 in hst; eauto.
    eapply nmem. eapply lts_refuses_spec2. eauto.
  Qed. *)

  (* ************************************************** *)

  Context `{@PreExtAction A H (P * mb A) FinA PreA PreA_eq PreA_countable 𝝳 Φ (FW_gLts gLtsP)}.
  Context `{@PreExtAction A H (Q * mb A) FinA PreA PreA_eq PreA_countable 𝝳 Φ (FW_gLts gLtsQ)}.

  Lemma equivalence_bhv_acc_mst2
    (p : P) (q : Q) :
    (p, ∅) ≼₁ (q, ∅) -> (p, ∅) ≾₂ (q, ∅) <-> (p, ∅) ≼₂ (q, ∅).
  Proof.
    intro hpre1.
    split.
    - intro hpre2. intros s q' hcnv hw hst.
      (* edestruct (either_MUST_or_ex (p, ∅) q' s hcnv).
      + exfalso. eapply Must_out_acc_npre; eauto with mdb.
      + set_solver. *) admit.
    - intro hpre2.
      intros s hcnv hcnv' G hm q' mem%wt_set_spec1 q0 hw.
      assert (exists r, q0 ⟹ r /\ r ↛) as (qt & hw' & hstq').
      { eapply terminate_then_wt_refuses, terminate_preserved_by_wt_nil; eauto.
        eapply cnv_wt_s_terminate; eauto. }
      edestruct (hpre2 s qt hcnv) as (pt & hwpt & hstpt & hsubpt); eauto.
      eapply wt_push_nil_right; eauto. eapply wt_push_nil_right; eauto.
      assert (exists μ r, μ ∈ G /\ pt ⟹{μ} r) as (μ & p0 & mem0 & hw0).
      { eapply hm. eapply wt_set_spec2; eauto. eapply wt_nil. }
      exists μ. inversion hw0; subst.
      + exfalso. eapply lts_refuses_spec2 in hstpt; eauto.
      + assert (𝝳 (Φ μ) ∈ pre_co_actions_of qt).
        { eapply hsubpt. eapply preactions_of_spec. eapply preactions_of_fin_test_spec1.
          admit. }
        (* exists qr. split; eauto. eapply wt_push_nil_left; eauto with mdb. *)
        admit.
  Admitted.

  Theorem equivalence_bhv_acc_mst
  (p : P) (q : Q) :
  (p, ∅) ≾ₘᵤₛₜ (q, ∅) <-> (p, ∅) ≼ₐₛ (q, ∅).
  Proof.
    split; intros (pre1 & pre2); split; eauto; now eapply equivalence_bhv_acc_mst2.
  Qed.

  Context `{attaboy : E -> Prop}.
  Context `{attaboy_dec : forall e, Decision (attaboy e)}.
  Context `{gLtsE : !gLts E A, !FiniteImagegLts E A, gLtsEqE: !gLtsEq E A, !Testing_Predicate E A attaboy}.
  Context `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}.
  Context `{@Prop_of_Inter Q E A parallel_inter H gLtsQ gLtsE}.

  Context `{@gLtsObaFB E A H gLtsE gLtsEqE gLtsObaE}.

  Context `{@Prop_of_Inter (P * mb A) E A parallel_inter H (inter_lts fw_inter) gLtsE}.
  Context `{@Prop_of_Inter (Q * mb A) E A parallel_inter H (inter_lts fw_inter) gLtsE}.

  Context `{@PreExtAction A H (P * mb A) FinA PreA PreA_eq PreA_countable 𝝳 Φ (FW_gLts gLtsP)}.
  Context `{@PreExtAction A H (Q * mb A) FinA PreA PreA_eq PreA_countable 𝝳 Φ (FW_gLts gLtsQ)}.
  Context `{@AbsAction A H E FinA gLtsE Φ}.

  Context `{igen_conv : @gen_spec_conv E _ _ _ _ attaboy Testing_Predicate0 co_of gen_conv}.
  Context `{igen_acc : @gen_spec_acc PreA _ _ E _ _ _ _ attaboy Testing_Predicate0 co_of gen_acc (fun x => 𝝳 (Φ x))}.

  Corollary equivalence_bhv_mst_ctx
    (p : P) (q : Q) : (p, ∅) ≾ₘᵤₛₜ (q, ∅) <-> @pre_extensional P Q _ _ _ attaboy _ p q.
  Proof.
    erewrite pre_extensional_eq.
    rewrite equivalence_bhv_acc_mst.
    rewrite <- equivalence_bhv_acc_ctx.
    eapply pre_extensional_eq.
  Qed.


End must_set_acc_set.
