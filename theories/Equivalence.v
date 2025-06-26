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

From stdpp Require Import base decidable gmap.
Require Import ssreflect.
Require Import Coq.Program.Equality.

From stdpp Require Import finite.
From Must Require Import TransitionSystems Must Bar Completeness Soundness Lift Subset_Act.

(** Extensional definition of Convergence and its equivalence
    with the inductive definition. *)

Section convergence.
  (* set of processes *)
  Context `{P : Type}.
  (* set of external actions *)
  Context `{A : Type}.
  
  Context `{H : !ExtAction A}.
  Context `{!Lts P A}.
  Context `{!FiniteImageLts P A}.
 
  Definition terminate_extensional (p : P) : Prop :=
    forall η : max_exec_from p, exists n fex,
      mex_take_from n η = Some fex /\ lts_stable (fex_from_last fex) τ.

  #[global] Instance conv_bar : Bar P := {| bar_pred p := sts_stable p |}.

  Lemma terminate_intensional_coincide (p : P) :
    intensional_pred p ↔ terminate p.
  Proof.
    split.
    - intros H1. dependent induction H1.
      + rewrite /bar_pred /= in H0. constructor => q l.
        eapply lts_stable_spec2 in H0. contradiction. eauto.
      + constructor => q l. by eauto.
    - intros H1; induction H1.
      destruct (decide (sts_stable p)).
      + constructor 1; rewrite /bar_pred //=.
      + constructor 2 =>//.
  Qed.

  Lemma terminate_ext_pred_iff_terminate_extensional (p : P) :
    extensional_pred p <-> terminate_extensional p.
  Proof. split; intros Hme η; destruct (Hme η) as (?&?&?&?); naive_solver. Qed.

  (* ************************************************** *)

  Lemma terminate_extensional_iff_terminate (p : P) :
    terminate_extensional p <-> terminate p.
  Proof.
    rewrite <- terminate_ext_pred_iff_terminate_extensional.
    rewrite <- terminate_intensional_coincide.
    split.
    - eapply extensional_implies_intensional.
    - eapply intensional_implies_extensional.
  Qed.

  Inductive cnv_extensional : P -> trace A -> Prop :=
  | cnv_ext_nil p : terminate_extensional p -> cnv_extensional p []
  | cnv_ext_act p μ s :
    terminate_extensional p ->
    (forall q, p ⟹{μ} q -> cnv_extensional q s) ->
    cnv_extensional p (μ :: s).

  Lemma cnv_extensional_iff_terminate (p : P) s : cnv_extensional p s <-> cnv p s.
  Proof.
    revert p. induction s as [|μ s].
    - now split; inversion 1; subst; constructor; eapply terminate_extensional_iff_terminate.
    - split; inversion 1; subst; constructor.
      now apply terminate_extensional_iff_terminate.
      firstorder. now eapply terminate_extensional_iff_terminate.
      firstorder.
  Qed.
End convergence.

Section must_set_acc_set.
  Context `{P : Type}.
  Context `{Q : Type}.
  Context `{A : Type}.
  Context `{H : !ExtAction A}.
  Context `{LtsP : !Lts P A, !FiniteImageLts P A}.
  Context `{LtsQ : !Lts Q A, !FiniteImageLts Q A}.

  Context `{@LtsObaFB P A H LtsP LtsEqP LtsObaP}.
  Context `{@LtsObaFB Q A H LtsQ LtsEqQ LtsObaQ}.

  Context `{@Prop_of_Inter P (mb A) A fw_inter H LtsP MbLts}.
  Context `{@Prop_of_Inter Q (mb A) A fw_inter H LtsQ MbLts}.


  Definition actions_acc 
  (p : P * mb A) s (h : p ⇓ s) : subset_of A := oas p s h.

  (* ************************************************** *)

  Lemma either_wperform_mu 
  (p : P * mb A) μ :
    p ⤓ -> (exists q, p ⟹{μ} q) \/ ~ (exists q, p ⟹{μ} q).
  Proof.
    intro ht. induction ht.
    destruct (lts_stable_decidable p (ActExt μ)).
    - assert (∀ x, x ∈ enum (dsig (lts_step p τ)) -> (∃ q0, `x ⟹{μ} q0) \/ ~ (∃ q0, `x ⟹{μ} q0))
         as Hyp
        by (intros (x & mem) _; set_solver).
      edestruct (exists_forall_in _ _ _ Hyp) as [Hyp' | Hyp'].
      + eapply Exists_exists in Hyp' as ((q' & pr) & mem & (q0 & hw)).
        left. exists q0. eapply wt_tau; eauto. now eapply bool_decide_unpack.
      + right. intros (q' & hw). inversion hw; subst.
        ++ contradict Hyp'. intros n. rewrite Forall_forall in n.
           eapply (n (dexist q l0)). eapply elem_of_enum. eauto.
        ++ eapply (@lts_stable_spec2 (P * mb A)); eauto.
    - left. eapply lts_stable_spec1 in n as (q & l). eauto with mdb.
  Qed.

  Lemma either_wperform_mem 
    (p : P * mb A) (G : subset_of A) (ht : p ⤓) :
    (exists μ p', μ ∈ G /\ p ⟹{μ} p') \/ (forall μ p', μ ∈ G -> ~ p ⟹{μ} p').
  Proof.
    (* induction G using set_ind_L; [|destruct IHG, (either_wperform_mu p x)]; set_solver. *)
  Admitted.

  Lemma either_wperform_mem_set
    (ps : gset (P * mb A)) (G : subset_of A) (ht : forall p, p ∈ ps -> p ⤓) :
    (exists p', p' ∈ ps /\ forall μ p0, μ ∈ G 
      -> ~ p' ⟹{μ} p0) \/ (forall p', p' ∈ ps -> exists μ p0, μ ∈ G /\ p' ⟹{μ} p0).
  Proof.
    induction ps using set_ind_L; [|destruct IHps, (either_wperform_mem x G)]; set_solver.
  Qed.

  Lemma either_MUST
      (p : P * mb A) (G : subset_of A) (hcnv : p ⇓ []) :
      MUST p G \/ ~ MUST p G.
  Proof.
    assert (∀ p0 : P * mb A, p0 ∈ wt_set p [] hcnv → p0 ⤓) as pre_Hyp.
    intros p0 mem0%wt_set_spec1. eapply cnv_terminate, cnv_preserved_by_wt_nil; eauto.
    destruct (either_wperform_mem_set (wt_set p [] hcnv) G) as [Hyp|]; eauto.
    - right. intro hm. destruct Hyp as (p' & mem%wt_set_spec1%hm & nhw). set_solver.
    - left. intros p1 hw%(wt_set_spec2 _ p1 [] hcnv). set_solver.
  Qed.

  Lemma either_ex_nMUST_or_MUST
    (ps : gset (P * mb A)) G (ht : forall p, p ∈ ps -> p ⇓ []) :
    (exists p, p ∈ ps /\ ~ MUST p G) \/ (forall p, p ∈ ps -> MUST p G).
  Proof.
    induction ps using set_ind_L; [|edestruct IHps, (either_MUST x G)]; set_solver.
  Qed.

  Lemma either_MUST__s
    (ps : gset (P * mb A)) (G : subset_of A ) :
    (forall p, p ∈ ps -> p ⇓ []) -> MUST__s ps G \/ ~ MUST__s ps G.
  Proof.
    intros. edestruct (either_ex_nMUST_or_MUST ps G) as [Hyp |]; eauto.
    right. intros hm. destruct Hyp as (p0 & mem0%hm & hnm). contradiction.
  Qed.

  Lemma nMusts_ex
    (ps : gset (P * mb A)) G :
    (forall p, p ∈ ps -> p ⇓ []) -> ~ MUST__s ps G -> exists p, p ∈ ps /\ ~ MUST p G.
  Proof. intros. edestruct (either_ex_nMUST_or_MUST ps G); set_solver. Qed.

  Lemma nMust_ex
    (p : P * mb A) G (hcnv : p ⇓ []) (hnm : ~ MUST p G) :
    exists p', p ⟹ p' /\ forall μ p0, μ ∈ G -> ~ p' ⟹{μ} p0.
  Proof.
    assert (∀ p0 : P * mb A, p0 ∈ wt_set p [] hcnv → p0 ⤓).
    intros p0 mem0%wt_set_spec1. eapply cnv_terminate, cnv_preserved_by_wt_nil; eauto.
    destruct (either_wperform_mem_set (wt_set p [] hcnv) G) as [Hyp|Hyp]; eauto.
    - destruct Hyp as (p' & mem'%wt_set_spec1 & nhw). set_solver.
    - edestruct hnm. intros p' mem. eapply Hyp. eapply wt_set_spec2; eauto.
  Qed.

  Lemma nMusts_nMust
  (p : P * mb A) G (hcnv : p ⇓ []) (hnm : ~ MUST__s (wt_set p [] hcnv) G) : ¬ MUST p G.
  Proof.
    intro hm. eapply hnm. intros p' mem0%wt_set_spec1.
    intros r hw. eapply hm. eapply wt_push_nil_left; eassumption.
  Qed.
  
  Lemma nMust_out_acc_ex 
  
    (p : P * mb A) pt (q' : Q * mb A) s hcnv :
    
    pt ∈ AFTER p s hcnv -> ~ MUST pt (actions_acc p s hcnv ∖ lts_acc_set_of q') ->
    exists p', pt ⟹ p' /\ p' ↛ /\ lts_acc_set_of p' ⊆ lts_acc_set_of q'.
  Proof.
    intros mem%wt_set_spec1 hnm.
    eapply nMust_ex in hnm as (p' & hw' & nhw).
    assert (ht': p' ⤓)
      by (eapply (cnv_wt_s_terminate p p' s hcnv), wt_push_nil_right; eauto).
    eapply terminate_then_wt_stable in ht' as (p0 & hw0 & hst).
    exists p0. split. eapply wt_push_nil_left; eauto.
    split; eauto.
    intros μ mem_mu.
(*     assert (is_output μ) as (a & heq).
    eapply elem_of_map in mem_mu as (a & heq & mem2).
    exists a. assumption. subst. *)
    (* destruct (decide (μ ∈ G)).
    + eauto. 
    + assert (μ ∉ G). admit.*)
      assert (mem0 : μ ∈ actions_acc p s hcnv).
      eapply elem_of_union_list. eexists. split; eauto.
      eapply elem_of_list_fmap.
      exists p0. repeat split; eauto.
      eapply elem_of_elements, wt_stable_set_spec2; split; eauto.
      eapply wt_push_nil_right, wt_push_nil_right; eauto.
      (* exfalso. *)
      (* eapply elem_of_union_list in mem0.
      destruct mem0 as (A' & ACC & mem'). *)
      eapply lts_stable_spec1 in mem_mu as (p'0 & HypTr).
      destruct (decide (μ ∈ lts_acc_set_of q')).
      + eauto.
      + exfalso.
        eapply (nhw $ μ); eauto. set_solver.
        eapply wt_push_nil_left; eauto with mdb.
      + constructor; eapply (cnv_wt_s_terminate p pt s hcnv); eauto.
  Qed.

  

  (* Lemma nMust_out_acc_ex 
  
    (p : P * mb A) pt G s hcnv :
    
    pt ∈ AFTER p s hcnv -> ~ MUST pt (actions_acc p s hcnv ∖ G) ->
    exists p', pt ⟹ p' /\ p' ↛ /\ lts_acc_set_of p' ⊆ G.
  Proof.
    intros mem%wt_set_spec1 hnm.
    eapply nMust_ex in hnm as (p' & hw' & nhw).
    assert (ht': p' ⤓)
      by (eapply (cnv_wt_s_terminate p p' s hcnv), wt_push_nil_right; eauto).
    eapply terminate_then_wt_stable in ht' as (p0 & hw0 & hst).
    exists p0. split. eapply wt_push_nil_left; eauto.
    split; eauto.
    intros μ mem_mu.
(*     assert (is_output μ) as (a & heq).
    eapply elem_of_map in mem_mu as (a & heq & mem2).
    exists a. assumption. subst. *)
    (* destruct (decide (μ ∈ G)).
    + eauto. 
    + assert (μ ∉ G). admit.*)
      assert (mem0 : μ ∈ actions_acc p s hcnv).
      eapply elem_of_union_list. eexists. split; eauto.
      eapply elem_of_list_fmap.
      exists p0. repeat split; eauto.
      eapply elem_of_elements, wt_stable_set_spec2; split; eauto.
      eapply wt_push_nil_right, wt_push_nil_right; eauto.
      (* exfalso. *)
      (* eapply elem_of_union_list in mem0.
      destruct mem0 as (A' & ACC & mem'). *)
      eapply lts_stable_spec1 in mem_mu as (p'0 & HypTr).
      (* destruct (decide (μ ∈ G)).
      + eauto.  *)
      + assert (μ ∉ G). admit.
        exfalso.
        eapply (nhw $ μ); eauto. set_solver.
        eapply wt_push_nil_left; eauto with mdb.
      + constructor; eapply (cnv_wt_s_terminate p pt s hcnv); eauto.
  Admitted. *)

  Lemma either_MUST_or_ex 
    (p : P * mb A) (q' : Q * mb A)  s hcnv :
    MUST__s (AFTER p s hcnv) (actions_acc p s hcnv ∖ lts_acc_set_of q')
    \/ (exists p', p ⟹[s] p' /\ p' ↛ /\ lts_acc_set_of p' ⊆ lts_acc_set_of q').
  Proof.
    assert (h1 : forall p0, p0 ∈ AFTER p s hcnv → p0 ⇓ []).
    intros p0 mem0. eapply cnv_nil, cnv_wt_s_terminate; eauto.
    eapply (wt_set_spec1 _ _ _ _ mem0).
    destruct (either_MUST__s (AFTER p s hcnv) (actions_acc p s hcnv ∖ lts_acc_set_of q')) 
        as [ |Hyp]. Print AFTER.
    + eauto.
    + left. eauto.
    + right.
      eapply nMusts_ex in Hyp as (pt & mem & hnm); eauto.
      eapply nMust_out_acc_ex in hnm as (pt' & hw & hst & hsub); eauto.
      exists pt'. split; eauto. eapply wt_push_nil_right; eauto. now eapply wt_set_spec1 in mem.
  Qed.

  Lemma Must_out_acc_npre 
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
    assert { r' | r ⟶[ μ ] r'} as (r' & HypTr). eapply lts_stable_spec1. eauto.
    inversion hw'; subst.
    eapply lts_stable_spec2 in hst; eauto.
    eapply nmem. eapply lts_stable_spec2. eauto.
  Qed.

  (* ************************************************** *)

  Lemma equivalence_bhv_acc_mst2
    (p : P) (q : Q) :
    (p, ∅) ≼₁ (q, ∅) -> (p, ∅) ≾₂ (q, ∅) <-> (p, ∅) ≼₂ (q, ∅).
  Proof.
    intro hpre1.
    split.
    - intro hpre2. intros s q' hcnv hw hst.
      edestruct (either_MUST_or_ex (p, ∅) q' s hcnv).
      + exfalso. eapply Must_out_acc_npre; eauto with mdb.
      + set_solver.
    - intro hpre2.
      intros s hcnv hcnv' G hm q' mem%wt_set_spec1 q0 hw.
      assert (exists r, q0 ⟹ r /\ r ↛) as (qt & hw' & hstq').
      eapply terminate_then_wt_stable, terminate_preserved_by_wt_nil; eauto.
      eapply cnv_wt_s_terminate; eauto.
      edestruct (hpre2 s qt hcnv) as (pt & hwpt & hstpt & hsubpt); eauto.
      eapply wt_push_nil_right; eauto. eapply wt_push_nil_right; eauto.
      assert (exists μ r, μ ∈ G /\ pt ⟹{μ} r) as (μ & p0 & mem0 & hw0).
      eapply hm. eapply wt_set_spec2; eauto. eapply wt_nil.
      exists μ. inversion hw0; subst.
      + exfalso. eapply lts_stable_spec2 in hstpt; eauto.
      + assert (¬ lts_stable qt (ActExt μ)) as not_stable_qt.
        eapply hsubpt.
        eapply lts_stable_spec2. eauto.
        eapply lts_stable_spec1 in not_stable_qt as (qr & l').
        exists qr. split; eauto. eapply wt_push_nil_left; eauto with mdb.
  Qed.

  Theorem equivalence_bhv_acc_mst
  (p : P) (q : Q) :
  (p, ∅) ≾ (q, ∅) <-> (p, ∅) ≼ (q, ∅).
  Proof.
    split; intros (pre1 & pre2); split; eauto; now eapply equivalence_bhv_acc_mst2.
  Qed.

End must_set_acc_set.

(* ************************************************** *)

Section failure_must_set.

  Context `{P : Type}.
  Context `{Q : Type}.
  Context `{A : Type}.
  Context `{H : !ExtAction A}.
  Context `{LtsP : !Lts P A, !FiniteImageLts P A}.
  Context `{LtsQ : !Lts Q A, !FiniteImageLts Q A}.

  Context `{@LtsObaFB P A H LtsP LtsEqP LtsObaP}.
  Context `{@LtsObaFB Q A H LtsQ LtsEqQ LtsObaQ}.

  Context `{@Prop_of_Inter P (mb A) A fw_inter H LtsP MbLts}.
  Context `{@Prop_of_Inter Q (mb A) A fw_inter H LtsQ MbLts}.

  Lemma equivalence_must_set_nfailure
    (p : P) (s : trace A) h1 (G : subset_of A) :
    MUST__s (AFTER (p, ∅) s h1) G <-> ¬ Failure (p, ∅) s G.
  Proof.
    split.
    - intros hm (e & hw & hf). eassumption.
      edestruct (hm e) as (μ & p' & mem' & hw'). eapply wt_set_spec2. eauto. eapply wt_nil.
      edestruct (hf μ mem'). eauto.
    - intros hnf.
      assert (∀ p0 : P * mb A, p0 ∈ AFTER (p ▷ ∅) s h1 → p0 ⇓ []).
      intros p0 mem0. eapply cnv_nil, cnv_wt_s_terminate; eauto.
      eapply (wt_set_spec1 _ _ _ _ mem0).
      destruct (either_MUST__s (AFTER (p, ∅) s h1) G) as [Hyp | Hyp]; eauto.
      + eapply nMusts_ex in Hyp as (p0 & mem & hnm).
        exfalso. eapply hnf.
        eapply nMust_ex in hnm as (p1 & hw1 & hnp).
        exists p1. split.
        eapply wt_push_nil_right.
        eapply (wt_set_spec1 _ _ _ _ mem). eassumption.
        intros μ mem0 (p' & hw'). eapply hnp. eassumption.
        eassumption.
        eapply cnv_nil, cnv_wt_s_terminate; eauto.
        eapply (wt_set_spec1 _ _ _ _ mem). eauto.
  Qed.

  Lemma equivalence_nmust_set_failure
    (p : P) (s : trace A) h1 (G : subset_of A) :
    ¬ MUST__s (AFTER (p ▷ ∅) s h1) G <-> Failure (p ▷ ∅) s G.
  Proof.
    split.
    - intro hm.
      eapply nMusts_ex in hm as (p0 & mem & hnm).
      eapply nMust_ex in hnm as (p1 & hw1 & hnp).
      exists p1. split.
      eapply wt_push_nil_right.
      eapply (wt_set_spec1 _ _ _ _ mem). eassumption.
      intros μ mem0 (p' & hw'). eapply hnp. eassumption.
      eassumption.
      eapply cnv_nil, cnv_wt_s_terminate; eauto.
      eapply (wt_set_spec1 _ _ _ _ mem).
      intros p0 mem0. eapply cnv_nil, cnv_wt_s_terminate; eauto.
      eapply (wt_set_spec1 _ _ _ _ mem0).
    - intros (e & hmem & hf) hm. eassumption.
      unfold MUST__s in hm.
      unfold MUST in hm.
      edestruct (hm e) as (μ & p1 & mem1 & hw1).
      eapply (wt_set_spec2 _ _ _ _ hmem). eapply wt_nil.
      eapply (hf μ mem1). eauto.
  Qed.

End failure_must_set.

Section failure_must_set_pre.
  Context `{P : Type}.
  Context `{Q : Type}.
  Context `{A : Type}.
  Context `{H : !ExtAction A}.
  Context `{LtsP : !Lts P A, !FiniteImageLts P A}.
  Context `{LtsQ : !Lts Q A, !FiniteImageLts Q A}.

  Context `{@LtsObaFB P A H LtsP LtsEqP LtsObaP}.
  Context `{@LtsObaFB Q A H LtsQ LtsEqQ LtsObaQ}.

  Context `{@Prop_of_Inter P (mb A) A fw_inter H LtsP MbLts}.
  Context `{@Prop_of_Inter Q (mb A) A fw_inter H LtsQ MbLts}.

  Theorem equivalence_pre_failure_must_set
  
  (p : P) (q : Q) : (p ▷ ∅) ≾ (q ▷ ∅) <-> (p ▷ ∅) ⋖ (q ▷ ∅).
  Proof.
    split.
    - intros (hpre1 & hpre2). split; eauto.
      intros s G hf.
      intro hcnv.
      eapply (equivalence_nmust_set_failure p s hcnv).
      intros hm. eapply (hpre2 s hcnv (hpre1 s hcnv)) in hm.
      eapply (equivalence_must_set_nfailure q s (hpre1 s hcnv) G) in hm. contradiction. eassumption.
    - intros (hpre1 & hpre2). split; eauto.
      intros s h1 h2 G hm%equivalence_must_set_nfailure.
      eapply (equivalence_must_set_nfailure q).
      intros hf%hpre2. contradiction.
  Qed.

End failure_must_set_pre.

Section preorder.

  (** Extensional definition of Must *)
(*   Context `{P : Type}.
  Context `{E : Type}. *)
 (*  Context `{H : !ExtAction A}. *)
(*   Context `{LtsP : !Lts P A, !FiniteImageLts P A}.
  Context `{LtsQ : !Lts Q A, !FiniteImageLts Q A}.

  Context `{@LtsObaFB P A H LtsP LtsEqP LtsObaP}.
  Context `{@LtsObaFB Q A H LtsQ LtsEqQ LtsObaQ}. 
  
  `{@Prop_of_Inter P E A parallel_inter H LtsP LtsE}
  *)
  Definition must_extensional
    {P : Type}
    `{Sts (P * E), good : E -> Prop} 
    (p : P) (e : E) : Prop :=
    forall η : max_exec_from (p, e), exists n fex, mex_take_from n η = Some fex 
          /\ good (fex_from_last fex).2 .

  Definition good_client {P : Type} `{Sts (P * E), good : E -> Prop} (s : (P * E)) := good s.2.

  #[global] Program Instance must_bar {P : Type} {E : Type} `{Sts (P * E)} (good : E -> Prop)
    `{good_decidable : forall e, Decision (good e)}: Bar (P * E) :=
    {| bar_pred '(p, e) := good e |}.
  Next Obligation. intros. destruct x as (p, e). simpl. eauto. Defined.

  Lemma must_intensional_coincide {P : Type}
    `{Sts (P * E), good : E -> Prop, good_decidable : 
    forall (e : E), Decision (good e)}
    (p : P) (e : E) : @intensional_pred (P * E) _ (must_bar good) (p, e) ↔ 
    @must_sts P E _ good p e.
  Proof.
    split.
    - intros H1. dependent induction H1; subst.
      + rewrite /bar_pred /= in H1. now eapply m_sts_now.
      + destruct (good_decidable e).
        rewrite /bar_pred /= in H1.
        now eapply m_sts_now. eapply m_sts_step; eauto.
    - intros hm; dependent induction hm.
      + constructor 1. 
        rewrite /bar_pred //=.
      + constructor 2.
        * eassumption.
        * intros (q, e') Hstep. apply H0 =>//=.
  Qed.
  Print must_extensional.
  Lemma must_ext_pred_iff_must_extensional 
    {P : Type}  
    `{StsPE : Sts (P * E), good : E -> Prop, good_decidable : forall (e : E), Decision (good e)}
    (p : P) (e : E) : @extensional_pred _ _ (must_bar good) (p, e) <-> 
    @must_extensional P E _ good p e.
  Proof. split; intros Hme η; destruct (Hme η) as (?&?&?&?).
         exists x, x0. split. eassumption. simpl. destruct (fex_from_last x0). naive_solver.
         exists x, x0. split. eassumption. simpl. destruct (fex_from_last x0). naive_solver.
  Qed.

  Definition pre_extensional
    {P : Type} {Q : Type} 
    `{Sts (P * E), Sts (Q * E), good : E -> Prop, good_decidable : forall (e : E), 
    Decision (good e)}
    (p : P) (q : Q) : Prop :=
    forall (e : E), @must_extensional P E _ good p e -> @must_extensional Q E _ good q e.

  (* ************************************************** *)

  Lemma must_extensional_iff_must_sts
    {P : Type}
    `{good : E -> Prop, good_decidable : forall (e : E), Decision (good e)}
    `{LtsP : @Lts P A H, !FiniteImageLts P A,
    LtsE : !Lts E A, !LtsEq E A, !Good E A good,  !FiniteImageLts E A}
    `{@Prop_of_Inter P E A parallel_inter H LtsP LtsE} (* à rajouter en context ? *)
    (p : P) (e : E) : @must_extensional P E _ good p e <-> @must_sts P E _ good p e.
  Proof.
    split.
    - intros hm. destruct Good0.
      eapply must_ext_pred_iff_must_extensional in hm.
      now eapply must_intensional_coincide, extensional_implies_intensional.
    - intros hm. destruct Good0.
      eapply must_intensional_coincide in hm.
      rewrite <- must_ext_pred_iff_must_extensional.
      eapply intensional_implies_extensional. eapply hm.
  Qed.

  Notation "p ⊑ₑ q" := (pre_extensional p q) (at level 70).

  Context `{good : E -> Prop}.
  Context `{good_dec : forall e, Decision (good e)}.
  Context `{P : Type}.
  Context `{Q : Type}.
  Context `{H : !ExtAction A}.
  Context `{LtsP : !Lts P A, !FiniteImageLts P A}.
  Context `{LtsQ : !Lts Q A, !FiniteImageLts Q A}.
  Context `{LtsE : !Lts E A, !FiniteImageLts E A, LtsEqE: !LtsEq E A, !Good E A good}.
  Context `{@Prop_of_Inter P E A parallel_inter H LtsP LtsE}.
  Context `{@Prop_of_Inter Q E A parallel_inter H LtsQ LtsE}.

  (* ************************************************** *)

  Lemma pre_extensional_eq (p : P) (q : Q) : 
    @pre_extensional P Q _ _ _ good _ p q <-> p ⊑ q.
    unfold pre_extensional, ctx_pre.
  Proof.
    split; intros hpre e.
    - rewrite <- 2 must_sts_iff_must, <- 2 must_extensional_iff_must_sts; eauto.
    - rewrite -> 2 must_extensional_iff_must_sts, -> 2 must_sts_iff_must; eauto.
  Qed.

  Context `{@LtsObaFB P A H LtsP LtsEqP LtsObaP}.
  Context `{@LtsObaFB Q A H LtsQ LtsEqQ LtsObaQ}.
  Context `{@LtsObaFB E A H LtsE LtsEqE LtsObaE}.

  Context `{igen_conv : @gen_spec_conv _ _ _ _ _ good Good0 co_of gen_conv}.
  Context `{igen_acc : @gen_spec_acc _ _ _ _ _ good Good0 co_of gen_acc}.

  Context `{@Prop_of_Inter P (mb A) A fw_inter H LtsP MbLts}.
  Context `{@Prop_of_Inter (P * mb A) E A parallel_inter H (inter_lts fw_inter) LtsE}.
  Context `{@Prop_of_Inter Q (mb A) A fw_inter H LtsQ MbLts}.
  Context `{@Prop_of_Inter (Q * mb A) E A parallel_inter H (inter_lts fw_inter) LtsE}.

  (* ************************************************** *)

  (** Equivalence between the extensional definition of the contextual preorder and
      the alternative, inductive characterisation. *)
  Theorem equivalence_bhv_acc_ctx (p : P) (q : Q) :
    @pre_extensional P Q _ _ _ good _ p q <-> (p, ∅) ≼ (q, ∅).
  Proof.
    split.
    - intros hpre%pre_extensional_eq.
      now eapply lift_fw_ctx_pre, completeness_fw in hpre.
    - intros hpre%soundness_fw.
      now eapply pre_extensional_eq, lift_fw_ctx_pre.
  Qed.

  (* ************************************************** *)


  Corollary equivalence_bhv_mst_ctx
    (p : P) (q : Q) : (p, ∅) ≾ (q, ∅) <-> @pre_extensional P Q _ _ _ good _ p q.
  Proof.
    rewrite pre_extensional_eq.
    rewrite equivalence_bhv_acc_mst.
    rewrite <- equivalence_bhv_acc_ctx.
    eapply pre_extensional_eq.
  Qed.

End preorder.

From stdpp Require Import gmultiset.

Section application.

  Lemma nil_stable (* `{@LtsOba Q A H LtsQ LtsEqQ} *)
  (* `{@Prop_of_Inter Q (mb A) A fw_inter H LtsQ MbLts} *)
  {Q A : Type} {H : ExtAction A}
  `{@LtsOba Q A H LtsQ LtsEqQ}
  `{@Prop_of_Inter Q (mb A) A fw_inter H LtsQ MbLts}
  
  (q : Q) (h : forall α, q ↛{α}) (m : mb A) : 
  lts_stable (q, m) τ.
  Proof.
    destruct (decide ((q, m) ↛)); eauto.
    eapply lts_stable_spec1 in n as (q' & l').
    inversion l'; subst.
    + edestruct lts_stable_spec2; eauto.
    + inversion l.
    + edestruct lts_stable_spec2; eauto.
  Qed.

  Lemma nil_cnv
  {Q A : Type} {H : ExtAction A}
  `{@LtsOba Q A H LtsQ LtsEqQ}
  `{@Prop_of_Inter Q (mb A) A fw_inter H LtsQ MbLts}
  (q : Q) (h : forall α, q ↛{α}) s m : 
  (q, m) ⇓ s.
  Proof.
    dependent induction s.
    - now eapply cnv_nil, terminate_if_stable, nil_stable.
    - eapply cnv_act.
      + now eapply terminate_if_stable, nil_stable.
      + intros (q', m') hw. inversion hw; subst.
        ++ exfalso. eapply (@lts_stable_spec2 (Q * mb A)).
           eauto. now eapply nil_stable.
        ++ inversion l; subst.
           +++ edestruct lts_stable_spec2. eauto. eauto.
           +++ eapply cnv_preserved_by_wt_nil; eauto.
  Qed.

  CoInductive ionly_spec {P A : Type} {H : ExtAction A} 
    `{@LtsOba P A H LtsQ LtsEqQ} (p : P) : Prop :=
  | mstep : (forall μ p', p ⟶[μ] p' -> ¬ non_blocking μ) 
        -> (forall α p', p ⟶{α} p' -> ionly_spec p') -> ionly_spec p.

  Lemma lts_non_blocking_ionly_spec {P A : Type}
        `{LtsOba P A} (p : P) (pr : ionly_spec p) : dom (lts_oba_mo p) = ∅.
  Proof.
    eapply leibniz_equiv. intro a. split.
    + intros mem.
      eapply gmultiset_elem_of_dom in mem.
      eapply lts_oba_mo_spec_bis2 in mem as (p' & nb & l').
      destruct pr as (h1 & h2). eapply h1 in l' as not_nb.
      contradiction.
    + intro. set_solver.
Qed.

  Lemma lts_non_blocking_ionly_spec_wt_nil_empty_mb 
        {Q A : Type} {H : ExtAction A}
        `{LL : @LtsObaFB Q A H LtsQ LtsEqQ LLOBA}
        `{@Prop_of_Inter Q (mb A) A fw_inter H LtsQ MbLts}
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
        `{LL : @LtsObaFB Q A H LtsQ LtsEqQ LLOBA}
        `{@Prop_of_Inter Q (mb A) A fw_inter H LtsQ MbLts}
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
        ++ eapply gmultiset_elem_of_dom. exact in_mem.
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

  Lemma ionly_nil_leq2_wt_nil {Q A : Type} {H : ExtAction A}
        `{LL : @LtsObaFB Q A H LtsQ LtsEqQ LLOBA}
        `{@Prop_of_Inter Q (mb A) A fw_inter H LtsQ MbLts}
    n p (pr : ionly_spec p) m :
    (p, m) ⤓ -> size m = n -> exists t, (p, m) ⟹ t /\ t ↛ /\ dom (lts_oba_mo t) ⊆ dom m.
  Proof.
    intros ht heq. edestruct @terminate_then_wt_stable as (t & hw & hst); eauto with mdb.
    exists t; split; eauto. split; eauto. eapply lts_non_blocking_ionly_spec_wt_nil; eauto.
  Qed.

  Lemma ionly_nil_leq2 {P Q A : Type} `{
    @LtsObaFB P A H LtsP LtsEqP LtsObaP,
    @LtsObaFB Q A H LtsQ LtsEqQ LtsObaQ}

    `{@Prop_of_Inter P (mb A) A fw_inter H LtsP MbLts}
    `{@Prop_of_Inter Q (mb A) A fw_inter H LtsQ MbLts}

    (p : P) (pr : ionly_spec p) (q : Q) m (h : forall α, q ↛{α}) : 
    (p, m) ≼₂ (q, m).
  Proof.
    intros s t hcnv hw hst.
    dependent induction hw.
    - inversion hcnv; subst.
      edestruct ionly_nil_leq2_wt_nil as (p' & hw & hst' & hsub); eauto.
      exists p'. split; eauto.
      split; eauto. admit. 
    - exfalso. eapply (@lts_stable_spec2 (Q * mb A)). eauto. now eapply nil_stable.
    - inversion hcnv; inversion l; subst.
      + exfalso. eapply (@lts_stable_spec2 Q); eauto.
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
  Admitted.

  Lemma input_only_leq_nil {P Q A : Type} `{
    @LtsObaFB P A H LtsP LtsEqP V, !FiniteImageLts P A,
    @LtsObaFB Q A H LtsQ LtsEqQ W, !FiniteImageLts Q A,
    @LtsObaFB E A H LtsE LtsEqE X, !FiniteImageLts E A, !Good E A good, (∀ e : E, Decision (good e)),
    @gen_spec_conv  _ _ _ _ _ good _ co_of gen_conv, @gen_spec_acc _ _ _ _ _ good _ co_of gen_acc}
    `{@Prop_of_Inter P E A parallel_inter H LtsP LtsE}
    `{@Prop_of_Inter Q E A parallel_inter H LtsQ LtsE}
    
    `{@Prop_of_Inter P (mb A) A fw_inter H LtsP MbLts}
    `{@Prop_of_Inter (P * mb A) E A parallel_inter H (inter_lts fw_inter) LtsE}

    `{@Prop_of_Inter Q (mb A) A fw_inter H LtsQ MbLts}
    `{@Prop_of_Inter (Q * mb A) E A parallel_inter H (inter_lts fw_inter) LtsE}
    (p : P) (pr : ionly_spec p) (q : Q) (h : forall α, q ↛{α}) : 
    @pre_extensional _ _ _ _ _ good _ p q.
  Proof.
    now eapply equivalence_bhv_acc_ctx; split; intros ? ?; [eapply nil_cnv | eapply ionly_nil_leq2].
  Qed.

End application.
