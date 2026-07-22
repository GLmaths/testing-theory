(*
   Copyright (c) 2024 Nomadic Labs
   Copyright (c) 2024 Paul Laforgue <paul.laforgue@nomadic-labs.com>
   Copyright (c) 2024 Léo Stefanesco <leo.stefanesco@mpi-sws.org>
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

From Stdlib Require Import ssreflect.
From Stdlib.Program Require Import Equality.

From stdpp Require Import base decidable gmap finite.

From TestingTheory Require Import 
  gLts Lts_OBA Lts_OBA_FB Lts_FW FiniteImageLTS Lts_CN
  Subset_Act ActTau 
  Convergence Termination Bisimulation WeakTransitions
  InteractionBetweenLts MultisetLTSConstruction 
  ParallelLTSConstruction ForwarderConstruction
  Testing_Predicate Must Lift DefinitionAS DefinitionMS
  InFiniteSetHelper.

Definition oas_all `{CC : Countable PreAct}  `{
  gLtsP : @gLts P A H, FiniteImagegLts P A,
  FiniteAbs : @FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 gLtsP gLtsT _ _}
  (p : P) (s : list A) (hcnv : p ⇓ s) : gset PreAct :=
  let ps : list P := elements (wt_set p s hcnv) in
  ⋃ map coR_abs ps.

Definition oas `{CC : Countable PreAct}  `{
  gLtsP : @gLts P A H, FiniteImagegLts P A,
  FiniteAbs : @FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 gLtsP gLtsT _ _}
  (p : P) (s : list A) (hcnv : p ⇓ s) : gset PreAct :=
  let ps : list P := elements (wt_refuses_set p s hcnv) in
  ⋃ map coR_abs ps.

  (* ************************************************** *)

Lemma either_wperform_mu `{gLts P A, !FiniteImagegLts P A}
(p : P) μ :
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
      ++ eapply (@lts_refuses_spec2 P); eauto.
  - left. eapply lts_refuses_spec1 in n as (q & l). eauto with mdb.
Qed.

Lemma either_wperform_co_mu `{CC : Countable PreAct} `{@gLts P A H, !FiniteImagegLts P A}
  `{@FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 _ gLtsT _ _ }
(p : P) i :
  p ⤓ -> (exists β μ q, ( 𝝳 ∘ Φ ) β = i /\ p ⟹{μ} q /\ dual μ β /\ blocking β) 
            \/ ~ (exists β μ q, ( 𝝳 ∘ Φ ) β = i /\ p ⟹{μ} q /\ dual μ β /\ blocking β).
Proof.
  intro ht. induction ht.
  destruct (decide (i ∈ (coR_abs p))) as [in_co | not_in_co].
  - left. eapply coR_abs_spec1 in in_co.
    destruct in_co as (β & mem & eq). subst. destruct mem as (μ & tr & duo & nb).
    eapply lts_refuses_spec1 in tr as (q & l). exists β, μ , q.
    repeat split ;eauto. eapply lts_to_wt;eauto.
  - assert (∀ x, x ∈ enum (dsig (lts_step p τ)) 
  -> (∃ β μ q0, ( 𝝳 ∘ Φ ) β = i /\ `x ⟹{μ} q0 /\ dual μ β /\ blocking β) \/ ~ (∃ β μ q0, ( 𝝳 ∘ Φ ) β = i /\ `x ⟹{μ} q0 /\ dual μ β /\ blocking β))
       as Hyp
      by (intros (x & mem) _; set_solver).
    edestruct (exists_forall_in _ _ _ Hyp) as [Hyp' | Hyp'].
    + eapply Exists_exists in Hyp' as ((q' & pr) & mem & (β & μ & q0 & eq & hw & duo & b)).
      left. exists β , μ, q0. repeat split ;eauto. eapply wt_tau; eauto. now eapply bool_decide_unpack.
    + right. intros (β & μ & q' & eq' & hw & duo & b). inversion hw; subst.
      ++ contradict Hyp'. intros n. rewrite Forall_forall in n.
         eapply (n (dexist q l)). eapply elem_of_enum.
         exists β , μ , q'. eauto.
      ++ assert ((𝝳 ∘ Φ) β ∈ coR_abs p).
         { eapply coR_abs_spec2. eapply map_gamma_of_action.
           exists μ. repeat split ;eauto. eapply (@lts_refuses_spec2 P); eauto. }
         contradiction.
Qed.

Lemma either_wperform_mem `{CC : Countable PreAct} `{@gLts P A H, !FiniteImagegLts P A}
  `{@FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 _ gLtsT _ _ }
  (p : P) (G : gset PreAct) (ht : p ⤓) :
  (exists β μ p', ( 𝝳 ∘ Φ ) β ∈ G /\ p ⟹{μ} p' /\ dual μ β /\ blocking β)
    \/ (forall β μ p', ( 𝝳 ∘ Φ ) β ∈ G -> dual μ β -> blocking β -> ~ p ⟹{μ} p').
Proof.
  induction G using set_ind_L. 
  + set_solver. 
  + destruct IHG. 
    * set_solver. 
    * destruct (either_wperform_co_mu p x) as [(β & μ & p' & eq & wt_tr & duo & b) | ].
      - exact ht.
      - left. exists β , μ , p'. subst. set_solver.
      - right. intros. intro. eapply H4.
        assert ((𝝳 ∘ Φ) β = x) by set_solver.
        exists β , μ , p'. eauto.
Qed.

Lemma either_wperform_mem_set `{CC : Countable PreAct} `{@gLts P A H, !FiniteImagegLts P A}
  `{@FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 _ gLtsT _ _ }
  (ps : gset P) (G : gset PreAct) (ht : forall p, p ∈ ps -> p ⤓) :
  (exists p', p' ∈ ps /\ forall β μ p0, ( 𝝳 ∘ Φ ) β ∈ G -> dual μ β -> blocking β
    -> ~ p' ⟹{μ} p0) 
    \/ (forall p', p' ∈ ps -> exists β μ p0, ( 𝝳 ∘ Φ ) β ∈ G /\ p' ⟹{μ} p0 /\ dual μ β /\ blocking β).
Proof.
  induction ps using set_ind_L. 
  + set_solver. 
  + destruct IHps.
    * intros. set_solver.
    * left; set_solver.
    * destruct (either_wperform_mem x G); set_solver.
Qed.

Lemma either_MUST `{CC : Countable PreAct} `{@gLts P A H, !FiniteImagegLts P A}
    `{@FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 _ gLtsT _ _ }
    (p : P) (G : gset PreAct) (hcnv : p ⇓ []) :
    p MUST G \/ ~ p MUST G.
Proof.
  assert (∀ p0 : P, p0 ∈ wt_set p [] hcnv → p0 ⤓) as pre_Hyp.
  intros p0 mem0%wt_set_spec1. eapply cnv_terminate, cnv_preserved_by_wt_nil; eauto.
  destruct (either_wperform_mem_set (wt_set p [] hcnv) G) 
    as [Hyp|]; eauto.
  - right. intro hm. destruct Hyp as (p' & mem%wt_set_spec1%hm & nhw). set_solver.
  - left. intros p1 hw%(wt_set_spec2 _ p1 [] hcnv). set_solver.
Qed.

Lemma either_ex_nMUST_or_MUST `{CC : Countable PreAct} `{@gLts P A H, !FiniteImagegLts P A}
  `{@FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 _ gLtsT _ _ }
  (ps : gset P) (G : gset PreAct)
    (ht : forall p, p ∈ ps -> p ⇓ []) :
  (exists p, p ∈ ps /\ ~ p MUST G) 
    \/ (forall p, p ∈ ps -> p MUST G).
Proof.
  induction ps using set_ind_L; [|edestruct IHps, (either_MUST x G)]; set_solver.
Qed.

Lemma either_MUST__s `{CC : Countable PreAct} `{@gLts P A H, !FiniteImagegLts P A}
  `{@FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 _ gLtsT _ _ }
  (ps : gset P) (G : gset PreAct)  :
  (forall p, p ∈ ps -> p ⇓ []) -> MUST__s ps G \/ ~ MUST__s ps G.
Proof.
  intros. edestruct (either_ex_nMUST_or_MUST ps G) as [Hyp |]; eauto.
  right. intros hm. destruct Hyp as (p0 & mem0%hm & hnm). contradiction.
Qed.

Lemma nMusts_ex `{CC : Countable PreAct} `{@gLts P A H, !FiniteImagegLts P A}
  `{@FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 _ gLtsT _ _ }
  (ps : gset P) (G : gset PreAct) :
  (forall p, p ∈ ps -> p ⇓ []) -> ~ MUST__s ps G
  -> exists p, p ∈ ps /\ ~ p MUST G.
Proof. intros. edestruct (either_ex_nMUST_or_MUST ps G); set_solver. Qed.

Lemma nMust_ex `{CC : Countable PreAct} `{@gLts P A H, !FiniteImagegLts P A}
  `{@FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 _ gLtsT _ _ }
  (p : P) (G : gset PreAct) (hcnv : p ⇓ []) 
  (hnm : ~ p MUST G) :
  exists p', p ⟹ p' /\ forall β μ p0, (𝝳 ∘ Φ) β ∈ G -> dual μ β -> blocking β -> ~ p' ⟹{μ} p0.
Proof.
  assert (∀ p0 : P, p0 ∈ wt_set p [] hcnv → p0 ⤓).
  intros p0 mem0%wt_set_spec1. eapply cnv_terminate, cnv_preserved_by_wt_nil; eauto.
  destruct (either_wperform_mem_set (wt_set p [] hcnv) G) as [Hyp|Hyp]; eauto.
  - destruct Hyp as (p' & mem'%wt_set_spec1 & nhw). set_solver.
  - edestruct hnm. intros p' mem. eapply Hyp. eapply wt_set_spec2; eauto.
Qed.

Lemma nMusts_nMust
`{CC : Countable PreAct} `{@gLts P A H, !FiniteImagegLts P A}
`{@FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 _ gLtsT _ _ }
(p : P) (G : gset PreAct) (hcnv : p ⇓ []) 
(hnm : ~ MUST__s (wt_set p [] hcnv) G) : 
¬ p MUST G.
Proof.
  intro hm. eapply hnm. intros p' mem0%wt_set_spec1.
  intros r hw. eapply hm. eapply wt_push_nil_left; eassumption.
Qed.

Lemma nMust_out_acc_ex
  `{CC : Countable PreAct} `{@gLts P A H, !FiniteImagegLts P A}
  `{@FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 _ gLtsT _ _ }
  (p : P) pt G s hcnv :

  pt ∈ AFTER p s hcnv 
  -> ~ pt MUST ((oas p s hcnv) ∖ G) ->
  exists p', pt ⟹ p' /\ p' ↛ /\ (coR_abs p') ⊆ G.
Proof.
  intros mem%wt_set_spec1 hnm.
  eapply nMust_ex in hnm as (p' & hw' & nhw).
  + assert (ht': p' ⤓)
    by (eapply (cnv_wt_s_terminate p p' s hcnv), wt_push_nil_right; eauto).
    eapply terminate_then_wt_refuses in ht' as (p0 & hw0 & hst).
    exists p0. split. eapply wt_push_nil_left; eauto.
    split; eauto.
    intros pre_μ mem_mu.
    assert (mem0 : pre_μ ∈ oas p s hcnv).
    { eapply elem_of_union_list. eexists. split; eauto.
      eapply list_elem_of_fmap.
      exists p0. repeat split; eauto.
      eapply elem_of_elements, wt_refuses_set_spec2; split; eauto.
      eapply wt_push_nil_right, wt_push_nil_right; eauto. }
    (* eapply lts_refuses_spec1 in mem_mu as (p'0 & HypTr). *)
    { destruct (decide (pre_μ ∈ G)).
      + eauto.
      + exfalso. 
        eapply coR_abs_spec1 in mem_mu as Hyp.
        destruct Hyp as (μ & Hyp_co & eq). subst.
        destruct Hyp_co as (μ' & tr & duo & b).
        eapply lts_refuses_spec1 in tr as (p'' & tr'').
        eapply (nhw $ μ); eauto.
        unfold oas in mem0. set_solver.
        eapply wt_push_nil_left; eauto with mdb. }
   + constructor; eapply (cnv_wt_s_terminate p pt s hcnv); eauto.
Qed.

Lemma either_MUST_or_ex
  `{CC : Countable PreAct} `{@gLts P A H, !FiniteImagegLts P A}
  `{@FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 _ gLtsT _ _ }
  (p : P) G s hcnv :
  MUST__s (AFTER p s hcnv) ((oas p s hcnv) ∖ G)
  \/ (exists p', p ⟹[s] p' /\ p' ↛ /\ (coR_abs p') ⊆ G).
Proof.
  assert (h1 : forall p0, p0 ∈ AFTER p s hcnv → p0 ⇓ []).
  intros p0 mem0. eapply cnv_nil, cnv_wt_s_terminate; eauto.
  eapply (wt_set_spec1 _ _ _ _ mem0).
  destruct (either_MUST__s (AFTER p s hcnv) ((oas p s hcnv) ∖ G))
      as [ |Hyp].
  + eauto.
  + left. eauto.
  + right.
    eapply nMusts_ex in Hyp as (pt & mem & hnm); eauto.
    eapply nMust_out_acc_ex in hnm as (pt' & hw & hst & hsub); eauto.
    exists pt'. split; eauto. eapply wt_push_nil_right; eauto. now eapply wt_set_spec1 in mem.
Qed.

Lemma Must_out_acc_npre `{CC : Countable PreAct} `{@gLts P A H, !FiniteImagegLts P A}
  `{@FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 _ gLtsT _ _ }
  `{@gLts Q A H, !FiniteImagegLts Q A}
  `{@FinitaryAbsAction Q T FinA PreAct A _ Φ 𝝳 _ gLtsT _ _ }
  (p : P) (q q' : Q) s hcnv :
  q ⇓ s -> q ⟹[s] q' -> q' ↛ ->
  MUST__s (AFTER p s hcnv) (oas p s hcnv ∖ coR_abs q') ->
  ~ p ₂≾ₘᵤₛₜ q.
Proof.
  intros hcnv' hw hst hm pre2.
  set (G := (oas p s hcnv ∖ coR_abs q')).
  assert (exists β μ t, (𝝳 ∘ Φ) β ∈ G /\ q' ⟹{μ} t /\ dual μ β /\ blocking β) as (β & μ & t & mem & hw' & duo & b).
  { eapply (pre2 s hcnv hcnv'); eauto. eapply wt_set_spec2; eauto. eapply wt_nil. }
  eapply elem_of_difference in mem as (mem & nmem).
  
  eapply elem_of_union_list in mem as (X & mem1 & mem2).
  eapply list_elem_of_fmap in mem1 as (r & heq & mem1). subst.
  
  eapply coR_abs_spec1 in mem2 as Hyp.
  destruct Hyp as (μ2 & Hyp_co & eq).
  destruct Hyp_co as (μ'2 & tr & duo' & b').

  assert { r' | r ⟶[ μ'2 ] r'} as (r' & HypTr).
  { eapply lts_refuses_spec1. eauto. }
  inversion hw'; subst.
  * eapply lts_refuses_spec2 in hst; eauto.
  * eapply nmem.
    eapply coR_abs_spec2.
    eapply map_gamma_of_action.
    exists μ. repeat split.
    - eapply lts_refuses_spec2. eauto.
    - exact duo.
    - exact b.
Qed.

(* ************************************************** *)

Lemma equivalence_bhv_acc_mst2 `{CC : Countable PreAct} `{@gLts P A H, !FiniteImagegLts P A}
  `{@FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 _ gLtsT _ _ }
  `{@gLts Q A H, !FiniteImagegLts Q A}
  `{@FinitaryAbsAction Q T FinA PreAct A _ Φ 𝝳 _ gLtsT _ _ }
  (p : P) (q : Q) :
  p ₁≼ₐₛ q -> p ₂≾ₘᵤₛₜ q <-> p ₂≼ₐₛ q.
Proof.
  intro hpre1.
  split.
  - intro hpre2. intros s q' hcnv hw hst.
    edestruct (either_MUST_or_ex p (coR_abs q') s hcnv).
    + exfalso. eapply (Must_out_acc_npre p q) in H4;eauto.
    + destruct H4 as (p' & wt_tr & stable & sub). 
      exists p'. repeat split; eauto. intros pre_μ mem.
      eapply coR_abs_spec2 in mem. eapply sub in mem.
      eapply coR_abs_spec1; eauto.
  - intro hpre2.
    intros s hcnv hcnv' G hm q' mem%wt_set_spec1 q0 hw.
    assert (exists r, q0 ⟹ r /\ r ↛) as (qt & hw' & hstq').
    { eapply terminate_then_wt_refuses, terminate_preserved_by_wt_nil; eauto.
      eapply cnv_wt_s_terminate; eauto. }
    edestruct (hpre2 s qt hcnv) as (pt & hwpt & hstpt & hsubpt); eauto.
    eapply wt_push_nil_right; eauto. eapply wt_push_nil_right; eauto.
    assert (exists β μ r, ( 𝝳 ∘ Φ ) β ∈ G /\ pt ⟹{μ} r /\ dual μ β /\ blocking β) as (β & μ & p0 & mem0 & hw0 & duo & b).
    { eapply hm. eapply wt_set_spec2; eauto. eapply wt_nil. }
    inversion hw0; subst.
    + exfalso. eapply lts_refuses_spec2 in hstpt; eauto.
    + assert (( 𝝳 ∘ Φ) β ∈ coR_abs qt) as mem'.
      { eapply coR_abs_spec2. eapply hsubpt.
      eapply map_gamma_of_action. exists μ.
      repeat split.
      -- eapply lts_refuses_spec2 ;eauto.
      -- exact duo. 
      -- exact b. }
      eapply coR_abs_spec1 in mem'. destruct mem' as (μ' & mem' & eq).
      destruct mem' as (μ'' & tr & duo' & b').
      exists μ'.  exists μ''. eapply lts_refuses_spec1 in tr as (qr & tr_qr).
      exists qr. repeat split.
      ++ rewrite<- eq; eauto.
      ++ eapply wt_push_nil_left; eauto with mdb.
      ++ exact duo'.
      ++ exact b'.
Qed.

Theorem equivalence_bhv_acc_mst `{CC : Countable PreAct} `{
  gLtsEqP : @gLtsEq P A H, !FiniteImagegLts P A,
  gLtsEqQ : @gLtsEq Q A H, !FiniteImagegLts Q A,
  FinAbsPT : @FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 _ gLtsT _ _,
  FinAbsQT : @FinitaryAbsAction Q T FinA PreAct A H Φ 𝝳 _ gLtsT _ _}
  (p : P) (q : Q) :
  p ≾ₘᵤₛₜ q <-> p ≼ₐₛ q.
  Proof.
    split; intros (pre1 & pre2) ; split; eauto; eapply equivalence_bhv_acc_mst2;eauto.
  Qed.

From stdpp Require Import base decidable gmap finite.
From Stdlib Require Import ssreflect.
From Stdlib.Program Require Import Equality.
From TestingTheory Require Import gLts Bisimulation Lts_OBA Lts_FW Lts_OBA_FB StateTransitionSystems Termination
    Must Bar Completeness Soundness Lift Subset_Act FiniteImageLTS WeakTransitions Convergence
    InteractionBetweenLts MultisetLTSConstruction ForwarderConstruction ParallelLTSConstruction ActTau
    Testing_Predicate DefinitionAS MustE Lts_Finite_Output_Chain Equivalence Soundness Completeness.

Section must_set_preorder.
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

  Context `{!Prop_of_Inter P (MO A) A fw_inter}.
  Context `{!Prop_of_Inter (P * MO A) T A dual}.
  Context `{!Prop_of_Inter Q (MO A) A fw_inter}.
  Context `{!Prop_of_Inter (Q * MO A) T A dual}.


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

  (** ** The must-set characterisation on FW is equivalent to the extensional must preorder *)
  Corollary equivalence_fw_must_set_and_must_e (p : P) (q : Q) :
    p ≾ₘᵤₛₜ q <-> pre_extensional outcome p q.
  Proof.
    erewrite equivalence_fw_bhv_acc_ctx.
    rewrite equivalence_bhv_acc_mst;eauto.
  Qed.

  (** ** The must-set characterisation on FW is equivalent to the inductive must preorder *)
  Corollary equivalence_fw_must_set_and_must_i (p : P) (q : Q) :
    p ≾ₘᵤₛₜ q <-> p ⊑ₘᵤₛₜᵢ q.
  Proof.
    split.
    - intros hpre. eapply soundness_fw.
      now eapply equivalence_bhv_acc_mst.
    - intros hpre. eapply completeness_fw in hpre.
      now eapply equivalence_bhv_acc_mst.
  Qed.

  End FWⁿ.
  (** ---- *)
  Section Lⁿ.

  Context `{!gLtsObaFB P A, !FiniteOutputChain_LtsOba P}.
  Context `{!gLtsObaFB Q A, !FiniteOutputChain_LtsOba Q}.
  Context `{!gLtsObaFB T A, !FiniteOutputChain_LtsOba T}.

  (** ** The must-set characterisation on toFW is equivalent to the inductive must preorder *)
  Corollary equivalence_must_set_and_must_i (p : P) (q : Q) :
    p ⊑ₘᵤₛₜᵢ q <-> (p, ∅) ≾ₘᵤₛₜ (q, ∅).
  Proof.
    split.
    - intros hpre. eapply equivalence_bhv_acc_mst.
      eapply lift_fw_ctx_pre , completeness_fw in hpre. eauto.
    - intros hpre%equivalence_bhv_acc_mst.
      eapply lift_fw_ctx_pre.
      eapply soundness_fw; eauto.
  Qed.

  (** ---- *)

  (** ** The inductive characterisation on toFW is equivalent to the extensional must preorder *)
  Corollary equivalence_must_set_and_must_e (p : P) (q : Q) :
    pre_extensional outcome p q <-> (p, ∅) ≾ₘᵤₛₜ (q, ∅).
  Proof.
    rewrite pre_extensional_eq. apply equivalence_must_set_and_must_i.
  Qed.

  End Lⁿ.

End must_set_preorder.
