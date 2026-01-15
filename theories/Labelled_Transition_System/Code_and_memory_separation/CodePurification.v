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

From Coq.Program Require Import Equality.
From stdpp Require Import base countable finite gmap list 
                        finite base decidable finite gmap gmultiset.
From Must Require Import MultisetHelper ForAllHelper gLts Bisimulation Lts_OBA.


(****************************** Reduction to pure code, code purification **********************************)

Reserved Notation "p ⟿{ m } q" (at level 30, format "p  ⟿{ m }  q").

Inductive strip `{gLtsEq P A} : P -> gmultiset A -> P -> Prop :=
| strip_nil p p'(eq : p ⋍ p') : p ⟿{∅} p'
| strip_step p1 p2 p3 η m :
  non_blocking η -> p1 ⟶[η] p2 -> p2 ⟿{m} p3 -> p1 ⟿{{[+ η +]} ⊎ m} p3

where "p ⟿{ m } q" := (strip p m q).

Notation "p ⟿⋍{ m } q" := (∃ r, p ⟿{m} r /\ r ⋍ q) (at level 30).

(** Lemmas about strip. *)

Lemma strip_eq `{@gLtsOba P A H gLtsP LOA} {e e' m} :
  e ⟿{m} e' -> ∀ r, r ⋍ e
    -> r ⟿⋍{ m } e'.
Proof.
  intro w.
  dependent induction w; intros r heq.
  - exists r. split. constructor. reflexivity. etransitivity; eauto.
  - assert (r ⟶⋍[η] p2) as (r0 & l0 & heq0).
    { eapply eq_spec. eexists; eauto. }
    destruct (IHw r0 heq0) as (r' & hwo' & heq').
    exists r'. split. eapply strip_step; eassumption. eassumption.
Qed.

Lemma strip_mem_ex `{gLtsOba P A} {p1 p2 m η} :
  p1 ⟿{{[+ η +]} ⊎ m} p2
    -> (∃ p', p1 ⟶[η] p' /\ non_blocking η).
Proof.
  intros hw.
  dependent induction hw.
  - multiset_solver.
  - assert (mem : η ∈ {[+ η0 +]} ⊎ m0). rewrite x. multiset_solver.
    eapply gmultiset_elem_of_disj_union in mem as [here | there].
    + eapply gmultiset_elem_of_singleton in here. subst. firstorder.
    + edestruct IHhw as (p & HypTr & nb) ; eauto.
      eapply gmultiset_disj_union_difference' in there; eassumption.
      edestruct (lts_oba_non_blocking_action_delay H2 H1 HypTr) as (u & l2 & l3).
      eauto.
Qed.

Lemma strip_eq_step `{gLtsOba P A} {e e' m η} :
  e ⟿{{[+ η +]} ⊎ m} e' -> ∀ r, e ⟶[η] r
    -> r ⟿⋍{m} e'.
Proof.
  intro w.
  dependent induction w.
  - multiset_solver.
  - intros r l.
    destruct (decide (η = η0)); subst.
    + assert (eq_rel p2 r) by (eapply lts_oba_non_blocking_action_deter; eassumption).
      eapply gmultiset_disj_union_inj_1 in x. subst.
      eapply strip_eq. eassumption. symmetry. assumption.
    + assert (m0 = {[+ η +]} ⊎ m ∖ {[+ η0 +]}) by multiset_solver.
      assert (η ≠ η0) by set_solver.
      edestruct (lts_oba_non_blocking_action_confluence H2 H4 H1 l)
        as (t0 & l0 & (r1 & l1 & heq1)).
      eapply IHw in H3 as (t & hwo & heq); eauto.
      assert (mem : η0 ∈ m) by multiset_solver.
      eapply gmultiset_disj_union_difference' in mem. rewrite mem.
      edestruct (strip_eq hwo r1 heq1) as (t2 & hw2 & heq2).
      exists t2. split. eapply strip_step. eassumption. eassumption. eassumption.
      etrans; eassumption.
Qed.

Lemma strip_m_deter `{gLtsOba P A} {m p p1 p2} :
  p ⟿{m} p1 -> p ⟿{m} p2
    -> p1 ⋍ p2.
Proof.
  revert p p1 p2.
  induction m using gmultiset_ind; intros p p1 p2 hw1 hw2.
  - inversion hw1; inversion hw2; subst; try multiset_solver. 
    eapply symmetry in eq. etransitivity; eauto.
  - destruct (strip_mem_ex hw1) as (t1 & lt1). destruct lt1 as [ lt1 nb1].
    destruct (strip_mem_ex hw2) as (t2 & lt2). destruct lt2 as [ lt2 nb2].
    eapply strip_eq_step in hw1 as (r1 & hwr1 & heqr1); eauto.
    eapply strip_eq_step in hw2 as (r2 & hwr2 & heqr2); eauto.
    etrans. symmetry. eassumption.
    symmetry. etrans. symmetry. eassumption. eauto.
Qed.

Lemma strip_eq_sim `{gLtsOba P A} {p q p' q' m} :
  p ⋍ q -> p ⟿{m} p' -> q ⟿{m} q' -> p' ⋍ q'.
Proof.
  intros heq hsp hsq.
  edestruct (strip_eq hsq) as (r & hsp' & heqr); eauto.
  transitivity r. eapply strip_m_deter; eauto. eassumption.
Qed.

Lemma lts_oba_mo_strip `{gLtsOba P A} p : 
  ∃ q , p ⟿{lts_oba_mo p} q.
Proof.
  remember (lts_oba_mo p) as ns.
  revert p Heqns.
  induction ns using gmultiset_ind; intros.
  - exists p. constructor. reflexivity.
  - assert (mem : x ∈ lts_oba_mo p) by multiset_solver.
    assert (exists q, non_blocking x /\ p ⟶[x] q) as (q & l).
    eapply lts_oba_mo_spec_bis2 in mem as (q & hl); destruct hl ; eauto.
    destruct l as [nb l]. set (h := lts_oba_mo_spec2 p x q nb l) in mem.
    assert (ns = lts_oba_mo q) as eq. rewrite <- Heqns in h. multiset_solver.
    eapply IHns in eq as (q0 & hw).
    exists q0. eapply strip_step; eassumption.
Qed.

Lemma strip_retract_act `{gLtsOba P A} {p q m t α} :
  p ⟿{m} q -> q ⟶{α} t -> ∃ r, p ⟶{α} r /\ r ⟿⋍{m} t.
Proof.
  intros HypStrip HypTr. 
  induction HypStrip as [| ? ? ? ? ? nb HypTr' ?  InductionHyp]; eauto.
  + edestruct (eq_spec p t) as (t' & l & equiv). exists p'. split; eauto.
    exists t'. repeat split; eauto. exists t'. split; eauto. constructor;eauto. reflexivity.
  + eapply InductionHyp in HypTr as (r & l & t' & hwo & heq).
    edestruct (lts_oba_non_blocking_action_delay nb HypTr' l) as (u & l1 & (r' & lr' & heqr')).
    edestruct (strip_eq hwo _ heqr') as (t0 & hwo0 & heq0).
    exists u. repeat split; eauto. exists t0. split; eauto. eapply strip_step; eassumption.
    etrans. eassumption. now symmetry.
Qed.

Lemma strip_delay_action_not_in_m `{gLtsOba P A} {p q m t μ} :
  μ ∉ m -> p ⟿{m} q -> p ⟶[μ] t
    -> ∃ r, q ⟶[μ] r.
Proof.
  intros not_in_mem HypStrip HypTr. revert t not_in_mem HypTr.
  induction HypStrip as [? ? equiv| ? ? ? ? ? nb HypTr' HypStrip]. 
  + intros. symmetry in equiv. 
    edestruct (eq_spec p' t) as (p'' & l' & equiv'). exists p. split; eauto.
    exists p''. eauto.
  + intros.
    assert (neq : μ ≠ η /\ μ ∉ m) by now multiset_solver. destruct neq as [neq not_in].
    edestruct (lts_oba_non_blocking_action_confluence nb neq HypTr' HypTr) as (r & l1 & l2). eauto.
Qed.

Lemma strip_delay_m `{gLtsOba P A} {p q m t μ} :
  μ ∉ m -> p ⟿{m} q -> p ⟶[μ] t
    -> ∃ r, t ⟿{m} r.
Proof.
  intros Hyp hwp hlp. revert p q t μ Hyp hwp hlp.
  induction m using gmultiset_ind; intros.
  - inversion hwp.
    + subst. exists t. eapply strip_nil. reflexivity.
    + multiset_solver.
  - eapply strip_mem_ex in hwp as h0.
    destruct h0 as (e & hle). destruct hle as [hle nb].
    assert (neq : μ ≠ x /\ μ ∉ m) by now multiset_solver. destruct neq as [neq not_in].
    edestruct (lts_oba_non_blocking_action_confluence nb neq hle hlp) as (u & l2 & l3).
    destruct l3 as (v & hlv & heqv).
    eapply strip_eq_step in hle as h1; eauto. destruct h1 as (r & hwr & heqr).
    destruct (IHm _ _ _ _ not_in hwr l2) as (r0 & hwu).
    edestruct (strip_eq hwu v heqv) as (w & hww & heqw).
    exists w. eapply strip_step; eauto.
Qed. 

Lemma strip_after `{gLtsOba P A} {p q m} :
  p ⟿{m} q -> lts_oba_mo p = m ⊎ lts_oba_mo q.
Proof.
  intros hwp. revert p q hwp.
  induction m using gmultiset_ind; intros.
  - inversion hwp; subst. 
    -- assert (∅ ⊎ lts_oba_mo q = lts_oba_mo q) as mem by multiset_solver.
       rewrite mem. eapply lts_oba_mo_eq; eauto.
    -- multiset_solver.
  - eapply strip_mem_ex in hwp as h0.
    destruct h0 as (e & hle). destruct hle as [hle nb].
    eapply strip_eq_step in hle as h1; eauto. destruct h1 as (r & hwr & heqr).
    eapply lts_oba_mo_spec2 in hle.
    rewrite hle. eapply IHm in hwr.
    rewrite hwr.
    rewrite gmultiset_disj_union_assoc.
    eapply gmultiset_eq_pop_l.
    eapply lts_oba_mo_eq. eassumption. eassumption.
Qed.

Lemma strip_aux2 `{gLtsOba P A} {p q q' m} :
  p ⋍ q -> q ⟿{m} q'
    -> p ⟿⋍{m} q'.
Proof.
  intros hwp1 hwp. revert p hwp1.
  dependent induction hwp; intros.
  - exists p. split; eauto. constructor. eauto.
  - edestruct (eq_spec p p2) as (p' & l & equiv). exists p1. split; eauto.
    edestruct (IHhwp p') as (p'3 & stripped & equiv'); eauto.
    exists p'3.
    split. econstructor; eauto. eauto.
Qed.

Lemma strip_aux1 `{gLtsOba P A} {p q t m1 m2} :
  p ⟿{m1} t -> p ⟿{m1 ⊎ m2} q
    -> t ⟿⋍{m2} q.
Proof.
  intros hwp1 hwp. revert q m2 hwp.
  dependent induction hwp1; intros.
  - rewrite gmultiset_disj_union_left_id in hwp.
    symmetry in eq. eapply strip_aux2 in eq; eauto.
  - rewrite <- gmultiset_disj_union_assoc in hwp.
    eapply strip_eq_step in hwp as (r1 & hwr1 & heqr1); eauto.
    destruct (IHhwp1 _ _ hwr1) as (u & hwp3 & hequ).
    exists u. split. eassumption. transitivity r1; eauto.
Qed.

Lemma strip_delay_inp4 `{gLtsOba P A} {p q t β} :
  blocking β -> p ⟶[β] t -> t ⟿{lts_oba_mo p} q
    -> ∃ r, p ⟿{lts_oba_mo p} r /\ r ⟶⋍[β] q.
Proof.
  intros Not_nb hlp hwt.
  remember (lts_oba_mo p) as pmo.
  revert p q t β Not_nb hwt hlp Heqpmo.
  induction pmo using gmultiset_ind; intros.
  - inversion hwt.
    + subst. exists p. split. eapply strip_nil. reflexivity. exists t. split. assumption. eauto.
    + multiset_solver.
  - assert (mem : x ∈ lts_oba_mo p) by multiset_solver.
    eapply lts_oba_mo_spec_bis2 in mem as (p1 & hlp1). destruct hlp1 as [nb hlp1].
    assert (neq : β ≠ x).  eapply BlockingAction_are_not_non_blocking; eauto.
    edestruct (lts_oba_non_blocking_action_confluence nb neq hlp1 hlp) as (u & l2 & l3).
    destruct l3 as (u' & hlu & hequ).
    eapply strip_eq_step in hlu as h1; eauto. destruct h1 as (r & hwr & heqr).
    edestruct (strip_eq hwr u (symmetry hequ)) as (r' & hwu & heqr').
    eapply lts_oba_mo_spec2 in hlp1 as hmop.
    assert (hmoeq : pmo = lts_oba_mo p1) by multiset_solver.
    destruct (IHpmo p1 r' u β Not_nb hwu l2 hmoeq) as (pt & hwpt & hlpt).
    exists pt. split. eapply strip_step; eauto.
    destruct hlpt as (r0 & hlpt & heqt0).
    exists r0. split. eassumption.
    transitivity r'. eassumption.
    transitivity r. eassumption. eassumption. eassumption.
Qed.

Lemma strip_delay_tau `{gLtsOba P A} {p q m t} :
  p ⟿{m} q -> p ⟶ t
    -> (∃ η μ r, dual μ η /\ non_blocking η /\ p ⟶[η] r /\ r ⟶⋍[μ] t) \/ (∃ r w, q ⟶ r /\ t ⟿{m} w /\ w ⋍ r).
Proof.
  intros hr hl. revert t hl.
  induction hr as [| ? ? ? ? ? nb HypTr' ?]; intros.
  + right. edestruct (eq_spec p' t) as (p'' & l & equiv). symmetry in eq. exists p. split;eauto.
    exists p'', t. repeat split; eauto. eapply strip_nil. reflexivity. symmetry; eauto.
  + edestruct (lts_oba_non_blocking_action_tau nb HypTr' hl) as [(r & l1 & l2)|].
    ++ eapply IHhr in l1 as [(b & c & r' & duo & nb' & l3 & l4) |(u, (w, (hu & hw & heq)))].
       +++ edestruct (lts_oba_non_blocking_action_delay nb HypTr' l3) as (z & l6 & l7).
           left. exists b, c , z. split. assumption. split. assumption. split. assumption.
           destruct l7 as (t0 & hlt0 & eqt0).
           destruct l4 as (t1 & hlt1 & eqt1).
           assert (t0 ⟶⋍[c] t1) as (t2 & hlt2 & eqt2).
           { eapply eq_spec; eauto. }
           edestruct (lts_oba_non_blocking_action_delay nb hlt0 hlt2) as (w & lw1 & lw2).
           exists w. split. assumption.
           destruct l2 as (v1 & hlv1 & heqv1).
           destruct lw2 as (u1 & hlu1 & hequ1).
           eapply (lts_oba_non_blocking_action_deter_inv η); try eassumption. 
           etrans. eassumption.
           etrans. eassumption.
           etrans. eassumption.
           now symmetry.
       +++ right.
           destruct l2 as (r' & hlr' & heqr').
           destruct (strip_eq hw _ heqr') as (w' & hww' & heqw').
           exists u, w'. repeat split. assumption. eapply strip_step; eauto.
           etrans; eauto.
    ++ destruct H1 as (μ & duo & r & hlr & heq).
       left. exists η, μ. exists p2. split; eauto. split. eassumption. split. eauto. exists r. eauto.
Qed.

Lemma woutpout_delay_inp `{gLtsOba P A} {p q m t μ} : 
  Forall (NotEq μ) (elements m) -> p ⟿{m} q -> p ⟶[μ] t 
    -> ∃ r, q ⟶[μ] r.
Proof.
  intros noteq_l stripped Hstep. revert t noteq_l Hstep. 
  induction stripped as [ | ? ? ? ? ? nb Hstep_nb]; intros.
  + symmetry in eq. edestruct (eq_spec p' t) as (p'' & l & equiv). exists p; eauto.
    exists p''; eauto. 
  + assert ((NotEq μ η) /\ (Forall (NotEq μ) (elements m))) as subeq_l.
    eapply simpl_P_in_l; eauto.
    destruct subeq_l as [neq Hyp].
    edestruct (lts_oba_non_blocking_action_confluence nb neq Hstep_nb Hstep) as (r & l1 & l2). eauto.
Qed.

Lemma nb_with_strip `{gLtsOba P A} p1 m p'1 η:
  p1 ⟿{m} p'1 -> η ∈ m 
    -> non_blocking η.
Proof.
  intros stripped mem.
  dependent induction stripped.
  + multiset_solver.
  + destruct (decide (η = η0)) as [eq | not_eq]; subst.
    ++ eauto.
    ++ assert (η ∈ m). multiset_solver.
       eapply IHstripped. eauto.
Qed.

Lemma woutpout_preserves_mu `{gLtsOba P A} {p q m t α} :
  p ⟿{m} q -> q ⟶{α} t 
    -> ∃ r t', p ⟶{α} r /\ r ⟿{m} t' /\ t ⋍ t'.
Proof.
  intros stripped Hstep. induction stripped as [ | ? ? ? ? ? nb Hstep_nb ]; eauto.
  - edestruct (eq_spec p t) as (p'' & l & equiv). exists p'; eauto.
    exists p'', t. repeat split; eauto. constructor. eauto. reflexivity.
  - eapply IHstripped in Hstep as (r & t' & l & hwo & heq).
    edestruct (lts_oba_non_blocking_action_delay nb Hstep_nb l) as (u & l1 & (r' & lr' & heqr')).
    edestruct (strip_eq hwo _ heqr') as (t0 & hwo0 & heq0).
    exists u, t0. repeat split; eauto. eapply strip_step; eassumption.
    etrans. eassumption. now symmetry.
Qed.

Lemma not_nb_with_strip_m `{gLtsOba P A} p1 m p'1 β :
  p1 ⟿{m} p'1 -> blocking β
    -> Forall (NotEq β) (elements m).
Proof.
  intros stripped.
  dependent induction stripped.
  + multiset_solver.
  + intro. eapply simpl_P_in_l. split; eauto.
       eapply BlockingAction_are_not_non_blocking; eauto.
Qed.

Lemma woutpout_delay_tau `{gLtsOba P A} {p q m t} :
  p ⟿{m} q -> p ⟶ t 
    -> (∃ η μ r t, non_blocking η /\ dual μ η /\ p ⟶[η] r /\ q ⟶[μ] t) \/ (∃ r, q ⟶ r).
Proof.
  intros stripped Hstep. revert t Hstep.
  induction stripped as [ | ? ? ? ? ? nb Hstep_nb]; intros.
  + symmetry in eq. edestruct (eq_spec p' t) as (p'' & l & equiv). exists p; eauto.
    right. exists p''; eauto.
  + edestruct (lts_oba_non_blocking_action_tau nb Hstep_nb Hstep) 
    as [(r & l1 & l2)| (μ & duo & r & hlr & heq)].
    ++ eapply IHstripped in l1 as [(b & t' & r' & l3 & l4)|].
       * destruct l4 as (nb' & duo' & Hstep_nb' & Hstep').
         edestruct (lts_oba_non_blocking_action_delay nb Hstep_nb Hstep_nb') as (z & l6 & l7).
         left. 
         exists b. exists t'. exists z. exists l3.
         eauto.
       * right. eauto.
    ++ left. exists η. 
       exists μ. exists p2.
       assert (blocking μ) as not_nb.
       eapply dual_blocks; eauto.
       assert (Forall (NotEq μ) (elements m)) as simpl_in_l.
       eapply not_nb_with_strip_m; eauto.
       eapply woutpout_delay_inp in hlr as (u & lu) ; eauto.
Qed.

Lemma aux0 `{gLtsOba P A} {e e' m} :
  ∀ η, η ∈ m -> e ⟿{m} e'
    -> ∃ e', e ⟶[η] e'.
Proof.
  intros a mem w.
  dependent induction w.
  - multiset_solver.
  - eapply gmultiset_elem_of_disj_union in mem as [here | there].
    + eapply gmultiset_elem_of_singleton in here. subst. firstorder.
    + eapply IHw in there as (q & l).
      edestruct (lts_oba_non_blocking_action_delay H1 H2 l) as (u & l2 & l3). eauto.
Qed.

Lemma aux3_ `{@gLtsOba P A H gLtsP LOA} {e e' m η} :
  e ⟿{{[+ η +]} ⊎ m} e' -> ∀ r, e ⟶[η] r
    -> r ⟿⋍{m} e'.
Proof.
  intro w.
  dependent induction w.
  - multiset_solver.
  - intros r l.
    destruct (decide (η = η0)); subst.
    + assert (eq_rel p2 r) by (eapply lts_oba_non_blocking_action_deter; eassumption).
      eapply gmultiset_disj_union_inj_1 in x. subst.
      eapply strip_eq. eassumption. symmetry. assumption.
    + assert (m0 = {[+ η +]} ⊎ m ∖ {[+ η0 +]}) by multiset_solver.
      assert (η ≠ η0) as neq by set_solver.
      edestruct (lts_oba_non_blocking_action_confluence H2 neq H1 l) as (t0 & l0 & (r1 & l1 & heq1)).
      eapply IHw in H3 as (t & hwo & heq); eauto.
      assert (mem : η0 ∈ m) by multiset_solver.
      eapply gmultiset_disj_union_difference' in mem. rewrite mem.
      edestruct (strip_eq hwo r1 heq1) as (t2 & hw2 & heq2).
      exists t2. split. eapply strip_step. eassumption. eassumption. eassumption.
      etrans; eassumption.
Qed.

Lemma mo_stripped_equiv `{gLtsOba P A} r m r' r'' : 
  r ⟿{m} r' -> r' ⋍ r'' 
    -> r ⟿{m} r''.
Proof.
  intros stripped Hyp. revert Hyp.
  induction stripped.
  + intro Hyp. constructor. etransitivity; eauto. 
  + intro Hyp. econstructor; eauto.
Qed.

Lemma mo_stripped_equiv_rev `{gLtsOba P A} r m r' r'' : 
  r ⟿{m} r' -> r ⋍ r'' 
    -> r'' ⟿{m} r'.
Proof.
  intros stripped eq. revert eq. revert r''.
  induction stripped.
  + intro Hyp. constructor. symmetry. symmetry in eq. etransitivity; eauto. 
  + intros r'' eq. symmetry in eq. 
    edestruct (eq_spec r'' p2) as (r''' & l & equiv). exists p1; eauto.
    econstructor. assumption. exact l. eapply IHstripped. symmetry;eauto.
Qed.

Lemma strip_union `{gLtsOba P A} p1 m1 p2 m2 p3 : 
  p1 ⟿{m1} p2 -> p2 ⟿{m2} p3 
    -> p1 ⟿{m1 ⊎ m2} p3.
Proof.
  intro stripped.
  dependent induction stripped.
  + intro. assert (∅ ⊎ m2 = m2) as mem. multiset_solver. rewrite mem.
    symmetry in eq. eapply mo_stripped_equiv_rev; eauto. 
  + intro stripped'. assert ({[+ η +]} ⊎ m ⊎ m2 = {[+ η +]} ⊎ (m ⊎ m2)) as eq. multiset_solver.
    rewrite eq. econstructor; eauto.
Qed.

Lemma mo_stripped `{gLtsOba P A} r m r' : 
  r ⟿{m} r' -> (∀ η : A, non_blocking η -> r' ↛[η]) 
    -> lts_oba_mo r = m. 
Proof.
  revert r r'.
  induction m using gmultiset_ind.
  + intros r r' stripped Hyp. inversion stripped; subst. 
    ++ destruct (decide (lts_oba_mo r = ∅)) as [empty | not_empty].
       -- assumption.
       -- eapply gmultiset_choose in not_empty. destruct not_empty as (η & mem).
          eapply lts_oba_mo_spec_bis2 in mem. destruct mem as (p2 & nb & l).
          eapply Hyp in nb. symmetry in eq. edestruct (eq_spec r' p2) as (r'' & l' & equiv').
          exists r; split; eauto. 
          assert (¬ r' ↛[η]). eapply lts_refuses_spec2; exists r''; eauto. contradiction.
    ++ multiset_solver.
  + intros r r' stripped Hyp.
    assert (exists r'', r ⟶[x] r'') as (r'' & HypTr).
    eapply aux0; eauto. set_solver.
    assert (r ⟿{{[+ x +]} ⊎ m} r') as des; eauto.
    eapply aux3_ in stripped as (t'' & stripped'' & eq); eauto.
    eapply IHm in stripped''; eauto.
    rewrite<- stripped''.
    eapply lts_oba_mo_spec2; eauto.
    eapply nb_with_strip in des. exact des. set_solver.
    intros. eapply refuses_preserved_by_eq; eauto. symmetry. eauto.
Qed.

Lemma lts_oba_mo_strip_refuses `{gLtsOba P A} p q: 
  strip p (lts_oba_mo p) q 
  -> forall η, non_blocking η -> q ↛[η].
Proof.
  intros w.
  dependent induction w.
  - intros η nb.
    destruct (decide (p ↛[η])) as [refuses | accepts].
    + eapply refuses_preserved_by_eq; eauto.
    + eapply lts_refuses_spec1 in accepts as (q & l).
      eapply lts_oba_mo_spec_bis1 in l; eauto. multiset_solver.
  - eapply lts_oba_mo_spec2 in H2. rewrite <- x in H2.
    eapply gmultiset_disj_union_inj_1 in H2. eauto. eassumption.
Qed. 



