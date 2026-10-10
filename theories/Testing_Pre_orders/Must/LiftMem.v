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

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Program Require Import Equality.
From stdpp Require Import base countable decidable gmap gmultiset.
From TestingTheory Require Import ActTau ForAllHelper gLts Bisimulation Lts_OBA Lts_OBA_FB Lts_Finite_Output_Chain
  Testing_Predicate StateTransitionSystems InteractionBetweenLts MultisetLTSConstruction CodePurification
  SyncActions MemAction InteractionUnion MemForwarder ForwarderMem Must CompletenessASsync.

#[local] Hint Mode ExtAction ! : typeclass_instances.

Section ForwarderSteps.

Context `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest} `{SA : !SyncAction Aproc Atest}.
Context `{gLtsEqP : !gLtsEq P Hp}.
Context `{PIP : !Prop_of_Inter P (MO (MemAct Atest)) Aproc (MemAct Atest) fw_inter_mem}.

#[local] Existing Instance toFwEq.

Lemma mem_msg_inv (m m' : MO (MemAct Atest)) (η : Atest) :
  m ⟶[msg η] m' → m = {[+ msg η +]} ⊎ m' ∧ non_blocking η.
Proof.
  intros l. inversion l as [m0 x μ duo nbx | m0 x nbx]; subst.
  - destruct x; simpl in *; done.
  - done.
Qed.

Lemma mem_cobar_inv (m m' : MO (MemAct Atest)) (η : Atest) :
  m ⟶[cobar η] m' → m' = {[+ msg η +]} ⊎ m ∧ non_blocking η.
Proof.
  intros l. inversion l as [m0 x μ duo nbx | m0 x nbx]; subst.
  - destruct x as [η' | η']; simpl in duo, nbx; [| done]. by subst.
  - done.
Qed.

Lemma fw_tau_left (p p' : P) (m : MO (MemAct Atest)) : p ⟶ p' → (p, m) ⟶ (p', m).
Proof. intros l. by apply (ParLeft τ). Qed.

Lemma fw_inl (p p' : P) (m : MO (MemAct Atest)) (μ : Aproc) :
  p ⟶[μ] p' → (p, m) ⟶[inl μ] (p', m).
Proof. intros l. by apply (ParLeft (ActExt (inl μ))). Qed.

Lemma fw_consume (p p' : P) (m : MO (MemAct Atest)) (μ : Aproc) (η : Atest) :
  p ⟶[μ] p' → sync μ η → non_blocking η → (p, {[+ msg η +]} ⊎ m) ⟶ (p', m).
Proof.
  intros l hs nb. apply (ParSync (inl μ) (inr (msg η))); [by split | exact l |].
  by apply (lts_multiset_minus m (msg η)).
Qed.

Lemma fw_give (p : P) (m : MO (MemAct Atest)) (η : Atest) :
  non_blocking η → (p, {[+ msg η +]} ⊎ m) ⟶[inr (msg η)] (p, m).
Proof. intros nb. apply (ParRight (ActExt (inr (msg η)))). by apply (lts_multiset_minus m (msg η)). Qed.

Lemma fw_recv (p : P) (m : MO (MemAct Atest)) (η : Atest) :
  non_blocking η → (p, m) ⟶[inr (cobar η)] (p, {[+ msg η +]} ⊎ m).
Proof. intros nb. apply (ParRight (ActExt (inr (cobar η)))). by apply (lts_multiset_add m (msg η) (cobar η)). Qed.

Lemma fw_tau_inv (p : P) (m : MO (MemAct Atest)) y :
  (p, m) ⟶ y →
    (∃ p', y = (p', m) ∧ p ⟶ p')
  ∨ (∃ p' μ η m', y = (p', m') ∧ p ⟶[μ] p' ∧ sync μ η ∧ non_blocking η ∧ m = {[+ msg η +]} ⊎ m').
Proof.
  intros l.
  inversion l as [α s1 s'1 s2 l1 | α s1 s2 s'2 l2 | a1 a2 s1 s'1 s2 s'2 hs l1 l2]; subst.
  - left. by exists s'1.
  - inversion l2.
  - right. destruct a1 as [μ | ], a2 as [ | [η | η]]; simpl in hs; try done.
    destruct hs as [hs nb]. apply mem_msg_inv in l2 as [-> _].
    by exists s'1, μ, η, s'2.
Qed.

Lemma fw_inl_inv (p : P) (m : MO (MemAct Atest)) (μ : Aproc) y :
  (p, m) ⟶[inl μ] y → ∃ p', y = (p', m) ∧ p ⟶[μ] p'.
Proof.
  intros l. inversion l as [α s1 s'1 s2 l1 | α s1 s2 s'2 l2 |]; subst; [| done].
  by exists s'1.
Qed.

Lemma fw_msg_inv (p : P) (m : MO (MemAct Atest)) (η : Atest) y :
  (p, m) ⟶[inr (msg η)] y → ∃ m', y = (p, m') ∧ m = {[+ msg η +]} ⊎ m' ∧ non_blocking η.
Proof.
  intros l. inversion l as [α s1 s'1 s2 l1 | α s1 s2 s'2 l2 |]; subst; [done |].
  apply mem_msg_inv in l2 as [-> nb]. by exists s'2.
Qed.

Lemma fw_cobar_inv (p : P) (m : MO (MemAct Atest)) (η : Atest) y :
  (p, m) ⟶[inr (cobar η)] y → y = (p, {[+ msg η +]} ⊎ m) ∧ non_blocking η.
Proof.
  intros l. inversion l as [α s1 s'1 s2 l1 | α s1 s2 s'2 l2 |]; subst; [done |].
  apply mem_cobar_inv in l2 as [-> nb]. by split.
Qed.

Lemma msg_in_mem (m m' : MO (MemAct Atest)) (η : Atest) :
  m = {[+ msg η +]} ⊎ m' → msg η ∈ m.
Proof. intros ->. multiset_solver. Qed.

End ForwarderSteps.

Section LiftMem.

Context `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest} `{SA : !SyncAction Aproc Atest}.
Context `{gLtsEqP : !gLtsEq P Hp}.
Context `{gLtsEqT : !gLtsEq T Ht} `{gLtsObaT : !gLtsOba T} `{!gLtsObaFB T Atest}
        `{!FiniteOutputChain_LtsOba T}.
Context (outcome : T → Prop) `{!Testing_Predicate outcome gLtsEqT}.
Context `{PIP : !Prop_of_Inter P (MO (MemAct Atest)) Aproc (MemAct Atest) fw_inter_mem}.
Context `{PIPT : !Prop_of_Inter P T Aproc Atest sync}.

#[local] Existing Instance toFwEq.

Context `{PIFT : !Prop_of_Inter (P * MO (MemAct Atest)) T (Aproc + MemAct Atest) Atest sync}.

Notation mmsg m := (gmultiset_map msg m).

Lemma msg_in_map (m : gmultiset Atest) (m' : MO (MemAct Atest)) (η : Atest) :
  mmsg m = {[+ msg η +]} ⊎ m' → η ∈ m.
Proof.
  intros heq. apply msg_in_mem in heq.
  apply elem_of_gmultiset_map in heq as (x & hx & hm). by injection hx as ->.
Qed.

Lemma nf_must_fw_l (m1 : gmultiset Atest) (m2 : MO (MemAct Atest)) (p : P) (e e' : T) :
  e ⟿{m1} e' → (p, mmsg m1 ⊎ m2) must_pass e' → (p, m2) must_pass e.
Proof.
  revert p e e' m2.
  induction m1 as [| x m1 IH] using gmultiset_ind; intros p e e' m2 hmo hm.
  - inversion hmo as [? ? heq | ? ? ? ? ? ? ? ? Heq]; subst; [| multiset_solver].
    rewrite gmultiset_map_empty, gmultiset_disj_union_left_id in hm.
    eapply must_eq_client; [symmetry; exact heq | exact hm].
  - assert (nb : non_blocking x) by (eapply nb_with_strip; [exact hmo | multiset_solver]).
    assert (mem : x ∈ {[+ x +]} ⊎ m1) by multiset_solver.
    destruct (aux0 x mem hmo) as (e0 & l0).
    destruct (aux3_ hmo e0 l0) as (t & hwo & heq).
    eapply (must_non_blocking_action_swap_l_fw_sync_eq outcome (p, {[+ msg x +]} ⊎ m2) (p, m2) e e0 x nb).
    + exists (p, m2). split; [by apply fw_give | reflexivity].
    + exists e0. split; [exact l0 | reflexivity].
    + eapply IH; [exact hwo |].
      eapply must_eq_client; [symmetry; exact heq |].
      rewrite gmultiset_map_disj_union, gmultiset_map_singleton in hm.
      by replace (mmsg m1 ⊎ ({[+ msg x +]} ⊎ m2)) with ({[+ msg x +]} ⊎ mmsg m1 ⊎ m2) by multiset_solver.
Qed.

Lemma nf_must_fw_r (p : P) (e e' : T) (m1 : gmultiset Atest) (m2 : MO (MemAct Atest)) :
  e ⟿{m1} e' → (p, m2) must_pass e → (p, mmsg m1 ⊎ m2) must_pass e'.
Proof.
  intros hwo. revert p m2.
  induction hwo as [e e' heq | e1 e2 e3 η m nb l w IH]; intros q m2 hm.
  - rewrite gmultiset_map_empty, gmultiset_disj_union_left_id.
    by eapply must_eq_client.
  - assert (hm' : (q, {[+ msg η +]} ⊎ m2) must_pass e2).
    { destruct hm as [happy | nh ex pt et com].
      - apply m_now. by eapply outcome_preserved_by_lts_non_blocking_action.
      - eapply com; [| by apply fw_recv | exact l]. reflexivity. }
    rewrite gmultiset_map_disj_union, gmultiset_map_singleton.
    replace ({[+ msg η +]} ⊎ mmsg m ⊎ m2) with (mmsg m ⊎ ({[+ msg η +]} ⊎ m2)) by multiset_solver.
    by apply IH.
Qed.

Lemma nf_must_fw (p : P) (e e' : T) (m : gmultiset Atest) :
  e ⟿{m} e' → (p, mmsg m) must_pass e' ↔ (p, ∅) must_pass e.
Proof.
  intros hwo. split; intros hm.
  - eapply nf_must_fw_l; [exact hwo |]. by rewrite gmultiset_disj_union_right_id.
  - rewrite <- (gmultiset_disj_union_right_id (mmsg m)). by eapply nf_must_fw_r.
Qed.

Lemma must_to_must_fw (p : P) (e : T) :
  p must_pass e → ∀ e', e ⟿{lts_oba_mo e} e' → (p, mmsg (lts_oba_mo e)) must_pass e'.
Proof.
  intros hm.
  induction hm as [p e happy | p e nh ex pt IHpt et IHet com IHcom]; intros e' hmo.
  - apply m_now. by eapply woutpout_preserves_outcome.
  - apply m_step.
    + intros h. apply nh. by eapply woutpout_preserves_outcome_converse.
    + destruct ex as (y & l).
      destruct (par_view_of p e y l) as [p' lp | e0 le | p' e0 μ ζ hs l1 l2].
      * exists ((p', mmsg (lts_oba_mo e)), e'). apply par_step_left. by apply fw_tau_left.
      * destruct (woutpout_delay_tau hmo le) as [(η & μ & r & t & nb & duo & l1 & l2) | (e'' & l')].
        -- rewrite (lts_oba_mo_spec2 e η r nb l1), gmultiset_map_disj_union, gmultiset_map_singleton.
           exists ((p, mmsg (lts_oba_mo r)), t).
           eapply (par_step_sync _ _ _ _ (inr (msg η)) μ);
             [exact (proj2 (msg_spec (Aproc := Aproc) η nb) μ duo) | by apply fw_give | exact l2].
        -- exists ((p, mmsg (lts_oba_mo e)), e''). by apply par_step_right.
      * destruct (decide (non_blocking ζ)) as [nb | nnb].
        -- rewrite (lts_oba_mo_spec2 e ζ e0 nb l2), gmultiset_map_disj_union, gmultiset_map_singleton.
           exists ((p', mmsg (lts_oba_mo e0)), e'). apply par_step_left. by apply (fw_consume p p' _ μ ζ).
        -- assert (hnot : Forall (NotEq ζ) (elements (lts_oba_mo e)))
             by (apply not_in_mb_to_not_eq', lts_oba_mo_non_blocking_contra, nnb).
           destruct (woutpout_delay_inp hnot hmo l2) as (e3 & l3).
           exists ((p', mmsg (lts_oba_mo e)), e3).
           eapply (par_step_sync _ _ _ _ (inl μ) ζ); [exact hs | by apply fw_inl | exact l3].
    + intros y l.
      destruct (fw_tau_inv p _ y l) as [(p' & -> & lp) | (p' & μ & η & m' & -> & lp & hs & nb & heq)].
      * by apply IHpt.
      * assert (mem : η ∈ lts_oba_mo e) by (eapply msg_in_map; exact heq).
        destruct (lts_oba_mo_spec_bis2 e η mem) as (e0 & _ & l0).
        pose proof (lts_oba_mo_spec2 e η e0 nb l0) as h.
        rewrite h, gmultiset_map_disj_union, gmultiset_map_singleton in heq.
        apply gmultiset_disj_union_inj_1 in heq. subst m'.
        rewrite h in hmo.
        destruct (aux3_ hmo e0 l0) as (t & hwo & heqt).
        eapply must_eq_client; [exact heqt |].
        by eapply (IHcom p' e0 μ η hs lp l0).
    + intros e0 l0.
      destruct (woutpout_preserves_mu hmo l0) as (e1 & t & l & hwo1 & heq1).
      eapply must_eq_client; [symmetry; exact heq1 |].
      rewrite <- (gmultiset_disj_union_right_id (mmsg (lts_oba_mo e))).
      eapply nf_must_fw_r; [exact hwo1 |].
      destruct (lts_oba_mo_strip e1) as (e2 & hwo2).
      eapply (nf_must_fw_l (lts_oba_mo e1) ∅); [exact hwo2 |].
      rewrite gmultiset_disj_union_right_id. by apply IHet.
    + intros y e0 a ζ hs l1 l2.
      destruct a as [μ | [η | η]].
      * destruct (fw_inl_inv p _ μ y l1) as (p' & -> & lp).
        destruct (woutpout_preserves_mu hmo l2) as (e1 & t & l & hwo1 & heq1).
        eapply must_eq_client; [symmetry; exact heq1 |].
        rewrite <- (gmultiset_disj_union_right_id (mmsg (lts_oba_mo e))).
        eapply nf_must_fw_r; [exact hwo1 |].
        destruct (lts_oba_mo_strip e1) as (e2 & hwo2).
        eapply (nf_must_fw_l (lts_oba_mo e1) ∅); [exact hwo2 |].
        rewrite gmultiset_disj_union_right_id. by eapply (IHcom p' e1 μ ζ hs lp l).
      * destruct (fw_msg_inv p _ η y l1) as (m' & -> & heq & nb).
        assert (mem : η ∈ lts_oba_mo e) by (eapply msg_in_map; exact heq).
        destruct (lts_oba_mo_spec_bis2 e η mem) as (u & _ & lu).
        pose proof (lts_oba_mo_spec2 e η u nb lu) as h.
        rewrite h, gmultiset_map_disj_union, gmultiset_map_singleton in heq.
        apply gmultiset_disj_union_inj_1 in heq. subst m'.
        rewrite h in hmo.
        destruct (aux3_ hmo u lu) as (e1' & hwoe1' & heqe1').
        destruct (eq_spec e1' e0 (ActExt ζ)) as (r & l4 & heq4); [by exists e' |].
        destruct (woutpout_preserves_mu hwoe1' l4) as (e2 & u' & le2 & hwoe2 & hequ').
        assert (duo : dual ζ η) by (symmetry; exact hs).
        destruct (feedback nb duo lu le2) as (t & hlt & heqt).
        eapply must_eq_client; [etrans; [symmetry; exact hequ' | exact heq4] |].
        rewrite <- (gmultiset_disj_union_right_id (mmsg (lts_oba_mo u))).
        eapply nf_must_fw_r; [exact hwoe2 |].
        eapply must_eq_client; [exact heqt |].
        destruct (lts_oba_mo_strip t) as (x & hx).
        eapply (nf_must_fw_l (lts_oba_mo t) ∅); [exact hx |].
        rewrite gmultiset_disj_union_right_id. by apply IHet.
      * destruct (fw_cobar_inv p _ η y l1) as (_ & nb).
        simpl in hs. subst ζ. exfalso.
        eapply (lts_oba_mo_strip_refuses e e' hmo η nb).
        apply lts_performs_spec2. by exists e0.
Qed.

Lemma must_fw_to_must (p : P) (e : T) : (p, ∅) must_pass e → p must_pass e.
Proof.
  intros hm. remember (p, ∅ : MO (MemAct Atest)) as x eqn:Hx. revert p Hx.
  induction hm as [x e happy | x e nh ex pt IHpt et IHet com IHcom]; intros p Hx; subst.
  - by apply m_now.
  - apply m_step; [exact nh | | | |].
    + destruct (lts_oba_mo_strip e) as (e' & hwo).
      assert (hm' : (p, mmsg (lts_oba_mo e)) must_pass e')
        by (apply (nf_must_fw p e e' _ hwo); by apply m_step).
      destruct hm' as [happy' | nh' ex' _ _ _].
      * exfalso. apply nh. by eapply woutpout_preserves_outcome_converse.
      * destruct ex' as (y & l).
        destruct (par_view_of _ _ y l) as [f' lf | e0 le | f' e0 a ζ hs l1 l2].
        -- destruct (fw_tau_inv p _ f' lf) as [(p0 & -> & lp) | (p0 & μ & η & m' & -> & lp & hs & nb & heq)].
           ++ exists (p0, e). by apply par_step_left.
           ++ assert (mem : η ∈ lts_oba_mo e) by (eapply msg_in_map; exact heq).
              destruct (lts_oba_mo_spec_bis2 e η mem) as (e2 & _ & l2).
              exists (p0, e2). eapply par_step_sync; [exact hs | exact lp | exact l2].
        -- destruct (woutpout_preserves_mu hwo le) as (r0 & _ & l0 & _).
           exists (p, r0). by apply par_step_right.
        -- destruct (woutpout_preserves_mu hwo l2) as (r0 & _ & l0 & _).
           destruct a as [μ | [η | η]].
           ++ destruct (fw_inl_inv p _ μ f' l1) as (p0 & -> & lp).
              exists (p0, r0). eapply par_step_sync; [exact hs | exact lp | exact l0].
           ++ destruct (fw_msg_inv p _ η f' l1) as (m' & -> & heq & nb).
              assert (mem : η ∈ lts_oba_mo e) by (eapply msg_in_map; exact heq).
              destruct (lts_oba_mo_spec_bis2 e η mem) as (e2 & _ & le2).
              assert (duo : dual ζ η) by (symmetry; exact hs).
              assert (neq : ζ ≠ η).
              { intros ->. by apply (dual_blocks η η nb duo). }
              destruct (nb_confluence nb neq le2 l0) as (e3 & l3 & _).
              destruct (feedback nb duo le2 l3) as (e4 & l4 & _).
              exists (p, e4). by apply par_step_right.
           ++ destruct (fw_cobar_inv p _ η f' l1) as (_ & nb).
              simpl in hs. subst ζ. exfalso.
              eapply (lts_oba_mo_strip_refuses e e' hwo η nb).
              apply lts_performs_spec2. by exists e0.
    + intros p' l. eapply IHpt; [by apply fw_tau_left | reflexivity].
    + intros e' l. eapply IHet; [exact l | reflexivity].
    + intros p' e' μ ζ hs l1 l2.
      eapply (IHcom (p', ∅) e' (inl μ) ζ); [exact hs | by apply fw_inl | exact l2 | reflexivity].
Qed.

Theorem must_iff_must_fw (p : P) (e : T) : p must_pass e ↔ (p, ∅) must_pass e.
Proof.
  split; intros hm.
  - destruct (lts_oba_mo_strip e) as (e' & hmo).
    apply (nf_must_fw p e e' _ hmo).
    by eapply must_to_must_fw.
  - by apply must_fw_to_must.
Qed.

End LiftMem.

Section LiftMemPreorder.

Context `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest} `{SA : !SyncAction Aproc Atest}.
Context `{gLtsEqT : !gLtsEq T Ht} `{gLtsObaT : !gLtsOba T} `{!gLtsObaFB T Atest}
        `{!FiniteOutputChain_LtsOba T}.
Context (outcome : T → Prop) `{!Testing_Predicate outcome gLtsEqT}.

Context `{gLtsEqP : !gLtsEq P Hp}.
Context `{PIP : !Prop_of_Inter P (MO (MemAct Atest)) Aproc (MemAct Atest) fw_inter_mem}.
Context `{PIPT : !Prop_of_Inter P T Aproc Atest sync}.

Context `{gLtsEqQ : !gLtsEq Q Hp}.
Context `{PIQ : !Prop_of_Inter Q (MO (MemAct Atest)) Aproc (MemAct Atest) fw_inter_mem}.
Context `{PIQT : !Prop_of_Inter Q T Aproc Atest sync}.

#[local] Existing Instance toFwEq.

Context `{PIFPT : !Prop_of_Inter (P * MO (MemAct Atest)) T (Aproc + MemAct Atest) Atest sync}.
Context `{PIFQT : !Prop_of_Inter (Q * MO (MemAct Atest)) T (Aproc + MemAct Atest) Atest sync}.

Theorem lift_fw_ctx_pre (p : P) (q : Q) :
  ctx_pre (gLtsT := gLtsEqT) p q ↔
  ctx_pre (gLtsT := gLtsEqT) (p, ∅ : MO (MemAct Atest)) (q, ∅ : MO (MemAct Atest)).
Proof.
  split; intros hctx e hm.
  - apply (must_iff_must_fw outcome). apply hctx. by apply (must_iff_must_fw outcome).
  - apply (must_iff_must_fw outcome). apply hctx. by apply (must_iff_must_fw outcome).
Qed.

End LiftMemPreorder.
(* end hide *)
