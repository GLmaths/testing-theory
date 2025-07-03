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

Require Import Coq.Program.Equality.
From stdpp Require Import base countable finite gmap list 
                        finite base decidable finite gmap gmultiset.
From Must Require Import TransitionSystems Must.

Lemma woutpout_preserves_good `{gLtsObaFB P A, !Good P A good }
  e m e': good e -> strip e m e' -> good e'.
Proof.
  intros happy stripped.
  induction stripped.
  + eapply good_preserved_by_eq; eauto.
  + eapply IHstripped. eapply good_preserved_by_lts_non_blocking_action; eauto.
Qed.

Lemma woutpout_preserves_good_converse `{gLtsObaFB P A, !Good P A good }
  e m e': good e' -> strip e m e' -> good e.
Proof.
  intros happy stripped. induction stripped.
  + symmetry in eq. eapply good_preserved_by_eq; eauto.
  + eapply good_preserved_by_lts_non_blocking_action_converse. eassumption. eassumption.
    now eapply IHstripped.
Qed.

Lemma strip_eq `{@gLtsOba P A H gLtsP LOA} {e e' m} :
  strip e m e' -> forall r, eq_rel r e -> exists r', strip r m r' /\ eq_rel r' e'.
Proof.
  intro w.
  dependent induction w; intros r heq.
  - exists r. split. constructor. reflexivity. etransitivity; eauto.
  - destruct (eq_spec r p2 (ActExt η)) as (r0 & l0 & heq0). eauto.
    destruct (IHw r0 heq0) as (r' & hwo' & heq').
    exists r'. split. eapply strip_step; eassumption. eassumption.
Qed.

Lemma woutpout_preserves_mu `{gLtsOba P A}
  {p q m t α} : strip p m q -> q ⟶{α} t -> exists r t', p ⟶{α} r /\ strip r m t' /\ eq_rel t t'.
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


(* Lemma elem_eq `{ExtAction A} (x : A) (g1 g2 : gmultiset A) : 
  x ∈ elements (g1 ⊎ g2) = x ∈ elements (g1) ++ elements g2.
Proof.
  eapply elem_of_Permutation_proper.
    eapply (gmultiset_elements_disj_union {[+ co μ1 +]} m2).
  (* setoid_rewrite eq. *)
Admitted.
eapply elem_of_Permutation_proper.
    eapply (gmultiset_elements_disj_union {[+ co μ1 +]} m2).
    
Lemma not_in_mb_to_not_eq `{ExtAction A} (x : A) (g : gmultiset A) : 
  (elements ({[+ x +]} ⊎ g) = [ x ] ++ elements g).
Proof.
  assert (elements (@singletonMS A (gmultiset A) gmultiset_singleton x) = [x]) as eq.
  rewrite gmultiset_elements_singleton. eauto.
  rewrite<- eq.
  now eapply elem_eq.
Qed. *)

(* Inductive ForallMSET `{H : ExtAction} (P : A → Prop) : 
      gmultiset A → Prop :=
    | Forall_nil : ForallMSET P ∅ 
    | Forall_cons : ∀ (x : A) (m : gmultiset A), P x → ForallMSET P m 
            → ForallMSET P ({[+ x +]} ⊎ m).
*)

Lemma simpl_P_in_l `{ExtAction A} {P} 
  (η : A) (m : mb A): 
  Forall P (elements ({[+ η +]} ⊎ m)) <-> P η /\ Forall P (elements m).
Proof.
  split.
  + assert ((elements ({[+ η +]} ⊎ m)) ≡ₚ elements ({[+ η +]} : gmultiset A) ++ (elements m)).
  eapply gmultiset_elements_disj_union.
  intro. assert (Forall P (elements (gmultiset_singleton η) ++ elements m)) as Hyp.
  eapply are_actions_preserved_by_perm; eauto.
  assert (elements (gmultiset_singleton η) = [η]) as eq.
  eapply gmultiset_elements_singleton. rewrite eq in Hyp. simpl in *.
  inversion Hyp. subst. split; eauto.
  + intros (PHyp & FHyp).
    assert (Forall P (η :: elements m)). econstructor; eauto.
    eapply are_actions_preserved_by_perm. symmetry. eapply gmultiset_elements_disj_union.
    assert (elements (gmultiset_singleton η) = [η]) as eq.
    eapply gmultiset_elements_singleton. unfold singletonMS. rewrite eq. simpl in *. eauto.
Qed.

Lemma woutpout_delay_inp `{gLtsOba P A} {p q m t μ} : 
    Forall (NotEq μ) (elements m) -> strip p m q -> p ⟶[μ] t -> exists r, q ⟶[μ] r.
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


Lemma nb_with_strip `{gLtsOba P A} p1 m p'1 η: p1 ⟿{m} p'1 -> η ∈ m -> non_blocking η.
Proof.
  intros stripped mem.
  dependent induction stripped.
  + multiset_solver.
  + destruct (decide (η = η0)) as [eq | not_eq]; subst.
    ++ eauto.
    ++ assert (η ∈ m). multiset_solver.
       eapply IHstripped. eauto.
Qed.


(* Lemma nb_with_strip_m `{gLtsOba P A} p1 m p'1: p1 ⟿{m} p'1 -> Forall non_blocking (elements m).
Proof.
  intros stripped.
  (* remember (elements m) as l.
  induction l. *)
  dependent induction stripped.
  + multiset_solver.
  + assert (elements ({[+ η +]} ⊎ m) = η :: (elements m)) as eq.
    admit.
    ++ rewrite eq. constructor. eauto. eauto.
Admitted. *)


Lemma not_nb_with_strip_m `{gLtsOba P A} p1 m p'1 μ : p1 ⟿{m} p'1 -> ¬ non_blocking μ
    -> Forall (NotEq μ) (elements m).
Proof.
  intros stripped.
  (* remember (elements m) as l.
  induction l. *)
  dependent induction stripped.
  + multiset_solver.
  + (* assert (elements ({[+ η +]} ⊎ m) = η :: (elements m)) as eq.
    eapply not_in_mb_to_not_eq. *)
    ++ intro. eapply simpl_P_in_l. split; eauto.
       eapply BlockingAction_are_not_non_blocking; eauto.
Qed.


Lemma woutpout_delay_tau `{gLtsOba P A} {p q m t} :
  strip p m q -> p ⟶ t 
  -> (exists η μ r t, non_blocking η /\ dual η μ /\ p ⟶[η] r /\ q ⟶[μ] t) \/ (exists r, q ⟶ r).
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
       assert (¬ non_blocking μ) as not_nb.
       eapply lts_oba_fw_non_blocking_duo_spec; eauto.
       assert (Forall (NotEq μ) (elements m)) as simpl_in_l.
       eapply not_nb_with_strip_m; eauto.
       eapply woutpout_delay_inp in hlr as (u & lu) ; eauto.
Qed.

Lemma conv (* `{gLts P A}  *)
  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}
  (p : P) : 
  p ⤓ -> (p, ∅) ⤓.
Proof.
  intro ht.
  induction ht.
  destruct (lts_refuses_decidable (p, ∅) τ).
  - eapply tstep. intros (p', m') l'.
    apply lts_refuses_spec2 in l. now exfalso. eauto with mdb.
  - eapply tstep. intros (p', m') l'.
    inversion l'; subst.
    + eapply H2; eauto.
    + inversion l.
    + exfalso. 
      destruct eq as (duo & nb).
      eapply non_blocking_action_in_ms in nb; eauto. multiset_solver.
Qed.

Lemma neq_multi_nil `{Countable A} (m : gmultiset A) a : {[+ a +]} ⊎ m ≠ ∅.
Proof. multiset_solver. Qed.

Lemma gmultiset_not_elem_of_multiplicity `{Countable A} x (g : gmultiset A) :
  x ∉ g <-> multiplicity x g = 0.
Proof. multiset_solver. Qed.

Lemma aux0 `{gLtsOba P A} {e e' m} :
  forall η, η ∈ m -> strip e m e' -> exists e', e ⟶[η] e'.
Proof.
  intros a mem w.
  dependent induction w.
  - multiset_solver.
  - eapply gmultiset_elem_of_disj_union in mem as [here | there].
    + eapply gmultiset_elem_of_singleton in here. subst. firstorder.
    + eapply IHw in there as (q & l).
      edestruct (lts_oba_non_blocking_action_delay H1 H2 l) as (u & l2 & l3). eauto.
Qed.

Lemma gmultiset_eq_drop_l `{Countable A} (m1 m2 m3 : gmultiset A) : m1 ⊎ m2 = m1 ⊎ m3 -> m2 = m3.
Proof. by multiset_solver. Qed.

Lemma aux3_ `{@gLtsOba P A H gLtsP LOA} {e e' m η} :
  strip e ({[+ η +]} ⊎ m) e' -> forall r, e ⟶[η] r -> exists t, strip r m t /\ eq_rel t e'.
Proof.
  intro w.
  dependent induction w.
  - multiset_solver.
  - intros r l.
    destruct (decide (η = η0)); subst.
    + assert (eq_rel p2 r) by (eapply lts_oba_non_blocking_action_deter; eassumption).
      eapply gmultiset_eq_drop_l in x. subst.
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

Lemma must_non_blocking_action_swap_l_fw_eq `{
  @gLtsObaFW P A H gLtsP M K, 
  @gLtsObaFB E A H gLtsE Y V, !Good E A good}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p1 p2 : P) (e1 e2 : E) (η : A) :
  non_blocking η -> p1 ⟶⋍[η] p2 -> e1 ⟶⋍[η] e2 -> must p1 e2 -> must p2 e1.
Proof.
  intros nb lp le hm. revert e1 p2 nb lp le.
  induction hm as [p e happy|p1 e2 nh ex Hpt IHpt Het IHet Hcom IHcom]; intros e1 p2 nb lp le.
  - eapply m_now.
    destruct le as (e' & hle' & heqe').
    eapply good_preserved_by_lts_non_blocking_action_converse. eassumption. eassumption.
    eapply good_preserved_by_eq. eapply happy. now symmetry.
  - eapply m_step.
    + intro h.
      destruct le as (e' & hle' & heqe').
      eapply nh, (good_preserved_by_eq e' e2); eauto.
      eapply good_preserved_by_lts_non_blocking_action; eauto.
    + destruct ex as ((p' & e') & l).
      inversion l; subst.
      destruct lp as (p0 & hlp0 & heqp0).
      ++ destruct (lts_oba_non_blocking_action_tau nb hlp0 l0) as [(t & l1 & l2) | m].
         +++ edestruct (eq_spec p2 t τ) as (p2' & hlp2' & heqp2').
             exists p0. split. now symmetry. eassumption.
             exists (p2', e1). eauto with mdb.
         +++ destruct m as (μ & duo &  p2' & hl & heq).
             destruct le as (e0 & hle0 & heqe0). 
             edestruct (eq_spec p2 p2' (ActExt $ μ)) as (p3 & hlp3 & heqp3).
             exists p0. split. now symmetry. eassumption.
             exists (p3, e0). 
             eapply ParSync; try eassumption.
      ++ destruct le as (e0 & hle0 & heqe0).
         edestruct (eq_spec e0 e' τ) as (e3 & hle3 & heqe3).
         exists e2. split. now symmetry. eassumption.
         destruct (lts_oba_non_blocking_action_delay nb hle0 hle3) as (t & l1 & l2).
         destruct lp as (p0 & hlp0 & heqp0).
         eauto with mdb.
      ++ destruct (decide (μ1 = η)); subst.
             +++ destruct lp as (p0 & hlp0 & heqp0), le as (e0 & hle0 & heqe0). subst. 
                 simpl in eq. subst.
                 edestruct (eq_spec e0 e' (ActExt $ μ2)) as (e3 & hle3 & heqe3).
                 exists e2. split. now symmetry. eassumption.
                 (* destruct eq as [duo_case1 | duo_case2].
                 --- destruct (lts_oba_fb_feedback nb duo_case1 hle0 hle3) as (e4 & hle4 & heqe4).
                 eauto with mdb.
                 --- admit. *) unfold parallel_inter.
                 assert (dual η μ2) as eq'. symmetry. eauto.
                 destruct (lts_oba_fb_feedback nb eq' hle0 hle3) as (e4 & hle4 & heqe4).
                 eauto with mdb.
             +++ destruct lp as (p0 & hlp0 & heqp0).
                 destruct le as (e0 & hle0 & heqe0).
                 destruct (lts_oba_non_blocking_action_confluence nb n hlp0 l1) as (t & l3 & l4).
                 edestruct (eq_spec e0 e' (ActExt μ2)) as (e3 & hle3 & heqe3).
                 exists e2. split. now symmetry. eassumption.
                 destruct (lts_oba_non_blocking_action_delay nb hle0 hle3) as (r & l5 & l6).
                 edestruct (eq_spec p2 t (ActExt μ1)) as (p3 & hlp3 & heqp3).
                 exists p0. split. now symmetry. eassumption.
                 eauto with mdb.
    + intros p' l.
      destruct lp as (p0 & hlp0 & heqp0).
      edestruct (eq_spec p0 p' τ) as (p3 & hlp3 & heqp3).
      by (exists p2; split; [now symmetry | eassumption]).
      destruct (lts_oba_non_blocking_action_delay nb hlp0 hlp3) as (t & l1 & l2).
      destruct l2 as (p4 & hlp4 & heqp4).
      eapply must_eq_server. etrans. eapply heqp4. eassumption.
      eapply IHpt; eauto with mdb. exists p4. split. eassumption. reflexivity.
    + intros e' l.
      destruct le as (e0 & hle0 & heqe0).
      destruct (lts_oba_non_blocking_action_tau nb hle0 l) as [(t & l0 & l1)| Hyp].
      ++ destruct (eq_spec e2 t τ) as (v & hlv & heqv).
         exists e0. split; eauto. now symmetry.
         eapply IHet. eassumption. eassumption. eassumption.
         destruct l1 as (e3 & hle3 & heqe3).
         exists e3. split; eauto. etrans. eassumption. now symmetry.
      ++ destruct Hyp as (μ & duo & u & hlu & hequ).
         destruct (eq_spec e2 u (ActExt $ μ)) as (v & hlv & heqv).
         exists e0. split. now symmetry. eassumption.
         eapply must_eq_client. etrans. eapply heqv. eassumption.
         destruct lp as (p0 & hlp0 & heqp0).
         eapply must_eq_server. eassumption. 
         eapply Hcom. (* left. *) symmetry in duo. exact duo. eassumption. eassumption. 
    + intros p' e' μ1 μ2 duo l1 l2.
      destruct lp as (p0 & hlp0 & heqp0).
      destruct le as (e0 & hle0 & heqe0).
      destruct (decide (μ2 = η)); subst; simpl in l2.
      ++ edestruct (eq_spec p0 p' (ActExt $ μ1)) as (p3 & hlp3 & heqp3).
         exists p2. split. now symmetry. eassumption.
         assert (heqe' : e0 ⋍ e'). eapply lts_oba_non_blocking_action_deter; eassumption.
         
         
         destruct (lts_oba_fw_feedback nb duo hlp0 hlp3) as [(p3' & hlp3' & heqp3')|].
         +++ eapply must_eq_client. eassumption.
             eapply must_eq_client. symmetry. eapply heqe0.
             eapply must_eq_server. transitivity p3; eassumption.
             eapply Hpt. eassumption.
         +++ eapply (must_eq_client _ e0 e'). eassumption.
             eapply (must_eq_client _ e2 e0). eapply (symmetry heqe0).
             eapply must_eq_server. transitivity p3; eassumption.
             eauto with mdb.
      ++ destruct (lts_oba_non_blocking_action_confluence nb n hle0 l2) as (t & l3 & l4).
         edestruct (eq_spec p0 p' (ActExt μ1)) as (p3 & hlp3 & heqp3). eauto with mdb.
         destruct (lts_oba_non_blocking_action_delay nb hlp0 hlp3) as (r & l5 & l6).
         edestruct (eq_spec e2 t (ActExt μ2)) as (e3 & hle3 & heqe3).
         exists e0. split. now symmetry. eassumption.
         eapply IHcom. eassumption. eassumption. eassumption. eassumption.
         destruct l6 as (p4 & hlp4 & heqp4).
         exists p4. split. eassumption. etrans. eapply heqp4. eassumption.
         destruct l4 as (e4 & hle4 & heqe4).
         exists e4. split. eassumption. etrans. eapply heqe4. now symmetry.
Qed. 

Lemma must_non_blocking_action_swap_r_fw_eq`{
  @gLtsObaFW P A H gLtsP M K, 
  @gLtsObaFB E A H gLtsE Y V, !Good E A good}
  
  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}
  
  (p1 p2 : P) (e1 e2 : E) (η : A) :
  non_blocking η -> p1 ⟶⋍[η] p2 -> e1 ⟶⋍[η] e2 -> must p2 e1 -> must p1 e2.
Proof.
  intros nb lp le hm. revert e2 p1 nb le lp.
  induction hm as [|p2 e1 nh ex Hpt IHpt Het IHet Hcom IHcom]; intros e2 p1 nb le lp.
  - eapply m_now.
    destruct le as (e' & hle' & heqe').
    eapply good_preserved_by_eq.
    eapply good_preserved_by_lts_non_blocking_action; eassumption.
    eassumption.
  - destruct lp as (p0 & hlp0 & heqp0).
    destruct le as (e0 & hle0 & heqe0).
    eapply m_step.
    + intro h. eapply nh.
      eapply good_preserved_by_lts_non_blocking_action_converse; eauto.
      eapply good_preserved_by_eq. eapply h. now symmetry.
    + destruct ex as ((p' & e') & l).
      inversion l; subst.
      ++ edestruct (eq_spec p0 p' τ) as (p3 & hlp3 & heqp3).
         exists p2. split. now symmetry. eassumption.
         destruct (lts_oba_non_blocking_action_delay nb hlp0 hlp3) as (t & l1 & l2).
         eauto with mdb.
      ++ destruct (lts_oba_non_blocking_action_tau nb hle0 l0) as [(t & l1 & l2) | m].
         +++ edestruct (eq_spec e2 t τ) as (e2' & hle2' & heqe2').
             exists e0. split. now symmetry. eassumption.
             exists (p1, e2'). eauto with mdb.
         +++ destruct m as (μ & duo & e2' & hl & heq).
             edestruct (eq_spec e2 e2' (ActExt $ μ)) as (e3 & hle3 & heqe3).
             exists e0. split. now symmetry. eassumption.
             exists (p0, e3). symmetry in duo. eapply ParSync; try eassumption. 
             (* left. assumption. *)
      ++ destruct (decide (μ2 = η)); subst.
             +++ assert (e0 ⋍ e') by (eapply (lts_oba_non_blocking_action_deter nb hle0 l2); eauto).
                 simpl in eq. subst.
                 edestruct (eq_spec p0 p' (ActExt $ μ1)) as (p3 & hlp3 & heqp3).
                 exists p2. split. now symmetry. eassumption.
                 (* destruct eq as [duo_case1 | duo_case2].
                 --- admit.
                 --- destruct (lts_oba_fw_feedback nb duo_case2 hlp0 hlp3) as [(t & hlt & heqt)|]; subst; eauto with mdb.
                     assert (hm : must p' e0) by eauto with mdb.
                     eapply (must_eq_client p' e0 e2) in hm.
                     eapply (must_eq_server p' p1 e2) in hm.
                     assert (¬ good e2).
                     intro hh. eapply nh. eapply good_preserved_by_lts_non_blocking_action_converse.
                     eassumption. eassumption. eapply good_preserved_by_eq. eassumption.
                     etrans. symmetry. eassumption. eassumption.
                     inversion hm; subst. contradiction. eassumption.
                     etrans. symmetry. eassumption. now symmetry. eassumption. *)
                 destruct (lts_oba_fw_feedback nb eq hlp0 hlp3) as [(t & hlt & heqt)|]; subst; eauto with mdb.
                 assert (hm : must p' e0) by eauto with mdb.
                 eapply (must_eq_client p' e0 e2) in hm.
                 eapply (must_eq_server p' p1 e2) in hm.
                 assert (¬ good e2).
                 intro hh. eapply nh. eapply good_preserved_by_lts_non_blocking_action_converse.
                 eassumption. eassumption. eapply good_preserved_by_eq. eassumption.
                 etrans. symmetry. eassumption. eassumption.
                 inversion hm; subst. contradiction. eassumption.
                 etrans. symmetry. eassumption. now symmetry. eassumption.
             +++ destruct (lts_oba_non_blocking_action_confluence nb n hle0 l2)
                    as (t & l3 & l4).
                  edestruct (eq_spec p0 p' (ActExt μ1)) as (p3 & hlp3 & heqp3).
                  exists p2. split. now symmetry. eassumption.
                  destruct (lts_oba_non_blocking_action_delay nb hlp0 hlp3)
                    as (r & l5 & l6).
                  edestruct (eq_spec e2 t (ActExt μ2)) as (e3 & hle3 & heqe3).
                  exists e0. split. now symmetry. eassumption.
                  eauto with mdb.
    + intros p' l.
      destruct (lts_oba_non_blocking_action_tau nb hlp0 l) as [(t & l0 & l1)| Hyp].
      ++ destruct (lts_oba_non_blocking_action_delay nb hlp0 l0) as (r & hl2 & hl3).
         destruct l1 as (e3 & hle3 & heqe3).
         destruct hl3 as (u & hlu & hequ).
         assert (heq : r ⋍ p'). eapply lts_oba_non_blocking_action_deter_inv; try eassumption.
         etrans. eassumption. now symmetry.
         destruct (eq_spec p' u (ActExt $ η)) as (v & hlv & heqv).
         exists r. split. now symmetry. eassumption.
         eapply (must_eq_server _ _ _ heq).
         edestruct (eq_spec p2 t τ) as (p3 & hlp3 & heqp3).
         exists p0. split. now symmetry. eassumption.
         eapply IHpt; eauto.
         exists e0. eauto with mdb.
         exists u. split. eassumption. etrans. eapply hequ. now symmetry.
      ++ destruct Hyp as (μ & duo & u & hlu & hequ).
         destruct (lts_oba_non_blocking_action_delay nb hlp0 hlu) as (r & hl2 & hl3).
         destruct (eq_spec p2 u (ActExt $ μ)) as (v & hlv & heqv).
         exists p0. split. now symmetry. eassumption.
         eapply must_eq_server. etrans. eapply heqv. eassumption.
         eapply must_eq_client. eassumption.
         eapply Hcom.
         eassumption. eassumption. eassumption.
    + intros e' l.
      edestruct (eq_spec e0 e' τ) as (e3 & hle3 & heqe3).
      exists e2. split. now symmetry. eassumption.
      destruct (lts_oba_non_blocking_action_delay nb hle0 hle3) as (t & l1 & l2).
      destruct l2 as (e4 & hle4 & heqe4).
      eapply must_eq_client. etrans. eapply heqe4. eassumption.
      eapply IHet. eassumption. eassumption. exists e4. split. eassumption. reflexivity.
      exists p0. split. eassumption. eassumption.
    + intros p' e' μ μ1 duo l1 l2.
      destruct (decide (μ = η)) as [eq | not_eq ].
      ++ subst. simpl in l2.
         edestruct (eq_spec e0 e' (ActExt $ μ1)) as (e3 & hle3 & heqe3).
         exists e2. split. now symmetry. eassumption.
         (* destruct duo as [duo_case1 | duo_case2].
            -- destruct (lts_oba_fb_feedback nb duo_case1 hle0 hle3) as (e3' & hle3' & heqe3').
               assert (heqe' : p0 ⋍ p'). eapply lts_oba_non_blocking_action_deter; eassumption.
               eapply must_eq_server. eassumption.
               eapply must_eq_server. symmetry. eapply heqp0.
               eapply must_eq_client. etrans. eapply heqe3'. eassumption.
               eapply Het. eassumption.
            -- admit. *)
         symmetry in duo.
         destruct (lts_oba_fb_feedback nb duo hle0 hle3) as (e3' & hle3' & heqe3').
         assert (heqe' : p0 ⋍ p'). eapply lts_oba_non_blocking_action_deter; eassumption.
         eapply must_eq_server. eassumption.
         eapply must_eq_server. symmetry. eapply heqp0.
         eapply must_eq_client. etrans. eapply heqe3'. eassumption.
         eapply Het. eassumption.
      ++ destruct (lts_oba_non_blocking_action_confluence nb not_eq hlp0 l1) as (t & l3 & l4).
         edestruct (eq_spec e0 e' (ActExt μ1)) as (e3 & hle3 & heqe3); eauto.
         destruct (lts_oba_non_blocking_action_delay nb hle0 hle3) as (r & l5 & l6).
         edestruct (eq_spec p2 t (ActExt μ)) as (p3 & hlp3 & heqp3).
         exists p0. split. now symmetry. eassumption.
         eapply IHcom. eassumption. eassumption. eassumption. eassumption.
         destruct l6 as (e4 & hle4 & heqe4).
         exists e4. split. eassumption. etrans. eapply heqe4. eassumption.
         destruct l4 as (p4 & hlp4 & heqp4).
         exists p4. split. eassumption. etrans. eapply heqp4. now symmetry.
Qed.

Lemma must_non_blocking_action_swap_l_fw `{
  @gLtsObaFW P A H gLtsP M K, 
  @gLtsObaFB E A H gLtsE Y V, !Good E A good}
  
  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}
  
  (p1 p2 : P) (e1 e2 : E) (η : A) :
  non_blocking η -> p1 ⟶[η] p2 -> e1 ⟶[η] e2 -> must p1 e2 -> must p2 e1.
Proof.
  intros. eapply must_non_blocking_action_swap_l_fw_eq; eauto; eexists; split; eauto; reflexivity.
Qed.

Lemma must_non_blocking_action_swap_r_fw `{
  @gLtsObaFW P A H gLtsP M K, 
  @gLtsObaFB E A H gLtsE Y V, !Good E A good}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p1 p2 : P) (e1 e2 : E) (η : A) :
  non_blocking η -> p1 ⟶[η] p2 -> e1 ⟶[η] e2 -> must p2 e1 -> must p1 e2.
Proof.
  intros.
  eapply must_non_blocking_action_swap_r_fw_eq; eauto; eexists; split; eauto; reflexivity.
Qed.

Lemma nf_must_fw_l `{
  @gLtsObaFB P A H gLtsP M K, !FiniteImagegLts P A,
  @gLtsObaFB E A H gLtsE Y V, !Good E A good}

  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}
  `{@Prop_of_Inter (P * mb A) E A parallel_inter H (inter_lts fw_inter) gLtsE}

  m1 m2 (p : P) (e e' : E) : e ⟿{m1} e' -> must (p, m1 ⊎ m2) e' -> must (p, m2) e.
Proof.
  revert p e e' m2.
  induction m1 using gmultiset_ind; intros p e e' m2 hmo hm.
  - inversion hmo; subst.
    rewrite gmultiset_disj_union_left_id in hm.
    symmetry in eq. eapply must_eq_client; eauto.
    multiset_solver.
  - assert (non_blocking x) as nb. eapply nb_with_strip; eauto. multiset_solver.
    assert (x ∈ {[+ x +]} ⊎ m1) as mem by multiset_solver.
    eapply aux0 in mem as (e0 & l0); eauto.
    eapply (aux3_) in hmo as (t & hwo & heq); eauto.
    eapply (must_non_blocking_action_swap_l_fw_eq ).
    exact nb. exists (p ▷ m2). split. 
    apply (ParRight (ActExt x) p ({[+ x +]} ⊎ m2) (m2)).
    unfold lts_step;simpl.
    eapply lts_multiset_minus; eauto. 
    reflexivity. exists e0. split. eassumption. reflexivity.
    eapply IHm1. eassumption. eapply must_eq_client. symmetry. eassumption.
    now replace (m1 ⊎ ({[+ x +]} ⊎ m2)) with ({[+ x +]} ⊎ m1 ⊎ m2) by multiset_solver.
Qed.


Lemma add_in_mb_fw_tau `{
  @Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}

  (m : mb A) (p : P) (mp : mb A) (p' : P) (mp' : mb A) :
  (p ▷ mp) ⟶ (p' ▷ mp') -> (p ▷ m ⊎ mp) ⟶ (p' ▷ m ⊎ mp').
Proof.
  intro Hstep.
  inversion Hstep; subst.
  + eapply ParLeft; assumption.
  + inversion l.
  + eapply ParSync; eauto.
    destruct (decide (non_blocking μ2)) as [nb | not_nb].
    ++ eapply non_blocking_action_in_ms in nb as eq'; eauto; subst.
       assert (m ⊎ ({[+ μ2 +]} ⊎ mp') 
       = {[+ μ2 +]} ⊎ (m ⊎ mp')) as eqm by multiset_solver.
       rewrite eqm.
       assert (m ⊎ mp' = mp' ⊎ m) as eqm' by multiset_solver.
       rewrite eqm'. eapply lts_multiset_minus; eauto.
    ++ eapply blocking_action_in_ms in not_nb as (eq' & duo & nb); eauto; subst.
       assert (m ⊎ ({[+ co μ2 +]} ⊎ mp) = {[+ co μ2 +]} ⊎ (m ⊎ mp))
       as eqm' by multiset_solver.
       rewrite eqm'. eapply lts_multiset_add; eauto.
Qed.

Lemma add_in_mb_fw_action `{
  @Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}

  (m : mb A) (p : P) (mp : mb A) (p' : P) (mp' : mb A) (μ : A):
  (p ▷ mp) ⟶[μ] (p' ▷ mp') -> (p ▷ m ⊎ mp) ⟶[μ] (p' ▷ m ⊎ mp').
Proof.
  intro Hstep.
  inversion Hstep; subst.
  + eapply ParLeft; assumption.
  + inversion l; subst.
    ++ eapply ParRight.
       assert ({[+ η +]} ⊎ (m ⊎ mp) = m ⊎ ({[+ η +]} ⊎ mp)) as eq.
       multiset_solver. rewrite<- eq. eapply lts_multiset_add; eauto.
    ++ eapply ParRight.
       assert (m ⊎ ({[+ μ +]} ⊎ mp') = {[+ μ +]} ⊎ (m ⊎ mp')) as eq.
       multiset_solver. rewrite eq. eapply lts_multiset_minus; eauto.
Qed.


Lemma nf_must_fw_r `{
  @gLtsObaFB P A H gLtsP M K, !FiniteImagegLts P A ,
  @gLtsObaFB E A H gLtsE Y V,  !Good E A good}
  
  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}
  `{@Prop_of_Inter (P * mb A) E A parallel_inter H (inter_lts fw_inter) gLtsE}
  
  (p : P) (e e' : E) m1 m2 : 
  strip e m1 e' -> must (p, m2) e -> must (p, m1 ⊎ m2) e'.
Proof.
  intro hwo. revert p m2.
  dependent induction hwo; intros q m2 hm.
  rename p into e, q into p.
  - rewrite gmultiset_disj_union_left_id. eapply must_eq_client; eauto.
  - assert (must (q, {[+ η +]} ⊎ m2) p2).
    -- dependent induction hm; subst. 
      + eapply m_now. eapply good_preserved_by_lts_non_blocking_action; eassumption.
      + assert (non_blocking η) as nb. eauto.
        edestruct exists_duo_nb as (μ & duo). 
        eapply com; eauto.
        eapply ParRight. assert (¬ non_blocking μ) as not_nb.
        eapply lts_oba_fw_non_blocking_duo_spec; eauto.
        eapply lts_multiset_add; eauto.
      (* + eapply m_step.
        ++ intro. eapply ungood_preserved_by_lts_non_blocking_action; eauto.
        ++ destruct ex as (((q' , m'2 ) , m') & Hinter_step). inversion Hinter_step; subst.
           +++ exists ((q' ▷ {[+ η +]} ⊎ m'2) , p2).
               eapply ParLeft. eapply add_in_mb_fw_tau ; eauto.
           +++ edestruct (lts_oba_non_blocking_action_tau H4 H5 l) as [confluence | comm].
               ++++ destruct confluence as (p'2 & HypTr & HypTr_nb).
                    exists ((q' ▷ {[+ η +]} ⊎ m'2) ▷ p'2). eapply ParRight. assumption.
               ++++ destruct comm as (μ & duo & HypTr).
                    destruct HypTr as (p'2 & HypTr & eq).
                    exists ((q' ▷ m'2) ▷ p'2). eapply ParSync. eassumption.
                    eapply ParRight. eapply lts_multiset_minus; eauto. assumption.
           +++ destruct (decide (μ2 = η)) as [eq' | not_eq']; subst.
               ++++ assert (¬ non_blocking μ1) as not_nb. apply symmetry in eq. 
                    eapply lts_oba_fw_non_blocking_duo_spec; eauto.
                    inversion l1; subst.
                    +++++ exists ((q' ▷ m'2) ▷ p2).
                          eapply ParLeft. eapply ParSync; eauto. 
                          split; try symmetry; eassumption.
                          eapply lts_multiset_minus; eauto.
                    +++++ eapply blocking_action_in_ms in l as (eq'' & duo'' & nb''); eauto; subst.
                          assert (η = co μ1). eapply unique_nb; eauto. symmetry. assumption.
                          subst. inversion l1; subst.
                          ++++++ exfalso. multiset_solver.
                          ++++++ admit. (*existence d'une co action ?*) 
               ++++ destruct (lts_oba_non_blocking_action_confluence H4 not_eq' H5 l2) 
                    as (p'2 & HypTr' & eq_sym).
                    assert ((q ▷ {[+ η +]} ⊎ m2) ⟶[μ1] (q' ▷ {[+ η +]} ⊎ m'2)) as HypTr''.
                    eapply add_in_mb_fw_action; eauto.
                    exists ((q' ▷ {[+ η +]} ⊎ m'2) ▷ p'2). eapply ParSync. eassumption.
                    assumption. assumption.
         ++ intros (q'' , mq'') Hstep_fw.
            inversion Hstep_fw; subst.
            +++ eapply H7; eauto. eapply ParLeft; eauto.
            +++ inversion l.
            +++ destruct eq as (duo' & nb').
                eapply non_blocking_action_in_ms in nb' as eq; eauto; subst.
                admit.
         ++ intros e' l. admit.
         ++ intros. admit. *)
    -- replace ({[+ η +]} ⊎ m ⊎ m2) with (m ⊎ ({[+ η +]} ⊎ m2)) by multiset_solver.
       eapply IHhwo. eassumption.
Qed.  (* existence d'une co_action nécéssaire *)

Lemma nf_must_fw `{
  @gLtsObaFB P A H gLtsP M K, !FiniteImagegLts P A ,
  @gLtsObaFB E A H gLtsE Y V , !Good E A good}

  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}
  `{@Prop_of_Inter (P * mb A) E A parallel_inter H (inter_lts fw_inter) gLtsE}

  (p : P) (e e' : E) m : 
  strip e m e' -> must (p, m) e' <-> must (p, ∅) e.
Proof.
  intros. split; intro hm.
  - eapply nf_must_fw_l; eauto. now rewrite gmultiset_disj_union_right_id.
  - rewrite <- gmultiset_disj_union_right_id. eapply nf_must_fw_r; eassumption.
Qed.

Lemma lts_oba_mo_strip `{gLtsOba P A} p : 
  exists q , strip p (lts_oba_mo p) q.
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

Lemma refuses_equiv `{gLtsEq P A} p q α : 
  p ⋍ q -> p ↛{ α } -> q ↛{ α }.
Proof.
  intros equiv refuses. destruct (decide (q ↛{α})) as [refuses_q | not_refuses_q].
  + assumption.
  + eapply lts_refuses_spec1 in not_refuses_q as (q' & l).
    edestruct (eq_spec p q') as (p' & l' & equiv'). exists q; eauto.
    assert (¬ p ↛{α}). eapply lts_refuses_spec2. eexists; eauto. contradiction.
Qed.

Lemma lts_oba_mo_strip_refuses `{gLtsOba P A} p q: 
  strip p (lts_oba_mo p) q 
  -> forall η, non_blocking η -> q ↛[η].
Proof.
  intros w.
  dependent induction w.
  - intros η nb.
    destruct (lts_refuses_decidable p (ActExt $ η)) as [refuses | not_refuses].
    + eapply refuses_equiv; eauto.
    + eapply lts_refuses_spec1 in not_refuses as (q & l).
      eapply lts_oba_mo_spec_bis1 in l. multiset_solver. eassumption.
  - eapply lts_oba_mo_spec2 in H2. rewrite <- x in H2.
    eapply gmultiset_eq_drop_l in H2. eauto. eassumption.
Qed.




Lemma not_in_mb_to_not_eq' `{gLtsOba P A} {μ p}: 
  μ ∉ lts_oba_mo p 
  -> Forall (NotEq μ) (elements (lts_oba_mo p)).
Proof.
  induction (lts_oba_mo p) using gmultiset_ind.
  + constructor.
  + intro not_in_mem.
    eapply simpl_P_in_l. split.
    ++ intro. subst. set_solver.
    ++ assert (μ ∉ g). set_solver. now eapply IHg.
Qed.

Lemma mo_stripped_equiv `{gLtsOba P A} r m r' r'' : 
  r ⟿{m} r'
  -> r' ⋍ r'' 
  -> r ⟿{m} r''.
Proof.
  intros stripped Hyp. revert Hyp.
  induction stripped.
  + intro Hyp. constructor. etransitivity; eauto. 
  + intro Hyp. econstructor; eauto.
Qed.

Lemma mo_stripped_equiv_rev `{gLtsOba P A} r m r' r'' : 
  r ⟿{m} r'
  -> r ⋍ r'' 
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
    p1 ⟿{m1} p2 
    -> p2 ⟿{m2} p3 
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
  r ⟿{m} r'
  -> (∀ η : A, non_blocking η -> r' ↛[η]) 
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
    intros. eapply refuses_equiv; eauto. symmetry. eauto.
Qed.

Lemma must_to_must_fw `{
  @gLtsObaFB P A H gLtsP M K, !FiniteImagegLts P A,
  @gLtsObaFB E A H gLtsE Y V, !Good E A good}

  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}
  `{@Prop_of_Inter (P * mb A) E A parallel_inter H (inter_lts fw_inter) gLtsE}
  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p : P) (e : E) (m : mb A) :
  must p e 
    -> m = lts_oba_mo e 
      -> forall e', strip e m e' 
        -> must (p, m) e'.
Proof.
  intros hm. revert m.
  dependent induction hm; intros m heq e' hmo.
  - eapply m_now. eapply woutpout_preserves_good; eauto.
  - eapply m_step; eauto with mdb.
    + intro hh. destruct nh. eapply woutpout_preserves_good_converse; eauto.
    + destruct ex as (t & l). inversion l; subst.
      ++ exists ((a2, lts_oba_mo e), e').
         eapply ParLeft. eapply ParLeft. assumption.
      ++ edestruct (woutpout_delay_tau hmo l0).
         +++ destruct H8 as (a & co_a & r & t & nb & duo & l1 & l2).
             eapply lts_oba_mo_spec2 in l1; eauto.
             exists (p, lts_oba_mo r, t). symmetry in duo.
             eapply (ParSync a co_a) ; simpl; eauto.
             rewrite l1. eapply ParRight.
             eapply lts_multiset_minus. eauto.
         +++ destruct H8 as (e'' & HypTr). eauto with mdb.
      ++ destruct (decide (non_blocking μ2)) as [nb |not_nb].
         +++ eapply lts_oba_mo_spec2 in l2 as h; eauto.
             exists (a2, lts_oba_mo b2, e'). eapply ParLeft.
             rewrite h. eapply ParSync. split.
             exact eq. exact nb. exact l1.
             eapply lts_multiset_minus; eauto.
         +++ assert (μ2 ∉ lts_oba_mo e) as not_in_mb. 
             eapply lts_oba_mo_non_blocking_contra; eauto.
             eapply not_in_mb_to_not_eq' in not_in_mb.
             edestruct (woutpout_delay_inp not_in_mb hmo l2) as (e3 & l3).
             exists (a2, lts_oba_mo e, e3).
             eapply ParSync; simpl; eauto.
             eapply ParLeft. assumption.
    + intros (p', m') l.
      inversion l; subst. 
      ++ eauto with mdb.
      ++ inversion l0.
      ++ assert (mem : μ2 ∈ ({[+ μ2 +]} ⊎ m')) by multiset_solver.
         destruct eq as (duo & nb). symmetry in duo.
         eapply non_blocking_action_in_ms in l2 as eq'; eauto; subst.
         rewrite <- eq' in hmo.
         eapply (aux0 μ2) in mem as (e0, l0); eauto.
         eapply (aux3_) in hmo as (t & hwo & heq); eauto.
         eapply must_eq_client. eassumption.
         symmetry in duo.
         eapply H7; eauto. 
         eapply lts_oba_mo_spec2 in l0; eauto.
         eapply (gmultiset_eq_drop_l {[+ μ2 +]}). now rewrite <- l0.
    + intros e0 l0.
      edestruct (woutpout_preserves_mu hmo l0) as (e1 & t & l & hwo1 & heq1).
      eapply must_eq_client. symmetry. eassumption.
      rewrite <- gmultiset_disj_union_right_id.
      eapply nf_must_fw_r. eassumption.
      destruct (lts_oba_mo_strip e1) as (e2 & hwo2).
      eapply nf_must_fw_l. eapply hwo2.
      rewrite gmultiset_disj_union_right_id.
      eapply H6; eauto with mdb.
    + intros (p', m') e0 μ1 μ2 duo l1 l2.
      destruct (decide (non_blocking μ2)) as [ nb | not_nb]; simpl in *.
      ++ rename μ2 into η. subst. inversion l1; subst.
         +++ rewrite <- gmultiset_disj_union_right_id.
             edestruct (woutpout_preserves_mu hmo l2) as (e3 & t & l3 & hwo1 & heq1).
             eapply must_eq_client. symmetry. eassumption.
             eapply nf_must_fw_r. eassumption.
             destruct (lts_oba_mo_strip e3) as (e3' & hwo3').
             eapply nf_must_fw_l. eapply hwo3'.
             rewrite gmultiset_disj_union_right_id.
             eapply H7; eauto with mdb.
         +++ exfalso. subst.
             eapply lts_refuses_spec2.
             exists e0. eassumption. eapply lts_oba_mo_strip_refuses; eauto.
       ++ destruct (decide (non_blocking μ1)) as [ nb1 | not_nb1];  simpl in *.
          +++ inversion l1; subst.
              ++++ rewrite <- gmultiset_disj_union_right_id.
                   edestruct (woutpout_preserves_mu hmo l2) as (e3 & t & l3 & hwo1 & heq1).
                   eapply must_eq_client. symmetry. eassumption.
                   eapply nf_must_fw_r. eassumption.
                   destruct (lts_oba_mo_strip e3) as (e3' & hwo3').
                   eapply nf_must_fw_l. eapply hwo3'.
                   rewrite gmultiset_disj_union_right_id.
                   eapply H7; eauto with mdb.
              ++++ eapply non_blocking_action_in_ms in nb1 as eq; eauto; subst.
                   assert (mem : μ1 ∈ lts_oba_mo e).
                   rewrite <- eq. multiset_solver.
                   eapply lts_oba_mo_spec_bis2 in mem as (u & nb'' & l'').
                   set (h := lts_oba_mo_spec2 _ _ _ nb'' l'').
                   rewrite <- eq in hmo.
                   destruct (aux3_ hmo _ l'') as (e1' & hwoe1' & heqe1').
                   destruct (eq_spec e1' e0 (ActExt $ μ2)) as (r & l4 & heq4). eauto.
                   edestruct (woutpout_preserves_mu hwoe1' l4) as (e2 & u' & le2 & hwoe2 & hequ').
                   symmetry in duo.
                   destruct (lts_oba_fb_feedback nb'' duo l'' le2) as (t & hlt & heqt).
                   eapply must_eq_client. eassumption.
                   rewrite <- gmultiset_disj_union_right_id.
                   eapply must_eq_client. symmetry. eassumption.
                   eapply nf_must_fw_r. eassumption.
                   eapply must_eq_client. eassumption.
                   edestruct (strip_eq hwoe2 t heqt) as (w & wmo & weq).
                   edestruct (lts_oba_mo_strip t) as (x & hwot).
                   eapply nf_must_fw_l. eassumption.
                   rewrite gmultiset_disj_union_right_id.
                   eapply H6. eassumption. reflexivity. eassumption.
        +++ inversion l1; subst.
            ++++ assert (e ⟿{lts_oba_mo e} e') as hmo'; eauto.
                 eapply (woutpout_preserves_mu) in hmo 
                  as (r & t' & l' & stripped & eq_equiv); eauto.
                 assert (lts_oba_mo t' = lts_oba_mo e0) as eq. 
                 eapply lts_oba_mo_eq. symmetry; eauto.
                 destruct (lts_oba_mo_strip e0) as (e0_strip & stripped').
                 destruct (lts_oba_mo_strip t') as (t'_strip & stripped'').
                 rewrite eq in stripped''.
                 assert (e0_strip ⋍ t'_strip). eapply strip_eq_sim; eauto.
                 assert (strip r (lts_oba_mo e ⊎ lts_oba_mo e0) t'_strip).
                 eapply strip_union; eauto.
                 assert (∀ η : A, non_blocking η → t'_strip ↛[η]).
                 rewrite<- eq in stripped''.
                 eapply lts_oba_mo_strip_refuses; eauto.
                 assert (lts_oba_mo e ⊎ lts_oba_mo e0 = lts_oba_mo r).
                 symmetry. eapply mo_stripped; eauto.
                 destruct (lts_oba_mo_strip r) as (r_stripped & stripped''').
                 assert ( t'_strip ⋍ r_stripped). rewrite H11 in H9. 
                 eapply strip_m_deter; eauto.
                 assert (e0_strip ⋍ r_stripped). etransitivity; eauto.
                 eapply (nf_must_fw_l (lts_oba_mo e0) (lts_oba_mo e)); eauto.
                 (* eapply strip_delay_inp4 in l' as (e'' & l'' & eq_equiv'); eauto.
                 destruct eq_equiv' as (e''' & l''' & equiv). *)
                 apply (H7 p' r μ1 μ2) ; eauto. multiset_solver.
                 assert (lts_oba_mo e ⊎ lts_oba_mo e0 = lts_oba_mo e0 ⊎ lts_oba_mo e) as eq''.
                 multiset_solver. rewrite<- eq''. eauto. rewrite H11.
                 eapply mo_stripped_equiv; eauto. symmetry; eauto.
            ++++ eapply blocking_action_in_ms in not_nb1 as (eq & duo' & nb'); subst ; eauto.
                 assert (non_blocking μ2). eapply nb_not_nb; eauto.
                 contradiction.
Qed.

Lemma must_fw_to_must `{
  @gLtsObaFB P A H gLtsP M K, !FiniteImagegLts P A,
  @gLtsObaFB E A H gLtsE Y V, !Good E A good}

  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}
  `{@Prop_of_Inter (P * mb A) E A parallel_inter H (inter_lts fw_inter) gLtsE}
  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p : P) (e : E) : must (p, ∅) e -> must p e.
Proof.
  intro hm.
  dependent induction hm; eauto with mdb.
  eapply m_step; eauto with mdb.
  - edestruct (lts_oba_mo_strip e) as (e' & hwo).
    assert (must (p, lts_oba_mo e) e'). eapply nf_must_fw; eauto with mdb.
    inversion H5; subst.
    + exfalso. eapply woutpout_preserves_good_converse in H9; eauto.
    + destruct ex0 as (((p0, m0), e0) & l).
      inversion l; subst.
      ++ inversion l0; subst.
         +++ eauto with mdb.
         +++ inversion l1.
         +++ destruct eq as (duo & nb).
             eapply non_blocking_action_in_ms in nb as eq; subst; eauto.
             assert (μ2 ∈ lts_oba_mo e) as mem. rewrite <- eq. set_solver.
             eapply lts_oba_mo_spec_bis2 in mem as (e'2 & nb' & l'2).
             exists (p0, e'2). eapply ParSync; eauto.
      ++ eapply woutpout_preserves_mu in l0 as (r0 & r1 & l0 & _); eauto.
         eauto with mdb.
      ++ destruct (decide (non_blocking μ2)); destruct (decide (non_blocking μ1)). 
         +++ exfalso. eapply lts_oba_fw_non_blocking_duo_spec. eauto. symmetry; eauto. eauto.
         +++ exfalso. eapply (lts_refuses_spec2 e').
             exists e0. exact l2. eapply lts_oba_mo_strip_refuses; eauto.
         +++ eapply woutpout_preserves_mu in l2 as (r0 & r1 & l0 & _); eauto.
             inversion l1; subst.
             ++++ exists (p0, r0). 
                  eapply ParSync ; eauto.
             ++++ eapply non_blocking_action_in_ms in n0 as eq' ; eauto ; subst.
                  assert (μ1 ∈ lts_oba_mo e) as mem. rewrite <- eq'. set_solver.
                  eapply lts_oba_mo_spec_bis2 in mem as (e2 & nb' & l'2).
                  assert (neq : μ2 ≠ μ1). eapply BlockingAction_are_not_non_blocking; eauto.
                  edestruct (lts_oba_non_blocking_action_confluence nb' neq l'2 l0) as (e3 & l3 & l4).
                  assert (dual μ1 μ2) as duo. symmetry; eauto.
                  destruct (lts_oba_fb_feedback nb' duo l'2 l3) as (e4 & l6 & _).
                  eauto with mdb.
        +++ inversion l1; subst.
            ++++ eapply woutpout_preserves_mu in hwo; eauto.
                 destruct hwo as (r & t' & l3 & stripped & equiv).
                 exists (p0, r).
                 eapply ParSync; eauto.
            ++++ eapply blocking_action_in_ms in n0 as (eq' & duo' & nb'); eauto; subst.
                 assert (non_blocking μ2) as nb''.
                 eapply nb_not_nb. eauto. exact duo'. eauto. contradiction.
  - intros p' l. eapply H8; eauto with mdb. eapply ParLeft; eauto.
  - intros p' e' μ1 μ2 duo l1 l2. eapply H6; eauto with mdb. eapply ParLeft; eauto.
Qed.

Lemma must_iff_must_fw `{
  @gLtsObaFB P A H gLtsP M K, !FiniteImagegLts P A,
  @gLtsObaFB E A H gLtsE Y V , !Good E A good}

  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}
  `{@Prop_of_Inter (P * mb A) E A parallel_inter H (inter_lts fw_inter) gLtsE}
  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p : P) (e : E) :
  must p e <-> must (p, ∅) e.
Proof.
  split; intro hm.
  - edestruct (lts_oba_mo_strip e) as (e' & hmo).
    eapply nf_must_fw_l. eassumption.
    rewrite gmultiset_disj_union_right_id.
    eapply must_to_must_fw. eassumption. reflexivity. eassumption.
  - eapply must_fw_to_must; eauto.
Qed.

Lemma lift_fw_ctx_pre `{
    @gLtsObaFB P A H gLtsP LOP V, !FiniteImagegLts P A,
    @gLtsObaFB Q A H gLtsQ LOQ W, !FiniteImagegLts Q A,
    @gLtsObaFB E A H gLtsE LOE Y, !Good E A good}

  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}

  `{@Prop_of_Inter (P * mb A) E A parallel_inter H (inter_lts fw_inter) gLtsE}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  `{@Prop_of_Inter Q (mb A) A fw_inter H gLtsQ MbgLts}

  `{@Prop_of_Inter (Q * mb A) E A parallel_inter H (inter_lts fw_inter) gLtsE}

  `{@Prop_of_Inter Q E A parallel_inter H gLtsQ gLtsE}
    
    
  (p : P) (q : Q) : p ⊑ q <-> (p, ∅) ⊑ (q, ∅).
Proof.
  split; intros hctx e hm%must_iff_must_fw. 
  - rewrite <- must_iff_must_fw. eauto.
  - rewrite must_iff_must_fw. eauto.
Qed.
