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

From Coq.Unicode Require Import Utf8.
From Coq.Lists Require Import List.
Import ListNotations.
From Coq.Program Require Import Equality.
From stdpp Require Import (* base *) countable (* list decidable finite gmap gmultiset. *) .
From Must Require Import ForAllHelper MultisetHelper.
From Must Require Import gLts Bisimulation Lts_OBA Lts_FW.
From Must Require Import ActTau Termination WeakTransitions.

(************************************** Convergence **************************************)

(* Convergence definition *)

Reserved Notation "p ⇓ s" (at level 70).

Inductive cnv `{gLts P A} : P -> trace A -> Prop :=
| cnv_nil p : p ⤓ -> p ⇓ ε
| cnv_act p μ s : p ⤓ -> (forall q, p ⟹{μ} q -> q ⇓ s) -> p ⇓ μ :: s

where "p ⇓ s" := (cnv p s).

Global Hint Constructors cnv:mdb.

(* Properties on convergence in Lts *)

Lemma cnv_terminate `{M : gLts P A} p s : p ⇓ s -> p ⤓.
Proof. by intros hcnv; now inversion hcnv. Qed.

Lemma cnv_preserved_by_lts_tau `{M : gLts P A} s p : p ⇓ s -> forall q, p ⟶ q -> q ⇓ s.
Proof.
  intros hcnv q l.
  inversion hcnv; subst.
  - eapply cnv_nil. inversion H0; eauto.
  - eapply cnv_act.
    + inversion H0; eauto.
    + eauto with mdb.
Qed.

Lemma cnv_preserved_by_wt_nil `{M : gLts P A} s p :
  p ⇓ s -> forall q, p ⟹ q -> q ⇓ s.
Proof.
  intros hcnv q w.
  dependent induction w; eauto with mdb.
  eapply IHw. eapply cnv_preserved_by_lts_tau; eauto. reflexivity.
Qed.

Lemma cnv_preserved_by_wt_act `{M: gLts P A} s p μ :
  p ⇓ μ :: s -> forall q, p ⟹{μ} q -> q ⇓ s.
Proof. by intros hcnv; inversion hcnv; eauto with mdb. Qed.

Lemma cnv_iff_prefix_terminate_l `{M: gLts P A} p s :
  p ⇓ s -> (forall t q, t `prefix_of` s -> p ⟹[t] q -> q ⤓).
Proof.
  intros hcnv t q hpre w.
  revert s p q hcnv hpre w.
  dependent induction t; intros.
  - eapply cnv_terminate, cnv_preserved_by_wt_nil; eassumption.
  - eapply wt_pop in w as (p' & w0 & w1).
    inversion hpre; subst. simpl in hcnv.
    eapply (IHt (t ++ x) p' q).
    eapply cnv_preserved_by_wt_act; eauto.
    now eapply prefix_cons_inv_2 in hpre.
    eassumption.
Qed.

Lemma cnv_iff_prefix_terminate_r `{M: gLts P A} p s :
  (forall t q, t `prefix_of` s -> p ⟹[t] q -> q ⤓) -> p ⇓ s.
Proof.
  intros h.
  revert p h.
  dependent induction s; intros; eauto with mdb.
  eapply cnv_act; eauto with mdb.
  eapply (h []) ; eauto with mdb; eapply prefix_nil.
  intros q w. eapply IHs.
  intros t r hpre w1.
  eapply (h (a :: t)); eauto with mdb. eapply prefix_cons. eassumption.
  eapply wt_push_left; eassumption.
Qed.

Corollary cnv_iff_prefix_terminate `{M: gLts P A} p s :
  p ⇓ s <-> (forall s0 q, s0 `prefix_of` s -> p ⟹[s0] q -> q ⤓).
Proof.
  split; [eapply cnv_iff_prefix_terminate_l|eapply cnv_iff_prefix_terminate_r].
Qed.

Lemma cnv_wt_prefix `{M: gLts P A} s1 s2 p :
  p ⇓ s1 ++ s2 -> forall q, p ⟹[s1] q -> q ⇓ s2.
Proof.
  revert s2 p.
  dependent induction s1; intros s2 p hcnv q w.
  - eapply cnv_preserved_by_wt_nil; eauto with mdb.
  - eapply wt_pop in w as (p' & w0 & w1).
    inversion hcnv; eauto with mdb.
Qed.

Lemma terminate_preserved_by_wt_nil `{M: gLts P A} p : p ⤓ -> forall q, p ⟹ q -> q ⤓.
Proof.
  intros hcnv q w.
  dependent induction w; eauto with mdb.
  eapply IHw. eapply terminate_preserved_by_lts_tau; eauto. reflexivity.
Qed.

(* Properties on convergence in Lts with a Bissimulation *)

Lemma cnv_preserved_by_eq `{gLtsEq P A} p q s : 
  p ⋍ q -> p ⇓ s 
    -> q ⇓ s.
Proof.
  intros heq hcnv. revert q heq.
  induction hcnv; intros.
  - eapply cnv_nil.
    eapply (terminate_preserved_by_eq H2 heq).
  - eapply cnv_act.
    + eapply (terminate_preserved_by_eq H2 heq).
    + intros t w.
      destruct (eq_spec_wt q p (symmetry heq) t [μ] w) as (t' & hlt' & heqt').
      eapply (H4 t' hlt' t heqt').
Qed.

(* Properties on convergence in Lts with OBA axioms *)

Lemma terminate_preserved_by_wt_non_blocking_action `{M: gLtsOba P A} p q η : 
  non_blocking η -> p ⤓ -> p ⟹{ η } q -> q ⤓.
Proof.
  intros nb ht w.
  dependent induction w.
  - eapply IHw; eauto. eapply terminate_preserved_by_lts_tau; eauto.
  - eapply terminate_preserved_by_wt_nil.
    eapply terminate_preserved_by_lts_non_blocking_action; eauto. assumption.
Qed.

(* Properties on convergence in Lts with Forwarder axioms *)

Lemma cnv_preserved_by_lts_non_blocking_action `{gLtsObaFW P A} p q η s :
  non_blocking η -> p ⇓ s -> p ⟶[η] q
    -> q ⇓ s.
Proof.
  revert p q η.
  induction s as [|μ s']; intros p q η nb hacnv l.
  - eapply cnv_nil. inversion hacnv. subst.
    eapply terminate_preserved_by_lts_non_blocking_action; eassumption.
  - inversion hacnv as [|p'  μ'  T  Hyp_p_conv Hyp_conv_through_μ];subst.
    eapply cnv_act.
    + eapply terminate_preserved_by_lts_non_blocking_action; eassumption.
    + intros r w.
      destruct (delay_wt_non_blocking_action nb (mk_lts_eq l) w) as (t & w0 & l1).
      destruct l1 as (r' & l2 & heq).
      eapply cnv_preserved_by_eq. eassumption.
      eapply IHs'. exact nb. eapply Hyp_conv_through_μ, w0.
      eassumption.
Qed.

Lemma cnv_preserved_by_wt_non_blocking_action `{gLtsObaFW P A} p q η s :
  non_blocking η -> p ⇓ s -> p ⟹{η} q
    -> q ⇓ s.
Proof.
  intros nb hcnv w.
  destruct (wt_decomp_one w) as (r1 & r2 & w1 & l0 & w2).
  eapply (cnv_preserved_by_wt_nil _ r2); eauto.
  eapply (cnv_preserved_by_lts_non_blocking_action r1); eauto.
  eapply cnv_preserved_by_wt_nil; eauto.
Qed.

Lemma cnv_drop_input_hd `{gLtsObaFW P A} p μ s :
  (exists η, non_blocking η /\ dual η μ) -> p ⇓ μ :: s
    -> p ⇓ s.
Proof.
  intros Hyp hacnv. destruct Hyp as [η Hyp]. destruct Hyp as [nb duo].
  inversion hacnv as [|p'  μ'  T  Hyp_p_conv Hyp_conv_through_μ];subst.
  destruct (lts_oba_fw_forward p η μ) as (r & l1 & l2). eassumption. eassumption.
  eapply cnv_preserved_by_lts_non_blocking_action. eassumption.
  eapply Hyp_conv_through_μ. eapply wt_act. eassumption. eapply wt_nil. eapply l2.
Qed. 

(* fixme: it should be enought to have ltsOba + one of the feedback *)
Lemma cnv_retract_lts_non_blocking_action `{gLtsObaFW P A} p q η μ s :
  non_blocking η -> dual η μ -> p ⇓ s -> p ⟶[η] q -> q ⇓ μ :: s.
Proof.
  intros nb duo hcnv l.
  eapply cnv_act.
  - inversion hcnv; eapply terminate_preserved_by_lts_non_blocking_action; eassumption.
  - intros q' w.
    destruct (wt_decomp_one w) as (r1 & r2 & w1 & l0 & w2).
    destruct (delay_wt_non_blocking_action nb (mk_lts_eq l) w1) as (t & w0 & l1).
    destruct l1 as (r' & l1 & heq).
    edestruct (eq_spec r' r2) as (r & hlr & heqr). exists r1. eauto.
    eapply (cnv_preserved_by_wt_nil _ r2); eauto.
    eapply cnv_preserved_by_eq. eassumption.
    destruct (lts_oba_fw_feedback nb duo l1 hlr) as [(t0 & hlt0 & heqt0)|].
    eapply cnv_preserved_by_eq. eassumption.
    eapply cnv_preserved_by_lts_tau.
    eapply (cnv_preserved_by_wt_nil _ p); eauto. eassumption.
    eapply cnv_preserved_by_eq. eassumption.
    eapply (cnv_preserved_by_wt_nil _ p); eauto.
Qed.

Lemma cnv_retract_wt_non_blocking_action `{gLtsObaFW P A} p q η μ s :
  non_blocking η -> dual η μ -> p ⇓ s -> p ⟹{η} q
    -> q ⇓ μ :: s.
Proof.
  intros nb duo hcnv w.
  eapply wt_decomp_one in w as (t1 & t2 & w1 & l & w2).
  eapply cnv_preserved_by_wt_nil; eauto.
  eapply (cnv_retract_lts_non_blocking_action t1); eauto.
  eapply cnv_preserved_by_wt_nil; eauto.
Qed.

Lemma cnv_input_swap `{gLtsObaFW P A} p μ1 μ2 s :
  (exists η1, non_blocking η1 /\ dual η1 μ1) -> (exists η2, non_blocking η2 /\ dual η2 μ2) -> p ⇓ μ1 :: μ2 :: s 
    -> p ⇓ μ2 :: μ1 :: s.
Proof.
  intros BlocDuo1 BlocDuo2 hcnv. 
  destruct BlocDuo1 as (η1 & nb1 & duo1).
  destruct BlocDuo2 as (η2 & nb2 & duo2).
  destruct (lts_oba_fw_forward p η1 μ1) as (t0 & l1 & l2). eassumption. eassumption.
  destruct (lts_oba_fw_forward t0 η2 μ2) as (t1 & l3 & l4). eassumption. eassumption.
  inversion hcnv; subst.
  eapply cnv_act; eauto.
  intros q w1. eapply cnv_act.
  - destruct (delay_wt_non_blocking_action nb1 (mk_lts_eq l2) w1) as (t' & w2 & (t2 & hlt2 & heqt2)).
    eapply (terminate_preserved_by_eq2 heqt2).
    eapply (terminate_preserved_by_lts_non_blocking_action nb1 hlt2).
    eapply (cnv_terminate t' s).
    eapply cnv_preserved_by_wt_act; eauto with mdb.
  - intros r w2.
    edestruct (wt_input_swap) as (t & w' & heq'). exists η1. eauto.
    eapply wt_push_left. eapply w1. eapply w2.
    eapply cnv_preserved_by_eq.
    eapply heq'.
    eapply (cnv_wt_prefix [μ1 ; μ2]); eauto.
Qed.

Lemma cnv_input_perm `{gLtsObaFW P A} p s1 s2 :
  Forall exist_co_nba s1 -> s1 ≡ₚ s2 -> p ⇓ s1
    -> p ⇓ s2.
Proof.
  intros his hp hcnv.
  revert p his hcnv.
  induction hp; intros; eauto with mdb.
  - inversion hcnv; subst.
    eapply cnv_act; eauto with mdb.
    intros q w. eapply IHhp; eauto with mdb.
    now inversion his.
  - inversion his as [|? ? Hyp_co_act Hyp_list_co_act]; subst. 
    inversion Hyp_list_co_act as [|? ? Hyp_co_act' Hyp_list_co_act']; subst.
    destruct Hyp_co_act, Hyp_co_act'. 
    eapply cnv_input_swap; eauto. 
  - eapply IHhp2. eapply are_actions_preserved_by_perm; eauto.
    eapply IHhp1. eapply are_actions_preserved_by_perm; eauto.
    eassumption.
Qed.

Lemma cnv_non_blocking_action_swap `{gLtsObaFW P A} p η1 η2 s :
  non_blocking η1 -> non_blocking η2 -> p ⇓ η1 :: η2 :: s
    -> p ⇓ η2 :: η1 :: s.
Proof.
  intros nb1 nb2 hcnv.
  eapply cnv_act.
  - now inversion hcnv.
  - intros q hw1.
    eapply cnv_act.
    eapply (cnv_terminate q []).
    eapply cnv_preserved_by_wt_non_blocking_action; eauto. eapply cnv_nil. now inversion hcnv.
    intros t hw2.
    replace (η1 :: η2 :: s) with ([η1 ; η2] ++ s) in hcnv.
    set (hw3 := wt_concat _ _ _ _ _ hw1 hw2). simpl in hw3.
    eapply wt_non_blocking_action_swap in hw3 as (t' & hw4 & eq').
    eapply cnv_preserved_by_eq. eassumption.
    eapply cnv_wt_prefix. eauto. eassumption.
    now simpl. now simpl. now simpl.
Qed.

Lemma cnv_non_blocking_action_perm `{gLtsObaFW P A} p s1 s2 :
  Forall non_blocking s1 -> s1 ≡ₚ s2 -> p ⇓ s1
    -> p ⇓ s2.
Proof.
  intros hos hp hcnv.
  revert p hos hcnv.
  induction hp; intros; eauto with mdb.
  - inversion hcnv; subst.
    eapply cnv_act; eauto with mdb.
    intros q w. eapply IHhp; eauto with mdb.
    now inversion hos.
  - inversion hos as [| ? ? nb Hyp_nb_list]; subst. inversion Hyp_nb_list;subst.
    now eapply cnv_non_blocking_action_swap.
  - eapply IHhp2.
    eapply Permutation_Forall; eassumption.
    eapply IHhp1.
    eapply Permutation_Forall. now symmetry. eassumption.
    eassumption.
Qed.

Lemma cnv_retract `{gLtsObaFW P A} p q s1 s2 s3:
  Forall non_blocking s1 -> Forall2 dual s1 s3 -> p ⇓ s2 -> p ⟹[s1] q
    -> q ⇓ s3 ++ s2.
Proof. 
  revert s2 s3 p q.
  induction s1; intros s2 s3 p q hos duo hcnv w; inversion duo ; subst.
  - eapply cnv_preserved_by_wt_nil ; eauto.
  - inversion hos. subst. 
    eapply push_wt_non_blocking_action in w as (q' & hwq' & heqq').
    eapply wt_split in hwq' as (t & w1 & w2).
    eapply cnv_preserved_by_eq. eassumption. subst.
    eapply cnv_retract_wt_non_blocking_action; eauto. eauto.
Qed.

Lemma cnv_drop_action_in_the_middle `{gLtsObaFW P A} p s1 s2 μ :
  Forall exist_co_nba s1 -> p ⇓ s1 ++ [μ] ++ s2 -> forall r, p ⟶[μ] r
    -> r ⇓ s1 ++ s2.
Proof.
  intros his hcnv r l.
  revert p s2 μ his hcnv r l.
  dependent induction s1; intros.
  - simpl in *.
    eapply cnv_preserved_by_wt_act; eauto. eapply lts_to_wt; eauto.
  - inversion his; subst.
    destruct H4 as (a' & nb & inter).
    assert (blocking a) as not_nb.
    { eapply dual_blocks; eauto. }
    assert (a' = co a) as eq_subst.
    { eapply unique_nb; eauto. } subst.
    edestruct (lts_oba_fw_forward p (co a) a) as (p_a & Hyp).
    destruct (Hyp nb inter) as (tr_b & tr_nb).
    edestruct (lts_oba_non_blocking_action_delay nb tr_nb l) as (p'_a & tr'_b & r' & tr'_nb & equiv').
    assert (p'_a ⇓ s1 ++ s2).
    { eapply IHs1; eauto. eapply cnv_preserved_by_wt_act; eauto. eapply lts_to_wt; eauto. }
    eapply cnv_preserved_by_eq; eauto.
    eapply cnv_retract_wt_non_blocking_action; eauto. eapply lts_to_wt; eauto.
Qed.

Lemma cnv_annhil `{gLtsObaFW P A} p μ η s1 s2 s3 :
  Forall exist_co_nba s1 -> Forall exist_co_nba s2 -> non_blocking η -> dual η μ -> p ⇓ s1 ++ [μ] ++ s2 ++ [η] ++ s3
    -> p ⇓ s1 ++ s2 ++ s3.
Proof.
  intros his1 his2 nb duo hcnv.
  eapply EquivDef in his1 as [s1' nbs1_duos1]. destruct nbs1_duos1 as [nbs1 duos1].
  eapply EquivDef in his2 as [s2' nbs2_duos2]. destruct nbs2_duos2 as [nbs2 duos2].
  assert (Forall non_blocking (s1' ++ [η] ++ s2')).
  eapply Forall_app. split; eauto.
  eapply Forall_app. split; eauto.
  assert (Forall2 dual (s1' ++ [η] ++ s2') (s1 ++ [μ] ++ s2)).
  eapply Forall2_app. assumption.
  eapply Forall2_app. apply Forall2_cons. assumption. apply Forall2_nil. assumption.
  edestruct (forward_s p (s1 ++ [μ] ++ s2)) as (t & w1 & w2); eauto.
  destruct w2 as (r & hwr & heqr).
  eapply (wt_non_blocking_action_perm _ ([η] ++ s1' ++ s2')) in hwr as (r0 & hwr0 & heqr0).
  eapply wt_split in hwr0 as (r1 & hwr0 & hwr1).
  rewrite app_assoc.
  eapply cnv_preserved_by_eq. etrans. eapply heqr0. eapply heqr.
  assert (Forall non_blocking (s1' ++ s2')).
  eapply Forall_app. split; assumption.
  assert (Forall2 dual (s1' ++ s2') (s1 ++ s2)).
  eapply Forall2_app; assumption.
  eapply cnv_retract; eauto.
  eapply cnv_wt_prefix. rewrite 3 app_assoc in hcnv.
  eassumption.
  eapply wt_concat. rewrite <- app_assoc. eassumption. eassumption.
  eassumption.
  symmetry. eapply Permutation_app_swap_app.
Qed.

Lemma cnv_prefix `{gLts P A} {p : P} {s1 s2} : p ⇓ s1 ++ s2 -> p ⇓ s1.
Proof.
  revert s2 p. induction s1; intros.
  - eapply cnv_nil. now inversion H1.
  - eapply cnv_act. now inversion H1.
    intros q hw. inversion H1; subst. eauto.
Qed.

Lemma cnv_jump `{gLts P A} s1 s2 p : p ⇓ s1 -> (forall q, p ⟹[s1] q -> q ⇓ s2) -> p ⇓ s1 ++ s2.
Proof.
  revert s2 p.
  induction s1 as [| μ s']; intros s2 p hcnv hs2.
  - eapply hs2. eauto with mdb.
  - simpl. eapply cnv_act.
    + now inversion hcnv.
    + intros t w.
      eapply IHs'. inversion hcnv; eauto.
      intros. eapply hs2. eapply wt_push_left; eauto.
Qed.




