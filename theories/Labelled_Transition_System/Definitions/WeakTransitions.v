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

From Coq Require ssreflect Setoid.
From Coq.Unicode Require Import Utf8.
From Coq.Lists Require Import List.
Import ListNotations.
From Coq.Wellfounded Require Import Inverse_Image.
From Coq.Logic Require Import JMeq ProofIrrelevance.
From Coq.Program Require Import Wf Equality.
From stdpp Require Import base countable list decidable finite gmap gmultiset.
From Must Require Import ActTau ForAllHelper MultisetHelper gLts Bisimulation Lts_OBA Lts_FW.

(********************************** Weak transitions ***************************************)

(* Definition weak transitions *)

Inductive wt `{gLts P A} : P -> trace A -> P -> Prop :=
| wt_nil p : wt p [] p
| wt_tau s p q t (l : p ⟶ q) (w : wt q s t) : wt p s t
| wt_act μ s p q t (l : p ⟶[μ] q) (w : wt q s t) : wt p (μ :: s) t
.

Global Hint Constructors wt:mdb.

Notation "p ⟹ q" := (wt p [] q) (at level 30).
Notation "p ⟹{ μ } q" := (wt p [μ] q) (at level 30, format "p  ⟹{ μ }  q").
Notation "p ⟹[ s ] q" := (wt p s q) (at level 30, format "p  ⟹[ s ]  q").

Definition wt_sc `{gLts P A, !gLtsEq P A} p s q := ∃ r, p ⟹[s] r /\ r ⋍ q.

Notation "p ⟹⋍ q" := (wt_sc p [] q) (at level 30, format "p  ⟹⋍  q").
Notation "p ⟹⋍{ μ } q" := (wt_sc p [μ] q) (at level 30, format "p  ⟹⋍{ μ }  q").
Notation "p ⟹⋍[ s ] q" := (wt_sc p s q) (at level 30, format "p  ⟹⋍[ s ]  q").

(* Weak transitions properties in Lts *)

Lemma wt_pop `{gLts P A} p q μ s : p ⟹[μ :: s] q -> ∃ t, p ⟹{μ} t /\ t ⟹[s] q.
Proof.
  intro w.
  dependent induction w; eauto with mdb.
  destruct (IHw μ s JMeq_refl) as (r & w1 & w2).
  exists r. eauto with mdb.
Qed.

Lemma wt_concat `{gLts P A} p q r s1 s2 :
  p ⟹[s1] q -> q ⟹[s2] r -> p ⟹[s1 ++ s2] r.
Proof. intros w1 w2. dependent induction w1; simpl; eauto with mdb. Qed.

Lemma wt_push_left `{gLts P A} {p q r μ s} :
  p ⟹{μ} q -> q ⟹[s] r -> p ⟹[μ :: s] r.
Proof.
  intros w1 w2.
  replace (μ :: s) with ([μ] ++ s) by eauto.
  eapply wt_concat; eauto.
Qed.

Lemma wt_split `{gLts P A} p q s1 s2 :
  p ⟹[s1 ++ s2] q -> ∃ r, p ⟹[s1] r /\ r ⟹[s2] q.
Proof.
  revert p q.
  dependent induction s1; intros p q w.
  - eauto with mdb.
  - simpl in w. eapply wt_pop in w as (r & w1 & w2).
    eapply IHs1 in w2 as (r' & w2 & w3).
    exists r'. split. eapply wt_push_left; eauto. assumption.
Qed.

Lemma wt_push_nil_left `{gLts P A} {p q r s} : p ⟹ q -> q ⟹[s] r -> p ⟹[s] r.
Proof. by intros w1 w2; dependent induction w1; eauto with mdb. Qed.

Lemma wt_push_nil_right `{gLts P A} p q r s : p ⟹[s] q -> q ⟹ r -> p ⟹[s] r.
Proof.
  intros w1 w2. replace s with (s ++ ([] : trace A)).
  eapply wt_concat; eauto. eapply app_nil_r.
Qed.

Lemma wt_push_right `{gLts P A} p q r μ s :
  p ⟹[s] q -> q ⟹{μ} r -> p ⟹[s ++ [μ]] r.
Proof. intros w1 w2. eapply wt_concat; eauto. Qed.

Lemma wt_decomp_one `{gLts P A} {μ p q} : p ⟹{μ} q -> ∃ r1 r2, p ⟹ r1 ∧ r1 ⟶[μ] r2 ∧ r2 ⟹ q.
Proof.
  intro w.
  dependent induction w; eauto with mdb.
  destruct (IHw μ JMeq_refl) as (r1 & r2 & w1 & l' & w2).
  exists r1, r2. eauto with mdb.
Qed.

Lemma wt_join_nil `{gLts P A} {p q r} : p ⟹ q -> q ⟹ r -> p ⟹ r.
Proof. intros w1 w2. dependent induction w1; eauto with mdb. Qed.

Lemma lts_to_wt `{gLts P A} {p q μ} : p ⟶[μ] q -> p ⟹{μ} q.
Proof. eauto with mdb. Qed.

Lemma lts_to_wt_tau`{gLts P A} {p q} : p ⟶ q -> p ⟹ q.
Proof. intros tr'. eapply wt_tau;eauto. constructor. Qed.

(* Properties on weak transitions in Lts with a Bisimulation *)

Lemma eq_spec_wt `{gLtsEq P A} p p' : p ⋍ p' -> forall q s, p ⟹[s] q -> p' ⟹⋍[s] q.
Proof.
  intros heq q s w.
  revert p' heq.
  dependent induction w; intros.
  + exists p'; split. eauto with mdb. now symmetry.
  + edestruct eq_spec as (t' & hlt' & heqt').
    exists p. split; [symmetry|]; eassumption.
    destruct (IHw t' (symmetry heqt')) as (u & hlu' & hequ').
    exists u. eauto with mdb.
  + edestruct eq_spec as (t' & hlt' & heqt').
    exists p. split; [symmetry|]; eassumption.
    destruct (IHw t' (symmetry heqt')) as (u & hlu' & hequ').
    exists u. eauto with mdb.
Qed.

Lemma lts_sc_to_wt_sc `{gLtsEq P A} {p q μ} : p ⟶⋍[μ] q -> p ⟹⋍{ μ } q.
Proof. intros (p' & tr' & eq). exists p'. split. now eapply lts_to_wt. eauto with mdb. Qed.

Lemma lts_sc_to_wt_tau_sc `{gLtsEq P A} {p q} : p ⟶⋍ q -> p ⟹⋍ q.
Proof. intros (p' & tr' & eq). exists p'. split. eapply wt_tau;eauto. eapply wt_nil. eauto with mdb. Qed.

Lemma wt_join_nil_eq `{gLtsEq P A} {p q r} : p ⟹⋍ q -> q ⟹⋍ r -> p ⟹⋍ r.
Proof.
  intros (q' & hwq' & heqq') (r' & hwr' & heqr').
  destruct (eq_spec_wt _ _ (symmetry heqq') r' [] hwr') as (r1 & hwr1 & heqr1).
  exists r1. split. eapply (wt_push_nil_left hwq' hwr1). etrans; eassumption.
Qed.

Lemma wt_join_nil_eq_l `{gLtsEq P A} {p q r s} : p ⟹⋍ q -> q ⟹[s] r -> p ⟹⋍[s] r.
Proof.
  intros (q' & hwq' & heqq') w2.
  destruct (eq_spec_wt _ _ (symmetry heqq') r s w2) as (r1 & hwr1 & heqr1).
  exists r1. split. eapply (wt_push_nil_left hwq' hwr1). eassumption.
Qed.

Lemma wt_join_nil_eq_r `{gLtsEq P A} {p q r s} : p ⟹[s] q -> q ⟹⋍ r -> p ⟹⋍[s] r.
  intros w1 (r' & hwr' & heqr').
  exists r'. split. eapply wt_push_nil_right; eauto. eassumption.
Qed.

Lemma wt_join_eq `{gLtsEq P A} {p q r s1 s2} : p ⟹⋍[s1] q -> q ⟹⋍[s2] r -> p ⟹⋍[s1 ++ s2] r.
  revert p q r s2.
Proof.
  induction s1; intros p q r s2 (q' & hwq' & heqq') w2; simpl in *.
  - destruct w2 as  (r' & hwr' & heqr').
    destruct (eq_spec_wt _ _ (symmetry heqq') r' s2 hwr') as (r1 & hwr1 & heqr1).
    exists r1. split. eapply (wt_push_nil_left hwq' hwr1). etrans; eassumption.
  - eapply wt_pop in hwq' as (p0 & w0 & w1).
    edestruct IHs1 as (t' & hwt' & heqt').
    exists q'. split; eassumption. eassumption.
    exists t'. split. eapply (wt_push_left w0 hwt'). eassumption.
Qed.

Lemma wt_join_eq_l `{gLtsEq P A} {p q r s1 s2} : p ⟹⋍[s1] q -> q ⟹[s2] r -> p ⟹⋍[s1 ++ s2] r.
Proof.
  intros (q' & hwq' & heqq') w2.
  destruct (eq_spec_wt _ _ (symmetry heqq') r s2 w2) as (r1 & hwr1 & heqr1).
  exists r1. split. eapply wt_concat; eassumption. eassumption.
Qed.

Lemma wt_join_eq_r `{gLtsEq P A} {p q r s1 s2} :
  p ⟹[s1] q -> q ⟹⋍[s2] r 
    -> p ⟹⋍[s1 ++ s2] r.
Proof.
  intros w1 (r' & hwr' & heqr').
  exists r'. split. eapply wt_concat; eassumption. eassumption.
Qed.

(* Properties on weak transitions in Lts with OBA axioms *)

Lemma refuses_tau_preserved_by_wt_non_blocking_action `{gLtsOba P A} p q s :
  Forall non_blocking s ->  p ↛ -> p ⟹[s] q -> q ↛.
Proof.
  intros s_spec hst hw.
  induction hw; eauto.
  - eapply lts_refuses_spec2 in hst. now exfalso. eauto.
  - inversion s_spec; subst.
    eapply IHhw. eassumption. eapply refuses_tau_preserved_by_lts_non_blocking_action; eauto.
Qed. 

Lemma refuses_tau_action_preserved_by_wt_non_blocking_action `{gLtsOba P A} p q s μ :
  Forall non_blocking s -> p ↛ -> p ↛[μ] -> p ⟹[s] q -> q ↛[μ].
Proof.
  intros s_spec hst_tau hst_inp hw.
  induction hw; eauto.
  - eapply lts_refuses_spec2 in hst_tau. now exfalso. eauto.
  - inversion s_spec; subst. eapply IHhw. 
    + assumption.
    + eapply refuses_tau_preserved_by_lts_non_blocking_action; eauto.
    + eapply refuses_action_preserved_by_lts_non_blocking_action; eauto.
Qed.

Lemma lts_input_preserved_by_wt_output `{gLtsOba P A} p q s μ :
  Forall non_blocking s 
    -> Forall (NotEq μ) s -> p ↛ -> (exists t, p ⟶[μ] t) -> p ⟹[s] q 
      -> (exists t, q ⟶[μ] t).
Proof.
  intros s_spec1 s_spec2 hst_tau hst_inp hw.
  induction hw; eauto.
  - eapply lts_refuses_spec2 in hst_tau. now exfalso. eauto.
  - inversion s_spec1; subst. inversion s_spec2; subst. eapply IHhw. 
    + eassumption.
    + eassumption.
    + eapply refuses_tau_preserved_by_lts_non_blocking_action; eauto.
    + eapply lts_different_action_preserved_by_lts_non_blocking_action; eauto.
Qed.

(* Properties of weak transitions in Lts with Forwarder axioms*)

Lemma delay_wt_non_blocking_action_nil `{gLtsObaFW P A} {p q r η} :
  non_blocking η -> p ⟶⋍[η] q -> q ⟹ r
    -> exists t, p ⟹ t /\ t ⟶⋍[η] r.
Proof.
  intros nb l w.
  revert p η nb l.
  dependent induction w; intros p0 η nb (p' & hl & heq); eauto with mdb.
  - exists p0. split; eauto with mdb. exists p'. split; eauto with mdb.
  - assert (p' ⟶⋍ q) as (r & hlr & heqr).
    { eapply eq_spec; eauto. }
    destruct (lts_oba_non_blocking_action_delay nb hl hlr) as (r' & l1 & (t' & l2 & heqt')).
    edestruct (IHw JMeq_refl r' η) as (r0 & w0 & (r1 & l1' & heq1)).
    exact nb. exists t'. split. eassumption. etrans; eassumption.
    exists r0. split. eapply wt_tau; eassumption. exists r1. eauto with mdb.
Qed.

Lemma delay_wt_non_blocking_action `{gLtsObaFW P A} {p q r η s} :
  non_blocking η -> p ⟶⋍[η] q -> q ⟹[s] r
    -> exists t, p ⟹[s] t /\ t ⟶⋍[η] r.
Proof.
  revert p q r η.
  induction s as [|μ s']; intros p q r η nb l w.
  - eapply delay_wt_non_blocking_action_nil; eauto.
  - eapply wt_pop in w as (q' & w0 & w1).
    destruct (wt_decomp_one w0) as (q0 & q1 & w2 & l' & w3).
    destruct (delay_wt_non_blocking_action_nil nb l w2) as (t & w4 & (q0' & l1' & heq')).
    assert (q0' ⟶⋍[μ] q1) as (r' & hr' & heqr').
    { eapply eq_spec; eauto. }
    destruct (lts_oba_non_blocking_action_delay nb l1' hr') as (u & l2 & l3).
    edestruct (eq_spec_wt q1 r' (symmetry heqr') r) as (t1 & w5 & l4); eauto with mdb.
    eapply wt_push_nil_left; eassumption.
    edestruct (IHs' u r') as (t2 & w6 & l5); eauto with mdb.
    exists t2. split.
    eapply wt_push_left; [eapply wt_push_nil_left|]; eauto with mdb.
    destruct l5 as (t1' & hlt1' & heqt1'). exists t1'. split; eauto with mdb.
    etrans; eassumption.
Qed.

Lemma wt_non_blocking_action_swap `{gLtsObaFW P A} p q η1 η2 : 
  non_blocking η1 -> non_blocking η2 -> p ⟹[[η1 ; η2]] q
    -> p ⟹⋍[[η2; η1]] q.
Proof.
  intros nb1 nb2 w.
  destruct (wt_pop p q η1 [η2] w) as (t & w1 & w2).
  eapply wt_decomp_one in w1 as (t1 & t2 & w3 & l1 & w4).
  eapply wt_decomp_one in w2 as (r1 & r2 & w5 & l2 & w6).
  assert (h : t2 ⟹ r1) by (eapply wt_push_nil_left; eassumption).
  destruct (delay_wt_non_blocking_action nb1 (mk_lts_eq l1) h) as (r & w7 & (r1' & hlr1' & heqr1')).
  assert (r1' ⟶⋍[η2] r2) as (t' & hlt' & heqt').
  { eapply eq_spec; eauto. }
  destruct (lts_oba_non_blocking_action_delay nb1 hlr1' hlt') as (u & hlu & (t0 & hlt0 & heqt0)); eauto.
  eapply wt_join_nil_eq_r.
  eapply (wt_push_nil_left w3).
  eapply (wt_push_nil_left w7).
  eapply (wt_act _ _ _ _ _ hlu), (wt_act _ _ _ _ _ hlt0), wt_nil.
  eapply eq_spec_wt. symmetry. etrans. eapply heqt0. eapply heqt'. eapply w6.
Qed.

Lemma wt_input_swap `{gLtsObaFW P A} p q μ1 μ2 : 
  (exists η2, non_blocking η2 /\ dual μ2 η2) -> p ⟹[[μ1 ; μ2]] q
    -> p ⟹⋍[[μ2; μ1]] q.
Proof.
  intro BlocDuo. destruct BlocDuo as (η2 & nb & duo).
  intro w.
  destruct (wt_pop p q (μ1) [μ2] w) as (t & w1 & w2).
  eapply wt_decomp_one in w1 as (t1 & t2 & w3 & l1 & w4).
  eapply wt_decomp_one in w2 as (r1 & r2 & w5 & l2 & w6).
  destruct (lts_oba_fw_forward t1 η2 μ2) as (t1' & l3 & l4); eauto.
  replace [μ2; μ1] with ([μ2] ++ [μ1]) by eauto.
  destruct (delay_wt_non_blocking_action nb (mk_lts_eq l4) (lts_to_wt l1)) as (r & l5 & l6).
  eapply wt_join_nil_eq_r.
  eapply (wt_push_nil_left w3).
  eapply (wt_act _ _ _ _ _ l3).
  eapply wt_decomp_one in l5 as (u1 & u2 & w7 & l7 & w8).
  eapply (wt_push_nil_left w7).
  eapply (wt_act _ _ _ _ _ l7 w8).
  assert (h : t2 ⟹ r1) by (eapply wt_push_nil_left; eassumption).
  destruct (delay_wt_non_blocking_action nb l6 h) as (v & wv & (v' & lv & heqv)).
  assert (v' ⟶⋍[μ2] r2) as (t' & hlt' & heqt').
  { eapply eq_spec; eauto. }
  eapply (wt_join_nil_eq_r wv).
  destruct (lts_oba_fw_feedback nb duo lv hlt') as [(t3 & hlt3 & heqt3)|]; subst; eauto with mdb.
  - eapply wt_join_nil_eq.
    exists t3. split; eauto with mdb.
    edestruct (eq_spec_wt r2 t') as (q' & hwq' & heqq').
    etrans. symmetry. eapply heqt'. now symmetry. eapply w6. exists q'. split; eauto with mdb.
  - edestruct (eq_spec_wt r2 v) as (q' & hwq' & heqq').
    etrans. symmetry. eassumption. now symmetry. eassumption.
    exists q'. split; eauto with mdb.
Qed.

Lemma wt_non_blocking_action_perm `{gLtsObaFW P A} {p q} s1 s2 :
  Forall non_blocking s1 -> s1 ≡ₚ s2 -> p ⟹[s1] q
    -> p ⟹⋍[s2] q.
Proof.
  intros hos hp w.
  revert p q hos w.
  dependent induction hp; intros; eauto.
  - exists q. split. eassumption. reflexivity.
  - eapply wt_pop in w as (p' & w0 & w1).
    replace (x :: l') with ([x] ++ l') by eauto.
    eapply wt_join_eq_r. eassumption.
    eapply IHhp. now inversion hos. eassumption.
  - inversion hos as [| ? ? nb Hyp_nb_list].
    inversion Hyp_nb_list as [| ? ? nb' Hyp_nb_list']; subst. 
    replace (x :: y :: l) with ([x ; y] ++ l) by eauto.
    replace (y :: x :: l) with ([y ; x] ++ l) in w by eauto.
    eapply wt_split in w as (p' & w1 & w2).
    eapply wt_join_eq_l.
    eapply wt_non_blocking_action_swap. eassumption. eassumption. eassumption. eassumption.
  - eapply IHhp1 in w as (q' & hw' & heq'); eauto.
    eapply IHhp2 in hw' as (q'' & hw'' & heq''); eauto.
    exists q''. split; eauto. etrans; eauto.
    eapply are_actions_preserved_by_perm; eauto.
Qed.

Lemma push_wt_non_blocking_action `{gLtsObaFW P A} {p q η s} :
  non_blocking η -> p ⟹[η :: s] q
    -> p ⟹⋍[s ++ [η]] q.
Proof.
  intros nb w.
  eapply wt_pop in w as (t & w1 & w2).
  eapply wt_decomp_one in w1 as (t1 & t2 & w3 & l & w4).
  set (w5 := wt_push_nil_left w4 w2).
  destruct (delay_wt_non_blocking_action nb (mk_lts_eq l) w5) as (r & w6 & w7).
  eapply wt_join_eq.
  exists r. split.
  eapply wt_push_nil_left; eassumption. reflexivity.
  destruct w7 as (u & hwu & hequ).
  exists u. split. eapply wt_act. eassumption. eapply wt_nil. eassumption.
Qed.

Lemma wt_annhil `{gLtsObaFW P A} p q η μ :
  non_blocking η -> dual μ η -> p ⟹[[η ; μ]] q
    -> p ⟹⋍ q.
Proof.
  intros nb duo w.
  destruct (wt_pop p q (η) [μ] w) as (u & w1 & w2).
  eapply wt_decomp_one in w1 as (t1 & t2 & w3 & l1 & w4).
  eapply wt_decomp_one in w2 as (r1 & r2 & w5 & l2 & w6).
  eapply (wt_join_nil_eq_r w3).
  destruct (delay_wt_non_blocking_action_nil nb (mk_lts_eq l1) (wt_join_nil w4 w5)) as (v & w0 & (v' & hlv' & heqv')).
  eapply (wt_join_nil_eq_r w0).
  assert (v' ⟶⋍[μ] r2) as (r2' & hlr2' & heqr2').
  { eapply eq_spec; eauto. }
  edestruct (lts_oba_fw_feedback nb duo hlv' hlr2') as [(t & hlt & heqt)| Hyp_equiv].
  - eapply wt_join_nil_eq.
    exists t. split. eapply wt_tau; eauto with mdb. eassumption.
    eapply wt_join_nil_eq_r. eapply wt_nil.
    eapply eq_spec_wt. etrans. eapply (symmetry heqr2'). now symmetry. eassumption.
  - eapply eq_spec_wt. etrans. eapply (symmetry heqr2'). symmetry. now rewrite Hyp_equiv.
    eassumption.
Qed.

Lemma wt_input_perm `{gLtsObaFW P A} {p q} s1 s2 :
  Forall exist_co_nba s1 -> s1 ≡ₚ s2 -> p ⟹[s1] q
    -> p ⟹⋍[s2] q.
Proof.
  intros his hp w.
  revert p q his w.
  dependent induction hp; intros; eauto.
  - exists q. split. eassumption. reflexivity.
  - eapply wt_pop in w as (p' & w0 & w1).
    replace (x :: l') with ([x] ++ l') by eauto.
    eapply wt_join_eq_r. eassumption.
    eapply IHhp. now inversion his. eassumption.
  - inversion his as [| ? ? Hyp_co_act Hyp_co_act_list]; subst. 
    inversion Hyp_co_act_list as [| ? ? Hyp_co_act' Hyp_co_act_list']; subst. 
    destruct Hyp_co_act, Hyp_co_act'.
    replace (x :: y :: l) with ([x ; y] ++ l) by eauto.
    replace (y :: x :: l) with ([y ; x] ++ l) in w by eauto.
    eapply wt_split in w as (p' & w1 & w2).
    eapply wt_join_eq_l.
    eapply wt_input_swap. eauto. eassumption. eassumption.
  - eapply IHhp1 in w as (q' & hw' & heq'); eauto.
    eapply IHhp2 in hw' as (q'' & hw'' & heq''); eauto.
    exists q''. split; eauto. etrans; eauto.
    eapply are_actions_preserved_by_perm; eauto.
Qed.

Lemma forward_s `{gLtsObaFW P A} p s1 s3:
  Forall non_blocking s3 -> Forall2 dual s1 s3 
    -> exists t, p ⟹[s1] t /\ t ⟹⋍[s3] p.
Proof.
  intros nb duo. revert p nb duo. dependent induction s1; intros; inversion duo ; subst.
  - exists p. simpl. split ; eauto with mdb.
    exists p. split; eauto with mdb. reflexivity.
  - inversion nb as [|? ? nb' Hyp_nb_list']; subst. 
    edestruct (lts_oba_fw_forward p y a) as (q & l0 & l1); eauto.
    destruct (IHs1 lb q Hyp_nb_list') as (q' & w1 & w2); eauto.
    exists q'. split.
    + eauto with mdb.
    + assert (q' ⟹⋍[lb ++ [y]] p) as Hyp. 
      eapply wt_join_eq. eassumption. exists p. split. eauto with mdb. reflexivity.
      ++ destruct Hyp as (p' & hwp' & heqp').
         eapply (wt_non_blocking_action_perm (lb ++ [y])) in hwp' as (p0 & hwp0 & heqp0).
         exists p0. split. eassumption. etrans; eassumption.
         eapply Forall_app. split. assumption. eauto. 
         symmetry. eapply Permutation_cons_append.
Qed.