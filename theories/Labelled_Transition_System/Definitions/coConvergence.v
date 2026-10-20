(* begin hide *)
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
(* end hide *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From Stdlib.Program Require Import Equality.
From stdpp Require Import countable.

From TestingTheory Require Import ActTau ForAllHelper MultisetHelper gLts SyncActions Bisimulation Lts_OBA Lts_FW
  ActTau Termination WeakTransitions Convergence coWeakTransition LtsFW.
(** ***** Co-convergence *)

(** ******* Definition *)

Reserved Notation "p ⇓ᶜᵒ s" (at level 70).

(** ******* Two alphabets, as [cowt]: on one alphabet [sync] is [dual]. *)
Inductive cocnv `{gLts P Aproc} `{Ht : ExtAction Atest} `{SA : !SyncAction Aproc Atest}
  : P -> trace Atest -> Prop :=
| cocnv_nil p : p ⤓ -> p ⇓ᶜᵒ ε
| cocnv_act p μ s : p ⤓ -> (forall q, p ⟹ᶜᵒ{μ} q -> q ⇓ᶜᵒ s) -> p ⇓ᶜᵒ μ :: s

where "p ⇓ᶜᵒ s" := (cocnv p s).

Global Hint Constructors cocnv:mdb.

(** ********** Properties on co-convergence in an LTS *)

Section cocnv_structure.

Context `{gLtsP : @gLts P Aproc Hp} `{Ht : ExtAction Atest} `{SA : !SyncAction Aproc Atest}.

Lemma cocnv_terminate p s : p ⇓ᶜᵒ s -> p ⤓.
Proof. by intros hcnv; now inversion hcnv. Qed.

Lemma cocnv_wk {p : P}{a : Atest} {s} : p ⇓ᶜᵒ a :: s -> p ⇓ᶜᵒ [ a ] .
Proof.
  intros pw; depelim pw; constructor.
  - assumption.
  - intros q qw%H0; constructor.
    eapply cocnv_terminate, qw.
Qed.

Lemma cocnv_preserved_by_lts_tau s p : p ⇓ᶜᵒ s -> forall q, p ⟶ q -> q ⇓ᶜᵒ s.
Proof.
  intros hcnv q l. destruct hcnv as [p p_cnv| μ p s p_cnv Hs].
  - eapply cocnv_nil. inversion p_cnv; eauto.
  - eapply cocnv_act.
    + inversion p_cnv; eauto.
    + eauto with mdb.
Qed.

Lemma cocnv_preserved_by_cowt_nil s p :
  p ⇓ᶜᵒ s -> forall q, p ⟹ᶜᵒ q -> q ⇓ᶜᵒ s.
Proof.
  intros hcnv q w.
  remember ([] : trace Atest) as s0 eqn:hs0 in w.
  revert hs0 hcnv. induction w as [| s1 p0 q0 t0 l w IHw | ]; intros hs0 hcnv; [done | | discriminate].
  eapply IHw; [exact hs0 |]. eapply cocnv_preserved_by_lts_tau; eauto.
Qed.

Lemma cocnv_preserved_by_cowt_act s p μ :
  p ⇓ᶜᵒ μ :: s -> forall q, p ⟹ᶜᵒ{μ} q -> q ⇓ᶜᵒ s.
Proof. by intros hcnv; inversion hcnv; eauto with mdb. Qed.

Lemma cocnv_iff_prefix_terminate_l p s :
  p ⇓ᶜᵒ s -> (forall t q, t `prefix_of` s -> p ⟹ᶜᵒ[t] q -> q ⤓).
Proof.
  intros hcnv t q hpre w.
  revert s p q hcnv hpre w.
  induction t; intros.
  - eapply cocnv_terminate, cocnv_preserved_by_cowt_nil; eassumption.
  - eapply cowt_pop in w as (p' & w0 & w1).
    inversion hpre; subst. simpl in hcnv.
    eapply (IHt (t ++ x) p' q).
    eapply cocnv_preserved_by_cowt_act; eauto.
    now eapply prefix_cons_inv_2 in hpre.
    eassumption.
Qed.

Lemma cocnv_iff_prefix_terminate_r p s :
  (forall t q, t `prefix_of` s -> p ⟹ᶜᵒ[t] q -> q ⤓) -> p ⇓ᶜᵒ s.
Proof.
  intros h.
  revert p h.
  induction s; intros; eauto with mdb.
  eapply cocnv_act; eauto with mdb.
  eapply (h []) ; eauto with mdb; eapply prefix_nil.
  intros q w. eapply IHs.
  intros t r hpre w1.
  eapply (h (a :: t)); eauto with mdb. eapply prefix_cons. eassumption.
  eapply cowt_push_left; eassumption.
Qed.

Corollary cocnv_iff_prefix_terminate p s :
  p ⇓ᶜᵒ s <-> (forall s0 q, s0 `prefix_of` s -> p ⟹ᶜᵒ[s0] q -> q ⤓).
Proof.
  split; [eapply cocnv_iff_prefix_terminate_l|eapply cocnv_iff_prefix_terminate_r].
Qed.

Lemma cocnv_cowt_prefix s1 s2 p :
  p ⇓ᶜᵒ s1 ++ s2 -> forall q, p ⟹ᶜᵒ[s1] q -> q ⇓ᶜᵒ s2.
Proof.
  revert s2 p.
  induction s1; intros s2 p hcnv q w.
  - eapply cocnv_preserved_by_cowt_nil; eauto with mdb.
  - eapply cowt_pop in w as (p' & w0 & w1).
    inversion hcnv; eauto with mdb.
Qed.

End cocnv_structure.

(** ******** Properties on co-convergence in an LTS with a Bisimulation *)

Section cocnv_structure_eq.

Context `{gLtsEqP : @gLtsEq P Aproc Hp} `{Ht : ExtAction Atest} `{SA : !SyncAction Aproc Atest}.

Global Instance cocnv_preserved_by_eq :
  Proper ((eq_rel) ==> (=) ==> (impl)) cocnv.
  (* p ⋍ q -> p ⇓ᶜᵒ s -> q ⇓ᶜᵒ s *)
  Proof.
  intros p q heq s s' Hs hcnv. subst s'. revert q heq.
  induction hcnv as [p p_cnv | p μ s p_cnv _ Hμ]; intros.
  - eapply cocnv_nil.
    eapply (terminate_preserved_by_eq p_cnv heq).
  - eapply cocnv_act.
    + eapply (terminate_preserved_by_eq p_cnv heq).
    + intros t w.
      destruct (eq_spec_cowt q p (symmetry heq) t [μ] w) as (t' & hlt' & heqt').
      eapply (Hμ t' hlt' t heqt').
Qed.

End cocnv_structure_eq.

(** ******* Properties on co-convergence in an LTS with OBA axioms *)

Lemma terminate_preserved_by_cowt_non_blocking_action `{M: gLtsOba P A} p q η :
  co_non_blocking η -> p ⤓ -> p ⟹ᶜᵒ{ η } q -> q ⤓.
Proof.
  intros nb ht w.
  eapply cowt_to_wt_dual in w as (s' & hf & w').
  inversion hf as [| x y la lb dxy hf']; subst.
  inversion hf'; subst.
  eapply terminate_preserved_by_wt_non_blocking_action; eauto.
  apply nb. symmetry. exact dxy.
Qed.

(** ******** Properties on co-convergence in an LTS with Forwarder axioms *)

Lemma cocnv_preserved_by_lts_non_blocking_action `{gLtsObaFW P A} p q η s :
  non_blocking η -> p ⇓ᶜᵒ s -> p ⟶[η] q
    -> q ⇓ᶜᵒ s.
Proof.
  revert p q η.
  induction s as [|μ s']; intros p q η nb hacnv l.
  - eapply cocnv_nil. inversion hacnv. subst.
    eapply terminate_preserved_by_lts_non_blocking_action; eassumption.
  - inversion hacnv as [|p'  μ'  T  Hyp_p_conv Hyp_conv_through_μ];subst.
    eapply cocnv_act.
    + eapply terminate_preserved_by_lts_non_blocking_action; eassumption.
    + intros r w.
      destruct (delay_cowt_non_blocking_action nb (mk_lts_eq l) w) as (t & w0 & l1).
      destruct l1 as (r' & l2 & heq).
      rewrite<- heq. eapply IHs'. exact nb. eapply Hyp_conv_through_μ, w0.
      eassumption.
Qed.

Lemma cocnv_preserved_by_cowt_non_blocking_action `{gLtsObaFW P A} p q η s :
  co_non_blocking η -> p ⇓ᶜᵒ s -> p ⟹ᶜᵒ{η} q
    -> q ⇓ᶜᵒ s.
Proof.
  intros nb hcnv w.
  eapply cowt_decomp_one in w as (r1 & r2 & μ' & w1 & duo & l0 & w2).
  eapply (cocnv_preserved_by_cowt_nil _ r2); eauto.
  eapply (cocnv_preserved_by_lts_non_blocking_action r1).
  apply nb. exact duo.
  eapply (cocnv_preserved_by_cowt_nil _ p); eauto.
  exact l0.
Qed.

Lemma cocnv_retract_lts_non_blocking_action `{H : ExtAction A, gLtsEqP : !gLtsEq P H, !LtsFW P A} p q η s :
  non_blocking η -> p ⇓ᶜᵒ s -> p ⟶[η] q -> q ⇓ᶜᵒ η :: s.
Proof.
  intros nb hcnv l.
  eapply cocnv_act.
  - eapply (lfw_terminate_preserved η); [exact nb | exact l | by eapply cocnv_terminate].
  - intros q0 w.
    eapply cowt_decomp_one in w as (r1 & r2 & μ' & w1 & duo & l' & w2).
    assert (w1' : q ⟹ r1) by exact (proj1 (cowt_iff_wt_nil _ _) w1).
    destruct (lfw_delay_wt_nil η nb (mk_lts_eq l) w1') as (t & w0 & l1).
    destruct l1 as (r' & l1 & heq).
    edestruct (eq_spec r' r2 (ActExt μ')) as (r'' & hlr'' & heqr'').
    { exists r1. split; [exact heq | exact l']. }
    assert (wpt : p ⟹ᶜᵒ t) by exact (proj2 (cowt_iff_wt_nil _ _) w0).
    assert (ht : t ⇓ᶜᵒ s) by (eapply cocnv_preserved_by_cowt_nil; eauto).
    destruct (lfw_feedback t r' r'' η μ' nb duo l1 hlr'') as [(m & hlm & heqm)| Heqr].
    + assert (hm : m ⇓ᶜᵒ s) by (eapply cocnv_preserved_by_lts_tau; eauto).
      assert (hr'' : r'' ⇓ᶜᵒ s) by (eapply cocnv_preserved_by_eq; [exact heqm | reflexivity | exact hm]).
      assert (hr2 : r2 ⇓ᶜᵒ s) by (eapply cocnv_preserved_by_eq; [exact heqr'' | reflexivity | exact hr'']).
      eapply cocnv_preserved_by_cowt_nil; eauto.
    + assert (hr'' : r'' ⇓ᶜᵒ s) by (eapply cocnv_preserved_by_eq; [exact Heqr | reflexivity | exact ht]).
      assert (hr2 : r2 ⇓ᶜᵒ s) by (eapply cocnv_preserved_by_eq; [exact heqr'' | reflexivity | exact hr'']).
      eapply cocnv_preserved_by_cowt_nil; eauto.
Qed.

Lemma cocnv_drop_action_in_the_middle `{H : ExtAction A, gLtsEqP : !gLtsEq P H, !LtsFW P A} p s1 s2 μ :
  Forall non_blocking s1 -> p ⇓ᶜᵒ (s1 ++ [μ] ++ s2)
    -> forall r μ', dual μ' μ -> p ⟶[μ'] r -> r ⇓ᶜᵒ (s1 ++ s2).
Proof.
  intros his hcnv.
  revert p s2 hcnv.
  induction s1 as [| a s1' IH]; intros p s2 hcnv r μ' duo l; simpl in *.
  - eapply cocnv_preserved_by_cowt_act. eauto.
    eapply lts_to_cowt. exact duo. exact l.
  - inversion his as [| a0 l0 nba his']; subst.
    destruct (lfw_boomerang p a nba) as (p2 & tr_b & tr_nb).
    destruct (lfw_delay p2 p r a (ActExt μ') nba tr_nb l) as (t & w0 & sc).
    destruct sc as (r' & lar & heq).
    assert (pcowt : p ⟹ᶜᵒ{a} p2) by (eapply lts_to_cowt; [exact (co_dual a) | exact tr_b]).
    inversion hcnv as [| p' a'' rest hp hclause]; subst.
    assert (hp2 : p2 ⇓ᶜᵒ s1' ++ μ :: s2) by (eapply hclause; exact pcowt).
    assert (ht : t ⇓ᶜᵒ s1' ++ s2) by (exact (IH his' p2 s2 hp2 t μ' duo w0)).
    assert (hr' : r' ⇓ᶜᵒ a :: (s1' ++ s2)) by (exact (cocnv_retract_lts_non_blocking_action t r' a (s1'++s2) nba ht lar)).
    eapply cocnv_preserved_by_eq; [exact heq | reflexivity | exact hr'].
Qed.

Lemma Forall2_dual_sym `{ExtAction A} s1 s2 : Forall2 dual s1 s2 -> Forall2 dual s2 s1.
Proof.
  induction 1 as [| x y l l' dxy hf IH].
  - constructor.
  - constructor; [symmetry; exact dxy | exact IH].
Qed.

Lemma coforward_s `{gLtsObaFW P A} p s1 s3:
  Forall non_blocking s1 -> Forall2 dual s3 s1
    -> exists t, p ⟹ᶜᵒ[s1] t /\ t ⟹ᶜᵒ⋍[s3] p.
Proof.
  intros hnb hdual.
  destruct (forward_s p s3 s1 hnb hdual) as (t & w1 & w2).
  exists t. split.
  - eapply wt_to_cowt_dual. exact w1. eapply Forall2_dual_sym. exact hdual.
  - destruct w2 as (t' & w2 & heq).
    exists t'. split; [| exact heq].
    eapply wt_to_cowt_dual. exact w2. exact hdual.
Qed.

Lemma cocnv_retract_wt_non_blocking_action `{gLtsObaFW P A} p q η s :
  non_blocking η -> p ⇓ᶜᵒ s -> p ⟹{η} q
    -> q ⇓ᶜᵒ η :: s.
Proof.
  intros nb hcnv w.
  eapply wt_decomp_one in w as (t1 & t2 & w1 & l & w2).
  assert (ht1 : t1 ⇓ᶜᵒ s).
  { eapply cocnv_preserved_by_cowt_nil; eauto.
    eapply wt_to_cowt_dual with (s:=[]) in w1; [exact w1 | constructor]. }
  assert (ht2 : t2 ⇓ᶜᵒ η :: s) by (exact (cocnv_retract_lts_non_blocking_action t1 t2 η s nb ht1 l)).
  eapply cocnv_preserved_by_cowt_nil; eauto.
  eapply wt_to_cowt_dual with (s:=[]) in w2; [exact w2 | constructor].
Qed.


Lemma cocnv_retract `{gLtsObaFW P A} p q s1 s2 (s3 : list A) :
  Forall non_blocking s1 -> p ⇓ᶜᵒ s2 -> p ⟹[s1] q
    -> q ⇓ᶜᵒ s1 ++ s2.
Proof.
  revert p q.
  induction s1 as [| a s1' IH]; intros p q hnb hcnv w; simpl in *.
  - eapply cocnv_preserved_by_cowt_nil; eauto.
    eapply wt_to_cowt_dual with (s:=[]) in w; [exact w | constructor].
  - inversion hnb as [| a0 l0 nba hnb']; subst.
    eapply push_wt_non_blocking_action in w as (q' & hwq' & heqq').
    2: exact nba.
    eapply wt_split in hwq' as (t & w1 & w2).
    assert (ht : t ⇓ᶜᵒ s1' ++ s2) by (exact (IH p t hnb' hcnv w1)).
    assert (hq' : q' ⇓ᶜᵒ a :: (s1' ++ s2)) by (exact (cocnv_retract_wt_non_blocking_action t q' a (s1' ++ s2) nba ht w2)).
    eapply cocnv_preserved_by_eq; [exact heqq' | reflexivity | exact hq'].
Qed.

Lemma cocnv_prefix `{gLts P A} {p : P} {s1 s2} : p ⇓ᶜᵒ s1 ++ s2 -> p ⇓ᶜᵒ s1.
Proof.
  revert s2 p. induction s1 as [|a s1]; intros s2 p Hcnv.
  - eapply cocnv_nil. now inversion Hcnv.
  - eapply cocnv_act. now inversion Hcnv.
    intros q hw. inversion Hcnv; subst. eauto.
Qed.

Lemma cocnv_jump `{gLts P A} s1 s2 p : p ⇓ᶜᵒ s1 -> (forall q, p ⟹ᶜᵒ[s1] q -> q ⇓ᶜᵒ s2) -> p ⇓ᶜᵒ s1 ++ s2.
Proof.
  revert s2 p.
  induction s1 as [| μ s']; intros s2 p hcnv hs2.
  - eapply hs2. eauto with mdb.
  - simpl. eapply cocnv_act.
    + now inversion hcnv.
    + intros t w.
      eapply IHs'. inversion hcnv; eauto.
      intros. eapply hs2. eapply cowt_push_left; eauto.
Qed.

Lemma equiv_cotermination `{gLtsP : @gLts P A H} p : p ⇓ᶜᵒ [] <-> p ⤓.
Proof.
  split.
  + intros. by inversion H0.
  + intros. constructor. eauto.
Qed.

Lemma cocnv_annhil_base `{H : ExtAction A, gLtsEqP : !gLtsEq P H, !LtsFW P A} p μ η s2 s3 :
  Forall non_blocking s2 -> non_blocking η -> dual μ η -> p ⇓ᶜᵒ ([η] ++ s2 ++ [μ] ++ s3)
    -> p ⇓ᶜᵒ (s2 ++ s3).
Proof.
  intros his2 nbη duo hcnv.
  destruct (lfw_boomerang p η nbη) as (t & l1 & l2).
  assert (pcowt : p ⟹ᶜᵒ{η} t) by (eapply lts_to_cowt; [exact (co_dual η) | exact l1]).
  simpl in hcnv.
  inversion hcnv as [| p' η' rest hp hclause]; subst.
  assert (ht : t ⇓ᶜᵒ s2 ++ [μ] ++ s3) by (eapply hclause; exact pcowt).
  exact (cocnv_drop_action_in_the_middle t s2 s3 μ his2 ht p η (symmetry duo) l2).
Qed.

Lemma cocnv_annhil `{H : ExtAction A, gLtsEqP : !gLtsEq P H, !LtsFW P A} p μ η s1 s2 s3 :
  Forall non_blocking s1 -> Forall non_blocking s2 -> non_blocking η -> dual μ η
    -> p ⇓ᶜᵒ (s1 ++ [η] ++ s2 ++ [μ] ++ s3)
    -> p ⇓ᶜᵒ (s1 ++ s2 ++ s3).
Proof.
  intros his1 his2 nbη duo.
  revert p.
  induction s1 as [| a s1' IHs1]; intros p hcnv; simpl in *.
  - exact (cocnv_annhil_base p μ η s2 s3 his2 nbη duo hcnv).
  - inversion his1 as [| a0 l0 nba his1']; subst.
    inversion hcnv as [| p' a'' rest hp hclause]; subst.
    eapply cocnv_act.
    + exact hp.
    + intros q w. exact (IHs1 his1' q (hclause q w)).
Qed.

Lemma cocnv_of_cnv_dual_rev `{EA : !ExtAction A} `{M : gLts P A} p μ : p ⇓ᶜᵒ [μ] -> p ⇓ [co μ].
Proof.
  intro hcocnv. eapply cnv_act.
  - eapply cocnv_terminate; eauto.
  - intros q w.
    assert (hcowt : p ⟹ᶜᵒ{μ} q).
    { eapply wt_to_cowt_dual with (s' := [co μ]); eauto.
      constructor; [exact (proj2_sig (exists_dual μ)) | constructor]. }
    eapply cocnv_preserved_by_cowt_act in hcowt; eauto.
    eapply equiv_termination, equiv_cotermination; eauto.
Qed.