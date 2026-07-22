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

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From Stdlib.Program Require Import Equality.
From stdpp Require Import countable.

From TestingTheory Require Import ForAllHelper MultisetHelper gLts Bisimulation Lts_OBA Lts_FW
  ActTau Termination WeakTransitions Convergence coWeakTransition.

(** ** Co-convergence

    [cocnv p s] is [cnv] with every step taken along [cowt] instead of [wt]:
    [p] converges "in the co sense" on [s] if it terminates and every
    co-weak-step along the head of [s] leads to a process that co-converges
    on the tail. *)

(** *** Definition *)

Reserved Notation "p ⇓ᶜᵒ s" (at level 70).

Inductive cocnv `{gLts P A} : P -> trace A -> Prop :=
| cocnv_nil p : p ⤓ -> p ⇓ᶜᵒ ε
| cocnv_act p μ s : p ⤓ -> (forall q, p ⟹ᶜᵒ{μ} q -> q ⇓ᶜᵒ s) -> p ⇓ᶜᵒ μ :: s

where "p ⇓ᶜᵒ s" := (cocnv p s).

Global Hint Constructors cocnv:mdb.

(** *** Properties on co-convergence in an LTS *)

Lemma cocnv_terminate `{M : gLts P A} p s : p ⇓ᶜᵒ s -> p ⤓.
Proof. by intros hcnv; now inversion hcnv. Qed.

Lemma cocnv_wk `{gLtsP : gLts P A} {p : P}{a : A} {s} : p ⇓ᶜᵒ a :: s -> p ⇓ᶜᵒ [ a ] .
Proof.
  intros pw; depelim pw; constructor.
  - assumption.
  - intros q qw%H0; constructor.
    eapply cocnv_terminate, qw.
Qed.

Lemma cocnv_preserved_by_lts_tau `{M : gLts P A} s p : p ⇓ᶜᵒ s -> forall q, p ⟶ q -> q ⇓ᶜᵒ s.
Proof.
  intros hcnv q l. destruct hcnv as [p p_cnv| μ p s p_cnv Hs].
  - eapply cocnv_nil. inversion p_cnv; eauto.
  - eapply cocnv_act.
    + inversion p_cnv; eauto.
    + eauto with mdb.
Qed.

Lemma cocnv_preserved_by_cowt_nil `{M : gLts P A} s p :
  p ⇓ᶜᵒ s -> forall q, p ⟹ᶜᵒ q -> q ⇓ᶜᵒ s.
Proof.
  intros hcnv q w.
  dependent induction w; eauto with mdb.
  eapply IHw. eapply cocnv_preserved_by_lts_tau; eauto. reflexivity.
Qed.

Lemma cocnv_preserved_by_cowt_act `{M: gLts P A} s p μ :
  p ⇓ᶜᵒ μ :: s -> forall q, p ⟹ᶜᵒ{μ} q -> q ⇓ᶜᵒ s.
Proof. by intros hcnv; inversion hcnv; eauto with mdb. Qed.

Lemma cocnv_iff_prefix_terminate_l `{M: gLts P A} p s :
  p ⇓ᶜᵒ s -> (forall t q, t `prefix_of` s -> p ⟹ᶜᵒ[t] q -> q ⤓).
Proof.
  intros hcnv t q hpre w.
  revert s p q hcnv hpre w.
  dependent induction t; intros.
  - eapply cocnv_terminate, cocnv_preserved_by_cowt_nil; eassumption.
  - eapply cowt_pop in w as (p' & w0 & w1).
    inversion hpre; subst. simpl in hcnv.
    eapply (IHt (t ++ x) p' q).
    eapply cocnv_preserved_by_cowt_act; eauto.
    now eapply prefix_cons_inv_2 in hpre.
    eassumption.
Qed.

Lemma cocnv_iff_prefix_terminate_r `{M: gLts P A} p s :
  (forall t q, t `prefix_of` s -> p ⟹ᶜᵒ[t] q -> q ⤓) -> p ⇓ᶜᵒ s.
Proof.
  intros h.
  revert p h.
  dependent induction s; intros; eauto with mdb.
  eapply cocnv_act; eauto with mdb.
  eapply (h []) ; eauto with mdb; eapply prefix_nil.
  intros q w. eapply IHs.
  intros t r hpre w1.
  eapply (h (a :: t)); eauto with mdb. eapply prefix_cons. eassumption.
  eapply cowt_push_left; eassumption.
Qed.

Corollary cocnv_iff_prefix_terminate `{M: gLts P A} p s :
  p ⇓ᶜᵒ s <-> (forall s0 q, s0 `prefix_of` s -> p ⟹ᶜᵒ[s0] q -> q ⤓).
Proof.
  split; [eapply cocnv_iff_prefix_terminate_l|eapply cocnv_iff_prefix_terminate_r].
Qed.

Lemma cocnv_cowt_prefix `{M: gLts P A} s1 s2 p :
  p ⇓ᶜᵒ s1 ++ s2 -> forall q, p ⟹ᶜᵒ[s1] q -> q ⇓ᶜᵒ s2.
Proof.
  revert s2 p.
  dependent induction s1; intros s2 p hcnv q w.
  - eapply cocnv_preserved_by_cowt_nil; eauto with mdb.
  - eapply cowt_pop in w as (p' & w0 & w1).
    inversion hcnv; eauto with mdb.
Qed.

(** *** Properties on co-convergence in an LTS with a Bisimulation *)

Global Instance cocnv_preserved_by_eq `{gLtsEq P A}:
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

(** *** Properties on co-convergence in an LTS with OBA axioms *)

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

(** *** Properties on co-convergence in an LTS with Forwarder axioms *)

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

(* [q]'s own convergence clause for [η] is itself indirect (it fires on
   [q ⟹ᶜᵒ{η} q0], i.e. some action dual to [η] out of [q]), so no external
   [μ]/[dual μ η] pair is needed here: the internal witness [cowt_decomp_one]
   exposes when we inspect that clause is exactly what [fwd_feedback] needs
   to cancel against the literal [η]-step [l]. *)
Lemma cocnv_retract_lts_non_blocking_action `{gLtsObaFW P A} p q η s :
  non_blocking η -> p ⇓ᶜᵒ s -> p ⟶[η] q -> q ⇓ᶜᵒ η :: s.
Proof.
  intros nb hcnv l.
  eapply cocnv_act.
  - eapply terminate_preserved_by_lts_non_blocking_action; eauto.
    eapply cocnv_terminate; eauto.
  - intros q0 w.
    eapply cowt_decomp_one in w as (r1 & r2 & μ' & w1 & duo & l' & w2).
    assert (w1' : q ⟹ r1).
    { eapply cowt_to_wt_dual in w1 as (s' & hf & w1''). inversion hf; subst. exact w1''. }
    destruct (delay_wt_non_blocking_action nb (mk_lts_eq l) w1') as (t & w0 & l1).
    destruct l1 as (r' & l1 & heq).
    edestruct (eq_spec r' r2 (ActExt μ')) as (r'' & hlr'' & heqr'').
    { exists r1. split; [exact heq | exact l']. }
    assert (wpt : p ⟹ᶜᵒ t).
    { eapply wt_to_cowt_dual with (s:=[]) in w0; [exact w0 | constructor]. }
    assert (ht : t ⇓ᶜᵒ s) by (eapply cocnv_preserved_by_cowt_nil; eauto).
    destruct (fwd_feedback nb duo l1 hlr'') as [(m & hlm & heqm)| Heqr].
    + assert (hm : m ⇓ᶜᵒ s) by (eapply cocnv_preserved_by_lts_tau; eauto).
      assert (hr'' : r'' ⇓ᶜᵒ s) by (eapply cocnv_preserved_by_eq; [exact heqm | reflexivity | exact hm]).
      assert (hr2 : r2 ⇓ᶜᵒ s) by (eapply cocnv_preserved_by_eq; [exact heqr'' | reflexivity | exact hr'']).
      eapply cocnv_preserved_by_cowt_nil; eauto.
    + assert (hr'' : r'' ⇓ᶜᵒ s) by (eapply cocnv_preserved_by_eq; [exact Heqr | reflexivity | exact ht]).
      assert (hr2 : r2 ⇓ᶜᵒ s) by (eapply cocnv_preserved_by_eq; [exact heqr'' | reflexivity | exact hr'']).
      eapply cocnv_preserved_by_cowt_nil; eauto.
Qed.

(* [dual μ' μ] plays the role [exist_co_nba]'s hidden witness played in the
   original: since [cocnv]'s own clause for the head of [s1] already goes
   through *some* dual internally, [s1]'s elements can be taken non-blocking
   directly, with no existential detour. Unlike an earlier attempt, [μ']
   itself needs no non-blockingness: mirroring the original's own proof, the
   "mover" commuted past the literal [μ']-step (via [nb_delay]) is [s1]'s
   head [a] (already non-blocking), reached backwards from [p] via
   [boomerang] — [μ'] plays the role of [nb_delay]'s fully generic [α]. *)
Lemma cocnv_drop_action_in_the_middle `{gLtsObaFW P A} p s1 s2 μ :
  Forall non_blocking s1 -> p ⇓ᶜᵒ (s1 ++ [μ] ++ s2)
    -> forall r μ', dual μ' μ -> p ⟶[μ'] r -> r ⇓ᶜᵒ (s1 ++ s2).
Proof.
  intros his hcnv.
  revert p s2 hcnv.
  induction s1 as [| a s1' IH]; intros p s2 hcnv r μ' duo l; simpl in *.
  - eapply cocnv_preserved_by_cowt_act. eauto.
    eapply lts_to_cowt. exact duo. exact l.
  - inversion his as [| a0 l0 nba his']; subst.
    destruct (exists_dual a) as (a' & daa').
    destruct (boomerang p a a') as (p2 & Hyp).
    destruct (Hyp nba (symmetry daa')) as (tr_b & tr_nb).
    destruct (nb_delay nba tr_nb l) as (t & w0 & sc).
    destruct sc as (r' & lar & heq).
    assert (pcowt : p ⟹ᶜᵒ{a} p2) by (eapply lts_to_cowt; [exact (symmetry daa') | exact tr_b]).
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

(* [forward_s] already builds a [wt] trace whose *own* dual is [s3]; reading
   the forward leg through [wt_to_cowt_dual] with [s1] (rather than [s3]) as
   the observed trace, and the return leg with [s3], both against the *same*
   given [Forall2 dual s3 s1] fact (never an independently re-decomposed
   one), is enough to reuse it without any determinacy assumption. *)
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

(* No [dual]/[Forall2] pairing at all here: [s1] is used verbatim on both
   sides (hypothesis and conclusion), so there is nothing to reconcile
   against an independently-obtained witness — unlike the earlier
   [cocnv_retract] attempt, which foundered on exactly that. *)
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
  + intros. dependent induction H0; eauto.
  + intros. constructor. eauto.
Qed.

(* [η] and [μ] cancel across the (non-blocking) [s2] in between: [forward_s]
   on the singleton [[μ]]/[[η]] constructs, consistently, both the co-step
   realizing [hcnv]'s head [η] *and* the literal step that later needs to
   cancel against it — never an independently re-decomposed dual, which is
   what made the general [cocnv_retract] attempt fail earlier. *)
Lemma cocnv_annhil_base `{gLtsObaFW P A} p μ η s2 s3 :
  Forall non_blocking s2 -> non_blocking η -> dual μ η -> p ⇓ᶜᵒ ([η] ++ s2 ++ [μ] ++ s3)
    -> p ⇓ᶜᵒ (s2 ++ s3).
Proof.
  intros his2 nbη duo hcnv.
  destruct (forward_s p [μ] [η]) as (t & w1 & w2).
  { constructor; [exact nbη | constructor]. }
  { constructor; [exact duo | constructor]. }
  assert (pcowt : p ⟹ᶜᵒ{η} t).
  { eapply (wt_to_cowt_dual p [μ] t w1 [η]).
    constructor; [exact (symmetry duo) | constructor]. }
  simpl in hcnv.
  inversion hcnv as [| p' η' rest hp hclause]; subst.
  assert (ht : t ⇓ᶜᵒ s2 ++ [μ] ++ s3) by (eapply hclause; exact pcowt).
  destruct w2 as (p' & w2 & heqp').
  eapply wt_decomp_one in w2 as (r1 & r2 & wr1 & lη & wr2).
  assert (r1cowt : t ⟹ᶜᵒ r1).
  { eapply wt_to_cowt_dual with (s:=[]) in wr1; [exact wr1 | constructor]. }
  assert (hr1 : r1 ⇓ᶜᵒ s2 ++ μ :: s3) by (eapply cocnv_preserved_by_cowt_nil; eauto).
  assert (hr2 : r2 ⇓ᶜᵒ s2 ++ s3).
  { exact (cocnv_drop_action_in_the_middle r1 s2 s3 μ his2 hr1 r2 η (symmetry duo) lη). }
  assert (r2cowt : r2 ⟹ᶜᵒ p').
  { eapply wt_to_cowt_dual with (s:=[]) in wr2; [exact wr2 | constructor]. }
  assert (hp' : p' ⇓ᶜᵒ s2 ++ s3) by (eapply cocnv_preserved_by_cowt_nil; eauto).
  eapply cocnv_preserved_by_eq; [exact heqp' | reflexivity | exact hp'].
Qed.

(* Only the base case ([s1 = []]) touches the [η]/[μ] cancellation; prepending
   [s1] is plain structural recursion through [cocnv_act]'s own clause, no
   duality reasoning involved. *)
Lemma cocnv_annhil `{gLtsObaFW P A} p μ η s1 s2 s3 :
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

(** *** From co-convergence to plain convergence on the dual action

    [p ⇓ᶜᵒ [μ]] means "[p] is ready to respond to an observer's [μ]",
    i.e. [p] is ready to itself perform [co μ] — exactly [p ⇓ [co μ]].
    Only this direction is provable without [dual]'s global uniqueness
    ([unique_nb]): [cocnv_act]'s clause quantifies over *every* action
    dual to [μ], so a single witness [p ⟹{co μ} q] (built from
    [exists_dual μ] alone, no uniqueness needed) instantiates it
    directly. The converse would need [unique_nb] to pin an arbitrary
    dual witness down to [co μ] specifically. *)
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
