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
From Stdlib.Program Require Import Equality.
From stdpp Require Import finite gmap decidable.
From TestingTheory Require Import ActTau gLts SyncActions Bisimulation Lts_OBA Subset_Act WeakTransitions Testing_Predicate
    StateTransitionSystems InteractionBetweenLts Convergence Termination FiniteImageLTS ParallelLTSConstruction.

 (** ** Inductive definition [must_sts] of Must based on the STS *)
Inductive must_sts 
  `{Sts (P1 * P2)} (outcome : P2 -> Prop)
  (p : P1) (t : P2) : Prop :=
| m_sts_now : outcome t -> must_sts outcome p t
| m_sts_step
    (nh : ¬ outcome t)
    (nst : ¬ sts_refuses (p, t))
    (l : forall p' t', sts_step (p, t) (p', t') -> must_sts outcome p' t')
  : must_sts outcome p t
.

Global Hint Constructors must_sts:mdb.

(** ** Inductive definition [must] of Must

    One definition for every setting.  The process and the observer may live
    on different alphabets, [Aproc] and [Atest]; which of their actions meet
    is the field [sync] of [SyncAction Aproc Atest], and the computations of
    [p ∥ t] are the [Sts] of [ParSts], for the two LTSs at hand.

    - In the one-alphabet development, [sync] is [dual]
      ([SyncAction_of_dual], found automatically) and the [Sts] is the τ-part
      of the parallel LTS given by [Prop_of_Inter] ([ParSts_of_inter]):
      [sts_step (p, t) t'] is then [(p, t) ⟶ t'] and [sync μ1 μ2] is
      [dual μ1 μ2], by computation.
    - With two alphabets the [Sts] is [inter_tau_sts], from [Prop_of_Inter] on two alphabets
      ([InteractionBetweenLts.v]). *)

(** The computations of [p ∥ t], for given LTSs of [P] and [T].  Indexing
    them by the two LTSs keeps [must] as rigid as it was with [Prop_of_Inter]:
    the instance is looked for with the very LTSs [must] is stated for. *)
Class ParSts (P T : Type) {Aproc Atest : Type} {Hp : ExtAction Aproc} {Ht : ExtAction Atest}
  (gLtsP : gLts P Hp) (gLtsT : gLtsEq T Ht) := MkParSts { par_sts : Sts (P * T) }.

#[global] Instance ParSts_of_inter {P T A : Type} {H : ExtAction A}
  (gLtsP : gLts P H) (gLtsT : gLtsEq T H)
  `{PI : !@Prop_of_Inter P T A A dual H gLtsP H (@gLtsEq_gLts T A H gLtsT)} : ParSts P T gLtsP gLtsT :=
  {| par_sts := @parallel_sts P T A H gLtsP (@gLtsEq_gLts T A H gLtsT) PI |}.

Inductive must `{
    gLtsP : @gLts P Aproc Hp,
    gLtsT : ! @gLtsEq T Atest Ht, !Testing_Predicate outcome _,
    SA : !SyncAction Aproc Atest, STS : !ParSts P T gLtsP gLtsT}

    (p : P) (t : T) : Prop :=
| m_now : outcome t -> must p t
| m_step
    (nh : ¬ outcome t)
    (ex : ∃ t', sts_step (Sts := par_sts) (p, t) t')
    (pt : forall p', p ⟶ p' -> must p' t)
    (et : forall t', t ⟶ t' -> must p t')
    (com : forall p' t' μ1 μ2, sync μ1 μ2
      -> p ⟶[μ1] p'
        -> t ⟶[μ2] t'
          -> must p' t')
  : must p t
.

Notation "p 'must_pass' t" := (must p t) (at level 70).

(* [lts_inversion] inverts the first transition it finds.  The computation
   step [ex] of [must] is now an [sts_step]; it is treated as the [lts_step]
   of the parallel LTS it used to be, in the same search order. *)
Ltac lts_inversion lts ::=
try match goal with
| H : ?X |- _ =>
  lazymatch X with lts_step _ _ _ => idtac | sts_step _ _ => idtac end;
  solve[inversion H; subst; discriminate || tauto]
| H : lts ?p ?a ?q |- _ => inversion H; subst; discriminate || tauto
 end;
match goal with
| H : ?X |- _ =>
  lazymatch X with lts_step _ _ _ => idtac | sts_step _ _ => idtac end;
  inversion H; subst; clear H
| H : lts ?p ?a ?q |- _ => inversion H; subst; clear H
 end.

Global Hint Constructors must:mdb.

(** ** Well-formed computations of [p ∥ t]

    The lemmas on [must] below only use that a computation of [p ∥ t] is a
    τ of [p], a τ of [t], or a synchronisation of an action of [p] with an
    action of [t] — and conversely.  [ParStsSpec] says so; it holds for the
    parallel composition of [Prop_of_Inter] (one alphabet) and for [inter_tau_sts]
    (two alphabets). *)

Class ParStsSpec (P T : Type) {Aproc Atest : Type}
  {Hp : ExtAction Aproc} {Ht : ExtAction Atest}
  (gLtsP : gLts P Hp) (gLtsT : gLtsEq T Ht) (SA : SyncAction Aproc Atest)
  (STS : ParSts P T gLtsP gLtsT) := MkParStsSpec {
    par_step_left p p' t :
      p ⟶ p' → sts_step (Sts := par_sts) (p, t) (p', t);
    par_step_right p t t' :
      t ⟶ t' → sts_step (Sts := par_sts) (p, t) (p, t');
    par_step_sync p p' t t' μ1 μ2 :
      sync μ1 μ2 → p ⟶[μ1] p' → t ⟶[μ2] t' → sts_step (Sts := par_sts) (p, t) (p', t');
    par_step_inv p t y :
      sts_step (Sts := par_sts) (p, t) y →
        (∃ p', y = (p', t) ∧ p ⟶ p')
      ∨ (∃ t', y = (p, t') ∧ t ⟶ t')
      ∨ (∃ p' t' μ1 μ2, y = (p', t') ∧ sync μ1 μ2 ∧ p ⟶[μ1] p' ∧ t ⟶[μ2] t');
  }.

(** The three shapes of a computation, as an inductive view: [inversion] on
    [par_view_of l] gives the cases with the names of [inter_tau_step]. *)
Inductive par_view `{gLtsP : @gLts P Aproc Hp} `{gLtsT : @gLts T Atest Ht}
  `{SA : !SyncAction Aproc Atest} (p : P) (t : T) : P * T → Prop :=
| ViewLeft p' (l : p ⟶ p') : par_view p t (p', t)
| ViewRight t' (l : t ⟶ t') : par_view p t (p, t')
| ViewSync p' t' μ η (hs : sync μ η) (l1 : p ⟶[μ] p') (l2 : t ⟶[η] t') : par_view p t (p', t').

Lemma par_view_of `{gLtsP : @gLts P Aproc Hp} `{gLtsT : !@gLtsEq T Atest Ht}
  `{SA : !SyncAction Aproc Atest} `{STS : !ParSts P T gLtsP gLtsT} `{!ParStsSpec P T gLtsP gLtsT SA STS}
  p t y : sts_step (Sts := par_sts) (p, t) y → par_view p t y.
Proof.
  intros l. destruct (par_step_inv p t y l)
    as [(p' & -> & lp) | [(t' & -> & lt) | (p' & t' & μ & η & -> & hs & l1 & l2)]].
  - by apply ViewLeft.
  - by apply ViewRight.
  - by eapply ViewSync.
Qed.

#[global] Instance ParStsSpec_of_inter {P T A : Type} {H : ExtAction A}
  (gLtsP : gLts P H) (gLtsT : gLtsEq T H)
  `{PI : !@Prop_of_Inter P T A A dual H gLtsP H (@gLtsEq_gLts T A H gLtsT)} :
  ParStsSpec P T gLtsP gLtsT SyncAction_of_dual (ParSts_of_inter gLtsP gLtsT).
Proof.
  apply MkParStsSpec.
  - intros p p' t l. change (inter_step (p, t) τ (p', t)). by apply ParLeft.
  - intros p t t' l. change (inter_step (p, t) τ (p, t')). by apply ParRight.
  - intros p p' t t' μ1 μ2 hs l1 l2. change (inter_step (p, t) τ (p', t')).
    by eapply ParSync.
  - intros p t y l. change (inter_step (p, t) τ y) in l.
    inversion l; subst.
    + left. by eexists.
    + right; left. by eexists.
    + right; right. by do 4 eexists.
Qed.

(* The instances built from [inter_tau_sts] have a lower priority than the
   ones of the parallel composition: on one alphabet, with [sync = dual],
   both would apply, and [must] must keep its one-alphabet reading. *)

(* An [eapply] of a lemma on [must] may leave the [ParSts]/[ParStsSpec]
   instances as goals; the [eauto] that usually follows closes them. *)
#[global] Hint Extern 1 (ParSts _ _ _ _) => typeclasses eauto : core.
#[global] Hint Extern 1 (ParStsSpec _ _ _ _ _ _) => typeclasses eauto : core.

(** With two alphabets, the computations are those of [inter_tau_sts]
    ([InteractionBetweenLts.v]), built from the interaction. *)

#[global] Instance ParSts_of_inter_tau {P T Aproc Atest : Type}
  {Hp : ExtAction Aproc} {Ht : ExtAction Atest}
  (gLtsP : gLts P Hp) (gLtsT : gLtsEq T Ht) {SA : SyncAction Aproc Atest}
  {SY : @Prop_of_Inter P T Aproc Atest (@sync Aproc Atest Hp Ht SA) Hp gLtsP Ht (@gLtsEq_gLts T Atest Ht gLtsT)} :
  ParSts P T gLtsP gLtsT | 10 :=
  {| par_sts := inter_tau_sts (M := SY) |}.

#[global] Instance ParStsSpec_of_inter_tau {P T Aproc Atest : Type}
  {Hp : ExtAction Aproc} {Ht : ExtAction Atest}
  (gLtsP : gLts P Hp) (gLtsT : gLtsEq T Ht) {SA : SyncAction Aproc Atest}
  {SY : @Prop_of_Inter P T Aproc Atest (@sync Aproc Atest Hp Ht SA) Hp gLtsP Ht (@gLtsEq_gLts T Atest Ht gLtsT)} :
  ParStsSpec P T gLtsP gLtsT SA (ParSts_of_inter_tau gLtsP gLtsT) | 10.
Proof.
  apply MkParStsSpec.
  - intros p p' t l. change (inter_tau_step (p, t) (p', t)). by apply TauLeft.
  - intros p t t' l. change (inter_tau_step (p, t) (p, t')). by apply TauRight.
  - intros p p' t t' μ1 μ2 hs l1 l2. change (inter_tau_step (p, t) (p', t')).
    by eapply TauSync.
  - intros p t y l. change (inter_tau_step (p, t) y) in l.
    inversion l; subst.
    + left. by eexists.
    + right; left. by eexists.
    + right; right. by do 4 eexists.
Qed.

(** ** Equivalence of the two inductive definitions [must] and [must_sts] *)

Lemma must_sts_iff_must `{
    gLtsP : @gLts P A H,
    gLtsT : ! gLtsEq T H, !Testing_Predicate outcome _}

    `{!Prop_of_Inter P T A A dual}

  (p : P) (t : T) :
  must_sts outcome p t <-> p must_pass t.
Proof.
  split.
  - intro hm. induction hm; eauto with mdb.
    apply m_step; eauto with mdb.
    + eapply sts_refuses_spec1 in nst as ((p', t') & hl).
      exists (p', t'). now simpl in hl.
    + simpl in *; eauto with mdb.
    + simpl in *; eauto with mdb.
    + intros p' t' μ1 μ2 duo hl1 hl2.
      apply H0, (ParSync μ1 μ2); eauto.
  - intro hm. dependent induction hm; eauto with mdb.
    eapply m_sts_step; eauto with mdb.
    + eapply sts_refuses_spec2.
      destruct (decide (sts_refuses (p, t))).
      ++ exfalso.
         destruct ex as ((p', t'), hl).
         eapply sts_refuses_spec2 in s; eauto.
      ++ now eapply sts_refuses_spec1 in n.
    + intros p' t' hl.
      inversion hl; subst; eauto with mdb.
Qed.

(** ** Definition of the contextual preorder based on [must] *)

Definition ctx_pre `{
  gLtsP : @gLts P Aproc Hp,
  gLtsQ : !@gLts Q Aproc Hp,
  gLtsT : !@gLtsEq T Atest Ht, !Testing_Predicate outcome _,
  SA : !SyncAction Aproc Atest, !ParSts P T gLtsP gLtsT, !ParSts Q T gLtsQ gLtsT}

  (p : P) (q : Q)
  := forall (t : T), p must_pass t -> q must_pass t.

Global Hint Unfold ctx_pre: mdb.

(** The must preorder, for a synchronisation [sync]... *)
Notation "p ⊆ₘᵤₛₜᵢ q" := (ctx_pre p q) (at level 70).
(** ... and for [sync = dual], on one alphabet. *)
Notation "p ⊑ₘᵤₛₜᵢ q" := (ctx_pre (SA := SyncAction_of_dual) p q) (at level 70).
Notation "p ⋢ₘᵤₛₜᵢ q" := (¬ ctx_pre (SA := SyncAction_of_dual) p q) (at level 70).
Notation "p ≂ₘᵤₛₜᵢ q" := (q ⊑ₘᵤₛₜᵢ p /\ p ⊑ₘᵤₛₜᵢ q) (at level 70).

(** ** Properties on [must]

    Stated once, for any well-formed composition ([ParStsSpec]): they hold
    for one alphabet and [dual] as for two alphabets and [inter_tau_sts]. *)

Lemma must_eq_client `{
  gLtsP : @gLts P Aproc Hp,
  gLtsT : !@gLtsEq T Atest Ht, !Testing_Predicate outcome _,
  SA : !SyncAction Aproc Atest, STS : !ParSts P T gLtsP gLtsT,
  !ParStsSpec P T gLtsP gLtsT SA STS} :

  forall (p : P) (t t' : T), t ⋍ t' -> p must_pass t -> p must_pass t'.
Proof.
  intros p t t' heq hm.
  revert t' heq.
  induction hm as [p t hout | p t nh ex pt IHpt et IHet com IHcom]; intros t' heq.
  - apply m_now. eapply outcome_preserved_by_eq; eauto.
  - apply m_step.
    + intro rh. eapply nh. eapply outcome_preserved_by_eq; eauto with mdb.
      now symmetry.
    + destruct ex as (y & l).
      destruct (par_step_inv _ _ _ l)
        as [(p' & -> & lp) | [(t'' & -> & lt) | (p' & t'' & μ1 & μ2 & -> & hs & l1 & l2)]].
      ++ exists (p', t'). by apply par_step_left.
      ++ symmetry in heq.
         assert (t' ⟶⋍ t'') as (t3 & l3 & l4).
         { eapply eq_spec; eauto. }
         exists (p, t3). by apply par_step_right.
      ++ symmetry in heq.
         assert (t' ⟶⋍[μ2] t'') as (t3 & l3 & l4).
         { eapply eq_spec; eauto. }
         exists (p', t3). by eapply par_step_sync.
    + intros p' l. by apply IHpt.
    + intros t'' l.
      assert (t ⟶⋍ t'') as (t''' & l3 & l4).
      { eapply eq_spec; eauto. }
      eauto.
    + intros p' r' μ1 μ2 hs l__r l__p.
      assert (t ⟶⋍[μ2] r') as (e' & l__e' & eq').
      { eapply eq_spec; eauto. } eauto.
Qed.

Lemma must_eq_server `{
  gLtsEqP : @gLtsEq P Aproc Hp,
  gLtsT : !@gLtsEq T Atest Ht, !Testing_Predicate outcome _,
  SA : !SyncAction Aproc Atest, STS : !ParSts P T (@gLtsEq_gLts P Aproc Hp gLtsEqP) gLtsT,
  !ParStsSpec P T (@gLtsEq_gLts P Aproc Hp gLtsEqP) gLtsT SA STS} :

  forall (p q : P) (t : T), p ⋍ q -> p must_pass t -> q must_pass t.
Proof.
  intros p q t heq hm.
  revert q heq.
  induction hm as [p t hout | p t nh ex pt IHpt et IHet com IHcom]; intros q heq.
  - now apply m_now.
  - apply m_step; [exact nh | | | |].
    + destruct ex as (y & l).
      destruct (par_step_inv _ _ _ l)
        as [(p' & -> & lp) | [(t' & -> & lt) | (p' & t' & μ1 & μ2 & -> & hs & l1 & l2)]].
      ++ symmetry in heq.
         assert (q ⟶⋍ p') as (q' & l3 & l4).
         { eapply eq_spec; eauto. }
         exists (q', t). by apply par_step_left.
      ++ exists (q, t'). by apply par_step_right.
      ++ symmetry in heq.
         assert (q ⟶⋍[μ1] p') as (q' & l3 & l4).
         { eapply eq_spec; eauto. }
         exists (q', t'). by eapply par_step_sync.
    + intros q' l.
      assert (p ⟶⋍ q') as (p' & l3 & l4).
      { eapply eq_spec; eauto. } eauto.
    + intros t' l. by apply IHet.
    + intros q' e' μ1 μ2 hs l__e l__q.
      assert (p ⟶⋍[μ1] q') as (p' & l3 & l4).
      { eapply eq_spec; eauto. } eauto.
Qed.

Lemma must_preserved_by_lts_tau_srv `{
  gLtsP : @gLts P Aproc Hp,
  gLtsT : !@gLtsEq T Atest Ht, !Testing_Predicate outcome _,
  SA : !SyncAction Aproc Atest, STS : !ParSts P T gLtsP gLtsT,
  !ParStsSpec P T gLtsP gLtsT SA STS}

  (p1 p2 : P) (t : T) :
  p1 must_pass t -> p1 ⟶ p2 -> p2 must_pass t.
Proof. by inversion 1; eauto with mdb. Qed.

Lemma must_preserved_by_weak_nil_srv `{
  gLtsP : @gLts P Aproc Hp,
  gLtsT : !@gLtsEq T Atest Ht, !Testing_Predicate outcome _,
  SA : !SyncAction Aproc Atest, STS : !ParSts P T gLtsP gLtsT,
  !ParStsSpec P T gLtsP gLtsT SA STS}

  (p q : P) (t : T) :
  p must_pass t -> p ⟹ q
    -> q must_pass t.
Proof.
  intros hm w.
  dependent induction w; eauto with mdb.
  eapply IHw; eauto.
  eapply must_preserved_by_lts_tau_srv; eauto.
Qed.

Lemma must_preserved_by_lts_tau_clt `{
  gLtsP : @gLts P Aproc Hp,
  gLtsT : !@gLtsEq T Atest Ht, !Testing_Predicate outcome _,
  SA : !SyncAction Aproc Atest, STS : !ParSts P T gLtsP gLtsT,
  !ParStsSpec P T gLtsP gLtsT SA STS}

  (p : P) (e1 e2 : T) :
  p must_pass e1 -> ¬ outcome e1 -> e1 ⟶ e2 -> p must_pass e2.
Proof. by inversion 1; eauto with mdb. Qed.

Lemma must_preserved_by_synch_if_notoutcome `{
  gLtsP : @gLts P Aproc Hp,
  gLtsT : !@gLtsEq T Atest Ht, !Testing_Predicate outcome _,
  SA : !SyncAction Aproc Atest, STS : !ParSts P T gLtsP gLtsT,
  !ParStsSpec P T gLtsP gLtsT SA STS}

  (p p' : P) (t t' : T) μ μ':
  p must_pass t -> ¬ outcome t -> sync μ μ' -> p ⟶[μ] p' -> t ⟶[μ'] t'
    -> p' must_pass t'.
Proof.
  intros hm u inter l__p l__t.
  inversion hm; subst.
  - contradiction.
  - eapply com; eauto with mdb.
Qed.

Lemma must_preserved_by_lts_tau_clt_rev `{
  gLtsP : @gLts P Aproc Hp,
  gLtsT : !@gLtsEq T Atest Ht, !Testing_Predicate outcome _,
  SA : !SyncAction Aproc Atest, STS : !ParSts P T gLtsP gLtsT,
  !ParStsSpec P T gLtsP gLtsT SA STS}

  (p : P) (t1 t2 : T) :
  p must_pass t2 -> t1 ⟶ t2 -> ¬ outcome t2 -> (forall μ, t1 ↛[μ]) -> (forall t', t1 ⟶ t' -> t' ⋍ t2)
    -> p must_pass t1.
Proof.
  intros must_hyp hyp_tr not_happy not_ext_action tau_determinacy.
  revert t1 hyp_tr not_happy not_ext_action tau_determinacy.
  induction must_hyp as [p t hout | p t nh ex pt IHpt et IHet com IHcom].
  - intros. contradiction.
  - intros. destruct (decide (outcome t1)) as [happy' | not_happy'].
    + now eapply m_now.
    + eapply m_step; eauto.
      ++ exists (p, t). by apply par_step_right.
      ++ intros. assert (t ⋍ t'). { symmetry; eauto. }
         eapply must_eq_client; eauto. eauto.
         eapply m_step; eauto.
      ++ intros p' t' μ1 μ2 inter tr_server tr_client.
         assert (t1 ↛[μ2]); eauto.
         assert (¬ t1 ↛[μ2]). eapply lts_refuses_spec2; eauto. contradiction.
Qed.

Lemma must_preserved_by_lts_tau_clt_rev_rev `{
  gLtsP : @gLts P Aproc Hp,
  gLtsT : !@gLtsEq T Atest Ht, !Testing_Predicate outcome _,
  SA : !SyncAction Aproc Atest, STS : !ParSts P T gLtsP gLtsT,
  !ParStsSpec P T gLtsP gLtsT SA STS}

  (p : P) (t1 t2 : T) :
  p must_pass t2 -> t1 ⟶ t2 -> (forall μ, t1 ↛[μ]) -> (forall t', t1 ⟶ t' -> outcome t') -> p ⤓
    -> p must_pass t1.
Proof.
  intros must_hyp hyp_tr not_ext_action happy_determinacy conv.
  revert t1 t2 must_hyp hyp_tr not_ext_action happy_determinacy.
  induction conv as [p hp IH].
  - intros. destruct (decide (outcome t1)) as [happy | not_happy].
    + now eapply m_now.
    + eapply m_step; eauto.
      ++ exists (p, t2). by apply par_step_right.
      ++ intros. assert (must p t2).
      { eapply m_now; eauto. }
      assert (must p' t2).
      { eapply must_preserved_by_lts_tau_srv; eauto. }
      eauto.
      ++ intros. assert (outcome t'); eauto. now eapply m_now.
      ++ intros. assert (t1 ↛[μ2]); eauto.
         assert (¬ t1 ↛[μ2]). eapply lts_refuses_spec2; eauto. contradiction.
Qed.

Lemma must_terminate_unoutcome `{
  gLtsP : @gLts P Aproc Hp,
  gLtsT : !@gLtsEq T Atest Ht, !Testing_Predicate outcome _,
  SA : !SyncAction Aproc Atest, STS : !ParSts P T gLtsP gLtsT,
  !ParStsSpec P T gLtsP gLtsT SA STS}

  (p : P) (t : T) : p must_pass t -> ¬ outcome t -> p ⤓.
Proof.
  intros hm. induction hm as [p t hout | p t nh ex pt IHpt et IHet com IHcom].
  + contradiction.
  + intros _. constructor. intros p' l. by apply IHpt.
Qed.

Lemma must_terminate_unoutcome' `{
  gLtsP : @gLts P Aproc Hp,
  gLtsT : !@gLtsEq T Atest Ht, !Testing_Predicate outcome _,
  SA : !SyncAction Aproc Atest, STS : !ParSts P T gLtsP gLtsT,
  !ParStsSpec P T gLtsP gLtsT SA STS}

  (p : P) (t : T) : p must_pass t -> outcome t \/ p ⤓.
Proof.
  intros hm. destruct (decide (outcome t)) as [happy | not_happy].
  + now left.
  + right. eapply must_terminate_unoutcome; eauto.
Qed.

Lemma must_preserved_by_lts_wk_clt `{
  gLtsP : @gLts P Aproc Hp,
  gLtsT : !@gLtsEq T Atest Ht, !Testing_Predicate outcome _,
  SA : !SyncAction Aproc Atest, STS : !ParSts P T gLtsP gLtsT,
  !ParStsSpec P T gLtsP gLtsT SA STS}

  (p : P) (t1 t2 : T) :
  p must_pass t1 -> ¬ outcome t1 -> (∀ t', t1 ⟹ t' -> t' ≠ t2 -> ¬ outcome t') -> t1 ⟹ t2 -> p must_pass t2.
Proof.
  intros Hyp not_happy Hyp_not_happy wk_tr.
  remember t2.
  dependent induction wk_tr.
  + subst. eauto.
  + subst. assert (∀ t' : T, q ⟹ t' → t' ≠ t2 → ¬ outcome t') as Hyp_final.
    {intros. eapply Hyp_not_happy. econstructor; eauto. eauto. }
    assert (must p q).
    {eapply must_preserved_by_lts_tau_clt; eauto. }
    destruct (decide (q = t2)) as [ eq | not_eq].
    ++ subst. eauto.
    ++ eapply IHwk_tr; eauto. eapply Hyp_not_happy; eauto with mdb.
Qed.

Lemma must_preserved_by_wt_synch_if_notoutcome `{
  gLtsP : @gLts P Aproc Hp,
  gLtsT : !@gLtsEq T Atest Ht, !Testing_Predicate outcome _,
  SA : !SyncAction Aproc Atest, STS : !ParSts P T gLtsP gLtsT,
  !ParStsSpec P T gLtsP gLtsT SA STS}

  (p p' : P) (t t' : T) (μ : Aproc) (μ' : Atest):
  p must_pass t
    -> ¬ outcome t
      -> sync μ μ'
        -> p ⟹{μ} p'
          -> t ⟶[μ'] t'
            -> p' must_pass t'.
Proof.
  intros hm u duo hwp hwr.
  dependent induction hwp.
  - eapply IHhwp; eauto. eapply must_preserved_by_lts_tau_srv; eauto.
  - eapply must_preserved_by_weak_nil_srv; eauto.
    inversion hm. contradiction. eapply com.
    eassumption. eassumption. eassumption.
Qed.

Lemma ctx_pre_not `{
  gLtsP : @gLts P Aproc Hp,
  gLtsQ : !@gLts Q Aproc Hp,
  gLtsT : !@gLtsEq T Atest Ht, !Testing_Predicate outcome _,
  SA : !SyncAction Aproc Atest, !ParSts P T gLtsP gLtsT, !ParSts Q T gLtsQ gLtsT}
  (p : P) (q : Q) (t : T) :
  p ⊆ₘᵤₛₜᵢ q -> ¬ q must_pass t -> ¬ p must_pass t.
Proof.
  intros hpre not_must.
  intro Hyp. eapply hpre in Hyp.
  contradiction.
Qed.

(* The relation ⊆ₘᵤₛₜᵢ, and so ⊑ₘᵤₛₜᵢ, is reflexive *)
#[global] Instance must_i_refl `{
  gLtsP : @gLts P Aproc Hp,
  gLtsT : !@gLtsEq T Atest Ht, !Testing_Predicate outcome _,
  SA : !SyncAction Aproc Atest, !ParSts P T gLtsP gLtsT} : Reflexive (@ctx_pre P Aproc Hp gLtsP P gLtsP T Atest Ht gLtsT outcome _ SA _ _).
Proof. intros p Hyp_test. eauto. Qed.

(* The relation ⊆ₘᵤₛₜᵢ, and so ⊑ₘᵤₛₜᵢ, is transitive *)
#[global] Instance must_i_transitive `{
  gLtsP : @gLts P Aproc Hp,
  gLtsT : !@gLtsEq T Atest Ht, !Testing_Predicate outcome _,
  SA : !SyncAction Aproc Atest, !ParSts P T gLtsP gLtsT} : Transitive (@ctx_pre P Aproc Hp gLtsP P gLtsP T Atest Ht gLtsT outcome _ SA _ _).
Proof.
  intros p q r Hyp1 Hyp2. intros t Hyp_test. eapply Hyp2. eapply Hyp1. eauto.
Qed.

#[global] Instance must_i_preorder `{
  gLtsP : @gLts P Aproc Hp,
  gLtsT : !@gLtsEq T Atest Ht, !Testing_Predicate outcome _,
  SA : !SyncAction Aproc Atest, !ParSts P T gLtsP gLtsT} : PreOrder (@ctx_pre P Aproc Hp gLtsP P gLtsP T Atest Ht gLtsT outcome _ SA _ _).
Proof.
  split.
  + exact must_i_refl.
  + exact must_i_transitive.
Qed.
