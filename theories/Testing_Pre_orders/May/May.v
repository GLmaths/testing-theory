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

From Stdlib.Lists Require Import List.
From Stdlib.Program Require Import Equality.
From stdpp Require Import decidable.
From TestingTheory Require Import ActTau gLts Bisimulation Testing_Predicate StateTransitionSystems InteractionBetweenLts
    WeakTransitions coWeakTransition.

(********************************************* Definition of May *****************************************)

Inductive may_sts 
  `{Sts (P * T), outcome : T -> Prop}
  (p : P) (t : T) : Prop :=
| m_sts_now : outcome t -> may_sts p t
| m_sts_step p' t' (nh : ¬ outcome t) (nst : sts_step (p, t) (p', t')) (l : may_sts p' t') : may_sts p t
.

Global Hint Constructors may_sts:mdb.

(********************* Definition of May decomposed with parallel computation definition *****************)

Inductive may `{
    gLtsP : @gLts P A H, 
    gLtsT : !gLtsEq T H, !Testing_Predicate outcome gLtsT} 

    {PInter: Prop_of_Inter P T A dual}

    (p : P) (t : T) : Prop :=
| may_now : outcome t -> may p t
| may_server_step p' (nh : ¬ outcome t) (pt : p ⟶ p') (hmay : may p' t) : may p t
| may_client_step t' (nh : ¬ outcome t) (et : t ⟶ t') (hmay : may p t') : may p t
| may_com_step p' μ1 t' μ2 (nh : ¬ outcome t) (inter : dual μ1 μ2) 
          (trS : p ⟶[μ1] p') (trC : t ⟶[μ2] t') (hmay : may p' t') : may p t.

Global Hint Constructors may:mdb.

Notation "p 'may_pass' t" := (may p t) (at level 70).

(****************** May and May decomposed with parallel computation definition are equivalent ****************)

Lemma must_sts_iff_must `{
  gLtsP : @gLts P A H, 
  gLtsT : !gLtsEq T H, !Testing_Predicate outcome gLtsT}

  {_ : Prop_of_Inter P T A dual}

  (p : P) (t : T) :
  @may_sts P T _ outcome p t <-> may p t.
Proof.
  split.
  - intro hm. dependent induction hm; eauto with mdb.
    inversion nst as [ | | ]; subst.
    + eapply may_server_step; eauto.
    + eapply may_client_step; eauto.
    + eapply may_com_step; eauto. 
  - intro hm. dependent induction hm; eauto with mdb.
    + eapply m_sts_step; eauto. eapply ParLeft; eauto.
    + eapply m_sts_step; eauto. eapply ParRight; eauto.
    + eapply m_sts_step; eauto. eapply ParSync; eauto.
Qed.

(********************************* Definition of the contextual pre order with May *********************************)

Definition ctx_may_pre `{
  gLtsP : @gLts P A H, 
  gLtsQ : !gLts Q H, 
  gLtsT : ! gLtsEq T H, !Testing_Predicate outcome gLtsT}

  {_ : Prop_of_Inter P T A dual}
  {_ : Prop_of_Inter Q T A dual}

  (p : P) (q : Q) 
  := forall (t : T), p may_pass t -> q may_pass t.

Global Hint Unfold ctx_may_pre: mdb.

Notation "p ⊑ₘₐᵧ q" := (ctx_may_pre p q) (at level 70).
Notation "p ⋢ₘₐᵧ q" := (¬ ctx_may_pre p q) (at level 70).

(********************************************* Properties on May **********************************************)

Lemma may_eq_client `{
  gLtsP : @gLts P A H, 
  gLtsT : ! gLtsEq T H, !Testing_Predicate outcome gLtsT}

  {_ : Prop_of_Inter P T A dual} :

  forall (p : P) (t1 t2 : T), t1 ⋍ t2 -> p may_pass t1 -> p may_pass t2.
Proof.
  intros p q r heq hm.
  revert r heq.
  dependent induction hm; intros.
  - apply may_now. eapply outcome_preserved_by_eq; eauto.
  - eapply may_server_step; eauto. eapply unoutcome_preserved_by_eq; eauto. symmetry. exact heq.
  - edestruct (eq_spec r t') as (r' & tr & eq).
    { exists t. split; eauto. now symmetry. }
    eapply may_client_step; eauto. eapply unoutcome_preserved_by_eq; eauto. symmetry. exact heq.
    eapply IHhm. now symmetry.
  - edestruct (eq_spec r t') as (r' & tr & eq).
    { exists t. split; eauto. now symmetry. }
    eapply may_com_step; eauto. eapply unoutcome_preserved_by_eq; eauto. symmetry. exact heq.
    eapply IHhm. now symmetry.
Qed.

Lemma may_eq_server `{
  gLtsP : @gLtsEq P A H,
  gLtsT : ! gLtsEq T H, !Testing_Predicate outcome gLtsT} 

  {_ : Prop_of_Inter P T A dual} :

  forall (p1 p2 : P) (t : T), p1 ⋍ p2 -> p1 may_pass t -> p2 may_pass t.
Proof.
  intros p q r heq hm.
  revert q heq.
  dependent induction hm; intros.
  - now apply may_now.
  - edestruct (eq_spec q p') as (q' & tr & eq).
    { exists p. split; eauto. now symmetry. }
    eapply may_server_step; eauto.
    eapply IHhm. now symmetry.
  - eapply may_client_step; eauto.
  - edestruct (eq_spec q p') as (q' & tr & eq).
    { exists p. split; eauto. now symmetry. }
    eapply may_com_step; eauto.
    eapply IHhm. now symmetry.
Qed.

Lemma may_not_stable_or_outcome `{
  gLtsP : @gLts P A H, 
  gLtsT : ! gLtsEq T H, !Testing_Predicate outcome gLtsT}

  {_ : Prop_of_Inter P T A dual}

  (p : P) (t : T) : p may_pass t -> outcome t \/ ¬ t ↛ \/ (exists μ, ¬ t ↛[μ]). 
Proof. 
  intros hm. destruct (decide (outcome t)) as [happy | not_happy].
  + now left. 
  + right. dependent induction hm. 
    - contradiction. 
    - exact (IHhm not_happy). 
    - left. eapply lts_refuses_spec2; eauto.
    - right. exists μ2. eapply lts_refuses_spec2; eauto.
Qed.

Lemma ctx_may_pre_not `{
  gLtsP : @gLts P A H,
  gLtsQ : !gLts Q H,
  gLtsT : ! gLtsEq T H, !Testing_Predicate outcome gLtsT}
  {_ : Prop_of_Inter P T A dual}
  {_ : Prop_of_Inter Q T A dual}
  (p : P) (q : Q) (t : T) :
  p ⊑ₘₐᵧ  q -> ¬ may q t -> ¬ may p t.
Proof.
  intros hpre not_may.
  intro Hyp. eapply hpre in Hyp.
  contradiction.
Qed.

(********************************* [may] and (co-)weak transitions **********************************************)

(** [may] is preserved backwards along a pure-τ weak transition of the
    server or the client — used by both the plain and the co-trace
    characterisations of May ([DefinitionTI.v]/[DefinitionTIco.v]), so
    it lives here rather than being duplicated in either. *)

Section May_and_wt.

Context `{gLtsP : @gLts P A H}.
Context `{gLtsT : !gLtsEq T H, !Testing_Predicate outcome gLtsT}.
Context {PInter : Prop_of_Inter P T A dual}.

Lemma may_wt_nil_server (s : trace A) (p1 p2 : P) (t : T) :
  p1 ⟹[s] p2 -> s = [] -> p2 may_pass t -> p1 may_pass t.
Proof.
  intro w.
  induction w as [ p | s' p q r l w IH | μ s' p q r l w IH ]; intros Hs hm.
  - exact hm.
  - destruct (decide (outcome t)) as [happy | nh].
    + now apply may_now.
    + eapply may_server_step; eauto.
  - discriminate.
Qed.

Lemma may_wt_tau_server (p1 p2 : P) (t : T) :
  p1 ⟹ p2 -> p2 may_pass t -> p1 may_pass t.
Proof. intros w hm. eapply may_wt_nil_server; eauto. Qed.

Lemma may_wt_nil_client (r : P) (s : trace A) (t1 t2 : T) :
  t1 ⟹[s] t2 -> s = [] -> r may_pass t2 -> r may_pass t1.
Proof.
  intro w.
  induction w as [ t | s' t u v l w IH | μ s' t u v l w IH ]; intros Hs hm.
  - exact hm.
  - destruct (decide (outcome t)) as [happy | nh].
    + now apply may_now.
    + eapply may_client_step; eauto.
  - discriminate.
Qed.

Lemma may_wt_tau_client (r : P) (t1 t2 : T) :
  t1 ⟹ t2 -> r may_pass t2 -> r may_pass t1.
Proof. intros w hm. eapply may_wt_nil_client; eauto. Qed.

(** The co-trace analogues, for the *process* side ([DefinitionTIco.v]
    puts the duality there, never on the test/client — see that file).
    With an empty trace, [cowt] only ever uses its
    [cowt_nil]/[cowt_tau] constructors (no dual action involved), so
    plain induction applies exactly as above. *)

Lemma may_wt_nil_server_co (s : trace A) (p1 p2 : P) (t : T) :
  p1 ⟹ᶜᵒ[s] p2 -> s = [] -> p2 may_pass t -> p1 may_pass t.
Proof.
  intro w.
  induction w as [ p | s' p q r l w IH | μ μ' s' p q r duo l w IH ]; intros Hs hm.
  - exact hm.
  - destruct (decide (outcome t)) as [happy | nh].
    + now apply may_now.
    + eapply may_server_step; eauto.
  - discriminate.
Qed.

Lemma may_wt_tau_server_co (p1 p2 : P) (t : T) :
  p1 ⟹ᶜᵒ p2 -> p2 may_pass t -> p1 may_pass t.
Proof. intros w hm. eapply may_wt_nil_server_co; eauto. Qed.

End May_and_wt.

