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
From Coq.Program Require Import Equality.
From stdpp Require Import finite gmap decidable.
From Must Require Import ActTau gLts Bisimulation Lts_OBA Subset_Act WeakTransitions Testing_Predicate
    StateTransitionSystems InteractionBetweenLts Convergence Termination FiniteImageLTS.

Inductive may_sts 
  `{Sts (P1 * P2), attaboy : P2 -> Prop}
  (p : P1) (e : P2) : Prop :=
| m_sts_now : attaboy e -> may_sts p e
| m_sts_step p' e' (nh : ¬ attaboy e) (nst : sts_step (p, e) (p', e')) (l : may_sts p' e') : may_sts p e
.

Global Hint Constructors may_sts:mdb.

Inductive may `{
    gLtsP : @gLts P A H, 
    gLtsE : ! gLts E A, ! gLtsEq E A, !Testing_Predicate E A attaboy} 

    `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

    (p : P) (e : E) : Prop :=
| may_now : attaboy e -> may p e
| may_server_step p' (nh : ¬ attaboy e) (pt : p ⟶ p') (hmay : may p' e) : may p e
| may_client_step e' (nh : ¬ attaboy e) (et : e ⟶ e') (hmay : may p e') : may p e
| may_com_step p' μ1 e' μ2 (nh : ¬ attaboy e) (inter : parallel_inter μ1 μ2) 
          (trS : p ⟶[μ1] p') (trC : e ⟶[μ2] e') (hmay : may p' e') : may p e.

Global Hint Constructors may:mdb.

Lemma must_sts_iff_must `{
  gLtsP : @gLts P A H, 
  gLtsE : !gLts E A, !gLtsEq E A, !Testing_Predicate E A attaboy}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p : P) (e : E) :
  @may_sts P E _ attaboy p e <-> may p e.
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

Definition ctx_may_pre `{
  gLtsP : gLts P A, 
  gLtsQ : !gLts Q A, 
  gLtsE : ! gLts E A, ! gLtsEq E A, !Testing_Predicate E A attaboy}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE} 
  `{@Prop_of_Inter Q E A parallel_inter H gLtsQ gLtsE}

  (p : P) (q : Q) 
  := forall (e : E), may p e -> may q e.

Global Hint Unfold ctx_may_pre: mdb.

Notation "p ⊑ q" := (ctx_may_pre p q) (at level 70).



(********************************************* Properties on Must_i **********************************************)

Lemma must_eq_client `{
  gLtsP : gLts P A, 
  gLtsQ : ! gLts Q A, ! gLtsEq Q A, !Testing_Predicate Q A attaboy}

  `{@Prop_of_Inter P Q A parallel_inter H gLtsP gLtsQ} :

  forall (p : P) (q r : Q), q ⋍ r -> may p q -> may p r.
Proof.
  intros p q r heq hm.
  revert r heq.
  dependent induction hm; intros.
  - apply may_now. eapply attaboy_preserved_by_eq; eauto.
  - eapply may_server_step; eauto. eapply unattaboy_preserved_by_eq; eauto. symmetry. exact heq.
  - edestruct (eq_spec r e') as (r' & tr & eq).
    { exists e. split; eauto. now symmetry. }
    eapply may_client_step; eauto. eapply unattaboy_preserved_by_eq; eauto. symmetry. exact heq.
    eapply IHhm. now symmetry.
  - edestruct (eq_spec r e') as (r' & tr & eq).
    { exists e. split; eauto. now symmetry. }
    eapply may_com_step; eauto. eapply unattaboy_preserved_by_eq; eauto. symmetry. exact heq.
    eapply IHhm. now symmetry.
Qed.

Lemma must_eq_server `{
  gLtsP : gLts P A, ! gLtsEq P A,
  gLtsE : ! gLts E A, ! gLtsEq E A, !Testing_Predicate E A attaboy} 

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE} :

  forall (p q : P) (e : E), p ⋍ q -> may p e -> may q e.
Proof.
  intros p q r heq hm.
  revert q heq.
  dependent induction hm; intros.
  - apply may_now. exact H1.
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

Lemma may_not_stable_or_attaboy `{
  gLtsP : gLts P A, 
  gLtsE : ! gLts E A, ! gLtsEq E A, !Testing_Predicate E A attaboy}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p : P) (e : E) : may p e -> attaboy e \/ ¬ e ↛.
Proof. 
  intros hm. destruct (decide (attaboy e)) as [happy | not_happy].
  + now left. 
  + right. admit.
Admitted.

Lemma ctx_may_pre_not `{
  gLtsP : gLts P A, 
  gLtsQ : !gLts Q A, 
  gLtsE : ! gLts E A, ! gLtsEq E A, !Testing_Predicate E A attaboy}
  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE} 
  `{@Prop_of_Inter Q E A parallel_inter H gLtsQ gLtsE}
  (p : P) (q : Q) (e : E) :
  p ⊑ q -> ¬ may q e -> ¬ may p e.
Proof.
  intros hpre not_may.
  intro Hyp. eapply hpre in Hyp.
  contradiction.
Qed.

(********************************************* Alt-preorder of May_i **********************************************)


(* Definition bhv_pre_cond1 `{LtsP : @gLts P A H, LtsQ : @gLts Q A H} 
  (p : P) (q : Q) := (* TODO *).

Notation "p ≼₁ q" := (bhv_pre_cond1 p q) (at level 70). *)

(* Definition bhv_pre_cond2 `{LtsP : @gLts P A H, LtsQ : @gLts Q A H}
  (p : P) (q : Q) :=(* TODO *).

Notation "p ≼₂ q" := (bhv_pre_cond2 p q) (at level 70). *)

(* Definition bhv_pre `{LtsP : @gLts P A H, LtsQ : @gLts Q A H}
    (p : P) (q : Q) := 
      p ≼₁ q /\ p ≼₂ q.

Notation "p ≼ q" := (bhv_pre p q) (at level 70). *)
