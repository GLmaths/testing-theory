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

From stdpp Require Import base decidable gmap finite.
From Coq Require Import ssreflect.
From Coq.Program Require Import Equality.
From Must Require Import gLts Bisimulation Lts_OBA Lts_FW Lts_OBA_FB StateTransitionSystems Termination
    Must Bar CompletenessAS SoundnessAS Lift Subset_Act FiniteImageLTS WeakTransitions Convergence
    InteractionBetweenLts MultisetLTSConstruction ForwarderConstruction  ParallelLTSConstruction ActTau
    Testing_Predicate DefinitionAS Must.

Section preorder.

  (** Extensional definition of Must *)

  Definition must_extensional {P : Type}
    `{Sts (P * E), outcome : E -> Prop} 
    (p : P) (e : E) : Prop :=
    forall η : max_exec_from (p, e), exists n fex, mex_take_from n η = Some fex 
          /\ outcome (fex_from_last fex).2 .

  Definition outcome_client {P : Type} `{Sts (P * E), outcome : E -> Prop} (s : (P * E)) := outcome s.2.

  #[global] Program Instance must_bar {P : Type} {E : Type} `{Sts (P * E)} (outcome : E -> Prop)
    `{outcome_decidable : forall e, Decision (outcome e)}: Bar (P * E) :=
    {| bar_pred '(p, e) := outcome e |}.
  Next Obligation. intros. destruct x as (p, e). simpl. eauto. Defined.

  Lemma must_intensional_coincide {P : Type}
    `{Sts (P * E), outcome : E -> Prop, outcome_decidable : 
    forall (e : E), Decision (outcome e)}
    (p : P) (e : E) : @intensional_pred (P * E) _ (must_bar outcome) (p, e) ↔ 
    @must_sts P E _ outcome p e.
  Proof.
    split.
    - intros H1. dependent induction H1; subst.
      + rewrite /bar_pred /= in H1. now eapply m_sts_now.
      + destruct (outcome_decidable e).
        rewrite /bar_pred /= in H1.
        now eapply m_sts_now. eapply m_sts_step; eauto.
    - intros hm; dependent induction hm.
      + constructor 1. 
        rewrite /bar_pred //=.
      + constructor 2.
        * eassumption.
        * intros (q, e') Hstep. apply H0 =>//=.
  Qed.

  Lemma must_ext_pred_iff_must_extensional {P : Type}
    `{StsPE : Sts (P * E), outcome : E -> Prop, outcome_decidable : forall (e : E), Decision (outcome e)}
    (p : P) (e : E) : @extensional_pred _ _ (must_bar outcome) (p, e) <-> 
    @must_extensional P E _ outcome p e.
  Proof. split; intros Hme η; destruct (Hme η) as (?&?&?&?).
         exists x, x0. split. eassumption. simpl. destruct (fex_from_last x0). naive_solver.
         exists x, x0. split. eassumption. simpl. destruct (fex_from_last x0). naive_solver.
  Qed.

  Definition pre_extensional
    {P : Type} {Q : Type} 
    `{Sts (P * E), Sts (Q * E), outcome : E -> Prop, outcome_decidable : forall (e : E), 
    Decision (outcome e)}
    (p : P) (q : Q) : Prop :=
    forall (e : E), @must_extensional P E _ outcome p e -> @must_extensional Q E _ outcome q e.

  (* ************************************************** *)

  Lemma must_extensional_iff_must_sts
    {P : Type}
    `{outcome : E -> Prop, outcome_decidable : forall (e : E), Decision (outcome e)}
    `{gLtsP : @gLts P A H, !FiniteImagegLts P A,
    gLtsE : !gLts E A, !gLtsEq E A, !Testing_Predicate E A outcome,  !FiniteImagegLts E A}
    `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE} (* à rajouter en context ? *)
    (p : P) (e : E) : 
    @must_extensional P E _ outcome p e <-> @must_sts P E _ outcome p e.
  Proof.
    split.
    - intros hm. destruct Testing_Predicate0.
      eapply must_ext_pred_iff_must_extensional in hm.
      now eapply must_intensional_coincide, extensional_implies_intensional.
    - intros hm. destruct Testing_Predicate0.
      eapply must_intensional_coincide in hm.
      rewrite <- must_ext_pred_iff_must_extensional.
      eapply intensional_implies_extensional. eapply hm.
  Qed.

  Notation "p ⊑ₑ q" := (pre_extensional p q) (at level 70).

  Context `{outcome : E -> Prop}.
  Context `{outcome_dec : forall e, Decision (outcome e)}.
  Context `{P : Type}.
  Context `{Q : Type}.
  Context `{H : !ExtAction A}.
  Context `{gLtsP : !gLts P A, !FiniteImagegLts P A}.
  Context `{gLtsQ : !gLts Q A, !FiniteImagegLts Q A}.
  Context `{gLtsE : !gLts E A, !FiniteImagegLts E A, gLtsEqE: !gLtsEq E A, !Testing_Predicate E A outcome}.
  Context `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}.
  Context `{@Prop_of_Inter Q E A parallel_inter H gLtsQ gLtsE}.

  (* ************************************************** *)

  Lemma pre_extensional_eq (p : P) (q : Q) : 
    @pre_extensional P Q _ _ _ outcome _ p q <-> p ⊑ₘᵤₛₜᵢ q.
    unfold pre_extensional, ctx_pre.
  Proof.
    split; intros hpre e.
    - rewrite <- 2 must_sts_iff_must, <- 2 must_extensional_iff_must_sts; eauto.
    - rewrite -> 2 must_extensional_iff_must_sts, -> 2 must_sts_iff_must; eauto.
  Qed.

End preorder.
