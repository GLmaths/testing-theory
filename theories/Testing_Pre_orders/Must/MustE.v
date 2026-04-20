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
From Stdlib Require Import ssreflect.
From Stdlib.Program Require Import Equality.
From Must Require Import gLts Bisimulation Lts_OBA Lts_FW Lts_OBA_FB StateTransitionSystems Termination
    Must Bar CompletenessAS SoundnessAS Lift Subset_Act FiniteImageLTS WeakTransitions Convergence
    InteractionBetweenLts MultisetLTSConstruction ForwarderConstruction ParallelLTSConstruction ActTau
    Testing_Predicate DefinitionAS Must.

Section preorder.

  (** Extensional definition of Must *)

  Definition must_extensional {P : Type}
    `{Sts (P * T), outcome : T -> Prop} 
    (p : P) (t : T) : Prop :=
    forall η : max_exec_from (p, t), exists n fex, mex_take_from n η = Some fex 
          /\ outcome (fex_from_last fex).2 .

  Definition outcome_client {P : Type} `{Sts (P * T), outcome : T -> Prop} (s : (P * T)) := outcome s.2.

  #[global] Program Instance must_bar {P : Type} {T : Type} `{Sts (P * T)} (outcome : T -> Prop)
    `{outcome_decidable : forall t, Decision (outcome t)}: Bar (P * T) :=
    {| bar_pred '(p, t) := outcome t |}.
  Next Obligation. intros. destruct x as (p, t). simpl. eauto. Defined.

  Lemma must_intensional_coincide {P : Type}
    `{Sts (P * T), outcome : T -> Prop, outcome_decidable : 
    forall (t : T), Decision (outcome t)}
    (p : P) (t : T) : @intensional_pred (P * T) _ (must_bar outcome) (p, t) ↔ 
    @must_sts P T _ outcome p t.
  Proof.
    split.
    - intros H1. dependent induction H1; subst.
      + rewrite /bar_pred /= in H1. now eapply m_sts_now.
      + destruct (outcome_decidable t).
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
    `{StsPT : Sts (P * T), outcome : T -> Prop, outcome_decidable : forall (t : T), Decision (outcome t)}
    (p : P) (t : T) : @extensional_pred _ _ (must_bar outcome) (p, t) <-> 
    @must_extensional P T _ outcome p t.
  Proof. split; intros Hme η; destruct (Hme η) as (?&?&?&?).
         exists x, x0. split. eassumption. simpl. destruct (fex_from_last x0). naive_solver.
         exists x, x0. split. eassumption. simpl. destruct (fex_from_last x0). naive_solver.
  Qed.

  Definition pre_extensional
    {P : Type} {Q : Type} 
    `{Sts (P * T), Sts (Q * T), outcome : T -> Prop, outcome_decidable : forall (t : T), 
    Decision (outcome t)}
    (p : P) (q : Q) : Prop :=
    forall (t : T), @must_extensional P T _ outcome p t -> @must_extensional Q T _ outcome q t.

  (* ************************************************** *)

  Lemma must_extensional_iff_must_sts
    {P : Type}
    `{outcome : T -> Prop, outcome_decidable : forall (t : T), Decision (outcome t)}
    `{gLtsP : @gLts P A H, !FiniteImagegLts P A,
      gLtsT : !gLtsEq T H, !FiniteImagegLts T A , !Testing_Predicate T A outcome}
    `{!Prop_of_Inter P T A dual} (* à rajouter en context ? *)
    (p : P) (t : T) : 
    @must_extensional P T _ outcome p t <-> @must_sts P T _ outcome p t.
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

  Notation "p ⊑ₘᵤₛₜ q" := (pre_extensional p q) (at level 70).

  Context `{outcome : T -> Prop}.
  Context `{outcome_dec : forall t, Decision (outcome t)}.
  Context `{P : Type}.
  Context `{Q : Type}.
  Context `{H : !ExtAction A}.
  Context `{gLtsP : !gLts P H, !FiniteImagegLts P A}.
  Context `{gLtsQ : !gLts Q H, !FiniteImagegLts Q A}.
  Context `{gLtsEqT: !gLtsEq T H, !FiniteImagegLts T A, !Testing_Predicate T A outcome}.
  Context `{!Prop_of_Inter P T A dual}.
  Context `{!Prop_of_Inter Q T A dual}.

  (* ************************************************** *)

  Lemma pre_extensional_eq (p : P) (q : Q) : 
    @pre_extensional P Q _ _ _ outcome _ p q <-> p ⊑ₘᵤₛₜᵢ q. (* p ⊑ₘᵤₛₜ q ↔ p ⊑ₘᵤₛₜᵢ q *)
    unfold pre_extensional, ctx_pre.
  Proof.
    split; intros hpre t.
    - rewrite <- 2 must_sts_iff_must, <- 2 must_extensional_iff_must_sts ; eauto.
    - rewrite -> 2 must_extensional_iff_must_sts, -> 2 must_sts_iff_must; eauto.
  Qed.

End preorder.
