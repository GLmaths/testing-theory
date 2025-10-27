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
    `{Sts (P * E), attaboy : E -> Prop} 
    (p : P) (e : E) : Prop :=
    forall η : max_exec_from (p, e), exists n fex, mex_take_from n η = Some fex 
          /\ attaboy (fex_from_last fex).2 .

  Definition attaboy_client {P : Type} `{Sts (P * E), attaboy : E -> Prop} (s : (P * E)) := attaboy s.2.

  #[global] Program Instance must_bar {P : Type} {E : Type} `{Sts (P * E)} (attaboy : E -> Prop)
    `{attaboy_decidable : forall e, Decision (attaboy e)}: Bar (P * E) :=
    {| bar_pred '(p, e) := attaboy e |}.
  Next Obligation. intros. destruct x as (p, e). simpl. eauto. Defined.

  Lemma must_intensional_coincide {P : Type}
    `{Sts (P * E), attaboy : E -> Prop, attaboy_decidable : 
    forall (e : E), Decision (attaboy e)}
    (p : P) (e : E) : @intensional_pred (P * E) _ (must_bar attaboy) (p, e) ↔ 
    @must_sts P E _ attaboy p e.
  Proof.
    split.
    - intros H1. dependent induction H1; subst.
      + rewrite /bar_pred /= in H1. now eapply m_sts_now.
      + destruct (attaboy_decidable e).
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
    `{StsPE : Sts (P * E), attaboy : E -> Prop, attaboy_decidable : forall (e : E), Decision (attaboy e)}
    (p : P) (e : E) : @extensional_pred _ _ (must_bar attaboy) (p, e) <-> 
    @must_extensional P E _ attaboy p e.
  Proof. split; intros Hme η; destruct (Hme η) as (?&?&?&?).
         exists x, x0. split. eassumption. simpl. destruct (fex_from_last x0). naive_solver.
         exists x, x0. split. eassumption. simpl. destruct (fex_from_last x0). naive_solver.
  Qed.

  Definition pre_extensional
    {P : Type} {Q : Type} 
    `{Sts (P * E), Sts (Q * E), attaboy : E -> Prop, attaboy_decidable : forall (e : E), 
    Decision (attaboy e)}
    (p : P) (q : Q) : Prop :=
    forall (e : E), @must_extensional P E _ attaboy p e -> @must_extensional Q E _ attaboy q e.

  (* ************************************************** *)

  Lemma must_extensional_iff_must_sts
    {P : Type}
    `{attaboy : E -> Prop, attaboy_decidable : forall (e : E), Decision (attaboy e)}
    `{gLtsP : @gLts P A H, !FiniteImagegLts P A,
    gLtsE : !gLts E A, !gLtsEq E A, !Testing_Predicate E A attaboy,  !FiniteImagegLts E A}
    `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE} (* à rajouter en context ? *)
    (p : P) (e : E) : 
    @must_extensional P E _ attaboy p e <-> @must_sts P E _ attaboy p e.
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

  Context `{attaboy : E -> Prop}.
  Context `{attaboy_dec : forall e, Decision (attaboy e)}.
  Context `{P : Type}.
  Context `{Q : Type}.
  Context `{H : !ExtAction A}.
  Context `{gLtsP : !gLts P A, !FiniteImagegLts P A}.
  Context `{gLtsQ : !gLts Q A, !FiniteImagegLts Q A}.
  Context `{gLtsE : !gLts E A, !FiniteImagegLts E A, gLtsEqE: !gLtsEq E A, !Testing_Predicate E A attaboy}.
  Context `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}.
  Context `{@Prop_of_Inter Q E A parallel_inter H gLtsQ gLtsE}.

  (* ************************************************** *)

  Lemma pre_extensional_eq (p : P) (q : Q) : 
    @pre_extensional P Q _ _ _ attaboy _ p q <-> p ⊑ q.
    unfold pre_extensional, ctx_pre.
  Proof.
    split; intros hpre e.
    - rewrite <- 2 must_sts_iff_must, <- 2 must_extensional_iff_must_sts; eauto.
    - rewrite -> 2 must_extensional_iff_must_sts, -> 2 must_sts_iff_must; eauto.
  Qed.

  Context `{@gLtsObaFB P A H gLtsP gLtsEqP gLtsObaP}.
  Context `{@gLtsObaFB Q A H gLtsQ gLtsEqQ gLtsObaQ}.
  Context `{@gLtsObaFB E A H gLtsE gLtsEqE gLtsObaE}.

  Context `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}.
  Context `{@Prop_of_Inter (P * mb A) E A parallel_inter H (inter_lts fw_inter) gLtsE}.
  Context `{@Prop_of_Inter Q (mb A) A fw_inter H gLtsQ MbgLts}.
  Context `{@Prop_of_Inter (Q * mb A) E A parallel_inter H (inter_lts fw_inter) gLtsE}.

  Context `{@PreExtAction A H (P * mb A) FinA PreA PreA_eq PreA_countable 𝝳 Φ (FW_gLts gLtsP)}.
  Context `{@PreExtAction A H (Q * mb A) FinA PreA PreA_eq PreA_countable 𝝳 Φ (FW_gLts gLtsQ)}.
  Context `{@AbsAction A H E FinA gLtsE Φ}.

  Context `{igen_conv : @gen_spec_conv E _ _ _ _ attaboy Testing_Predicate0 co_of gen_conv}.
  Context `{igen_acc : @gen_spec_acc PreA _ _ E _ _ _ _ attaboy Testing_Predicate0 co_of gen_acc (fun x => 𝝳 (Φ x))}.

  (* ************************************************** *)

  (** Equivalence between the extensional definition of the contextual preorder and
      the alternative, inductive characterisation. *)
  Theorem equivalence_bhv_acc_ctx (p : P) (q : Q) :
    @pre_extensional P Q _ _ _ attaboy _ p q <-> (p, ∅) ≼ (q, ∅).
  Proof.
    split.
    - intros hpre%pre_extensional_eq.
      now eapply lift_fw_ctx_pre, completeness_fw in hpre.
    - intros hpre%soundness_fw.
      now eapply pre_extensional_eq, lift_fw_ctx_pre.
  Qed.

End preorder.
