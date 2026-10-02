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

(** * Core Erlang: the must preorder and its characterisations

    The observers are VACCS processes: [Erlang_Test_Dilemma] shows that Erlang
    systems cannot follow a trace, so they cannot be the tests.  The framework
    allows the tests to live in their own LTS, and VACCS — instantiated by
    [Erlang_VACCS_Parameters], hence over the very same actions — comes with
    the observers [gen_conv] and [gen_acc] and their specifications.

    What is missing here is only the interaction between an Erlang system (or
    an Erlang forwarder) and an observer. *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list numbers finite sets gmap gmultiset.
From TestingTheory Require Import ActTau InputOutputActions InListPropHelper
  gLts Bisimulation Lts_OBA Lts_OBA_FB Lts_FW Lts_Finite_Output_Chain
  FiniteImageLTS coFiniteImage Subset_Act Termination Convergence WeakTransitions
  coWeakTransition coConvergence StateTransitionSystems
  InteractionBetweenLts MultisetLTSConstruction ForwarderConstruction
  ParallelLTSConstruction SetLTSConstruction
  Must MustE Lift Testing_Predicate
  DefinitionAS Completeness Soundness Equivalence
  DefinitionASco CompletenessASco SoundnessASco EquivalenceASco TestSpecBridge
  DefinitionMS EquivalenceMS DefinitionFMS EquivalenceFMS
  DefinitionCI EquivalenceCI Coin_tower
  VACCS VACCS_Instance VACCS_Good VACCS_CoFiniteImage VACCS_ta_tc_gen
  Erlang_Syntax Erlang_LTS Erlang_Instance Erlang_LabelAbstraction Erlang_Forwarder.

(** [PreActActionForFW] of [DefinitionAS.v] — the lift of an abstraction to the
    forwarder, whose process-side obligation is [Admitted] — is taken out of
    instance search: [Erl_AbsAction_FW] below replaces it, so that nothing here
    rests on the hole. *)
Remove Hints PreActActionForFW FinitaryPreActActionForFW : typeclass_instances.

Section Erlang_Must_Characterization.

Context `{EP : Erlang_Program}.

(** ** An Erlang system interacting with an observer *)

#[global] Program Instance Erl_Inter_test : Prop_of_Inter sys proc erl_act erl_act dual :=
  {| lts_essential_actions_left S := dom (erl_mo S) ;
     lts_essential_actions_right q := set_map ActOut (outputs_of q) |}.
Next Obligation. intros S ξ hin. by apply erl_out_of_dom. Defined.
Next Obligation.
  intros q ξ hin; simpl in *.
  unfold set_map in hin. simpl in *.
  apply elem_of_list_to_set, list_elem_of_fmap in hin.
  destruct ξ as [a | a].
  - exfalso. destruct hin as (a' & heq & _). inversion heq.
  - eapply outputs_of_spec2. destruct hin as (a' & heq & hmem). inversion heq; subst.
    apply elem_of_elements. exact hmem.
Defined.
Next Obligation.
  intros S μ1 S' q μ2 q' hl1 hl2 hinter; simpl in *.
  destruct μ1 as [a | a].
  - right. apply simplify_match_input in hinter as ->.
    apply elem_of_list_to_set, list_elem_of_fmap. exists a. split; [done |].
    apply elem_of_elements. eapply outputs_of_spec1. exact hl2.
  - left. apply erl_out_shape in hl1 as (p & v & -> & ->).
    apply erl_out_dom. multiset_solver.
Defined.
Next Obligation.
  intros ξ S. destruct ξ as [a | a]; [exact empty | exact {[ ActIn a ]}].
Defined.
Next Obligation.
  intros S S' ξ μ q hmem hl hinter; simpl in *.
  unfold Erl_Inter_test_obligation_4.
  destruct ξ as [a | a].
  - exfalso. unfold set_map in hmem. simpl in *.
    apply elem_of_list_to_set, list_elem_of_fmap in hmem.
    destruct hmem as (a' & heq & _). inversion heq.
  - symmetry in hinter. apply simplify_match_output in hinter as ->. set_solver.
Defined.
Next Obligation.
  intros ξ q. destruct ξ as [a | a]; [exact empty | exact {[ ActIn a ]}].
Defined.
Next Obligation.
  intros q q' ξ μ S hmem hl hinter; simpl in *.
  unfold Erl_Inter_test_obligation_6.
  destruct ξ as [a | a].
  - exfalso. apply erl_dom_out in hmem as (p' & v' & heq & _). discriminate heq.
  - apply simplify_match_output in hinter as ->. set_solver.
Defined.

(** ** An Erlang forwarder interacting with an observer *)

#[global] Program Instance Erl_Inter_FW_test :
  Prop_of_Inter (sys * MO erl_act) proc erl_act erl_act dual :=
  {| lts_essential_actions_left p := dom (erl_mo p.1) ∪ dom (MO_without_not_nb p.2) ;
     lts_essential_actions_right q := set_map ActOut (outputs_of q) |}.
Next Obligation.
  intros (S, m) ξ hin. simpl in *.
  destruct (decide (ξ ∈ dom (MO_without_not_nb m))) as [hm | hm].
  - apply gmultiset_elem_of_dom in hm.
    apply lts_MO_nb_with_nb_spec1 in hm as (nb & hmem).
    assert (m = {[+ ξ +]} ⊎ (m ∖ {[+ ξ +]})) as heq by multiset_solver.
    exists (S, m ∖ {[+ ξ +]}). apply ParRight.
    rewrite heq at 1. by apply lts_multiset_minus.
  - assert (ξ ∈ dom (erl_mo S)) as hS by set_solver.
    destruct (erl_out_of_dom S ξ hS) as (T & hl).
    exists (T, m). by apply ParLeft.
Defined.
Next Obligation.
  intros q ξ hin; simpl in *.
  unfold set_map in hin. simpl in *.
  apply elem_of_list_to_set, list_elem_of_fmap in hin.
  destruct ξ as [a | a].
  - exfalso. destruct hin as (a' & heq & _). inversion heq.
  - eapply outputs_of_spec2. destruct hin as (a' & heq & hmem). inversion heq; subst.
    apply elem_of_elements. exact hmem.
Defined.
Next Obligation.
  intros (S, m) μ1 (S', m') q μ2 q' hl1 hl2 hinter; simpl in *.
  destruct μ1 as [a | a].
  - right. apply simplify_match_input in hinter as ->.
    apply elem_of_list_to_set, list_elem_of_fmap. exists a. split; [done |].
    apply elem_of_elements. eapply outputs_of_spec1. exact hl2.
  - left. inversion hl1; subst.
    + apply elem_of_union. left.
      apply erl_out_shape in l as (p & v & -> & ->). apply erl_out_dom. multiset_solver.
    + apply elem_of_union. right.
      assert (non_blocking (ActOut a)) as nb by (by exists a).
      eapply non_blocking_action_in_ms in l; eauto.
      apply gmultiset_elem_of_dom.
      apply (lts_MO_nb_with_nb_spec2 (ActOut a) _ nb). multiset_solver.
Defined.
Next Obligation.
  intros ξ p. destruct ξ as [a | a]; [exact empty | exact {[ ActIn a ]}].
Defined.
Next Obligation.
  intros (S, m) (S', m') ξ μ q hmem hl hinter; simpl in *.
  unfold Erl_Inter_FW_test_obligation_4.
  destruct ξ as [a | a].
  - exfalso. unfold set_map in hmem. simpl in *.
    apply elem_of_list_to_set, list_elem_of_fmap in hmem.
    destruct hmem as (a' & heq & _). inversion heq.
  - symmetry in hinter. apply simplify_match_output in hinter as ->. set_solver.
Defined.
Next Obligation.
  intros ξ q. destruct ξ as [a | a]; [exact {[ ActOut a ]} | exact {[ ActIn a ]}].
Defined.
Next Obligation.
  intros q q' ξ μ (S, m) hmem hl hinter; simpl in *.
  unfold Erl_Inter_FW_test_obligation_6.
  destruct ξ as [a | a].
  - apply simplify_match_input in hinter as ->. set_solver.
  - apply simplify_match_output in hinter as ->. set_solver.
Defined.

(** ** The abstraction lifted to the forwarder

    [DefinitionAS.v] lifts an abstraction from [P] to [P * MO A] through
    [PreActActionForFW], whose process-side obligation is [Admitted].  It is not
    needed: [𝝳ᴠᴀᴄᴄꜱ] is the identity, so that obligation is its own hypothesis
    rewritten.  The instance is given here so that nothing below rests on the
    hole. *)

#[global] Program Instance Erl_AbsAction_FW :
  @AbsAction (sys * MO erl_act) proc FinA PreAct erl_act VACCS_ExtAction
    Φᴠᴀᴄᴄꜱ 𝝳ᴠᴀᴄᴄꜱ _ _ _ VACCS_gLtsEq _.
Next Obligation.
  intros t β β' hb hb' heq hmem.
  eapply (@abstraction_test_spec proc proc FinA PreAct erl_act VACCS_ExtAction
            Φᴠᴀᴄᴄꜱ 𝝳ᴠᴀᴄᴄꜱ _ _ _ VACCS_gLtsEq _ AbsVACCS t β β'); eassumption.
Qed.
Next Obligation.
  intros p β β' _ _ heq hmem. unfold 𝝳ᴠᴀᴄᴄꜱ in heq. by rewrite <- heq.
Qed.

(** [FinitaryPreActActionForFW] is a closed term mentioning the [Admitted]
    instance, so it is replaced too; its two obligations are the ones of
    [DefinitionAS.v], which are proved. *)

#[global] Program Instance Erl_FinitaryAbsAction_FW :
  @FinitaryAbsAction (sys * MO erl_act) proc FinA PreAct erl_act VACCS_ExtAction
    Φᴠᴀᴄᴄꜱ 𝝳ᴠᴀᴄᴄꜱ _ _ _ VACCS_gLtsEq _ _ _ :=
  {| FinitaryAbsAction_Abs := Erl_AbsAction_FW ;
     coR_abs p := coR_abs p.1
                  ∪ dom (gmultiset_map (fun x => 𝝳ᴠᴀᴄᴄꜱ (Φᴠᴀᴄᴄꜱ (co x)))
                           (MO_without_not_nb p.2)) |}.
Next Obligation.
  intros p pre_mu hmem. destruct p as (p, m). simpl in *.
  apply elem_of_union in hmem. destruct hmem as [in_p | in_M].
  + change (pre_mu ∈ coR_abs p) in in_p. eapply coR_abs_spec1 in in_p.
    destruct in_p as (mu & mem & eq). subst.
    exists mu. split.
    - destruct mem as (mu2 & tr & duo & b).
      eapply lts_refuses_spec1 in tr as (p2 & tr).
      exists mu2. repeat split; eauto.
      eapply lts_refuses_spec2. exists (p2 ▷ m).
      eapply ParLeft. exact tr.
    - eauto.
  + simpl in *. eapply gmultiset_elem_of_dom, elem_of_gmultiset_map in in_M.
    destruct in_M as (mu & eq & mem).
    exists (co mu). split; eauto.
    exists mu. repeat split; eauto.
    - eapply lts_refuses_spec2.
      assert (mu ∈ MO_without_not_nb m) as mem2; eauto.
      apply (lts_MO_nb_with_nb_spec1 mu m) in mem as (nb & mem).
      exists (p, m ∖ {[+ mu +]}).
      eapply ParRight.
      assert (m = {[+ mu +]} ⊎ (m ∖ {[+ mu +]})) as eqm by multiset_solver.
      rewrite eqm at 1.
      eapply lts_multiset_minus. exact nb.
    - exact (proj2_sig (exists_dual mu)).
    - apply (lts_MO_nb_with_nb_spec1 mu m) in mem as (nb & mem).
      eapply dual_blocks; eauto. symmetry. exact (proj2_sig (exists_dual mu)).
Qed.
Next Obligation.
  intros pre_mu p hmem. destruct hmem as (mu & mem & eq). subst.
  destruct p as (p, m). destruct mem as (mu2 & tr & duo & b).
  eapply lts_refuses_spec1 in tr as ((p2 , m2) & eq).
  inversion eq; subst; simpl in *.
  + eapply elem_of_union. left.
    change (𝝳ᴠᴀᴄᴄꜱ (Φᴠᴀᴄᴄꜱ mu) ∈ coR_abs p). eapply coR_abs_spec2.
    exists mu. repeat split; eauto. exists mu2. repeat split; eauto.
    eapply lts_refuses_spec2. eauto.
  + eapply elem_of_union. right.
    eapply gmultiset_elem_of_dom, elem_of_gmultiset_map.
    destruct (decide (non_blocking mu2)) as [nb2 | b2].
    - exists mu2. split; eauto.
      * assert (mu = co mu2) as ->; [| eauto]. eapply VACCS_UniqueDual; eauto.
      * eapply non_blocking_action_in_ms in l; eauto. subst.
        apply (lts_MO_nb_with_nb_spec2 mu2 _ nb2). multiset_solver.
    - assert (blocking mu2) as Imp; eauto.
      eapply blocking_action_in_ms in Imp as (mem2 & duo2 & nb2); eauto.
      eapply VACCS_UniqueDual in duo; eauto. subst. contradiction.
Qed.

(** ** The characterisations *)

Notation "p ᴇʀʟ⊑ₘᵤₛₜᵢ q" := (p ⊑ₘᵤₛₜᵢ q) (at level 70).

(** The must preorder on Erlang systems, tested by asynchronous observers, is
    the inclusion of co-acceptance sets. *)
Corollary must_iff_co_acceptance_set_Erlang (S T : sys) :
  S ᴇʀʟ⊑ₘᵤₛₜᵢ T ↔ (S ▷ ∅) ≼꜀ₒ₋ₐₛ (T ▷ ∅).
Proof. now rewrite equivalence_acc_set_and_must_i_co_trace. Qed.

(** The same, on traces rather than co-traces. *)
Corollary must_iff_acceptance_set_Erlang (S T : sys) :
  S ᴇʀʟ⊑ₘᵤₛₜᵢ T ↔ (S ▷ ∅) ≼ₐₛ (T ▷ ∅).
Proof. now rewrite equivalence_acc_set_and_must_i. Qed.

End Erlang_Must_Characterization.
