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

(** * Core Erlang: the forwarder [toFW (Erlang)]

    What is left for [toFW] and for the co-trace characterisation: the
    co-finite-image condition and the interaction between a forwarder and a
    test. *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list numbers finite sets gmap gmultiset.
From TestingTheory Require Import ActTau InputOutputActions InListPropHelper
  gLts Bisimulation Lts_OBA Lts_OBA_FB Lts_FW Lts_Finite_Output_Chain
  FiniteImageLTS coFiniteImage
  InteractionBetweenLts MultisetLTSConstruction ForwarderConstruction
  Erlang_Syntax Erlang_LTS Erlang_Instance.

(** ** A finite image is a co-finite image

    Generic: with a unique dual, [∃ α', dual α' α ∧ p ⟶[α'] q] is [p ⟶[co α] q],
    so [coFiniteImagegLts] follows from [FiniteImagegLts].  This belongs in
    [coFiniteImage.v]; it is kept here so that no file of the framework has to
    change.  It is not declared as an instance, to keep instance search
    predictable. *)

Lemma dual_image_iff `{gLts P A} {unique_nb : UniqueDual A} (p q : P) α :
  (∃ α', dual α' α ∧ p ⟶[α'] q) ↔ p ⟶[co α] q.
Proof.
  split.
  - intros (α' & hd & hl). assert (α' = co α) as ->; [| done].
    apply unique_nb. by symmetry.
  - intros hl. exists (co α). split; [| done].
    symmetry. exact (proj2_sig (exists_dual α)).
Qed.

Definition coFiniteImage_from_FiniteImage `{FiniteImagegLts P A}
  {unique_nb : UniqueDual A} : coFiniteImagegLts P A.
Proof.
  unshelve refine {|
    cofolts_states_countable := folts_states_countable;
    cofolts_tau_next_states_finite := _;
    cofolts_next_states_decidable := _;
    cofolts_next_states_finite := _;
  |}.
  - intros p α q. destruct (decide (p ⟶[co α] q)) as [h | h].
    + left. by apply dual_image_iff.
    + right. intros hc. apply h. by apply dual_image_iff.
  - intros p α. unfold dsig.
    eapply (in_list_finite (map proj1_sig (enum (dsig (fun q => p ⟶[co α] q))))).
    intros q hq%bool_decide_unpack.
    apply list_elem_of_fmap. apply dual_image_iff in hq.
    exists (dexist q hq). split; [reflexivity | eapply elem_of_enum].
Defined.

Section Erlang_Forwarder.

Context `{EP : Erlang_Program}.

#[global] Instance Erl_coFiniteImage : coFiniteImagegLts sys erl_act :=
  coFiniteImage_from_FiniteImage.

(** ** Interaction between a forwarder and a test *)

#[global] Program Instance Erl_Inter_FW :
  Prop_of_Inter (sys * MO erl_act) sys erl_act dual :=
  {| lts_essential_actions_left p := dom (erl_mo p.1) ∪ dom (MO_without_not_nb p.2) ;
     lts_essential_actions_right S := dom (erl_mo S) |}.
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
Next Obligation. intros S ξ hin. by apply erl_out_of_dom. Defined.
Next Obligation.
  intros (S1, m1) μ1 (S1', m1') S2 μ2 S2' hl1 hl2 hinter. simpl in *.
  destruct μ2 as [a | a].
  - left. symmetry in hinter. apply simplify_match_input in hinter as ->.
    inversion hl1; subst.
    + apply elem_of_union. left.
      apply erl_out_shape in l as (p & v & -> & ->). apply erl_out_dom. multiset_solver.
    + apply elem_of_union. right.
      assert (non_blocking (ActOut a)) as nb by (by exists a).
      eapply non_blocking_action_in_ms in l; eauto.
      (* [nb] is passed explicitly: it fixes the [ExtAction] instance, without
         which the unifier will not see through its [eqdec] projection. *)
      apply gmultiset_elem_of_dom.
      apply (lts_MO_nb_with_nb_spec2 (ActOut a) _ nb). multiset_solver.
  - right. symmetry in hinter. apply simplify_match_output in hinter as ->.
    apply erl_out_shape in hl2 as (p & v & -> & ->). apply erl_out_dom. multiset_solver.
Defined.
Next Obligation.
  intros ξ p. destruct ξ as [a | a]; [exact empty | exact {[ ActIn a ]}].
Defined.
Next Obligation.
  intros (S1, m1) (S1', m1') ξ μ S2 hmem hl hinter. simpl in *.
  unfold Erl_Inter_FW_obligation_4.
  destruct ξ as [a | a].
  - exfalso. apply erl_dom_out in hmem as (p' & v' & heq & _). discriminate heq.
  - symmetry in hinter. apply simplify_match_output in hinter as ->. set_solver.
Defined.
Next Obligation.
  intros ξ S. destruct ξ as [a | a]; [exact {[ ActOut a ]} | exact {[ ActIn a ]}].
Defined.
Next Obligation.
  intros S2 S2' ξ μ (S1, m1) hmem hl hinter. simpl in *.
  unfold Erl_Inter_FW_obligation_6.
  destruct ξ as [a | a].
  - apply simplify_match_input in hinter as ->. set_solver.
  - apply simplify_match_output in hinter as ->. set_solver.
Defined.

End Erlang_Forwarder.
