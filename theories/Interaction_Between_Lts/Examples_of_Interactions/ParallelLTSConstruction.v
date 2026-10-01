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
From stdpp Require Import base.
From TestingTheory Require Import ActTau gLts FiniteImageLTS InteractionBetweenLts StateTransitionSystems.

(** ** Parallel composition of two LTSs *)

#[global] Program Instance parallel_gLts {P1 P2}
 {A : Type} {H : ExtAction A} {H0 : gLts P1 H} {H1 : gLts P2 H} `{H2 : !@Prop_of_Inter P1 P2 A A dual H H0 H H1} : gLts (P1 * P2) H := inter_lts dual.

Definition reverse_dual `{H : !ExtAction A} μ1 μ2 := dual μ2 μ1.

#[global] Program Instance Inter_rev_parallel {P1 P2} {A : Type} {H : ExtAction A} {H0 : gLts P1 H} {H1 : gLts P2 H} `{H2 : !@Prop_of_Inter P1 P2 A A dual H H0 H H1} : Prop_of_Inter P2 P1 A A reverse_dual.
Next Obligation.
  intros. destruct H2. exact (lts_essential_actions_right X).
Defined.
Next Obligation.
  intros. simpl in *. unfold Inter_rev_parallel_obligation_1 in H3.
  destruct H2. simpl in *. eauto.
Defined.
Next Obligation.
  intros. destruct H2. exact (lts_essential_actions_left X).
Defined.
Next Obligation.
  intros. destruct H2; eauto.
Defined.
Next Obligation.
  intros. unfold Inter_rev_parallel_obligation_1.
  unfold Inter_rev_parallel_obligation_3. destruct H2; eauto.
  unfold reverse_dual in H5. eapply lts_essential_actions_spec_interact in H5; eauto.
  destruct H5. right; eauto. left; eauto.
Defined.
Next Obligation.
  intros. destruct H2. exact (lts_co_inter_action_right X X0).
Defined.
Next Obligation.
  intros. unfold Inter_rev_parallel_obligation_6. destruct H2; eauto.
Defined.
Next Obligation.
  intros. destruct H2. exact (lts_co_inter_action_left X X0).
Defined.
Next Obligation.
  intros. unfold Inter_rev_parallel_obligation_8. destruct H2; eauto.
Defined.

 #[global] Program Instance parallel_gLts_inv {P1 P2}
 {A : Type} {H : ExtAction A} {H0 : gLts P1 H} {H1 : gLts P2 H} `{H2 : !@Prop_of_Inter P1 P2 A A dual H H0 H H1} : gLts (P2 * P1) H := inter_lts reverse_dual.

(** ** The computations of [p ∥ t], as a state transition system

    The [Sts] that [must] runs on, in the one-alphabet development.  It is
    found (hint below) before the generic [sts_of_lts], so that
    for [P1 = P2] the search does not pick the reversed composition
    [parallel_gLts_inv] instead; and its step is [inter_step] itself, so that
    [inversion] sees through it as it did through [(p, t) ⟶ t']. *)
Definition parallel_sts {P1 P2} {A : Type} {H : ExtAction A} {H0 : gLts P1 H} {H1 : gLts P2 H} `{H2 : !@Prop_of_Inter P1 P2 A A dual H H0 H H1} : Sts (P1 * P2) :=
  let S0 := sts_of_lts parallel_gLts in
  {| sts_step x y := inter_step x τ y;
     sts_state_eqdec := @sts_state_eqdec _ S0;
     sts_step_decidable := @sts_step_decidable _ S0;
     sts_refuses := @sts_refuses _ S0;
     sts_refuses_decidable := @sts_refuses_decidable _ S0;
     sts_refuses_spec1 := @sts_refuses_spec1 _ S0;
     sts_refuses_spec2 := @sts_refuses_spec2 _ S0 |}.

(* Found by first finding the interaction: the two LTSs of [p ∥ t] are then
   the ones the interaction is stated for (e.g. [gLtsEq_gLts VCCS_gLtsEq]),
   as in the lemmas about [must], and not whatever [gLts] instance a separate
   search would pick (e.g. [VCCS_gLts]). *)
#[global] Hint Extern 1 (Sts (?P1 * ?P2)) =>
  let PI := constr:(_ : Prop_of_Inter P1 P2 _ _ dual) in
  exact (@parallel_sts P1 P2 _ _ _ _ PI) : typeclass_instances.
(** [parallel_sts] is [sts_of_lts parallel_gLts] up to computation, so it is
    countable when the parallel LTS is. *)
#[global] Instance parallel_csts {P1 P2} {A : Type} {H : ExtAction A} {H0 : gLts P1 H} {H1 : gLts P2 H} `{H2 : !@Prop_of_Inter P1 P2 A A dual H H0 H H1}
  (M : CountablegLts (P1 * P2) A) : CountableSts (P1 * P2) | 1 :=
  csts_of_clts M.
