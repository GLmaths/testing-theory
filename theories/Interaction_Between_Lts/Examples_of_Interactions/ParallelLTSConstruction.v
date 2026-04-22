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
From Must Require Import gLts InteractionBetweenLts.

(**************************************** Parallel LTS of two LTS *************************************)

#[global] Program Instance parallel_gLts {P1 P2}
 `{Prop_of_Inter P1 P2 A dual} : gLts (P1 * P2) H := inter_lts dual.

Definition reverse_dual `{H : !ExtAction A} μ1 μ2 := dual μ2 μ1.

#[global] Program Instance Inter_rev_parallel `{Prop_of_Inter P1 P2 A dual} : Prop_of_Inter P2 P1 A reverse_dual.
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
 `{Prop_of_Inter P1 P2 A dual} : gLts (P2 * P1) H := inter_lts reverse_dual.