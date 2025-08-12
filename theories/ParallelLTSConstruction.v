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
From stdpp Require Import base.
From Must Require Import gLts InteractionBetweenLts.

(**************************************** Parallel LTS of two LTS *************************************)

Definition parallel_inter `{ExtAction A} μ1 μ2 := dual μ2 μ1 . (* \/ dual μ2 μ1. *)

#[global] Instance parallel_inter_sym `{ExtAction A} : Symmetric parallel_inter.
Proof. intros μ1 μ2. intro Hyp. eapply duo_sym. assumption. Defined.

#[global] Program Instance parallel_gLts {P1 P2 A : Type} `{H : ExtAction A} (M1: gLts P1 A) (M2: gLts P2 A)
  `{Prop_of_Inter P1 P2 A parallel_inter} 
: gLts (P1 * P2) A := inter_lts parallel_inter. 