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

From stdpp Require Import gmap.

Lemma lem_dec `{Countable A} (X Y Z : gset A) :
    X ⊆ Y ∪ Z
      -> exists Y' Z', Y' ⊆ Y /\ Z' ⊆ Z /\ (Y' ∪ Z' ≡ X)%stdpp.
Proof.
  induction X using set_ind_L; intros sub.
  - exists ∅, ∅. set_solver.
  - assert (sub0 : X ⊆ Y ∪ Z) by set_solver.
    destruct (IHX sub0) as (Y0 & Z0 & sub1 & sub2 & eq).
    assert (mem_dec : x ∈ Y \/ x ∈ Z). set_solver.
    destruct mem_dec.
    + exists ({[x]} ∪ Y0), Z0. set_solver.
    + exists Y0, ({[x]} ∪ Z0). set_solver.
Qed.