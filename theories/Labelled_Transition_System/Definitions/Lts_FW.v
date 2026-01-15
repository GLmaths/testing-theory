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
From Must Require Import gLts Bisimulation Lts_OBA.

Class gLtsObaFW (P A : Type) `{gLtsOba P A} :=
  MkgLtsObaFW {
      lts_oba_fw_forward p1 η β :
      ∃ p2, non_blocking η -> dual β η
        -> p1 ⟶[ β ] p2 /\ p2 ⟶[ η ] p1 ;
      lts_oba_fw_feedback {p1 p2 p3 η β } :
      non_blocking η -> dual β η -> p1 ⟶[ η ] p2 -> p2 ⟶[ β ] p3 
        -> p1 ⟶⋍ p3 \/ p1 ⋍ p3 ;
    }.

(* Properties on OBA FW *)

Lemma lts_ht_input_ex `{gLtsObaFW P A} (p : P) :
  ∀ η, non_blocking η → ∃ β, exists p', p ⟶[ β ] p'.
Proof.
  intro η. intro nb.
  destruct (exists_dual η) as (β & duo). symmetry in duo.
  eapply unique_nb in duo as eq; eauto; subst.
  edestruct (lts_oba_fw_forward  p (co β)) as (t & l1 & l2); eauto.
Qed.