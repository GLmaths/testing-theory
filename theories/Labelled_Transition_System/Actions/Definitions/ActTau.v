(* begin hide *)
(*
   Copyright (c) 2026 Nomadic Labs
   Copyright (c) 2026 Paul Laforgue <paul.laforgue@nomadic-labs.com>
   Copyright (c) 2026 Léo Stefanesco <leo.stefanesco@mpi-sws.org>
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

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import decidable countable.

(* * Actions and traces *)
(********** Actions := External Action ⊎ { τ } **********)

Inductive Act (A: Type) :=
  (* External Action *)
  | ActExt (μ: A)
  (* Silent Action / Computation Action / Reduction Action *)
  | τ 
 .

Arguments ActExt {_} _.
Arguments τ {_}.

(****************** Trace Definition ********************)
Definition trace A := list A.
(* Empty Trace *)
Definition ε {A : Type} := [] : list A. 

(***************** EqDecision for Act *******************)
#[global] Instance act_eqdec `{EqDecision A} : EqDecision (Act A).
Proof. solve_decision. Defined.

Class ExtAction (A : Type) :=
  MkExtAction {
      eqdec: EqDecision A;
      countable: Countable A;
      non_blocking : A → Prop;
      non_blocking_dec a : Decision (non_blocking a);
      dual : A → A → Prop;
      dual_dec a b: Decision (dual a b);

      (* Co-action of a non-blocking action is blocking, otherwise infinite non-blocking action sequence in FW *)
      dual_blocks β η :
      non_blocking η → dual β η → 
        ¬ non_blocking β ;

      (* dual is symmetric *)
      duo_sym : Symmetric dual;

      (* Constructive way to build a dual action *)
      exists_dual μ : { η | dual μ η};

      (* Unique dual *)
      (* unique_nb η β: dual β η → η = proj1_sig (exists_dual β); *)

      (* Handy hypothesis *)
      (* nb_not_nb η1 η2 ɣ : non_blocking η1 → dual η1 ɣ → dual η2 ɣ → non_blocking η2; *)
    }.
#[global] Existing Instance eqdec.
#[global] Existing Instance countable.
#[global] Existing Instance non_blocking_dec.
#[global] Existing Instance dual_dec.
#[global] Existing Instance duo_sym.

(* Definition of blocking action *)
Notation "'blocking' β" := (¬ non_blocking β) (at level 30).

(* Definition of the co-action *)
Notation "'co' μ" := (proj1_sig (exists_dual μ)) (at level 30).

(*Definition of the co-trace *)
Notation "'coₜ' s" := (map (fun μ => (proj1_sig (exists_dual μ))) s) (at level 30).

(* Uniqueness of the dual, no longer a field of [ExtAction]. It is taken as a
   hypothesis [{unique_nb : UniqueDual A}] where it is still needed; the goal
   is to remove these hypotheses one by one. *)
Definition UniqueDual (A : Type) `{ExtAction A} :=
  forall η β, dual β η → η = proj1_sig (exists_dual β).
Existing Class UniqueDual.
(* end hide *)
