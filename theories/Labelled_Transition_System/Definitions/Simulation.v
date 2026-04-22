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

From stdpp Require Import base countable strings sets gmap.

From TestingTheory Require Import gLts Bisimulation Termination Lts_OBA MultisetHelper ActTau.

(** ** Similarity *)
CoInductive similar `{@gLts A L H} `{@gLts B L H}  (a : A) (b : B) : Prop :=
| smi_step : (forall (α : Act L) a', a ⟶{α} a' -> exists b', b ⟶{α} b' /\ similar a' b') -> similar a b.
Infix "≲" := (similar) (at level 20).


Section Similarity.

(** *** Similarity preserves termination *)
Lemma similar_terminate `{@gLts A L H} `{@gLts B L H} (a : A) (b : B) :
  b ≲ a -> a ⤓ -> b ⤓.
Proof.
intros Hs Ht. revert b Hs. induction Ht as [a Ht Hi].
constructor. intros q Hq. destruct Hs as [Hs].
destruct (Hs τ q Hq) as (a' & Ha' & Hs').
eapply Hi; eassumption.
Qed.

End Similarity.

Section TerminateWith.

Context `{gLts A L}.

(* Generalisation of termination where each tau-accessible external action
  must satisfy some property *)
Reserved Notation "p ⤓_ Q " (at level 50).
Inductive terminate_with (Q : L -> Prop) (p : A) : Prop :=
    twstep : (forall μ q, p ⟶[μ] q -> Q μ) ->
             (forall q : A, p ⟶ q -> q ⤓_ Q) -> p ⤓_ Q
where "p ⤓_ Q" := (terminate_with Q p).

(* Termination is termination_with the trivial property on external actions *)
Lemma terminate_with_True p : p ⤓ -> p ⤓_ (fun _ => True).
Proof. intro Ht; induction Ht; constructor; auto. Qed.

Lemma terminate_with_terminate Q p : p ⤓_ Q -> p ⤓.
Proof. intro Ht; induction Ht; constructor; auto. Qed.

Notation "p '⤓_' Q" := (terminate_with Q p).

End TerminateWith.

From TestingTheory Require Import InteractionBetweenLts ParallelLTSConstruction.

Section ParallelTermination.

Context `{gLtsP : @gLts P A H}.
Context `{gLtsQ : @gLts Q A H}.
Context `{!Prop_of_Inter P Q A dual}.

Local Instance gLtsPQ : gLts (P * Q) H := parallel_gLts.

(* The parallel composition of two states that may never interact *)
Lemma parallel_termination_with R S (p : P) (q : Q) :
  (forall μ μ', R μ -> S μ' -> ¬ (dual μ μ')) ->
  terminate_with R p ->
  terminate_with S q ->
    terminate (p, q).
Proof.
intros Hm Hp Hq. revert q Hq.
induction Hp as [p He Ht Hi]. intros q Hq.
induction Hq as [q He' Ht' Hi'].
constructor.
intros (r & s) Hrs. lts_inversion idtac.
- now apply Hi.
- now apply Hi'. (* right tau *)
- (* communication is impossible *)
  exfalso; eapply Hm.
  + eapply He. eassumption.
  + eapply He'. eassumption.
  + trivial.
Qed.

End ParallelTermination.
