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

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From Stdlib Require Import Lia.
From stdpp Require Import base countable decidable gmultiset.
From TestingTheory Require Import ActTau gLts Bisimulation Lts_OBA Lts_FW
    InputOutputActions WeakTransitions VACCS VACCS_Instance NormalForm Normalisation.

(** * Examples of normalisation in VACCS

    We instantiate VACCS over natural channels and natural values, and we
    normalise a few traces.  We write [out c v] for the emission of the value
    [v] on the channel [c] and [inp c v] for its reception.

    In VACCS the outputs are the non-blocking actions and every input has a
    non-blocking co-action, so only two of the three classes occur: [CNB] for
    the outputs and [CIN] for the inputs.  A normalised trace is therefore a
    list of alternating multisets of inputs and multisets of outputs, which is
    exactly the shape [(I_0,M_0),(I_1,M_1),...] of the original work. *)

#[local] Instance NatVP : VACCS_Parameters :=
  {| Channel := nat ; Value := nat ; O := 0 |}.

Definition out (c v : nat) : ExtAct TypeOfActions := ActOut (cst c, cst v).
Definition inp (c v : nat) : ExtAct TypeOfActions := ActIn  (cst c, cst v).

(** ** The classes of the VACCS actions *)

Example cls_out (c v : nat) : cls_tr (out c v) = CNB.
Proof. reflexivity. Qed.

Example cls_inp (c v : nat) : cls_tr (inp c v) = CIN.
Proof. reflexivity. Qed.

(** No VACCS action is opaque: the third class is empty here. *)
Example vaccs_no_opaque (μ : ExtAct TypeOfActions) : cls_tr μ ≠ COP.
Proof. destruct μ; discriminate. Qed.

(** ** Example 1: the runs are collected into multisets *)

Definition s1 : trace (ExtAct TypeOfActions) :=
  [inp 1 0; inp 2 1; out 3 2; out 4 3; inp 5 4].

Example nform_s1 :
  nform cls_tr s1 =
    [ (CIN, {[+ inp 1 0 +]} ⊎ {[+ inp 2 1 +]})
    ; (CNB, {[+ out 3 2 +]} ⊎ {[+ out 4 3 +]})
    ; (CIN, {[+ inp 5 4 +]}) ].
Proof. reflexivity. Qed.

(** Nothing to simplify here: no output is followed by one of its co-actions. *)
Example fbnf_s1 : fbnf s1 = s1.
Proof. vm_compute. reflexivity. Qed.

(** Inside a run the order is forgotten: permuting the two inputs and the two
    outputs does not change the normal form. *)
Example nform_inside_runs :
  nform cls_tr [inp 1 0; inp 2 1; out 3 2; out 4 3]
  = nform cls_tr [inp 2 1; inp 1 0; out 4 3; out 3 2].
Proof.
  eapply nform_tequiv. eapply te_trans.
  - eapply (te_swap cls_tr [] (inp 1 0) (inp 2 1) [out 3 2; out 4 3]);
      [reflexivity | discriminate].
  - eapply (te_swap cls_tr [inp 2 1; inp 1 0] (out 3 2) (out 4 3) []);
      [reflexivity | discriminate].
Qed.

(** The order *between* the runs is kept. *)
Example nform_between_runs :
  nform cls_tr [inp 1 0; out 2 1] ≠ nform cls_tr [out 2 1; inp 1 0].
Proof. intro h. inversion h. Qed.

(** ** Example 2: a feedback is consumed

    The trace emits [out 1 0] and receives it back, three actions later.  Both
    disappear, and the two runs of outputs that [inp 1 0] separated merge. *)

Definition s2 : trace (ExtAct TypeOfActions) :=
  [out 1 0; inp 2 1; inp 3 2; out 4 3; inp 1 0; out 5 4].

Definition s2' : trace (ExtAct TypeOfActions) :=
  [inp 2 1; inp 3 2; out 4 3; out 5 4].

Example s2_feedback : s2 ⊑ₜ s2'.
Proof.
  eapply (trace_leq_feedback_mid [] [inp 2 1; inp 3 2; out 4 3] [out 5 4]
            (out 1 0) (inp 1 0)).
  - exists (cst 1, cst 0). reflexivity.
  - reflexivity.
Qed.

(** The simplification function computes it too. *)
Example fbnf_s2 : fbnf s2 = s2'.
Proof. vm_compute. reflexivity. Qed.

Example nform_s2' :
  nform cls_tr s2' =
    [ (CIN, {[+ inp 2 1 +]} ⊎ {[+ inp 3 2 +]})
    ; (CNB, {[+ out 4 3 +]} ⊎ {[+ out 5 4 +]}) ].
Proof. reflexivity. Qed.

(** The normal form of [s2] -- feedbacks consumed, then runs collected. *)
Example fnf_s2 : fnf s2 = nform cls_tr s2'.
Proof. reflexivity. Qed.

(** For comparison, the normal form of [s2] *before* simplification still has
    five blocks. *)
Example nform_s2 :
  nform cls_tr s2 =
    [ (CNB, {[+ out 1 0 +]})
    ; (CIN, {[+ inp 2 1 +]} ⊎ {[+ inp 3 2 +]})
    ; (CNB, {[+ out 4 3 +]})
    ; (CIN, {[+ inp 1 0 +]})
    ; (CNB, {[+ out 5 4 +]}) ].
Proof. reflexivity. Qed.

(** ** Example 3: two nested feedbacks cancel the whole trace *)

Definition s3 : trace (ExtAct TypeOfActions) :=
  [out 1 0; out 2 1; inp 2 1; inp 1 0].

Example s3_feedback : s3 ⊑ₜ [].
Proof.
  eapply tl_trans.
  - eapply (trace_leq_feedback_mid [] [out 2 1; inp 2 1] [] (out 1 0) (inp 1 0)).
    + exists (cst 1, cst 0). reflexivity.
    + reflexivity.
  - eapply (trace_leq_feedback_mid [] [] [] (out 2 1) (inp 2 1)).
    + exists (cst 2, cst 1). reflexivity.
    + reflexivity.
Qed.

Example fbnf_s3 : fbnf s3 = [].
Proof. vm_compute. reflexivity. Qed.

(** ** Example 4: an input before its output is not a feedback

    Nothing can be simplified in [inp 1 0; out 1 0]: the emission comes after
    the reception, so the two do not cancel. *)

Definition s4 : trace (ExtAct TypeOfActions) := [inp 1 0; out 1 0].

Example fbnf_s4 : fbnf s4 = s4.
Proof. vm_compute. reflexivity. Qed.

Example s4_minimal : trace_min s4.
Proof. eapply trace_min_of_measure. reflexivity. Qed.

Example s4_no_feedback (s1 s2 s3 : trace (ExtAct TypeOfActions)) (η μ : ExtAct TypeOfActions) :
  s4 = s1 ++ η :: (s2 ++ μ :: s3) -> non_blocking η -> dual μ η -> False.
Proof.
  intros heq nb d.
  assert (hle : s4 ⊑ₜ s1 ++ s2 ++ s3)
    by (rewrite heq; eapply trace_leq_feedback_mid; assumption).
  pose proof (trace_leq_length s4 (s1 ++ s2 ++ s3) hle eq_refl) as hl.
  rewrite heq in hl.
  rewrite !length_app' in hl. simpl in hl.
  rewrite !length_app' in hl. simpl in hl. lia.
Qed.

(** ** What this means for a process

    In any forwarder LTS over the VACCS actions -- in particular the forwarder
    lifting of VACCS itself -- a process that can perform [s2] can perform the
    simplified trace [s2'] and reach the very same state, up to the
    bisimulation. *)

Section OnAnyForwarderLts.

  Context `{@gLtsOba P (ExtAct TypeOfActions) VACCS_ExtAction gLtsEqP}.
  Context `{!gLtsObaFW P (ExtAct TypeOfActions)}.

  Example s2_feedback_lts (p q : P) : p ⟹[s2] q -> p ⟹⋍[s2'] q.
  Proof. intro w. eapply wt_trace_leq; [eapply s2_feedback | exact w]. Qed.

End OnAnyForwarderLts.
