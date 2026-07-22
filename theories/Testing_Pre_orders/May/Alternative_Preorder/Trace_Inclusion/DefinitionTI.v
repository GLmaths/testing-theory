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

From Stdlib.Lists Require Import List.
From stdpp Require Import decidable.
From TestingTheory Require Import ActTau gLts Bisimulation WeakTransitions Testing_Predicate InteractionBetweenLts May.

(** * Alternative preorder for May based on trace inclusion *)

(** ** Traces of a process

    [s] is a trace of [p] whenever [p] can weakly perform [s]. *)

Definition traces `{gLts P A} (p : P) (s : trace A) : Prop := ∃ p', p ⟹[s] p'.

Global Hint Unfold traces : mdb.

(** ** Definition of the alternative preorder: trace inclusion *)

Definition bhv_pre_ti `{gLtsP : @gLts P A H, gLtsQ : !gLts Q H} (p : P) (q : Q) :=
  ∀ (s : trace A), traces p s -> traces q s.

Global Hint Unfold bhv_pre_ti : mdb.

Notation "p ≼ₜᵢ q" := (bhv_pre_ti p q) (at level 70).
Notation "p ⋠ₜᵢ q" := (¬ bhv_pre_ti p q) (at level 70).

(** ** [≼ₜᵢ] is a preorder *)

#[global] Instance bhv_pre_ti_refl `{gLtsP : @gLts P A H} : Reflexive bhv_pre_ti.
Proof. intros p s hs. exact hs. Qed.

#[global] Instance bhv_pre_ti_transitive `{gLtsP : @gLts P A H} : Transitive bhv_pre_ti.
Proof. intros p q r hpq hqr s hs. eapply hqr, hpq, hs. Qed.

#[global] Instance bhv_pre_ti_preorder `{gLtsP : @gLts P A H} : PreOrder bhv_pre_ti.
Proof. split; [exact bhv_pre_ti_refl | exact bhv_pre_ti_transitive]. Qed.

(** * Characterisation of [may] in terms of traces

    The bridge between the contextual predicate [may] and traces: [p may_pass t]
    holds exactly when the server and the client synchronise along some trace [s]
    (the client following the co-trace [coₜ s]) and the client reaches a
    successful state.

    This is the only place where the operational content of [may] is unfolded;
    both soundness and completeness of [≼ₜᵢ] rest on it. *)

Section May_and_traces.

Context `{gLtsP : @gLts P A H}.
Context `{gLtsT : !gLtsEq T H, !Testing_Predicate outcome gLtsT}.
(* non-generalising binder: the [gLts] instances must be [gLtsP] and [gLtsT],
   not freshly generalised ones *)
Context {PInter : Prop_of_Inter P T A dual}.

(** [may_wt_nil_server]/[may_wt_tau_server]/[may_wt_nil_client]/
    [may_wt_tau_client] — "[may] is preserved backwards along
    τ-transitions of the server/client" — now live in [May.v], shared
    with [DefinitionTIco.v]. *)

(** ** From a successful computation to a synchronising trace *)

Lemma may_to_wt (p : P) (t : T) :
  p may_pass t ->
  ∃ (s : trace A) (p' : P) (t' : T), p ⟹[s] p' /\ t ⟹[coₜ s] t' /\ outcome t'.
Proof.
  intro hm.
  induction hm as [ p t happy
                  | p t p' nh pt hm IH
                  | p t t' nh et hm IH
                  | p t p' μ1 t' μ2 nh inter trS trC hm IH ].
  - (* the client is already successful: the empty trace works *)
    exists ([] : trace A), p, t. repeat split; eauto with mdb.
  - (* τ-step of the server: prepend it to the server run *)
    destruct IH as (s & p'' & t'' & wS & wC & happy).
    exists s, p'', t''. repeat split; eauto with mdb.
  - (* τ-step of the client: prepend it to the client run *)
    destruct IH as (s & p'' & t'' & wS & wC & happy).
    exists s, p'', t''. repeat split; eauto with mdb.
  - (* synchronisation: [μ2] is the dual of [μ1], so the client follows the co-trace *)
    destruct IH as (s & p'' & t'' & wS & wC & happy).
    assert (μ2 = co μ1) as -> by (eapply unique_nb; eauto).
    exists (μ1 :: s), p'', t''. repeat split.
    + eapply wt_act; eauto.
    + simpl. eapply wt_act; eauto.
    + assumption.
Qed.

(** ** From a synchronising trace to a successful computation *)

Lemma wt_to_may (s : trace A) (p p' : P) (t t' : T) :
  p ⟹[s] p' -> t ⟹[coₜ s] t' -> outcome t' -> p may_pass t.
Proof.
  intro wS. revert t t'.
  induction wS as [ p | s p q r l wS IH | μ s p q r l wS IH ]; intros t1 t2 wC happy.
  - (* empty trace: the client reaches success on its own *)
    eapply may_wt_tau_client; [exact wC |]. now apply may_now.
  - (* τ-step of the server *)
    destruct (decide (outcome t1)) as [happy1 | nh1].
    + now apply may_now.
    + eapply may_server_step; eauto.
  - (* the client must answer [μ] with its dual [co μ] *)
    simpl in wC.
    eapply wt_pop in wC as (u & wC1 & wC2).
    eapply wt_decomp_one in wC1 as (t3 & t4 & w13 & tr34 & w4u).
    (* first let the client silently reach the state [t3] that fires [co μ] *)
    eapply may_wt_tau_client; [exact w13 |].
    assert (q may_pass t4) as hmq.
    { eapply may_wt_tau_client; [exact w4u |]. eapply IH; eauto. }
    destruct (decide (outcome t3)) as [happy3 | nh3].
    + now apply may_now.
    + eapply may_com_step; eauto.
      exact (proj2_sig (exists_dual μ)).
Qed.

(** ** The characterisation *)

Lemma may_iff_wt (p : P) (t : T) :
  p may_pass t <->
  ∃ (s : trace A) (p' : P) (t' : T), p ⟹[s] p' /\ t ⟹[coₜ s] t' /\ outcome t'.
Proof.
  split.
  - eapply may_to_wt.
  - intros (s & p' & t' & wS & wC & happy). eapply wt_to_may; eauto.
Qed.

End May_and_traces.
