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
From TestingTheory Require Import ActTau gLts Bisimulation WeakTransitions coWeakTransition
    Testing_Predicate InteractionBetweenLts May.

(** * Alternative preorder for May based on co-trace inclusion

    Mirrors [DefinitionTI.v], mechanically replacing the plain weak
    transition [⟹[s]] by the co-weak-transition [⟹ᶜᵒ[s]] on the
    *process* side — the same substitution used to go from
    [DefinitionAS.v] to [DefinitionASco.v]. The duality lives on the
    process being compared (the "co" is not on the test/client side:
    it is the process that answers a trace with duals), never on the
    test [t]: [t] always performs its half of the computation
    literally. Unlike [DefinitionTI.v]'s [may_iff_wt] (which relies on
    the canonical dual [coₜ]/[unique_nb]), this file never picks a
    canonical dual witness: [cowt]'s own constructors only need *some*
    witness satisfying [dual], recovered directly from
    [may_com_step]'s own [inter] field. *)

(** ** Co-traces of a process

    [s] is a co-trace of [p] whenever [p] can weakly answer [s] with
    duals at each step. *)

Definition traces_co `{gLts P A} (p : P) (s : trace A) : Prop := ∃ p', p ⟹ᶜᵒ[s] p'.

Global Hint Unfold traces_co : mdb.

(** ** Definition of the alternative preorder: co-trace inclusion *)

Definition bhv_pre_ti_co `{gLtsP : @gLts P A H, gLtsQ : !gLts Q H} (p : P) (q : Q) :=
  ∀ (s : trace A), traces_co p s -> traces_co q s.

Global Hint Unfold bhv_pre_ti_co : mdb.

Notation "p ≼꜀ₒ₋ₜᵢ q" := (bhv_pre_ti_co p q) (at level 70).
Notation "p ⋠꜀ₒ₋ₜᵢ q" := (¬ bhv_pre_ti_co p q) (at level 70).

(** ** [≼꜀ₒ₋ₜᵢ] is a preorder *)

#[global] Instance bhv_pre_ti_co_refl `{gLtsP : @gLts P A H} : Reflexive bhv_pre_ti_co.
Proof. intros p s hs. exact hs. Qed.

#[global] Instance bhv_pre_ti_co_transitive `{gLtsP : @gLts P A H} : Transitive bhv_pre_ti_co.
Proof. intros p q r hpq hqr s hs. eapply hqr, hpq, hs. Qed.

#[global] Instance bhv_pre_ti_co_preorder `{gLtsP : @gLts P A H} : PreOrder bhv_pre_ti_co.
Proof. split; [exact bhv_pre_ti_co_refl | exact bhv_pre_ti_co_transitive]. Qed.

(** * Characterisation of [may] in terms of co-traces

    The bridge between the contextual predicate [may] and co-traces:
    [p may_pass t] holds exactly when the process answers some trace
    [s] with duals (co-weakly) and the client performs that very
    trace [s] literally, reaching a successful state. *)

Section May_and_cotraces.

Context `{gLtsP : @gLts P A H}.
Context `{gLtsT : !gLtsEq T H, !Testing_Predicate outcome gLtsT}.
(* non-generalising binder: the [gLts] instances must be [gLtsP] and [gLtsT],
   not freshly generalised ones *)
Context {PInter : Prop_of_Inter P T A dual}.

(** [may_wt_nil_server_co]/[may_wt_tau_server_co] (the co-trace
    analogues, for the *process* side — [DefinitionTIco.v] puts the
    duality there, never on the test/client) and the plain
    [may_wt_nil_client]/[may_wt_tau_client] (the client never carries
    duality here, so these are unchanged) all live in [May.v], shared
    with [DefinitionTI.v]. *)

(** ** From a successful computation to a synchronising co-trace *)

Lemma may_to_wt_co (p : P) (t : T) :
  p may_pass t ->
  ∃ (s : trace A) (p' : P) (t' : T), p ⟹ᶜᵒ[s] p' /\ t ⟹[s] t' /\ outcome t'.
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
  - (* synchronisation: [μ1] is a dual of [μ2], so the server co-answers [μ2] *)
    destruct IH as (s & p'' & t'' & wS & wC & happy).
    exists (μ2 :: s), p'', t''. repeat split.
    + simpl. eapply cowt_act; [exact inter | exact trS | exact wS].
    + eapply wt_act; eauto.
    + assumption.
Qed.

(** ** From a synchronising co-trace to a successful computation *)

Lemma wt_to_may_co (s : trace A) (p p' : P) (t t' : T) :
  p ⟹ᶜᵒ[s] p' -> t ⟹[s] t' -> outcome t' -> p may_pass t.
Proof.
  intro wS. revert t t'.
  induction wS as [ p | s p q r l wS IH | μ μ' s p q r duo l wS IH ]; intros t1 t2 wC happy.
  - (* empty trace: the client reaches success on its own *)
    eapply may_wt_tau_client; [exact wC |]. now apply may_now.
  - (* τ-step of the server *)
    destruct (decide (outcome t1)) as [happy1 | nh1].
    + now apply may_now.
    + eapply may_server_step; eauto.
  - (* the server answers [μ] with some dual [μ'], recovered from [cowt] directly *)
    eapply wt_pop in wC as (u & wC1 & wC2).
    eapply wt_decomp_one in wC1 as (t3 & t4 & w13 & tr34 & w4u).
    eapply may_wt_tau_client; [exact w13 |].
    assert (q may_pass t4) as hmq.
    { eapply may_wt_tau_client; [exact w4u |]. eapply IH; eauto. }
    destruct (decide (outcome t3)) as [happy3 | nh3].
    + now apply may_now.
    + eapply (may_com_step p t3 q μ' t4 μ); eauto.
Qed.

(** ** The characterisation *)

Lemma may_iff_wt_co (p : P) (t : T) :
  p may_pass t <->
  ∃ (s : trace A) (p' : P) (t' : T), p ⟹ᶜᵒ[s] p' /\ t ⟹[s] t' /\ outcome t'.
Proof.
  split.
  - eapply may_to_wt_co.
  - intros (s & p' & t' & wS & wC & happy). eapply wt_to_may_co; eauto.
Qed.

End May_and_cotraces.
