(*
   Copyright (c) 2026 Gaëtan Lopez <gaetanlopez.maths@gmail.com>

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

(** * Dropping an absorbing input summand

    An input guard whose continuation is itself below [𝟘] may be **removed
    from a sum**:

        must_i_input_drop :
          (∀ v, P^v ⊑ₘᵤₛₜᵢ 𝟘) -> g ((c ? P) + G) ⊑ₘᵤₛₜᵢ g G

    ** Why this rule has to exist

    Nothing in the 25-rule system could derive even the simplest instance,
    [g (c ? 𝟘) ⊑ₘᵤₛₜᵢ g 𝟘] — checked rule by rule: [ax_input] and
    [ax_choice_input] preserve the guard, so they would need
    [⊢ 𝟘 ⊑ (c ! v • 𝟘)], which is **false** (a test can be made to fail by
    an extra pending message: [t := c ? (If x = v Then 𝟘 Else ①)] is passed
    by [𝟘] and failed by [c ! v • 𝟘]); [ax_ccat_l] and [ax_resp] both put a
    guard that *re-emits* on the left; every other rule with a bare input
    guard on the left needs one on the right too.  So this is an eleventh
    correction to the rule set, found the same way as all the others — by
    working backwards from what a derivation must build.

    ** Why it is sound

    A server that only ever swallows a message cannot help a client.  The
    single interesting field is [ex]: the sum's own step may be the
    [c]-synchronisation, which the residue [G] has no counterpart for.  In
    that case the client emitted, so
    [TransitionShapeForOutputSimplified] gives [t ≡* (c ! v • 𝟘) ‖ t'], the
    [com] field gives [P^v must_pass t'], the hypothesis turns it into
    [𝟘 must_pass t'], and that leaves only two possibilities: [t'] is good
    — whence [t] is good, contradicting [nh] — or [t'] has a [τ], which
    lifts through the congruence to a [τ] of [t], and *that* is a step of
    [(g G) ▷ t].  Outputs floating out by structural congruence alone is
    exactly the asynchrony of the calculus, and it is what makes the
    argument work.

    ** What it does NOT cover

    The rule is sound but the family is not yet complete.  With three
    distinct channels one has

        c ? (d ? (c ! x • 𝟘))  ⊑ₘᵤₛₜᵢ  𝟘        (semantically true)

    while its continuation [d ? (c ! v • 𝟘)] is *not* below [𝟘] — checked:
    the client [d ! w • 𝟘 ‖ (c ? ①)] is [τ]-stuck and not good, so [𝟘]
    fails it, yet [d ? (c ! v • 𝟘)] passes it by taking the [d]-message and
    answering on [c].  The premise above is therefore too strong.  The
    exact condition relativises to clients that *refuse* [c ?] — which is
    automatic in the situation the rule is applied in (the client was
    [τ]-stuck *while* holding the [c]-message, so it cannot have offered
    [c ?]), but is not expressible as a plain [⊑ₘᵤₛₜᵢ].  Recorded here so
    the gap is not mistaken for an oversight. *)

From Stdlib Require Import List Lia.
From stdpp Require Import base sets gmap gmultiset.
From TestingTheory Require Import Lts_Finite_Output_Chain.
From TestingTheory Require Import VACCS VACCS_Instance Must ActTau InputOutputActions
  gLts Bisimulation InteractionBetweenLts Testing_Predicate VACCS_Good WeakTransitions
  Subset_Act DefinitionAS Convergence VACCS_Static VACCS_Must_Characterization
  VACCS_Erasure VACCS_Precongruence VACCS_Copycat.

Section VACCS_Absorb.

Context `{VP : VACCS_Parameters}.

(** [must (g 𝟘) t] is a property of the *client* alone: [𝟘] never
    interacts, so the only field with content is [ex], which says [t] has a
    [τ] of its own whenever it is not already good. *)
Lemma must_nil_tau : forall (t : proc), (g 𝟘) must_pass t -> ~ good_VACCS t ->
  exists t', lts t τ t'.
Proof.
  intros t Hm Hng. inversion Hm; subst.
  - contradiction.
  - destruct ex as (u & Hu). inversion Hu; subst.
    + unfold lts_step in *; simpl in *. inversion l.
    + eexists. eassumption.
    + unfold lts_step in *; simpl in *. inversion l1.
Qed.

(** ** The law *)

Lemma must_i_input_drop : forall c P G,
  (forall v, (P^v) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (g 𝟘)) -> (g ((c ? P) + G)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (g G).
Proof.
  intros c P G HP t Hm. remember (g ((c ? P) + G)) as p0 eqn:Heq.
  induction Hm; subst.
  - apply m_now. assumption.
  - apply m_step.
    + assumption.
    + destruct ex as (u & Hu). inversion Hu; subst; unfold lts_step in *; simpl in *.
      * inversion l; subst.
        -- inversion H6.
        -- eexists. eapply ParLeft. eassumption.
      * eexists. eapply ParRight. eassumption.
      * inversion l1; subst.
        -- inversion H6; subst.
           destruct μ2 as [[c2 v2]|[c2 v2]]; simpl in eq; try (exfalso; exact eq).
           inversion eq; subst.
           assert (Hmv : (P ^ v2) must_pass b2)
             by (eapply (com _ _ (ActIn (c2,v2)) (ActOut (c2,v2)));
                 [ reflexivity | apply lts_choiceL; apply lts_input | exact l2 ]).
           assert (Hnil : (g 𝟘) must_pass b2) by (apply (HP v2); exact Hmv).
           assert (Hsh : t ≡* ((c2 ! v2 • 𝟘) ‖ b2))
             by (eapply TransitionShapeForOutputSimplified; exact l2).
           destruct (good_decidable b2) as [Hgb | Hgb].
           ++ exfalso. apply nh. eapply good_preserved_by_cgr; [ | apply cgr_symm; exact Hsh ].
              apply good_par. right. exact Hgb.
           ++ destruct (must_nil_tau b2 Hnil Hgb) as (b3 & Hb3).
              assert (Hstep : sc_then_lts t τ ((c2 ! v2 • 𝟘) ‖ b3)).
              { exists ((c2 ! v2 • 𝟘) ‖ b2). split; [ exact Hsh | apply lts_parR; exact Hb3 ]. }
              apply Congruence_Respects_Transition in Hstep.
              destruct Hstep as (r & Hr & _).
              eexists. eapply ParRight. exact Hr.
        -- eexists. eapply ParSync; [ exact eq | eassumption | exact l2 ].
    + intros p' Hp'. apply pt. apply lts_choiceR. exact Hp'.
    + intros t' Ht'. eapply H0; [ exact Ht' | reflexivity ].
    + intros p' t' mu1 mu2 Hd Hl1 Hl2.
      eapply com; [ exact Hd | apply lts_choiceR; exact Hl1 | exact Hl2 ].
Qed.

(** The bare instance, for reference: an absorbing input is invisible. *)
Corollary must_i_input_nil : forall c P,
  (forall v, (P^v) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (g 𝟘)) -> (g (c ? P)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (g 𝟘).
Proof.
  intros c P HP t Hm.
  apply (must_i_input_drop c P 𝟘 HP).
  assert (Hc : (g (c ? P)) ≂ₘᵤₛₜᵢ (g ((c ? P) + 𝟘)))
    by (apply must_i_cgr; apply cgr_choice_nil_rev).
  destruct Hc as [Hc1 Hc2]. apply Hc2. exact Hm.
Qed.

(** * Harmlessness relative to a set of refused channels

    [must_i_input_drop]'s premise is sound but too strong, and no premise
    of the form "[P^v ⊑ₘᵤₛₜᵢ X]" can replace it: the semantic condition
    quantifies over a **strict subclass** of clients (those that are
    τ-stuck, not good, and refuse [c ?]), while [⊑ₘᵤₛₜᵢ] quantifies over
    all of them.  Three candidates were tried and all three fail —
    `∀v, ⊢ P^v ⊑ 𝟘` is too strong (it rejects the true
    [c ? (d ? (c!x•𝟘)) ⊑ₘᵤₛₜᵢ 𝟘]), while `∀v, ⊢ (c!v•𝟘) ‖ P^v ⊑ (c!v•𝟘)`
    and `∀v, ⊢ P^v ⊑ (c!v•𝟘)` are outright false.

    The right notion is a judgement, not a preorder, and it has to carry
    the set of channels the client is known to refuse — because chasing
    the condition through an input **grows** that set:

        Harmless S p  :=  p passes no client that is τ-stuck, not good,
                          and refuses every channel in S

    The input clause is sound for the reason every law in this
    development turns on: a τ-stuck client holding a [d]-message cannot
    be offering [d ?], so the residue really does refuse one more
    channel.  [lts_in_value_swap] is what makes "refuses [d]" mean *at
    every value*, from a single message.

    Four instances, and the judgement gets all four right:
    [c ? 𝟘 ⊑ 𝟘] and [c ? (d ? (c!x•𝟘)) ⊑ 𝟘] are covered (the latter is
    exactly what defeats the old premise), [d ? (c!x•𝟘) ⊑ 𝟘] is correctly
    *refused* (it is false), and [ccat]/[resp] are covered — so this
    single judgement subsumes [ax_ccat_l] and [ax_resp] as well. *)

Definition chset := ChannelData -> Prop.

Inductive Harmless : chset -> proc -> Prop :=
| hm_nil : forall S, Harmless S (g 𝟘)
| hm_success : forall S, Harmless S (g ①)
| hm_out : forall S c v, S c -> Harmless S (c ! v • 𝟘)
| hm_tau : forall S p, Harmless S p -> Harmless S (g (𝛕 • p))
| hm_in : forall S c P, (forall w, Harmless (fun d => S d \/ d = c) (P ^ w)) ->
    Harmless S (g (c ? P))
| hm_choice : forall S M N, Harmless S (g M) -> Harmless S (g N) ->
    Harmless S (g (M + N))
| hm_par : forall S p q, Harmless S p -> Harmless S q -> Harmless S (p ‖ q).

Lemma Harmless_mono : forall S p, Harmless S p ->
  forall S', (forall d, S d -> S' d) -> Harmless S' p.
Proof.
  intros S p H. induction H; intros S' Hsub.
  - apply hm_nil.
  - apply hm_success.
  - apply hm_out. apply Hsub. assumption.
  - apply hm_tau. apply IHHarmless. exact Hsub.
  - apply hm_in. intro w. apply (H0 w).
    intros d [Hd|Hd]; [ left; apply Hsub; exact Hd | right; exact Hd ].
  - apply hm_choice; [ apply IHHarmless1 | apply IHHarmless2 ]; exact Hsub.
  - apply hm_par; [ apply IHHarmless1 | apply IHHarmless2 ]; exact Hsub.
Qed.

(** The four transition-level facts the soundness induction needs.  With
    [hm_par] present, a [τ] of the server may be an *internal
    synchronisation*, and closing that case is what forces both an output
    clause ([hm_out_step]) and the argument that the set need not grow:
    the emitting side's channel is already in [S] ([hm_out_chan]), so
    [hm_in_step]'s [S ∪ {c}] collapses back to [S] by [Harmless_mono].
    That is the whole reason [hm_par] is sound. *)

Lemma hm_out_chan : forall S p, Harmless S p ->
  forall c v p', lts p (ActExt (ActOut (c,v))) p' -> S c.
Proof.
  intros S p H. induction H; intros c0 v0 p' Hl; try (inversion Hl; fail).
  - inversion Hl; subst. assumption.
  - inversion Hl; subst; [ eapply IHHarmless1 | eapply IHHarmless2 ]; eassumption.
  - inversion Hl; subst; [ eapply IHHarmless1 | eapply IHHarmless2 ]; eassumption.
Qed.

Lemma hm_out_step : forall S p, Harmless S p ->
  forall c v p', lts p (ActExt (ActOut (c,v))) p' -> Harmless S p'.
Proof.
  intros S p H. induction H; intros c0 v0 p' Hl; try (inversion Hl; fail).
  - inversion Hl; subst. apply hm_nil.
  - inversion Hl; subst; [ eapply IHHarmless1 | eapply IHHarmless2 ]; eassumption.
  - inversion Hl; subst.
    + apply hm_par; [ eapply IHHarmless1; eassumption | assumption ].
    + apply hm_par; [ assumption | eapply IHHarmless2; eassumption ].
Qed.

Lemma hm_in_step : forall S p, Harmless S p ->
  forall c w p', lts p (ActExt (ActIn (c,w))) p' ->
  Harmless (fun d => S d \/ d = c) p'.
Proof.
  intros S p H. induction H; intros c0 w0 p' Hl; try (inversion Hl; fail).
  - inversion Hl; subst. apply H.
  - inversion Hl; subst; [ eapply IHHarmless1 | eapply IHHarmless2 ]; eassumption.
  - inversion Hl; subst.
    + apply hm_par; [ eapply IHHarmless1; eassumption | ].
      eapply Harmless_mono; [ eassumption | intros d Hd; left; exact Hd ].
    + apply hm_par; [ | eapply IHHarmless2; eassumption ].
      eapply Harmless_mono; [ eassumption | intros d Hd; left; exact Hd ].
Qed.

Lemma hm_tau_step : forall S p, Harmless S p -> forall p', lts p τ p' -> Harmless S p'.
Proof.
  intros S p H. induction H; intros p' Hl; try (inversion Hl; fail).
  - inversion Hl; subst. exact H.
  - inversion Hl; subst; [ apply IHHarmless1 | apply IHHarmless2 ]; assumption.
  - inversion Hl; subst.
    + apply hm_par.
      * exact (hm_out_step S p H c v p2 H3).
      * eapply Harmless_mono; [ exact (hm_in_step S q H0 c v q2 H4) | ].
        intros d [Hd|Hd]; [ exact Hd | subst d; exact (hm_out_chan S p H c v p2 H3) ].
    + apply hm_par.
      * eapply Harmless_mono; [ exact (hm_in_step S p H c v q2 H4) | ].
        intros d [Hd|Hd]; [ exact Hd | subst d; exact (hm_out_chan S q H0 c v p2 H3) ].
      * exact (hm_out_step S q H0 c v p2 H3).
    + apply hm_par; [ apply IHHarmless1; assumption | assumption ].
    + apply hm_par; [ assumption | apply IHHarmless2; assumption ].
Qed.

Definition RefusesIn (S : chset) (u : proc) : Prop :=
  forall c v q, S c -> ~ lts u (ActExt (ActIn (c,v))) q.

(** ** Soundness

    By induction on the [must] derivation, not on [Harmless] — the
    judgement is preserved by transitions ([hm_tau_step], [hm_in_step]),
    so each field of [m_step] hands the induction a smaller [must] fact
    with the invariant restored.  The [ParSync]-on-an-input case is where
    the set grows and where the asynchronous shape lemma
    ([TransitionShapeForOutputSimplified]) and [lts_in_value_swap] are
    used. *)

Theorem Harmless_sound : forall (p u : proc), p must_pass u ->
  forall S, Harmless S p -> (forall q, ~ lts u τ q) -> ~ good_VACCS u ->
  RefusesIn S u -> False.
Proof.
  intros p u Hm. induction Hm; intros S HH Hst Hng Href.
  - contradiction.
  - destruct ex as (x & Hx). inversion Hx; subst; unfold lts_step in *; simpl in *.
    + eapply H; [ exact l | eapply hm_tau_step; eassumption | exact Hst | exact Hng | exact Href ].
    + eapply Hst. exact l.
    + destruct μ1 as [[c1 v1]|[c1 v1]]; destruct μ2 as [[c2 v2]|[c2 v2]];
        simpl in eq; try (exfalso; exact eq); inversion eq; subst.
      * assert (Hsh : t ≡* ((c2 ! v2 • 𝟘) ‖ b2))
          by (eapply TransitionShapeForOutputSimplified; exact l2).
        assert (Hstb : forall q, ~ lts b2 τ q).
        { intros q Hq.
          assert (Hsc : sc_then_lts t τ ((c2 ! v2 • 𝟘) ‖ q))
            by (exists ((c2 ! v2 • 𝟘) ‖ b2); split; [ exact Hsh | apply lts_parR; exact Hq ]).
          apply Congruence_Respects_Transition in Hsc. destruct Hsc as (r & Hr & _).
          eapply Hst. exact Hr. }
        assert (Hngb : ~ good_VACCS b2).
        { intro Hgb. apply Hng. eapply good_preserved_by_cgr;
            [ | apply cgr_symm; exact Hsh ]. apply good_par. right. exact Hgb. }
        eapply (H1 a2 b2 (ActIn (c2,v2)) (ActOut (c2,v2)));
          [ reflexivity | exact l1 | exact l2 | eapply hm_in_step; eassumption
          | exact Hstb | exact Hngb | ].
        intros d x q [Hd|Hd] Hl.
        -- assert (Hsc : sc_then_lts t (ActExt (ActIn (d,x))) ((c2 ! v2 • 𝟘) ‖ q))
             by (exists ((c2 ! v2 • 𝟘) ‖ b2); split; [ exact Hsh | apply lts_parR; exact Hl ]).
           apply Congruence_Respects_Transition in Hsc. destruct Hsc as (r & Hr & _).
           eapply Href; [ exact Hd | exact Hr ].
        -- subst d.
           destruct (lts_in_value_swap b2 (ActIn (c2,x)) q Hl c2 x v2 eq_refl) as (q' & Hq').
           assert (Hsc : sc_then_lts t τ ((g 𝟘) ‖ q')).
           { exists ((c2 ! v2 • 𝟘) ‖ b2). split; [ exact Hsh | ].
             eapply lts_comL; [ apply lts_output | exact Hq' ]. }
           apply Congruence_Respects_Transition in Hsc. destruct Hsc as (r & Hr & _).
           eapply Hst. exact Hr.
      * eapply Href; [ | exact l2 ]. eapply hm_out_chan; eassumption.
Qed.

(** A transition either exists or does not — constructively, because the
    VACCS [gLts] instance exposes [lts_set] as a [gset], whose equality
    with [∅] is decidable.  (The generic [lts_refuses_spec1]/[_spec2] both
    misbehave on this instance — one times out — so go through [lts_set]
    directly, as elsewhere in this development.  The [Unshelve] is the
    usual instance-resolution quirk after [set_choose_L].) *)

Lemma lts_dec : forall (b : proc) (al : ActIO TypeOfActions),
  (forall q, ~ lts b al q) \/ (exists q, lts b al q).
Proof.
  intros b al. destruct (decide (lts_set b al = ∅)) as [He|He].
  - left. intros q Hq. apply lts_set_spec1 in Hq. rewrite He in Hq.
    eapply (elem_of_empty q). exact Hq.
  - right. apply set_choose_L in He. destruct He as (q & Hq).
    exists q. apply lts_set_spec0. exact Hq.
  Unshelve. all: typeclasses eauto.
Qed.

(** ** The general drop law

    The same proof as [must_i_input_drop], with [Harmless_sound] in place
    of [must_nil_tau].  The [ex]/[ParSync] case now splits three ways with
    [lts_dec]: if the residue [b2] has a [τ], or offers [c ?], then the
    *client* [t] has a [τ] and [ParRight] supplies the step; otherwise
    [b2] is τ-stuck, not good, and — by [lts_in_value_swap] — refuses [c]
    at every value, which is exactly [Harmless_sound]'s hypothesis.

    Statement gotcha: write [subst_in_proc 0 v P], not [P ^ v].  In this
    position nothing anchors the scope (unlike inside [⊑ₘᵤₛₜᵢ]) and [^]
    resolves in [nat_scope], with the unhelpful error "P has type proc
    while it is expected to have type nat". *)

Theorem must_i_input_drop_harmless :
  forall (c : ChannelData) (P : proc) (G : gproc),
  (forall v : ValueData, Harmless (fun d => d = c) (subst_in_proc 0 v P)) ->
  (g ((c ? P) + G)) ⊑ₘᵤₛₜᵢ (g G).
Proof.
  intros c P G HP t Hm. remember (g ((c ? P) + G)) as p0 eqn:Heq.
  induction Hm; subst.
  - apply m_now. assumption.
  - apply m_step.
    + assumption.
    + destruct ex as (u & Hu). inversion Hu; subst; unfold lts_step in *; simpl in *.
      * inversion l; subst.
        -- inversion H6.
        -- eexists. eapply ParLeft. eassumption.
      * eexists. eapply ParRight. eassumption.
      * inversion l1; subst.
        -- inversion H6; subst.
           destruct μ2 as [[c2 v2]|[c2 v2]]; simpl in eq; try (exfalso; exact eq).
           inversion eq; subst.
           assert (Hmv : (P ^ v2) must_pass b2)
             by (eapply (com _ _ (ActIn (c2,v2)) (ActOut (c2,v2)));
                 [ reflexivity | apply lts_choiceL; apply lts_input | exact l2 ]).
           assert (Hsh : t ≡* ((c2 ! v2 • 𝟘) ‖ b2))
             by (eapply TransitionShapeForOutputSimplified; exact l2).
           destruct (good_decidable b2) as [Hgb | Hgb].
           ++ exfalso. apply nh. eapply good_preserved_by_cgr; [ | apply cgr_symm; exact Hsh ].
              apply good_par. right. exact Hgb.
           ++ destruct (lts_dec b2 τ) as [Hstb | (b3 & Hb3)].
              ** destruct (lts_dec b2 (ActExt (ActIn (c2,v2)))) as [Hnoin | (q' & Hq')].
                 --- exfalso. eapply (Harmless_sound (P ^ v2) b2 Hmv (fun d => d = c2));
                       [ apply HP | exact Hstb | exact Hgb | ].
                     intros d x q Hd Hl. subst d.
                     destruct (lts_in_value_swap b2 (ActIn (c2,x)) q Hl c2 x v2 eq_refl)
                       as (r & Hr).
                     eapply Hnoin. exact Hr.
                 --- assert (Hsc : sc_then_lts t τ ((g 𝟘) ‖ q')).
                     { exists ((c2 ! v2 • 𝟘) ‖ b2). split; [ exact Hsh | ].
                       eapply lts_comL; [ apply lts_output | exact Hq' ]. }
                     apply Congruence_Respects_Transition in Hsc.
                     destruct Hsc as (r & Hr & _). eexists. eapply ParRight. exact Hr.
              ** assert (Hsc : sc_then_lts t τ ((c2 ! v2 • 𝟘) ‖ b3)).
                 { exists ((c2 ! v2 • 𝟘) ‖ b2). split; [ exact Hsh | apply lts_parR; exact Hb3 ]. }
                 apply Congruence_Respects_Transition in Hsc.
                 destruct Hsc as (r & Hr & _). eexists. eapply ParRight. exact Hr.
        -- eexists. eapply ParSync; [ exact eq | eassumption | exact l2 ].
    + intros p' Hp'. apply pt. apply lts_choiceR. exact Hp'.
    + intros t' Ht'. eapply H0; [ exact Ht' | reflexivity ].
    + intros p' t' mu1 mu2 Hd Hl1 Hl2.
      eapply com; [ exact Hd | apply lts_choiceR; exact Hl1 | exact Hl2 ].
Qed.

(** ** Four instances, all one line — and they were four separate laws

    The copycat, the responder, the swallow, and the nested case that
    defeated the old premise.  Note the responder is obtained at an
    **arbitrary** channel here, where [VACCS_Copycat.v]'s [ax_resp] needs
    a constant one: that restriction was an artefact of its proof
    technique, not of the fact. *)

Corollary must_i_copycat_drop : forall (c : ChannelData) (G : gproc),
  (g ((c ? (c ! (bvar 0) • 𝟘)) + G)) ⊑ₘᵤₛₜᵢ (g G).
Proof.
  intros c G. apply must_i_input_drop_harmless. intro v.
  simpl. apply hm_out. reflexivity.
Qed.

Corollary must_i_resp_drop : forall (c : ChannelData) (V : ValueData) (G : gproc),
  (g ((c ? (c ! V • 𝟘)) + G)) ⊑ₘᵤₛₜᵢ (g G).
Proof.
  intros c V G. apply must_i_input_drop_harmless. intro v.
  simpl. apply hm_out. reflexivity.
Qed.

Corollary must_i_nested_drop : forall (c d : ChannelData) (V : ValueData) (G : gproc),
  (g ((c ? (g (d ? (c ! V • 𝟘)))) + G)) ⊑ₘᵤₛₜᵢ (g G).
Proof.
  intros c d V G. apply must_i_input_drop_harmless. intro v.
  simpl. apply hm_in. intro w. simpl. apply hm_out. left. reflexivity.
Qed.

Corollary must_i_swallow_drop : forall (c : ChannelData) (G : gproc),
  (g ((c ? (g 𝟘)) + G)) ⊑ₘᵤₛₜᵢ (g G).
Proof.
  intros c G. apply must_i_input_drop_harmless. intro v. simpl. apply hm_nil.
Qed.

(** ** The judgement — two clauses, no syntax at all

    The first version of this file had three *syntactic* clauses (a
    message, a bad [𝛕]-summand, a stable sum with all input branches bad).
    They are all instances of two clauses stated purely over the LTS, and
    the general form covers [‖] and [ν] for free — which the syntactic one
    did not, and which the normal form [Ѵⁿ (msgs l ‖ g M)] needs:

    - [bad_step] — one [τ]-successor is bad.  Sound through [pt].
    - [bad_stuck] — [p] is [τ]-stuck, every channel it can *emit* on is
      already refused ([S]), and every *input* residue is bad at [S ∪ {c}].
      Sound through [ex]: the client, being [τ]-stuck too, can only move by
      feeding [p], and feeding is what the third condition follows.

    These are exactly the two ways [must p u] can fail at a [τ]-stuck
    client, so the judgement is complete by construction. *)

Inductive Bad : chset -> proc -> Prop :=
| bad_step : forall S p p', lts p τ p' -> Bad S p' -> Bad S p
| bad_stuck : forall S p,
    (forall q, ~ lts p τ q) ->
    (forall c v p', lts p (ActExt (ActOut (c,v))) p' -> S c) ->
    (forall c v p', lts p (ActExt (ActIn (c,v))) p' ->
       exists p'', lts p (ActExt (ActIn (c,v))) p'' /\
                   Bad (fun d => S d \/ d = c) p'') ->
    Bad S p.

(** ** Soundness

    Induction on the [must] derivation; at each step the *judgement* is
    destructed and each clause picks the field that refutes it — [bad_step]
    uses [pt], [bad_stuck] uses [ex].  No preservation lemmas are needed,
    which is the whole point of stating the clauses over transitions.  The
    [ParSync]-on-an-input case is the only one with content, and it is the
    same asynchronous argument as everywhere else: the client emitted, so
    it splits as [(c!v•𝟘) ‖ b2], [τ]-stuckness forces [b2] to refuse [c],
    and [lts_in_value_swap] upgrades that to every value. *)

Theorem Bad_sound : forall (p u : proc), p must_pass u ->
  forall S, Bad S p -> (forall q, ~ lts u τ q) -> ~ good_VACCS u ->
  RefusesIn S u -> False.
Proof.
  intros p u Hm. induction Hm; intros S HB Hst Hng Href.
  - contradiction.
  - destruct HB as [ S p0 p1 Hl HB' | S p0 Hstp Hout Hin ].
    + eapply H; [ exact Hl | exact HB' | exact Hst | exact Hng | exact Href ].
    + destruct ex as (x & Hx). inversion Hx; subst; unfold lts_step in *; simpl in *.
      * eapply Hstp. exact l.
      * eapply Hst. exact l.
      * destruct μ1 as [[c1 v1]|[c1 v1]].
        -- destruct μ2 as [[c2 v2]|[c2 v2]]; simpl in eq; try (exfalso; exact eq).
           inversion eq; subst.
           assert (Hsh : t ≡* ((c2 ! v2 • 𝟘) ‖ b2))
             by (eapply TransitionShapeForOutputSimplified; exact l2).
           assert (Hstb : forall q, ~ lts b2 τ q).
           { intros q Hq.
             assert (Hsc : sc_then_lts t τ ((c2 ! v2 • 𝟘) ‖ q))
               by (exists ((c2 ! v2 • 𝟘) ‖ b2); split; [ exact Hsh | apply lts_parR; exact Hq ]).
             apply Congruence_Respects_Transition in Hsc. destruct Hsc as (r & Hr & _).
             eapply Hst. exact Hr. }
           assert (Hngb : ~ good_VACCS b2).
           { intro Hgb. apply Hng. eapply good_preserved_by_cgr;
               [ | apply cgr_symm; exact Hsh ]. apply good_par. right. exact Hgb. }
           destruct (Hin _ _ _ l1) as (a2' & Hl1' & HBa2').
           eapply (H1 a2' b2 (ActIn (c2,v2)) (ActOut (c2,v2)));
             [ reflexivity | exact Hl1' | exact l2 | exact HBa2'
             | exact Hstb | exact Hngb | ].
           intros d x q [Hd|Hd] Hl.
           ++ assert (Hsc : sc_then_lts t (ActExt (ActIn (d,x))) ((c2 ! v2 • 𝟘) ‖ q))
                by (exists ((c2 ! v2 • 𝟘) ‖ b2); split; [ exact Hsh | apply lts_parR; exact Hl ]).
              apply Congruence_Respects_Transition in Hsc. destruct Hsc as (r & Hr & _).
              eapply Href; [ exact Hd | exact Hr ].
           ++ subst d.
              destruct (lts_in_value_swap b2 (ActIn (c2,x)) q Hl c2 x v2 eq_refl) as (q' & Hq').
              assert (Hsc : sc_then_lts t τ ((g 𝟘) ‖ q')).
              { exists ((c2 ! v2 • 𝟘) ‖ b2). split; [ exact Hsh | ].
                eapply lts_comL; [ apply lts_output | exact Hq' ]. }
              apply Congruence_Respects_Transition in Hsc. destruct Hsc as (r & Hr & _).
              eapply Hst. exact Hr.
        -- destruct μ2 as [[c2 v2]|[c2 v2]]; simpl in eq; try (exfalso; exact eq).
           inversion eq; subst.
           eapply Href; [ eapply Hout; exact l1 | exact l2 ].
Qed.

Lemma bad_msg : forall S c v, S c -> Bad S (c ! v • 𝟘).
Proof.
  intros S c v Sc. apply bad_stuck.
  - intros q Hq. inversion Hq.
  - intros d x p' Hl. inversion Hl; subst. exact Sc.
  - intros d x p' Hl. inversion Hl.
Qed.

Lemma bad_nil_any : forall S, Bad S ((g 𝟘) : proc).
Proof.
  intro S. apply bad_stuck;
    [ intros q Hq | intros d x q Hq | intros d x q Hq ]; inversion Hq.
Qed.

(** ** The drop law at [Bad]

    Same shape as [must_i_input_drop_harmless]; only the appeal in the
    stuck case changes, from [Harmless_sound] to [Bad_sound]. *)

Theorem must_i_input_drop_bad :
  forall (c : ChannelData) (P : proc) (G : gproc),
  (forall v : ValueData, Bad (fun d => d = c) (subst_in_proc 0 v P)) ->
  (g ((c ? P) + G)) ⊑ₘᵤₛₜᵢ (g G).
Proof.
  intros c P G HP t Hm. remember (g ((c ? P) + G)) as p0 eqn:Heq.
  induction Hm; subst.
  - apply m_now. assumption.
  - apply m_step.
    + assumption.
    + destruct ex as (u & Hu). inversion Hu; subst; unfold lts_step in *; simpl in *.
      * inversion l; subst.
        -- inversion H6.
        -- eexists. eapply ParLeft. eassumption.
      * eexists. eapply ParRight. eassumption.
      * inversion l1; subst.
        -- inversion H6; subst.
           destruct μ2 as [[c2 v2]|[c2 v2]]; simpl in eq; try (exfalso; exact eq).
           inversion eq; subst.
           assert (Hmv : (P ^ v2) must_pass b2)
             by (eapply (com _ _ (ActIn (c2,v2)) (ActOut (c2,v2)));
                 [ reflexivity | apply lts_choiceL; apply lts_input | exact l2 ]).
           assert (Hsh : t ≡* ((c2 ! v2 • 𝟘) ‖ b2))
             by (eapply TransitionShapeForOutputSimplified; exact l2).
           destruct (good_decidable b2) as [Hgb | Hgb].
           ++ exfalso. apply nh. eapply good_preserved_by_cgr; [ | apply cgr_symm; exact Hsh ].
              apply good_par. right. exact Hgb.
           ++ destruct (lts_dec b2 τ) as [Hstb | (b3 & Hb3)].
              ** destruct (lts_dec b2 (ActExt (ActIn (c2,v2)))) as [Hnoin | (q' & Hq')].
                 --- exfalso. eapply (Bad_sound (P ^ v2) b2 Hmv (fun d => d = c2));
                       [ apply HP | exact Hstb | exact Hgb | ].
                     intros d x q Hd Hl. subst d.
                     destruct (lts_in_value_swap b2 (ActIn (c2,x)) q Hl c2 x v2 eq_refl)
                       as (r & Hr).
                     eapply Hnoin. exact Hr.
                 --- assert (Hsc : sc_then_lts t τ ((g 𝟘) ‖ q')).
                     { exists ((c2 ! v2 • 𝟘) ‖ b2). split; [ exact Hsh | ].
                       eapply lts_comL; [ apply lts_output | exact Hq' ]. }
                     apply Congruence_Respects_Transition in Hsc.
                     destruct Hsc as (r & Hr & _). eexists. eapply ParRight. exact Hr.
              ** assert (Hsc : sc_then_lts t τ ((c2 ! v2 • 𝟘) ‖ b3)).
                 { exists ((c2 ! v2 • 𝟘) ‖ b2). split; [ exact Hsh | apply lts_parR; exact Hb3 ]. }
                 apply Congruence_Respects_Transition in Hsc.
                 destruct Hsc as (r & Hr & _). eexists. eapply ParRight. exact Hr.
        -- eexists. eapply ParSync; [ exact eq | eassumption | exact l2 ].
    + intros p' Hp'. apply pt. apply lts_choiceR. exact Hp'.
    + intros t' Ht'. eapply H0; [ exact Ht' | reflexivity ].
    + intros p' t' mu1 mu2 Hd Hl1 Hl2.
      eapply com; [ exact Hd | apply lts_choiceR; exact Hl1 | exact Hl2 ].
Qed.


(** * Restricting a stable sum to a channel set — the rule the matching needs

    Dropping guards one at a time is the wrong move (see the plan notes):
    it is unsound as a *strategy* on the left, and unsound as a *step* on
    the mirror.  The right move is to restrict the whole sum's channel set
    in **one** step, and that is sound under a condition the semantics
    actually supplies:

        must_i_restrict :  M' ⊆ M (transitions),  M stable,
          (every τ-stuck non-good client M must-passes emits on a channel
           M' offers)
          ->  g M ⊑ₘᵤₛₜᵢ g M'

    Only [ex] has content: at a τ-stuck client the restricted sum must
    still have a step, and the hypothesis is exactly that.  [com] and [pt]
    transfer because [M']'s transitions are among [M]'s.

    And the hypothesis is what [g M ⊑ₘᵤₛₜᵢ g L] gives, for [M'] covering
    [L]'s channels ([restrict_premise]): a τ-stuck non-good client that [M]
    passes is passed by [L] too, and [L] — being a guarded sum, so unable
    to emit — can only have taken a step by *receiving*, i.e. the client
    emitted on a channel [L] offers.

    This replaces [gGuardsIn] entirely: no guard is ever dropped
    individually, so the fact that a stable sum may offer channels the
    right-hand side does not ([c ? 𝟘 ⊑ₘᵤₛₜᵢ 𝟘]) stops being an obstacle. *)

Definition offers (M : gproc) (c : ChannelData) : Prop :=
  exists w r, lts (g M) (ActExt (ActIn (c,w))) r.

Theorem must_i_restrict : forall (M M' : gproc),
  (forall al q, lts (g M') al q -> lts (g M) al q) ->
  (forall p, ~ lts (g M) τ p) ->
  (forall u, (forall q, ~ lts u τ q) -> ~ good_VACCS u -> (g M) must_pass u ->
     exists c v q, offers M' c /\ lts u (ActExt (ActOut (c,v))) q) ->
  (g M) ⊑ₘᵤₛₜᵢ (g M').
Proof.
  intros M M' Hsub Hst Hex t Hm. remember (g M) as p0 eqn:Heq.
  induction Hm; subst.
  - apply m_now. assumption.
  - apply m_step.
    + assumption.
    + destruct (lts_dec t τ) as [Htst | (t2 & Ht2)].
      * assert (Horig : (g M) must_pass t) by (apply m_step; assumption).
        destruct (Hex t Htst nh Horig) as (c & v & q & (w & r & Hoff) & Hemit).
        destruct (lts_in_value_swap (g M') (ActIn (c,w)) r Hoff c w v eq_refl) as (r' & Hr').
        eexists. eapply (ParSync (ActIn (c,v)) (ActOut (c,v)));
          [ reflexivity | exact Hr' | exact Hemit ].
      * eexists. eapply ParRight. exact Ht2.
    + intros p' Hp'. exfalso. eapply Hst. apply Hsub. exact Hp'.
    + intros t' Ht'. eapply H0; [ exact Ht' | reflexivity | exact Hsub | exact Hst | exact Hex ].
    + intros p' t' mu1 mu2 Hd Hl1 Hl2.
      eapply com; [ exact Hd | apply Hsub; exact Hl1 | exact Hl2 ].
Qed.

(** A guarded sum can never emit — the fact that makes the premise
    derivable, and the same one behind [gproc_coR_empty]. *)
Lemma gsum_no_out : forall (N : gproc) c v q,
  ~ lts (g N) (ActExt (ActOut (c,v))) q.
Proof.
  induction N as [ | | d p | p | N1 IH1 N2 IH2 ]; intros c v q Hl;
    inversion Hl; subst.
  - eapply IH1; eassumption.
  - eapply IH2; eassumption.
Qed.

Theorem restrict_premise : forall (M L : gproc),
  (g M) ⊑ₘᵤₛₜᵢ (g L) -> (forall p, ~ lts (g L) τ p) ->
  forall u, (forall q, ~ lts u τ q) -> ~ good_VACCS u -> (g M) must_pass u ->
  exists c v q, offers L c /\ lts u (ActExt (ActOut (c,v))) q.
Proof.
  intros M L Hpre HstL u Hstu Hng Hm.
  assert (HmL : (g L) must_pass u) by (apply Hpre; exact Hm).
  inversion HmL; subst.
  - contradiction.
  - destruct ex as (x & Hx). inversion Hx; subst; unfold lts_step in *; simpl in *.
    + exfalso. eapply HstL. exact l.
    + exfalso. eapply Hstu. exact l.
    + destruct μ1 as [[c1 v1]|[c1 v1]].
      * destruct μ2 as [[c2 v2]|[c2 v2]]; simpl in eq; try (exfalso; exact eq).
        inversion eq; subst.
        exists c2, v2, b2. split; [ | exact l2 ]. exists v2, a2. exact l1.
      * exfalso. eapply gsum_no_out. exact l1.
Qed.

(** ** A sum of copycats is equivalent to [𝟘] — the other direction

    [must_i_nil_below_copycats] ([VACCS_Copycat.v]) gives [𝟘 ⊑ₘᵤₛₜᵢ g N];
    this gives the converse, so the equivalence is complete.  It is the
    same three-way split as [must_i_input_drop_harmless], with
    [gCopycats_lts] supplying the continuation's shape and
    [Harmless {c} (c!v•𝟘)] closing the stuck case.

    It is what lets the matching add copycats *and take them away again*:
    [X ≂ₘᵤₛₜᵢ g M ‖ g CC ≂ₘᵤₛₜᵢ g M], so the mirror construction changes
    nothing semantically and `g X ⊑ₘᵤₛₜᵢ g L` follows from
    `g M ⊑ₘᵤₛₜᵢ g L`. *)

Theorem must_i_copycats_below_nil : forall (N : gproc), gCopycats N ->
  (g N) ⊑ₘᵤₛₜᵢ (g 𝟘).
Proof.
  intros N Hcop t Hm. remember (g N) as p0 eqn:Heq.
  induction Hm; subst.
  - apply m_now. assumption.
  - apply m_step.
    + assumption.
    + destruct ex as (u & Hu). inversion Hu; subst; unfold lts_step in *; simpl in *.
      * exfalso. eapply gCopycats_no_tau; eassumption.
      * eexists. eapply ParRight. eassumption.
      * destruct (gCopycats_lts N Hcop μ1 a2 l1) as (c & v & Hmu & Hp). subst.
        destruct μ2 as [[c2 v2]|[c2 v2]]; simpl in eq; try (exfalso; exact eq).
        inversion eq; subst.
        assert (Hmv : (c2 ! v2 • 𝟘) must_pass b2)
          by (eapply (com _ _ (ActIn (c2,v2)) (ActOut (c2,v2)));
              [ reflexivity | exact l1 | exact l2 ]).
        assert (Hsh : t ≡* ((c2 ! v2 • 𝟘) ‖ b2))
          by (eapply TransitionShapeForOutputSimplified; exact l2).
        destruct (good_decidable b2) as [Hgb | Hgb].
        -- exfalso. apply nh. eapply good_preserved_by_cgr; [ | apply cgr_symm; exact Hsh ].
           apply good_par. right. exact Hgb.
        -- destruct (lts_dec b2 τ) as [Hstb | (b3 & Hb3)].
           ++ destruct (lts_dec b2 (ActExt (ActIn (c2,v2)))) as [Hnoin | (q' & Hq')].
              ** exfalso. eapply (Harmless_sound (c2 ! v2 • 𝟘) b2 Hmv (fun d => d = c2));
                   [ apply hm_out; reflexivity | exact Hstb | exact Hgb | ].
                 intros d x q Hd Hl. subst d.
                 destruct (lts_in_value_swap b2 (ActIn (c2,x)) q Hl c2 x v2 eq_refl) as (r & Hr).
                 eapply Hnoin. exact Hr.
              ** assert (Hsc : sc_then_lts t τ ((g 𝟘) ‖ q')).
                 { exists ((c2 ! v2 • 𝟘) ‖ b2). split; [ exact Hsh | ].
                   eapply lts_comL; [ apply lts_output | exact Hq' ]. }
                 apply Congruence_Respects_Transition in Hsc.
                 destruct Hsc as (r & Hr & _). eexists. eapply ParRight. exact Hr.
           ++ assert (Hsc : sc_then_lts t τ ((c2 ! v2 • 𝟘) ‖ b3)).
              { exists ((c2 ! v2 • 𝟘) ‖ b2). split; [ exact Hsh | apply lts_parR; exact Hb3 ]. }
              apply Congruence_Respects_Transition in Hsc.
              destruct Hsc as (r & Hr & _). eexists. eapply ParRight. exact Hr.
    + intros p' Hp'. unfold lts_step in *; simpl in *. inversion Hp'.
    + intros t' Ht'. eapply H0; [ exact Ht' | reflexivity ].
    + intros p' t' mu1 mu2 Hd Hl1 Hl2. unfold lts_step in *; simpl in *. inversion Hl1.
Qed.

(** ** The restriction that IS sound on its own

    [must_i_restrict]'s premise is semantic, so it cannot become a rule of
    the system: the fact that justifies it is the very inequation the
    completeness proof is trying to derive.  There is, however, a
    syntactic special case that *is* sound unconditionally — restricting to
    a sub-sum that still offers **every channel the original offers**:

        must_i_restrict_same : M' ⊆ M -> M stable ->
          (∀ c, offers M c -> offers M' c) -> g M ⊑ₘᵤₛₜᵢ g M'

    A client that the sum must-passes and that cannot move by itself has
    fed one of the sum's channels; if [M'] still offers it, [M'] has the
    step too ([lts_in_value_swap] supplies it at the right value).  So
    *duplicate* guards on already-offered channels may always be dropped —
    which is the merge/collapse direction — while guards on *surplus*
    channels may not, and that asymmetry is exactly the open point. *)

Theorem must_i_restrict_same : forall (M M' : gproc),
  (forall al q, lts (g M') al q -> lts (g M) al q) ->
  (forall p, ~ lts (g M) τ p) ->
  (forall c, offers M c -> offers M' c) ->
  (g M) ⊑ₘᵤₛₜᵢ (g M').
Proof.
  intros M M' Hsub Hst Hcov.
  apply must_i_restrict; [ exact Hsub | exact Hst | ].
  intros u Hstu Hng Hm.
  inversion Hm; subst.
  - contradiction.
  - destruct ex as (x & Hx). inversion Hx; subst; unfold lts_step in *; simpl in *.
    + exfalso. eapply Hst. exact l.
    + exfalso. eapply Hstu. exact l.
    + destruct μ1 as [[c1 v1]|[c1 v1]].
      * destruct μ2 as [[c2 v2]|[c2 v2]]; simpl in eq; try (exfalso; exact eq).
        inversion eq; subst.
        exists c2, v2, b2. split; [ | exact l2 ].
        apply Hcov. exists v2, a2. exact l1.
      * exfalso. eapply gsum_no_out. exact l1.
Qed.

(** * [BadK]: a killer-channel set, and the first judgement that certifies
      the counterexample

    [VACCS_DropProbes.v] shows that no *local* certificate can work: for
    its [PP] there is provably no target [Q] above it that any
    harmlessness judgement could accept.  The way out is not a better
    certificate for one continuation but a judgement that can record how
    **several guards cooperate** — which is what the counterexample is
    about, `a ? PP` surviving only on help from `b`, a channel the
    `b ? 𝟘` guard already kills.

    So index the judgement by two channel sets:

      [BadK S D p] := "p passes no client that is τ-stuck, not good,
                       refuses inputs on S, **and emits on no channel of D**"

    and add one clause, [bk_kill], which performs the case split the
    semantics performs and an inductive judgement previously could not:

    - either the client **does** emit on [c] — then the [c]-continuations
      have to be bad, at [S ∪ {c}];
    - or it does not — then the rest of the argument may **assume** it,
      i.e. continue at [D ∪ {c}].

    The existence premise is what makes that sound: an input's
    availability is value-independent ([lts_in_value_swap]), so a single
    [c]-input of [p] supplies one at whatever value the client emits, and
    [must]'s [com] field then applies.  Without it a process with no
    [c]-input could "kill" on [c] while ignoring the client entirely.

    Deciding the case split needs "does [u] emit on [c]?", which is
    decidable because a process's pending messages are a **finite
    multiset** ([lts_oba_mo], [Lts_Finite_Output_Chain.v]) — the
    asynchronous structure paying for itself once more.  No classical
    reasoning is used. *)

Definition emits_on (c : ChannelData) (u : proc) : Prop :=
  exists v q, lts u ((c ▷ v)!) q.

Definition emitsb (c : ChannelData) (u : proc) : bool :=
  existsb (fun eta => match eta with
                      | ActOut (d,_) => bool_decide (d = c)
                      | _ => false end)
          (elements (lts_oba_mo u)).

Lemma emits_on_dec : forall c u, emits_on c u \/ ~ emits_on c u.
Proof.
  intros c u. destruct (emitsb c u) eqn:E.
  - left. unfold emitsb in E. apply existsb_exists in E as (eta & Hin & Hb).
    destruct eta as [[d x]|[d x]]; [ discriminate Hb | ].
    apply bool_decide_eq_true in Hb. subst d.
    apply list_elem_of_In in Hin. apply gmultiset_elem_of_elements in Hin.
    destruct (lts_oba_mo_spec_bis2 u (ActOut (c,x)) Hin) as (q & Hnb & Hl).
    exists x, q. exact Hl.
  - right. intros (v & q & Hl).
    assert (Hnb : non_blocking (ActOut (c,v))).
    { unfold non_blocking. simpl. unfold non_blocking_output. exists (c ▷ v). reflexivity. }
    pose proof (lts_oba_mo_spec_bis1 u (ActOut (c,v)) q Hnb Hl) as Hmem.
    unfold emitsb in E.
    assert (Hex : existsb (fun eta => match eta with
                      | ActOut (d,_) => bool_decide (d = c)
                      | _ => false end) (elements (lts_oba_mo u)) = true).
    { apply existsb_exists. exists (ActOut (c,v)). split.
      - apply list_elem_of_In. apply gmultiset_elem_of_elements. exact Hmem.
      - apply bool_decide_eq_true. reflexivity. }
    rewrite Hex in E. discriminate E.
Qed.

Definition EmitsNone (D : chset) (u : proc) : Prop :=
  forall c, D c -> ~ emits_on c u.

Inductive BadK : chset -> chset -> proc -> Prop :=
| bk_step : forall S D p p', lts p τ p' -> BadK S D p' -> BadK S D p
| bk_kill : forall S D c p (f : ValueData -> proc),
    (forall v, lts p (ActExt (ActIn (c,v))) (f v)) ->
    (forall v, BadK (fun d => S d \/ d = c) D (f v)) ->
    BadK S (fun d => D d \/ d = c) p ->
    BadK S D p
| bk_stuck : forall S D p,
    (forall q, ~ lts p τ q) ->
    (forall c v p', lts p (ActExt (ActOut (c,v))) p' -> S c) ->
    (forall c v p', lts p (ActExt (ActIn (c,v))) p' -> D c) ->
    BadK S D p.

(** Soundness is by induction on the **judgement**, not on the [must]
    derivation: [bk_kill]'s second premise is about the *same* process, so
    only the judgement decreases there.  The [bk_stuck] base case is where
    [D] pays off — every input of [p] is on a channel the client cannot
    feed, so [ex] has nothing to fire on. *)

Theorem BadK_sound : forall S D (p : proc), BadK S D p ->
  forall u, p must_pass u -> (forall q, ~ lts u τ q) -> ~ good_VACCS u ->
  RefusesIn S u -> EmitsNone D u -> False.
Proof.
  intros S D p HB. induction HB as
    [ S D p p' Hl HB IH
    | S D c p f Hf Hcont IHcont Hrest IHrest
    | S D p Hstp Hout Hin ];
    intros u Hm Hst Hng Href Hem.
  - inversion Hm as [Ho | Ho Hex0 Hpt Het Hcom]; subst; [contradiction |].
    eapply IH; [ apply Hpt; exact Hl | exact Hst | exact Hng | exact Href | exact Hem ].
  - destruct (emits_on_dec c u) as [(v & q & Hlq) | Hno].
    + inversion Hm as [Ho | Ho Hex0 Hpt Het Hcom]; subst; [contradiction |].
      assert (Hobl : (f v) must_pass q)
        by (eapply (Hcom _ _ (ActIn (c,v)) (ActOut (c,v)));
              [ reflexivity | apply Hf | exact Hlq ]).
      assert (Hsh : u ≡* ((c ! v • 𝟘) ‖ q))
        by (eapply TransitionShapeForOutputSimplified; exact Hlq).
      assert (Hstq : forall z, ~ lts q τ z).
      { intros z Hz.
        assert (Hsc : sc_then_lts u τ ((c ! v • 𝟘) ‖ z))
          by (exists ((c ! v • 𝟘) ‖ q); split; [ exact Hsh | apply lts_parR; exact Hz ]).
        apply Congruence_Respects_Transition in Hsc.
        destruct Hsc as (r & Hr & _). eapply Hst. exact Hr. }
      assert (Hngq : ~ good_VACCS q).
      { intro Hg. apply Hng. eapply good_preserved_by_cgr; [ | apply cgr_symm; exact Hsh ].
        apply good_par. right. exact Hg. }
      eapply (IHcont v q Hobl Hstq Hngq).
      * intros d x z [Hd|Hd] Hlz.
        -- assert (Hsc : sc_then_lts u ((d ▷ x)?) ((c ! v • 𝟘) ‖ z))
             by (exists ((c ! v • 𝟘) ‖ q); split; [ exact Hsh | apply lts_parR; exact Hlz ]).
           apply Congruence_Respects_Transition in Hsc.
           destruct Hsc as (r & Hr & _). eapply Href; [ exact Hd | exact Hr ].
        -- subst d.
           destruct (lts_in_value_swap q (ActIn (c,x)) z Hlz c x v eq_refl) as (z' & Hz').
           assert (Hsc : sc_then_lts u τ ((g 𝟘) ‖ z')).
           { exists ((c ! v • 𝟘) ‖ q). split; [ exact Hsh | ].
             eapply lts_comL; [ apply lts_output | exact Hz' ]. }
           apply Congruence_Respects_Transition in Hsc.
           destruct Hsc as (r & Hr & _). eapply Hst. exact Hr.
      * intros d Hd (x & z & Hlz). eapply (Hem d Hd).
        assert (Hsc : sc_then_lts u ((d ▷ x)!) ((c ! v • 𝟘) ‖ z))
          by (exists ((c ! v • 𝟘) ‖ q); split; [ exact Hsh | apply lts_parR; exact Hlz ]).
        apply Congruence_Respects_Transition in Hsc.
        destruct Hsc as (r & Hr & _). exists x, r. exact Hr.
    + eapply IHrest; [ exact Hm | exact Hst | exact Hng | exact Href | ].
      intros d [Hd|Hd]; [ exact (Hem d Hd) | subst d; exact Hno ].
  - inversion Hm as [Ho | Ho Hex0 Hpt Het Hcom]; subst; [contradiction |].
    destruct Hex0 as (z & Hz). inversion Hz; subst; unfold lts_step in *; simpl in *.
    + eapply Hstp. exact l.
    + eapply Hst. exact l.
    + destruct μ1 as [[c1 v1]|[c1 v1]].
      * destruct μ2 as [[c2 v2]|[c2 v2]]; simpl in eq; try (exfalso; exact eq).
        inversion eq; subst.
        eapply (Hem c2 (Hin c2 v2 a2 l1)). exists v2, b2. exact l2.
      * destruct μ2 as [[c2 v2]|[c2 v2]]; simpl in eq; try (exfalso; exact eq).
        inversion eq; subst.
        eapply Href; [ eapply Hout; exact l1 | exact l2 ].
Qed.


(** * The joint-removal law

    [must_i_restrict] is the semantically right move — restrict a stable
    sum's channel set in one step rather than dropping guards one at a
    time — but its third premise is the very inequation completeness is
    trying to derive, so it could never be a rule.  [BadK] is exactly
    that premise made **checkable**: "every τ-stuck, non-good client that
    emits on none of [M']'s channels is failed by [g M]" is
    [BadK ∅ (offers M') (g M)]. *)

(** [BadK] is monotone in **both** sets: enlarging [S] weakens the
    output condition of [bk_stuck], enlarging [D] weakens its input
    condition, and [bk_kill] passes both enlargements to its premises. *)

Lemma BadK_mono : forall S D p, BadK S D p ->
  forall (S' D' : chset), (forall c, S c -> S' c) -> (forall c, D c -> D' c) ->
  BadK S' D' p.
Proof.
  intros S D p HB. induction HB as
    [ S D p p' Hl HB IH
    | S D c p f Hf Hcont IHcont Hrest IHrest
    | S D p Hstp Hout Hin ];
    intros S' D' HS HD.
  - eapply bk_step; [ exact Hl | apply IH; assumption ].
  - eapply (bk_kill _ _ c _ f); [ exact Hf | | ].
    + intros v. eapply IHcont; [ | exact HD ].
      intros d [Hd|Hd]; [ left; apply HS; exact Hd | right; exact Hd ].
    + eapply IHrest; [ exact HS | ].
      intros d [Hd|Hd]; [ left; apply HD; exact Hd | right; exact Hd ].
  - apply bk_stuck.
    + exact Hstp.
    + intros c v p' Hl. apply HS. eapply Hout; exact Hl.
    + intros c v p' Hl. apply HD. eapply Hin; exact Hl.
Qed.

(** Deciding "does [u] emit on some channel of [D]?" — again from the
    finiteness of the pending-message multiset, now swept over a whole
    channel set.  [offers M'] is decidable because an input's
    availability does not depend on the value ([lts_in_value_swap]), so
    one probe at the distinguished value [O] settles it. *)

Lemma list_find_out : forall (D : chset), (forall c, D c \/ ~ D c) ->
  forall l : list (ExtAct TypeOfActions),
  (exists c v, In (ActOut (c,v)) l /\ D c)
  \/ (forall c v, In (ActOut (c,v)) l -> ~ D c).
Proof.
  intros D Hdec. induction l as [|eta l IH].
  - right. intros c v []. 
  - destruct IH as [(c & v & Hin & Hd) | Hno].
    + left. exists c, v. split; [ right; exact Hin | exact Hd ].
    + destruct eta as [[d x]|[d x]].
      * right. intros c v [He|Hin]; [ discriminate He | exact (Hno c v Hin) ].
      * destruct (Hdec d) as [Hd|Hd].
        -- left. exists d, x. split; [ left; reflexivity | exact Hd ].
        -- right. intros c v [He|Hin]; [ injection He as He1 He2; subst; exact Hd
                                       | exact (Hno c v Hin) ].
Qed.

Lemma emits_in_set_dec : forall (D : chset), (forall c, D c \/ ~ D c) ->
  forall u, (exists c, D c /\ emits_on c u) \/ EmitsNone D u.
Proof.
  intros D Hdec u.
  destruct (list_find_out D Hdec (elements (lts_oba_mo u))) as [(c & v & Hin & Hd) | Hno].
  - left. exists c. split; [ exact Hd | ].
    apply list_elem_of_In in Hin. apply gmultiset_elem_of_elements in Hin.
    destruct (lts_oba_mo_spec_bis2 u (ActOut (c,v)) Hin) as (q & _ & Hl).
    exists v, q. exact Hl.
  - right. intros c Hd (v & q & Hl). eapply (Hno c v); [ | exact Hd ].
    apply list_elem_of_In. apply gmultiset_elem_of_elements.
    eapply lts_oba_mo_spec_bis1; [ | exact Hl ].
    unfold non_blocking. simpl. unfold non_blocking_output. exists (c ▷ v). reflexivity.
Qed.

Lemma offers_dec : forall (M' : gproc) c, offers M' c \/ ~ offers M' c.
Proof.
  intros M' c. destruct (lts_dec (g M') (ActExt (ActIn (c, cst O)))) as [Hno | (q & Hq)].
  - right. intros (w & r & Hr).
    destruct (lts_in_value_swap (g M') (ActIn (c,w)) r Hr c w (cst O) eq_refl) as (r' & Hr').
    eapply Hno. exact Hr'.
  - left. exists (cst O), q. exact Hq.
Qed.

Theorem must_i_restrict_badk : forall (M M' : gproc),
  (forall al q, lts (g M') al q -> lts (g M) al q) ->
  (forall p, ~ lts (g M) τ p) ->
  BadK (fun _ => False) (offers M') (g M) ->
  (g M) ⊑ₘᵤₛₜᵢ (g M').
Proof.
  intros M M' Hsub Hst HB. apply must_i_restrict; [ exact Hsub | exact Hst | ].
  intros u Hstu Hng Hm.
  destruct (emits_in_set_dec (offers M') (offers_dec M') u) as [(c & Hoff & v & q & Hl) | Hno].
  - exists c, v, q. split; [ exact Hoff | exact Hl ].
  - exfalso. eapply BadK_sound; [ exact HB | exact Hm | exact Hstu | exact Hng | | ].
    + intros d x z Hd. contradiction.
    + exact Hno.
Qed.

(** * Building [BadK] derivations for a stable sum: the kill-list driver

    A stable guarded sum's derivation has exactly one shape: kill its
    channels one after another with [bk_kill], each time enlarging [D],
    until every input channel is in [D] and [bk_stuck] closes.  The
    driver below iterates that over an explicit list, so all a caller has
    to supply is [KillOk] — the per-channel obligations **in the order
    the list fixes**, each stated at the [D] accumulated so far.

    Order matters, and that is the whole content of the counterexample in
    [VACCS_DropProbes.v]: there [b] must be killed before [a], because
    [a]'s continuation only becomes bad once the client is known to be
    silent on [b].  The reverse order fails.  So a completeness proof for
    [BadK] on stable sums amounts to *finding* a good order — which is
    the one question still open. *)

Fixpoint gchans (M : gproc) : list ChannelData :=
match M with
| gpr_input c _ => [c]
| gpr_choice M1 M2 => gchans M1 ++ gchans M2
| _ => []
end.

Lemma gchans_complete : forall (M : gproc) c v p',
  lts (g M) (ActExt (ActIn (c,v))) p' -> In c (gchans M).
Proof.
  induction M as [ | | d P | P | M1 IH1 M2 IH2 ]; intros c v p' Hl; inversion Hl; subst.
  - left. reflexivity.
  - simpl. apply in_or_app. left. eapply IH1. eassumption.
  - simpl. apply in_or_app. right. eapply IH2. eassumption.
Qed.

Lemma gchans_offers : forall (M : gproc) c, In c (gchans M) -> offers M c.
Proof.
  induction M as [ | | d P | P | M1 IH1 M2 IH2 ]; intros c Hin; simpl in Hin.
  - contradiction.
  - contradiction.
  - destruct Hin as [He|[]]. subst d. exists (cst O), (P ^ (cst O)). apply lts_input.
  - contradiction.
  - apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    + destruct (IH1 c Hin) as (w & r & Hr). exists w, r. apply lts_choiceL. exact Hr.
    + destruct (IH2 c Hin) as (w & r & Hr). exists w, r. apply lts_choiceR. exact Hr.
Qed.

Fixpoint KillOk (M : gproc) (S D : chset) (l : list ChannelData) : Prop :=
match l with
| [] => True
| c :: l' =>
    (exists f : ValueData -> proc,
       (forall v, lts (g M) (ActExt (ActIn (c,v))) (f v))
       /\ (forall v, BadK (fun d => S d \/ d = c) D (f v)))
    /\ KillOk M S (fun d => D d \/ d = c) l'
end.

Lemma BadK_kill_list : forall (l : list ChannelData) (M : gproc) (S D : chset),
  (forall q, ~ lts (g M) τ q) ->
  (forall c v p', lts (g M) (ActExt (ActIn (c,v))) p' -> D c \/ In c l) ->
  (forall c, In c l -> offers M c) ->
  KillOk M S D l ->
  BadK S D (g M).
Proof.
  induction l as [|c l IH]; intros M S D Hst Hcov Hoff Hok.
  - apply bk_stuck.
    + exact Hst.
    + intros d x p' Hl. exfalso. eapply gsum_no_out. exact Hl.
    + intros d x p' Hl. destruct (Hcov d x p' Hl) as [Hd|[]]. exact Hd.
  - destruct Hok as ((f & Hf & Hcont) & Hok').
    eapply (bk_kill _ _ c _ f).
    + exact Hf.
    + exact Hcont.
    + apply IH; [ exact Hst | | | exact Hok' ].
      * intros d x p' Hl. destruct (Hcov d x p' Hl) as [Hd | [He|Hin]].
        -- left. left. exact Hd.
        -- left. right. symmetry. exact He.
        -- right. exact Hin.
      * intros d Hin. apply Hoff. right. exact Hin.
Qed.

(** Run at the sum's own channel list, so the coverage and existence
    premises are discharged by [gchans_complete] / [gchans_offers] and
    only [KillOk] is left to the caller. *)

Theorem BadK_stable : forall (M : gproc) (S D : chset),
  (forall q, ~ lts (g M) τ q) -> KillOk M S D (gchans M) -> BadK S D (g M).
Proof.
  intros M S D Hst Hok. eapply BadK_kill_list; [ exact Hst | | | exact Hok ].
  - intros c v p' Hl. right. eapply gchans_complete. exact Hl.
  - intros c Hin. apply gchans_offers. exact Hin.
Qed.

(** * Restricting a sum to another sum's channels

    The syntactic side of [ax_restrict]: [grestrict N M] keeps exactly
    [M]'s guards on channels [N] offers and replaces the rest by [𝟘].
    Its transitions are among [M]'s and every guard it keeps is on a
    channel [N] offers, so it is precisely the sub-sum that discharges
    [VACCS_Matching]'s [gGuardsIn] side condition — the one place the
    matching argument still asks for something. *)

Definition offersb (N : gproc) (c : ChannelData) : bool :=
  existsb (fun d => bool_decide (d = c)) (gchans N).

Lemma offersb_spec : forall N c, offersb N c = true <-> offers N c.
Proof.
  intros N c. split.
  - intro E. apply gchans_offers. unfold offersb in E.
    apply existsb_exists in E as (d & Hin & Hb).
    apply bool_decide_eq_true in Hb. subst d. exact Hin.
  - intros (w & r & Hr). unfold offersb. apply existsb_exists. exists c. split.
    + eapply gchans_complete. exact Hr.
    + apply bool_decide_eq_true. reflexivity.
Qed.

Fixpoint grestrict (N M : gproc) : gproc :=
match M with
| gpr_input c P => if offersb N c then gpr_input c P else 𝟘
| gpr_tau _ => 𝟘
| gpr_choice M1 M2 => gpr_choice (grestrict N M1) (grestrict N M2)
| _ => M
end.

Lemma grestrict_sub : forall (N M : gproc) al q,
  lts (g (grestrict N M)) al q -> lts (g M) al q.
Proof.
  induction M as [ | | c P | P | M1 IH1 M2 IH2 ]; intros al q Hl; simpl in Hl.
  - exact Hl.
  - exact Hl.
  - destruct (offersb N c) eqn:E; [ exact Hl | inversion Hl ].
  - inversion Hl.
  - inversion Hl; subst.
    + apply lts_choiceL. apply IH1. assumption.
    + apply lts_choiceR. apply IH2. assumption.
Qed.

Lemma grestrict_offered : forall (N M : gproc) c v p',
  lts (g (grestrict N M)) (ActExt (ActIn (c,v))) p' -> offers N c.
Proof.
  induction M as [ | | d P | P | M1 IH1 M2 IH2 ]; intros c v p' Hl; simpl in Hl.
  - inversion Hl.
  - inversion Hl.
  - destruct (offersb N d) eqn:E; [ | inversion Hl ].
    inversion Hl; subst. apply offersb_spec. exact E.
  - inversion Hl.
  - inversion Hl; subst.
    + eapply IH1. eassumption.
    + eapply IH2. eassumption.
Qed.

Lemma grestrict_stable : forall (N M : gproc),
  (forall q, ~ lts (g M) τ q) -> forall q, ~ lts (g (grestrict N M)) τ q.
Proof. intros N M Hst q Hl. eapply Hst. eapply grestrict_sub. exact Hl. Qed.

(** …and the restriction itself, given the certificate.

    **Scope, stated plainly.**  The certificate is *not* implied by
    [g M ⊑ₘᵤₛₜᵢ g N] in general.  With [M := a ? A] and [N := b ? B]
    (disjoint channels) the restriction would be to [𝟘], whose
    certificate is [g M ⊑ₘᵤₛₜᵢ 𝟘] — and that can fail while
    [g M ⊑ₘᵤₛₜᵢ g N] holds, because every client [M] passes may also feed
    [b] and so be caught by [N] too.  So [ax_restrict] discharges
    [gGuardsIn] exactly when the surplus guards really are useless; when
    they are not, the matching has to *keep* them, and that case is still
    open. *)

Theorem ax_restrict_to : forall (N M : gproc),
  (forall q, ~ lts (g M) τ q) ->
  BadK (fun _ => False) (offers (grestrict N M)) (g M) ->
  (g M) ⊑ₘᵤₛₜᵢ (g (grestrict N M)).
Proof.
  intros N M Hst HB. apply must_i_restrict_badk; [ | exact Hst | exact HB ].
  intros al q Hl. eapply grestrict_sub. exact Hl.
Qed.


(** ** The channel footprint of a process — first brick of the separating client

    The residue (see the note above [VACCS_Matching.ax_phaseA_direct])
    is the certificate [Settles (chans K) (P ▷ K)] at the *specific*
    [P].  Its contrapositive is the natural attack: from a **failure**
    to settle, build a τ-stuck non-good client that the left passes and
    the right fails.  The client to build is
    [Σ_{d ∉ chans K} d ? ①] — every reachable stable state emits outside
    [chans K], the client absorbs one such emission and succeeds, while
    a right-hand side emitting only within [chans K] deadlocks against
    it.

    A guarded sum is finite, so that client can only exist if the
    channels a process may ever emit on are finitely many and
    computable.  [pchans] is that footprint, and the lemmas below say it
    is one: substitution does not change it (a value is not a channel),
    no transition creates a channel, and every emission along a run is
    inside the *initial* process's footprint.

    The [ν] case is the only one with content: a channel escaping a
    restriction is shifted ([lts_res_ext] carries [VarC_action_add 1]),
    so the footprint under a [ν] is the *unshift* of the inner one —
    with the just-bound [bvar 0] dropped, since it can never escape.
    That is [resg]'s own analysis, read at the level of channel sets. *)

Definition unshiftC (Y : ChannelData) : list ChannelData :=
match Y with
| cst a => [cst a]
| bvar 0 => []
| bvar (S i) => [bvar i]
end.

Fixpoint pchans (p : proc) : list ChannelData :=
match p with
| P ‖ Q => pchans P ++ pchans Q
| pr_var _ => []
| rec _ • P => pchans P
| If _ Then P Else Q => pchans P ++ pchans Q
| c ! _ • 𝟘 => [c]
| ν P => flat_map unshiftC (pchans P)
| g M => gpchans M
end
with gpchans (M : gproc) : list ChannelData :=
match M with
| gpr_success => []
| gpr_nil => []
| gpr_input c P => c :: pchans P
| gpr_tau P => pchans P
| gpr_choice M1 M2 => gpchans M1 ++ gpchans M2
end.

Lemma pchans_subst : forall p k X, pchans (subst_in_proc k X p) = pchans p
with gpchans_subst : forall M k X, gpchans (subst_in_gproc k X M) = gpchans M.
Proof.
  - destruct p as [P Q | i | x P | C P Q | c v | P | M ]; intros k X; simpl.
    + f_equal; apply pchans_subst.
    + reflexivity.
    + apply pchans_subst.
    + f_equal; apply pchans_subst.
    + reflexivity.
    + f_equal. apply pchans_subst.
    + apply gpchans_subst.
  - destruct M as [ | | c P | P | M1 M2 ]; intros k X; simpl.
    + reflexivity.
    + reflexivity.
    + f_equal. apply pchans_subst.
    + apply pchans_subst.
    + f_equal; apply gpchans_subst.
Qed.

Lemma flat_map_unshift_mono : forall (L L' : list ChannelData),
  (forall d, In d L -> In d L') ->
  forall d, In d (flat_map unshiftC L) -> In d (flat_map unshiftC L').
Proof.
  intros L L' Hsub d Hd.
  apply in_flat_map in Hd as (y & Hy & Hd).
  apply in_flat_map. exists y. split; [ apply Hsub; exact Hy | exact Hd ].
Qed.

Lemma unshiftC_add : forall c, In c (unshiftC (VarC_add 1 c)).
Proof. intros [a|i]; simpl; left; reflexivity. Qed.

Lemma lts_pchans_target : forall p a q, Static p -> lts p a q ->
  forall d, In d (pchans q) -> In d (pchans p).
Proof.
  intros p a q Hst Hl. induction Hl; intros d Hd; simpl in *;
    try (rewrite pchans_subst in Hd);
    try (exact Hd);
    try (right; exact Hd).
  all: try (inversion Hst; subst).
  - apply in_or_app. left. apply IHHl; assumption.
  - apply in_or_app. right. apply IHHl; assumption.
  - eapply flat_map_unshift_mono; [ | exact Hd ]. intros d0 Hd0. apply IHHl; assumption.
  - eapply flat_map_unshift_mono; [ | exact Hd ]. intros d0 Hd0. apply IHHl; assumption.
  - apply in_app_or in Hd as [Hd|Hd]; apply in_or_app;
      [ left; apply IHHl1; assumption | right; apply IHHl2; assumption ].
  - apply in_app_or in Hd as [Hd|Hd]; apply in_or_app;
      [ left; apply IHHl2; assumption | right; apply IHHl1; assumption ].
  - apply in_app_or in Hd as [Hd|Hd]; apply in_or_app;
      [ left; apply IHHl; assumption | right; exact Hd ].
  - apply in_app_or in Hd as [Hd|Hd]; apply in_or_app;
      [ left; exact Hd | right; apply IHHl; assumption ].
  - apply in_or_app. left. apply IHHl; [ constructor; inversion H0; assumption | exact Hd ].
  - apply in_or_app. right. apply IHHl; [ constructor; inversion H0; assumption | exact Hd ].
Qed.

Lemma lts_pchans_out : forall p a q, Static p -> lts p a q ->
  forall c v, a = ActExt (ActOut (c,v)) -> In c (pchans p).
Proof.
  intros p a q Hst Hl. induction Hl; intros c0 v0 Ha; simpl in *;
    try discriminate Ha;
    try (inversion Hst; subst);
    try (apply in_or_app; left; eapply IHHl; eauto; fail);
    try (apply in_or_app; right; eapply IHHl; eauto; fail).
  - injection Ha as Ec Ev. subst. left. reflexivity.
  - injection Ha as Ha. subst.
    apply in_flat_map. exists (VarC_add 1 c0). split.
    + eapply IHHl; [ assumption | simpl; reflexivity ].
    + destruct c0 as [a|i]; simpl; left; reflexivity.
  - apply in_or_app. left. eapply IHHl;
      [ constructor; inversion H0; assumption | reflexivity ].
  - apply in_or_app. right. eapply IHHl;
      [ constructor; inversion H0; assumption | reflexivity ].
Qed.

Lemma wt_pchans : forall s (p q : proc), Static p -> p ⟹[s] q ->
  forall d, In d (pchans q) -> In d (pchans p).
Proof.
  intros s p q Hst Hw. induction Hw as [x|s0 x y z Hl Hwt IH|mu s0 x y z Hl Hwt IH];
    intros d Hd.
  - exact Hd.
  - eapply lts_pchans_target; [ exact Hst | exact Hl | ].
    apply IH; [ eapply Static_preserved_by_lts; [ exact Hst | exact Hl ] | exact Hd ].
  - eapply lts_pchans_target; [ exact Hst | exact Hl | ].
    apply IH; [ eapply Static_preserved_by_lts; [ exact Hst | exact Hl ] | exact Hd ].
Qed.

(** The payoff: every emission a [Static] process can ever perform, at
    any point of any run, is on a channel of its own footprint. *)

Lemma emits_in_pchans : forall s (p q r : proc) c v, Static p ->
  p ⟹[s] q -> lts q (ActExt (ActOut (c,v))) r -> In c (pchans p).
Proof.
  intros s p q r c v Hst Hw Hl.
  assert (Hq : Static q) by (eapply Static_preserved_by_wt; [ exact Hst | exact Hw ]).
  eapply wt_pchans; [ exact Hst | exact Hw | ].
  eapply lts_pchans_out; [ exact Hq | exact Hl | reflexivity ].
Qed.

(** ** L'empreinte d'ÉMISSION seule

    [pchans] compte aussi les canaux **gardés** ([gpchans (c ? P) =
    c :: pchans P]), ce qui le rend trop grossier pour un critère de
    non-régénération : il rejette [c ? (c ? 𝟘)], qui garde [c] à nouveau
    mais ne le rend jamais.  [ochans] est le même parcours **sans** cette
    ligne : il ne retient que les canaux sur lesquels un message peut
    réellement partir.

    Les trois lemmes sont ceux de [pchans], au caractère près — la seule
    différence dans les preuves est que le cas de l'entrée se ferme par
    [exact] au lieu de [right; exact], la continuation n'ajoutant plus le
    canal de sa garde. *)

Fixpoint ochans (p : proc) : list ChannelData :=
match p with
| P ‖ Q => ochans P ++ ochans Q
| pr_var _ => []
| rec _ • P => ochans P
| If _ Then P Else Q => ochans P ++ ochans Q
| c ! _ • 𝟘 => [c]
| ν P => flat_map unshiftC (ochans P)
| g M => gochans M
end
with gochans (M : gproc) : list ChannelData :=
match M with
| gpr_success => []
| gpr_nil => []
| gpr_input _ P => ochans P
| gpr_tau P => ochans P
| gpr_choice M1 M2 => gochans M1 ++ gochans M2
end.

Lemma ochans_subst : forall p k X, ochans (subst_in_proc k X p) = ochans p
with gochans_subst : forall M k X, gochans (subst_in_gproc k X M) = gochans M.
Proof.
  - destruct p as [P Q | i | x P | C P Q | c v | P | M ]; intros k X; simpl.
    + f_equal; apply ochans_subst.
    + reflexivity.
    + apply ochans_subst.
    + f_equal; apply ochans_subst.
    + reflexivity.
    + f_equal. apply ochans_subst.
    + apply gochans_subst.
  - destruct M as [ | | c P | P | M1 M2 ]; intros k X; simpl.
    + reflexivity.
    + reflexivity.
    + apply ochans_subst.
    + apply ochans_subst.
    + f_equal; apply gochans_subst.
Qed.

Lemma lts_ochans_target : forall p a q, Static p -> lts p a q ->
  forall d, In d (ochans q) -> In d (ochans p).
Proof.
  intros p a q Hst Hl. induction Hl; intros d Hd; simpl in *;
    try (rewrite ochans_subst in Hd);
    try (exact Hd);
    try (right; exact Hd).
  all: try (inversion Hst; subst).
  - apply in_or_app. left. apply IHHl; assumption.
  - apply in_or_app. right. apply IHHl; assumption.
  - eapply flat_map_unshift_mono; [ | exact Hd ]. intros d0 Hd0. apply IHHl; assumption.
  - eapply flat_map_unshift_mono; [ | exact Hd ]. intros d0 Hd0. apply IHHl; assumption.
  - apply in_app_or in Hd as [Hd|Hd]; apply in_or_app;
      [ left; apply IHHl1; assumption | right; apply IHHl2; assumption ].
  - apply in_app_or in Hd as [Hd|Hd]; apply in_or_app;
      [ left; apply IHHl2; assumption | right; apply IHHl1; assumption ].
  - apply in_app_or in Hd as [Hd|Hd]; apply in_or_app;
      [ left; apply IHHl; assumption | right; exact Hd ].
  - apply in_app_or in Hd as [Hd|Hd]; apply in_or_app;
      [ left; exact Hd | right; apply IHHl; assumption ].
  - apply in_or_app. left. apply IHHl; [ constructor; inversion H0; assumption | exact Hd ].
  - apply in_or_app. right. apply IHHl; [ constructor; inversion H0; assumption | exact Hd ].
Qed.

Lemma lts_ochans_out : forall p a q, Static p -> lts p a q ->
  forall c v, a = ActExt (ActOut (c,v)) -> In c (ochans p).
Proof.
  intros p a q Hst Hl. induction Hl; intros c0 v0 Ha; simpl in *;
    try discriminate Ha;
    try (inversion Hst; subst);
    try (apply in_or_app; left; eapply IHHl; eauto; fail);
    try (apply in_or_app; right; eapply IHHl; eauto; fail).
  - injection Ha as Ec Ev. subst. left. reflexivity.
  - injection Ha as Ha. subst.
    apply in_flat_map. exists (VarC_add 1 c0). split.
    + eapply IHHl; [ assumption | simpl; reflexivity ].
    + destruct c0 as [a|i]; simpl; left; reflexivity.
  - apply in_or_app. left. eapply IHHl;
      [ constructor; inversion H0; assumption | reflexivity ].
  - apply in_or_app. right. eapply IHHl;
      [ constructor; inversion H0; assumption | reflexivity ].
Qed.

(** ** L'empreinte d'ENTRÉE seule

    Miroir exact de [ochans] : garde le canal de chaque garde d'entrée et
    descend, un message ne contribuant rien.  [pchans] est la réunion des
    deux, ce qui le rend inutilisable pour un critère de disjonction — il
    contient trivialement [ochans].

    L'intérêt de la paire [ichans]/[ochans] est un critère de
    non-régénération qui **tolère les [𝛕]-sommants**, là où
    [VACCS_Matching.no_regen_of_own_channel] exige la τ-stabilité de la
    somme (sa preuve n'est qu'une inversion sur le premier pas du run). *)

Fixpoint ichans (p : proc) : list ChannelData :=
match p with
| P ‖ Q => ichans P ++ ichans Q
| pr_var _ => []
| rec _ • P => ichans P
| If _ Then P Else Q => ichans P ++ ichans Q
| _ ! _ • 𝟘 => []
| ν P => flat_map unshiftC (ichans P)
| g M => gichans M
end
with gichans (M : gproc) : list ChannelData :=
match M with
| gpr_success => []
| gpr_nil => []
| gpr_input c P => c :: ichans P
| gpr_tau P => ichans P
| gpr_choice M1 M2 => gichans M1 ++ gichans M2
end.

Lemma ichans_subst : forall p k X, ichans (subst_in_proc k X p) = ichans p
with gichans_subst : forall M k X, gichans (subst_in_gproc k X M) = gichans M.
Proof.
  - destruct p as [P Q | i | x P | C P Q | c v | P | M ]; intros k X; simpl.
    + f_equal; apply ichans_subst.
    + reflexivity.
    + apply ichans_subst.
    + f_equal; apply ichans_subst.
    + reflexivity.
    + f_equal. apply ichans_subst.
    + apply gichans_subst.
  - destruct M as [ | | c P | P | M1 M2 ]; intros k X; simpl.
    + reflexivity.
    + reflexivity.
    + f_equal. apply ichans_subst.
    + apply ichans_subst.
    + f_equal; apply gichans_subst.
Qed.

Lemma lts_ichans_target : forall p a q, Static p -> lts p a q ->
  forall d, In d (ichans q) -> In d (ichans p).
Proof.
  intros p a q Hst Hl. induction Hl; intros d Hd; simpl in *;
    try (rewrite ichans_subst in Hd);
    try (exact Hd);
    try (right; exact Hd).
  all: try (inversion Hst; subst).
  - apply in_or_app. left. apply IHHl; assumption.
  - apply in_or_app. right. apply IHHl; assumption.
  - eapply flat_map_unshift_mono; [ | exact Hd ]. intros d0 Hd0. apply IHHl; assumption.
  - eapply flat_map_unshift_mono; [ | exact Hd ]. intros d0 Hd0. apply IHHl; assumption.
  - apply in_app_or in Hd as [Hd|Hd]; apply in_or_app;
      [ left; apply IHHl1; assumption | right; apply IHHl2; assumption ].
  - apply in_app_or in Hd as [Hd|Hd]; apply in_or_app;
      [ left; apply IHHl2; assumption | right; apply IHHl1; assumption ].
  - apply in_app_or in Hd as [Hd|Hd]; apply in_or_app;
      [ left; apply IHHl; assumption | right; exact Hd ].
  - apply in_app_or in Hd as [Hd|Hd]; apply in_or_app;
      [ left; exact Hd | right; apply IHHl; assumption ].
  - apply in_or_app. left. apply IHHl; [ constructor; inversion H0; assumption | exact Hd ].
  - apply in_or_app. right. apply IHHl; [ constructor; inversion H0; assumption | exact Hd ].
Qed.

Lemma lts_ichans_in : forall p a q, Static p -> lts p a q ->
  forall c v, a = ActExt (ActIn (c,v)) -> In c (ichans p).
Proof.
  intros p a q Hst Hl. induction Hl; intros c0 v0 Ha; simpl in *;
    try discriminate Ha;
    try (inversion Hst; subst);
    try (apply in_or_app; left; eapply IHHl; eauto; fail);
    try (apply in_or_app; right; eapply IHHl; eauto; fail).
  - injection Ha as Ec Ev. subst. left. reflexivity.
  - injection Ha as Ha. subst.
    apply in_flat_map. exists (VarC_add 1 c0). split.
    + eapply IHHl; [ assumption | simpl; reflexivity ].
    + destruct c0 as [a|i]; simpl; left; reflexivity.
  - apply in_or_app. left. eapply IHHl;
      [ constructor; inversion H0; assumption | reflexivity ].
  - apply in_or_app. right. eapply IHHl;
      [ constructor; inversion H0; assumption | reflexivity ].
Qed.

Lemma wt_ichans : forall s (p q : proc), Static p -> p ⟹[s] q ->
  forall d, In d (ichans q) -> In d (ichans p).
Proof.
  intros s p q Hst Hw. induction Hw as [x|s0 x y z Hl Hwt IH|mu s0 x y z Hl Hwt IH];
    intros d Hd.
  - exact Hd.
  - eapply lts_ichans_target; [ exact Hst | exact Hl | ].
    apply IH; [ eapply Static_preserved_by_lts; [ exact Hst | exact Hl ] | exact Hd ].
  - eapply lts_ichans_target; [ exact Hst | exact Hl | ].
    apply IH; [ eapply Static_preserved_by_lts; [ exact Hst | exact Hl ] | exact Hd ].
Qed.

Lemma wt_ochans : forall s (p q : proc), Static p -> p ⟹[s] q ->
  forall d, In d (ochans q) -> In d (ochans p).
Proof.
  intros s p q Hst Hw. induction Hw as [x|s0 x y z Hl Hwt IH|mu s0 x y z Hl Hwt IH];
    intros d Hd.
  - exact Hd.
  - eapply lts_ochans_target; [ exact Hst | exact Hl | ].
    apply IH; [ eapply Static_preserved_by_lts; [ exact Hst | exact Hl ] | exact Hd ].
  - eapply lts_ochans_target; [ exact Hst | exact Hl | ].
    apply IH; [ eapply Static_preserved_by_lts; [ exact Hst | exact Hl ] | exact Hd ].
Qed.

(** ** [ochans p ⊆ S] certifie [Bad S p]

    Le champ [ex] de [must] réclame un pas de la paire ; si le serveur
    n'émet que sur des voies **déjà refusées** par le client, la clause de
    sortie de [bad_stuck] est satisfaite d'emblée.  Les entrées se
    traitent par récurrence : le résidu hérite du critère
    ([lts_ochans_target]) et décroît en taille, l'ensemble ne faisant que
    grandir.

    Le critère unifie trois lois de drop qui existaient séparément :

    - [ochans P = []] — le puits, à profondeur libre ([ax_swallow] en est
      le cas [P := 𝟘]) ;
    - [ochans P ⊆ {c}] — le **copycat** et le **répondeur**, dont la
      continuation ne réémet que sur la voie de la garde.

    Conséquence pratique : un critère purement syntaxique, indépendant de
    la valeur reçue ([ochans_subst]), alimente [ax_input_drop] — donc il
    atteint les **dérivations** et pas seulement la sémantique. *)

Lemma ochans_sub_Bad_aux : forall n (p : proc), size p < n -> Static p ->
  forall S, (forall d, In d (ochans p) -> S d) -> Bad S p.
Proof.
  induction n as [|n IH]; intros p Hsz Hst S Hsub; [ lia | ].
  destruct (lts_dec p τ) as [Hno | (q & Hq)].
  - apply bad_stuck.
    + exact Hno.
    + intros c v p' Hl. apply Hsub.
      eapply lts_ochans_out; [ exact Hst | exact Hl | reflexivity ].
    + intros c v p' Hl. exists p'. split; [ exact Hl | ].
      eapply IH.
      * assert (Hd : size p' < size p)
          by (eapply Static_lts_decrease; eassumption). lia.
      * eapply Static_preserved_by_lts; eassumption.
      * intros d Hd. left. apply Hsub.
        eapply lts_ochans_target; [ exact Hst | exact Hl | exact Hd ].
  - eapply bad_step; [ exact Hq | ].
    eapply IH.
    + assert (Hd : size q < size p)
        by (eapply Static_lts_decrease; eassumption). lia.
    + eapply Static_preserved_by_lts; eassumption.
    + intros d Hd. apply Hsub.
      eapply lts_ochans_target; [ exact Hst | exact Hq | exact Hd ].
Qed.

Theorem ochans_sub_Bad : forall (p : proc) (S : chset), Static p ->
  (forall d, In d (ochans p) -> S d) -> Bad S p.
Proof.
  intros p S Hst Hsub.
  eapply (ochans_sub_Bad_aux (Datatypes.S (size p))); try eassumption. lia.
Qed.

Corollary no_output_Bad : forall (p : proc), Static p -> ochans p = [] ->
  forall Sc, Bad Sc p.
Proof.
  intros p Hst Hoc Sc. apply ochans_sub_Bad; [ exact Hst | ].
  intros d Hd. rewrite Hoc in Hd. contradiction.
Qed.

End VACCS_Absorb.
