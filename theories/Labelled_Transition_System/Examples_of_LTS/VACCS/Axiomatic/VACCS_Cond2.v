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

(** * Cashing in [⊑ₘᵤₛₜᵢ]: the acceptance condition, with the forwarder gone

    [must_iff_acceptance_set_VACCS] states everything at [p ▷ ∅], and
    [VACCS_ReadySet.v] explains why that is not optional.  But
    [VACCS_Forwarder.v]'s transparency result says the forwarder is
    invisible along **input-free** traces, and the empty trace is one.  So
    at [ε] the acceptance condition can be read entirely at the level of
    bare processes:

        must_i_cond2_nil :  p ⊑ₘᵤₛₜᵢ q ->
          ∀ q₁, q ⟹ q₁ -> q₁ ↛ ->
          ∃ p₁, p ⟹ p₁ ∧ p₁ ↛ ∧ (every channel p₁ emits on, q₁ emits on)

    — the ready-set inclusion having collapsed, by [VACCS_ReadySet.v], to
    an inclusion of *emittable channels*.

    ** And input observation needs no forwarder either

    The other half of the acceptance condition — traces that carry inputs —
    does not need to be handled at the forwarder at all, because in an
    asynchronous calculus **feeding an input is definable in the syntax**:
    [must_i_feed] below is one line from [must_i_par_compat_r], and
    [(c!v•𝟘) ‖ p] delivers the message to [p]'s input on [c] by an ordinary
    [τ].  So an input-bearing observation turns into a *fresh* [⊑ₘᵤₛₜᵢ]
    between [Static] processes, to be read at [ε] again.

    That is why the buffer, though essential to the *semantics* (a guarded
    sum's ready set is empty — [gproc_coR_empty]), need never appear in a
    *derivation*. *)

From Stdlib Require Import List PeanoNat Lia.
From stdpp Require Import base sets gmap gmultiset.
From TestingTheory Require Import VACCS VACCS_Instance Must ActTau InputOutputActions
  gLts Bisimulation InteractionBetweenLts Testing_Predicate VACCS_Good WeakTransitions
  Subset_Act DefinitionAS Convergence Termination MultisetLTSConstruction ForwarderConstruction
  Lts_OBA Lts_FW Lts_OBA_FB VACCS_Static VACCS_Must_Characterization
  VACCS_Erasure VACCS_Precongruence VACCS_Expansion VACCS_Forwarder
  DefinitionCI EquivalenceCI VACCS_ta_tc_gen Soundness Completeness.

Section VACCS_Cond2.

Context `{VP : VACCS_Parameters}.

(** Typeclass resolution for [terminate]/[cnv] at the pair type diverges at
    the default depth; capping it fixes the elaboration.  (Everything else
    at the pair type — [⟶], [⟹], [↛] — is fine, because there the instance
    is pinned by a surrounding [inter_step].) *)
Set Typeclasses Depth 3.

Lemma empty_not_disj : forall a (m' : MO (ExtAct TypeOfActions)),
  (∅ : MO (ExtAct TypeOfActions)) = {[+ ActOut a +]} ⊎ m' -> False.
Proof.
  intros a m' Hm.
  assert (Hc : ActOut a ∈ ({[+ ActOut a +]} ⊎ m'))
    by (apply gmultiset_elem_of_disj_union; left; apply gmultiset_elem_of_singleton; reflexivity).
  rewrite <- Hm in Hc. apply gmultiset_elem_of_empty in Hc. exact Hc.
Qed.

(** Convergence at [ε], which is [bhv_pre_cond2]'s premise: an empty buffer
    can never fill, so the forwarder's [τ]-successors are the process's. *)
Lemma fw_nil_terminate : forall (p : proc), p ⤓ -> (p ▷ ∅) ⤓.
Proof.
  intros p H. induction H as [p Hall IH].
  constructor. intros x Hx. destruct x as (p1,m1).
  destruct (fw_tau_shape p ∅ (p1,m1) Hx) as [HA|HB].
  - destruct HA as (p' & Hp' & E). inversion E; subst. apply IH. exact Hp'.
  - destruct HB as (a & p' & m' & Hm & _ & _). exfalso. eapply empty_not_disj. exact Hm.
Qed.

Lemma fw_nil_stable_iff : forall (p : proc), (p ▷ ∅) ↛ <-> p ↛.
Proof.
  intro p. split.
  - intro H. destruct (decide (lts_refuses p τ)) as [Hy|Hn]; [exact Hy | ].
    exfalso. apply lts_refuses_spec1 in Hn as (q & Hq).
    apply (@lts_refuses_spec2 (proc * MO (ExtAct TypeOfActions)) _ _ _ (p ▷ ∅) τ); [ | exact H ].
    exists (q ▷ ∅). apply fw_tau_left. exact Hq.
  - intro H. destruct (decide (lts_refuses (p ▷ ∅) τ)) as [Hy|Hn]; [exact Hy | ].
    exfalso. apply lts_refuses_spec1 in Hn as ((p1,m1) & Hq).
    destruct (fw_tau_shape p ∅ (p1,m1) Hq) as [HA|HB].
    + destruct HA as (p' & Hp' & E).
      apply (@lts_refuses_spec2 proc _ _ _ p τ); [ | exact H ].
      exists p'. exact Hp'.
    + destruct HB as (a & p' & m' & Hm & _ & _). eapply empty_not_disj. exact Hm.
Qed.

(** ** The acceptance condition at the empty trace, on bare processes *)

Theorem must_i_cond2_nil : forall (p q : proc), Static p -> Static q ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
  forall q1, q ⟹ q1 -> q1 ↛ ->
  exists p1, p ⟹ p1 /\ p1 ↛ /\
    (forall c, (exists v r, lts p1 (ActExt (ActOut (c,v))) r) ->
               (exists v r, lts q1 (ActExt (ActOut (c,v))) r)).
Proof.
  intros p q Hp Hq Hpq q1 Hw Hst.
  apply must_iff_acceptance_set_VACCS in Hpq as (Hc1 & Hc2).
  assert (Hcnv : (p ▷ ∅) ⇓ []).
  { apply cnv_nil. apply fw_nil_terminate. apply Static_terminate. exact Hp. }
  assert (Hwq : (q ▷ ∅) ⟹[[]] (q1 ▷ ∅)) by (apply fw_wt_lift; exact Hw).
  assert (Hstq : (q1 ▷ ∅) ↛) by (apply fw_nil_stable_iff; exact Hst).
  destruct (Hc2 [] (q1 ▷ ∅) Hcnv Hwq Hstq) as (x & Hwx & Hstx & Hincl).
  destruct x as (p1,m1).
  destruct (fw_reach_noinput [] p p1 m1 eq_refl Hwx) as (Hm & Hwp).
  subst m1.
  exists p1. split; [ exact Hwp | ].
  split; [ apply (proj1 (fw_nil_stable_iff p1)); exact Hstx | ].
  intros c (v & r & Hr).
  assert (Hin : (Inputs c) ∈ ⌈ 𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ ⌉ (coR (p1 ▷ ∅))).
  { exists (ActIn (c,v)). split; [ | reflexivity ].
    exists (ActOut (c,v)). repeat split.
    + intro Hst2. eapply (@lts_refuses_spec2 (proc * MO (ExtAct TypeOfActions)) _ _ _
                            (p1 ▷ ∅) (ActExt (ActOut (c,v)))); [ | exact Hst2 ].
      exists (r ▷ ∅). apply fw_ext_left. exact Hr.
    + unfold non_blocking_output, is_output. intros (b & Hb). discriminate Hb. }
  apply Hincl in Hin. destruct Hin as (mu & Hmu & Heq).
  destruct mu as [[c0 v0]|[c0 v0]]; simpl in Heq.
  - inversion Heq; subst.
    destruct Hmu as (mu2 & Hnr & Hd & _).
    destruct mu2 as [[d w]|[d w]]; simpl in Hd; [ exact (match Hd with end) | ].
    inversion Hd; subst.
    apply lts_refuses_spec1 in Hnr as ((r1,m2) & Hr1).
    destruct (fw_ext_shape q1 ∅ (ActOut (c0,v0)) (r1,m2) Hr1) as [HA|[HB|HC]].
    + destruct HA as (r' & Hr' & _). exists v0, r'. exact Hr'.
    + destruct HB as (b & Hb & _). discriminate Hb.
    + destruct HC as (b & m' & _ & Hm & _). exfalso. eapply empty_not_disj. exact Hm.
  - exfalso. destruct Hmu as (mu2 & _ & _ & Hb).
    unfold non_blocking_output, is_output in Hb. apply Hb. eexists; reflexivity.
Qed.

(** ** Input observation, syntactically

    One line, and it is what removes the need for [bhv_pre_cond2] at
    input-bearing traces. *)

Lemma must_i_feed : forall c v (p q : proc),
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> ((c ! v • 𝟘) ‖ p) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((c ! v • 𝟘) ‖ q).
Proof. intros c v p q H. apply must_i_par_compat_r. exact H. Qed.

(** * The acceptance condition at an INPUT-bearing trace

    [must_i_feed] above collapses an input observation back to [ε] by
    putting the message in parallel.  That is cheap and sound, but it
    **throws away exactly the information about input guards** — which is
    what the surplus-guard problem needs.  The right move, and the one
    VCCS's completeness proof makes, is to read [bhv_pre_cond2] at the
    trace that feeds the message and keep the buffer.

    (Both readings are legitimate: [Lift.must_iff_must_fw] says [p] and
    [FW p] pass exactly the same tests, so nothing is lost by working at
    the forwarder — and forwarder states need no new syntax, since
    [p ▷ m] behaves as [p ‖ msgs m], which is why the normal form is
    already [Ѵⁿ (msgs l ‖ g M)].)

    Why this is the informative reading: a *bare* guarded sum's abstracted
    ready set is empty ([VACCS_ReadySet.gproc_coR_empty]), so [cond2] at
    [ε] constrains nothing.  At the forwarder the ready set is the set of
    channels carrying a pending message, so feeding one and looking at
    what comes back out is precisely where a stable sum's input guards
    become observable. *)

(** ** Convergence at an arbitrary buffer

    [cond2]'s premise is convergence along the trace, and on the [Static]
    fragment it holds at *any* buffer: a [τ] is either the process's own
    or a delivery, and both shrink [size] of the process component
    ([Static_lts_decrease]) — the buffer never needs to be measured. *)

Lemma fw_static_tau : forall (p : proc) (m : MO (ExtAct TypeOfActions)) x,
  Static p -> (p ▷ m) ⟶ x -> Static x.1 /\ (size x.1 < size p)%nat.
Proof.
  intros p m x HS Hl. destruct (fw_tau_shape p m x Hl) as [HA|HB].
  - destruct HA as (r & Hr & E). subst x. simpl. split.
    + eapply Static_preserved_by_lts; eassumption.
    + eapply Static_lts_decrease; eassumption.
  - destruct HB as (a & r & m0 & Hm & Hr & E). subst x. simpl. split.
    + eapply Static_preserved_by_lts; eassumption.
    + eapply Static_lts_decrease; eassumption.
Qed.

Lemma fw_terminate_static : forall n (p : proc) (m : MO (ExtAct TypeOfActions)),
  Static p -> (size p <= n)%nat -> (p ▷ m) ⤓.
Proof.
  induction n as [|n IH]; intros p m HS Hn; constructor; intros x Hx.
  - exfalso. destruct (fw_static_tau p m x HS Hx) as (_ & Hlt). lia.
  - destruct (fw_static_tau p m x HS Hx) as (HSx & Hlt).
    destruct x as (p1,m1). simpl in *. apply IH; [ exact HSx | lia ].
Qed.

Lemma fw_static_ext : forall (p : proc) (m : MO (ExtAct TypeOfActions)) mu x,
  Static p -> (p ▷ m) ⟶[mu] x -> Static x.1.
Proof.
  intros p m mu x HS Hl. destruct (fw_ext_shape p m mu x Hl) as [HA|[HB|HC]].
  - destruct HA as (r & Hr & E). subst x. simpl. eapply Static_preserved_by_lts; eassumption.
  - destruct HB as (a & _ & E). subst x. simpl. exact HS.
  - destruct HC as (a & m' & _ & _ & E). subst x. simpl. exact HS.
Qed.

Lemma fw_static_wt : forall s (x y : proc * MO (ExtAct TypeOfActions)),
  Static x.1 -> x ⟹[s] y -> Static y.1.
Proof.
  intros s x y HS Hw. induction Hw as [z|s1 z r w Hl Hwt IH|mu s1 z r w Hl Hwt IH].
  - exact HS.
  - apply IH. destruct (fw_static_tau z.1 z.2 r) as (Hr & _); [ exact HS | | exact Hr ].
    destruct z as (z1,z2). exact Hl.
  - apply IH. destruct z as (z1,z2). eapply fw_static_ext; [ exact HS | exact Hl ].
Qed.

Theorem fw_converge_static : forall s (p : proc) (m : MO (ExtAct TypeOfActions)),
  Static p -> (p ▷ m) ⇓ s.
Proof.
  induction s as [|mu s IH]; intros p m HS.
  - apply cnv_nil. eapply fw_terminate_static; [ exact HS | apply le_n ].
  - apply cnv_act.
    + eapply fw_terminate_static; [ exact HS | apply le_n ].
    + intros q Hq. destruct q as (q1,m1).
      apply IH. eapply (fw_static_wt [mu] (p ▷ m) (q1 ▷ m1)); [ exact HS | exact Hq ].
Qed.

(** ** The condition itself

    Read [cond2] at the trace [[c?]] — [fw_wt_feed] turns a run of
    [q ▷ {c!v}] into one of [q ▷ ∅] over that trace — and unfold the
    abstracted ready-set inclusion into "every channel the left-hand
    stable state can emit on, the right-hand one can too".

    Compare [must_i_cond2_nil]: same shape, but the buffer is no longer
    empty, so the conclusion says something about what the *continuation*
    of an input guard gives back, which at [ε] it cannot. *)

Theorem must_i_cond2_in : forall (p q : proc) c v, Static p -> Static q ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
  forall y, (q ▷ ({[+ ActOut (c,v) +]} : MO (ExtAct TypeOfActions))) ⟹[[]] y -> y ↛ ->
  exists x, (p ▷ (∅ : MO (ExtAct TypeOfActions))) ⟹[[ActIn (c,v)]] x /\ x ↛ /\
    (forall d, (exists w r, x ⟶[ActOut (d,w)] r) ->
               (exists w r, y ⟶[ActOut (d,w)] r)).
Proof.
  intros p q c v Hp Hq Hpq y Hwy Hsty.
  apply must_iff_acceptance_set_VACCS in Hpq as (Hc1 & Hc2).
  assert (Hcnv : (p ▷ (∅ : MO (ExtAct TypeOfActions))) ⇓ [ActIn (c,v)])
    by (apply fw_converge_static; exact Hp).
  assert (Hwq : (q ▷ (∅ : MO (ExtAct TypeOfActions))) ⟹[[ActIn (c,v)]] y).
  { rewrite <- (gmultiset_disj_union_right_id ({[+ ActOut (c,v) +]} : MO (ExtAct TypeOfActions))) in Hwy.
    eapply fw_wt_feed. exact Hwy. }
  destruct (Hc2 [ActIn (c,v)] y Hcnv Hwq Hsty) as (x & Hwx & Hstx & Hincl).
  exists x. split; [ exact Hwx | ]. split; [ exact Hstx | ].
  intros d (w & r & Hr).
  assert (Hin : (Inputs d) ∈ ⌈ 𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ ⌉ (coR x)).
  { exists (ActIn (d,w)). split; [ | reflexivity ].
    exists (ActOut (d,w)). repeat split.
    + intro Hst2. eapply (@lts_refuses_spec2 (proc * MO (ExtAct TypeOfActions)) _ _ _
                            x (ActExt (ActOut (d,w)))); [ | exact Hst2 ].
      exists r. exact Hr.
    + unfold non_blocking_output, is_output. intros (b & Hb). discriminate Hb. }
  apply Hincl in Hin. destruct Hin as (mu & Hmu & Heq).
  destruct mu as [[d0 w0]|[d0 w0]]; simpl in Heq.
  - inversion Heq; subst.
    destruct Hmu as (mu2 & Hnr & Hd & _).
    destruct mu2 as [[e1 x1]|[e1 x1]]; simpl in Hd; [ exact (match Hd with end) | ].
    inversion Hd; subst.
    apply lts_refuses_spec1 in Hnr as (z & Hz). exists w0, z. exact Hz.
  - exfalso. destruct Hmu as (mu2 & _ & _ & Hb).
    unfold non_blocking_output, is_output in Hb. apply Hb. eexists; reflexivity.
Qed.

(** ** Feeding is reversible — the converse of [fw_wt_feed]

    A run of [p ▷ ∅] over the trace [[a?]] is always a run of
    [p ▷ {a!}] over [ε].  The input step is either the buffer absorbing
    (in which case the two states already coincide) or [p]'s own input
    (in which case the buffered message is delivered by a [τ] instead) —
    and the surrounding [τ]s are available with the extra message
    present, since a delivery of some *other* message is unaffected by it.

    With this, [must_i_cond2_in] can be read entirely in terms of
    [p ▷ {c!v}], i.e. of "hand the process a message and watch": no trace
    reasoning is left in the statement. *)

Lemma mo_swap : forall (X Y Z : MO (ExtAct TypeOfActions)), X ⊎ (Y ⊎ Z) = Y ⊎ (X ⊎ Z).
Proof.
  intros X Y Z.
  rewrite (assoc_L (@disj_union (MO (ExtAct TypeOfActions)) _)).
  rewrite (comm_L (@disj_union (MO (ExtAct TypeOfActions)) _) X Y).
  rewrite <- (assoc_L (@disj_union (MO (ExtAct TypeOfActions)) _)).
  reflexivity.
Qed.

Lemma fw_feed_inv : forall (x y : proc * MO (ExtAct TypeOfActions)) a,
  x ⟹[[ActIn a]] y -> (x.1 ▷ ({[+ ActOut a +]} ⊎ x.2)) ⟹[[]] y.
Proof.
  intros x y a Hw. remember [ActIn a] as s0 eqn:Hs. revert a Hs.
  induction Hw as [z|s1 z r w Hl Hwt IH|mu s1 z r w Hl Hwt IH]; intros a Hs.
  - discriminate Hs.
  - specialize (IH a Hs).
    destruct (fw_tau_shape z.1 z.2 r) as [HA|HB]; [ destruct z as (z1,z2); exact Hl | | ].
    + destruct HA as (p' & Hp' & E). subst r. simpl in *.
      eapply wt_tau; [ | exact IH ]. apply fw_tau_left. exact Hp'.
    + destruct HB as (b & p' & m' & Hm & Hp' & E). subst r. simpl in *.
      eapply wt_tau; [ | exact IH ].
      rewrite Hm. rewrite mo_swap. apply fw_tau_deliver. exact Hp'.
  - injection Hs as Hmu Hs1. subst mu s1.
    destruct (fw_ext_shape z.1 z.2 (ActIn a) r) as [HA|[HB|HC]];
      [ destruct z as (z1,z2); exact Hl | | | ].
    + destruct HA as (p' & Hp' & E). subst r. simpl in *.
      eapply wt_tau; [ apply fw_tau_deliver; exact Hp' | exact Hwt ].
    + destruct HB as (b & Hb & E). injection Hb as Hb. subst b. subst r.
      simpl in *. exact Hwt.
    + destruct HC as (b & m' & Hb & _ & _). discriminate Hb.
Qed.

(** The acceptance condition, stated purely as "hand both sides the same
    message and compare what they can still emit". *)

Corollary must_i_cond2_fed : forall (p q : proc) c v, Static p -> Static q ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
  forall y, (q ▷ ({[+ ActOut (c,v) +]} : MO (ExtAct TypeOfActions))) ⟹[[]] y -> y ↛ ->
  exists x, (p ▷ ({[+ ActOut (c,v) +]} : MO (ExtAct TypeOfActions))) ⟹[[]] x /\ x ↛ /\
    (forall d, (exists w r, x ⟶[ActOut (d,w)] r) ->
               (exists w r, y ⟶[ActOut (d,w)] r)).
Proof.
  intros p q c v Hp Hq Hpq y Hwy Hsty.
  destruct (must_i_cond2_in p q c v Hp Hq Hpq y Hwy Hsty) as (x & Hwx & Hstx & Hincl).
  exists x. split; [ | split; [ exact Hstx | exact Hincl ] ].
  pose proof (fw_feed_inv (p ▷ (∅ : MO (ExtAct TypeOfActions))) x (c,v) Hwx) as H.
  simpl in H.
  replace ({[+ ActOut (c,v) +]} : MO (ExtAct TypeOfActions))
    with (({[+ ActOut (c,v) +]} : MO (ExtAct TypeOfActions)) ⊎ ∅)
    by (apply gmultiset_disj_union_right_id).
  exact H.
Qed.

(** * What the semantics says about a SURPLUS guard, in reachability form

    Take stable sums with `g M ⊑ₘᵤₛₜᵢ g N` and a channel [c] that [M]
    offers and [N] does not.  Hand both sides the message [c!v].  The
    right-hand state [g N ▷ {c!v}] is *stable* — [N] has no [τ] and
    refuses [c], so the message just sits there — and the only channel it
    can emit on is [c].  So [must_i_cond2_fed] forces the left-hand side
    to settle likewise:

        from [g M ▷ {c!v}], reach a stable state that can emit only on [c].

    **This is the surplus-guard obligation in its acceptance-set form, and
    it is ∃/reachability-shaped** — "some run settles well" — where the
    client-side formulation was ∀-over-clients ("every client fails").
    On [VACCS_DropProbes.v]'s counterexample the client-side version is
    *false* ([no_drop_target_for_a]) while this one is *true*: the
    delivery reaches [PP ▷ ∅], stable and emitting nothing.

    That is the shape an inductive judgement can carry — [bk_step] and
    [bk_stuck] are already reachability-shaped — so this is the condition
    the kill-list obligations should be restated against. *)

Lemma gsum_no_output : forall (N : gproc) d w r,
  ~ lts (g N) (ActExt (ActOut (d,w))) r.
Proof.
  induction N as [ | | c0 P | P | N1 IH1 N2 IH2 ]; intros d w r Hl; inversion Hl; subst.
  - eapply IH1. eassumption.
  - eapply IH2. eassumption.
Qed.

Theorem surplus_settles : forall (M N : gproc) c v, gStatic M -> gStatic N ->
  (forall p, ~ lts (g N) τ p) ->
  (forall w r, ~ lts (g N) (ActExt (ActIn (c,w))) r) ->
  (g M) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (g N) ->
  exists x, ((g M) ▷ ({[+ ActOut (c,v) +]} : MO (ExtAct TypeOfActions))) ⟹[[]] x
         /\ x ↛
         /\ (forall d w r, x ⟶[ActOut (d,w)] r -> d = c).
Proof.
  intros M N c v HM HN HstN Hnoc Hsem.
  assert (Hsty : ((g N) ▷ ({[+ ActOut (c,v) +]} : MO (ExtAct TypeOfActions))) ↛).
  { assert (Hnostep : forall x,
      ~ (((g N) ▷ ({[+ ActOut (c,v) +]} : MO (ExtAct TypeOfActions))) ⟶ x)).
    { apply fw_stable_iff. split; [ exact HstN | ].
      intros a Hin q Hq. apply gmultiset_elem_of_singleton in Hin.
      injection Hin as Hin. subst a. eapply Hnoc. exact Hq. }
    destruct (decide (lts_refuses ((g N) ▷ ({[+ ActOut (c,v) +]} : MO (ExtAct TypeOfActions))) τ))
      as [Hy|Hn]; [ exact Hy | ].
    exfalso. apply lts_refuses_spec1 in Hn as (x & Hx). eapply Hnostep. exact Hx. }
  destruct (must_i_cond2_fed (g M) (g N) c v (static_g M HM) (static_g N HN) Hsem
              ((g N) ▷ ({[+ ActOut (c,v) +]} : MO (ExtAct TypeOfActions)))
              (wt_nil _) Hsty) as (x & Hwx & Hstx & Hincl).
  exists x. split; [ exact Hwx | ]. split; [ exact Hstx | ].
  intros d w r Hr.
  destruct (Hincl d (ex_intro _ w (ex_intro _ r Hr))) as (w0 & r0 & Hr0).
  destruct (fw_ext_shape (g N) _ (ActOut (d,w0)) r0 Hr0) as [HA|[HB|HC]].
  - destruct HA as (r' & Hr' & _). exfalso. eapply gsum_no_output. exact Hr'.
  - destruct HB as (a & Ha & _). discriminate Ha.
  - destruct HC as (a & m' & Ha & Hm & _). injection Ha as Ha. subst a.
    assert (Hin : ActOut (d,w0) ∈ ({[+ ActOut (c,v) +]} : MO (ExtAct TypeOfActions))).
    { rewrite Hm. apply gmultiset_elem_of_disj_union. left.
      apply gmultiset_elem_of_singleton. reflexivity. }
    apply gmultiset_elem_of_singleton in Hin. injection Hin as Hin. congruence.
Qed.

(** * [Settles] — the reachability predicate the obligations should use

    "[x] can reach, by internal steps alone, a stable state whose pending
    outputs all lie on channels in [S]".

    Contrast with [VACCS_Absorb.BadK]: that is a *client-side* predicate
    ("fails every client of such and such a shape"), inductively
    presentable but strictly stronger than the semantics requires — which
    is why its per-channel obligations force the [KillOk] ordering
    problem.  [Settles] is what [bhv_pre_cond2] actually hands over
    ([surplus_Settles]), it is ∃-shaped, and it is closed under exactly
    the two moves an inductive judgement needs: prefixing a [τ]
    ([Settles_tau]) and stopping at a stable state ([Settles_here]). *)


Lemma Settles_mono : forall (S S' : ChannelData -> Prop) x,
  (forall d, S d -> S' d) -> Settles S x -> Settles S' x.
Proof.
  intros S S' x Hsub (y & Hw & Hst & He). exists y.
  split; [ exact Hw | ]. split; [ exact Hst | ].
  intros d w r Hr. apply Hsub. eapply He. exact Hr.
Qed.

Lemma Settles_tau : forall (S : ChannelData -> Prop) x x',
  x ⟶ x' -> Settles S x' -> Settles S x.
Proof.
  intros S x x' Hl (y & Hw & Hst & He). exists y.
  split; [ eapply wt_tau; [ exact Hl | exact Hw ] | ].
  split; [ exact Hst | exact He ].
Qed.

Lemma Settles_here : forall (S : ChannelData -> Prop) x,
  x ↛ -> (forall d w r, x ⟶[ActOut (d,w)] r -> S d) -> Settles S x.
Proof.
  intros S x Hst He. exists x. split; [ apply wt_nil | ]. split; [ exact Hst | exact He ].
Qed.

(** [surplus_settles], restated: a surplus guard's obligation *is* a
    [Settles] fact, handed over by the semantics. *)

Corollary surplus_Settles : forall (M N : gproc) c v, gStatic M -> gStatic N ->
  (forall p, ~ lts (g N) τ p) ->
  (forall w r, ~ lts (g N) (ActExt (ActIn (c,w))) r) ->
  (g M) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (g N) ->
  Settles (fun d => d = c) ((g M) ▷ ({[+ ActOut (c,v) +]} : MO (ExtAct TypeOfActions))).
Proof.
  intros M N c v HM HN HstN Hnoc Hsem.
  destruct (surplus_settles M N c v HM HN HstN Hnoc Hsem) as (x & Hw & Hst & He).
  exists x. split; [ exact Hw | ]. split; [ exact Hst | ].
  intros d w r Hr. eapply He. exact Hr.
Qed.

(** * A settling simulation, and the preorder from it

    [bhv_pre_cond2] quantifies over *all* traces, so a per-channel
    [Settles] fact is not by itself enough to justify a rule.  What is
    enough is a **simulation carrying [Settles] at the stable states**:

      [SettleSim R] :=
        - a [τ] of the right is matched by internal steps of the left,
        - a visible step of the right is matched by the same visible step
          of the left,
        - and wherever the right is *stable*, the left [Settles] within
          the channels the right can emit on.

    [settle_sim_run] then replays a whole run, and [settle_sim_below]
    turns it into [⊑ₘᵤₛₜᵢ] — via [must_iff_acceptance_set_VACCS], with
    [fw_converge_static] discharging [cond1] and [coR_abs_pair_iff]
    translating the abstracted ready-set inclusion into the
    emitted-channel inclusion the simulation produces.

    This is the acceptance-set counterpart of the [must]-level bridges:
    it lets an inequation be established by exhibiting a *relation*
    instead of reasoning about every client, and it is the shape the
    restriction certificate should take.  Note it does not re-derive
    [≼ₐₛ] in disguise — [R] only has to relate the two specific sums and
    their reducts, which on the [Static] fragment are finitely many. *)

Lemma coR_abs_pair_iff : forall (x : proc * MO (ExtAct TypeOfActions)) d,
  (Inputs d) ∈ ⌈ 𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ ⌉ (coR x) <-> (exists w r, x ⟶[ActOut (d,w)] r).
Proof.
  intros x d. split.
  - intros (mu & Hmu & Heq). destruct mu as [[d0 w0]|[d0 w0]]; simpl in Heq.
    + inversion Heq; subst.
      destruct Hmu as (mu2 & Hnr & Hd & _).
      destruct mu2 as [[e1 x1]|[e1 x1]]; simpl in Hd; [ exact (match Hd with end) | ].
      inversion Hd; subst.
      apply lts_refuses_spec1 in Hnr as (z & Hz). exists w0, z. exact Hz.
    + exfalso. destruct Hmu as (mu2 & _ & _ & Hb).
      unfold non_blocking_output, is_output in Hb. apply Hb. eexists; reflexivity.
  - intros (w & r & Hr).
    exists (ActIn (d,w)). split; [ | reflexivity ].
    exists (ActOut (d,w)). repeat split.
    + intro Hst2. eapply (@lts_refuses_spec2 (proc * MO (ExtAct TypeOfActions)) _ _ _
                            x (ActExt (ActOut (d,w)))); [ | exact Hst2 ].
      exists r. exact Hr.
    + unfold non_blocking_output, is_output. intros (b & Hb). discriminate Hb.
Qed.


Definition SettleSim
  (R : (proc * MO (ExtAct TypeOfActions)) -> (proc * MO (ExtAct TypeOfActions)) -> Prop)
  : Prop :=
  (forall x y y', R x y -> y ⟶ y' -> exists x', x ⟹[[]] x' /\ R x' y')
  /\ (forall x y mu y', R x y -> y ⟶[mu] y' -> exists x', x ⟹{mu} x' /\ R x' y')
  /\ (forall x y, R x y -> y ↛ -> Settles (emits y) x).

(** Two closure facts that make a [SettleSim] modular: the diagonal is
    one, and unions of them are.  Together they mean a construction only
    has to supply its *off-diagonal* part and show that part steps into
    (itself ∪ the diagonal) — which is how [restrict_by_settle] is
    organised, and how any richer relation for the message layer will
    have to be.

    Worth keeping in view when designing such a relation: the step
    clauses answer with **weak** transitions ([⟹[[]]] and [⟹{mu}]), so
    the left is free to take internal moves while mimicking the right.
    That is not a technicality — it is exactly what lets a configuration
    whose bag can be *regenerated* by a continuation keep up with a right
    that merely emits from its buffer. *)

Lemma settle_sim_diag : SettleSim (fun x y => x = y).
Proof.
  split; [ | split ].
  - intros x y y' Hxy Hl. subst x. exists y'.
    split; [ eapply wt_tau; [ exact Hl | apply wt_nil ] | reflexivity ].
  - intros x y mu y' Hxy Hl. subst x. exists y'.
    split; [ eapply wt_act; [ exact Hl | apply wt_nil ] | reflexivity ].
  - intros x y Hxy Hst. subst x. apply Settles_here; [ exact Hst | ].
    intros d w r Hr. exists w, r. exact Hr.
Qed.

Lemma settle_sim_union : forall R1 R2, SettleSim R1 -> SettleSim R2 ->
  SettleSim (fun x y => R1 x y \/ R2 x y).
Proof.
  intros R1 R2 (A1 & A2 & A3) (B1 & B2 & B3). split; [ | split ].
  - intros x y y' [H|H] Hl.
    + destruct (A1 x y y' H Hl) as (x' & Hw & HR). exists x'. split; [ exact Hw | left; exact HR ].
    + destruct (B1 x y y' H Hl) as (x' & Hw & HR). exists x'. split; [ exact Hw | right; exact HR ].
  - intros x y mu y' [H|H] Hl.
    + destruct (A2 x y mu y' H Hl) as (x' & Hw & HR). exists x'. split; [ exact Hw | left; exact HR ].
    + destruct (B2 x y mu y' H Hl) as (x' & Hw & HR). exists x'. split; [ exact Hw | right; exact HR ].
  - intros x y [H|H] Hst; [ apply A3 | apply B3 ]; assumption.
Qed.

Lemma settle_sim_run : forall R, SettleSim R -> forall s y y' x,
  R x y -> y ⟹[s] y' -> y' ↛ ->
  exists x', x ⟹[s] x' /\ x' ↛ /\ (forall d, emits x' d -> emits y' d).
Proof.
  intros R (H1 & H2 & H3) s y y' x HR Hw. revert x HR.
  induction Hw as [z|s1 z r w Hl Hwt IH|mu s1 z r w Hl Hwt IH]; intros x HR Hst.
  - destruct (H3 x z HR Hst) as (x' & Hwx & Hstx & He).
    exists x'. split; [ exact Hwx | ]. split; [ exact Hstx | ].
    intros d (w0 & r0 & Hr0). eapply He. exact Hr0.
  - destruct (H1 x z r HR Hl) as (x1 & Hwx1 & HR1).
    destruct (IH x1 HR1 Hst) as (x' & Hwx & Hstx & He).
    exists x'. split; [ | split; [ exact Hstx | exact He ] ].
    replace s1 with ([] ++ s1) by reflexivity.
    eapply wt_concat; [ exact Hwx1 | exact Hwx ].
  - destruct (H2 x z mu r HR Hl) as (x1 & Hwx1 & HR1).
    destruct (IH x1 HR1 Hst) as (x' & Hwx & Hstx & He).
    exists x'. split; [ | split; [ exact Hstx | exact He ] ].
    eapply wt_push_left; [ exact Hwx1 | exact Hwx ].
Qed.

Theorem settle_sim_below : forall (p q : proc) R, Static p -> Static q ->
  SettleSim R -> R (p ▷ (∅ : MO (ExtAct TypeOfActions))) (q ▷ (∅ : MO (ExtAct TypeOfActions))) ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q.
Proof.
  intros p q R Hp Hq Hsim HR. apply must_iff_acceptance_set_VACCS. split.
  - intros s _. apply fw_converge_static. exact Hq.
  - intros s y' _ Hwy Hsty.
    destruct (settle_sim_run R Hsim s (q ▷ (∅ : MO (ExtAct TypeOfActions))) y'
                (p ▷ (∅ : MO (ExtAct TypeOfActions))) HR Hwy Hsty)
      as (x' & Hwx & Hstx & He).
    exists x'. split; [ exact Hwx | ]. split; [ exact Hstx | ].
    intros a Ha. destruct a as [d].
    apply coR_abs_pair_iff. apply He. apply coR_abs_pair_iff. exact Ha.
Qed.

(** * Buffers and traces, in both directions

    [fw_wt_feed_list] turns a run of [p ▷ bag l] into one of [p ▷ ∅] over
    the trace [feed l]; these are the converse and the monotonicity fact
    it needs.

    [fw_tau_add] / [fw_tau_run_add]: internal steps survive extra
    messages.  A [τ] is either the process's own — unaffected — or a
    delivery, which is still available when *other* messages are present
    ([mo_swap] does the bookkeeping).

    [fw_feed_inv_list]: a run over a whole feeding trace is a run with all
    those messages handed over up front.  This is what lets the settling
    obligation be read at an *arbitrary* buffer rather than one message at
    a time — which is what a [SettleSim] between two sums needs, since its
    stable clause quantifies over every buffer the right-hand side can
    accumulate. *)

Lemma fw_tau_add : forall (x y : proc * MO (ExtAct TypeOfActions)) k,
  x ⟶ y -> (x.1 ▷ (k ⊎ x.2)) ⟶ (y.1 ▷ (k ⊎ y.2)).
Proof.
  intros x y k Hl. destruct (fw_tau_shape x.1 x.2 y) as [HA|HB];
    [ destruct x as (x1,x2); exact Hl | | ].
  - destruct HA as (p' & Hp' & E). subst y. simpl. apply fw_tau_left. exact Hp'.
  - destruct HB as (a & p' & m' & Hm & Hp' & E). subst y. simpl.
    rewrite Hm. rewrite mo_swap. apply fw_tau_deliver. exact Hp'.
Qed.

Lemma fw_tau_run_add : forall (x y : proc * MO (ExtAct TypeOfActions)) k,
  x ⟹[[]] y -> (x.1 ▷ (k ⊎ x.2)) ⟹[[]] (y.1 ▷ (k ⊎ y.2)).
Proof.
  intros x y k Hw. remember ([] : trace (ExtAct TypeOfActions)) as s0 eqn:Hs.
  induction Hw as [z|s1 z r w Hl Hwt IH|mu s1 z r w Hl Hwt IH].
  - destruct z as (z1,z2). apply wt_nil.
  - eapply wt_tau; [ | apply IH; exact Hs ]. apply fw_tau_add. exact Hl.
  - discriminate Hs.
Qed.

Lemma fw_feed_inv_list : forall (l : list TypeOfActions) (x y : proc * MO (ExtAct TypeOfActions)),
  x ⟹[feed l] y -> (x.1 ▷ (bag l ⊎ x.2)) ⟹[[]] y.
Proof.
  induction l as [|a l IH]; intros x y Hw; simpl in *.
  - replace ((∅ : MO (ExtAct TypeOfActions)) ⊎ x.2) with x.2
      by (symmetry; apply gmultiset_disj_union_left_id).
    destruct x as (x1,x2). exact Hw.
  - destruct (wt_pop _ _ _ _ Hw) as (z & Hz1 & Hz2).
    pose proof (fw_feed_inv x z a Hz1) as Hstep.
    pose proof (IH z y Hz2) as Hrest.
    assert (Hlift : ((x.1) ▷ (bag l ⊎ ({[+ ActOut a +]} ⊎ x.2)))
                      ⟹[[]] ((z.1) ▷ (bag l ⊎ z.2))).
    { pose proof (fw_tau_run_add ((x.1) ▷ ({[+ ActOut a +]} ⊎ x.2)) z (bag l) Hstep) as HL.
      simpl in HL. exact HL. }
    simpl in Hlift.
    replace ({[+ ActOut a +]} ⊎ bag l ⊎ x.2)
      with (bag l ⊎ ({[+ ActOut a +]} ⊎ x.2))
      by (rewrite mo_swap; rewrite (assoc_L (@disj_union (MO (ExtAct TypeOfActions)) _)); reflexivity).
    replace ([] : trace (ExtAct TypeOfActions)) with (([] ++ []) : trace (ExtAct TypeOfActions))
      by reflexivity.
    eapply wt_concat; [ exact Hlift | exact Hrest ].
Qed.

(** * Restriction from a settling certificate — both step clauses free

    For a transition-sub-sum [M' ⊆ M] the relation

        R x y  :=  x = y  ∨  ∃ m, x = (g M ▷ m) ∧ y = (g M' ▷ m)

    is a [SettleSim] as soon as its **stable clause** holds, and that
    clause is the *only* obligation:

    - on the diagonal every step matches itself and [Settles_here]
      closes the stable case;
    - off the diagonal a right-hand [τ] is either [M']'s own step or a
      delivery, and in both cases the *same* transition is available on
      the left because [M' ⊆ M] — after which the two sides are the
      **same state**, so the pair drops onto the diagonal;
    - a right-hand visible step is either [M']'s own (same, drops onto
      the diagonal) or a buffer absorb/emit, which both sides perform
      identically, keeping equal buffers.

    So restricting a stable sum's channel set reduces to a single
    reachability statement at an arbitrary buffer.  Compare
    [VACCS_Absorb.must_i_restrict_badk], whose certificate is a
    ∀-over-clients judgement and whose per-channel obligations force the
    kill-order problem: here the shape of the certificate is
    [Settles] — exactly what [bhv_pre_cond2] produces. *)

Theorem restrict_by_settle : forall (M M' : gproc),
  gStatic M -> gStatic M' ->
  (forall al q, lts (g M') al q -> lts (g M) al q) ->
  (forall m, ((g M') ▷ m) ↛ -> Settles (emits ((g M') ▷ m)) ((g M) ▷ m)) ->
  (g M) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (g M').
Proof.
  intros M M' HM HM' Hsub Hcert.
  set (R := fun (x y : proc * MO (ExtAct TypeOfActions)) =>
              x = y \/ (exists m, x = ((g M) ▷ m) /\ y = ((g M') ▷ m))).
  eapply (settle_sim_below (g M) (g M') R (static_g M HM) (static_g M' HM')).
  - split; [ | split ].
    + intros x y y' HR Hl. destruct HR as [He | (m & Ex & Ey)].
      * subst x. exists y'. split; [ eapply wt_tau; [ exact Hl | apply wt_nil ] | ].
        left. reflexivity.
      * subst x y. destruct (fw_tau_shape (g M') m y' Hl) as [HA|HB].
        -- destruct HA as (p' & Hp' & E). subst y'.
           exists (p' ▷ m). split; [ | left; reflexivity ].
           eapply wt_tau; [ apply fw_tau_left; apply Hsub; exact Hp' | apply wt_nil ].
        -- destruct HB as (a & p' & m0 & Hm & Hp' & E). subst y'.
           exists (p' ▷ m0). split; [ | left; reflexivity ].
           eapply wt_tau; [ | apply wt_nil ]. rewrite Hm.
           apply fw_tau_deliver. apply Hsub. exact Hp'.
    + intros x y mu y' HR Hl. destruct HR as [He | (m & Ex & Ey)].
      * subst x. exists y'. split; [ eapply wt_act; [ exact Hl | apply wt_nil ] | ].
        left. reflexivity.
      * subst x y. destruct (fw_ext_shape (g M') m mu y' Hl) as [HA|[HB|HC]].
        -- destruct HA as (p' & Hp' & E). subst y'.
           exists (p' ▷ m). split; [ | left; reflexivity ].
           eapply wt_act; [ | apply wt_nil ]. apply fw_ext_left. apply Hsub. exact Hp'.
        -- destruct HB as (a & Ha & E). subst mu y'.
           exists ((g M) ▷ ({[+ ActOut a +]} ⊎ m)). split.
           ++ eapply wt_act; [ apply fw_input_always | apply wt_nil ].
           ++ right. exists ({[+ ActOut a +]} ⊎ m). split; reflexivity.
        -- destruct HC as (a & m0 & Ha & Hm & E). subst mu y'.
           exists ((g M) ▷ m0). split.
           ++ eapply wt_act; [ | apply wt_nil ]. rewrite Hm. apply fw_emit.
           ++ right. exists m0. split; reflexivity.
    + intros x y HR Hst. destruct HR as [He | (m & Ex & Ey)].
      * subst x. apply Settles_here; [ exact Hst | ]. intros d w r Hr. exists w, r. exact Hr.
      * subst x y. apply Hcert. exact Hst.
  - right. exists (∅ : MO (ExtAct TypeOfActions)). split; reflexivity.
Qed.

(** * The certificate's target set is just the buffer's channels

    A guarded sum emits nothing of its own, so [emits (g M' ▷ m)] is
    exactly "some message of [m] is on this channel".  Two consequences,
    and the second is the useful one:

    - [Settles_gsum_stable]: when the *left* is already stable the
      certificate is **free** — its own emitted channels are the buffer's.
      So all the content of [restrict_by_settle]'s hypothesis lies in the
      unstable case, where a delivery has to be chosen well.  That is
      exactly the [∃] the client-side formulation could not express: on
      [VACCS_DropProbes.v]'s [MM] at buffer [{a!v, b!w}], delivering [b]
      first settles inside the buffer's channels while delivering [a]
      first escapes to [e].
    - [Settles_gsum_chans]: the hypothesis may therefore be discharged in
      the [chans] form, which mentions only the buffer. *)

Definition chans (m : MO (ExtAct TypeOfActions)) (d : ChannelData) : Prop :=
  exists w, ActOut (d,w) ∈ m.

Lemma emits_gsum_chans : forall (M : gproc) (m : MO (ExtAct TypeOfActions)) d,
  emits ((g M) ▷ m) d -> chans m d.
Proof.
  intros M m d (w & r & Hr).
  destruct (fw_ext_shape (g M) m (ActOut (d,w)) r Hr) as [HA|[HB|HC]].
  - destruct HA as (p' & Hp' & _). exfalso. eapply gsum_no_output. exact Hp'.
  - destruct HB as (a & Ha & _). discriminate Ha.
  - destruct HC as (a & m' & Ha & Hm & _). injection Ha as Ha. subst a.
    exists w. rewrite Hm. apply gmultiset_elem_of_disj_union. left.
    apply gmultiset_elem_of_singleton. reflexivity.
Qed.

Theorem Settles_gsum_stable : forall (M : gproc) (m : MO (ExtAct TypeOfActions)),
  ((g M) ▷ m) ↛ -> Settles (chans m) ((g M) ▷ m).
Proof.
  intros M m Hst. apply Settles_here; [ exact Hst | ].
  intros d w r Hr. eapply emits_gsum_chans. exists w, r. exact Hr.
Qed.

Lemma fw_emit_of_mem : forall (p : proc) (m : MO (ExtAct TypeOfActions)) a,
  ActOut a ∈ m -> exists r, (p ▷ m) ⟶[ActOut a] r.
Proof.
  intros p m a Hin. apply gmultiset_disj_union_difference' in Hin.
  rewrite Hin. eexists. apply fw_emit.
Qed.

Lemma emits_gsum_iff : forall (M' : gproc) (m : MO (ExtAct TypeOfActions)) d,
  emits ((g M') ▷ m) d <-> chans m d.
Proof.
  intros M' m d. split; [ apply emits_gsum_chans | ].
  intros (w & Hin). exists w. apply fw_emit_of_mem. exact Hin.
Qed.

Corollary Settles_gsum_chans : forall (M M' : gproc) (m : MO (ExtAct TypeOfActions)),
  Settles (chans m) ((g M) ▷ m) -> Settles (emits ((g M') ▷ m)) ((g M) ▷ m).
Proof.
  intros M M' m H. eapply Settles_mono; [ | exact H ].
  intros d Hd. apply emits_gsum_iff. exact Hd.
Qed.

(** * Adding messages after settling

    The remaining case of the certificate is a buffer mixing *surplus*
    channels (offered by [M], not by [N]) with channels [M] does not
    offer at all.  For the surplus part the semantics supplies the run
    directly ([surplus_Settles]); this lemma is what puts the rest back:

    settle first with the surplus messages only, then hand over the
    remaining ones — provided the settled state refuses them, which is
    exactly the case when [M] never offered those channels.  The added
    messages contribute their own channels to the emitted set and nothing
    else, so the target set grows by exactly [chans k].

    [fw_tau_run_add] lifts the run, [fw_stable_iff] re-establishes
    stability from the two refusal facts, and [fw_emit_of_mem] accounts
    for the buffer's own contribution to the emitted channels. *)

Lemma Settles_add : forall (S : ChannelData -> Prop) k x1 x2 y1 y2,
  ((x1 : proc) ▷ (x2 : MO (ExtAct TypeOfActions))) ⟹[[]] (y1 ▷ y2) ->
  ((y1 : proc) ▷ (y2 : MO (ExtAct TypeOfActions))) ↛ ->
  (forall d w r, (y1 ▷ y2) ⟶[ActOut (d,w)] r -> S d) ->
  (forall a q, ActOut a ∈ k -> ~ lts y1 (ActExt (ActIn a)) q) ->
  Settles (fun d => S d \/ chans k d) (x1 ▷ (k ⊎ x2)).
Proof.
  intros S k x1 x2 y1 y2 Hw Hst He Hk.
  exists (y1 ▷ (k ⊎ y2)). split.
  { apply (fw_tau_run_add (x1 ▷ x2) (y1 ▷ y2) k). exact Hw. }
  assert (Hsty : forall z, ~ ((y1 ▷ y2) ⟶ z)).
  { intros z Hz. eapply (@lts_refuses_spec2 (proc * MO (ExtAct TypeOfActions)) _ _ _
                           (y1 ▷ y2) τ); [ | exact Hst ].
    exists z. exact Hz. }
  apply fw_stable_iff in Hsty as (Hty & Hry). simpl in Hty, Hry.
  split.
  - destruct (decide (lts_refuses ((y1 : proc) ▷ (k ⊎ y2)) τ)) as [Hy|Hn]; [ exact Hy | ].
    exfalso. apply lts_refuses_spec1 in Hn as (z & Hz).
    eapply (proj2 (fw_stable_iff y1 (k ⊎ y2))); [ | exact Hz ].
    split; [ exact Hty | ].
    intros a Hin q Hq. apply gmultiset_elem_of_disj_union in Hin.
    destruct Hin as [Hin|Hin].
    + eapply Hk; [ exact Hin | exact Hq ].
    + eapply Hry; [ exact Hin | exact Hq ].
  - intros d w r Hr.
    destruct (fw_ext_shape y1 (k ⊎ y2) (ActOut (d,w)) r Hr) as [HA|[HB|HC]].
    + destruct HA as (p' & Hp' & _). left.
      apply (He d w (p' ▷ y2)). apply fw_ext_left. exact Hp'.
    + destruct HB as (a & Ha & _). discriminate Ha.
    + destruct HC as (a & m' & Ha & Hm & _). injection Ha as Ha. subst a.
      assert (Hin : ActOut (d,w) ∈ (k ⊎ y2)).
      { rewrite Hm. apply gmultiset_elem_of_disj_union. left.
        apply gmultiset_elem_of_singleton. reflexivity. }
      apply gmultiset_elem_of_disj_union in Hin. destruct Hin as [Hin|Hin].
      * right. exists w. exact Hin.
      * left. destruct (fw_emit_of_mem y1 y2 (d,w) Hin) as (z & Hz).
        apply (He d w z). exact Hz.
Qed.

(** * The whole surplus buffer at once — no iteration needed

    [surplus_settles] handles one surplus message; the multi-message case
    turns out to need **no iteration at all**, because the right-hand
    state stays stable however many surplus messages are fed:
    [g N ▷ bag l] has no [τ] (a guarded sum with no [τ]-summand refusing
    every channel in the bag) and emits exactly the bag's channels.  So
    one instance of [bhv_pre_cond2], at the trace [feed l], does it:
    [fw_wt_feed_list] builds the right-hand run, [fw_feed_inv_list] turns
    the left-hand one back into a run from [g M ▷ bag l], and
    [emits_gsum_chans] reads the emitted channels off the bag.

    This was the last case of the certificate that looked as though it
    needed a construction; it does not. *)

Theorem surplus_settles_bag : forall (P : proc) (N : gproc) (l : list TypeOfActions),
  Static P -> gStatic N ->
  (forall p, ~ lts (g N) τ p) ->
  (forall a, ActOut a ∈ bag l -> forall r, ~ lts (g N) (ActExt (ActIn a)) r) ->
  P ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (g N) ->
  Settles (chans (bag l)) (P ▷ bag l).
Proof.
  intros P N l HP HN HstN Hnoc Hsem.
  assert (Hsty : ((g N) ▷ bag l) ↛).
  { assert (Hnostep : forall x, ~ (((g N) ▷ bag l) ⟶ x)).
    { apply fw_stable_iff. split; [ exact HstN | ].
      intros a Hin q Hq. eapply Hnoc; [ exact Hin | exact Hq ]. }
    destruct (decide (lts_refuses ((g N) ▷ bag l) τ)) as [Hy|Hn]; [ exact Hy | ].
    exfalso. apply lts_refuses_spec1 in Hn as (z & Hz). eapply Hnostep. exact Hz. }
  assert (Hwq : ((g N) ▷ (∅ : MO (ExtAct TypeOfActions))) ⟹[feed l] ((g N) ▷ bag l)).
  { replace (feed l) with (feed l ++ []) by (rewrite app_nil_r; reflexivity).
    apply fw_wt_feed_list.
    replace (bag l ⊎ (∅ : MO (ExtAct TypeOfActions))) with (bag l)
      by (symmetry; apply gmultiset_disj_union_right_id).
    apply wt_nil. }
  apply must_iff_acceptance_set_VACCS in Hsem as (Hc1 & Hc2).
  destruct (Hc2 (feed l) ((g N) ▷ bag l)
              (fw_converge_static (feed l) P ∅ HP) Hwq Hsty)
    as (x & Hwx & Hstx & Hincl).
  exists x. split.
  - pose proof (fw_feed_inv_list l (P ▷ (∅ : MO (ExtAct TypeOfActions))) x Hwx) as H.
    simpl in H.
    replace (bag l) with (bag l ⊎ (∅ : MO (ExtAct TypeOfActions)))
      by (apply gmultiset_disj_union_right_id).
    exact H.
  - split; [ exact Hstx | ].
    intros d w r Hr.
    assert (Hin : (Inputs d) ∈ ⌈ 𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ ⌉ (coR x))
      by (apply coR_abs_pair_iff; exists w, r; exact Hr).
    apply Hincl in Hin. apply coR_abs_pair_iff in Hin.
    eapply emits_gsum_chans. exact Hin.
Qed.

(** * Buffers are bags

    The forwarder only ever stores *outputs*, so every buffer reachable
    from [∅] is a [bag].  [OutOnly] records that, is preserved by the
    three buffer operations (absorb, emit, deliver), and [outonly_bag]
    converts it into the list form the [feed]/[bag] lemmas are stated
    with — the bridge between the multiset the LTS produces and the
    trace-shaped statements. *)


Lemma OutOnly_empty : OutOnly ∅.
Proof. intros x Hx. exfalso. eapply gmultiset_not_elem_of_empty. exact Hx. Qed.

Lemma OutOnly_add : forall a m, OutOnly m -> OutOnly ({[+ ActOut a +]} ⊎ m).
Proof.
  intros a m H x Hx. apply gmultiset_elem_of_disj_union in Hx. destruct Hx as [Hx|Hx].
  - apply gmultiset_elem_of_singleton in Hx. exists a. exact Hx.
  - apply H. exact Hx.
Qed.

Lemma OutOnly_sub : forall a m, OutOnly ({[+ ActOut a +]} ⊎ m) -> OutOnly m.
Proof.
  intros a m H x Hx. apply H. apply gmultiset_elem_of_disj_union. right. exact Hx.
Qed.

Lemma outonly_bag : forall (m : MO (ExtAct TypeOfActions)),
  OutOnly m -> exists l, m = bag l.
Proof.
  induction m as [|x m IH] using gmultiset_ind; intro H.
  - exists []. reflexivity.
  - destruct (H x) as (a & Ha).
    { apply gmultiset_elem_of_disj_union. left.
      apply gmultiset_elem_of_singleton. reflexivity. }
    subst x. destruct IH as (l & Hl).
    + eapply OutOnly_sub. exact H.
    + exists (a :: l). simpl. rewrite Hl. reflexivity.
Qed.

(** * The certificate, for every buffer the right-hand side refuses

    Combining [outonly_bag] with [surplus_settles_bag]: whenever [N]
    refuses every channel carried by the buffer, the certificate holds —
    at an arbitrary buffer, with no iteration and no side condition
    beyond [Static]-ness and [N]'s stability.

    This is the whole of `restrict_by_settle`'s hypothesis in the case
    that matters most.  Recall the hypothesis quantifies over buffers
    that [M' = grestrict N M] refuses, and [M'] refuses [c] exactly when
    [M] does not offer [c] **or** [c] is not one of [N]'s channels.  So
    the only buffers *not* covered here carry a channel that [N] offers
    and [M] does not — and in particular, whenever

        every channel [N] offers is also offered by [M]

    the two conditions coincide and this lemma discharges the hypothesis
    outright.  The residual case is recorded in the plan notes; it needs
    the argument iterated along deliveries rather than applied once. *)

Theorem certificate_N_refuses : forall (P : proc) (N : gproc), Static P -> gStatic N ->
  (forall p, ~ lts (g N) τ p) ->
  P ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (g N) ->
  forall m, OutOnly m ->
  (forall a, ActOut a ∈ m -> forall r, ~ lts (g N) (ActExt (ActIn a)) r) ->
  Settles (chans m) (P ▷ m).
Proof.
  intros P N HP HN HstN Hsem m Hout Hnoc.
  destruct (outonly_bag m Hout) as (l & Hl). subst m.
  eapply surplus_settles_bag; eassumption.
Qed.

(** * Settling in stages

    [Settles_add] finishes as soon as the added messages are refused.
    When they are *not* — which the residual case shows really happens —
    the argument must **continue** rather than stop: prefix the run
    obtained so far and keep settling from the enlarged state.

    [Settles_wt] is the prefixing (a τ-run before a [Settles] fact is
    still a [Settles] fact), and [Settles_add_wt] is the staged form: run
    with the small buffer, hand over the extra messages, and require
    only that the *resulting* state settles — a strictly weaker demand
    than [Settles_add]'s refusal side condition, and the shape the
    induction on the process component needs. *)

Lemma Settles_wt : forall (S : ChannelData -> Prop) x z,
  x ⟹[[]] z -> Settles S z -> Settles S x.
Proof.
  intros S x z Hw (y & Hwy & Hst & He). exists y.
  split; [ | split; [ exact Hst | exact He ] ].
  replace ([] : trace (ExtAct TypeOfActions)) with (([] ++ []) : trace (ExtAct TypeOfActions))
    by reflexivity.
  eapply wt_concat; [ exact Hw | exact Hwy ].
Qed.

Lemma Settles_add_wt : forall (S : ChannelData -> Prop) k x1 x2 y1 y2,
  ((x1 : proc) ▷ (x2 : MO (ExtAct TypeOfActions))) ⟹[[]] (y1 ▷ y2) ->
  Settles S ((y1 : proc) ▷ (k ⊎ y2)) ->
  Settles S (x1 ▷ (k ⊎ x2)).
Proof.
  intros S k x1 x2 y1 y2 Hw HS.
  eapply Settles_wt; [ | exact HS ].
  apply (fw_tau_run_add (x1 ▷ x2) (y1 ▷ y2) k). exact Hw.
Qed.

(** * [⊑ₘᵤₛₜᵢ 𝟘], read as settling

    Pairs with [VACCS_Bad.below_nil_iff] ("`p ⊑ₘᵤₛₜᵢ 𝟘` iff `p` fails
    every τ-stuck, non-good client"): on the acceptance-set side the same
    inequation says **`p` settles inside whatever buffer it is handed**.
    One instance of `bhv_pre_cond2` per buffer, against the stable state
    `𝟘 ▷ bag l`.

    Worth stating because it makes the shape of `restrict_by_settle`'s
    hypothesis plain — see the note in the plan file: at `M' = 𝟘` the
    hypothesis *is* `g M ⊑ₘᵤₛₜᵢ 𝟘`, so the certificate is not a weaker
    thing than the conclusion but a repackaging of it. *)

Theorem settles_of_below_nil : forall (p : proc), Static p ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc) ->
  forall m, OutOnly m -> Settles (chans m) (p ▷ m).
Proof.
  intros p Hp Hsem m Hout.
  destruct (outonly_bag m Hout) as (l & Hl). subst m.
  assert (Hsty : (((g 𝟘) : proc) ▷ bag l) ↛).
  { assert (Hnostep : forall x, ~ ((((g 𝟘) : proc) ▷ bag l) ⟶ x)).
    { apply fw_stable_iff. split.
      - intros q Hq. inversion Hq.
      - intros a Hin q Hq. inversion Hq. }
    destruct (decide (lts_refuses (((g 𝟘) : proc) ▷ bag l) τ)) as [Hy|Hn]; [ exact Hy | ].
    exfalso. apply lts_refuses_spec1 in Hn as (z & Hz). eapply Hnostep. exact Hz. }
  assert (Hwq : (((g 𝟘) : proc) ▷ (∅ : MO (ExtAct TypeOfActions)))
                  ⟹[feed l] (((g 𝟘) : proc) ▷ bag l)).
  { replace (feed l) with (feed l ++ []) by (rewrite app_nil_r; reflexivity).
    apply fw_wt_feed_list.
    replace (bag l ⊎ (∅ : MO (ExtAct TypeOfActions))) with (bag l)
      by (symmetry; apply gmultiset_disj_union_right_id).
    apply wt_nil. }
  apply must_iff_acceptance_set_VACCS in Hsem as (Hc1 & Hc2).
  destruct (Hc2 (feed l) (((g 𝟘) : proc) ▷ bag l)
              (fw_converge_static (feed l) p ∅ Hp) Hwq Hsty)
    as (x & Hwx & Hstx & Hincl).
  exists x. split.
  - pose proof (fw_feed_inv_list l (p ▷ (∅ : MO (ExtAct TypeOfActions))) x Hwx) as H.
    simpl in H.
    replace (bag l) with (bag l ⊎ (∅ : MO (ExtAct TypeOfActions)))
      by (apply gmultiset_disj_union_right_id).
    exact H.
  - split; [ exact Hstx | ].
    intros d w r Hr.
    assert (Hin : (Inputs d) ∈ ⌈ 𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ ⌉ (coR x))
      by (apply coR_abs_pair_iff; exists w, r; exact Hr).
    apply Hincl in Hin. apply coR_abs_pair_iff in Hin.
    eapply (emits_gsum_chans 𝟘). exact Hin.
Qed.

(** * Input commutation is FALSE — machine-checked

    It is tempting to think that in an asynchronous calculus the order of
    two nested input guards cannot matter: both `c ? (d ? P)` and
    `d ? (c ? P)` want the same two messages and then behave as `P`.
    **They are not comparable**, and the reason is exactly the fact
    `VACCS_ReadySet.gproc_coR_empty` records, used the other way round:

    hand both sides a single `d`-message.  The right-hand side consumes
    it and settles at `(c ? P) ▷ ∅` — stable, emitting **nothing**.  The
    left-hand side offers only `c`, so no delivery is possible; its only
    internally reachable state is `p ▷ {d!w}`, stable and **emitting on
    `d`** — a guard that cannot consume a pending message leaves it
    visible as a pending output, and the ready set sees it.
    `bhv_pre_cond2` then has no witness.

    (`must_i_cond2_fed` is what makes this a three-line argument rather
    than a search for a separating test.) *)

Lemma wt_nil_stable_fw : forall (x y : proc * MO (ExtAct TypeOfActions)),
  x ↛ -> x ⟹[[]] y -> y = x.
Proof.
  intros x y Hst Hw. remember ([] : trace (ExtAct TypeOfActions)) as s0 eqn:Hs.
  induction Hw as [z|s1 z r w Hl Hwt IH|mu s1 z r w Hl Hwt IH].
  - reflexivity.
  - exfalso. eapply (@lts_refuses_spec2 (proc * MO (ExtAct TypeOfActions)) _ _ _ z τ);
      [ | exact Hst ]. exists r. exact Hl.
  - discriminate Hs.
Qed.

Lemma fw_gsum_empty_no_emit : forall (M : gproc) d w r,
  ~ (((g M) : proc) ▷ (∅ : MO (ExtAct TypeOfActions))) ⟶[ActOut (d,w)] r.
Proof.
  intros M d w r Hr.
  destruct (fw_ext_shape (g M) ∅ (ActOut (d,w)) r Hr) as [HA|[HB|HC]].
  - destruct HA as (p' & Hp' & _). eapply gsum_no_output. exact Hp'.
  - destruct HB as (a & Ha & _). discriminate Ha.
  - destruct HC as (a & m' & _ & Hm & _). eapply empty_not_disj. exact Hm.
Qed.

Theorem input_comm_false : forall (c d e : Channel) (w y : Value),
  c <> d ->
  ~ ((g ((cst c) ? (g ((cst d) ? ((cst e) ! (cst y) • 𝟘)))))
       ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (g ((cst d) ? (g ((cst c) ? ((cst e) ! (cst y) • 𝟘)))))).
Proof.
  intros c d e w y Hcd Hle.
  set (P := ((cst e) ! (cst y) • 𝟘) : proc).
  set (p := (g ((cst c) ? (g ((cst d) ? P)))) : proc).
  set (q := (g ((cst d) ? (g ((cst c) ? P)))) : proc).
  assert (Hy : (((g ((cst c) ? P)) : proc) ▷ (∅ : MO (ExtAct TypeOfActions))) ↛).
  { assert (Hns : forall z,
      ~ ((((g ((cst c) ? P)) : proc) ▷ (∅ : MO (ExtAct TypeOfActions))) ⟶ z)).
    { apply fw_stable_iff. split.
      - intros z Hz. inversion Hz.
      - intros a Hin z Hz. exfalso. eapply gmultiset_not_elem_of_empty. exact Hin. }
    destruct (decide (lts_refuses (((g ((cst c) ? P)) : proc)
                                    ▷ (∅ : MO (ExtAct TypeOfActions))) τ))
      as [Hok|Hn]; [ exact Hok | ].
    exfalso. apply lts_refuses_spec1 in Hn as (z & Hz). eapply Hns. exact Hz. }
  assert (Hwy : (q ▷ ({[+ ActOut (cst d, cst w) +]} : MO (ExtAct TypeOfActions)))
                  ⟹[[]] (((g ((cst c) ? P)) : proc) ▷ (∅ : MO (ExtAct TypeOfActions)))).
  { eapply wt_tau; [ | apply wt_nil ].
    replace ({[+ ActOut (cst d, cst w) +]} : MO (ExtAct TypeOfActions))
      with (({[+ ActOut (cst d, cst w) +]} : MO (ExtAct TypeOfActions)) ⊎ ∅)
      by (apply gmultiset_disj_union_right_id).
    apply fw_tau_deliver.
    assert (E : ((g ((cst c) ? P)) : proc) ^ (cst w) = g ((cst c) ? P)) by reflexivity.
    assert (Hli : lts q (ActExt (ActIn (cst d, cst w)))
                   (((g ((cst c) ? P)) : proc) ^ (cst w)))
      by (unfold q; apply lts_input).
    rewrite E in Hli. exact Hli. }
  assert (Hsp : Static p) by (unfold p, P; repeat constructor).
  assert (Hsq : Static q) by (unfold q, P; repeat constructor).
  destruct (must_i_cond2_fed p q (cst d) (cst w) Hsp Hsq Hle _ Hwy Hy)
    as (x & Hwx & Hstx & Hincl).
  assert (Hstp : (p ▷ ({[+ ActOut (cst d, cst w) +]} : MO (ExtAct TypeOfActions))) ↛).
  { assert (Hns : forall z,
      ~ ((p ▷ ({[+ ActOut (cst d, cst w) +]} : MO (ExtAct TypeOfActions))) ⟶ z)).
    { apply fw_stable_iff. split.
      - intros z Hz. unfold p in Hz. inversion Hz.
      - intros a Hin z Hz. apply gmultiset_elem_of_singleton in Hin.
        injection Hin as Hin. subst a. unfold p in Hz. inversion Hz; subst.
        apply Hcd. reflexivity. }
    destruct (decide (lts_refuses (p ▷ ({[+ ActOut (cst d, cst w) +]}
                                          : MO (ExtAct TypeOfActions))) τ))
      as [Hok|Hn]; [ exact Hok | ].
    exfalso. apply lts_refuses_spec1 in Hn as (z & Hz). eapply Hns. exact Hz. }
  pose proof (wt_nil_stable_fw _ _ Hstp Hwx) as Hxe. subst x.
  destruct (Hincl (cst d)) as (w0 & r0 & Hr0).
  { exists (cst w). apply fw_emit_of_mem.
    apply gmultiset_elem_of_singleton. reflexivity. }
  eapply fw_gsum_empty_no_emit. exact Hr0.
Qed.

(** The same, with the relation restricted to buffers that really are
    bags of outputs — which is all the forwarder can reach from [∅].  The
    three [OutOnly] closure lemmas make every clause go through
    unchanged, and the certificate may then be stated for [OutOnly]
    buffers only, which is what [certificate_N_refuses] needs. *)

(** The simulation that [restrict_by_settle_out] exhibits, **named**.

    Isolating it is what turns the restriction into a *derived* law: the
    system's primitive becomes [ax_settle_sim] — any [SettleSim] proves an
    inequation between configurations — and [ax_restrict_settle] is its
    instance at this particular, **rigid** relation: same buffer on both
    sides, the left process fixed at [g M] and the right at [g M'], with
    only the diagonal to escape to.  That rigidity is exactly what the
    development's counterexamples refute in general, so the general rule
    is strictly stronger. *)

Definition restrict_rel (M M' : gproc)
  : (proc * MO (ExtAct TypeOfActions)) -> (proc * MO (ExtAct TypeOfActions)) -> Prop :=
  fun x y => x = y \/ (exists m, OutOnly m /\ x = ((g M) ▷ m) /\ y = ((g M') ▷ m)).

Lemma restrict_settle_sim_out : forall (M M' : gproc),
  (forall al q, lts (g M') al q -> lts (g M) al q) ->
  (forall m, OutOnly m -> ((g M') ▷ m) ↛ ->
     Settles (emits ((g M') ▷ m)) ((g M) ▷ m)) ->
  SettleSim (restrict_rel M M').
Proof.
  intros M M' Hsub Hcert. unfold restrict_rel.
  split; [ | split ].
    + intros x y y' HR Hl. destruct HR as [He | (m & Hout & Ex & Ey)].
      * subst x. exists y'. split; [ eapply wt_tau; [ exact Hl | apply wt_nil ] | ].
        left. reflexivity.
      * subst x y. destruct (fw_tau_shape (g M') m y' Hl) as [HA|HB].
        -- destruct HA as (p' & Hp' & E). subst y'.
           exists (p' ▷ m). split; [ | left; reflexivity ].
           eapply wt_tau; [ apply fw_tau_left; apply Hsub; exact Hp' | apply wt_nil ].
        -- destruct HB as (a & p' & m0 & Hm & Hp' & E). subst y'.
           exists (p' ▷ m0). split; [ | left; reflexivity ].
           eapply wt_tau; [ | apply wt_nil ]. rewrite Hm.
           apply fw_tau_deliver. apply Hsub. exact Hp'.
    + intros x y mu y' HR Hl. destruct HR as [He | (m & Hout & Ex & Ey)].
      * subst x. exists y'. split; [ eapply wt_act; [ exact Hl | apply wt_nil ] | ].
        left. reflexivity.
      * subst x y. destruct (fw_ext_shape (g M') m mu y' Hl) as [HA|[HB|HC]].
        -- destruct HA as (p' & Hp' & E). subst y'.
           exists (p' ▷ m). split; [ | left; reflexivity ].
           eapply wt_act; [ | apply wt_nil ]. apply fw_ext_left. apply Hsub. exact Hp'.
        -- destruct HB as (a & Ha & E). subst mu y'.
           exists ((g M) ▷ ({[+ ActOut a +]} ⊎ m)). split.
           ++ eapply wt_act; [ apply fw_input_always | apply wt_nil ].
           ++ right. exists ({[+ ActOut a +]} ⊎ m).
              split; [ apply OutOnly_add; exact Hout | split; reflexivity ].
        -- destruct HC as (a & m0 & Ha & Hm & E). subst mu y'.
           exists ((g M) ▷ m0). split.
           ++ eapply wt_act; [ | apply wt_nil ]. rewrite Hm. apply fw_emit.
           ++ right. exists m0.
              split; [ eapply OutOnly_sub; rewrite <- Hm; exact Hout
                     | split; reflexivity ].
    + intros x y HR Hst. destruct HR as [He | (m & Hout & Ex & Ey)].
      * subst x. apply Settles_here; [ exact Hst | ]. intros d w r Hr. exists w, r. exact Hr.
      * subst x y. apply Hcert; assumption.
Qed.

Theorem restrict_by_settle_out : forall (M M' : gproc),
  gStatic M -> gStatic M' ->
  (forall al q, lts (g M') al q -> lts (g M) al q) ->
  (forall m, OutOnly m -> ((g M') ▷ m) ↛ ->
     Settles (emits ((g M') ▷ m)) ((g M) ▷ m)) ->
  (g M) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (g M').
Proof.
  intros M M' HM HM' Hsub Hcert.
  apply (settle_sim_below (g M) (g M') (restrict_rel M M')
           (static_g M HM) (static_g M' HM')).
  - apply restrict_settle_sim_out; assumption.
  - right. exists (∅ : MO (ExtAct TypeOfActions)).
    split; [ apply OutOnly_empty | split; reflexivity ].
Qed.

(** ** A buffered message is a message on the client

    The buffer, a server-side pending message and a client-side pending
    message are all the same thing.  [VACCS_Precongruence.must_msg_swap]
    moves a message between server and client at the level of bare
    processes; this is the same move with the message in the *buffer*.

    Unlike the process-level version — where the [noone] bridge had to be
    used, because VACCS's [proc] is **not** a [Lts_FW.gLtsObaFW] (a bare
    process cannot always absorb an output and give it back, so
    [boomerang] fails) — here the abstract lemmas apply directly: the
    forwarder [proc * MO _] *is* a [gLtsObaFW], which is exactly what
    [Lift.must_non_blocking_action_swap_l_fw]/[_r_fw] require of the
    server. *)

Lemma fw_msg_swap : forall (c : ChannelData) (v : ValueData)
    (p e : proc) (m : MO (ExtAct TypeOfActions)),
  ((p ▷ ({[+ ActOut (c,v) +]} ⊎ m)) must_pass e)
  <-> ((p ▷ m) must_pass ((c ! v • 𝟘) ‖ e)).
Proof.
  intros c v p e m.
  assert (Hnb : non_blocking (ActOut (c,v))).
  { unfold non_blocking. simpl. unfold non_blocking_output. unfold is_output. eauto. }
  assert (Hnil : forall r : proc, ((𝟘 : proc) ‖ r) ≡* r).
  { intro r. eapply cgr_trans. apply cgr_par_com. apply cgr_par_nil. }
  assert (Hp : (p ▷ ({[+ ActOut (c,v) +]} ⊎ m)) ⟶[ActOut (c,v)] (p ▷ m))
    by apply fw_emit.
  assert (He : ((c ! v • 𝟘) ‖ e) ⟶[ActOut (c,v)] ((𝟘 : proc) ‖ e)).
  { apply lts_parL. apply lts_output. }
  split; intro Hm.
  - eapply (Lift.must_non_blocking_action_swap_l_fw _ _ _ _ (ActOut (c,v)) Hnb Hp He).
    eapply must_eq_client; [ | exact Hm ]. apply cgr_symm. apply Hnil.
  - eapply must_eq_client; [ apply Hnil | ].
    eapply (Lift.must_non_blocking_action_swap_r_fw _ _ _ _ (ActOut (c,v)) Hnb Hp He).
    exact Hm.
Qed.

(** ** A syntactic message bag IS the forwarder's buffer

    [msgs l ‖ p] and [p ▷ bag l] pass exactly the same tests.  Two moves
    do it, one per level:

    - [VACCS_Precongruence.must_msg_swap] takes a message from the server
      to the *client* (the [noone] bridge at an atomic message);
    - [VACCS_Cond2.fw_msg_swap] takes it from the *buffer* to the client
      (the abstract [Lift] output-swap, which applies because the
      forwarder — unlike a bare VACCS process — is a [gLtsObaFW]).

    Composing them, buffer and syntactic bag are interchangeable.  This is
    what makes the [Ѵⁿ (msgs l ‖ ·)] layer of the normal form addressable
    by the forwarder machinery ([Settles], [SettleSim]) rather than
    needing a syntax of its own. *)

Lemma msgs_buffer_iff : forall (l : list TypeOfActions) (p e : proc),
  ((msgs l ‖ p) must_pass e) <-> ((p ▷ bag l) must_pass e).
Proof.
  assert (Hnil : forall r : proc, ((𝟘 : proc) ‖ r) ≡* r).
  { intro r. eapply cgr_trans. apply cgr_par_com. apply cgr_par_nil. }
  assert (Hfw : forall (x t : proc),
            x must_pass t <-> (x ▷ (∅ : MO (ExtAct TypeOfActions))) must_pass t).
  { intros x t. apply Lift.must_iff_must_fw. }
  assert (Hrot : forall X Y Z : proc, ((X ‖ Y) ‖ Z) ≡* ((Y ‖ Z) ‖ X)).
  { intros X Y Z. eapply cgr_trans; [ apply cgr_par_assoc | apply cgr_par_com ]. }
  assert (Hcgr : forall (x y t : proc), x ≡* y -> y must_pass t -> x must_pass t).
  { intros x y t Hc Hmm. destruct (must_i_cgr x y Hc) as [H1 H2]. apply H1. exact Hmm. }
  induction l as [ | a l IH ]; intros p e.
  - simpl. split; intro Hm.
    + apply Hfw. eapply Hcgr; [ | exact Hm ]. apply cgr_symm. apply Hnil.
    + assert (Hx : p must_pass e) by (apply Hfw; exact Hm).
      eapply Hcgr; [ | exact Hx ]. apply Hnil.
  - destruct a as (c,v). simpl. split; intro Hm.
    + apply fw_msg_swap. apply IH. apply must_msg_swap.
      eapply Hcgr; [ | exact Hm ]. apply cgr_symm. apply Hrot.
    + assert (Hx : ((msgs l ‖ p) ‖ ((c ! v • 𝟘) : proc)) must_pass e).
      { apply must_msg_swap. apply IH. apply fw_msg_swap. exact Hm. }
      eapply Hcgr; [ | exact Hx ]. apply Hrot.
Qed.

(** Hence a comparison of two configurations is a comparison of two
    forwarder states with the bags loaded into their buffers.  Recall
    [ctx_pre p q] is [∀ t, p must_pass t -> q must_pass t]. *)

Corollary msgs_below_iff : forall (l l' : list TypeOfActions) (p q : proc),
  ((msgs l ‖ p) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l' ‖ q))
  <-> (forall e : proc, (p ▷ bag l) must_pass e -> (q ▷ bag l') must_pass e).
Proof.
  intros l l' p q. unfold ctx_pre. split.
  - intros Hpre e He. apply msgs_buffer_iff. apply Hpre. apply msgs_buffer_iff. exact He.
  - intros Hall e He. apply msgs_buffer_iff. apply Hall. apply msgs_buffer_iff. exact He.
Qed.

(** And hence the *acceptance condition* is available between two
    forwarder states with **loaded** buffers, not only at [▷ ∅].

    This is the enabling lemma for the message layer.  The repository's
    own [Completeness.completeness_fw] turns [⊑ₘᵤₛₜᵢ] into [≼ₐₛ] at any
    type that is a [Lts_FW.gLtsObaFW] — the forwarder [proc * MO _] is
    one — and [msgs_below_iff] supplies its hypothesis from a comparison
    of two *configurations*.  So everything [VACCS_Cond2.v] proves about
    [p ▷ m] becomes usable about [msgs l ‖ p]. *)

Lemma msgs_accept : forall (l l' : list TypeOfActions) (p q : proc),
  ((msgs l ‖ p) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l' ‖ q)) ->
  ((p ▷ bag l) ≼ₐₛ (q ▷ bag l')).
Proof.
  intros l l' p q Hpre.
  apply Completeness.completeness_fw.
  unfold ctx_pre. intros t Ht.
  apply msgs_buffer_iff. apply Hpre. apply msgs_buffer_iff. exact Ht.
Qed.

(** ** THE CONFIGURATION PREORDER *IS* THE ACCEPTANCE PREORDER ON LOADED STATES

    [msgs_accept] has a converse, by the repository's own
    [Soundness.soundness_fw] — which, like [Completeness.completeness_fw],
    holds at any [Lts_FW.gLtsObaFW], and the forwarder is one.  So the two
    notions coincide:

    a comparison of two *configurations* is exactly the acceptance-set
    comparison of two forwarder states with the bags loaded into their
    buffers.  Nothing about [Settles], [SettleSim] or the certificate
    needs restating for the message layer: it is the same machinery at a
    shifted buffer. *)

Lemma msgs_sound : forall (l l' : list TypeOfActions) (p q : proc),
  ((p ▷ bag l) ≼ₐₛ (q ▷ bag l')) ->
  ((msgs l ‖ p) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l' ‖ q)).
Proof.
  intros l l' p q Hacc.
  apply msgs_below_iff. apply Soundness.soundness_fw. exact Hacc.
Qed.

Corollary msgs_accept_iff : forall (l l' : list TypeOfActions) (p q : proc),
  ((msgs l ‖ p) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l' ‖ q)) <-> ((p ▷ bag l) ≼ₐₛ (q ▷ bag l')).
Proof.
  intros l l' p q. split; [ apply msgs_accept | apply msgs_sound ].
Qed.

(** And hence the settling simulation — the acceptance-set counterpart of
    the two [must]-level bridges — proves inequations between
    *configurations*, not only between bare processes.  Same statement as
    [VACCS_Cond2.settle_sim_below], with the buffers loaded. *)

Theorem settle_sim_below_bag : forall (l l' : list TypeOfActions) (p q : proc) R,
  Static p -> Static q -> SettleSim R -> R (p ▷ bag l) (q ▷ bag l') ->
  (msgs l ‖ p) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l' ‖ q).
Proof.
  intros l l' p q R Hp Hq Hsim HR. apply msgs_sound. split.
  - intros s _. apply fw_converge_static. exact Hq.
  - intros s y' _ Hwy Hsty.
    destruct (settle_sim_run R Hsim s (q ▷ bag l') y' (p ▷ bag l) HR Hwy Hsty)
      as (x' & Hwx & Hstx & He).
    exists x'. split; [ exact Hwx | ]. split; [ exact Hstx | ].
    intros a Ha. destruct a as [d].
    apply coR_abs_pair_iff. apply He. apply coR_abs_pair_iff. exact Ha.
Qed.



(** * THE COINDUCTIVE, SET-BASED READING OF THE HYPOTHESIS

    [bhv_pre_cond2] quantifies over *whole traces*, and every attempt to
    use it below the bag has foundered on the same point: it hands back a
    run of the left over the same trace, and an **emission cannot be
    replayed backwards**, so the run cannot be re-based at the smaller
    buffer.

    The repository carries a second, equivalent presentation that does
    not have that shape: [DefinitionCI.copre], a **coinductive** relation
    on *sets* of states, with

    - [c_now]  — every stable state of the right set is matched by some
      element of the left set settling below it (this is [Settles], the
      abstracted ready sets unfolding by [coR_abs_pair_iff]);
    - [c_step] — after **one** visible action the relation holds again,
      between the two sets of reducts;
    - [c_tau], [c_cnv] for internal moves and convergence.

    So the hypothesis can be consumed one action at a time, an emission
    included, instead of being instantiated at a trace and then
    un-instantiated.

    [msgs_copre] is the bridge for configurations, composing
    [msgs_accept] with [Soundness.alt_set_singleton_iff] and
    [equivalence_co_inductive_acc_set_and_acc_set].

    ** What it does and does not buy — stated plainly

    [copre] is *equivalent* to [≼ₐₛ], so it carries no new information,
    and a rule taking it as a premise would be vacuous (unlike
    [ax_settle_sim], whose [SettleSim] premise is sound but incomplete).
    What it changes is the **shape**: after [c_step] the left is a *set*
    of reducts and [c_now] promises that *some* element of it settles.

    That is exactly why it points at a different architecture rather than
    at a patch.  The present one keeps a single left configuration, so it
    needs the matching state to be a *specific* one and the semantics
    only ever promises *some* one — the mismatch behind every failed
    route recorded above.  An architecture carrying the whole set, pooled
    syntactically by [VACCS_Matching.ichoice], does not have it: the
    internal choice sits **below** each of its members
    ([ax_ichoice_below]), so a single good element chosen by [c_now]
    suffices, by transitivity, to place the whole choice below the target.
    That is precisely how VCCS's [CompletenessAx.ax_M_below] is organised
    ([leaves], [leafsum], [ichoice]), and it is the part of that
    development VACCS has not ported. *)

Lemma msgs_copre : forall (l l' : list TypeOfActions) (p q : proc),
  ((msgs l ‖ p) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l' ‖ q)) ->
  ({[ (p ▷ bag l) ]} : gset (proc * MO (ExtAct TypeOfActions)))
    ᶜᵒ≼ₐₛ ({[ (q ▷ bag l') ]} : gset (proc * MO (ExtAct TypeOfActions))).
Proof.
  intros l l' p q Hsem.
  apply equivalence_co_inductive_acc_set_and_acc_set.
  apply Soundness.alt_set_singleton_iff.
  apply msgs_accept. exact Hsem.
Qed.


(** ** [c_now], read as [Settles]

    The first brick of the set-based route: the coinductive relation's
    "now" clause *is* the settling condition, once the abstracted ready
    sets are unfolded by [coR_abs_pair_iff].  Stated over sets, because
    that is where the route's leverage lies — after [c_step] the left is
    a set and the promise is that **some** element of it settles. *)

Lemma copre_now_settles :
  forall (X Y : gset (proc * MO (ExtAct TypeOfActions))),
  X ᶜᵒ≼ₐₛ Y -> X ⤓ ->
  forall y, y ∈ Y -> y ↛ -> exists x, x ∈ X /\ Settles (emits y) x.
Proof.
  intros X Y Hco Ht y Hy Hsty.
  destruct (c_now X Y Hco Ht y Hy Hsty) as (x & Hx & x' & Hwx & Hstx & Hincl).
  exists x. split; [ exact Hx | ].
  exists x'. split; [ exact Hwx | ]. split; [ exact Hstx | ].
  intros d w r Hr.
  assert (Hin : (Inputs d) ∈ ⌈ 𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ ⌉ (coR x'))
    by (apply coR_abs_pair_iff; exists w, r; exact Hr).
  apply Hincl in Hin. apply coR_abs_pair_iff in Hin. exact Hin.
Qed.

(** At a singleton it degenerates to the reading already available from
    [bhv_pre_cond2] at the empty trace — as it must, the two being
    equivalent.  It is recorded because it is the base case of the
    intended recursion, and because it fixes the instances: the [⤓] on
    the [gset] must be the *inductive* set LTS ([SetLTSConstruction.toSET]),
    which is what [copre] uses; writing the statement by hand instead
    lets [Set Typeclasses Depth 3] pick the **co** instance
    ([coSetLTSConstruction.coToSET]) and the two do not unify. *)

Corollary copre_settles_from_sem :
  forall (l l' : list TypeOfActions) (p q : proc), Static p ->
  ((msgs l ‖ p) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l' ‖ q)) ->
  ((q ▷ bag l') ↛) -> Settles (emits (q ▷ bag l')) (p ▷ bag l).
Proof.
  intros l l' p q Hp Hsem Hst.
  edestruct (copre_now_settles _ _ (msgs_copre l l' p q Hsem))
    as (x & Hx & HS).
  - apply SetLTSConstruction.termination_set_if_termination.
    eapply fw_terminate_static; [ exact Hp | apply Nat.le_refl ].
  - apply elem_of_singleton_2. reflexivity.
  - exact Hst.
  - apply elem_of_singleton_1 in Hx. subst x. exact HS.
Qed.


(** ** [c_step]: one action, including an EMISSION

    This is what the coinductive presentation buys, and it is exactly
    what no reading of [bhv_pre_cond2] could give.  [c_step] carries the
    relation across **one** visible action between the two reduct sets;
    on the right the set may be taken to be the singleton of the reduct
    (its [spec1] obligation is just "reachable from some element"), on
    the left it is the canonical reduct set
    [FiniteImageLTS.wt_s_set_from_pset], whose [spec] is proved.

    Composing it with [copre_now_settles] gives [copre_settles_after]:
    after the right-hand side performs [μ] and settles, **some
    [μ]-reduct of the left settles below it**.  Take [μ] to be an
    *emission* and the left-hand reduct is at the smaller buffer — the
    certificate below the bag, which the trace reading could never
    produce because an emission cannot be replayed backwards.

    What it still does not give is the *specific* state: the reduct is
    quantified existentially over the whole set.  That is the gap the
    set-based architecture is meant to close, by carrying the set and
    pooling it with [VACCS_Matching.ichoice] — the internal choice lying
    **below** each member, one good element suffices. *)

Lemma copre_step_single :
  forall (X Y : gset (proc * MO (ExtAct TypeOfActions))) y y' mu,
  X ᶜᵒ≼ₐₛ Y ->
  (forall x, x ∈ X -> x ⇓ [mu]) ->
  y ∈ Y -> y ⟶[mu] y' ->
  exists X', FiniteImageLTS.wt_set_from_pset_spec X [mu] X'
        /\ X' ᶜᵒ≼ₐₛ ({[ y' ]} : gset (proc * MO (ExtAct TypeOfActions))).
Proof.
  intros X Y y y' mu Hco Hcnv Hy Hl.
  exists (FiniteImageLTS.wt_s_set_from_pset X [mu] Hcnv).
  pose proof (FiniteImageLTS.wt_s_set_from_pset_ispec X [mu] Hcnv) as Hspec.
  split; [ exact Hspec | ].
  eapply c_step; [ exact Hco | | | exact Hspec ].
  - apply SetLTSConstruction.convergence_set_if_convergence_forall. exact Hcnv.
  - intros z Hz. apply elem_of_singleton_1 in Hz. subst z.
    exists y. split; [ exact Hy | ]. eapply wt_act; [ exact Hl | apply wt_nil ].
Qed.

Theorem copre_settles_after :
  forall (l l' : list TypeOfActions) (p q : proc) mu y', Static p ->
  ((msgs l ‖ p) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l' ‖ q)) ->
  ((q ▷ bag l') ⟶[mu] y') -> y' ↛ ->
  exists x, (p ▷ bag l) ⟹{mu} x /\ Settles (emits y') x.
Proof.
  intros l l' p q mu y' Hp Hsem Hl Hst.
  assert (Hcnv : forall x, x ∈ ({[ (p ▷ bag l) ]} : gset (proc * MO (ExtAct TypeOfActions))) ->
                   x ⇓ [mu]).
  { intros x Hx. apply elem_of_singleton_1 in Hx. subst x.
    apply fw_converge_static. exact Hp. }
  destruct (copre_step_single _ _ (q ▷ bag l') y' mu
              (msgs_copre l l' p q Hsem) Hcnv
              (elem_of_singleton_2 _ _ eq_refl) Hl)
    as (X' & (Hs1 & Hs2) & Hco').
  edestruct (copre_now_settles X' _ Hco') as (x & Hx & HS).
  - apply SetLTSConstruction.termination_forall. intros z Hz.
    apply SetLTSConstruction.termination_set_if_termination.
    destruct (Hs1 z Hz) as (z0 & Hz0 & Hw).
    apply elem_of_singleton_1 in Hz0. subst z0.
    assert (Hz1 : Static z.1)
      by (eapply (fw_static_wt _ (p ▷ bag l)); [ exact Hp | exact Hw ]).
    destruct z as (z1, z2). simpl in Hz1.
    eapply fw_terminate_static; [ exact Hz1 | apply Nat.le_refl ].
  - apply elem_of_singleton_2. reflexivity.
  - exact Hst.
  - destruct (Hs1 x Hx) as (x0 & Hx0 & Hw).
    apply elem_of_singleton_1 in Hx0. subst x0.
    exists x. split; [ exact Hw | exact HS ].
Qed.


(** ** Iterating the coinductive step along a WHOLE TRACE

    [c_step] carries the relation across **one** visible action.
    Iterating it along a trace is a plain induction, and the only care
    it needs is bookkeeping: at each stage the left set is replaced by
    the canonical reduct set [wt_s_set_from_pset], whose members are
    again reachable — hence again [Static] ([fw_static_wt]) and again
    convergent ([fw_converge_static]), which is what the next [c_step]
    asks for.

    Only [wt_set_from_pset_spec1] survives the composition, and that is
    all a consumer needs: every member of the final set is reachable
    from the start over the whole trace.  (The full spec cannot be
    carried, since the composite of two canonical reduct sets is not
    syntactically the canonical set of the concatenated trace.)

    The payoff, [copre_settles_along], generalises
    [copre_settles_after] from one action to an arbitrary trace: after
    the right-hand side runs [s] and settles, **some state the left
    reaches over the same [s]** settles below it.  Taking [s] to contain
    emissions puts the left at a smaller buffer — the certificate below
    the bag. *)

Lemma copre_step_trace :
  forall (s : trace (ExtAct TypeOfActions))
         (X Y : gset (proc * MO (ExtAct TypeOfActions))) y y',
  X ᶜᵒ≼ₐₛ Y ->
  (forall x, x ∈ X -> Static (fst x)) ->
  y ∈ Y -> y ⟹[s] y' ->
  exists X', FiniteImageLTS.wt_set_from_pset_spec1 X s X'
        /\ X' ᶜᵒ≼ₐₛ ({[ y' ]} : gset (proc * MO (ExtAct TypeOfActions))).
Proof.
  induction s as [|mu s IH]; intros X Y y y' Hco HSt Hy Hw.
  - exists X. split.
    + intros z Hz. exists z. split; [ exact Hz | apply wt_nil ].
    + eapply c_tau; [ exact Hco | ].
      intros z Hz. apply elem_of_singleton_1 in Hz. subst z.
      exists y. split; [ exact Hy | exact Hw ].
  - apply wt_pop in Hw as (y1 & Hw1 & Hw2).
    assert (Hcnv : forall x, x ∈ X -> x ⇓ [mu]).
    { intros x Hx. destruct x as (x1,x2). apply fw_converge_static. apply (HSt _ Hx). }
    set (X1 := FiniteImageLTS.wt_s_set_from_pset X [mu] Hcnv).
    pose proof (FiniteImageLTS.wt_s_set_from_pset_ispec X [mu] Hcnv) as Hspec1.
    assert (Hco1 : X1 ᶜᵒ≼ₐₛ ({[ y1 ]} : gset (proc * MO (ExtAct TypeOfActions)))).
    { eapply c_step; [ exact Hco | | | exact Hspec1 ].
      - apply SetLTSConstruction.convergence_set_if_convergence_forall. exact Hcnv.
      - intros z Hz. apply elem_of_singleton_1 in Hz. subst z.
        exists y. split; [ exact Hy | exact Hw1 ]. }
    assert (HSt1 : forall x, x ∈ X1 -> Static (fst x)).
    { intros x Hx. destruct Hspec1 as (Hs1 & _).
      destruct (Hs1 x Hx) as (x0 & Hx0 & Hwx).
      eapply fw_static_wt; [ apply (HSt _ Hx0) | exact Hwx ]. }
    destruct (IH X1 _ y1 y' Hco1 HSt1 (elem_of_singleton_2 _ _ eq_refl) Hw2)
      as (X' & Hs1' & Hco').
    exists X'. split; [ | exact Hco' ].
    intros z Hz. destruct (Hs1' z Hz) as (x1 & Hx1 & Hwz).
    destruct Hspec1 as (Hs1 & _).
    destruct (Hs1 x1 Hx1) as (x0 & Hx0 & Hwx).
    exists x0. split; [ exact Hx0 | eapply wt_push_left; [ exact Hwx | exact Hwz ] ].
Qed.

Theorem copre_settles_along :
  forall (s : trace (ExtAct TypeOfActions)) (l l' : list TypeOfActions) (p q : proc) y',
  Static p ->
  ((msgs l ‖ p) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l' ‖ q)) ->
  ((q ▷ bag l') ⟹[s] y') -> y' ↛ ->
  exists x, (p ▷ bag l) ⟹[s] x /\ Settles (emits y') x.
Proof.
  intros s l l' p q y' Hp Hsem Hw Hst.
  destruct (copre_step_trace s _ _ (q ▷ bag l') y'
              (msgs_copre l l' p q Hsem)
              (fun x Hx => ltac:(apply elem_of_singleton_1 in Hx; subst x; exact Hp))
              (elem_of_singleton_2 _ _ eq_refl) Hw)
    as (X' & Hs1 & Hco').
  edestruct (copre_now_settles X' _ Hco') as (x & Hx & HS).
  - apply SetLTSConstruction.termination_forall. intros z Hz.
    apply SetLTSConstruction.termination_set_if_termination.
    destruct (Hs1 z Hz) as (z0 & Hz0 & Hwz).
    apply elem_of_singleton_1 in Hz0. subst z0.
    assert (Hz1 : Static z.1)
      by (eapply (fw_static_wt _ (p ▷ bag l)); [ exact Hp | exact Hwz ]).
    destruct z as (z1, z2). simpl in Hz1.
    eapply fw_terminate_static; [ exact Hz1 | apply Nat.le_refl ].
  - apply elem_of_singleton_2. reflexivity.
  - exact Hst.
  - destruct (Hs1 x Hx) as (x0 & Hx0 & Hwx).
    apply elem_of_singleton_1 in Hx0. subst x0.
    exists x. split; [ exact Hwx | exact HS ].
Qed.


(** ** A simulation between SETS — the set-based counterpart of [SettleSim]

    [SettleSim] relates LTS *states*, and that is exactly why it cannot
    carry the set-based information the coinductive presentation
    produces (see the note at [VACCS_Matching.ichoice_cfg], and the
    delimitation at [VACCS_Matching.Settles_tau_reduct]): [c_now]
    promises *some* element of a set, while a state-level simulation must
    answer at the state it is given.

    The fix is to make the premise itself set-based.  The clauses below
    are [copre]'s own — τ-closure on the right, one visible action, and
    the "now" clause — with [Settles] in place of the abstracted
    ready-set inclusion, and with no convergence obligations: on the
    [Static] fragment those are free ([fw_terminate_static]).

    Crucially this is **not** circular.  [copre] is *equivalent* to
    [⊑ₘᵤₛₜᵢ], so a rule taking [copre] as its premise would be vacuous;
    but an exhibited relation [R] satisfying the clauses is only
    *contained* in [copre] — the same relationship [SettleSim] has to
    [≼ₐₛ].  The user must supply [R].

    Mechanical note: the clauses are spelled out rather than packaged in
    a [Definition], and [R]'s type is a binder of the *same* statement as
    the [copre] conclusion.  Both are forced by instance resolution: a
    standalone [Definition] elaborates its [gset] at the [prod_countable]
    instances, whereas [copre] wants [FiniteImageLTS]'s own — and the two
    do not unify.  Stating everything together lets unification pick one.
    (This is the same family of traps recorded for [⤓] and for
    [lts_refuses_spec1/2].) *)

Lemma set_sim_copre :
  forall (R : gset (proc * MO (ExtAct TypeOfActions)) ->
              gset (proc * MO (ExtAct TypeOfActions)) -> Prop),
  (forall X Y, R X Y -> forall y, y ∈ Y -> Static (fst y)) ->
  (forall X Y Y', R X Y ->
     (forall z, z ∈ Y' -> exists y, y ∈ Y /\ y ⟹[[]] z) -> R X Y') ->
  (forall X Y mu X' Y', R X Y ->
     (forall z, z ∈ Y' -> exists y, y ∈ Y /\ y ⟹[[mu]] z) ->
     (forall z, z ∈ X' -> exists x, x ∈ X /\ x ⟹[[mu]] z) ->
     (forall x z, x ∈ X -> x ⟹[[mu]] z -> z ∈ X') ->
     R X' Y') ->
  (forall X Y y, R X Y -> y ∈ Y -> y ↛ ->
     exists x, x ∈ X /\ Settles (emits y) x) ->
  forall X Y, R X Y -> X ᶜᵒ≼ₐₛ Y.
Proof.
  intros R HStY Htau Hstep Hnow.
  cofix CH. intros X Y H. constructor.
  - intros Y' HY'. apply CH. eapply Htau; [ exact H | ]. exact HY'.
  - intros _ y Hy Hst.
    destruct (Hnow X Y y H Hy Hst) as (x & Hx & HS).
    exists x. split; [ exact Hx | ].
    destruct HS as (x' & Hw & Hst' & Hem).
    exists x'. split; [ exact Hw | ]. split; [ exact Hst' | ].
    intros a Ha. destruct a as [d].
    apply coR_abs_pair_iff. apply coR_abs_pair_iff in Ha.
    destruct Ha as (w & r & Hr). eapply Hem. exact Hr.
  - intros mu Y' X' _ HY' (Hs1 & Hs2). apply CH.
    eapply Hstep; [ exact H | exact HY' | exact Hs1 | exact Hs2 ].
  - intros _. apply SetLTSConstruction.termination_forall. intros z Hz.
    apply SetLTSConstruction.termination_set_if_termination.
    pose proof (HStY X Y H z Hz) as Hs. destruct z as (z1,z2). simpl in Hs.
    eapply fw_terminate_static; [ exact Hs | apply Nat.le_refl ].
Qed.

(** The converse of [msgs_copre]: at singletons the coinductive relation
    is the configuration preorder. *)

Lemma copre_msgs : forall (l l' : list TypeOfActions) (p q : proc),
  ({[ (p ▷ bag l) ]} : gset (proc * MO (ExtAct TypeOfActions)))
    ᶜᵒ≼ₐₛ ({[ (q ▷ bag l') ]} : gset (proc * MO (ExtAct TypeOfActions))) ->
  ((msgs l ‖ p) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l' ‖ q)).
Proof.
  intros l l' p q H. apply msgs_accept_iff.
  apply Soundness.alt_set_singleton_iff.
  apply equivalence_co_inductive_acc_set_and_acc_set. exact H.
Qed.

(** …and the soundness statement a rule can be built on: exhibiting a
    set-simulation relating the two singletons establishes the
    configuration inequation. *)

Theorem set_sim_below_bag :
  forall (R : gset (proc * MO (ExtAct TypeOfActions)) ->
              gset (proc * MO (ExtAct TypeOfActions)) -> Prop),
  (forall X Y, R X Y -> forall y, y ∈ Y -> Static (fst y)) ->
  (forall X Y Y', R X Y ->
     (forall z, z ∈ Y' -> exists y, y ∈ Y /\ y ⟹[[]] z) -> R X Y') ->
  (forall X Y mu X' Y', R X Y ->
     (forall z, z ∈ Y' -> exists y, y ∈ Y /\ y ⟹[[mu]] z) ->
     (forall z, z ∈ X' -> exists x, x ∈ X /\ x ⟹[[mu]] z) ->
     (forall x z, x ∈ X -> x ⟹[[mu]] z -> z ∈ X') ->
     R X' Y') ->
  (forall X Y y, R X Y -> y ∈ Y -> y ↛ ->
     exists x, x ∈ X /\ Settles (emits y) x) ->
  forall (l l' : list TypeOfActions) (p q : proc),
  R ({[ (p ▷ bag l) ]} : gset (proc * MO (ExtAct TypeOfActions)))
    ({[ (q ▷ bag l') ]} : gset (proc * MO (ExtAct TypeOfActions))) ->
  ((msgs l ‖ p) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l' ‖ q)).
Proof.
  intros R H1 H2 H3 H4 l l' p q HR.
  apply copre_msgs. eapply set_sim_copre; eauto.
Qed.


(** ** …AND WHY IT MUST NOT BECOME A RULE — the clauses are satisfied by
       [copre] itself

    [set_sim_below_bag] is sound, and it was briefly added to the system
    as a constructor.  That was a mistake, and the two results below are
    the machine-checked reason it was removed.

    A premise is worth having only if it is *strictly stronger* than the
    conclusion.  [SettleSim] is: it demands, at each state, a matching
    weak transition **preserving the relation**, and a behavioural
    preorder is not a simulation — [≼ₐₛ]'s [cond2] quantifies over
    stable reducts after a trace and gives no such per-step matching.

    The set-based clauses are **not**.  They are literally [copre]'s own
    fields, and [copre] is coinductively defined by them — so the
    relation "[copre] and both sides [Static]" satisfies every one of
    them ([set_sim_clauses_hold_for_copre]), and it relates every
    semantically-below pair of configurations ([copre_st_of_sem]).  A
    rule with those clauses as premise would therefore derive
    [⊢ p ⊑ q] from [p ⊑ₘᵤₛₜᵢ q] outright, trivialising completeness and
    emptying the axiom system of content.

    So [set_sim_copre]/[set_sim_below_bag] are kept as what they really
    are — the **coinduction principle** for [copre], a proof technique —
    and the rule set stays at 26.

    **And the objection is not specific to these clauses.**  Weakening
    them does not help, it makes matters worse: a variant in which the
    left answer is a *user-chosen* list of reachable states, rather than
    the full reduct set, is satisfied a fortiori — carry "every state
    reachable from the left over the trace the right has taken" and the
    step clauses hold by construction, while the stable clause is
    literally [bhv_pre_cond2].  Since the clauses are weaker, [copre]
    satisfies them too, and the theorem below applies unchanged.

    The general shape of the objection: **a simulation premise is
    non-vacuous only if it pins the left to a single state.**  That is
    exactly what [SettleSim] does and what makes [ax_settle_sim] a real
    restriction — and, conversely, it is why the certificate
    [Settles (chans K) (P ▷ K)] has to hold at the *specific* [P]
    ([VACCS_Matching.ax_phaseA_direct]), which is the residue this
    development is left with. *)

Theorem set_sim_clauses_hold_for_copre :
  (forall (X Y : gset (proc * MO (ExtAct TypeOfActions))),
     (X ᶜᵒ≼ₐₛ Y /\ (forall x, x ∈ X -> Static (fst x))
                /\ (forall y, y ∈ Y -> Static (fst y))) ->
     forall y, y ∈ Y -> Static (fst y))
  /\ (forall (X Y Y' : gset (proc * MO (ExtAct TypeOfActions))),
     (X ᶜᵒ≼ₐₛ Y /\ (forall x, x ∈ X -> Static (fst x))
                /\ (forall y, y ∈ Y -> Static (fst y))) ->
     (forall z, z ∈ Y' -> exists y, y ∈ Y /\ y ⟹[[]] z) ->
     (X ᶜᵒ≼ₐₛ Y' /\ (forall x, x ∈ X -> Static (fst x))
                 /\ (forall y, y ∈ Y' -> Static (fst y))))
  /\ (forall (X Y X' Y' : gset (proc * MO (ExtAct TypeOfActions))) mu,
     (X ᶜᵒ≼ₐₛ Y /\ (forall x, x ∈ X -> Static (fst x))
                /\ (forall y, y ∈ Y -> Static (fst y))) ->
     (forall z, z ∈ Y' -> exists y, y ∈ Y /\ y ⟹[[mu]] z) ->
     (forall z, z ∈ X' -> exists x, x ∈ X /\ x ⟹[[mu]] z) ->
     (forall x z, x ∈ X -> x ⟹[[mu]] z -> z ∈ X') ->
     (X' ᶜᵒ≼ₐₛ Y' /\ (forall x, x ∈ X' -> Static (fst x))
                  /\ (forall y, y ∈ Y' -> Static (fst y))))
  /\ (forall (X Y : gset (proc * MO (ExtAct TypeOfActions))) y,
     (X ᶜᵒ≼ₐₛ Y /\ (forall x, x ∈ X -> Static (fst x))
                /\ (forall y, y ∈ Y -> Static (fst y))) ->
     y ∈ Y -> y ↛ -> exists x, x ∈ X /\ Settles (emits y) x).
Proof.
  split; [ | split; [ | split ] ].
  - intros X Y (_ & _ & HY). exact HY.
  - intros X Y Y' (Hco & HX & HY) Hspec. split; [ | split ].
    + eapply c_tau; [ exact Hco | exact Hspec ].
    + exact HX.
    + intros z Hz. destruct (Hspec z Hz) as (y & Hy & Hw).
      eapply fw_static_wt; [ apply (HY _ Hy) | exact Hw ].
  - intros X Y X' Y' mu (Hco & HX & HY) HY' HX'1 HX'2. split; [ | split ].
    + eapply c_step; [ exact Hco | | exact HY' | split; [ exact HX'1 | exact HX'2 ] ].
      apply SetLTSConstruction.convergence_set_if_convergence_forall.
      intros x Hx. destruct x as (x1,x2). apply fw_converge_static. apply (HX _ Hx).
    + intros z Hz. destruct (HX'1 z Hz) as (x & Hx & Hw).
      eapply fw_static_wt; [ apply (HX _ Hx) | exact Hw ].
    + intros z Hz. destruct (HY' z Hz) as (y & Hy & Hw).
      eapply fw_static_wt; [ apply (HY _ Hy) | exact Hw ].
  - intros X Y y (Hco & HX & HY) Hy Hst.
    edestruct (c_now _ _ Hco) as (x & Hx & x' & Hw & Hst' & Hincl).
    + apply SetLTSConstruction.termination_forall. intros z Hz.
      apply SetLTSConstruction.termination_set_if_termination.
      pose proof (HX z Hz) as Hs. destruct z as (z1,z2). simpl in Hs.
      eapply fw_terminate_static; [ exact Hs | apply Nat.le_refl ].
    + exact Hy.
    + exact Hst.
    + exists x. split; [ exact Hx | ].
      exists x'. split; [ exact Hw | ]. split; [ exact Hst' | ].
      intros d w r Hr. apply coR_abs_pair_iff. apply Hincl.
      apply coR_abs_pair_iff. exists w, r. exact Hr.
Qed.

Lemma copre_st_of_sem : forall (l l' : list TypeOfActions) (p q : proc),
  Static p -> Static q ->
  ((msgs l ‖ p) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l' ‖ q)) ->
  (({[ (p ▷ bag l) ]} : gset (proc * MO (ExtAct TypeOfActions)))
      ᶜᵒ≼ₐₛ ({[ (q ▷ bag l') ]} : gset (proc * MO (ExtAct TypeOfActions)))
   /\ (forall x, x ∈ ({[ (p ▷ bag l) ]} : gset (proc * MO (ExtAct TypeOfActions))) ->
         Static (fst x))
   /\ (forall y, y ∈ ({[ (q ▷ bag l') ]} : gset (proc * MO (ExtAct TypeOfActions))) ->
         Static (fst y))).
Proof.
  intros l l' p q Hp Hq Hsem. split; [ | split ].
  - apply msgs_copre. exact Hsem.
  - intros x Hx. apply elem_of_singleton_1 in Hx. subst x. exact Hp.
  - intros y Hy. apply elem_of_singleton_1 in Hy. subst y. exact Hq.
Qed.


(** ** The repository's OWN completeness tests, read at the forwarder

    The generic completeness proof for acceptance sets
    ([Acceptance_Set/Completeness.v]) builds two tests: one for
    convergence — useless here, since [Static] processes always converge
    ([Static_converge]) — and one for an acceptance set, specified by
    [test_co_acceptance_set_spec] and instantiated for VACCS in
    [VACCS_ta_tc_gen.gen_acc].

    Reading that instance is instructive, because its acceptance part is
    **literally** the probe built by hand here:
    [unroll_fw L = Σ_{Inputs c ∈ L} (c ? ①)] is [VACCS_Matching.probes].
    What it has in addition is the two things the hand-rolled version
    lacked:

    - a **trace driver** ([gen_test_raw]): the test replays the co-trace,
      handing the server's inputs over *in parallel*
      ([(c!v•𝟘) ‖ rest] — asynchrony, no ordering imposed) and absorbing
      the server's outputs with a guard;
    - **escape hatches**: every input guard is [… + 𝛕 • ①], and a wrong
      value leads to [If … Else ①].  So any run that deviates from the
      intended trace makes the test succeed *immediately*.

    That second point is exactly what defeated the hand-rolled attempt
    (see the note at [VACCS_Matching.probe_test]): a test with no escape
    can be deadlocked by a run that settles quietly, and [must]
    quantifies over **all** runs.

    And the payoff is [must_ta_or_empty_pre_action_set_for_all_trace],
    which is the constructive dichotomy this development was missing —
    at *any* trace, and with [Settles] as its good branch (unfold
    [Settles] and [coR_abs_pair_iff]: "stable, reachable, emitting
    within [E]" is exactly the first disjunct).  It applies at the VACCS
    forwarder directly. *)

Lemma settles_or_test :
  forall (p : proc * MO (ExtAct TypeOfActions)) s E (hcnv : p ⇓ s),
  (exists x, p ⟹[s] x /\ lts_refuses x τ /\ coR_abs x ⊆ E)
  \/ p must_pass (gen_acc ((oas p s hcnv) ∖ E) (coₜ s)).
Proof.
  intros. exact (must_ta_or_empty_pre_action_set_for_all_trace s p hcnv E).
Qed.

End VACCS_Cond2.
