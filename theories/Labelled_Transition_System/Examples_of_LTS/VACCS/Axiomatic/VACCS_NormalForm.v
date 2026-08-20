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

(** * The VACCS normal form: [Ѵⁿ (messages ‖ guarded sum)]

        [NF n l M := Ѵ n (msgs l ‖ g M)]

    every [Static] process is [⊢]-equal to one, with [gStatic M].

    **This shape is the forwarder state [p ▷ m], written syntactically** —
    a residue in parallel with a bag of pending messages, under a block of
    restrictions.  It is forced on us, and the reason is the one recorded
    at [VACCS_Expansion.v]: an output [c!v•𝟘] is not a [gproc] at all, so a
    parallel composition involving one can never be flattened into a
    guarded sum.  VCCS's normal form is a bare [g M]; VACCS's cannot be.

    ** Why this is markedly easier than VCCS's [normal_form]

    VCCS's version had to be strengthened with [step_dominated] and cost a
    whole checkpoint, because normalisation there is *not* size-decreasing
    (the expansion law blows terms up) and the [𝛕]-continuations had to be
    re-normalised.  Here the recursion is plain structural induction on
    [size]: each case recurses on strict subterms, and the expansion law is
    applied **once**, at the end of the [‖] case, to two *already
    normalised* sums.  Nothing is ever re-normalised.

    The only real work is de Bruijn bookkeeping: pulling both operands'
    restriction blocks to the top by scope extrusion, which shifts the
    other operand's channels.  [VACCS_Instance.v] already provides
    everything for that ([cgr_res_scope_n], [NewVarCn_res], [cgr_res_n]);
    what had to be added is how [NewVarCn] distributes over a message list. *)

From Stdlib.Wellfounded Require Import Inverse_Image.
From Stdlib Require Import List Permutation PeanoNat Lia.
From stdpp Require Import base gmultiset.
From TestingTheory Require Import VACCS VACCS_Instance Must ActTau InputOutputActions
  gLts Bisimulation InteractionBetweenLts Testing_Predicate VACCS_Good WeakTransitions
  Subset_Act DefinitionAS Convergence VACCS_Static VACCS_Must_Characterization
  VACCS_Erasure VACCS_Shift VACCS_Precongruence VACCS_Expansion VACCS_ResNormalize
  VACCS_Copycat VACCS_DefinitionAxiomatic VACCS_SoundnessAx.
From TestingTheory Require Import MultisetLTSConstruction ForwarderConstruction
  VACCS_Forwarder VACCS_Cond2.
Import ListNotations.

Section VACCS_NormalForm.

Context `{VP : VACCS_Parameters}.

(** Shifting a message's channel [n] times, at depth [k] — what scope
    extrusion does to the *other* operand of a [‖]. *)
Definition shiftCn (k n : nat) (cv : ChannelData * ValueData) : ChannelData * ValueData :=
  (Nat.iter n (NewVar_in_ChannelData k) (fst cv), snd cv).

Definition NF (n : nat) (l : list (ChannelData * ValueData)) (M : gproc) : proc :=
  Ѵ n (msgs l ‖ g M).

(** A buffer empties along its own output trace.  This is the run the
    acceptance condition is read at when one wants to see the *bag*:
    the ready-set abstraction erases both the value and the multiplicity
    of a pending message, so a bag is only observable through traces. *)

Lemma bag_wt_drain : forall (l : list TypeOfActions) (p0 : proc)
    (m : MO (ExtAct TypeOfActions)),
  ((p0 ▷ (bag l ⊎ m)) ⟹[map ActOut l] (p0 ▷ m)).
Proof.
  induction l as [ | a l IH ]; intros p0 m; simpl.
  - replace ((∅ : MO (ExtAct TypeOfActions)) ⊎ m) with m
      by (symmetry; apply (gmultiset.gmultiset_disj_union_left_id m)).
    apply wt_nil.
  - replace (({[+ ActOut a +]} ⊎ bag l) ⊎ m)
       with ({[+ ActOut a +]} ⊎ (bag l ⊎ m))
      by (apply (assoc_L (@disj_union (MO (ExtAct TypeOfActions)) _))).
    eapply wt_act; [ apply fw_emit | apply IH ].
Qed.

(** ** THE TWO BAGS AGREE

    For two *stable* configurations the pending-message bags are equal —
    not merely their channel sets.  Read the acceptance condition along
    the trace that empties the right-hand bag: the right settles at
    [g N ▷ ∅], which is stable and offers no output at all, so the left
    must reach a stable state over the *same* trace that likewise offers
    nothing.  [fw_out_run_drain] says such a run of a stable configuration
    with a mute process is pure buffer emission, so the trace is exactly
    the part of the left bag that left — and what stayed behind must be
    empty, since the reached state offers nothing.

    This is where the message layer's information actually lives: the
    ready-set abstraction erases a message's value *and* its multiplicity
    ([VACCS_ReadySet.coR_abs_iff]), so at [ε] the bags are invisible; only
    an output trace sees them, and it sees them exactly.  Compare the two
    probes in [VACCS_DropProbes.v] ([msg_not_below_nil],
    [nil_not_below_msg]), which are the degenerate instances. *)

Theorem bags_agree : forall (l l' : list TypeOfActions) (M N : gproc),
  gStatic M ->
  (forall z, ~ ((g M ▷ bag l) ⟶ z)) ->
  (forall q, ~ lts (g N) τ q) ->
  ((msgs l ‖ g M) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l' ‖ g N)) ->
  bag l = bag l'.
Proof.
  intros l l' M N HM HstM HNtau Hpre.
  destruct (msgs_accept l l' (g M) (g N) Hpre) as (Hc1 & Hc2).
  assert (Hdr : (g N ▷ bag l') ⟹[map ActOut l'] (g N ▷ (∅ : MO (ExtAct TypeOfActions)))).
  { replace (bag l') with (bag l' ⊎ (∅ : MO (ExtAct TypeOfActions)))
      by (apply gmultiset.gmultiset_disj_union_right_id).
    apply bag_wt_drain. }
  assert (HstN0 : forall z, ~ ((g N ▷ (∅ : MO (ExtAct TypeOfActions))) ⟶ z)).
  { apply fw_stable_iff. split; [ exact HNtau | ].
    intros a Ha. exfalso. eapply gmultiset.gmultiset_not_elem_of_empty. exact Ha. }
  destruct (Hc2 (map ActOut l') (g N ▷ (∅ : MO (ExtAct TypeOfActions)))
             (fw_converge_static (map ActOut l') (g M) (bag l) (static_g M HM))
             Hdr (stable_of_no_step _ HstN0))
    as (x & Hwx & Hstx & Hincl).
  assert (Hnoemit : forall a y, ~ (x ⟶[ActOut a] y)).
  { intros (d,w) y Hy.
    assert (Hin : (Inputs d) ∈ ⌈ 𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ ⌉ (coR x))
      by (apply coR_abs_pair_iff; exists w, y; exact Hy).
    apply Hincl in Hin. apply coR_abs_pair_iff in Hin as (w' & r & Hr).
    assert (Hex : exists y0, ((g N) ▷ (∅ : MO (ExtAct TypeOfActions))) ⟶[ActOut (d,w')] y0)
      by (exists r; exact Hr).
    apply fw_emits_iff in Hex as [ (p' & Hp') | Hmem ].
    - eapply gsum_no_output. exact Hp'.
    - eapply gmultiset.gmultiset_not_elem_of_empty. exact Hmem. }
  destruct (fw_out_run_drain (map ActOut l') (g M ▷ bag l) x Hwx (ins_map_out l'))
    as (Hx1 & Hx2).
  - intros a p' Hp'. simpl in Hp'. destruct a as (d,w). eapply gsum_no_output. exact Hp'.
  - exact HstM.
  - rewrite outs_map_out in Hx2. simpl in Hx2.
    assert (Hempty : x.2 = ∅).
    { destruct x as (x1,x2). simpl in *.
      eapply fw_no_emit_empty_buffer; [ | intros a y Hy; eapply Hnoemit; exact Hy ].
      intros z Hz. eapply bag_out. rewrite <- Hx2.
      apply gmultiset.gmultiset_elem_of_disj_union. right. exact Hz. }
    rewrite Hempty in Hx2.
    rewrite <- Hx2. apply gmultiset.gmultiset_disj_union_right_id.
Qed.

(** ** The settling certificate, at a configuration

    [VACCS_Cond2.surplus_settles_bag] reads the acceptance condition at
    the trace that feeds a bag in, and concludes that the left settles
    inside the bag's channels.  Here is the same argument with the *left
    already holding a bag of its own*: the buffers are shifted by
    [bag l] throughout, and nothing else changes — which is exactly the
    point of [msgs_accept_iff].

    This is the form Phase A needs at a configuration, where the left is
    [msgs l ‖ g M] and may well be **unstable** (its own guards can
    consume part of [l]) — a case [bags_agree] does not cover. *)

Theorem surplus_settles_config : forall (M N : gproc) (l k : list TypeOfActions),
  gStatic M -> gStatic N ->
  (forall p, ~ lts (g N) τ p) ->
  (forall a, ActOut a ∈ (bag k ⊎ bag l) -> forall r, ~ lts (g N) (ActExt (ActIn a)) r) ->
  ((msgs l ‖ g M) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ g N)) ->
  Settles (chans (bag k ⊎ bag l)) ((g M) ▷ (bag k ⊎ bag l)).
Proof.
  intros M N l k HM HN HstN Hnoc Hsem.
  assert (Hnostep : forall x, ~ (((g N) ▷ (bag k ⊎ bag l)) ⟶ x)).
  { apply fw_stable_iff. split; [ exact HstN | ].
    intros a Hin q Hq. eapply Hnoc; [ exact Hin | exact Hq ]. }
  assert (Hsty : ((g N) ▷ (bag k ⊎ bag l)) ↛) by (apply stable_of_no_step; exact Hnostep).
  assert (Hwq : ((g N) ▷ bag l) ⟹[feed k] ((g N) ▷ (bag k ⊎ bag l))).
  { replace (feed k) with (feed k ++ (nil : trace (ExtAct TypeOfActions)))
      by (rewrite app_nil_r; reflexivity).
    apply fw_wt_feed_list. apply wt_nil. }
  destruct (msgs_accept l l (g M) (g N) Hsem) as (Hc1 & Hc2).
  destruct (Hc2 (feed k) ((g N) ▷ (bag k ⊎ bag l))
              (fw_converge_static (feed k) (g M) (bag l) (static_g M HM)) Hwq Hsty)
    as (x & Hwx & Hstx & Hincl).
  exists x. split.
  - pose proof (fw_feed_inv_list k ((g M) ▷ bag l) x Hwx) as H. simpl in H. exact H.
  - split; [ exact Hstx | ].
    intros d w r Hr.
    assert (Hin : (Inputs d) ∈ ⌈ 𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ ⌉ (coR x))
      by (apply coR_abs_pair_iff; exists w, r; exact Hr).
    apply Hincl in Hin. apply coR_abs_pair_iff in Hin.
    eapply emits_gsum_chans. exact Hin.
Qed.

(** The multiset form, via [outonly_bag] — every buffer the forwarder can
    reach is a bag. *)

Corollary certificate_config : forall (M N : gproc) (l : list TypeOfActions),
  gStatic M -> gStatic N ->
  (forall p, ~ lts (g N) τ p) ->
  ((msgs l ‖ g M) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ g N)) ->
  forall m, OutOnly m ->
    (forall a, ActOut a ∈ (m ⊎ bag l) -> forall r, ~ lts (g N) (ActExt (ActIn a)) r) ->
    Settles (chans (m ⊎ bag l)) ((g M) ▷ (m ⊎ bag l)).
Proof.
  intros M N l HM HN HstN Hsem m Hout Hnoc.
  destruct (outonly_bag m Hout) as (k & Hk). subst m.
  apply surplus_settles_config with (N := N); assumption.
Qed.

(** ** THE CERTIFICATE IN THE **SPLIT** SETTING, ON THE CONE ABOVE THE BAG

    When the left carries a surplus bag [d] — the shape
    [VACCS_Matching.ax_below_split_from_certificate] compares — the
    certificate it asks for is [Settles (chans K) (g M ▷ (bag d ⊎ K))]:
    the left must settle emitting **only within [K]**, hence absorb the
    whole of [d].

    Two positive fragments, and the first is the striking one:

    - at [K = bag l] it is *exactly* [bhv_pre_cond2] read at the **empty
      trace**.  The right-hand state [g N ▷ bag l] is stable by
      hypothesis and emits exactly [chans (bag l)], so the condition
      hands the required run over directly — no drain, no feeding, no
      side condition on regeneration.  The obligation that looked like
      the whole difficulty is free at that one buffer.
    - above it, at [K = bag k ⊎ bag l], the same reading at the trace
      [feed k] works, feeding being reversible ([fw_feed_inv_list]).

    What is still missing is the region **below** the bag, reachable when
    the right-hand side emits — the same frontier as everywhere else in
    this development. *)

Lemma bag_app : forall (d l : list TypeOfActions), bag (d ++ l) = bag d ⊎ bag l.
Proof.
  induction d as [|a d IH]; intro l; simpl.
  - symmetry. apply (left_id_L (∅ : MO (ExtAct TypeOfActions))
                       (@disj_union (MO (ExtAct TypeOfActions)) _)).
  - rewrite IH. apply (assoc_L (@disj_union (MO (ExtAct TypeOfActions)) _)).
Qed.

Theorem certificate_at_bag : forall (M N : gproc) (d l : list TypeOfActions),
  gStatic M -> gStatic N ->
  (forall x, ~ (((g N) ▷ bag l) ⟶ x)) ->
  ((msgs (d ++ l) ‖ g M) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ g N)) ->
  Settles (chans (bag l)) (((g M) : proc) ▷ (bag d ⊎ bag l)).
Proof.
  intros M N d l HM HN Hns Hsem.
  destruct (msgs_accept (d ++ l) l (g M) (g N) Hsem) as (Hc1 & Hc2).
  assert (Hsty : ((g N) ▷ bag l) ↛) by (apply stable_of_no_step; exact Hns).
  destruct (Hc2 [] ((g N) ▷ bag l)
              (fw_converge_static [] (g M) (bag (d ++ l)) (static_g M HM))
              (wt_nil _) Hsty)
    as (x & Hwx & Hstx & Hincl).
  exists x. split.
  - rewrite <- bag_app. exact Hwx.
  - split; [ exact Hstx | ].
    intros e w r Hr.
    assert (Hin : (Inputs e) ∈ ⌈ 𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ ⌉ (coR x))
      by (apply coR_abs_pair_iff; exists w, r; exact Hr).
    apply Hincl in Hin. apply coR_abs_pair_iff in Hin.
    eapply emits_gsum_chans. exact Hin.
Qed.

Theorem certificate_above_bag : forall (M N : gproc) (d l k : list TypeOfActions),
  gStatic M -> gStatic N ->
  (forall x, ~ (((g N) ▷ (bag k ⊎ bag l)) ⟶ x)) ->
  ((msgs (d ++ l) ‖ g M) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ g N)) ->
  Settles (chans (bag k ⊎ bag l)) (((g M) : proc) ▷ (bag d ⊎ (bag k ⊎ bag l))).
Proof.
  intros M N d l k HM HN Hns Hsem.
  destruct (msgs_accept (d ++ l) l (g M) (g N) Hsem) as (Hc1 & Hc2).
  assert (Hsty : ((g N) ▷ (bag k ⊎ bag l)) ↛) by (apply stable_of_no_step; exact Hns).
  assert (Hwq : ((g N) ▷ bag l) ⟹[feed k] ((g N) ▷ (bag k ⊎ bag l))).
  { replace (feed k) with (feed k ++ (nil : trace (ExtAct TypeOfActions)))
      by (rewrite app_nil_r; reflexivity).
    apply fw_wt_feed_list. apply wt_nil. }
  destruct (Hc2 (feed k) ((g N) ▷ (bag k ⊎ bag l))
              (fw_converge_static (feed k) (g M) (bag (d ++ l)) (static_g M HM))
              Hwq Hsty)
    as (x & Hwx & Hstx & Hincl).
  exists x. split.
  - pose proof (fw_feed_inv_list k ((g M) ▷ bag (d ++ l)) x Hwx) as H. simpl in H.
    replace (bag d ⊎ (bag k ⊎ bag l)) with (bag k ⊎ bag (d ++ l)); [ exact H | ].
    rewrite bag_app.
    rewrite !(assoc_L (@disj_union (MO (ExtAct TypeOfActions)) _)). f_equal.
    apply (comm_L (@disj_union (MO (ExtAct TypeOfActions)) _)).
  - split; [ exact Hstx | ].
    intros e w r Hr.
    assert (Hin : (Inputs e) ∈ ⌈ 𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ ⌉ (coR x))
      by (apply coR_abs_pair_iff; exists w, r; exact Hr).
    apply Hincl in Hin. apply coR_abs_pair_iff in Hin.
    eapply emits_gsum_chans. exact Hin.
Qed.

(** ** DRAIN, THEN REFILL — the certificate BELOW the bag

    [certificate_config] covers the buffers *above* the bag, [m ⊎ bag l],
    and that is forced: it reads [bhv_pre_cond2] along a trace of
    **inputs**, and feeding is reversible ([fw_feed_inv_list]), so a run
    over [feed k] from [g M ▷ bag l] *is* a run over [ε] from
    [g M ▷ (bag k ⊎ bag l)] — exactly what [Settles] asks for.  Emission
    is not reversible, so the same reading gives nothing below the bag.

    But the client has one more trace available: **drain the bag, then
    refill it**.  [drain_refill_run] builds it on the right-hand side,
    and [wt_split] cuts the matching left-hand run in two — the drain,
    then the refill, whose [feed] part is again reversible.  What is left
    over is precisely the *state the left reaches after draining*, and
    the whole gap is whether that state is [g M] with an empty buffer.

    It need not be.  A continuation may **regenerate** a message the left
    has emitted — a copycat does exactly that — so the left can drain its
    bag while its process has moved on.  That single possibility is
    [surplus_settles_drain]'s only hypothesis, and it is stated as such
    rather than assumed away: with it, the certificate holds at **every**
    buffer, above or below the bag, and Phase A goes through at an
    unstable configuration; without it, the drain reading collapses.

    So the residue of the unstable-left gap is one named, checkable side
    condition — "the left's drain run is forced" — and no longer a
    mystery about which buffers are reachable. *)

Lemma drain_refill_run : forall (N : gproc) (l k : list TypeOfActions),
  ((g N) ▷ bag l) ⟹[map ActOut l ++ feed k] ((g N) ▷ bag k).
Proof.
  intros N l k. eapply wt_concat.
  - assert (E : bag l = bag l ⊎ (∅ : MO (ExtAct TypeOfActions)))
      by (symmetry; apply gmultiset_disj_union_right_id).
    rewrite E at 1. apply bag_wt_drain.
  - replace (feed k) with (feed k ++ (nil : trace (ExtAct TypeOfActions)))
      by (rewrite app_nil_r; reflexivity).
    apply fw_wt_feed_list. simpl.
    match goal with |- context[@disj_union ?T ?d (bag k) ?e] =>
      assert (Eg : @disj_union T d (bag k) e = bag k)
        by (apply gmultiset_disj_union_right_id)
    end.
    rewrite Eg. apply wt_nil.
Qed.

Theorem surplus_settles_drain : forall (M N : gproc) (l k : list TypeOfActions),
  gStatic M -> gStatic N ->
  (forall p, ~ lts (g N) τ p) ->
  (forall a, ActOut a ∈ bag k -> forall r, ~ lts (g N) (ActExt (ActIn a)) r) ->
  ((msgs l ‖ g M) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ g N)) ->
  (forall y, ((g M) ▷ bag l) ⟹[map ActOut l] y ->
             y = ((g M) ▷ (∅ : MO (ExtAct TypeOfActions)))) ->
  Settles (chans (bag k)) ((g M) ▷ bag k).
Proof.
  intros M N l k HM HN HstN Hnoc Hsem Hdrain.
  assert (Hnostep : forall x, ~ (((g N) ▷ bag k) ⟶ x)).
  { apply fw_stable_iff. split; [ exact HstN | ].
    intros a Hin q Hq. eapply Hnoc; [ exact Hin | exact Hq ]. }
  assert (Hsty : ((g N) ▷ bag k) ↛) by (apply stable_of_no_step; exact Hnostep).
  destruct (msgs_accept l l (g M) (g N) Hsem) as (Hc1 & Hc2).
  destruct (Hc2 (map ActOut l ++ feed k) ((g N) ▷ bag k)
              (fw_converge_static (map ActOut l ++ feed k) (g M) (bag l) (static_g M HM))
              (drain_refill_run N l k) Hsty)
    as (x & Hwx & Hstx & Hincl).
  apply wt_split in Hwx as (y & Hwy & Hwx2).
  specialize (Hdrain y Hwy). subst y.
  exists x. split.
  - pose proof (fw_feed_inv_list k ((g M) ▷ (∅ : MO (ExtAct TypeOfActions))) x Hwx2) as H.
    simpl in H.
    match goal with H0 : (?p ▷ @disj_union ?T ?d (bag k) ?e) ⟹[_] _ |- _ =>
      assert (Eg : @disj_union T d (bag k) e = bag k)
        by (apply gmultiset_disj_union_right_id)
    end.
    rewrite Eg in H. exact H.
  - split; [ exact Hstx | ].
    intros d w r Hr.
    assert (Hin : (Inputs d) ∈ ⌈ 𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ ⌉ (coR x))
      by (apply coR_abs_pair_iff; exists w, r; exact Hr).
    apply Hincl in Hin. apply coR_abs_pair_iff in Hin.
    eapply emits_gsum_chans. exact Hin.
Qed.

(** The multiset form, as for [certificate_config]. *)

Corollary certificate_drain : forall (M N : gproc) (l : list TypeOfActions),
  gStatic M -> gStatic N ->
  (forall p, ~ lts (g N) τ p) ->
  ((msgs l ‖ g M) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ g N)) ->
  (forall y, ((g M) ▷ bag l) ⟹[map ActOut l] y ->
             y = ((g M) ▷ (∅ : MO (ExtAct TypeOfActions)))) ->
  forall m, OutOnly m ->
    (forall a, ActOut a ∈ m -> forall r, ~ lts (g N) (ActExt (ActIn a)) r) ->
    Settles (chans m) ((g M) ▷ m).
Proof.
  intros M N l HM HN HstN Hsem Hdrain m Hout Hnoc.
  destruct (outonly_bag m Hout) as (k & Hk). subst m.
  eapply surplus_settles_drain; eassumption.
Qed.

(** ** REGENERATION IS THE ONLY OBSTRUCTION

    [surplus_settles_drain]'s side condition — "the left's drain run is
    forced" — is not a black box.  [fw_conservation]'s balance equation,
    read along a trace of pure **outputs**, says

        bag l ⊎ bag (outs r)  =  y.2 ⊎ bag l ⊎ bag (ins r)

    where [r] is the *process*'s own trace; cancelling [bag l] leaves
    [bag (outs r) = y.2 ⊎ bag (ins r)].  So if the process emits nothing
    of its own along the drain, its residual buffer is empty **and** it
    consumed nothing — hence its trace is empty, and a τ-stable process
    that does nothing is where it started.

    Contrapositive, and this is the content: the *only* way the drain can
    leave the left somewhere other than [g M ▷ ∅] is for a continuation
    to **re-emit** a message the left has already given up — regeneration.
    A copycat does exactly that, which is why the condition is not
    vacuous, and why it is stated rather than assumed away. *)

Lemma wt_nil_stable_proc : forall (p q : proc),
  (forall z, ~ lts p τ z) -> p ⟹[[]] q -> q = p.
Proof.
  intros p q Hst Hw. remember (nil : trace (ExtAct TypeOfActions)) as s eqn:Es.
  revert Hst Es. induction Hw; intros Hst Es.
  - reflexivity.
  - exfalso. eapply Hst. eassumption.
  - discriminate Es.
Qed.

Lemma trace_nil_of_ins_outs : forall s, ins s = [] -> outs s = [] -> s = [].
Proof.
  intros s. destruct s as [|a s']; [ reflexivity | ].
  destruct a as [x|x]; simpl; intros H1 H2; discriminate.
Qed.

(** Stated at the **generic** multiset type on purpose: at [MO (ExtAct
    TypeOfActions)] the two elaborations of [⊎] that the development
    carries are convertible but not syntactically equal, so [rewrite]
    misfires; generically there is only one instance and the size
    lemmas apply directly.  [apply … in] then crosses back by
    conversion. *)

Lemma disj_union_cancel_empty : forall (A : Type) (EqA : EqDecision A) (CA : Countable A)
  (X Y Z : gmultiset A),
  X ⊎ ∅ ⊎ ∅ = Y ⊎ X ⊎ Z -> Y = ∅ /\ Z = ∅.
Proof.
  intros A EqA CA X Y Z H.
  assert (E1 : base.size (X ⊎ ∅ ⊎ ∅) = base.size (Y ⊎ X ⊎ Z)) by (rewrite H; reflexivity).
  rewrite !gmultiset_size_disj_union in E1. rewrite gmultiset_size_empty in E1.
  assert (HY : (base.size Y = 0)%nat) by lia.
  assert (HZ : (base.size Z = 0)%nat) by lia.
  split; [ apply gmultiset_size_empty_inv; exact HY
         | apply gmultiset_size_empty_inv; exact HZ ].
Qed.

Theorem drain_forced_of_no_output : forall (M : gproc) (l : list TypeOfActions) y,
  (forall z, ~ lts (g M) τ z) ->
  (forall r q, ((g M) : proc) ⟹[r] q -> outs r = []) ->
  ((g M) ▷ bag l) ⟹[map ActOut l] y ->
  y = ((g M) ▷ (∅ : MO (ExtAct TypeOfActions))).
Proof.
  intros M l y HstM Hno Hw.
  destruct (fw_conservation (map ActOut l) ((g M) ▷ bag l) y Hw) as (r & Hr & Heq).
  simpl in Hr, Heq.
  rewrite ins_map_out in Heq. rewrite outs_map_out in Heq.
  assert (Ho : outs r = []) by (eapply Hno; exact Hr).
  rewrite Ho in Heq. simpl in Heq.
  apply disj_union_cancel_empty in Heq as (Hy2 & Hir).
  apply bag_nil_inv in Hir.
  assert (Er : r = []) by (apply trace_nil_of_ins_outs; assumption).
  subst r.
  apply (wt_nil_stable_proc (g M) y.1 HstM) in Hr.
  destruct y as (y1, y2). simpl in Hr, Hy2. subst y1 y2. reflexivity.
Qed.

(** ** …and the condition weakens to exactly what the balance equation asks

    "[M] never emits" is far too strong — it already fails for
    [c ? (d ! v • 𝟘)], whose drain is nevertheless forced (the trace
    demands [c!u], and the only way to produce it is from the buffer;
    delivering into the guard yields a [d]-emitter, which realises a
    *different* trace).

    Reading the balance equation again shows what is really needed.  With
    [bag l] cancelled it says [bag (outs r) = y.2 ⊎ bag (ins r)], so the
    process **re-emitted at least everything it consumed** — that, and
    nothing more, is regeneration.  Hence the condition

        every run of [g M] that gives back all it took, took nothing

    and [gsum_run_no_input] then closes it: a τ-stable guarded sum that
    performs no input performs nothing at all, since it cannot emit
    either ([gsum_no_output]).

    A copycat violates it (consume [c!u], re-emit [c!u]); [c ? (d!v•𝟘)]
    does not ([{c} ⊄ {d}]). *)

Lemma disj_union_cancel_gen : forall (A : Type) (EqA : EqDecision A) (CA : Countable A)
  (X Y Z W : gmultiset A),
  X ⊎ ∅ ⊎ W = Y ⊎ X ⊎ Z -> W = Y ⊎ Z.
Proof.
  intros A EqA CA X Y Z W H.
  rewrite gmultiset_disj_union_right_id in H.
  assert (E : Y ⊎ X ⊎ Z = X ⊎ (Y ⊎ Z)).
  { rewrite (comm_L (@disj_union (gmultiset A) _) Y X).
    rewrite <- (assoc_L (@disj_union (gmultiset A) _)). reflexivity. }
  rewrite E in H. apply (gmultiset_disj_union_inj_1 X). exact H.
Qed.

Lemma gsum_run_no_input : forall (M : gproc) r q,
  (forall z, ~ lts (g M) τ z) -> ((g M) : proc) ⟹[r] q -> ins r = [] ->
  r = [] /\ q = ((g M) : proc).
Proof.
  intros M r q Hst Hw. remember ((g M) : proc) as p0 eqn:Ep.
  revert M Hst Ep. induction Hw; intros M Hst Ep Hins.
  - split; [ reflexivity | congruence ].
  - exfalso. subst. eapply Hst. eassumption.
  - exfalso. subst. destruct μ as [b|b].
    + simpl in Hins. discriminate Hins.
    + destruct b as (d,w). eapply gsum_no_output. exact l.
Qed.

Theorem drain_forced_no_regen : forall (M : gproc) (l : list TypeOfActions) y,
  (forall z, ~ lts (g M) τ z) ->
  (forall r q, ((g M) : proc) ⟹[r] q -> bag (ins r) ⊆ bag (outs r) -> ins r = []) ->
  ((g M) ▷ bag l) ⟹[map ActOut l] y ->
  y = ((g M) ▷ (∅ : MO (ExtAct TypeOfActions))).
Proof.
  intros M l y HstM Hno Hw.
  destruct (fw_conservation (map ActOut l) ((g M) ▷ bag l) y Hw) as (r & Hr & Heq).
  simpl in Hr, Heq.
  rewrite ins_map_out in Heq. rewrite outs_map_out in Heq. simpl in Heq.
  apply disj_union_cancel_gen in Heq.
  assert (Hsub : bag (ins r) ⊆ bag (outs r))
    by (rewrite Heq; apply gmultiset_disj_union_subseteq_r).
  pose proof (Hno r y.1 Hr Hsub) as Hins.
  destruct (gsum_run_no_input M r y.1 HstM Hr Hins) as (Er & Ey1).
  subst r. simpl in Heq.
  destruct y as (y1, y2). simpl in Ey1, Heq. subst y1.
  rewrite gmultiset_disj_union_right_id in Heq. subst y2. reflexivity.
Qed.

(** So for a τ-stable, non-regenerating left the certificate holds at
    **every** buffer — above or below the bag — from the configuration
    hypothesis alone. *)

Corollary certificate_no_regeneration : forall (M N : gproc) (l : list TypeOfActions),
  gStatic M -> gStatic N ->
  (forall p, ~ lts (g N) τ p) ->
  (forall z, ~ lts (g M) τ z) ->
  (forall r q, ((g M) : proc) ⟹[r] q -> bag (ins r) ⊆ bag (outs r) -> ins r = []) ->
  ((msgs l ‖ g M) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ g N)) ->
  forall m, OutOnly m ->
    (forall a, ActOut a ∈ m -> forall r, ~ lts (g N) (ActExt (ActIn a)) r) ->
    Settles (chans m) ((g M) ▷ m).
Proof.
  intros M N l HM HN HstN HstM Hno Hsem m Hout Hnoc.
  eapply certificate_drain; try eassumption.
  intros y Hy. eapply drain_forced_no_regen; eassumption.
Qed.

(** ** CANCELLATION, FOR A STABLE CONFIGURATION

    A common message bag can be *cancelled* on both sides — provided the
    left configuration is stable, i.e. [M] refuses everything the bag
    holds.

    There is no cancellation in general ([VACCS_DropProbes.nil_not_below_msg]
    is the obstruction: a pending message is observable, so adding one to
    both sides is not a conservative move).  What rescues the stable case
    is that the client can **drain the bag first**: read the acceptance
    condition at a trace of the form [map ActOut l ++ s].  The right can
    always empty its buffer along that prefix ([bag_wt_drain]); the left
    must match it, and [fw_out_run_drain] says a stable configuration
    with a mute process has *only* the draining run — so after the prefix
    the left is at exactly [g M ▷ ∅], and the rest of the trace reads off
    the bare acceptance condition.

    This is what makes Phase A lift to a configuration: with the bag
    cancelled, the whole mirror/restrict/match chain applies to [g M] and
    [g N] and is carried back under [msgs l ‖ ·] by [ax_par]. *)

Theorem msgs_cancel : forall (l : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N ->
  (forall z, ~ ((g M ▷ bag l) ⟶ z)) ->
  ((msgs l ‖ g M) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ g N)) ->
  (g M) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (g N).
Proof.
  intros l M N HM HN HstM Hpre.
  destruct (msgs_accept l l (g M) (g N) Hpre) as (Hc1 & Hc2).
  apply must_iff_acceptance_set_VACCS. split.
  - intros s _. apply fw_converge_static. apply static_g. exact HN.
  - intros s y _ Hwy Hsty.
    assert (Hdrain : ((g N) ▷ bag l) ⟹[map ActOut l] ((g N) ▷ (∅ : MO (ExtAct TypeOfActions)))).
    { replace (bag l) with (bag l ⊎ (∅ : MO (ExtAct TypeOfActions))) at 1
        by (apply gmultiset.gmultiset_disj_union_right_id).
      apply bag_wt_drain. }
    assert (Hbig : ((g N) ▷ bag l) ⟹[map ActOut l ++ s] y)
      by (eapply wt_concat; [ exact Hdrain | exact Hwy ]).
    destruct (Hc2 (map ActOut l ++ s) y
                (fw_converge_static (map ActOut l ++ s) (g M) (bag l) (static_g M HM))
                Hbig Hsty)
      as (x & Hwx & Hstx & Hincl).
    destruct (wt_split _ _ _ _ Hwx) as (z & Hz1 & Hz2).
    destruct (fw_out_run_drain (map ActOut l) ((g M) ▷ bag l) z Hz1 (ins_map_out l))
      as (Hz11 & Hz12).
    + intros a p' Hp'. simpl in Hp'. destruct a as (d,w). eapply gsum_no_output. exact Hp'.
    + exact HstM.
    + rewrite outs_map_out in Hz12. simpl in Hz12, Hz11.
      assert (Hz2e : z.2 = ∅).
      { apply (gmultiset.gmultiset_disj_union_inj_1 (bag l)).
        etransitivity; [ exact Hz12 | ].
        symmetry. apply gmultiset.gmultiset_disj_union_right_id. }
      exists x. split; [ | split; [ exact Hstx | exact Hincl ] ].
      destruct z as (z1,z2). simpl in *. subst z1. subst z2. exact Hz2.
Qed.

(** ** …AND WITHOUT STABILITY, IF THE SUM DOES NOT REGENERATE

    [msgs_cancel] uses its stability hypothesis in **one** place: to know
    that the left's run over [map ActOut l] is the pure drain, so that it
    ends at [(g M ▷ ∅)].  [drain_forced_no_regen] gives the same
    conclusion from a different premise — that no run of [g M] returns
    everything it consumed without having consumed nothing — and that
    premise does **not** require the configuration to be stable.

    So the bag can be cancelled for an **unstable** configuration too,
    provided [M] does not regenerate.  Note the [τ]-stability asked here
    is that of the bare sum [g M] (free for a [gStable] sum), not of the
    configuration [(g M ▷ bag l)] — which is exactly the difference, and
    exactly the case [msgs_cancel] cannot reach.

    The balance equation of [fw_conservation] is what makes the premise
    the right one: along a trace that emits the whole bag, the process
    must have emitted at least what it took, so "took something and gave
    it all back" is precisely what has to be excluded. *)

Theorem msgs_cancel_no_regen : forall (l : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N ->
  (forall z, ~ lts ((g M) : proc) τ z) ->
  (forall r q, ((g M) : proc) ⟹[r] q -> bag (ins r) ⊆ bag (outs r) -> ins r = []) ->
  ((msgs l ‖ g M) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ g N)) ->
  (g M) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (g N).
Proof.
  intros l M N HM HN HstM Hno Hpre.
  destruct (msgs_accept l l (g M) (g N) Hpre) as (Hc1 & Hc2).
  apply must_iff_acceptance_set_VACCS. split.
  - intros s _. apply fw_converge_static. apply static_g. exact HN.
  - intros s y _ Hwy Hsty.
    assert (Hdrain : ((g N) ▷ bag l) ⟹[map ActOut l] ((g N) ▷ (∅ : MO (ExtAct TypeOfActions)))).
    { replace (bag l) with (bag l ⊎ (∅ : MO (ExtAct TypeOfActions))) at 1
        by (apply gmultiset.gmultiset_disj_union_right_id).
      apply bag_wt_drain. }
    assert (Hbig : ((g N) ▷ bag l) ⟹[map ActOut l ++ s] y)
      by (eapply wt_concat; [ exact Hdrain | exact Hwy ]).
    destruct (Hc2 (map ActOut l ++ s) y
                (fw_converge_static (map ActOut l ++ s) (g M) (bag l) (static_g M HM))
                Hbig Hsty)
      as (x & Hwx & Hstx & Hincl).
    destruct (wt_split _ _ _ _ Hwx) as (z & Hz1 & Hz2).
    assert (Hz : z = ((g M) ▷ (∅ : MO (ExtAct TypeOfActions))))
      by (eapply drain_forced_no_regen; eassumption).
    exists x. split; [ | split; [ exact Hstx | exact Hincl ] ].
    rewrite <- Hz. exact Hz2.
Qed.

(** ** Lifting a run into a larger guarded sum

    A run of `(g M ▷ m₀)` is also a run of `(g K ▷ m₀)` whenever `K`'s
    transitions include `M`'s — **once the process has moved**, because a
    guarded choice commits and the two then sit at the *same* state.
    Until then the run is pure buffer traffic and the process component
    still differs; that is the second disjunct.

    This is the transport the union route needs in both directions
    (`lts_choiceR` for `M` inside `N + M`, `lts_choiceL` for `N`). *)

Lemma fw_sub_lift : forall (M K : gproc),
  (forall al z, lts (g M) al z -> lts (g K) al z) ->
  forall s (x0 x : proc * MO (ExtAct TypeOfActions)),
  x0 ⟹[s] x -> x0.1 = g M ->
  (((g K) ▷ x0.2) ⟹[s] x)
  \/ (exists m, x = ((g M) ▷ m) /\ ((g K) ▷ x0.2) ⟹[s] ((g K) ▷ m)).
Proof.
  intros M K Hsub s x0 x Hw.
  induction Hw as [z|s0 z q y Hl Hwt IH|mu s0 z q y Hl Hwt IH]; intros Heq.
  - right. destruct z as (p,m). simpl in *. subst p.
    exists m. split; [ reflexivity | apply wt_nil ].
  - left. destruct z as (p,m). destruct q as (p1,m1). simpl in *. subst p.
    destruct (fw_tau_shape (g M) m (p1,m1) Hl) as [HA|HB].
    + destruct HA as (p' & Hp' & E). inversion E; subst.
      eapply wt_tau; [ | exact Hwt ]. apply fw_tau_left. apply Hsub. exact Hp'.
    + destruct HB as (a & p' & m' & Hm & Hp' & E). inversion E; subst.
      eapply wt_tau; [ | exact Hwt ]. apply fw_tau_deliver. apply Hsub. exact Hp'.
  - destruct z as (p,m). destruct q as (p1,m1). simpl in *. subst p.
    destruct (fw_ext_shape (g M) m mu (p1,m1) Hl) as [HA|[HB|HC]].
    + left. destruct HA as (p' & Hp' & E). inversion E; subst.
      eapply wt_act; [ | exact Hwt ]. apply ParLeft. apply Hsub. exact Hp'.
    + destruct HB as (a & Hmu & E). inversion E; subst.
      destruct (IH eq_refl) as [Hleft | (m2 & Ey & Hright)].
      * left. simpl in Hleft. eapply wt_act; [ | exact Hleft ]. apply fw_input_always.
      * right. exists m2. split; [ exact Ey | ].
        simpl in Hright. eapply wt_act; [ | exact Hright ]. apply fw_input_always.
    + destruct HC as (a & m' & Hmu & Hm & E). inversion E; subst.
      destruct (IH eq_refl) as [Hleft | (m2 & Ey & Hright)].
      * left. simpl in Hleft. eapply wt_act; [ | exact Hleft ]. apply fw_emit.
      * right. exists m2. split; [ exact Ey | ].
        simpl in Hright. eapply wt_act; [ | exact Hright ]. apply fw_emit.
Qed.

(** The same, strengthened: in the second disjunct the run used **no
    process step at all**, so it is a run over *any* process. *)

Lemma fw_sub_lift_gen : forall (M K : gproc),
  (forall al z, lts (g M) al z -> lts (g K) al z) ->
  forall s (x0 x : proc * MO (ExtAct TypeOfActions)),
  x0 ⟹[s] x -> x0.1 = g M ->
  (((g K) ▷ x0.2) ⟹[s] x)
  \/ (exists m, x = ((g M) ▷ m) /\ forall X : proc, (X ▷ x0.2) ⟹[s] (X ▷ m)).
Proof.
  intros M K Hsub s x0 x Hw.
  induction Hw as [z|s0 z q y Hl Hwt IH|mu s0 z q y Hl Hwt IH]; intros Heq.
  - right. destruct z as (p,m). simpl in *. subst p.
    exists m. split; [ reflexivity | intro X; apply wt_nil ].
  - left. destruct z as (p,m). destruct q as (p1,m1). simpl in *. subst p.
    destruct (fw_tau_shape (g M) m (p1,m1) Hl) as [HA|HB].
    + destruct HA as (p' & Hp' & E). inversion E; subst.
      eapply wt_tau; [ | exact Hwt ]. apply fw_tau_left. apply Hsub. exact Hp'.
    + destruct HB as (a & p' & m' & Hm & Hp' & E). inversion E; subst.
      eapply wt_tau; [ | exact Hwt ]. apply fw_tau_deliver. apply Hsub. exact Hp'.
  - destruct z as (p,m). destruct q as (p1,m1). simpl in *. subst p.
    destruct (fw_ext_shape (g M) m mu (p1,m1) Hl) as [HA|[HB|HC]].
    + left. destruct HA as (p' & Hp' & E). inversion E; subst.
      eapply wt_act; [ | exact Hwt ]. apply ParLeft. apply Hsub. exact Hp'.
    + destruct HB as (a & Hmu & E). inversion E; subst.
      destruct (IH eq_refl) as [Hleft | (m2 & Ey & Hright)].
      * left. simpl in Hleft. eapply wt_act; [ | exact Hleft ]. apply fw_input_always.
      * right. exists m2. split; [ exact Ey | ].
        intro X. eapply wt_act; [ apply fw_input_always | apply Hright ].
    + destruct HC as (a & m' & Hmu & Hm & E). inversion E; subst.
      destruct (IH eq_refl) as [Hleft | (m2 & Ey & Hright)].
      * left. simpl in Hleft. eapply wt_act; [ | exact Hleft ]. apply fw_emit.
      * right. exists m2. split; [ exact Ey | ].
        intro X. eapply wt_act; [ apply fw_emit | apply Hright ].
Qed.

(** A buffer-only run's final buffer is a *function* of the trace — read
    off at the process `𝟘`, which has no transitions at all, so its
    forwarder is a pure buffer. *)

Lemma bag_sub_add : forall (a : ExtAct TypeOfActions) (m : MO (ExtAct TypeOfActions)),
  ({[+ a +]} ⊎ m) ∖ {[+ a +]} = m.
Proof.
  intros a m. symmetry.
  apply (gmultiset.gmultiset_disj_union_inj_1 {[+ a +]}).
  apply gmultiset.gmultiset_disj_union_difference'.
  apply gmultiset.gmultiset_elem_of_disj_union. left.
  apply gmultiset.gmultiset_elem_of_singleton. reflexivity.
Qed.

Fixpoint bufafter (s : trace (ExtAct TypeOfActions)) (m : MO (ExtAct TypeOfActions))
  : MO (ExtAct TypeOfActions) :=
match s with
| nil => m
| ActIn a :: s' => bufafter s' ({[+ ActOut a +]} ⊎ m)
| ActOut a :: s' => bufafter s' (m ∖ {[+ ActOut a +]})
end.

Lemma nil_no_lts : forall al q, ~ lts ((g 𝟘) : proc) al q.
Proof. intros al q H. inversion H. Qed.

Lemma nil_buf_run : forall s (x0 y : proc * MO (ExtAct TypeOfActions)),
  x0 ⟹[s] y -> x0.1 = ((g 𝟘) : proc) ->
  y = (((g 𝟘) : proc) ▷ bufafter s x0.2).
Proof.
  intros s x0 y Hw.
  induction Hw as [z|s0 z q y Hl Hwt IH|mu s0 z q y Hl Hwt IH]; intros Heq.
  - destruct z as (p,m). simpl in *. subst p. reflexivity.
  - exfalso. destruct z as (p,m). destruct q as (p1,m1). simpl in *. subst p.
    destruct (fw_tau_shape ((g 𝟘) : proc) m (p1,m1) Hl) as [HA|HB].
    + destruct HA as (p' & Hp' & _). eapply nil_no_lts. exact Hp'.
    + destruct HB as (a & p' & m' & _ & Hp' & _). eapply nil_no_lts. exact Hp'.
  - destruct z as (p,m). destruct q as (p1,m1). simpl in *. subst p.
    destruct (fw_ext_shape ((g 𝟘) : proc) m mu (p1,m1) Hl) as [HA|[HB|HC]].
    + exfalso. destruct HA as (p' & Hp' & _). eapply nil_no_lts. exact Hp'.
    + destruct HB as (a & Hmu & E). inversion E; subst.
      specialize (IH eq_refl). simpl in IH. exact IH.
    + destruct HC as (a & m' & Hmu & Hm & E). inversion E; subst.
      specialize (IH eq_refl). simpl in IH. rewrite bag_sub_add. exact IH.
Qed.

(** ** THE UNION SUM IS BELOW — the last step of the union route, semantically

    Adding the *left*-hand sum's guards to the right-hand one preserves
    the comparison.  This is the inequation the union route needs to
    finish, and it holds:

        msgs l ‖ g M ⊑ₘᵤₛₜᵢ msgs l ‖ g N
     ⟹ msgs l ‖ g (N + M) ⊑ₘᵤₛₜᵢ msgs l ‖ g N

    Read `cond2` at a trace `s` with a stable `y` reached from
    `(g N ▷ bag l)`, and split on whether each run moves its *process*:

    - the hypothesis's witness moved — `fw_sub_lift_gen`'s first disjunct
      lands on it exactly, because a guarded choice **commits** and the
      two sums are the same continuation afterwards;
    - it did not, but the right's run moved — lift the right instead and
      land on `y` itself;
    - neither moved — then both runs are pure buffer traffic over the same
      trace, so `nil_buf_run` makes the two final buffers equal, and both
      `M` and `N` refuse that buffer's channels, so `g (N + M)` sits
      stable there emitting exactly what `y` does.

    **Note what this does *not* give**: a derivation.  The bare
    `g (N + M) ⊑ₘᵤₛₜᵢ g N` is false in general
    ([VACCS_DropProbes]'s copycat example), so `ax_par` cannot take this
    step, and no rule of the system currently can.  What the theorem does
    is confirm the route is semantically correct end to end, and fix the
    soundness statement any new primitive would have to meet. *)

Theorem union_below : forall (l : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N ->
  ((msgs l ‖ g M) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ g N)) ->
  ((msgs l ‖ g (N + M)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ g N)).
Proof.
  intros l M N HM HN Hpre.
  assert (HsubM : forall al z, lts (g M) al z -> lts (g (N + M)) al z)
    by (intros al z H; apply lts_choiceR; exact H).
  assert (HsubN : forall al z, lts (g N) al z -> lts (g (N + M)) al z)
    by (intros al z H; apply lts_choiceL; exact H).
  destruct (msgs_accept l l (g M) (g N) Hpre) as (Hc1 & Hc2).
  apply msgs_sound. split.
  - intros s _. apply fw_converge_static. apply static_g. exact HN.
  - intros s y Hcnv Hwy Hsty.
    destruct (Hc2 s y (fw_converge_static s (g M) (bag l) (static_g M HM)) Hwy Hsty)
      as (x & Hwx & Hstx & Hincl).
    destruct (fw_sub_lift_gen M (N + M) HsubM s ((g M) ▷ bag l) x Hwx eq_refl)
      as [HL | (m & Ex & HL)].
    + exists x. split; [ exact HL | split; [ exact Hstx | exact Hincl ] ].
    + destruct (fw_sub_lift_gen N (N + M) HsubN s ((g N) ▷ bag l) y Hwy eq_refl)
        as [HR | (m2 & Ey & HR)].
      * exists y. split; [ exact HR | split; [ exact Hsty | intros a Ha; exact Ha ] ].
      * assert (Em : m = m2).
        { pose proof (nil_buf_run s (((g 𝟘) : proc) ▷ bag l) (((g 𝟘) : proc) ▷ m)
                        (HL ((g 𝟘) : proc)) eq_refl) as E1.
          pose proof (nil_buf_run s (((g 𝟘) : proc) ▷ bag l) (((g 𝟘) : proc) ▷ m2)
                        (HR ((g 𝟘) : proc)) eq_refl) as E2.
          simpl in E1, E2. inversion E1. inversion E2. congruence. }
        subst m2. subst x y.
        exists ((g (N + M)) ▷ m). split; [ exact (HL _) | ].
        assert (HsX : forall z, ~ (((g M) ▷ m) ⟶ z)) by (apply no_step_of_stable; exact Hstx).
        assert (HsY : forall z, ~ (((g N) ▷ m) ⟶ z)) by (apply no_step_of_stable; exact Hsty).
        apply fw_stable_iff in HsX as (HX1 & HX2).
        apply fw_stable_iff in HsY as (HY1 & HY2).
        split.
        -- apply stable_of_no_step. apply fw_stable_iff. split.
           ++ intros q Hq. inversion Hq; subst; [ eapply HY1 | eapply HX1 ]; eassumption.
           ++ intros a Ha q Hq. inversion Hq; subst;
                [ eapply HY2 | eapply HX2 ]; eassumption.
        -- intros a Ha. destruct a as [d].
           apply coR_abs_pair_iff. apply coR_abs_pair_iff in Ha as (w & r & Hr).
           assert (Hex : exists y0, ((g (N + M)) ▷ m) ⟶[ActOut (d,w)] y0)
             by (exists r; exact Hr).
           apply fw_emits_iff in Hex as [ (p' & Hp') | Hmem ].
           ++ exfalso. eapply gsum_no_output. exact Hp'.
           ++ assert (Hm : m = {[+ ActOut (d,w) +]} ⊎ (m ∖ {[+ ActOut (d,w) +]}))
                by (apply gmultiset.gmultiset_disj_union_difference'; exact Hmem).
              exists w, (((g N) : proc) ▷ (m ∖ {[+ ActOut (d,w) +]})).
              rewrite Hm at 1. apply fw_emit.
Qed.

(** The settling certificate transfers from `g M` to the union sum.

    Note where the argument turns: `Settles` uses the **empty** trace, so
    `fw_sub_lift_gen`'s second disjunct — the run took no process step —
    forces the run to be *nil* (`nil_buf_run` at the empty trace), hence
    the reached state is `(g M ▷ K)` itself, stable, so `M` refuses `K`'s
    channels and the union sum is stable there too.  With a non-empty
    trace that collapse is unavailable, which is exactly why the *general*
    restriction certificate is out of reach. *)

Lemma settles_union : forall (M N : gproc) (K : MO (ExtAct TypeOfActions)),
  Settles (chans K) ((g M) ▷ K) ->
  (forall z, ~ (((g N) ▷ K) ⟶ z)) ->
  Settles (chans K) ((g (N + M)) ▷ K).
Proof.
  intros M N K (z & Hwz & Hstz & Hez) HstN.
  assert (HsubM : forall al w, lts (g M) al w -> lts (g (N + M)) al w)
    by (intros al w H; apply lts_choiceR; exact H).
  destruct (fw_sub_lift_gen M (N + M) HsubM nil ((g M) ▷ K) z Hwz eq_refl)
    as [HLift | (m & Ez & HLift)].
  - exists z. split; [ exact HLift | split; [ exact Hstz | exact Hez ] ].
  - assert (Em : m = K).
    { pose proof (nil_buf_run nil (((g 𝟘) : proc) ▷ K) (((g 𝟘) : proc) ▷ m)
                    (HLift ((g 𝟘) : proc)) eq_refl) as E1.
      simpl in E1. inversion E1. reflexivity. }
    subst m. subst z.
    apply fw_stable_iff in HstN as (HN1 & HN2).
    assert (HsX : forall w, ~ (((g M) ▷ K) ⟶ w)) by (apply no_step_of_stable; exact Hstz).
    apply fw_stable_iff in HsX as (HM1 & HM2).
    exists ((g (N + M)) ▷ K). split; [ apply wt_nil | ]. split.
    + apply stable_of_no_step. apply fw_stable_iff. split.
      * intros q Hq. inversion Hq; subst; [ eapply HN1 | eapply HM1 ]; eassumption.
      * intros a Ha q Hq. inversion Hq; subst; [ eapply HN2 | eapply HM2 ]; eassumption.
    + intros d w r Hr.
      assert (Hex : exists y0, ((g (N + M)) ▷ K) ⟶[ActOut (d,w)] y0)
        by (exists r; exact Hr).
      apply fw_emits_iff in Hex as [ (p' & Hp') | Hmem ].
      * exfalso. eapply gsum_no_output. exact Hp'.
      * exists w. exact Hmem.
Qed.

(** ** How the channel shift distributes *)

Lemma NewVarCn_par : forall k n P Q, NewVarCn k n (P ‖ Q) = NewVarCn k n P ‖ NewVarCn k n Q.
Proof. intros k n. induction n; intros P Q; simpl; [ reflexivity | rewrite IHn; reflexivity ]. Qed.

Lemma NewVarCn_g : forall k n M, NewVarCn k n (g M) = g (gNewVarCn k n M).
Proof. intros k n. induction n; intro M; simpl; [ reflexivity | rewrite IHn; reflexivity ]. Qed.

Lemma NewVarCn_nil : forall k n, NewVarCn k n (g 𝟘) = g 𝟘.
Proof. intros k n. induction n; simpl; [ reflexivity | rewrite IHn; reflexivity ]. Qed.

Lemma NewVarCn_msg : forall k n c v,
  NewVarCn k n (c ! v • 𝟘) = (Nat.iter n (NewVar_in_ChannelData k) c) ! v • 𝟘.
Proof. intros k n c v. induction n; simpl; [ reflexivity | rewrite IHn; reflexivity ]. Qed.

Lemma NewVarCn_msgs : forall k n l, NewVarCn k n (msgs l) = msgs (map (shiftCn k n) l).
Proof.
  intros k n. induction l as [|cv l IH]; simpl.
  - apply NewVarCn_nil.
  - rewrite NewVarCn_par. rewrite IH. f_equal.
    unfold shiftCn. destruct cv as (c,v). simpl. apply NewVarCn_msg.
Qed.

Lemma gStatic_gNewVarCn : forall k n M, gStatic M -> gStatic (gNewVarCn k n M).
Proof.
  intros k n. induction n; intros M H; simpl; [ exact H | ].
  assert (Static (g (gNewVarCn k n M))) as HS by (constructor; apply IHn; exact H).
  pose proof (Static_NewVarC _ HS k) as HS2. simpl in HS2. inversion HS2; subst. assumption.
Qed.

Lemma BigNew_add : forall n m p, Ѵ (n + m) p = Ѵ n (Ѵ m p).
Proof. induction n; intros m p; simpl; [ reflexivity | rewrite IHn; reflexivity ]. Qed.

Lemma ax_res_n : forall n p q, ax_pre p q -> ax_pre (Ѵ n p) (Ѵ n q).
Proof. induction n; intros p q H; simpl; [ exact H | apply ax_res; apply IHn; exact H ]. Qed.

(** ** Merging two normal forms

    Scope extrusion pulls both restriction blocks to the top — each
    shifting the other operand's channels — then the four components are
    reassociated into "all the messages" beside "the two sums". *)

Lemma NF_par_step : forall n1 l1 M1 n2 l2 M2,
  (NF n1 l1 M1 ‖ NF n2 l2 M2)
  ≡* Ѵ (n1 + n2) ((msgs (map (shiftCn n2 n1) l2) ‖ msgs (map (shiftCn 0 n2) l1))
                  ‖ (g (gNewVarCn n2 n1 M2) ‖ g (gNewVarCn 0 n2 M1))).
Proof.
  intros n1 l1 M1 n2 l2 M2. unfold NF.
  etransitivity; [ apply cgr_res_scope_n | ].
  rewrite BigNew_add. apply cgr_res_n.
  rewrite (NewVarCn_res 0 n1 n2). simpl.
  etransitivity; [ apply cgr_par_com | ].
  etransitivity; [ apply cgr_res_scope_n | ].
  apply cgr_res_n.
  rewrite !NewVarCn_par, !NewVarCn_msgs, !NewVarCn_g.
  etransitivity; [ apply cgr_par_assoc | ].
  etransitivity; [ | apply cgr_par_assoc_rev ].
  apply cgr_fullpar; [ reflexivity | ].
  etransitivity; [ apply cgr_par_assoc_rev | ].
  etransitivity; [ | apply cgr_par_assoc ].
  apply cgr_fullpar; [ | reflexivity ].
  apply cgr_par_com.
Qed.

(** ** The normal form *)

Theorem normal_form : forall p, Static p ->
  exists n l M, gStatic M /\ ax_pre p (NF n l M) /\ ax_pre (NF n l M) p.
Proof.
  intro p. induction p as [p IHp] using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intro Hs. destruct p as [p1 p2|x|x p0|E p1 p2|c v|p0|M].
  - (* parallel: normalise both, extrude, then one expansion step *)
    inversion Hs; subst.
    destruct (IHp p1 ltac:(simpl; lia) H1) as (n1 & l1 & M1 & HM1 & Ha1 & Hb1).
    destruct (IHp p2 ltac:(simpl; lia) H2) as (n2 & l2 & M2 & HM2 & Ha2 & Hb2).
    set (N1 := gNewVarCn 0 n2 M1). set (N2 := gNewVarCn n2 n1 M2).
    set (L1 := map (shiftCn 0 n2) l1). set (L2 := map (shiftCn n2 n1) l2).
    exists ((n1 + n2)%nat), (L2 ++ L1), (ext N2 N1 + ext_r N1 N2).
    split.
    { subst N1 N2. constructor.
      - apply ext_gStatic; apply gStatic_gNewVarCn; assumption.
      - apply ext_r_gStatic; apply gStatic_gNewVarCn; assumption. }
    assert (Hmid : ax_pre (NF n1 l1 M1 ‖ NF n2 l2 M2)
                          (NF ((n1 + n2)%nat) (L2 ++ L1) (ext N2 N1 + ext_r N1 N2))
                   /\ ax_pre (NF ((n1 + n2)%nat) (L2 ++ L1) (ext N2 N1 + ext_r N1 N2))
                             (NF n1 l1 M1 ‖ NF n2 l2 M2)).
    { unfold NF at 3 4. split.
      - eapply ax_trans; [ apply ax_cgr; apply NF_par_step | ].
        apply ax_res_n.
        eapply ax_trans;
          [ apply ax_cgr; apply cgr_fullpar; [ symmetry; apply msgs_app | reflexivity ] | ].
        apply ax_par; [ apply ax_refl | apply ax_expansion_l ].
      - eapply ax_trans; [ | apply ax_cgr_sym; apply NF_par_step ].
        apply ax_res_n.
        eapply ax_trans; [ apply ax_par; [ apply ax_refl | apply ax_expansion_r ] | ].
        apply ax_cgr. apply cgr_fullpar; [ apply msgs_app | reflexivity ]. }
    destruct Hmid as (Hm1 & Hm2). split.
    + eapply ax_trans; [ apply ax_par; [ exact Ha1 | exact Ha2 ] | exact Hm1 ].
    + eapply ax_trans; [ exact Hm2 | apply ax_par; [ exact Hb1 | exact Hb2 ] ].
  - inversion Hs.
  - inversion Hs.
  - (* conditional: [Eval_Eq 0] never fails, so it is [≡*] one branch *)
    destruct (Eval_Eq 0 E) as [[|]|] eqn:HE;
      [ | | exfalso; eapply Eval_Eq_0_not_none; exact HE ].
    + inversion Hs; subst.
      destruct (IHp p1 ltac:(simpl; lia) H1) as (n & l & M & HM & Ha & Hb).
      exists n, l, M. split; [ exact HM | ]. split.
      * eapply ax_trans; [ apply ax_cgr; apply cgr_if_true; exact HE | exact Ha ].
      * eapply ax_trans; [ exact Hb | apply ax_cgr_sym; apply cgr_if_true; exact HE ].
    + inversion Hs; subst.
      destruct (IHp p2 ltac:(simpl; lia) H3) as (n & l & M & HM & Ha & Hb).
      exists n, l, M. split; [ exact HM | ]. split.
      * eapply ax_trans; [ apply ax_cgr; apply cgr_if_false; exact HE | exact Ha ].
      * eapply ax_trans; [ exact Hb | apply ax_cgr_sym; apply cgr_if_false; exact HE ].
  - (* a message is already a one-element bag *)
    exists 0, [(c,v)], 𝟘. split; [ constructor | ]. simpl. split.
    + apply ax_cgr. etransitivity; [ apply cgr_par_nil_rev | ].
      apply cgr_fullpar; [ apply cgr_par_nil_rev | reflexivity ].
    + apply ax_cgr_sym. etransitivity; [ apply cgr_par_nil_rev | ].
      apply cgr_fullpar; [ apply cgr_par_nil_rev | reflexivity ].
  - (* restriction: just one more [ν] on the block *)
    inversion Hs; subst.
    destruct (IHp p0 ltac:(simpl; lia) H0) as (n & l & M & HM & Ha & Hb).
    exists (S n), l, M. split; [ exact HM | ]. split; apply ax_res; assumption.
  - (* a guarded sum is already one, with an empty bag *)
    inversion Hs; subst.
    exists 0, [], M. split; [ assumption | ]. simpl. split.
    + apply ax_cgr. etransitivity; [ apply cgr_par_nil_rev | apply cgr_par_com ].
    + apply ax_cgr_sym. etransitivity; [ apply cgr_par_nil_rev | apply cgr_par_com ].
Qed.

(** * LE FRAGMENT SANS [ν] : la forme normale est une CONFIGURATION NUE

    Le seul cas de [normal_form] qui produise un bloc de restriction est
    celui de [ν] ; tous les autres rendent [n = 0] ou l'additionnent.
    Interdire [ν] **sur l'épine** — pas à l'intérieur des gardes, où il ne
    change pas la forme du terme — donne donc une forme normale
    [msgs l ‖ g M], sans bloc.

    L'enjeu n'est pas cosmétique.  [completeness_from_NF] livre son
    hypothèse sémantique **sous** le bloc, alors que tous les
    [VACCS_Matching.ax_below_NF_*] la réclament au niveau de la
    configuration ; et l'on ne peut pas la faire sortir, [ν] cachant
    ([ν p ⊑ₘᵤₛₜᵢ ν q] n'entraîne pas [p ⊑ₘᵤₛₜᵢ q]).  Sur le fragment sans
    [ν] cet obstacle **disparaît** : [completeness_nores_from_cfg] rend
    l'hypothèse exactement là où la machinerie de configuration
    l'attend.

    La preuve est aussi nettement plus courte que celle de [normal_form] :
    plus d'extrusion de portée, plus de [NewVarCn] — le cas [‖] est un
    simple réarrangement ([cgr_par_exchange]) suivi d'une application de
    la loi d'expansion. *)

Fixpoint NoRes (p : proc) : Prop :=
match p with
| P ‖ Q => NoRes P /\ NoRes Q
| pr_var _ => True
| rec _ • P => NoRes P
| If _ Then P Else Q => NoRes P /\ NoRes Q
| _ ! _ • 𝟘 => True
| ν _ => False
| g _ => True
end.

Lemma cgr_par_exchange : forall (A B C D : proc),
  ((A ‖ B) ‖ (C ‖ D)) ≡* ((A ‖ C) ‖ (B ‖ D)).
Proof.
  intros A B C D.
  etransitivity; [ apply cgr_par_assoc | ].
  etransitivity; [ | symmetry; apply cgr_par_assoc ].
  apply cgr_fullpar; [ reflexivity | ].
  etransitivity; [ apply cgr_par_assoc_rev | ].
  etransitivity; [ apply cgr_fullpar; [ apply cgr_par_com | reflexivity ] | ].
  apply cgr_par_assoc.
Qed.

Theorem normal_form_nores : forall p, Static p -> NoRes p ->
  exists l M, gStatic M /\ ax_pre p (msgs l ‖ ((g M) : proc))
                        /\ ax_pre (msgs l ‖ ((g M) : proc)) p.
Proof.
  intro p. induction p as [p IHp] using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros Hs Hnr. destruct p as [p1 p2|x|x p0|E p1 p2|c v|p0|M].
  - inversion Hs; subst. destruct Hnr as (Hn1 & Hn2).
    destruct (IHp p1 ltac:(simpl; lia) H1 Hn1) as (l1 & M1 & HM1 & Ha1 & Hb1).
    destruct (IHp p2 ltac:(simpl; lia) H2 Hn2) as (l2 & M2 & HM2 & Ha2 & Hb2).
    exists (l1 ++ l2), (ext M1 M2 + ext_r M2 M1).
    split; [ constructor; [ apply ext_gStatic | apply ext_r_gStatic ]; assumption | ].
    assert (Hc : ((msgs l1 ‖ ((g M1) : proc)) ‖ (msgs l2 ‖ ((g M2) : proc)))
                 ≡* (msgs (l1 ++ l2) ‖ (((g M1) : proc) ‖ ((g M2) : proc)))).
    { etransitivity; [ apply cgr_par_exchange | ].
      apply cgr_fullpar; [ symmetry; apply msgs_app | reflexivity ]. }
    split.
    + eapply ax_trans; [ apply ax_par; [ exact Ha1 | exact Ha2 ] | ].
      eapply ax_trans; [ apply ax_cgr; exact Hc | ].
      apply ax_par; [ apply ax_refl | apply ax_expansion_l ].
    + eapply ax_trans; [ apply ax_par; [ apply ax_refl | apply ax_expansion_r ] | ].
      eapply ax_trans; [ apply ax_cgr_sym; exact Hc | ].
      apply ax_par; [ exact Hb1 | exact Hb2 ].
  - inversion Hs.
  - inversion Hs.
  - destruct (Eval_Eq 0 E) as [[|]|] eqn:HE;
      [ | | exfalso; eapply Eval_Eq_0_not_none; exact HE ].
    + inversion Hs; subst. destruct Hnr as (Hn1 & Hn2).
      destruct (IHp p1 ltac:(simpl; lia) H1 Hn1) as (l & M & HM & Ha & Hb).
      exists l, M. split; [ exact HM | ]. split.
      * eapply ax_trans; [ apply ax_cgr; apply cgr_if_true; exact HE | exact Ha ].
      * eapply ax_trans; [ exact Hb | apply ax_cgr_sym; apply cgr_if_true; exact HE ].
    + inversion Hs; subst. destruct Hnr as (Hn1 & Hn2).
      destruct (IHp p2 ltac:(simpl; lia) H3 Hn2) as (l & M & HM & Ha & Hb).
      exists l, M. split; [ exact HM | ]. split.
      * eapply ax_trans; [ apply ax_cgr; apply cgr_if_false; exact HE | exact Ha ].
      * eapply ax_trans; [ exact Hb | apply ax_cgr_sym; apply cgr_if_false; exact HE ].
  - exists [(c,v)], 𝟘. split; [ constructor | ]. simpl. split.
    + apply ax_cgr. etransitivity; [ apply cgr_par_nil_rev | ].
      apply cgr_fullpar; [ apply cgr_par_nil_rev | reflexivity ].
    + apply ax_cgr_sym. etransitivity; [ apply cgr_par_nil_rev | ].
      apply cgr_fullpar; [ apply cgr_par_nil_rev | reflexivity ].
  - simpl in Hnr. contradiction.
  - inversion Hs; subst. exists [], M. split; [ assumption | ]. simpl. split.
    + apply ax_cgr. etransitivity; [ apply cgr_par_nil_rev | apply cgr_par_com ].
    + apply ax_cgr_sym. etransitivity; [ apply cgr_par_nil_rev | apply cgr_par_com ].
Qed.

(** La réduction : sur le fragment sans [ν], la complétude se ramène à la
    comparaison de deux **configurations nues**, avec l'hypothèse
    sémantique livrée exactement à ce niveau-là. *)

Theorem completeness_nores_from_cfg :
  (forall l1 M1 l2 M2, gStatic M1 -> gStatic M2 ->
     (msgs l1 ‖ ((g M1) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l2 ‖ ((g M2) : proc)) ->
     ax_pre (msgs l1 ‖ ((g M1) : proc)) (msgs l2 ‖ ((g M2) : proc))) ->
  forall p q, Static p -> Static q -> NoRes p -> NoRes q ->
    p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> ax_pre p q.
Proof.
  intros H p q Hp Hq Hnp Hnq Hsem.
  destruct (normal_form_nores p Hp Hnp) as (l1 & M1 & HM1 & Ha1 & Hb1).
  destruct (normal_form_nores q Hq Hnq) as (l2 & M2 & HM2 & Ha2 & Hb2).
  eapply ax_trans; [ exact Ha1 | ].
  eapply ax_trans; [ | exact Hb2 ].
  apply H; try assumption.
  intros t Ht.
  apply (soundness_ax _ _ Ha2). apply Hsem. apply (soundness_ax _ _ Hb1). exact Ht.
Qed.

(** The semantic reading, for free by soundness. *)
Corollary normal_form_sem : forall p, Static p ->
  exists n l M, gStatic M /\ p ≂ₘᵤₛₜᵢ (NF n l M).
Proof.
  intros p Hs. destruct (normal_form p Hs) as (n & l & M & HM & Ha & Hb).
  exists n, l, M. split; [ exact HM | ]. split; apply soundness_ax; assumption.
Qed.

(** ** A step-dominating normal form

    [normal_form] alone is not enough to recurse into a [𝛕]-continuation:
    normalisation is **not** size-decreasing (the expansion law blows terms
    up), so a continuation of the normal form is not known to be smaller
    than the process it came from.  VCCS solved this with a one-step
    simulation, and the same works here.

        step_dominated p q  :=  ∀ a r, q ⟶{a} r ->
                                ∃ r', p ⟶{a} r' ∧ ⊢ r ≂ r'

    Each transition of the normal form is matched by a transition of the
    **original** process, with [⊢]-equal targets.  A matched target is a
    genuine reduct of [p], so [Static_lts_decrease] makes it strictly
    smaller in [size]; the caller recurses on *it* and transports the
    result back along the [⊢]-equality.  No bisimulation and no coinduction
    are needed — one step always suffices.

    [dom] bundles the simulation with the [⊢]-equality, because the [‖]
    case needs both: when one side moves, the *other* side is the
    normalised component on the left and the original on the right, and
    only the [⊢]-equality relates them.

    The combinators below then give the theorem for free, each construction
    of [normal_form] having its own: [dom_cgr] for the structural steps
    (via the repository's [Congruence_Respects_Transition]), [dom_par] and
    [dom_res] for the operators, and [dom_expansion] / [dom_resg] for the
    two flattening laws — those two are *literal* transition equalities, so
    their targets need only [ax_refl]. *)

Definition step_dominated (p q : proc) : Prop :=
  forall a r, lts q a r -> exists r', lts p a r' /\ ax_pre r r' /\ ax_pre r' r.

Definition dom (p q : proc) : Prop := ax_pre p q /\ ax_pre q p /\ step_dominated p q.

Lemma dom_refl : forall p, dom p p.
Proof.
  intros p. split; [apply ax_refl | split; [apply ax_refl | ]].
  intros a r H. exists r. split; [exact H | split; apply ax_refl].
Qed.

Lemma dom_trans : forall p q r, dom p q -> dom q r -> dom p r.
Proof.
  intros p q r (Ha & Hb & Hs) (Hc & Hd & Ht).
  split; [ eapply ax_trans; eassumption | split; [ eapply ax_trans; eassumption | ]].
  intros a x Hx.
  destruct (Ht a x Hx) as (y & Hy & H1 & H2).
  destruct (Hs a y Hy) as (z & Hz & H3 & H4).
  exists z. split; [exact Hz | split; eapply ax_trans; eassumption].
Qed.

Lemma dom_cgr : forall p q, p ≡* q -> dom p q.
Proof.
  intros p q Hc.
  split; [apply ax_cgr; exact Hc | split; [apply ax_cgr_sym; exact Hc | ]].
  intros a r Hr.
  assert (sc_then_lts p a r) as Hsc by (exists q; split; assumption).
  apply Congruence_Respects_Transition in Hsc as (r' & Hl & Hcgr).
  exists r'. split; [exact Hl | split; [ apply ax_cgr_sym; exact Hcgr | apply ax_cgr; exact Hcgr ]].
Qed.

Lemma dom_res : forall p q, dom p q -> dom (ν p) (ν q).
Proof.
  intros p q (Ha & Hb & Hs).
  split; [apply ax_res; exact Ha | split; [apply ax_res; exact Hb | ]].
  intros a r Hr. inversion Hr; subst.
  - destruct (Hs _ _ H0) as (y & Hy & H1' & H2').
    exists (ν y). split; [ apply lts_res_ext; exact Hy | split; apply ax_res; assumption ].
  - match goal with HH : lts q _ _ |- _ => destruct (Hs _ _ HH) as (y & Hy & H1' & H2') end.
    exists (ν y). split; [ apply lts_res_tau; exact Hy | split; apply ax_res; assumption ].
Qed.

Lemma dom_par : forall p1 q1 p2 q2, dom p1 q1 -> dom p2 q2 -> dom (p1 ‖ p2) (q1 ‖ q2).
Proof.
  intros p1 q1 p2 q2 (Ha1 & Hb1 & Hs1) (Ha2 & Hb2 & Hs2).
  split; [apply ax_par; assumption | split; [apply ax_par; assumption | ]].
  intros a r Hr. inversion Hr; subst.
  - match goal with HA : lts q1 _ _ |- _ => destruct (Hs1 _ _ HA) as (y & Hy & Hc & Hd) end.
    match goal with HB : lts q2 _ _ |- _ => destruct (Hs2 _ _ HB) as (z & Hz & He & Hf) end.
    exists (y ‖ z). split; [ eapply lts_comL; eassumption | split; apply ax_par; assumption ].
  - match goal with HA : lts q1 _ _ |- _ => destruct (Hs1 _ _ HA) as (y & Hy & Hc & Hd) end.
    match goal with HB : lts q2 _ _ |- _ => destruct (Hs2 _ _ HB) as (z & Hz & He & Hf) end.
    exists (y ‖ z). split; [ eapply lts_comR; eassumption | split; apply ax_par; assumption ].
  - match goal with HA : lts q1 _ _ |- _ => destruct (Hs1 _ _ HA) as (y & Hy & Hc & Hd) end.
    exists (y ‖ p2). split; [ apply lts_parL; exact Hy | split; apply ax_par; assumption ].
  - match goal with HB : lts q2 _ _ |- _ => destruct (Hs2 _ _ HB) as (z & Hz & He & Hf) end.
    exists (p1 ‖ z). split; [ apply lts_parR; exact Hz | split; apply ax_par; assumption ].
Qed.

Lemma dom_expansion : forall M N, dom (g M ‖ g N) (g (ext M N + ext_r N M)).
Proof.
  intros M N.
  split; [apply ax_expansion_l | split; [apply ax_expansion_r | ]].
  intros a r Hr. exists r. split; [ | split; apply ax_refl ].
  apply expansion_lts_iff. apply lts_choice2_iff. exact Hr.
Qed.

Lemma dom_resg : forall M, dom (ν (g M)) (g (resg M)).
Proof.
  intros M.
  split; [apply ax_res_normalize_l | split; [apply ax_res_normalize_r | ]].
  intros a r Hr. exists r. split; [ | split; apply ax_refl ].
  apply resg_lts_iff. exact Hr.
Qed.

Lemma dom_res_n : forall n p q, dom p q -> dom (Ѵ n p) (Ѵ n q).
Proof. induction n; intros p q H; simpl; [exact H | apply dom_res; apply IHn; exact H]. Qed.

(** ** [dom] IS closable under one step — the simulation [domsim]

    [step_dominated] stops at [⊢]-equal targets, so it descends exactly one
    step.  Anything that has to follow a *run* of the normal form — for
    instance a state reached by emitting part of the message bag and only
    then performing an input — needs the matched targets to be related
    again.  That is [domsim]: a **one-sided simulation up to [⊢]**.

    It is strictly weaker than a bisimulation (nothing is asked of the
    left-hand side's own transitions), and every combinator of the [dom]
    layer carries over unchanged:

    - [domsim_expansion] and [domsim_resg] need no coinduction at all —
      their transition correspondences are *literal equalities*, so the
      target is its own witness;
    - [domsim_cgr] closes because [Congruence_Respects_Transition] returns
      a target still related by [≡*], which re-enters the same lemma;
    - [domsim_par]/[domsim_res] are compositional, feeding the corecursive
      call the strengthened sub-results.

    So the earlier worry that iterating [dom] would need bisimulation
    strength was the right instinct and the wrong conclusion. *)

CoInductive domsim : proc -> proc -> Prop :=
| DomSim : forall p q,
    ax_pre p q -> ax_pre q p ->
    (forall a r, lts q a r -> exists r', lts p a r' /\ domsim r' r) ->
    domsim p q.

Definition ds_l {p q} (H : domsim p q) : ax_pre p q :=
  match H with DomSim _ _ a _ _ => a end.
Definition ds_r {p q} (H : domsim p q) : ax_pre q p :=
  match H with DomSim _ _ _ b _ => b end.
Definition ds_s {p q} (H : domsim p q) :
  forall a r, lts q a r -> exists r', lts p a r' /\ domsim r' r :=
  match H with DomSim _ _ _ _ s => s end.

Lemma domsim_dom : forall p q, domsim p q -> dom p q.
Proof.
  intros p q H. split; [ exact (ds_l H) | split; [ exact (ds_r H) | ] ].
  intros a r Hr. destruct (ds_s H a r Hr) as (r' & Hl & Hd).
  exists r'. split; [ exact Hl | split; [ exact (ds_r Hd) | exact (ds_l Hd) ] ].
Qed.

Lemma domsim_refl : forall p, domsim p p.
Proof.
  cofix CIH. intro p. apply DomSim; [ apply ax_refl | apply ax_refl | ].
  intros a r Hr. exists r. split; [ exact Hr | apply CIH ].
Qed.

Lemma domsim_trans : forall p q r, domsim p q -> domsim q r -> domsim p r.
Proof.
  cofix CIH. intros p q r Hpq Hqr.
  apply DomSim;
    [ eapply ax_trans; [ exact (ds_l Hpq) | exact (ds_l Hqr) ]
    | eapply ax_trans; [ exact (ds_r Hqr) | exact (ds_r Hpq) ] | ].
  intros a x Hx.
  destruct (ds_s Hqr a x Hx) as (y & Hy & Hy2).
  destruct (ds_s Hpq a y Hy) as (z & Hz & Hz2).
  exists z. split; [ exact Hz | eapply CIH; [ exact Hz2 | exact Hy2 ] ].
Qed.

Lemma domsim_cgr : forall p q, p ≡* q -> domsim p q.
Proof.
  cofix CIH. intros p q Hc.
  apply DomSim; [ apply ax_cgr; exact Hc | apply ax_cgr_sym; exact Hc | ].
  intros a r Hr.
  assert (sc_then_lts p a r) as Hsc by (exists q; split; assumption).
  apply Congruence_Respects_Transition in Hsc as (r' & Hl & Hcgr).
  exists r'. split; [ exact Hl | apply CIH; exact Hcgr ].
Qed.

Lemma domsim_res : forall p q, domsim p q -> domsim (ν p) (ν q).
Proof.
  cofix CIH. intros p q H.
  apply DomSim; [ apply ax_res; exact (ds_l H) | apply ax_res; exact (ds_r H) | ].
  intros a r Hr. inversion Hr; subst.
  - match goal with HH : lts q _ _ |- _ => destruct (ds_s H _ _ HH) as (y & Hy & Hy2) end.
    exists (ν y). split; [ apply lts_res_ext; exact Hy | apply CIH; exact Hy2 ].
  - match goal with HH : lts q _ _ |- _ => destruct (ds_s H _ _ HH) as (y & Hy & Hy2) end.
    exists (ν y). split; [ apply lts_res_tau; exact Hy | apply CIH; exact Hy2 ].
Qed.

Lemma domsim_par : forall p1 q1 p2 q2,
  domsim p1 q1 -> domsim p2 q2 -> domsim (p1 ‖ p2) (q1 ‖ q2).
Proof.
  cofix CIH. intros p1 q1 p2 q2 H1 H2.
  apply DomSim;
    [ apply ax_par; [ exact (ds_l H1) | exact (ds_l H2) ]
    | apply ax_par; [ exact (ds_r H1) | exact (ds_r H2) ] | ].
  intros a r Hr. inversion Hr; subst.
  - match goal with HA : lts q1 _ _ |- _ => destruct (ds_s H1 _ _ HA) as (y & Hy & Hy2) end.
    match goal with HB : lts q2 _ _ |- _ => destruct (ds_s H2 _ _ HB) as (z & Hz & Hz2) end.
    exists (y ‖ z). split; [ eapply lts_comL; eassumption | apply CIH; assumption ].
  - match goal with HA : lts q1 _ _ |- _ => destruct (ds_s H1 _ _ HA) as (y & Hy & Hy2) end.
    match goal with HB : lts q2 _ _ |- _ => destruct (ds_s H2 _ _ HB) as (z & Hz & Hz2) end.
    exists (y ‖ z). split; [ eapply lts_comR; eassumption | apply CIH; assumption ].
  - match goal with HA : lts q1 _ _ |- _ => destruct (ds_s H1 _ _ HA) as (y & Hy & Hy2) end.
    exists (y ‖ p2). split; [ apply lts_parL; exact Hy | apply CIH; [ exact Hy2 | exact H2 ] ].
  - match goal with HB : lts q2 _ _ |- _ => destruct (ds_s H2 _ _ HB) as (z & Hz & Hz2) end.
    exists (p1 ‖ z). split; [ apply lts_parR; exact Hz | apply CIH; [ exact H1 | exact Hz2 ] ].
Qed.

Lemma domsim_expansion : forall M N, domsim (g M ‖ g N) (g (ext M N + ext_r N M)).
Proof.
  intros M N. apply DomSim; [ apply ax_expansion_l | apply ax_expansion_r | ].
  intros a r Hr. exists r.
  split; [ apply expansion_lts_iff; apply lts_choice2_iff; exact Hr | apply domsim_refl ].
Qed.

Lemma domsim_resg : forall M, domsim (ν (g M)) (g (resg M)).
Proof.
  intros M. apply DomSim; [ apply ax_res_normalize_l | apply ax_res_normalize_r | ].
  intros a r Hr. exists r.
  split; [ apply resg_lts_iff; exact Hr | apply domsim_refl ].
Qed.

Lemma domsim_res_n : forall n p q, domsim p q -> domsim (Ѵ n p) (Ѵ n q).
Proof. induction n; intros p q H; simpl; [ exact H | apply domsim_res; apply IHn; exact H ]. Qed.

(** The normal form is reached by the simulation, not merely by [dom] —
    and the proof script is [normal_form_strong]'s, unchanged apart from
    the names. *)
Theorem normal_form_strong_sim : forall p, Static p ->
  exists n l M, gStatic M /\ domsim p (NF n l M).
Proof.
  intro p. induction p as [p IHp] using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intro Hs. destruct p as [p1 p2|x|x p0|E p1 p2|c v|p0|M].
  - inversion Hs; subst.
    destruct (IHp p1 ltac:(simpl; lia) H1) as (n1 & l1 & M1 & HM1 & Hd1).
    destruct (IHp p2 ltac:(simpl; lia) H2) as (n2 & l2 & M2 & HM2 & Hd2).
    set (N1 := gNewVarCn 0 n2 M1). set (N2 := gNewVarCn n2 n1 M2).
    set (L1 := map (shiftCn 0 n2) l1). set (L2 := map (shiftCn n2 n1) l2).
    exists ((n1 + n2)%nat), (L2 ++ L1), (ext N2 N1 + ext_r N1 N2).
    split.
    { subst N1 N2. constructor.
      - apply ext_gStatic; apply gStatic_gNewVarCn; assumption.
      - apply ext_r_gStatic; apply gStatic_gNewVarCn; assumption. }
    eapply domsim_trans; [ apply domsim_par; [exact Hd1 | exact Hd2] | ].
    eapply domsim_trans; [ apply domsim_cgr; apply NF_par_step | ].
    unfold NF. apply domsim_res_n.
    eapply domsim_trans;
      [ apply domsim_par;
        [ apply domsim_cgr; symmetry; apply msgs_app | apply domsim_refl ] | ].
    apply domsim_par; [ apply domsim_refl | apply domsim_expansion ].
  - inversion Hs.
  - inversion Hs.
  - destruct (Eval_Eq 0 E) as [[|]|] eqn:HE;
      [ | | exfalso; eapply Eval_Eq_0_not_none; exact HE ].
    + inversion Hs; subst.
      destruct (IHp p1 ltac:(simpl; lia) H1) as (n & l & M & HM & Hd).
      exists n, l, M. split; [ exact HM | ].
      eapply domsim_trans; [ apply domsim_cgr; apply cgr_if_true; exact HE | exact Hd ].
    + inversion Hs; subst.
      destruct (IHp p2 ltac:(simpl; lia) H3) as (n & l & M & HM & Hd).
      exists n, l, M. split; [ exact HM | ].
      eapply domsim_trans; [ apply domsim_cgr; apply cgr_if_false; exact HE | exact Hd ].
  - exists 0, [(c,v)], 𝟘. split; [ constructor | ]. unfold NF. simpl.
    apply domsim_cgr. etransitivity; [ apply cgr_par_nil_rev | ].
    apply cgr_fullpar; [ apply cgr_par_nil_rev | reflexivity ].
  - inversion Hs; subst.
    destruct (IHp p0 ltac:(simpl; lia) H0) as (n & l & M & HM & Hd).
    exists (S n), l, M. split; [ exact HM | ]. unfold NF in *. simpl.
    apply domsim_res. exact Hd.
  - inversion Hs; subst.
    exists 0, [], M. split; [ assumption | ]. unfold NF. simpl.
    apply domsim_cgr. etransitivity; [ apply cgr_par_nil_rev | apply cgr_par_com ].
Qed.

(** The payoff: the descent follows a whole **run**, not one step.  Every
    state the normal form reaches along a trace — including one reached by
    emitting part of the message bag before acting — is [⊢]-equal to a
    state the original process reaches along the *same* trace. *)
Lemma domsim_wt : forall q s r, q ⟹[s] r ->
  forall p, domsim p q -> exists r', p ⟹[s] r' /\ domsim r' r.
Proof.
  intros q s r Hw. induction Hw as [q0 | s0 q0 q1 r0 Hl Hw IH | mu s0 q0 q1 r0 Hl Hw IH];
    intros p Hd.
  - exists p. split; [ apply wt_nil | exact Hd ].
  - destruct (ds_s Hd _ _ Hl) as (y & Hy & Hy2).
    destruct (IH y Hy2) as (z & Hz & Hz2).
    exists z. split; [ eapply wt_tau; [ exact Hy | exact Hz ] | exact Hz2 ].
  - destruct (ds_s Hd _ _ Hl) as (y & Hy & Hy2).
    destruct (IH y Hy2) as (z & Hz & Hz2).
    exists z. split; [ eapply wt_act; [ exact Hy | exact Hz ] | exact Hz2 ].
Qed.

Corollary domsim_wt_reduct : forall p q s r, Static p -> domsim p q -> q ⟹[s] r ->
  exists r', p ⟹[s] r' /\ Static r' /\ ax_pre r r' /\ ax_pre r' r.
Proof.
  intros p q s r Hp Hd Hw.
  destruct (domsim_wt q s r Hw p Hd) as (r' & Hr' & Hd').
  exists r'. split; [ exact Hr' | ].
  split; [ eapply Static_preserved_by_wt; eassumption | ].
  split; [ exact (ds_r Hd') | exact (ds_l Hd') ].
Qed.

(** ** UNIFORM domination — the notion the recursive normal form needs

    [step_dominated] matches each transition of the normal form by one of
    the original process, but for an *input* it does so **per value**: the
    witness depends on [v].  The omega rule [ax_fwd_match] consumes a
    single **open** continuation, so a construction that normalises input
    continuations needs the witness to be a family [R'^v] for one open
    [R'].  That is [sd_u].

    Why it is wanted: with it, a *recursive* normal form becomes
    constructible — one whose input continuations are themselves complete
    configurations.  That dissolves the level mismatch recorded at
    [VACCS_Matching.ax_below_stable_NF], because the recursive premise's
    right-hand side is then already wrapped, and [dom] and the matching
    meet at the same level.

    **Status: begun, not finished.**  The four combinators below are
    proved.  [dom_u_expansion] and [dom_u_resg] are free — their
    transition correspondences are *literal equalities*, so the witness is
    the given family itself.  What remains is [dom_u_res], [dom_u_par] and
    [dom_u_cgr], and then re-proving [normal_form_strong] with [dom_u] in
    place of [dom].  The first two need a syntactic inversion that is
    stated but not proved here: from [∀v, R^v = ν S_v] (resp. a parallel
    composition) conclude [R = ν S] for an open [S] — true because
    substitution preserves head constructors, but it is a case analysis
    over all seven [proc] constructors.  [dom_u_cgr] is the doubtful one:
    it goes through [Congruence_Respects_Transition], whose witness is an
    existential with no uniformity built in. *)

Definition sd_u (p q : proc) : Prop :=
  forall (c : ChannelData) (R : proc),
    (forall v, lts q (ActExt (ActIn (c,v))) (subst_in_proc 0 v R)) ->
    exists R', (forall v, lts p (ActExt (ActIn (c,v))) (subst_in_proc 0 v R'))
            /\ (forall v, ax_pre (subst_in_proc 0 v R) (subst_in_proc 0 v R'))
            /\ (forall v, ax_pre (subst_in_proc 0 v R') (subst_in_proc 0 v R)).

Definition dom_u (p q : proc) : Prop := dom p q /\ sd_u p q.

Lemma dom_u_refl : forall p, dom_u p p.
Proof.
  intro p. split; [ apply dom_refl | ].
  intros c R HR. exists R. split; [ exact HR | split; intro v; apply ax_refl ].
Qed.

Lemma dom_u_trans : forall p q r, dom_u p q -> dom_u q r -> dom_u p r.
Proof.
  intros p q r (Hd1 & Hu1) (Hd2 & Hu2). split; [ eapply dom_trans; eassumption | ].
  intros c R HR.
  destruct (Hu2 c R HR) as (R1 & H1 & H2 & H3).
  destruct (Hu1 c R1 H1) as (R2 & H4 & H5 & H6).
  exists R2. split; [ exact H4 | split; intro v; eapply ax_trans; eauto ].
Qed.

Lemma dom_u_expansion : forall M N, dom_u (g M ‖ g N) (g (ext M N + ext_r N M)).
Proof.
  intros M N. split; [ apply dom_expansion | ].
  intros c R HR. exists R. split; [ | split; intro v; apply ax_refl ].
  intro v. apply expansion_lts_iff. apply lts_choice2_iff. apply HR.
Qed.

Lemma dom_u_resg : forall M, dom_u (ν (g M)) (g (resg M)).
Proof.
  intros M. split; [ apply dom_resg | ].
  intros c R HR. exists R. split; [ | split; intro v; apply ax_refl ].
  intro v. apply resg_lts_iff. apply HR.
Qed.

(** Input transitions come in **uniform families**.  Every `(c,v)?`-step
    of a process is `R^v` for one open `R` that works at *every* value —
    the constructive strengthening of [lts_in_value_swap], which only
    asserts that *some* step exists at each value.

    Read off the transition rules: [lts_input] is the only one that
    inspects the value, and it substitutes into a fixed continuation;
    every other rule is a context that the value never enters.  The two
    parallel cases are where the bookkeeping shows: the untouched side has
    to be shifted out of the binder's way with [NewVar], and
    [NewVar_subst_cancel] puts it back.

    This is the transition half of what a *recursive* normal form needs.
    The equality half — that the `⊢`-witness can also be chosen uniformly
    — is what [sd_u] asks for, and is not supplied by this lemma. *)

Lemma lts_in_uniform : forall (p : proc) (a : ActIO TypeOfActions) (r : proc),
  lts p a r -> forall c v, a = ActExt (ActIn (c,v)) ->
  exists R, r = subst_in_proc 0 v R
         /\ forall w, lts p (ActExt (ActIn (c,w))) (subst_in_proc 0 w R).
Proof.
  intros p a r Hl.
  induction Hl; intros c0 v0 Heq; try discriminate Heq.
  - inversion Heq; subst. exists P. split; [ reflexivity | intro w; apply lts_input ].
  - destruct (IHHl c0 v0 Heq) as (R & E1 & E2).
    exists R. split; [ exact E1 | intro w; eapply lts_ifOne; [ exact H | apply E2 ] ].
  - destruct (IHHl c0 v0 Heq) as (R & E1 & E2).
    exists R. split; [ exact E1 | intro w; eapply lts_ifZero; [ exact H | apply E2 ] ].
  - inversion Heq; subst.
    destruct (IHHl (VarC_add 1 c0) v0 eq_refl) as (R & E1 & E2).
    exists (ν R). split.
    + simpl. rewrite E1. reflexivity.
    + intro w. simpl. apply lts_res_ext. apply E2.
  - inversion Heq; subst.
    destruct (IHHl c0 v0 eq_refl) as (R & E1 & E2).
    exists (R ‖ NewVar 0 q). split.
    + simpl. rewrite E1. rewrite NewVar_subst_cancel. reflexivity.
    + intro w. simpl. rewrite NewVar_subst_cancel. apply lts_parL. apply E2.
  - inversion Heq; subst.
    destruct (IHHl c0 v0 eq_refl) as (R & E1 & E2).
    exists (NewVar 0 p ‖ R). split.
    + simpl. rewrite E1. rewrite NewVar_subst_cancel. reflexivity.
    + intro w. simpl. rewrite NewVar_subst_cancel. apply lts_parR. apply E2.
  - destruct (IHHl c0 v0 Heq) as (R & E1 & E2).
    exists R. split; [ exact E1 | intro w; apply lts_choiceL; apply E2 ].
  - destruct (IHHl c0 v0 Heq) as (R & E1 & E2).
    exists R. split; [ exact E1 | intro w; apply lts_choiceR; apply E2 ].
Qed.

(** Substitution preserves head constructors, so an open term whose
    instance is a parallel composition (a restriction) is itself one.
    These are the inversions the functorial [dom_u] combinators need, and
    they cost one [destruct] apiece. *)

Lemma subst_par_inv : forall (R : proc) (v : ValueData) (r1 r2 : proc),
  subst_in_proc 0 v R = r1 ‖ r2 ->
  exists R1 R2, R = R1 ‖ R2
             /\ r1 = subst_in_proc 0 v R1 /\ r2 = subst_in_proc 0 v R2.
Proof.
  intros R v r1 r2 H. destruct R; simpl in H; try discriminate H.
  inversion H; subst. exists R1, R2. split; [ reflexivity | split; reflexivity ].
Qed.

Lemma subst_res_inv : forall (R : proc) (v : ValueData) (r : proc),
  subst_in_proc 0 v R = ν r ->
  exists R0, R = ν R0 /\ r = subst_in_proc 0 v R0.
Proof.
  intros R v r H. destruct R; simpl in H; try discriminate H.
  inversion H; subst. exists R. split; [ reflexivity | reflexivity ].
Qed.

(** Uniform domination survives restriction.  The channel shift
    [VarC_action_add] leaves the *value* alone, so the inner family is
    indexed by the same values as the outer one. *)

Lemma dom_u_res : forall p q, dom_u p q -> dom_u (ν p) (ν q).
Proof.
  intros p q (Hd & Hu). split; [ apply dom_res; exact Hd | ].
  intros c R HR.
  assert (H0 := HR (cst O)).
  inversion H0; subst.
  destruct (subst_res_inv R (cst O) p' (eq_sym H2)) as (R0 & ER & _).
  subst R.
  assert (HQ : forall v, lts q (ActExt (ActIn (VarC_add 1 c, v))) (subst_in_proc 0 v R0)).
  { intro v. assert (Hv := HR v). simpl in Hv. inversion Hv; subst.
    match goal with HH : lts q _ _ |- _ => exact HH end. }
  destruct (Hu (VarC_add 1 c) R0 HQ) as (R0' & H1 & H2' & H3').
  exists (ν R0'). split.
  - intro v. simpl. apply lts_res_ext. apply H1.
  - split; intro v; simpl; apply ax_res; [ apply H2' | apply H3' ].
Qed.

(** Uniform domination survives parallel composition — and this is where
    the notion earns its `Static` hypotheses.

    For an *input* only [lts_parL] and [lts_parR] apply ([lts_comL] and
    [lts_comR] produce a `τ`), so the family either always moves the left
    operand or always the right.  That it cannot *switch* with the value
    is the one non-formal step: if `cst O` took [parL] while some `v` took
    [parR], then `R1^v = q1` — so `size (R1^v) = size q1` — while
    `R1^(cst O)` is a strict reduct of `q1`.  [size_subst] makes the two
    sizes equal and [Static_lts_decrease] makes them differ.

    Both call sites in [normal_form_strong] have the `Static` hypotheses
    available. *)

Lemma dom_u_par : forall p1 q1 p2 q2, Static q1 -> Static q2 ->
  dom_u p1 q1 -> dom_u p2 q2 -> dom_u (p1 ‖ p2) (q1 ‖ q2).
Proof.
  intros p1 q1 p2 q2 HS1 HS2 (Hd1 & Hu1) (Hd2 & Hu2).
  split; [ apply dom_par; assumption | ].
  intros c R HR.
  assert (H0 := HR (cst O)).
  inversion H0; subst.
  - destruct (subst_par_inv R (cst O) p3 q2 (eq_sym H4)) as (R1 & R2 & ER & E1 & E2).
    subst R.
    assert (HQ : forall v, lts q1 (ActExt (ActIn (c,v))) (subst_in_proc 0 v R1)
                        /\ subst_in_proc 0 v R2 = subst_in_proc 0 (cst O) R2).
    { intro v. assert (Hv := HR v). simpl in Hv. inversion Hv; subst.
      - split; [ assumption | symmetry; assumption ].
      - exfalso.
        assert (Hsz : (size (subst_in_proc 0 (cst O) R1) < size (subst_in_proc 0 v R1))%nat)
          by (eapply Static_lts_decrease; [ exact HS1 | exact H3 ]).
        rewrite !size_subst in Hsz. lia. }
    destruct (Hu1 c R1 (fun v => proj1 (HQ v))) as (R1' & Ha & Hb & Hc).
    destruct Hd2 as (Hd2a & Hd2b & _).
    exists (R1' ‖ NewVar 0 p2). split.
    + intro v. simpl. rewrite NewVar_subst_cancel. apply lts_parL. apply Ha.
    + split; intro v; simpl; rewrite NewVar_subst_cancel;
        rewrite (proj2 (HQ v)); rewrite <- E2;
        apply ax_par; solve [ apply Hb | apply Hc | exact Hd2a | exact Hd2b ].
  - destruct (subst_par_inv R (cst O) q1 q3 (eq_sym H4)) as (R1 & R2 & ER & E1 & E2).
    subst R.
    assert (HQ : forall v, lts q2 (ActExt (ActIn (c,v))) (subst_in_proc 0 v R2)
                        /\ subst_in_proc 0 v R1 = subst_in_proc 0 (cst O) R1).
    { intro v. assert (Hv := HR v). simpl in Hv. inversion Hv; subst.
      - exfalso.
        assert (Hsz : (size (subst_in_proc 0 (cst O) R2) < size (subst_in_proc 0 v R2))%nat)
          by (eapply Static_lts_decrease; [ exact HS2 | exact H3 ]).
        rewrite !size_subst in Hsz. lia.
      - split; [ assumption | symmetry; assumption ]. }
    destruct (Hu2 c R2 (fun v => proj1 (HQ v))) as (R2' & Ha & Hb & Hc).
    destruct Hd1 as (Hd1a & Hd1b & _).
    exists (NewVar 0 p1 ‖ R2'). split.
    + intro v. simpl. rewrite NewVar_subst_cancel. apply lts_parR. apply Ha.
    + split; intro v; simpl; rewrite NewVar_subst_cancel;
        rewrite (proj2 (HQ v)); rewrite <- E1;
        apply ax_par; solve [ apply Hb | apply Hc | exact Hd1a | exact Hd1b ].
Qed.

(** Two of `normal_form_strong`'s six `dom_cgr` sites need no work at all.

    A process with **no input transitions** dominates uniformly for free —
    the hypothesis of `sd_u` is unsatisfiable.  That covers the
    `pr_output` case, whose normal form `msgs [(c,v)] ‖ g 𝟘` is a message
    beside `𝟘`. *)

Lemma sd_u_vacuous : forall p q,
  (forall c v r, ~ lts q (ActExt (ActIn (c,v))) r) -> sd_u p q.
Proof.
  intros p q Hno c R HR. exfalso. eapply Hno. apply (HR (cst O)).
Qed.

(** And the bare-sum case is the unit law, whose transition
    correspondence is functorial: only [lts_parR] can fire, so the family
    is carried across unchanged and the `⊢`-equalities are one `ax_cgr`. *)

Lemma dom_u_nil_par : forall p, dom_u p (((g 𝟘) : proc) ‖ p).
Proof.
  intro p.
  assert (Hc : p ≡* (((g 𝟘) : proc) ‖ p)).
  { etransitivity; [ apply cgr_par_nil_rev | apply cgr_par_com ]. }
  split; [ apply dom_cgr; exact Hc | ].
  intros c R HR.
  assert (H0 := HR (cst O)). inversion H0; subst.
  - exfalso. match goal with HH : lts (g 𝟘) _ _ |- _ => inversion HH end.
  - destruct (subst_par_inv R (cst O) ((g 𝟘) : proc) q2 (eq_sym H4))
      as (R1 & R2 & ER & E1 & E2).
    subst R.
    assert (HQ : forall v, lts p (ActExt (ActIn (c,v))) (subst_in_proc 0 v R2)
                        /\ subst_in_proc 0 v R1 = ((g 𝟘) : proc)).
    { intro v. assert (Hv := HR v). simpl in Hv. inversion Hv; subst.
      - exfalso. match goal with HH : lts (g 𝟘) _ _ |- _ => inversion HH end.
      - split; [ assumption | reflexivity ]. }
    exists R2. split; [ intro v; apply (proj1 (HQ v)) | ].
    split; intro v; simpl; rewrite (proj2 (HQ v)).
    + apply ax_cgr. etransitivity; [ apply cgr_par_com | apply cgr_par_nil ].
    + apply ax_cgr_sym. etransitivity; [ apply cgr_par_com | apply cgr_par_nil ].
Qed.

(** A message bag has no input transitions at all — it is a parallel
    composition of *outputs*.  So every congruence between message bags is
    uniformly dominating for free, which retires the `msgs_app` site. *)

Lemma dom_u_cgr_no_input : forall p q, p ≡* q ->
  (forall c v r, ~ lts q (ActExt (ActIn (c,v))) r) -> dom_u p q.
Proof.
  intros p q Hc Hno. split; [ apply dom_cgr; exact Hc | apply sd_u_vacuous; exact Hno ].
Qed.

(** Commutativity of [‖], uniformly.  Same recipe as [dom_u_par]: invert
    with [subst_par_inv], rule out the branch switching by [size_subst] +
    [Static_lts_decrease], rebuild the family with [NewVar] on the
    untouched side, and discharge the two `⊢`-equalities with one
    [ax_cgr] each. *)

Lemma dom_u_par_com : forall p q, Static p -> Static q -> dom_u (p ‖ q) (q ‖ p).
Proof.
  intros p q HSp HSq.
  split; [ apply dom_cgr; apply cgr_par_com | ].
  intros c R HR.
  assert (H0 := HR (cst O)). inversion H0; subst.
  - destruct (subst_par_inv R (cst O) p2 p (eq_sym H4)) as (R1 & R2 & ER & E1 & E2).
    subst R.
    assert (HQ : forall v, lts q (ActExt (ActIn (c,v))) (subst_in_proc 0 v R1)
                        /\ subst_in_proc 0 v R2 = subst_in_proc 0 (cst O) R2).
    { intro v. assert (Hv := HR v). simpl in Hv. inversion Hv; subst.
      - split; [ assumption | symmetry; assumption ].
      - exfalso.
        assert (Hsz : (size (subst_in_proc 0 (cst O) R1) < size (subst_in_proc 0 v R1))%nat)
          by (eapply Static_lts_decrease; [ exact HSq | exact H3 ]).
        rewrite !size_subst in Hsz. lia. }
    exists (NewVar 0 p ‖ R1). split.
    + intro v. simpl. rewrite NewVar_subst_cancel. apply lts_parR. apply (proj1 (HQ v)).
    + split; intro v; simpl; rewrite NewVar_subst_cancel;
        rewrite (proj2 (HQ v)); rewrite <- E2;
        [ apply ax_cgr | apply ax_cgr_sym ]; apply cgr_par_com.
  - destruct (subst_par_inv R (cst O) q q2 (eq_sym H4)) as (R1 & R2 & ER & E1 & E2).
    subst R.
    assert (HQ : forall v, lts p (ActExt (ActIn (c,v))) (subst_in_proc 0 v R2)
                        /\ subst_in_proc 0 v R1 = subst_in_proc 0 (cst O) R1).
    { intro v. assert (Hv := HR v). simpl in Hv. inversion Hv; subst.
      - exfalso.
        assert (Hsz : (size (subst_in_proc 0 (cst O) R2) < size (subst_in_proc 0 v R2))%nat)
          by (eapply Static_lts_decrease; [ exact HSp | exact H3 ]).
        rewrite !size_subst in Hsz. lia.
      - split; [ assumption | symmetry; assumption ]. }
    exists (R2 ‖ NewVar 0 q). split.
    + intro v. simpl. rewrite NewVar_subst_cancel. apply lts_parL. apply (proj1 (HQ v)).
    + split; intro v; simpl; rewrite NewVar_subst_cancel;
        rewrite (proj2 (HQ v)); rewrite <- E1;
        [ apply ax_cgr | apply ax_cgr_sym ]; apply cgr_par_com.
Qed.

(** The channel shift and the value substitution commute — they never
    touch the same syntax.  Both indices have to be generalised: the
    substitution's index climbs under an input guard, the shift's under a
    [ν], and each fixpoint's own case does one of the two. *)

Lemma subst_NewVarC : forall q j k X,
  subst_in_proc j X (NewVarC k q) = NewVarC k (subst_in_proc j X q)
with subst_gNewVarC : forall M j k X,
  subst_in_gproc j X (gNewVarC k M) = gNewVarC k (subst_in_gproc j X M).
Proof.
  - destruct q; intros j k X; simpl; try reflexivity.
    + f_equal; apply subst_NewVarC.
    + f_equal; apply subst_NewVarC.
    + f_equal; apply subst_NewVarC.
    + f_equal; apply subst_NewVarC.
    + f_equal; apply subst_gNewVarC.
  - destruct M; intros j k X; simpl; try reflexivity.
    + f_equal; apply subst_NewVarC.
    + f_equal; apply subst_NewVarC.
    + f_equal; apply subst_gNewVarC.
Qed.

(** And the converse: an open term whose instance is a channel-shift is
    itself one.  This is the [NewVarC] analogue of [subst_par_inv] /
    [subst_res_inv] — but `‖` and `ν` are *constructors*, so those were one
    `destruct`, whereas [NewVarC k] is a *function* and this needs the full
    structural induction, matching [NewVarC]'s own shape.

    Explicit `destruct` patterns on **both** arguments are what keeps it
    short: the 7×7 (and 5×5) off-diagonal cases all fall to
    `try discriminate`, leaving one goal per constructor. *)

Lemma subst_NewVarC_inv : forall R j v k s,
  subst_in_proc j v R = NewVarC k s ->
  exists S, R = NewVarC k S /\ s = subst_in_proc j v S
with subst_gNewVarC_inv : forall M j v k N,
  subst_in_gproc j v M = gNewVarC k N ->
  exists S, M = gNewVarC k S /\ N = subst_in_gproc j v S.
Proof.
  - destruct R as [Ra Rb|xa|xa Ra|Ea Ra Rb|ca wa|Ra|Ma];
    destruct s as [sa sb|xb|xb sa|Eb sa sb|cb wb|sa|Mb];
    intros H; simpl in H; try discriminate H.
    + inversion H; subst.
      destruct (subst_NewVarC_inv Ra j v k sa H1) as (S1 & EA & EB).
      destruct (subst_NewVarC_inv Rb j v k sb H2) as (S2 & EC & ED).
      exists (S1 ‖ S2). subst. split; reflexivity.
    + inversion H; subst. exists (pr_var xb). split; reflexivity.
    + inversion H; subst.
      destruct (subst_NewVarC_inv Ra j v k sa H2) as (S1 & EA & EB).
      exists (rec xb • S1). subst. split; reflexivity.
    + inversion H; subst.
      destruct (subst_NewVarC_inv Ra j v k sa H2) as (S1 & EA & EB).
      destruct (subst_NewVarC_inv Rb j v k sb H3) as (S2 & EC & ED).
      exists (If Ea Then S1 Else S2). subst. split; reflexivity.
    + inversion H; subst. exists (cb ! wa • 𝟘). split; reflexivity.
    + inversion H; subst.
      destruct (subst_NewVarC_inv Ra j v (S k) sa H1) as (S1 & EA & EB).
      exists (ν S1). subst. split; reflexivity.
    + inversion H; subst.
      destruct (subst_gNewVarC_inv Ma j v k Mb H1) as (S1 & EA & EB).
      exists (VACCS.g S1). subst. split; reflexivity.
  - destruct M as [ | | ca Ma | Ma | Ma Mb ];
    destruct N as [ | | cb Na | Na | Na Nb ];
    intros H; simpl in H; try discriminate H.
    + exists ①. split; reflexivity.
    + exists 𝟘. split; reflexivity.
    + inversion H; subst.
      destruct (subst_NewVarC_inv Ma (S j) (Succ_bvar v) k Na H2) as (S1 & EA & EB).
      exists (cb ? S1). subst. split; reflexivity.
    + inversion H; subst.
      destruct (subst_NewVarC_inv Ma j v k Na H1) as (S1 & EA & EB).
      exists (𝛕 • S1). subst. split; reflexivity.
    + inversion H; subst.
      destruct (subst_gNewVarC_inv Ma j v k Na H1) as (S1 & EA & EB).
      destruct (subst_gNewVarC_inv Mb j v k Nb H2) as (S2 & EC & ED).
      exists (S1 + S2). subst. split; reflexivity.
Qed.

(** The channel shift is injective — needed to turn
    [lts_NewVarC_inv]'s per-value witness into the *given* family: the
    inversion returns some [q0_v] with [NewVarC 0 (S^v) = NewVarC 0 q0_v],
    and only injectivity makes that [q0_v = S^v]. *)

Lemma NewVarC_inj : forall a b k, NewVarC k a = NewVarC k b -> a = b
with gNewVarC_inj : forall A B k, gNewVarC k A = gNewVarC k B -> A = B.
Proof.
  - destruct a as [Ra Rb|xa|xa Ra|Ea Ra Rb|ca wa|Ra|Ma];
    destruct b as [sa sb|xb|xb sa|Eb sa sb|cb wb|sa|Mb];
    intros k H; simpl in H; try discriminate H.
    + inversion H. f_equal; eapply NewVarC_inj; eassumption.
    + inversion H. reflexivity.
    + inversion H. f_equal. eapply NewVarC_inj; eassumption.
    + inversion H. f_equal; eapply NewVarC_inj; eassumption.
    + inversion H. f_equal. eapply NewVar_in_ChannelData_inj. eassumption.
    + inversion H. f_equal. eapply NewVarC_inj; eassumption.
    + inversion H. f_equal. eapply gNewVarC_inj; eassumption.
  - destruct A as [ | | ca Ma | Ma | Ma Mb ];
    destruct B as [ | | cb Na | Na | Na Nb ];
    intros k H; simpl in H; try discriminate H.
    + reflexivity.
    + reflexivity.
    + inversion H. f_equal;
        [ eapply NewVar_in_ChannelData_inj; eassumption
        | eapply NewVarC_inj; eassumption ].
    + inversion H. f_equal. eapply NewVarC_inj; eassumption.
    + inversion H. f_equal; eapply gNewVarC_inj; eassumption.
Qed.

(** Scope extrusion dominates uniformly.  This is the last of the six
    congruence sites [normal_form_strong] goes through.  Both cases follow
    the [dom_u_par] recipe — invert the open family with
    [subst_par_inv]/[subst_res_inv], rule out a value-dependent choice of
    branch with [size_subst] + [Static_lts_decrease], rebuild the family and
    discharge the two [ax_pre] obligations with [cgr_res_scope].  The [parR]
    case is the one with content: the moving operand is the *shifted* one, so
    the family has to be pulled back through [NewVarC 0] — [subst_NewVarC_inv]
    writes it as [NewVarC 0 T] for an open [T], [subst_NewVarC] moves the
    substitution past the shift, and [NewVarC_inj] identifies the per-value
    witnesses [lts_NewVarC_inv] returns with [T ^ v]. *)
Lemma dom_u_res_scope : forall p q, Static p -> Static q ->
  dom_u ((ν p) ‖ q) (ν (p ‖ (NewVarC 0 q))).
Proof.
  intros p q HSp HSq.
  split; [ apply dom_cgr; apply cgr_res_scope_rev | ].
  intros c R HR.
  assert (H0 := HR (cst O)). inversion H0; subst.
  destruct (subst_res_inv R (cst O) p' (eq_sym H2)) as (R0 & ER & E0). subst R.
  simpl in H3. inversion H3; subst.
  - (* the unrestricted operand moves *)
    destruct (subst_par_inv R0 (cst O) p2 (NewVarC 0 q) (eq_sym H5))
      as (R01 & R02 & ER0 & E1 & E2).
    subst R0.
    assert (HQ : forall v, lts p (ActExt (ActIn (VarC_add 1 c, v))) (subst_in_proc 0 v R01)
                        /\ subst_in_proc 0 v R02 = NewVarC 0 q).
    { intro v. assert (Hv := HR v). simpl in Hv. inversion Hv; subst.
      match goal with HH : lts (p ‖ NewVarC 0 q) _ _ |- _ =>
        simpl in HH; inversion HH; subst end.
      - split; [ assumption | reflexivity ].
      - exfalso.
        assert (Hsz : (size (subst_in_proc 0 (cst O) R01) < size (subst_in_proc 0 v R01))%nat)
          by (eapply Static_lts_decrease; [ exact HSp | exact H6 ]).
        rewrite !size_subst in Hsz. lia. }
    exists ((ν R01) ‖ NewVar 0 q). split.
    + intro v. simpl. rewrite NewVar_subst_cancel.
      apply lts_parL. apply lts_res_ext. apply (proj1 (HQ v)).
    + split; intro v; simpl; rewrite NewVar_subst_cancel; rewrite (proj2 (HQ v));
        [ apply ax_cgr | apply ax_cgr_sym ]; apply cgr_res_scope.
  - (* the shifted operand moves *)
    destruct (subst_par_inv R0 (cst O) p q2 (eq_sym H5))
      as (R01 & R02 & ER0 & E1 & E2).
    subst R0.
    assert (HQ : forall v, lts (NewVarC 0 q) (ActExt (ActIn (VarC_add 1 c, v)))
                                             (subst_in_proc 0 v R02)
                        /\ subst_in_proc 0 v R01 = p).
    { intro v. assert (Hv := HR v). simpl in Hv. inversion Hv; subst.
      match goal with HH : lts _ (ActExt (VarC_action_add 1 (ActIn (c ▷ v)))) _ |- _ =>
        simpl in HH; inversion HH; subst end.
      - exfalso.
        match goal with HH : lts (R01 ^ cst O) _ (R01 ^ v) |- _ =>
          assert (Hsz : (size (subst_in_proc 0 v R01)
                         < size (subst_in_proc 0 (cst O) R01))%nat)
            by (eapply Static_lts_decrease; [ exact HSp | exact HH ]) end.
        rewrite !size_subst in Hsz. lia.
      - split; [ assumption | reflexivity ]. }
    destruct (lts_NewVarC_inv q 0 _ _ (proj1 (HQ (cst O)))) as (a0 & q0 & Ea & Eq & Hlq).
    destruct (subst_NewVarC_inv R02 0 (cst O) 0 q0 Eq) as (T & ET & ET2).
    assert (HT : forall v, lts q (ActExt (ActIn (c, v))) (subst_in_proc 0 v T)).
    { intro v. assert (Hv := proj1 (HQ v)).
      rewrite ET in Hv. rewrite subst_NewVarC in Hv.
      destruct (lts_NewVarC_inv q 0 _ _ Hv) as (b0 & r0 & Eb & Er & Hlr).
      assert (Er' : subst_in_proc 0 v T = r0) by (eapply NewVarC_inj; exact Er).
      rewrite Er'. destruct b0 as [[[c0 v0]|[c0 v0]]|]; simpl in Eb; try discriminate Eb.
      inversion Eb; subst.
      assert (Ec : c = c0).
      { eapply NewVar_in_ChannelData_inj with (k := 0).
        rewrite !NewVarC_at_zero. assumption. }
      subst c0. exact Hlr. }
    exists ((NewVar 0 (ν p)) ‖ T). split.
    + intro v. simpl. rewrite NewVar_subst_cancel. apply lts_parR. apply HT.
    + split; intro v; simpl; rewrite NewVar_subst_cancel;
        rewrite (proj2 (HQ v)); rewrite ET; rewrite subst_NewVarC;
        [ apply ax_cgr | apply ax_cgr_sym ]; apply cgr_res_scope.
Qed.

(** Associativity of [‖].  Three branches — the moving leaf is [p], [q] or
    [r] — each closed by the same recipe as [dom_u_par]: invert the open
    family, rule out a value-dependent choice of branch by [size_subst] +
    [Static_lts_decrease], rebuild.  The two untouched leaves are shifted out
    of the binder's way with [NewVar] and put back by
    [NewVar_subst_cancel]. *)
Lemma dom_u_par_assoc : forall p q r, Static p -> Static q -> Static r ->
  dom_u ((p ‖ q) ‖ r) (p ‖ (q ‖ r)).
Proof.
  intros p q r HSp HSq HSr.
  split; [ apply dom_cgr; apply cgr_par_assoc | ].
  intros c R HR.
  assert (H0 := HR (cst O)). inversion H0; subst.
  - (* the leftmost leaf moves *)
    destruct (subst_par_inv R (cst O) p2 (q ‖ r) (eq_sym H4)) as (R1 & R2 & ER & E1 & E2).
    subst R.
    assert (HQ : forall v, lts p (ActExt (ActIn (c,v))) (subst_in_proc 0 v R1)
                        /\ subst_in_proc 0 v R2 = q ‖ r).
    { intro v. assert (Hv := HR v). simpl in Hv. inversion Hv; subst.
      - split; [ assumption | reflexivity ].
      - exfalso.
        match goal with HH : lts _ ((c ▷ cst O) ?) (R1 ^ cst O) |- _ =>
          assert (Hsz : (size (subst_in_proc 0 (cst O) R1)
                         < size (subst_in_proc 0 v R1))%nat)
            by (eapply Static_lts_decrease; [ exact HSp | exact HH ]) end.
        rewrite !size_subst in Hsz. lia. }
    exists ((R1 ‖ NewVar 0 q) ‖ NewVar 0 r). split.
    + intro v. simpl. rewrite !NewVar_subst_cancel.
      apply lts_parL. apply lts_parL. apply (proj1 (HQ v)).
    + split; intro v; simpl; rewrite !NewVar_subst_cancel; rewrite (proj2 (HQ v));
        [ apply ax_cgr; apply cgr_par_assoc_rev | apply ax_cgr; apply cgr_par_assoc ].
  - destruct (subst_par_inv R (cst O) p q2 (eq_sym H4)) as (R1 & R2 & ER & E1 & E2).
    subst R.
    assert (HQ : forall v, lts (q ‖ r) (ActExt (ActIn (c,v))) (subst_in_proc 0 v R2)
                        /\ subst_in_proc 0 v R1 = subst_in_proc 0 (cst O) R1).
    { intro v. assert (Hv := HR v). simpl in Hv. inversion Hv; subst.
      - exfalso.
        match goal with HH : lts _ ((c ▷ v) ?) (R1 ^ v) |- _ =>
          assert (Hsz : (size (subst_in_proc 0 v R1)
                         < size (subst_in_proc 0 (cst O) R1))%nat)
            by (eapply Static_lts_decrease; [ exact HSp | exact HH ]) end.
        rewrite !size_subst in Hsz. lia.
      - split; [ assumption | symmetry; assumption ]. }
    assert (HQ2 := proj1 (HQ (cst O))). simpl in HQ2. inversion HQ2; subst.
    + (* the middle leaf moves *)
      destruct (subst_par_inv R2 (cst O) p2 r (eq_sym H6)) as (R21 & R22 & ER2 & E21 & E22).
      subst R2.
      assert (HW : forall v, lts q (ActExt (ActIn (c,v))) (subst_in_proc 0 v R21)
                          /\ subst_in_proc 0 v R22 = r).
      { intro v. assert (Hv := proj1 (HQ v)). simpl in Hv. inversion Hv; subst.
        - split; [ assumption | reflexivity ].
        - exfalso.
          match goal with HH : lts _ ((c ▷ cst O) ?) (R21 ^ cst O) |- _ =>
            assert (Hsz : (size (subst_in_proc 0 (cst O) R21)
                           < size (subst_in_proc 0 v R21))%nat)
              by (eapply Static_lts_decrease; [ exact HSq | exact HH ]) end.
          rewrite !size_subst in Hsz. lia. }
      exists ((NewVar 0 (subst_in_proc 0 (cst O) R1) ‖ R21) ‖ NewVar 0 r). split.
      * intro v. simpl. rewrite !NewVar_subst_cancel.
        apply lts_parL. apply lts_parR. apply (proj1 (HW v)).
      * split; intro v; simpl; rewrite !NewVar_subst_cancel;
          rewrite (proj2 (HQ v)); rewrite (proj2 (HW v));
          [ apply ax_cgr; apply cgr_par_assoc_rev | apply ax_cgr; apply cgr_par_assoc ].
    + (* the rightmost leaf moves *)
      destruct (subst_par_inv R2 (cst O) q q0 (eq_sym H6)) as (R21 & R22 & ER2 & E21 & E22).
      subst R2.
      assert (HW : forall v, lts r (ActExt (ActIn (c,v))) (subst_in_proc 0 v R22)
                          /\ subst_in_proc 0 v R21 = subst_in_proc 0 (cst O) R21).
      { intro v. assert (Hv := proj1 (HQ v)). simpl in Hv. inversion Hv; subst.
        - exfalso.
          match goal with HH : lts _ ((c ▷ v) ?) (R21 ^ v) |- _ =>
            assert (Hsz : (size (subst_in_proc 0 v R21)
                           < size (subst_in_proc 0 (cst O) R21))%nat)
              by (eapply Static_lts_decrease; [ exact HSq | exact HH ]) end.
          rewrite !size_subst in Hsz. lia.
        - split; [ assumption | symmetry; assumption ]. }
      exists ((NewVar 0 (subst_in_proc 0 (cst O) R1)
               ‖ NewVar 0 (subst_in_proc 0 (cst O) R21)) ‖ R22). split.
      * intro v. simpl. rewrite !NewVar_subst_cancel. rewrite <- E21.
        apply lts_parR. apply (proj1 (HW v)).
      * split; intro v; simpl; rewrite !NewVar_subst_cancel;
          rewrite (proj2 (HQ v)); rewrite (proj2 (HW v));
          [ apply ax_cgr; apply cgr_par_assoc_rev | apply ax_cgr; apply cgr_par_assoc ].
Qed.

(** The other direction costs nothing: commutativity turns a right-nested
    product into a left-nested one in five top-level steps, using only
    [dom_u_par_com] and [dom_u_par_assoc]. *)
Lemma dom_u_par_assoc_rev : forall p q r, Static p -> Static q -> Static r ->
  dom_u (p ‖ (q ‖ r)) ((p ‖ q) ‖ r).
Proof.
  intros p q r HSp HSq HSr.
  eapply dom_u_trans; [ apply dom_u_par_com; [ exact HSp | constructor; assumption ] | ].
  eapply dom_u_trans; [ apply dom_u_par_assoc; assumption | ].
  eapply dom_u_trans; [ apply dom_u_par_com; [ exact HSq | constructor; assumption ] | ].
  eapply dom_u_trans; [ apply dom_u_par_assoc; assumption | ].
  apply dom_u_par_com; [ exact HSr | constructor; assumption ].
Qed.

(** The [n]-fold versions, mirroring [cgr_res_n] and [cgr_res_scope_n]. *)
Lemma Static_res_n : forall n P, Static P -> Static (Ѵ n P).
Proof. induction n; intros P HP; simpl; [ exact HP | constructor; apply IHn; exact HP ]. Qed.

Lemma dom_u_res_n : forall n P Q, dom_u P Q -> dom_u (Ѵ n P) (Ѵ n Q).
Proof.
  induction n; intros P Q H; simpl; [ exact H | apply dom_u_res; apply IHn; exact H ].
Qed.

Lemma dom_u_res_scope_n : forall n P Q, Static P -> Static Q ->
  dom_u ((Ѵ n P) ‖ Q) (Ѵ n (P ‖ NewVarCn 0 n Q)).
Proof.
  induction n; intros P Q HP HQ; simpl.
  - apply dom_u_refl.
  - eapply dom_u_trans;
      [ apply dom_u_res_scope; [ apply Static_res_n; exact HP | exact HQ ] | ].
    apply dom_u_res. rewrite <- NewVarCn_revert_def.
    apply IHn; [ exact HP | apply Static_NewVarC; exact HQ ].
Qed.

Lemma Static_NewVarCn : forall k n P, Static P -> Static (NewVarCn k n P).
Proof.
  induction n; intros P HP; simpl; [ exact HP | apply Static_NewVarC; apply IHn; exact HP ].
Qed.

(** The scope-extrusion chain of [NF_par_step], re-run at [dom_u].  Every link
    is one of the combinators above; the [rewrite]s are definitional
    equalities and so cost nothing. *)
Lemma dom_u_NF_par_step : forall n1 l1 M1 n2 l2 M2, gStatic M1 -> gStatic M2 ->
  dom_u (NF n1 l1 M1 ‖ NF n2 l2 M2)
        (Ѵ (n1 + n2) ((msgs (map (shiftCn n2 n1) l2) ‖ msgs (map (shiftCn 0 n2) l1))
                      ‖ (g (gNewVarCn n2 n1 M2) ‖ g (gNewVarCn 0 n2 M1)))).
Proof.
  intros n1 l1 M1 n2 l2 M2 HM1 HM2. unfold NF.
  assert (S1 : Static (msgs l1 ‖ g M1))
    by (constructor; [ apply msgs_Static | constructor; assumption ]).
  assert (S2 : Static (msgs l2 ‖ g M2))
    by (constructor; [ apply msgs_Static | constructor; assumption ]).
  eapply dom_u_trans;
    [ apply dom_u_res_scope_n; [ exact S1 | apply Static_res_n; exact S2 ] | ].
  rewrite BigNew_add. apply dom_u_res_n.
  rewrite (NewVarCn_res 0 n1 n2). simpl.
  eapply dom_u_trans;
    [ apply dom_u_par_com;
      [ exact S1 | apply Static_res_n; apply Static_NewVarCn; exact S2 ] | ].
  eapply dom_u_trans;
    [ apply dom_u_res_scope_n; [ apply Static_NewVarCn; exact S2 | exact S1 ] | ].
  apply dom_u_res_n.
  rewrite !NewVarCn_par, !NewVarCn_msgs, !NewVarCn_g.
  assert (SA : Static (msgs (map (shiftCn n2 n1) l2))) by apply msgs_Static.
  assert (SC : Static (msgs (map (shiftCn 0 n2) l1))) by apply msgs_Static.
  assert (SB : Static (g (gNewVarCn n2 n1 M2)))
    by (constructor; apply gStatic_gNewVarCn; exact HM2).
  assert (SD : Static (g (gNewVarCn 0 n2 M1)))
    by (constructor; apply gStatic_gNewVarCn; exact HM1).
  eapply dom_u_trans;
    [ apply dom_u_par_assoc; [ exact SA | exact SB | constructor; assumption ] | ].
  eapply dom_u_trans;
    [ | apply dom_u_par_assoc_rev; [ exact SA | exact SC | constructor; assumption ] ].
  apply dom_u_par; [ exact SA | constructor; [ exact SC | constructor; assumption ]
                   | apply dom_u_refl | ].
  eapply dom_u_trans;
    [ apply dom_u_par_assoc_rev; [ exact SB | exact SC | exact SD ] | ].
  eapply dom_u_trans;
    [ | apply dom_u_par_assoc; [ exact SC | exact SB | exact SD ] ].
  apply dom_u_par; [ constructor; assumption | exact SD
                   | apply dom_u_par_com; assumption | apply dom_u_refl ].
Qed.

Theorem normal_form_strong : forall p, Static p ->
  exists n l M, gStatic M /\ dom p (NF n l M).
Proof.
  intro p. induction p as [p IHp] using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intro Hs. destruct p as [p1 p2|x|x p0|E p1 p2|c v|p0|M].
  - inversion Hs; subst.
    destruct (IHp p1 ltac:(simpl; lia) H1) as (n1 & l1 & M1 & HM1 & Hd1).
    destruct (IHp p2 ltac:(simpl; lia) H2) as (n2 & l2 & M2 & HM2 & Hd2).
    set (N1 := gNewVarCn 0 n2 M1). set (N2 := gNewVarCn n2 n1 M2).
    set (L1 := map (shiftCn 0 n2) l1). set (L2 := map (shiftCn n2 n1) l2).
    exists ((n1 + n2)%nat), (L2 ++ L1), (ext N2 N1 + ext_r N1 N2).
    split.
    { subst N1 N2. constructor.
      - apply ext_gStatic; apply gStatic_gNewVarCn; assumption.
      - apply ext_r_gStatic; apply gStatic_gNewVarCn; assumption. }
    eapply dom_trans; [ apply dom_par; [exact Hd1 | exact Hd2] | ].
    eapply dom_trans; [ apply dom_cgr; apply NF_par_step | ].
    unfold NF. apply dom_res_n.
    eapply dom_trans;
      [ apply dom_par; [ apply dom_cgr; symmetry; apply msgs_app | apply dom_refl ] | ].
    apply dom_par; [ apply dom_refl | apply dom_expansion ].
  - inversion Hs.
  - inversion Hs.
  - destruct (Eval_Eq 0 E) as [[|]|] eqn:HE;
      [ | | exfalso; eapply Eval_Eq_0_not_none; exact HE ].
    + inversion Hs; subst.
      destruct (IHp p1 ltac:(simpl; lia) H1) as (n & l & M & HM & Hd).
      exists n, l, M. split; [ exact HM | ].
      eapply dom_trans; [ apply dom_cgr; apply cgr_if_true; exact HE | exact Hd ].
    + inversion Hs; subst.
      destruct (IHp p2 ltac:(simpl; lia) H3) as (n & l & M & HM & Hd).
      exists n, l, M. split; [ exact HM | ].
      eapply dom_trans; [ apply dom_cgr; apply cgr_if_false; exact HE | exact Hd ].
  - exists 0, [(c,v)], 𝟘. split; [ constructor | ]. unfold NF. simpl.
    apply dom_cgr. etransitivity; [ apply cgr_par_nil_rev | ].
    apply cgr_fullpar; [ apply cgr_par_nil_rev | reflexivity ].
  - inversion Hs; subst.
    destruct (IHp p0 ltac:(simpl; lia) H0) as (n & l & M & HM & Hd).
    exists (S n), l, M. split; [ exact HM | ]. unfold NF in *. simpl. apply dom_res. exact Hd.
  - inversion Hs; subst.
    exists 0, [], M. split; [ assumption | ]. unfold NF. simpl.
    apply dom_cgr. etransitivity; [ apply cgr_par_nil_rev | apply cgr_par_com ].
Qed.

(** ** The normal form dominates UNIFORMLY

    [normal_form_strong] matches an input transition of the normal form
    per value; the omega rule [ax_input] consumes a single *open*
    continuation.  [normal_form_strong_u] closes that gap: every input
    transition of the normal form is matched by a whole uniform family of
    the original process, with [⊢]-equal members at every value.  This is
    what lets a matching argument descend into an input continuation
    without losing the binder. *)

Lemma Static_NF : forall n l M, gStatic M -> Static (NF n l M).
Proof.
  intros n l M HM. unfold NF. apply Static_res_n.
  constructor; [ apply msgs_Static | constructor; exact HM ].
Qed.

(** The two [If] cases are free: [lts_ifOne]/[lts_ifZero] carry a
    transition of the selected branch to the conditional with the *same*
    target, so the given family is its own witness. *)
Lemma dom_u_if_true : forall E p1 p2, Eval_Eq 0 E = Some true ->
  dom_u (If E Then p1 Else p2) p1.
Proof.
  intros E p1 p2 HE. split; [ apply dom_cgr; apply cgr_if_true; exact HE | ].
  intros c R HR. exists R. split; [ | split; intro v; apply ax_refl ].
  intro v. eapply lts_ifOne; [ exact HE | apply HR ].
Qed.

Lemma dom_u_if_false : forall E p1 p2, Eval_Eq 0 E = Some false ->
  dom_u (If E Then p1 Else p2) p2.
Proof.
  intros E p1 p2 HE. split; [ apply dom_cgr; apply cgr_if_false; exact HE | ].
  intros c R HR. exists R. split; [ | split; intro v; apply ax_refl ].
  intro v. eapply lts_ifZero; [ exact HE | apply HR ].
Qed.

(** A message's normal form has no input transition at all, so its
    [sd_u] obligation is vacuous. *)
Lemma msg_NF_no_input : forall c v cc w r,
  ~ lts (NF 0 [(c,v)] 𝟘) (ActExt (ActIn (cc,w))) r.
Proof.
  intros c v cc w r H. unfold NF in H. simpl in H.
  inversion H; subst.
  - match goal with HH : lts _ _ _ |- _ => inversion HH; subst end;
      match goal with HH : lts _ _ _ |- _ => inversion HH end.
  - match goal with HH : lts (g 𝟘) _ _ |- _ => inversion HH end.
Qed.

Theorem normal_form_strong_u : forall p, Static p ->
  exists n l M, gStatic M /\ dom_u p (NF n l M).
Proof.
  intro p. induction p as [p IHp] using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intro Hs. destruct p as [p1 p2|x|x p0|E p1 p2|c v|p0|M].
  - inversion Hs; subst.
    destruct (IHp p1 ltac:(simpl; lia) H1) as (n1 & l1 & M1 & HM1 & Hd1).
    destruct (IHp p2 ltac:(simpl; lia) H2) as (n2 & l2 & M2 & HM2 & Hd2).
    set (N1 := gNewVarCn 0 n2 M1). set (N2 := gNewVarCn n2 n1 M2).
    set (L1 := map (shiftCn 0 n2) l1). set (L2 := map (shiftCn n2 n1) l2).
    assert (HN1 : gStatic N1) by (subst N1; apply gStatic_gNewVarCn; assumption).
    assert (HN2 : gStatic N2) by (subst N2; apply gStatic_gNewVarCn; assumption).
    exists ((n1 + n2)%nat), (L2 ++ L1), (ext N2 N1 + ext_r N1 N2).
    split.
    { constructor; [ apply ext_gStatic | apply ext_r_gStatic ]; assumption. }
    eapply dom_u_trans;
      [ apply dom_u_par;
        [ apply Static_NF; exact HM1 | apply Static_NF; exact HM2
        | exact Hd1 | exact Hd2 ] | ].
    eapply dom_u_trans; [ apply dom_u_NF_par_step; assumption | ].
    unfold NF. apply dom_u_res_n.
    eapply dom_u_trans;
      [ apply (dom_u_par _ (msgs (L2 ++ L1)) _ (((g N2) : proc) ‖ ((g N1) : proc)));
        [ apply msgs_Static
        | constructor; constructor; assumption
        | apply dom_u_cgr_no_input;
          [ symmetry; apply msgs_app | apply msgs_no_input ]
        | apply dom_u_refl ] | ].
    apply dom_u_par;
      [ apply msgs_Static
      | constructor; constructor; [ apply ext_gStatic | apply ext_r_gStatic ]; assumption
      | apply dom_u_refl | apply dom_u_expansion ].
  - inversion Hs.
  - inversion Hs.
  - destruct (Eval_Eq 0 E) as [[|]|] eqn:HE;
      [ | | exfalso; eapply Eval_Eq_0_not_none; exact HE ].
    + inversion Hs; subst.
      destruct (IHp p1 ltac:(simpl; lia) H1) as (n & l & M & HM & Hd).
      exists n, l, M. split; [ exact HM | ].
      eapply dom_u_trans; [ apply dom_u_if_true; exact HE | exact Hd ].
    + inversion Hs; subst.
      destruct (IHp p2 ltac:(simpl; lia) H3) as (n & l & M & HM & Hd).
      exists n, l, M. split; [ exact HM | ].
      eapply dom_u_trans; [ apply dom_u_if_false; exact HE | exact Hd ].
  - exists 0, [(c,v)], 𝟘. split; [ constructor | ].
    apply dom_u_cgr_no_input; [ | apply msg_NF_no_input ].
    unfold NF. simpl. etransitivity; [ apply cgr_par_nil_rev | ].
    apply cgr_fullpar; [ apply cgr_par_nil_rev | reflexivity ].
  - inversion Hs; subst.
    destruct (IHp p0 ltac:(simpl; lia) H0) as (n & l & M & HM & Hd).
    exists (S n), l, M. split; [ exact HM | ]. unfold NF in *. simpl.
    apply dom_u_res. exact Hd.
  - inversion Hs; subst.
    exists 0, [], M. split; [ assumption | ]. unfold NF. simpl.
    apply dom_u_nil_par.
Qed.

(** ** Value substitution commutes with the value-binder shift

    The standard de Bruijn commutation, missing from the development until
    now and needed by anything that normalises an *open* term (in
    particular by a normal form whose input continuations are themselves
    normal forms).  Both [subst_in_proc] and [NewVar] bump their index
    under an input guard, and [subst_in_proc] also bumps the value it
    substitutes — [NewVar_in_Data_Succ] is exactly the compatibility that
    makes the two bumps agree. *)

Lemma NewVar_in_Data_Succ : forall j X,
  NewVar_in_Data (S j) (Succ_bvar X) = Succ_bvar (NewVar_in_Data j X).
Proof.
  intros j [a|i]; simpl; [ reflexivity | ].
  destruct (decide (S j < S (S i))); destruct (decide (j < S i));
    simpl; try reflexivity; exfalso; lia.
Qed.

Lemma subst_NewVar_Data : forall j k X Y, (j <= k)%nat ->
  subst_Data (S k) (NewVar_in_Data j X) (NewVar_in_Data j Y)
  = NewVar_in_Data j (subst_Data k X Y).
Proof.
  intros j k X [a|i] Hjk; simpl; [ reflexivity | ].
  destruct (decide (j < S i)) as [Hji|Hji]; simpl.
  - destruct (decide (S i = S k)) as [E1|E1]; destruct (decide (i = k)) as [E2|E2];
      simpl; try (exfalso; lia); [ reflexivity | ].
    destruct (decide (S i < S k)) as [E3|E3]; destruct (decide (i < k)) as [E4|E4];
      simpl; try (exfalso; lia).
    + destruct (decide (j < S i)); simpl; [ reflexivity | exfalso; lia ].
    + destruct (decide (j < S (Nat.pred i))); simpl; [ | exfalso; lia ].
      destruct i; [ exfalso; lia | simpl; reflexivity ].
  - destruct (decide (i = S k)) as [E1|E1]; [ exfalso; lia | ].
    destruct (decide (i < S k)) as [E2|E2]; [ | exfalso; lia ]. simpl.
    destruct (decide (i = k)) as [E3|E3]; [ exfalso; lia | ].
    destruct (decide (i < k)) as [E4|E4]; [ | exfalso; lia ]. simpl.
    destruct (decide (j < S i)); [ exfalso; lia | reflexivity ].
Qed.

Lemma subst_NewVar : forall p j k X, (j <= k)%nat ->
  subst_in_proc (S k) (NewVar_in_Data j X) (NewVar j p) = NewVar j (subst_in_proc k X p)
with subst_gNewVar : forall M j k X, (j <= k)%nat ->
  subst_in_gproc (S k) (NewVar_in_Data j X) (gNewVar j M) = gNewVar j (subst_in_gproc k X M).
Proof.
  - destruct p as [p1 p2|x|x p0|E p1 p2|c w|p0|M]; intros j k X Hjk; simpl.
    + f_equal; apply subst_NewVar; exact Hjk.
    + reflexivity.
    + f_equal; apply subst_NewVar; exact Hjk.
    + destruct E as [D1 D2]. simpl. f_equal;
        [ f_equal; apply subst_NewVar_Data; exact Hjk
        | apply subst_NewVar; exact Hjk | apply subst_NewVar; exact Hjk ].
    + f_equal. apply subst_NewVar_Data. exact Hjk.
    + f_equal. apply subst_NewVar. exact Hjk.
    + f_equal. apply subst_gNewVar. exact Hjk.
  - destruct M as [ | |c p0|p0|M1 M2]; intros j k X Hjk; simpl.
    + reflexivity.
    + reflexivity.
    + f_equal. rewrite <- NewVar_in_Data_Succ. apply subst_NewVar. lia.
    + f_equal. apply subst_NewVar. exact Hjk.
    + f_equal; apply subst_gNewVar; exact Hjk.
Qed.

Lemma NewVar_in_Data_zero : forall X, NewVar_in_Data 0 X = Succ_bvar X.
Proof.
  intros [a|i]; simpl; [ reflexivity | ].
  destruct (decide (0 < S i)); [ reflexivity | exfalso; lia ].
Qed.

(** The instance the expansion law's [gNewVar 0] needs. *)
Corollary subst_NewVar_0 : forall p k X,
  subst_in_proc (S k) (Succ_bvar X) (NewVar 0 p) = NewVar 0 (subst_in_proc k X p).
Proof. intros p k X. rewrite <- NewVar_in_Data_zero. apply subst_NewVar. lia. Qed.

(** A message bag under substitution is the bag of substituted messages. *)
Definition substl (k : nat) (X : ValueData) (l : list (ChannelData * ValueData))
  : list (ChannelData * ValueData) := map (fun cv => (fst cv, subst_Data k X (snd cv))) l.

Lemma subst_msgs : forall l k X, subst_in_proc k X (msgs l) = msgs (substl k X l).
Proof.
  induction l as [|cv l IH]; intros k X; simpl; [ reflexivity | ].
  f_equal. apply IH.
Qed.

Lemma subst_res_n : forall n j X p,
  subst_in_proc j X (Ѵ n p) = Ѵ n (subst_in_proc j X p).
Proof. induction n; intros j X p; simpl; [ reflexivity | f_equal; apply IHn ]. Qed.

(** ** …and with every construction the normal form is built from

    So the normal-form *shape* is substitution-equivariant: instantiating an
    open term's normal form is the normal form of the instantiated term, as
    far as the syntax is concerned.  This is the base infrastructure for an
    open re-run of [normal_form_strong_u] — whose induction is on [size p],
    itself substitution-invariant by [size_subst], so the recursion carries
    over unchanged. *)

Corollary subst_gNewVar_0 : forall M k X,
  subst_in_gproc (S k) (Succ_bvar X) (gNewVar 0 M) = gNewVar 0 (subst_in_gproc k X M).
Proof. intros M k X. rewrite <- NewVar_in_Data_zero. apply subst_gNewVar. lia. Qed.

Lemma subst_ext : forall M N k X,
  subst_in_gproc k X (ext M N) = ext (subst_in_gproc k X M) (subst_in_gproc k X N).
Proof.
  induction M as [ | |c p0|p0|M1 IH1 M2 IH2]; intros N k X; simpl;
    [ reflexivity | reflexivity | | reflexivity | f_equal; auto ].
  f_equal. simpl. f_equal. f_equal. apply subst_gNewVar_0.
Qed.

Lemma subst_ext_r : forall N M k X,
  subst_in_gproc k X (ext_r N M) = ext_r (subst_in_gproc k X N) (subst_in_gproc k X M).
Proof.
  induction N as [ | |c q0|q0|N1 IH1 N2 IH2]; intros M k X; simpl;
    [ reflexivity | reflexivity | | reflexivity | f_equal; auto ].
  f_equal. simpl. f_equal. f_equal. apply subst_gNewVar_0.
Qed.

(** [resg] dispatches on a *channel*, which a value substitution never
    touches — so the two commute with no side condition at all. *)
Lemma subst_resg : forall M k X,
  subst_in_gproc k X (resg M) = resg (subst_in_gproc k X M).
Proof.
  induction M as [ | |c p0|p0|M1 IH1 M2 IH2]; intros k X; simpl;
    [ reflexivity | reflexivity | | reflexivity | f_equal; auto ].
  destruct c as [a|[|j]]; simpl; reflexivity.
Qed.

Lemma subst_NewVarCn : forall n i j X p,
  subst_in_proc j X (NewVarCn i n p) = NewVarCn i n (subst_in_proc j X p).
Proof.
  induction n; intros i j X p; simpl; [ reflexivity | ].
  rewrite subst_NewVarC. f_equal. apply IHn.
Qed.

Lemma subst_gNewVarCn : forall n i j X M,
  subst_in_gproc j X (gNewVarCn i n M) = gNewVarCn i n (subst_in_gproc j X M).
Proof.
  induction n; intros i j X M; simpl; [ reflexivity | ].
  rewrite subst_gNewVarC. f_equal. apply IHn.
Qed.

(** The channel shift touches a message's channel, the substitution its
    value, so they pass through each other untouched. *)
Lemma substl_shiftCn : forall l i n k X,
  substl k X (map (shiftCn i n) l) = map (shiftCn i n) (substl k X l).
Proof.
  intros l i n k X. unfold substl, shiftCn.
  rewrite !map_map. apply map_ext. intros [c w]. reflexivity.
Qed.

Lemma subst_NF : forall n l M k X,
  subst_in_proc k X (NF n l M) = NF n (substl k X l) (subst_in_gproc k X M).
Proof.
  intros n l M k X. unfold NF. rewrite subst_res_n. simpl. rewrite subst_msgs.
  reflexivity.
Qed.

(** ** …but NORMALISATION itself is not substitution-equivariant

    The commutations above cover every construction the normal form is
    *built* from, so one is tempted to conclude that an open term has an
    open normal form — i.e. that there are open [n], [l], [M] with
    [NF n (substl 0 v l) (M ^ v)] a normal form of [p ^ v] at **every**
    value.  **That is false**, and the obstruction is [If].

    [normal_form] chooses a branch by computing [Eval_Eq 0 E], and that
    computation is not stable under substitution: an equation comparing a
    *bound* value variable with a constant evaluates to [Some false] while
    it is still open (the [n <= i] guard in [Eval_Eq] fires at [n = 0]),
    and to [Some true] once the matching constant is substituted in.  So
    the two instances of one open term normalise through **different
    branches**, and no single open [(n, l, M)] can serve both. *)

Lemma if_open_branch_depends_on_value : forall (a b : Value) (P1 P2 : proc),
  a <> b ->
  subst_in_proc 0 (cst a) (If (Equality (bvar 0) (cst a)) Then P1 Else P2)
    ≡* subst_in_proc 0 (cst a) P1
  /\ subst_in_proc 0 (cst b) (If (Equality (bvar 0) (cst a)) Then P1 Else P2)
    ≡* subst_in_proc 0 (cst b) P2.
Proof.
  intros a b P1 P2 Hab. split; simpl.
  - apply cgr_if_true. simpl.
    destruct (decide (0 = 0)) as [_|E]; [ | exfalso; congruence ].
    simpl. destruct (decide (a = a)); [ reflexivity | exfalso; congruence ].
  - apply cgr_if_false. simpl.
    destruct (decide (0 = 0)) as [_|E]; [ | exfalso; congruence ].
    simpl. destruct (decide (b = a)); [ exfalso; congruence | reflexivity ].
Qed.

(** ** Padding the restriction block

    Two processes normalise to blocks of *different* depth, and every
    configuration-level statement compares two normal forms at the **same**
    [Ѵⁿ (msgs l ‖ ·)].  Matching the bags is [bags_agree]; matching the
    depths is padding, and padding is available:

    a vacuous restriction can always be added, because
    [ν (NewVarC 0 q) ≡* q] — which is not a rule of [Congruence.v] but
    follows from scope extrusion with [𝟘] on the inside
    ([cgr_res_scope] at [p := 𝟘], then [cgr_res_nil]).

    The padded form is again an [NF]: the shift distributes over the
    message bag and the sum by [NewVarCn_msgs] and [NewVarCn_g]. *)

Lemma cgr_res_newvarc : forall q, ν (NewVarC 0 q) ≡* q.
Proof.
  intro q.
  etransitivity;
    [ apply cgr_res; etransitivity;
      [ apply cgr_par_nil_rev | apply cgr_par_com ] | ].
  etransitivity; [ apply cgr_res_scope | ].
  etransitivity; [ apply cgr_fullpar; [ apply cgr_res_nil | reflexivity ] | ].
  etransitivity; [ apply cgr_par_com | apply cgr_par_nil ].
Qed.

Lemma res_pad : forall k X, Ѵ k (NewVarCn 0 k X) ≡* X.
Proof.
  induction k as [|k IH]; intro X; simpl; [ reflexivity | ].
  rewrite <- NewVarCn_revert_def.
  etransitivity; [ apply cgr_res; apply IH | apply cgr_res_newvarc ].
Qed.

Lemma NF_pad : forall n k l M,
  NF ((n + k)%nat) (map (shiftCn 0 k) l) (gNewVarCn 0 k M) ≡* NF n l M.
Proof.
  intros n k l M. unfold NF. rewrite BigNew_add. apply cgr_res_n.
  rewrite <- NewVarCn_msgs. rewrite <- NewVarCn_g. rewrite <- NewVarCn_par.
  apply res_pad.
Qed.

Corollary ax_NF_pad_l : forall n k l M,
  ax_pre (NF n l M) (NF ((n + k)%nat) (map (shiftCn 0 k) l) (gNewVarCn 0 k M)).
Proof. intros. apply ax_cgr_sym. apply NF_pad. Qed.

Corollary ax_NF_pad_r : forall n k l M,
  ax_pre (NF ((n + k)%nat) (map (shiftCn 0 k) l) (gNewVarCn 0 k M)) (NF n l M).
Proof. intros. apply ax_cgr. apply NF_pad. Qed.


(** * THE ν-FREE NORMAL FORM, REACHED BY THE SIMULATION

    [normal_form_nores] gives [n = 0] — a **bare configuration** — and
    [normal_form_strong_sim] gives a [domsim]; neither gives both, and the
    outer recursion needs both: the first so that the configuration
    machinery applies, the second so that its recursive calls can be
    measured against the *original* process ([VACCS_Matching.DomOk]).

    The proof is [normal_form_nores]'s, with each [ax_trans] of a pair of
    [⊢]-facts replaced by one [domsim_trans] — the combinators
    ([domsim_cgr], [domsim_par], [domsim_expansion], [domsim_refl]) line
    up one for one with the rules the original used. *)

Theorem normal_form_nores_sim : forall p, Static p -> NoRes p ->
  exists l M, gStatic M /\ domsim p (msgs l ‖ ((g M) : proc)).
Proof.
  intro p. induction p as [p IHp] using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros Hs Hnr. destruct p as [p1 p2|x|x p0|E p1 p2|c v|p0|M].
  - inversion Hs; subst. destruct Hnr as (Hn1 & Hn2).
    destruct (IHp p1 ltac:(simpl; lia) H1 Hn1) as (l1 & M1 & HM1 & Hd1).
    destruct (IHp p2 ltac:(simpl; lia) H2 Hn2) as (l2 & M2 & HM2 & Hd2).
    exists (l1 ++ l2), (ext M1 M2 + ext_r M2 M1).
    split; [ constructor; [ apply ext_gStatic | apply ext_r_gStatic ]; assumption | ].
    assert (Hc : ((msgs l1 ‖ ((g M1) : proc)) ‖ (msgs l2 ‖ ((g M2) : proc)))
                 ≡* (msgs (l1 ++ l2) ‖ (((g M1) : proc) ‖ ((g M2) : proc)))).
    { etransitivity; [ apply cgr_par_exchange | ].
      apply cgr_fullpar; [ symmetry; apply msgs_app | reflexivity ]. }
    eapply domsim_trans; [ apply domsim_par; [ exact Hd1 | exact Hd2 ] | ].
    eapply domsim_trans; [ apply domsim_cgr; exact Hc | ].
    apply domsim_par; [ apply domsim_refl | apply domsim_expansion ].
  - inversion Hs.
  - inversion Hs.
  - destruct (Eval_Eq 0 E) as [[|]|] eqn:HE;
      [ | | exfalso; eapply Eval_Eq_0_not_none; exact HE ].
    + inversion Hs; subst. destruct Hnr as (Hn1 & Hn2).
      destruct (IHp p1 ltac:(simpl; lia) H1 Hn1) as (l & M & HM & Hd).
      exists l, M. split; [ exact HM | ].
      eapply domsim_trans; [ apply domsim_cgr; apply cgr_if_true; exact HE | exact Hd ].
    + inversion Hs; subst. destruct Hnr as (Hn1 & Hn2).
      destruct (IHp p2 ltac:(simpl; lia) H3 Hn2) as (l & M & HM & Hd).
      exists l, M. split; [ exact HM | ].
      eapply domsim_trans; [ apply domsim_cgr; apply cgr_if_false; exact HE | exact Hd ].
  - exists [(c,v)], 𝟘. split; [ constructor | ]. simpl.
    apply domsim_cgr. etransitivity; [ apply cgr_par_nil_rev | ].
    apply cgr_fullpar; [ apply cgr_par_nil_rev | reflexivity ].
  - simpl in Hnr. contradiction.
  - inversion Hs; subst. exists [], M. split; [ assumption | ]. simpl.
    apply domsim_cgr. etransitivity; [ apply cgr_par_nil_rev | apply cgr_par_com ].
Qed.

End VACCS_NormalForm.
