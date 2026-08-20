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

(** * What a forwarder state [p ▷ m] can actually do

    [VACCS_Must_Characterization.v] states every alternative
    characterisation of [⊑ₘᵤₛₜᵢ] at the forwarder, and
    [VACCS_ReadySet.v] shows why that is not a convenience: a bare
    process's abstracted ready set carries only its *outgoing* messages
    (a guarded sum's is empty), so the incoming half of the behaviour has
    to come from the buffer.  This file pins down exactly what the buffer
    contributes, by reading off [inter_lts fw_inter].

    **The [τ]-steps are: [p]'s own, and message delivery.**

        fw_tau_shape :  (p ▷ m) ⟶ x  ->
              (∃p', p ⟶ p' ∧ x = p' ▷ m)
            ∨ (∃a p' m', m = {[ActOut a]} ⊎ m' ∧ p ⟶[a?] p' ∧ x = p' ▷ m')

    with both shapes really being steps ([fw_tau_left], [fw_tau_deliver]),
    hence the stability criterion [fw_stable_iff]: a forwarder state is
    stable iff the process is stable **and** refuses every message the
    buffer is holding.

    **The visible steps are: [p]'s own, absorbing *any* input, and emitting
    a stored message.**

        fw_ext_shape :  (p ▷ m) ⟶[μ] x  ->
              (∃p', p ⟶[μ] p' ∧ x = p' ▷ m)
            ∨ (∃a, μ = a? ∧ x = p ▷ ({[ActOut a]} ⊎ m))
            ∨ (∃a m', μ = a! ∧ m = {[ActOut a]} ⊎ m' ∧ x = p ▷ m')

    The middle disjunct is the whole point, and [fw_input_always] states
    it on its own: **a forwarder state can perform any input at any time**,
    storing the corresponding message.  That is the buffer's
    [lts_multiset_add], and it is what makes the must-preorder of VACCS
    coarser than VCCS's — the process-level shadow of it being the copycat
    law [ax_ccat] ([VACCS_Copycat.v]).

    Everything is stated in terms of [inter_step] rather than the derived
    [↛] of the [toFW] instance, so that none of it depends on the
    refusal-decision machinery. *)

From Stdlib Require Import List Permutation PeanoNat Lia.
From stdpp Require Import base sets gmap gmultiset.
From TestingTheory Require Import VACCS VACCS_Instance Must ActTau InputOutputActions
  gLts Bisimulation InteractionBetweenLts Testing_Predicate VACCS_Good WeakTransitions
  Subset_Act DefinitionAS Convergence MultisetLTSConstruction ForwarderConstruction
  Lts_OBA Lts_FW Lts_OBA_FB VACCS_Static VACCS_Must_Characterization
  VACCS_Erasure VACCS_Precongruence VACCS_Expansion.

Section VACCS_Forwarder.

Context `{VP : VACCS_Parameters}.

(** ** The internal steps *)

Lemma fw_tau_shape : forall (p : proc) (m : MO (ExtAct TypeOfActions))
                            (x : proc * MO (ExtAct TypeOfActions)),
  (p ▷ m) ⟶ x ->
  (exists p', lts p τ p' /\ x = (p' ▷ m))
  \/ (exists a p' m', m = {[+ ActOut a +]} ⊎ m' /\ lts p (ActExt (ActIn a)) p' /\ x = (p' ▷ m')).
Proof.
  intros p m x H. inversion H; subst.
  - left. exists a2. split; [ exact l | reflexivity ].
  - inversion l.
  - right. destruct eq as (Hd & Hnb).
    destruct μ2 as [a|a]; simpl in Hnb, Hd.
    + exfalso. destruct Hnb as (b & Hb). discriminate Hb.
    + destruct μ1 as [b|b]; simpl in Hd; [ | exact (match Hd with end) ]. subst.
      inversion l2; subst.
      * exfalso. simpl in *. destruct nb as (z & Hz).
        rewrite Hz in duo. simpl in duo. exact duo.
      * exists a, a2, b2. split; [ reflexivity | split; [ exact l1 | reflexivity ] ].
Qed.

Lemma fw_tau_left : forall (p p' : proc) (m : MO (ExtAct TypeOfActions)),
  lts p τ p' -> (p ▷ m) ⟶ (p' ▷ m).
Proof. intros p p' m H. eapply ParLeft. exact H. Qed.

(** Delivery: the buffer emits a stored message and the process receives it. *)
Lemma fw_tau_deliver : forall (p p' : proc) a (m : MO (ExtAct TypeOfActions)),
  lts p (ActExt (ActIn a)) p' -> (p ▷ ({[+ ActOut a +]} ⊎ m)) ⟶ (p' ▷ m).
Proof.
  intros p p' a m H. eapply (ParSync (ActIn a) (ActOut a)).
  - split; [ simpl; reflexivity | simpl; eexists; reflexivity ].
  - exact H.
  - apply lts_multiset_minus. simpl. eexists; reflexivity.
Qed.

(** A forwarder state is stable iff the process is stable *and* refuses
    every message the buffer holds. *)
Lemma fw_stable_iff : forall (p : proc) (m : MO (ExtAct TypeOfActions)),
  (forall x, ~ ((p ▷ m) ⟶ x))
  <-> ((forall q, ~ lts p τ q)
       /\ (forall a, ActOut a ∈ m -> forall q, ~ lts p (ActExt (ActIn a)) q)).
Proof.
  intros p m. split.
  - intro H. split.
    + intros q Hq. eapply H. apply fw_tau_left. exact Hq.
    + intros a Ha q Hq.
      assert (m = {[+ ActOut a +]} ⊎ (m ∖ {[+ ActOut a +]})) as Heq by multiset_solver.
      apply (H (q ▷ (m ∖ {[+ ActOut a +]}))).
      rewrite Heq at 1. apply fw_tau_deliver. exact Hq.
  - intros (H1 & H2) x Hx.
    destruct (fw_tau_shape _ _ _ Hx) as [(p' & Hp' & _)|(a & p' & m' & Hm & Hp' & _)].
    + eapply H1. exact Hp'.
    + eapply H2; [ | exact Hp' ]. rewrite Hm. multiset_solver.
Qed.

(** ** The visible steps *)

Lemma fw_ext_shape : forall (p : proc) (m : MO (ExtAct TypeOfActions)) mu x,
  (p ▷ m) ⟶[mu] x ->
    (exists p', lts p (ActExt mu) p' /\ x = (p' ▷ m))
  \/ (exists a, mu = ActIn a /\ x = (p ▷ ({[+ ActOut a +]} ⊎ m)))
  \/ (exists a m', mu = ActOut a /\ m = {[+ ActOut a +]} ⊎ m' /\ x = (p ▷ m')).
Proof.
  intros p m mu x H. inversion H; subst.
  - left. exists a2. split; [ exact l | reflexivity ].
  - inversion l; subst.
    + right. left. destruct η as [b|b]; simpl in *.
      * destruct nb as (z & Hz). discriminate Hz.
      * destruct mu as [a|a]; simpl in duo; [ | exact (match duo with end) ]. subst.
        exists b. split; reflexivity.
    + right. right. destruct mu as [a|a]; simpl in nb.
      * destruct nb as (z & Hz). discriminate Hz.
      * exists a, b2. split; [ reflexivity | split; reflexivity ].
Qed.

(** **The** asynchrony fact: a forwarder state performs *any* input at any
    time, storing the corresponding message.  Nothing about [p] is
    consulted. *)
Lemma fw_input_always : forall (p : proc) (m : MO (ExtAct TypeOfActions)) a,
  (p ▷ m) ⟶[ActIn a] (p ▷ ({[+ ActOut a +]} ⊎ m)).
Proof.
  intros p m a. eapply ParRight.
  eapply (lts_multiset_add m (ActOut a) (ActIn a)).
  - simpl. reflexivity.
  - simpl. eexists; reflexivity.
Qed.

Lemma fw_emit : forall (p : proc) (m : MO (ExtAct TypeOfActions)) a,
  (p ▷ ({[+ ActOut a +]} ⊎ m)) ⟶[ActOut a] (p ▷ m).
Proof.
  intros p m a. eapply ParRight.
  apply (lts_multiset_minus m (ActOut a)). simpl. eexists; reflexivity.
Qed.

Lemma fw_ext_left : forall (p p' : proc) (m : MO (ExtAct TypeOfActions)) mu,
  lts p (ActExt mu) p' -> (p ▷ m) ⟶[mu] (p' ▷ m).
Proof. intros p p' m mu H. eapply ParLeft. exact H. Qed.

(** ** Weak transitions: feeding the buffer

    [fw_input_always] iterated.  A trace may *inject* messages into the
    buffer before anything else happens, and that is how a process's input
    behaviour becomes observable at all — at the bare-process level the
    abstracted ready set never mentions inputs ([VACCS_ReadySet.v]).

    [feed l] is the trace of inputs that loads the bag [bag l]. *)

Lemma fw_wt_lift : forall (s : trace (ExtAct TypeOfActions)) (p p' : proc)
                          (m : MO (ExtAct TypeOfActions)),
  p ⟹[s] p' -> (p ▷ m) ⟹[s] (p' ▷ m).
Proof.
  intros s p p' m H. induction H.
  - apply wt_nil.
  - eapply wt_tau; [ apply fw_tau_left; exact l | exact IHwt ].
  - eapply wt_act; [ apply fw_ext_left; exact l | exact IHwt ].
Qed.

Lemma fw_wt_feed : forall a (p : proc) (m : MO (ExtAct TypeOfActions)) s x,
  (p ▷ ({[+ ActOut a +]} ⊎ m)) ⟹[s] x -> (p ▷ m) ⟹[ActIn a :: s] x.
Proof. intros a p m s x H. eapply wt_act; [ apply fw_input_always | exact H ]. Qed.

Fixpoint feed (l : list TypeOfActions) : trace (ExtAct TypeOfActions) :=
match l with
| nil => nil
| a :: l' => ActIn a :: feed l'
end.

Fixpoint bag (l : list TypeOfActions) : MO (ExtAct TypeOfActions) :=
match l with
| nil => ∅
| a :: l' => {[+ ActOut a +]} ⊎ bag l'
end.

Lemma fw_wt_feed_list : forall (l : list TypeOfActions) (p : proc)
                               (m : MO (ExtAct TypeOfActions)) s x,
  (p ▷ (bag l ⊎ m)) ⟹[s] x -> (p ▷ m) ⟹[feed l ++ s] x.
Proof.
  induction l as [|a l IH]; intros p m s x H; simpl in *.
  - assert (∅ ⊎ m = m) as E by multiset_solver. rewrite <- E. exact H.
  - apply fw_wt_feed. apply IH.
    replace (bag l ⊎ ({[+ ActOut a +]} ⊎ m)) with ({[+ ActOut a +]} ⊎ bag l ⊎ m)
      by multiset_solver.
    exact H.
Qed.

(** ** The buffer only ever holds what the trace put in

    First half of the decomposition of a forwarder run.  Messages enter the
    buffer *only* through [lts_multiset_add], which fires on an input of
    the pair and therefore contributes that input to the trace; they leave
    by being emitted (an output in the trace) or delivered to [p] (a [τ]).
    [p]'s own outputs go straight out, never through the buffer.  Hence: *)

Fixpoint ins (s : trace (ExtAct TypeOfActions)) : list TypeOfActions :=
match s with
| nil => nil
| ActIn a :: s' => a :: ins s'
| ActOut _ :: s' => ins s'
end.

Lemma fw_buffer_bounded : forall (s : trace (ExtAct TypeOfActions))
    (x y : proc * MO (ExtAct TypeOfActions)),
  x ⟹[s] y -> y.2 ⊆ x.2 ⊎ bag (ins s).
Proof.
  intros s x y H.
  induction H as [x|s x q y Hl Hw IH|mu s x q y Hl Hw IH]; simpl.
  - multiset_solver.
  - destruct x as (p,m). destruct q as (p1,m1).
    destruct (fw_tau_shape p m (p1,m1) Hl) as [(p' & _ & E)|(a & p' & m' & Hm & _ & E)];
      inversion E; subst; simpl in *; multiset_solver.
  - destruct x as (p,m). destruct q as (p1,m1).
    destruct (fw_ext_shape p m mu (p1,m1) Hl) as [HA|[HB|HC]].
    + destruct HA as (p' & _ & E). inversion E; subst. simpl in *.
      destruct mu as [a|a]; simpl; multiset_solver.
    + destruct HB as (a & Hmu & E). inversion E; subst. simpl in *. multiset_solver.
    + destruct HC as (a & m' & Hmu & Hm & E). inversion E; subst. simpl in *. multiset_solver.
Qed.

(** Consequence: **on an output-only trace the buffer never fills**, so on
    that fragment the forwarder is exactly the bare process.  All the extra
    discriminating power of [p ▷ ∅] over [p] comes from traces that carry
    inputs — which is the same statement as [VACCS_ReadySet.v]'s (a bare
    process's ready set never mentions inputs), seen from the trace side. *)

Corollary fw_buffer_empty : forall (s : trace (ExtAct TypeOfActions)) p p' m',
  ins s = nil -> (p ▷ ∅) ⟹[s] (p' ▷ m') -> m' = ∅.
Proof.
  intros s p p' m' Hs H.
  pose proof (fw_buffer_bounded s (p ▷ ∅) (p' ▷ m') H) as Hb.
  simpl in Hb. rewrite Hs in Hb. simpl in Hb. multiset_solver.
Qed.

(** ** The conservation law: recovering the process's own trace

    Second half of the decomposition.  Every forwarder run projects onto a
    run of the *process*, and the two traces are related by a single
    multiset equation.

    Writing [ins]/[outs] for a trace's inputs and outputs and [bag] for the
    multiset they form, a run [(p ▷ m) ⟹[s] (p' ▷ m')] admits a process
    trace [r] with [p ⟹[r] p'] and

        m  ⊎  ins s  ⊎  outs r   =   m'  ⊎  outs s  ⊎  ins r

    Read it as a balance sheet.  On the left: what the buffer started with,
    what the environment sent in, and what the process produced.  On the
    right: what the buffer ended with, what the environment saw come out,
    and what the process consumed.  Nothing is created or lost, and the
    three ways a message can move — absorbed by the buffer, delivered to
    the process, emitted to the environment — are exactly what makes the
    two sides differ term by term.

    Note what it does *not* say: [r] is not determined by [s].  The same
    trace can be realised with the process consuming an input directly or
    with the buffer absorbing it first and delivering it later, and a
    message the buffer still holds at the end is one the environment sent
    that the process never took.  That slack is the asynchrony, and the
    equation is exactly the invariant that survives it. *)

Fixpoint outs (s : trace (ExtAct TypeOfActions)) : list TypeOfActions :=
match s with
| nil => nil
| ActIn _ :: s' => outs s'
| ActOut a :: s' => a :: outs s'
end.

Lemma fw_conservation : forall (s : trace (ExtAct TypeOfActions))
    (x y : proc * MO (ExtAct TypeOfActions)),
  x ⟹[s] y -> exists r, x.1 ⟹[r] y.1 /\
    x.2 ⊎ bag (ins s) ⊎ bag (outs r) = y.2 ⊎ bag (outs s) ⊎ bag (ins r).
Proof.
  intros s x y H.
  induction H as [x|s x q y Hl Hw IH|mu s x q y Hl Hw IH].
  - exists nil. split; [ apply wt_nil | simpl; multiset_solver ].
  - destruct x as (p,m). destruct q as (p1,m1).
    destruct IH as (r & Hr & Heq). simpl in *.
    destruct (fw_tau_shape p m (p1,m1) Hl) as [HA|HB].
    + (* the process moves on its own *)
      destruct HA as (p' & Hp' & E). inversion E; subst.
      exists r. split; [ eapply wt_tau; [ exact Hp' | exact Hr ] | simpl in *; multiset_solver ].
    + (* delivery: the buffer loses a message, the process gains an input *)
      destruct HB as (a & p' & m' & Hm & Hp' & E). inversion E; subst.
      exists (ActIn a :: r). split.
      * eapply wt_act; [ exact Hp' | exact Hr ].
      * simpl in *. multiset_solver.
  - destruct x as (p,m). destruct q as (p1,m1).
    destruct IH as (r & Hr & Heq). simpl in *.
    destruct (fw_ext_shape p m mu (p1,m1) Hl) as [HA|[HB|HC]].
    + (* the process acts visibly: the action is on both sides *)
      destruct HA as (p' & Hp' & E). inversion E; subst.
      exists (mu :: r). split.
      * eapply wt_act; [ exact Hp' | exact Hr ].
      * destruct mu as [a|a]; simpl in *; multiset_solver.
    + (* absorption: the trace gains an input, the buffer gains the message *)
      destruct HB as (a & Hmu & E). inversion E; subst.
      exists r. split; [ exact Hr | simpl in *; multiset_solver ].
    + (* emission: the buffer loses a message, the trace gains an output *)
      destruct HC as (a & m' & Hmu & Hm & E). inversion E; subst.
      exists r. split; [ exact Hr | simpl in *; multiset_solver ].
Qed.

(** ** A STABLE state with a mute process just drains its buffer

    The conservation law leaves slack on purpose.  When the state is
    *stable* and its process can never emit — which is exactly a guarded
    sum sitting in front of messages it refuses — the slack vanishes: an
    output-only run cannot move the process at all (its own [τ] is absent,
    a delivery is refused, and it has no output of its own), so every step
    is a buffer emission and the trace *is* the part of the buffer that
    left.

    This is what makes a pending message bag **observable**: the ready-set
    abstraction erases both the value and the multiplicity of a message
    ([VACCS_ReadySet.coR_abs_iff]), so a bag can only be seen through
    traces — and along an output trace it is seen exactly. *)

Lemma fw_out_run_drain : forall (s : trace (ExtAct TypeOfActions))
    (x y : proc * MO (ExtAct TypeOfActions)),
  x ⟹[s] y -> ins s = nil ->
  (forall a p', ~ lts x.1 (ActExt (ActOut a)) p') ->
  (forall z, ~ (x ⟶ z)) ->
  y.1 = x.1 /\ (bag (outs s) ⊎ y.2 = x.2).
Proof.
  intros s x y H.
  induction H as [x|s x q y Hl Hw IH|mu s x q y Hl Hw IH];
    intros Hins Hno Hst.
  - split; [ reflexivity | simpl; multiset_solver ].
  - exfalso. eapply Hst. exact Hl.
  - destruct x as (p,m). destruct q as (p1,m1). simpl in *.
    destruct mu as [a|a]; simpl in Hins; [ discriminate Hins | ].
    destruct (fw_ext_shape p m (ActOut a) (p1,m1) Hl) as [HA|[HB|HC]].
    + destruct HA as (p' & Hp' & _). exfalso. eapply Hno. exact Hp'.
    + destruct HB as (b & Hb & _). discriminate Hb.
    + destruct HC as (b & m' & Hb & Hm & E). inversion Hb; subst.
      inversion E; subst.
      apply fw_stable_iff in Hst as (Hst1 & Hst2).
      destruct (IH Hins Hno) as (Hy1 & Hy2).
      { apply fw_stable_iff. split; [ exact Hst1 | ].
        intros a0 Ha0. apply Hst2. multiset_solver. }
      split; [ exact Hy1 | ]. simpl. multiset_solver.
Qed.

(** Moving between the two ways of saying "no internal step".  The
    generic [lts_refuses] is decidable on this instance, so the two forms
    are interchangeable; going through [decide] is the workaround already
    on record for this concrete [gLts]. *)

Lemma stable_of_no_step : forall (x : proc * MO (ExtAct TypeOfActions)),
  (forall z, ~ (x ⟶ z)) -> x ↛.
Proof.
  intros x H. destruct (decide (lts_refuses x τ)) as [Hy|Hn]; [ exact Hy | ].
  exfalso. apply lts_refuses_spec1 in Hn as (q & Hq). eapply H. exact Hq.
Qed.

Lemma no_step_of_stable : forall (x : proc * MO (ExtAct TypeOfActions)),
  x ↛ -> forall z, ~ (x ⟶ z).
Proof.
  intros x H z Hz.
  eapply (@lts_refuses_spec2 (proc * MO (ExtAct TypeOfActions)) _ _ _ x τ);
    [ exists z; exact Hz | exact H ].
Qed.

Lemma bag_out : forall (l : list TypeOfActions) z,
  z ∈ bag l -> exists a, z = ActOut a.
Proof.
  induction l as [|a l IH]; intros z Hz; simpl in Hz.
  - exfalso. multiset_solver.
  - apply gmultiset_elem_of_disj_union in Hz as [Hz|Hz].
    + exists a. multiset_solver.
    + apply IH. exact Hz.
Qed.

Lemma ins_map_out : forall (l : list TypeOfActions), ins (map ActOut l) = nil.
Proof. induction l as [|a l IH]; simpl; [ reflexivity | exact IH ]. Qed.

Lemma outs_map_out : forall (l : list TypeOfActions), outs (map ActOut l) = l.
Proof. induction l as [|a l IH]; simpl; [ reflexivity | rewrite IH; reflexivity ]. Qed.

(** A state that offers no output at all has an empty buffer — provided
    the buffer really holds messages, which is what [VACCS_Cond2.OutOnly]
    records for every buffer reachable from [∅]. *)

Lemma fw_no_emit_empty_buffer : forall (p : proc) (m : MO (ExtAct TypeOfActions)),
  (forall z, z ∈ m -> exists a, z = ActOut a) ->
  (forall a y, ~ ((p ▷ m) ⟶[ActOut a] y)) -> m = ∅.
Proof.
  intros p m Hout H.
  destruct (decide (m = ∅)) as [He|He]; [ exact He | exfalso ].
  apply gmultiset_choose in He as (z & Hz).
  destruct (Hout z Hz) as (a & Ea). subst z.
  assert (Hm : m = {[+ ActOut a +]} ⊎ (m ∖ {[+ ActOut a +]})) by multiset_solver.
  eapply (H a). rewrite Hm at 1. apply fw_emit.
Qed.

(** ** Projecting a drain run onto a smaller buffer

    [fw_out_run_drain] says that a *stable* state whose process is mute
    only ever emits from its buffer.  What follows is the statement one
    actually needs when the buffer is **larger** than what the trace
    emits: the surplus messages are simply carried along, so the very same
    run is a [τ]-run from the surplus alone.

    The hypothesis is [MuteRun] — "no run of this process ever emits" —
    rather than the one-step "this process has no output": the property
    has to survive every state the run visits, and in that form it is
    preserved by transitions ([MuteRun_step]) while giving the one-step
    fact for free ([MuteRun_no_out]).  In [VACCS_Matching.v] it is
    discharged from [ochans p = []] by [trace_out_in_ochans]. *)

Definition MuteRun (p : proc) : Prop :=
  forall r q, p ⟹[r] q -> outs r = [].

Lemma MuteRun_step : forall (p : proc) a q, MuteRun p -> lts p a q -> MuteRun q.
Proof.
  intros p a q Hm Hl r z Hw.
  destruct a as [mu|].
  - assert (Hbig : p ⟹[mu :: r] z) by (eapply wt_act; [ exact Hl | exact Hw ]).
    specialize (Hm _ _ Hbig). destruct mu as [b|b]; simpl in Hm.
    + exact Hm.
    + discriminate Hm.
  - apply (Hm r z). eapply wt_tau; [ exact Hl | exact Hw ].
Qed.

Lemma MuteRun_no_out : forall (p : proc) a q, MuteRun p ->
  ~ lts p (ActExt (ActOut a)) q.
Proof.
  intros p a q Hm Hl.
  assert (Hw : p ⟹[ActOut a :: nil] q) by (eapply wt_act; [ exact Hl | apply wt_nil ]).
  specialize (Hm _ _ Hw). simpl in Hm. discriminate Hm.
Qed.

(** A run whose trace carries no input, from a buffer that is exactly what
    the trace emits plus a surplus [m], is a [τ]-run from [m] alone — and
    it reaches the **same** state, buffer included.

    The only step with content is the *delivery*: a message leaves the
    buffer into the process, and one has to know it came from the surplus
    rather than from the part still owed to the trace.  That is not a
    local fact — it follows from [fw_conservation] applied to the
    remaining run, which pins [bag (outs s)] inside the buffer that is
    left.  A buffer emission, by contrast, is simply **dropped**: that is
    what makes the projection shorter than the run it projects. *)

Lemma fw_drain_project : forall (s : trace (ExtAct TypeOfActions))
    (x y : proc * MO (ExtAct TypeOfActions)),
  x ⟹[s] y -> MuteRun x.1 -> ins s = [] ->
  forall m, x.2 = bag (outs s) ⊎ m -> (x.1 ▷ m) ⟹[[]] y.
Proof.
  intros s x y Hw. induction Hw as [x|s x q y Hl Hwt IH|mu s x q y Hl Hwt IH];
    intros Hmute Hins m Hbuf.
  - simpl in Hbuf. destruct x as (p,k). simpl in *.
    replace k with m in * by (rewrite Hbuf; multiset_solver).
    apply wt_nil.
  - destruct x as (p,k). destruct q as (p1,k1). simpl in *. subst k.
    destruct (fw_tau_shape p _ (p1,k1) Hl) as [HA|HB].
    + destruct HA as (p' & Hp' & E). inversion E; subst.
      assert (Hm' : MuteRun p') by (eapply MuteRun_step; [ exact Hmute | exact Hp' ]).
      specialize (IH Hm' Hins m eq_refl). simpl in IH.
      eapply wt_tau; [ apply fw_tau_left; exact Hp' | exact IH ].
    + destruct HB as (a & p' & m' & Hk & Hp' & E). inversion E; subst.
      assert (Hm' : MuteRun p') by (eapply MuteRun_step; [ exact Hmute | exact Hp' ]).
      destruct (fw_conservation _ _ _ Hwt) as (r & Hr & Hbal). simpl in Hbal.
      assert (Houtr : outs r = []) by (eapply Hm'; exact Hr).
      rewrite Hins, Houtr in Hbal. simpl in Hbal.
      assert (Hsub : bag (outs s) ⊆ m') by multiset_solver.
      assert (Hin : ActOut a ∈ m) by multiset_solver.
      remember (m ∖ {[+ ActOut a +]}) as m2 eqn:Em2.
      assert (Hsplit : m = {[+ ActOut a +]} ⊎ m2) by (rewrite Em2; multiset_solver).
      assert (Hm2 : m' = bag (outs s) ⊎ m2) by (rewrite Em2; multiset_solver).
      specialize (IH Hm' Hins _ Hm2). simpl in IH.
      eapply wt_tau; [ | exact IH ].
      rewrite Hsplit. apply fw_tau_deliver. exact Hp'.
  - destruct x as (p,k). destruct q as (p1,k1). simpl in *. subst k.
    destruct mu as [b|b]; simpl in Hins; [ discriminate Hins | ].
    destruct (fw_ext_shape p _ (ActOut b) (p1,k1) Hl) as [HA|[HB|HC]].
    + destruct HA as (p' & Hp' & _). exfalso. eapply MuteRun_no_out; eassumption.
    + destruct HB as (a & Hcon & _). discriminate Hcon.
    + destruct HC as (a & m'' & Ha & Hk & E). injection Ha as Ha. subst a.
      inversion E; subst. simpl in Hk.
      assert (Hm2 : m'' = bag (outs s) ⊎ m) by multiset_solver.
      exact (IH Hmute Hins _ Hm2).
Qed.

(** ** The forwarder's offers

    Completing the ready-set story of [VACCS_ReadySet.v] at the forwarder
    level.  [coR] holds inputs only, and an input is in it exactly when the
    dual **output** is offered — so what matters is what a state can emit.

    A forwarder state emits [a] iff the process does or the buffer holds
    it; and it accepts *every* input, unconditionally. *)

Lemma fw_emits_iff : forall (p : proc) (m : MO (ExtAct TypeOfActions)) a,
  (exists y, (p ▷ m) ⟶[ActOut a] y)
  <-> ((exists p', lts p (ActExt (ActOut a)) p') \/ ActOut a ∈ m).
Proof.
  intros p m a. split.
  - intros (y & Hy). destruct y as (p1,m1).
    destruct (fw_ext_shape p m (ActOut a) (p1,m1) Hy) as [HA|[HB|HC]].
    + destruct HA as (p' & Hp' & _). left. exists p'. exact Hp'.
    + destruct HB as (b & Hb & _). discriminate Hb.
    + destruct HC as (b & m' & Hb & Hm & _). inversion Hb; subst.
      right. multiset_solver.
  - intros [(p' & Hp')|Hin].
    + exists (p' ▷ m). apply fw_ext_left. exact Hp'.
    + exists (p ▷ (m ∖ {[+ ActOut a +]})).
      assert (m = {[+ ActOut a +]} ⊎ (m ∖ {[+ ActOut a +]})) as Heq by multiset_solver.
      rewrite Heq at 1. apply fw_emit.
Qed.

Lemma fw_inputs_always_iff : forall (p : proc) (m : MO (ExtAct TypeOfActions)) a,
  exists y, (p ▷ m) ⟶[ActIn a] y.
Proof. intros p m a. eexists. apply fw_input_always. Qed.

(** ** On input-free traces the forwarder is transparent

    Started from an empty buffer, a run whose trace carries no input can
    neither fill the buffer (only [lts_multiset_add] does, and it needs an
    input) nor empty it (it is already empty, so no emission and no
    delivery).  So the buffer is [∅] throughout and every step is the
    process's own:

        fw_wt_noinput_proj : x ⟹[s] y -> x.2 = ∅ -> ins s = [] ->
                             y.2 = ∅ ∧ x.1 ⟹[s] y.1

    Together with [fw_wt_lift] (the converse) and the two corollaries on
    stability and offers, this says that at such a trace [p ▷ ∅] and [p]
    are indistinguishable — reachable states, stability, and ready sets
    all coincide.

    **This localises exactly where the forwarder earns its keep.**
    [VACCS_ReadySet.v] showed a bare process's abstracted ready set carries
    only its outgoing messages; here is the trace-side complement, and the
    two together say: everything the forwarder adds to [⊑ₘᵤₛₜᵢ] comes from
    traces that feed inputs in.  For [bhv_pre_cond2] that is directly
    usable — at every input-free trace, and in particular at [ε], the
    condition is a statement about bare processes. *)

Lemma fw_wt_noinput_proj : forall (s : trace (ExtAct TypeOfActions))
    (x y : proc * MO (ExtAct TypeOfActions)),
  x ⟹[s] y -> x.2 = ∅ -> ins s = nil -> y.2 = ∅ /\ x.1 ⟹[s] y.1.
Proof.
  intros s x y H. induction H as [x|s x q y Hl Hw IH|mu s x q y Hl Hw IH];
    intros Hm Hs; simpl in *.
  - split; [exact Hm | apply wt_nil].
  - destruct x as (p,m). destruct q as (p1,m1). simpl in *.
    destruct (fw_tau_shape p m (p1,m1) Hl) as [HA|HB].
    + destruct HA as (p' & Hp' & E). inversion E; subst.
      destruct (IH eq_refl Hs) as (H1 & H2). simpl in *.
      split; [exact H1 | eapply wt_tau; [exact Hp' | exact H2]].
    + (* delivery is impossible: the buffer is empty *)
      destruct HB as (a & p' & m' & Hmeq & _ & _). exfalso.
      subst m. multiset_solver.
  - destruct x as (p,m). destruct q as (p1,m1). simpl in *.
    destruct (fw_ext_shape p m mu (p1,m1) Hl) as [HA|[HB|HC]].
    + destruct HA as (p' & Hp' & E). inversion E; subst.
      destruct mu as [a|a]; simpl in Hs; [ discriminate Hs | ].
      destruct (IH eq_refl Hs) as (H1 & H2). simpl in *.
      split; [exact H1 | eapply wt_act; [exact Hp' | exact H2]].
    + (* absorption is impossible: the trace has no input *)
      destruct HB as (a & Hmu & E). subst mu. simpl in Hs. discriminate Hs.
    + (* emission is impossible: the buffer is empty *)
      destruct HC as (a & m' & Hmu & Hmeq & E). exfalso.
      subst m. multiset_solver.
Qed.

Corollary fw_reach_noinput : forall s p p' m',
  ins s = nil -> (p ▷ ∅) ⟹[s] (p' ▷ m') -> m' = ∅ /\ p ⟹[s] p'.
Proof.
  intros s p p' m' Hs H.
  destruct (fw_wt_noinput_proj s (p ▷ ∅) (p' ▷ m') H eq_refl Hs) as (H1 & H2).
  simpl in *. split; assumption.
Qed.

Corollary fw_reach_noinput_iff : forall s p p',
  ins s = nil -> ((p ▷ ∅) ⟹[s] (p' ▷ ∅) <-> p ⟹[s] p').
Proof.
  intros s p p' Hs. split.
  - intro H. destruct (fw_reach_noinput s p p' ∅ Hs H) as (_ & H2). exact H2.
  - intro H. apply fw_wt_lift. exact H.
Qed.

Corollary fw_nil_stable : forall p,
  (forall x, ~ ((p ▷ ∅) ⟶ x)) <-> (forall q, ~ lts p τ q).
Proof.
  intro p. split.
  - intro H. apply (proj1 (fw_stable_iff p ∅) H).
  - intro H. apply fw_stable_iff. split; [exact H | intros a Ha; multiset_solver].
Qed.

Corollary fw_nil_emits : forall p a,
  (exists y, (p ▷ ∅) ⟶[ActOut a] y) <-> (exists q, lts p (ActExt (ActOut a)) q).
Proof.
  intros p a. rewrite fw_emits_iff. split.
  - intros [H|H]; [exact H | multiset_solver].
  - intro H. left. exact H.
Qed.

(** * Three notions the acceptance-set arguments are phrased with

    They live here rather than with their lemmas so that the axiom system
    can mention them: [VACCS_Cond2.v] imports [VACCS_ReadySet.v], which
    imports the axiom system, so anything a *rule* refers to has to be
    defined at this level.

    - [emits y d]: the state can emit on channel [d].
    - [Settles S x]: [x] can reach, by internal steps alone, a stable
      state whose pending outputs all lie on channels in [S].  This is
      the ∃-shaped condition [bhv_pre_cond2] hands over.
    - [OutOnly m]: the buffer holds outputs only, which is all the
      forwarder can ever reach from [∅]. *)

Definition emits (y : proc * MO (ExtAct TypeOfActions)) (d : ChannelData) : Prop :=
  exists w r, y ⟶[ActOut (d,w)] r.

Definition Settles (S : ChannelData -> Prop) (x : proc * MO (ExtAct TypeOfActions)) : Prop :=
  exists y, x ⟹[[]] y /\ y ↛ /\ (forall d w r, y ⟶[ActOut (d,w)] r -> S d).

Definition OutOnly (m : MO (ExtAct TypeOfActions)) : Prop :=
  forall x, x ∈ m -> exists a, x = ActOut a.


(** ** The bag is a multiset: permutation, emptiness, membership

    Three facts about [bag] that any comparison of two configurations
    needs â [bags_agree] delivers an equality of *multisets*, and the
    syntax is built from *lists*. *)

Lemma bag_perm : forall (l l' : list TypeOfActions), Permutation l l' -> bag l = bag l'.
Proof.
  intros l l' H. induction H as [ | x l0 l1 Hp IH | x z l0 | l0 l1 l2 H1 IH1 H2 IH2 ];
    simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
  - multiset_solver.
  - rewrite IH1. exact IH2.
Qed.

Lemma bag_nil_inv : forall (l : list TypeOfActions), bag l = ∅ -> l = [].
Proof.
  intros [|cv l] H; [ reflexivity | exfalso ]. simpl in H.
  assert (Hm : ActOut cv ∈ bag (cv :: l)).
  { simpl. apply gmultiset.gmultiset_elem_of_disj_union. left.
    apply gmultiset_elem_of_singleton. reflexivity. }
  simpl in Hm. rewrite H in Hm. eapply gmultiset_not_elem_of_empty. exact Hm.
Qed.

Lemma bag_elem : forall (l : list TypeOfActions) (a : TypeOfActions),
  ActOut a ∈ bag l -> In a l.
Proof.
  induction l as [|cv l IH]; intros a H; simpl in H.
  - exfalso. eapply gmultiset_not_elem_of_empty. exact H.
  - apply gmultiset.gmultiset_elem_of_disj_union in H as [H|H].
    + left. apply gmultiset_elem_of_singleton in H. congruence.
    + right. apply IH. exact H.
Qed.

(** ** Message bags *)

Fixpoint msgs (l : list (ChannelData * ValueData)) : proc :=
match l with
| [] => g 𝟘
| cv :: l' => (fst cv ! snd cv • 𝟘) ‖ msgs l'
end.

Lemma msgs_Static : forall l, Static (msgs l).
Proof. induction l as [|cv l IH]; simpl; [ repeat constructor | constructor; [ constructor | exact IH ] ]. Qed.

Lemma msgs_app : forall l1 l2, msgs (l1 ++ l2) ≡* (msgs l1 ‖ msgs l2).
Proof.
  induction l1 as [|cv l1 IH]; intro l2; simpl.
  - symmetry. etransitivity; [ apply cgr_par_com | apply cgr_par_nil ].
  - etransitivity; [ | apply cgr_par_assoc_rev ]. apply cgr_fullpar; [ reflexivity | apply IH ].
Qed.

Lemma msgs_no_input : forall l c v r, ~ lts (msgs l) (ActExt (ActIn (c,v))) r.
Proof.
  induction l as [|a l IH]; intros c v r H; simpl in H.
  - inversion H.
  - inversion H; subst.
    + match goal with HH : lts (_ ! _ • 𝟘) _ _ |- _ => inversion HH end.
    + eapply IH. eassumption.
Qed.

(** ** From an equality of bags to a structural congruence of message bags

    [bags_agree] concludes [bag l = bag l'] — an equality of *multisets* —
    while every configuration-level statement is written with the *list*
    [msgs l].  These two close that gap: a permutation of the list is a
    structural congruence of the bag, and equal multisets come from
    permuted lists. *)

Lemma msgs_perm : forall (l l' : list TypeOfActions),
  Permutation l l' -> msgs l ≡* msgs l'.
Proof.
  intros l l' H. induction H as [ | x l0 l1 Hp IH | x z l0 | l0 l1 l2 H1 IH1 H2 IH2 ];
    simpl.
  - reflexivity.
  - apply cgr_fullpar; [ reflexivity | exact IH ].
  - etransitivity; [ apply cgr_par_assoc_rev | ].
    etransitivity; [ | apply cgr_par_assoc ].
    apply cgr_fullpar; [ apply cgr_par_com | reflexivity ].
  - etransitivity; [ exact IH1 | exact IH2 ].
Qed.

Lemma bag_msgs_eq : forall (l l' : list TypeOfActions),
  bag l = bag l' -> msgs l ≡* msgs l'.
Proof.
  induction l as [|cv l0 IH]; intros l' H.
  - simpl in H. assert (E : l' = []) by (apply bag_nil_inv; symmetry; exact H).
    subst l'. reflexivity.
  - assert (Hin : In cv l').
    { apply bag_elem. rewrite <- H. simpl.
      apply gmultiset.gmultiset_elem_of_disj_union. left.
      apply gmultiset_elem_of_singleton. reflexivity. }
    apply in_split in Hin as (l1 & l2 & E). subst l'.
    assert (Hp : Permutation (l1 ++ cv :: l2) (cv :: (l1 ++ l2)))
      by (symmetry; apply Permutation_middle).
    assert (Hb : bag (l1 ++ cv :: l2) = bag (cv :: (l1 ++ l2)))
      by (apply bag_perm; exact Hp).
    rewrite Hb in H. simpl in H.
    assert (Hb2 : bag l0 = bag (l1 ++ l2))
      by (eapply gmultiset_disj_union_inj_1; exact H).
    etransitivity; [ | apply msgs_perm; symmetry; exact Hp ].
    simpl. apply cgr_fullpar; [ reflexivity | apply IH; exact Hb2 ].
Qed.


End VACCS_Forwarder.
