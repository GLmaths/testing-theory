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
From stdpp Require Import base countable list decidable.
From TestingTheory Require Import ActTau gLts Bisimulation Lts_OBA WeakTransitions Termination Convergence Subset_Act
    NormalForm Normalisation.

(** * Simulations restricted to the feedback-free traces

    A plain simulation proves the inclusion of *all* traces of a process into
    those of another.  It is therefore too strong to compare two processes on
    the feedback-free traces only, which is what a preorder quantifying over
    feedback-simplified traces asks for: one must be allowed to ignore the
    inputs that close a feedback, that is the inputs dual to an action the
    process has already emitted.

    The relation therefore carries a *ledger*: the list of the non-blocking
    actions emitted so far.  The output clause appends to the ledger, and the
    input clause is only required for the inputs that are dual to nothing in
    it.  Reading a trace that way from the empty ledger is exactly the absence
    of feedback ([ff_from_nil]). *)

(** ** Reading a trace against a ledger *)

Section FeedbackFreeTraces.

  Context `{H : !ExtAction A}.

  (** [μ] closes no feedback against the ledger [E]. *)
  Definition no_fb_after (E : list A) (μ : A) : Prop := Forall (fun η => ¬ dual μ η) E.

  (** [s] performs no feedback, given what has already been emitted. *)
  Fixpoint ff_from (E : list A) (s : trace A) : Prop :=
    match s with
    | [] => True
    | x :: s' =>
        if decide (non_blocking x)
        then ff_from (x :: E) s'
        else no_fb_after E x /\ ff_from E s'
    end.

  Fixpoint has_fb_from (E : list A) (s : trace A) : Prop :=
    match s with
    | [] => False
    | x :: s' =>
        if decide (non_blocking x)
        then has_fb_from (x :: E) s'
        else Exists (fun η => dual x η) E \/ has_fb_from E s'
    end.

  (** The inputs of [s] that close a feedback opened before [s]. *)
  Definition hits (E : list A) (s : trace A) : Prop :=
    Exists (fun μ => ¬ non_blocking μ /\ Exists (fun η => dual μ η) E) s.

  Lemma Exists_or (Q R : A -> Prop) l :
    Exists (fun x => Q x \/ R x) l <-> Exists Q l \/ Exists R l.
  Proof.
    induction l as [| x l IH]; simpl.
    - split; [intro h; inversion h | intros [h|h]; inversion h].
    - rewrite 3 Exists_cons_iff, IH. tauto.
  Qed.

  Lemma Exists_iff_pt (Q R : A -> Prop) l :
    (forall x, Q x <-> R x) -> (Exists Q l <-> Exists R l).
  Proof.
    intro h. induction l as [| x l IH]; simpl.
    - split; intro k; inversion k.
    - rewrite 2 Exists_cons_iff, IH, (h x). tauto.
  Qed.

  Lemma forall_not_exists (Q : A -> Prop) (l : list A) :
    Forall (fun x => ¬ Q x) l <-> ¬ Exists Q l.
  Proof.
    induction l as [| x l IH]; simpl.
    - split; [intros _ h; inversion h | intros _; constructor].
    - split.
      + intro hf. eapply Forall_cons_1 in hf as (hx & hl).
        rewrite Exists_cons_iff. intros [h | h]; [exact (hx h) | eapply IH; eassumption].
      + intro h. constructor.
        * intro hx. eapply h, Exists_cons_iff. now left.
        * eapply IH. intro h'. eapply h, Exists_cons_iff. now right.
  Qed.

  (** An action dual to a non-blocking one is blocking. *)
  Lemma exists_dual_blocking (x : A) (l : trace A) :
    non_blocking x ->
    Exists (fun μ => dual μ x) l <-> Exists (fun μ => ¬ non_blocking μ /\ dual μ x) l.
  Proof.
    intro nb. eapply Exists_iff_pt. intro μ. split.
    - intro d. split; [| exact d]. intro nbμ. exact (dual_blocks μ x nb d nbμ).
    - now intros (_ & d).
  Qed.

  Lemma hits_cons_ledger E x s :
    non_blocking x -> (hits (x :: E) s <-> dual_later x s \/ hits E s).
  Proof.
    intro nb.
    transitivity (Exists (fun μ => (¬ non_blocking μ /\ dual μ x)
                                \/ (¬ non_blocking μ /\ Exists (fun η => dual μ η) E)) s).
    - unfold hits. eapply Exists_iff_pt. intro μ. rewrite Exists_cons_iff. tauto.
    - rewrite Exists_or. unfold hits, dual_later.
      rewrite <- (exists_dual_blocking x s nb). reflexivity.
  Qed.

  Lemma has_fb_from_split E s : has_fb_from E s <-> hits E s \/ has_fb s.
  Proof.
    revert E. induction s as [| x s IH]; intro E.
    - simpl. unfold hits. split.
      + contradiction.
      + intros [h | h]; [inversion h | exact h].
    - simpl. destruct (decide (non_blocking x)) as [nb | nb].
      + rewrite IH, (hits_cons_ledger E x s nb).
        unfold hits. rewrite Exists_cons_iff. tauto.
      + rewrite IH. unfold hits. rewrite Exists_cons_iff. tauto.
  Qed.

  Lemma has_fb_from_nil s : has_fb_from [] s <-> has_fb s.
  Proof.
    rewrite has_fb_from_split. unfold hits. split.
    - intros [h | h]; [| exact h].
      exfalso. clear -h. induction s as [| y s IHs]; [inversion h |].
      eapply Exists_cons_iff in h as [(_ & h) | h]; [inversion h | eapply IHs, h].
    - intro h. now right.
  Qed.

  Lemma ff_from_iff E s : ff_from E s <-> ¬ has_fb_from E s.
  Proof.
    revert E. induction s as [| x s IH]; intro E; simpl.
    - split; [intros _ h; exact h | intros _; exact I].
    - destruct (decide (non_blocking x)) as [nb | nb]; [eapply IH |].
      unfold no_fb_after. rewrite forall_not_exists, IH. tauto.
  Qed.

  (** Reading a trace from the empty ledger is exactly being feedback-free. *)
  Theorem ff_from_nil s : ff_from [] s <-> ¬ has_fb s.
  Proof. rewrite ff_from_iff, has_fb_from_nil. reflexivity. Qed.

End FeedbackFreeTraces.

(** ** Restricted simulations *)

Section RestrictedSimulation.

  Context `{H : !ExtAction A}.
  Context `{gLtsP : !gLts P H}.
  Context `{gLtsQ : !gLts Q H}.

  Definition rsim (R : list A -> P -> Q -> Prop) : Prop :=
    (forall E p1 q1 p2, R E p1 q1 -> p1 ⟶ p2 ->
        exists q2, q1 ⟹ q2 /\ R E p2 q2)
    /\ (forall E p1 q1 η p2, R E p1 q1 -> non_blocking η -> p1 ⟶[η] p2 ->
        exists q2, q1 ⟹{η} q2 /\ R (η :: E) p2 q2)
    /\ (forall E p1 q1 μ p2, R E p1 q1 -> ¬ non_blocking μ -> no_fb_after E μ ->
        p1 ⟶[μ] p2 -> exists q2, q1 ⟹{μ} q2 /\ R E p2 q2).

  Section Soundness.

    Variable R : list A -> P -> Q -> Prop.
    Hypothesis hR : rsim R.

    Lemma rsim_nil E p1 q1 p2 :
      R E p1 q1 -> p1 ⟹ p2 -> exists q2, q1 ⟹ q2 /\ R E p2 q2.
    Proof.
      intros hr w. remember ([] : trace A) as s0 eqn:Hs. revert q1 hr Hs.
      induction w as [ p | s p r t l w IH | μ s p r t l w IH ]; intros q1 hr Hs.
      - exists q1. split; [eauto with mdb | exact hr].
      - subst s. destruct hR as (hτ & _ & _).
        destruct (hτ E p q1 r hr l) as (q' & wq & hr').
        destruct (IH q' hr' eq_refl) as (q2 & wq2 & hr2).
        exists q2. split; [eapply wt_join_nil; eassumption | exact hr2].
      - discriminate.
    Qed.

    Lemma rsim_step_nb E p1 q1 (η : A) p2 :
      R E p1 q1 -> non_blocking η -> p1 ⟹{η} p2 ->
      exists q2, q1 ⟹{η} q2 /\ R (η :: E) p2 q2.
    Proof.
      intros hr nb w.
      eapply wt_decomp_one in w as (r1 & r2 & w1 & l & w2).
      destruct (rsim_nil E p1 q1 r1 hr w1) as (s1 & ws1 & hr1).
      destruct hR as (_ & hnb & _).
      destruct (hnb E r1 s1 η r2 hr1 nb l) as (s2 & ws2 & hr2).
      destruct (rsim_nil (η :: E) r2 s2 p2 hr2 w2) as (s3 & ws3 & hr3).
      exists s3. split; [| exact hr3].
      eapply wt_push_nil_left; [exact ws1 |].
      eapply wt_push_nil_right; [exact ws2 | exact ws3].
    Qed.

    Lemma rsim_step_b E p1 q1 (μ : A) p2 :
      R E p1 q1 -> ¬ non_blocking μ -> no_fb_after E μ -> p1 ⟹{μ} p2 ->
      exists q2, q1 ⟹{μ} q2 /\ R E p2 q2.
    Proof.
      intros hr nb hok w.
      eapply wt_decomp_one in w as (r1 & r2 & w1 & l & w2).
      destruct (rsim_nil E p1 q1 r1 hr w1) as (s1 & ws1 & hr1).
      destruct hR as (_ & _ & hb).
      destruct (hb E r1 s1 μ r2 hr1 nb hok l) as (s2 & ws2 & hr2).
      destruct (rsim_nil E r2 s2 p2 hr2 w2) as (s3 & ws3 & hr3).
      exists s3. split; [| exact hr3].
      eapply wt_push_nil_left; [exact ws1 |].
      eapply wt_push_nil_right; [exact ws2 | exact ws3].
    Qed.

    Theorem rsim_sound s : forall E p1 q1 p2,
      R E p1 q1 -> ff_from E s -> p1 ⟹[s] p2 -> exists q2, q1 ⟹[s] q2.
    Proof.
      induction s as [| α s IH]; intros E p1 q1 p2 hr hff w.
      - destruct (rsim_nil E p1 q1 p2 hr w) as (q2 & wq & _). now exists q2.
      - eapply wt_pop in w as (t & w1 & w2).
        simpl in hff. destruct (decide (non_blocking α)) as [nb | nb].
        + destruct (rsim_step_nb E p1 q1 α t hr nb w1) as (s2 & ws & hr2).
          destruct (IH (α :: E) t s2 p2 hr2 hff w2) as (q2 & wq2).
          exists q2. eapply wt_push_left; eassumption.
        + destruct hff as (hok & hff).
          destruct (rsim_step_b E p1 q1 α t hr nb hok w1) as (s2 & ws & hr2).
          destruct (IH E t s2 p2 hr2 hff w2) as (q2 & wq2).
          exists q2. eapply wt_push_left; eassumption.
    Qed.

    (** A restricted simulation from the empty ledger yields the inclusion of
        the feedback-free traces -- and only of those. *)
    Corollary rsim_traces_ff (p1 : P) (q1 : Q) s :
      R [] p1 q1 -> ¬ has_fb s -> (exists p2, p1 ⟹[s] p2) -> exists q2, q1 ⟹[s] q2.
    Proof.
      intros hr hff (p2 & w).
      eapply (rsim_sound s [] p1 q1 p2 hr); [| exact w].
      now eapply ff_from_nil.
    Qed.

  End Soundness.

End RestrictedSimulation.

(** * Simulations for convergence, restricted to the feedback-free traces

    The must conditions quantify over convergence, and convergence travels
    along the trace preorder in the direction *opposite* to the traces.  So
    where [rsim] simulates [p] by [q] to transport the traces of [p] into
    those of [q], the transport of [p ⇓ s] into [q ⇓ s] needs the mirror: a
    relation that simulates [q] by [p] and reflects termination.

    The ledger plays the same role, and for the same reason: an input dual to
    something already emitted is one a feedback-free trace never offers, so the
    corresponding clause need not be matched.

    One extra freedom is needed here, and it is not an artefact.  Once [p] has
    no move left, [p ⇓ s] holds vacuously and offers nothing; the obligation on
    [q] must then be discharged on its own.  Each move clause therefore allows
    a second answer: [q'] converges on every feedback-free continuation, full
    stop. *)

Section ConvergenceSimulation.

  Context `{H : !ExtAction A}.
  Context `{gLtsP : !gLts P H}.
  Context `{gLtsQ : !gLts Q H}.

  Lemma cnv_term (p : P) s : p ⇓ s -> p ⤓.
  Proof. intro h. inversion h; subst; assumption. Qed.

  Lemma cnv_step (p : P) μ s : p ⇓ (μ :: s) -> forall r, p ⟹{μ} r -> r ⇓ s.
  Proof. intro h. inversion h; subst. assumption. Qed.

  Definition csim (R : list A -> P -> Q -> Prop) : Prop :=
    (forall E p q, R E p q -> p ⤓ -> q ⤓)
    /\ (forall E p q η q', R E p q -> p ⤓ -> non_blocking η -> q ⟹{η} q' ->
          (exists p', p ⟹{η} p' /\ R (η :: E) p' q') \/ (forall s, ff_from (η :: E) s -> q' ⇓ s))
    /\ (forall E p q μ q', R E p q -> p ⤓ -> ¬ non_blocking μ -> no_fb_after E μ -> q ⟹{μ} q' ->
          (exists p', p ⟹{μ} p' /\ R E p' q') \/ (forall s, ff_from E s -> q' ⇓ s)).

  Theorem csim_sound (R : list A -> P -> Q -> Prop) (hR : csim R) :
    forall s E p q, R E p q -> ff_from E s -> p ⇓ s -> q ⇓ s.
  Proof.
    induction s as [| μ s IH]; intros E p q hr hff hcnv.
    - eapply cnv_nil. eapply (proj1 hR); [exact hr | eapply cnv_term, hcnv].
    - assert (hpt : p ⤓) by (eapply cnv_term, hcnv).
      eapply cnv_act; [eapply (proj1 hR); eassumption |].
      intros q' w. simpl in hff.
      destruct (decide (non_blocking μ)) as [nb | nb].
      + destruct (proj1 (proj2 hR) E p q μ q' hr hpt nb w) as [(p' & wp & hr') | hsafe].
        * eapply (IH (μ :: E) p' q'); [exact hr' | exact hff | eapply cnv_step; eassumption].
        * eapply hsafe, hff.
      + destruct hff as (hok & hff).
        destruct (proj2 (proj2 hR) E p q μ q' hr hpt nb hok w) as [(p' & wp & hr') | hsafe].
        * eapply (IH E p' q'); [exact hr' | exact hff | eapply cnv_step; eassumption].
        * eapply hsafe, hff.
  Qed.

  (** A restricted convergence simulation from the empty ledger transports the
      convergence of [p] into that of [q] -- on the feedback-free traces, and
      only on those. *)
  Corollary csim_cnv_ff (R : list A -> P -> Q -> Prop) (hR : csim R) (p : P) (q : Q) s :
    R [] p q -> ¬ has_fb s -> p ⇓ s -> q ⇓ s.
  Proof.
    intros hr hff hcnv. eapply (csim_sound R hR s [] p q hr); [| exact hcnv].
    now eapply ff_from_nil.
  Qed.

End ConvergenceSimulation.

(** * Simulations for acceptance sets, restricted to the feedback-free traces

    The second must condition asks that every stable state [q] reaches along a
    trace be matched by a stable state of [p] accepting no more.  Like [csim],
    the simulation therefore goes from [q] to [p]; unlike it, what has to be
    transported at the end of the trace is not termination but the co-ready
    set, so the relation carries one extra clause: at a stable [q], [p] must be
    able to settle on a stable state whose acceptance set is included.

    The ledger plays its usual role, and for the usual reason. *)

Section AcceptanceSimulation.

  Context `{H : !ExtAction A}.
  Context `{gLtsP : !gLts P H}.
  Context `{gLtsQ : !gLts Q H}.

  Definition asim (R : list A -> P -> Q -> Prop) : Prop :=
    (forall E p q q', R E p q -> q ⟹ q' -> exists p', p ⟹ p' /\ R E p' q')
    /\ (forall E p q, R E p q -> q ↛ -> exists p', p ⟹ p' /\ p' ↛ /\ coR p' ⊆ coR q)
    /\ (forall E p q η q', R E p q -> non_blocking η -> q ⟹{η} q' ->
          exists p', p ⟹{η} p' /\ R (η :: E) p' q')
    /\ (forall E p q μ q', R E p q -> ¬ non_blocking μ -> no_fb_after E μ -> q ⟹{μ} q' ->
          exists p', p ⟹{μ} p' /\ R E p' q').

  Theorem asim_sound (R : list A -> P -> Q -> Prop) (hR : asim R) :
    forall s E p q q', R E p q -> ff_from E s -> q ⟹[s] q' -> q' ↛ ->
      exists p', p ⟹[s] p' /\ p' ↛ /\ coR p' ⊆ coR q'.
  Proof.
    induction s as [| μ s IH]; intros E p q q' hr hff w hst.
    - destruct (proj1 hR E p q q' hr w) as (p1 & w1 & hr1).
      destruct (proj1 (proj2 hR) E p1 q' hr1 hst) as (p2 & w2 & hst2 & hsub).
      exists p2. split; [eapply wt_join_nil; eassumption | split; [exact hst2 | exact hsub]].
    - eapply wt_pop in w as (r & w1 & w2). simpl in hff.
      destruct (decide (non_blocking μ)) as [nb | nb].
      + destruct (proj1 (proj2 (proj2 hR)) E p q μ r hr nb w1) as (p1 & wp & hr1).
        destruct (IH (μ :: E) p1 r q' hr1 hff w2 hst) as (p2 & wp2 & hst2 & hsub).
        exists p2. split; [eapply wt_push_left; eassumption | split; [exact hst2 | exact hsub]].
      + destruct hff as (hok & hff).
        destruct (proj2 (proj2 (proj2 hR)) E p q μ r hr nb hok w1) as (p1 & wp & hr1).
        destruct (IH E p1 r q' hr1 hff w2 hst) as (p2 & wp2 & hst2 & hsub).
        exists p2. split; [eapply wt_push_left; eassumption | split; [exact hst2 | exact hsub]].
  Qed.

  (** The second must condition, on the feedback-free traces and only there. *)
  Corollary asim_cond2_ff (R : list A -> P -> Q -> Prop) (hR : asim R) (p : P) (q : Q) s q' :
    R [] p q -> ¬ has_fb s -> q ⟹[s] q' -> q' ↛ ->
    exists p', p ⟹[s] p' /\ p' ↛ /\ coR p' ⊆ coR q'.
  Proof.
    intros hr hff w hst. eapply (asim_sound R hR s [] p q q' hr); [| exact w | exact hst].
    now eapply ff_from_nil.
  Qed.

End AcceptanceSimulation.

(** * Traces without an echo

    The mirror of the ledger above.  Where [ff_from] records the non-blocking
    actions already emitted and forbids the inputs dual to them -- the
    feedbacks -- [ef_from] records the blocking actions already received and
    forbids the outputs dual to *them*: a process receiving a message and
    sending the same one back, an *echo*.

    On a co-trace this is what the ordinary [has_fb] designates: a co-trace
    label that is itself non-blocking is an output of the observer, that is an
    input of the process, and its dual appearing later is the process echoing
    it.  So "the co-trace carries no feedback", read literally with [has_fb],
    means "the process never echoes". *)

Section EchoFreeTraces.

  Context `{H : !ExtAction A}.

  Definition no_echo_after (E : list A) (η : A) : Prop := Forall (fun μ => ¬ dual η μ) E.

  Fixpoint ef_from (E : list A) (s : trace A) : Prop :=
    match s with
    | [] => True
    | x :: s' =>
        if decide (non_blocking x)
        then no_echo_after E x /\ ef_from E s'
        else ef_from (x :: E) s'
    end.

  Fixpoint has_echo (u : trace A) : Prop :=
    match u with
    | [] => False
    | x :: u' => (¬ non_blocking x /\ Exists (fun η => non_blocking η /\ dual η x) u') \/ has_echo u'
    end.

  Fixpoint has_echo_from (E : list A) (s : trace A) : Prop :=
    match s with
    | [] => False
    | x :: s' =>
        if decide (non_blocking x)
        then Exists (fun μ => dual x μ) E \/ has_echo_from E s'
        else has_echo_from (x :: E) s'
    end.

  Definition ehits (E : list A) (s : trace A) : Prop :=
    Exists (fun η => non_blocking η /\ Exists (fun μ => dual η μ) E) s.

  Lemma ehits_cons_ledger E x s :
    ehits (x :: E) s <-> Exists (fun η => non_blocking η /\ dual η x) s \/ ehits E s.
  Proof.
    transitivity (Exists (fun η => (non_blocking η /\ dual η x)
                                \/ (non_blocking η /\ Exists (fun μ => dual η μ) E)) s).
    - unfold ehits. eapply Exists_iff_pt. intro η. rewrite Exists_cons_iff. tauto.
    - rewrite Exists_or. reflexivity.
  Qed.

  Lemma has_echo_from_split E s : has_echo_from E s <-> ehits E s \/ has_echo s.
  Proof.
    revert E. induction s as [| x s IH]; intro E.
    - simpl. unfold ehits. split.
      + contradiction.
      + intros [h | h]; [inversion h | exact h].
    - simpl. destruct (decide (non_blocking x)) as [nb | nb].
      + rewrite IH. unfold ehits. rewrite Exists_cons_iff. tauto.
      + rewrite IH, (ehits_cons_ledger E x s).
        unfold ehits. rewrite Exists_cons_iff. tauto.
  Qed.

  Lemma has_echo_from_nil s : has_echo_from [] s <-> has_echo s.
  Proof.
    rewrite has_echo_from_split. unfold ehits. split.
    - intros [h | h]; [| exact h].
      exfalso. clear -h. induction s as [| y s IHs]; [inversion h |].
      eapply Exists_cons_iff in h as [(_ & h) | h]; [inversion h | eapply IHs, h].
    - intro h. now right.
  Qed.

  Lemma ef_from_iff E s : ef_from E s <-> ¬ has_echo_from E s.
  Proof.
    revert E. induction s as [| x s IH]; intro E; simpl.
    - split; [intros _ h; exact h | intros _; exact I].
    - destruct (decide (non_blocking x)) as [nb | nb]; [| eapply IH].
      unfold no_echo_after. rewrite forall_not_exists, IH. tauto.
  Qed.

  Theorem ef_from_nil s : ef_from [] s <-> ¬ has_echo s.
  Proof. rewrite ef_from_iff, has_echo_from_nil. reflexivity. Qed.

End EchoFreeTraces.

(** * Acceptance simulations restricted to the traces without an echo

    Same shape as [asim]; only the ledger and the guarded clause are exchanged.
    This is the tool for the second must condition read on co-traces with
    [has_fb] taken literally. *)

Section EchoAcceptanceSimulation.

  Context `{H : !ExtAction A}.
  Context `{gLtsP : !gLts P H}.
  Context `{gLtsQ : !gLts Q H}.

  Definition easim (R : list A -> P -> Q -> Prop) : Prop :=
    (forall E p q q', R E p q -> q ⟹ q' -> exists p', p ⟹ p' /\ R E p' q')
    /\ (forall E p q, R E p q -> q ↛ -> exists p', p ⟹ p' /\ p' ↛ /\ coR p' ⊆ coR q)
    /\ (forall E p q η q', R E p q -> non_blocking η -> no_echo_after E η -> q ⟹{η} q' ->
          exists p', p ⟹{η} p' /\ R E p' q')
    /\ (forall E p q μ q', R E p q -> ¬ non_blocking μ -> q ⟹{μ} q' ->
          exists p', p ⟹{μ} p' /\ R (μ :: E) p' q').

  Theorem easim_sound (R : list A -> P -> Q -> Prop) (hR : easim R) :
    forall s E p q q', R E p q -> ef_from E s -> q ⟹[s] q' -> q' ↛ ->
      exists p', p ⟹[s] p' /\ p' ↛ /\ coR p' ⊆ coR q'.
  Proof.
    induction s as [| μ s IH]; intros E p q q' hr hef w hst.
    - destruct (proj1 hR E p q q' hr w) as (p1 & w1 & hr1).
      destruct (proj1 (proj2 hR) E p1 q' hr1 hst) as (p2 & w2 & hst2 & hsub).
      exists p2. split; [eapply wt_join_nil; eassumption | split; [exact hst2 | exact hsub]].
    - eapply wt_pop in w as (r & w1 & w2). simpl in hef.
      destruct (decide (non_blocking μ)) as [nb | nb].
      + destruct hef as (hok & hef).
        destruct (proj1 (proj2 (proj2 hR)) E p q μ r hr nb hok w1) as (p1 & wp & hr1).
        destruct (IH E p1 r q' hr1 hef w2 hst) as (p2 & wp2 & hst2 & hsub).
        exists p2. split; [eapply wt_push_left; eassumption | split; [exact hst2 | exact hsub]].
      + destruct (proj2 (proj2 (proj2 hR)) E p q μ r hr nb w1) as (p1 & wp & hr1).
        destruct (IH (μ :: E) p1 r q' hr1 hef w2 hst) as (p2 & wp2 & hst2 & hsub).
        exists p2. split; [eapply wt_push_left; eassumption | split; [exact hst2 | exact hsub]].
  Qed.

  Corollary easim_cond2_ef (R : list A -> P -> Q -> Prop) (hR : easim R) (p : P) (q : Q) s q' :
    R [] p q -> ¬ has_echo s -> q ⟹[s] q' -> q' ↛ ->
    exists p', p ⟹[s] p' /\ p' ↛ /\ coR p' ⊆ coR q'.
  Proof.
    intros hr hef w hst. eapply (easim_sound R hR s [] p q q' hr); [| exact w | exact hst].
    now eapply ef_from_nil.
  Qed.

End EchoAcceptanceSimulation.
