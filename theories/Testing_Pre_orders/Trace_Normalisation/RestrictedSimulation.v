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
From TestingTheory Require Import ActTau gLts Bisimulation Lts_OBA WeakTransitions
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
