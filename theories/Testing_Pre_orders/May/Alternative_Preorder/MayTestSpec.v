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
From stdpp Require Import base decidable.
From TestingTheory Require Import ActTau gLts Bisimulation Lts_OBA WeakTransitions Testing_Predicate.

Import ListNotations.

(** * The axiomatised test attesting a trace, for May

    [may_test_spec] and everything that follows from it alone — the
    test's own behaviour, independent of *which* trace-inclusion
    characterisation (plain [Trace_Inclusion/] or co-trace
    [coTrace_Inclusion/]) ends up using it. Lives alongside [May.v]
    rather than inside either characterisation so both can import it
    directly, instead of one importing the other's file for it. *)

(** ** Success is unreachable from [t] *)

Definition never_outcome `{gLts T A} (outcome : T -> Prop) (t : T) : Prop :=
  ∀ (u : trace A) (t' : T), t ⟹[u] t' -> ¬ outcome t'.

(** ** Axioms for the tests attesting a trace

    This mirrors the Must [test_spec] of [Completeness.v] field by field. The
    *only* semantic difference is the polarity of the deviation axiom:

    - Must: deviating from the trace reaches a *good* state, so a process that
      does not follow the trace passes the test trivially.
    - May: deviating from the trace must make success *unreachable*, otherwise a
      process could pass [gen r] without ever performing [r].

    Note the [blocking β] guards. They are not decoration: with a non-blocking
    (output) head, the deviation axiom is *inconsistent*. NB-DELAY
    ([Lts_OBA.v]) forces [gen (η :: μ :: s)] to be able to perform [μ] first,
    keeping [η] pending — a "deviation" the LTS itself guarantees is harmless.
    Asynchronous tests cannot sequentialise their outputs; that is exactly why the
    Must test emits them as floating messages ([(c ! v) ‖ …] in VACCS) and why
    [test_side_effect_by_construction] is guarded by [blocking β] there too. *)

Class may_test_spec
  `{gLtsT : @gLtsEq T A H, !Testing_Predicate outcome _}
  (gen : trace A -> T) := {
    (* 1 *) may_test_ungood s :
              ¬ outcome (gen s) ;
    (* 2 *) may_test_next_step μ s :
              gen (μ :: s) ⟶⋍[μ] gen s ;
    (* 3 *) may_test_follows_trace_determinacy {β s t} :
              blocking β -> gen (β :: s) ⟶[β] t -> t ⋍ gen s ;
    (* 4 *) may_test_deviation_is_fatal {β μ s t} :
              blocking β -> gen (β :: s) ⟶[μ] t -> μ ≠ β
                -> never_outcome outcome t ;
    (* 5 *) may_test_can_compute :
              ∃ e, gen ε ⟶ e ;
    (* 6 *) may_test_computes_to_good e :
              gen ε ⟶ e -> outcome e ;
    (* 7 *) may_test_tau_on_blocking_is_fatal {β s t} :
              blocking β -> gen (β :: s) ⟶ t -> never_outcome outcome t ;
  }.

(** Nothing at all is assumed about [gen ε] beyond (5) and (6) — in particular no
    counterpart of the side condition Must drags through its inversion lemmas,
    [∀ μ, f ε ↛[μ] ∨ (∀ t, f ε ⟶[μ] t -> outcome t)].  It is not needed: should
    [gen ε] offer some stray external action, it is only ever *reachable* once the
    trace is down to floating messages — and those are inputs on the process side,
    which a forwarder performs outright ([fw_run_inputs]).  That is exactly what
    the [Forall non_blocking s] disjunct of the inversion lemmas records. *)

Section May_tests.

Context `{gLtsT : @gLtsEq T A H, gLtsObaT : !gLtsOba T, !Testing_Predicate outcome _}.
Context {gen : trace A -> T} {gen_spec : may_test_spec gen}.

(** ** Determinacy on the expected action, for every action

    On a non-blocking head it comes for free from NB-DETERMINACY, which is why
    axiom (3) only needs to speak about blocking heads. Same argument as Must's
    [test_spec_determinacy]. *)

Lemma may_test_determinacy (μ : A) (s : trace A) (t : T) :
  gen (μ :: s) ⟶[μ] t -> t ⋍ gen s.
Proof.
  intro l.
  destruct (decide (non_blocking μ)) as [nb | b].
  - destruct (may_test_next_step μ s) as (v & lv & heqv).
    assert (heq : v ⋍ t) by (eapply nb_determinacy; eauto).
    etransitivity; [symmetry; exact heq | exact heqv].
  - eapply may_test_follows_trace_determinacy; eauto.
Qed.

(** ** Fatality propagates backwards along a non-blocking action

    The May counterpart of [outcome_preserved_by_lts_non_blocking_action_converse].
    It is not an axiom: it is *derived*, by showing that [w] can replay any
    successful run of [t] once [t] has emitted [η] — NB-CONFLUENCE lets [w] follow
    an external move, NB-TAU a silent one, NB-DETERMINACY the emission of [η]
    itself. *)

Lemma outcome_reachable_nb_forward (u : trace A) (t e : T) :
  t ⟹[u] e -> outcome e ->
  ∀ (w : T) (eta : A), non_blocking eta -> t ⟶[eta] w ->
  ∃ u' e', w ⟹[u'] e' /\ outcome e'.
Proof.
  intro wt.
  induction wt as [ x | u0 x y z l wt IH | mu u0 x y z l wt IH ];
    intros happy w eta nb leta.
  - (* the run is over: [x] is already successful, hence so is [w] *)
    exists ε, w. split; [eapply wt_nil |].
    eapply outcome_preserved_by_lts_non_blocking_action; eauto.
  - (* a silent move of [x] *)
    destruct (nb_tau nb leta l)
      as [ (z0 & lz0 & (y' & ly' & heqy')) | (beta & duo & (w2 & lw2 & heqw2)) ].
    + (* [w] follows the tau, and [y] can still emit eta *)
      destruct (IH happy y' eta nb ly') as (u' & e' & wu & happy').
      edestruct (eq_spec_wt y' z0 heqy' e' u' wu) as (e'' & wu' & heqe'').
      exists u', e''. split.
      * eapply wt_tau; [exact lz0 | exact wu'].
      * eapply outcome_preserved_by_eq; [exact happy' | now symmetry].
    + (* the tau was a feedback: [w] absorbs it with a blocking beta *)
      edestruct (eq_spec_wt y w2) as (e'' & wu' & heqe'').
      { now symmetry. }
      { exact wt. }
      exists (beta :: u0), e''. split.
      * eapply wt_act; [exact lw2 | exact wu'].
      * eapply outcome_preserved_by_eq; [exact happy | now symmetry].
  - (* an external move [mu] of [x] *)
    destruct (decide (mu = eta)) as [-> | neq].
    + (* the very same action: NB-DETERMINACY identifies [y] and [w] *)
      assert (heq : y ⋍ w) by (eapply nb_determinacy; eauto).
      edestruct (eq_spec_wt y w heq z u0 wt) as (e'' & wu' & heqe'').
      exists u0, e''. split; [exact wu' |].
      eapply outcome_preserved_by_eq; [exact happy | now symmetry].
    + (* a different action: NB-CONFLUENCE, [w] follows [mu] *)
      destruct (nb_confluence nb neq leta l) as (r & lr & (y' & ly' & heqy')).
      destruct (IH happy y' eta nb ly') as (u' & e' & wu & happy').
      edestruct (eq_spec_wt y' r heqy' e' u' wu) as (e'' & wu' & heqe'').
      exists (mu :: u'), e''. split.
      * eapply wt_act; [exact lr | exact wu'].
      * eapply outcome_preserved_by_eq; [exact happy' | now symmetry].
Qed.

Lemma never_outcome_nb_back (t w : T) (eta : A) :
  non_blocking eta -> t ⟶[eta] w ->
  never_outcome outcome w -> never_outcome outcome t.
Proof.
  intros nb l nw u e wu happy.
  destruct (outcome_reachable_nb_forward u t e wu happy w eta nb l)
    as (u' & e' & wu' & happy').
  eapply nw; eauto.
Qed.

(** ** The test does run its own trace, all the way to success *)

Lemma may_test_runs (r : trace A) : ∃ e, gen r ⟹[r] e /\ outcome e.
Proof.
  induction r as [ | μ r' IH ].
  - (* trace exhausted: the test computes silently to a successful state *)
    destruct may_test_can_compute as (e & le).
    exists e. split.
    + eapply wt_tau; [exact le | eapply wt_nil].
    + eapply may_test_computes_to_good; exact le.
  - destruct IH as (e & w & happy).
    destruct (may_test_next_step μ r') as (y & l & heq).
    edestruct (eq_spec_wt (gen r') y) as (z & wz & heqz).
    { now symmetry. }
    { exact w. }
    exists z. split.
    + eapply wt_act; eauto.
    + eapply outcome_preserved_by_eq; [exact happy | now symmetry].
Qed.

(** ** A trace element can be consumed from the middle of the trace

    Duplicated from Must's [f_gen_lts_mu_in_the_middle] / [..._middle'] (they only
    use [test_next_step], the determinacy above, and the OBA axioms, never
    [test_ungood] nor the deviation axiom, so the proofs carry over verbatim).
    [Forall non_blocking s1] is what makes the delay of outputs precise: the
    messages of [s1] are already floating, so anything after them is reachable. *)

Lemma gen_lts_mu_in_the_middle (s1 s2 : trace A) (μ : A) :
  Forall non_blocking s1 -> gen (s1 ++ μ :: s2) ⟶⋍[μ] gen (s1 ++ s2).
Proof.
  revert s2 μ.
  induction s1 as [| ν s']; intros s2 μ his; simpl in *.
  - eapply (may_test_next_step μ).
  - inversion his as [| ? ? nb his']; subst.
    destruct (IHs' s2 μ his') as (r & hlr & heqr).
    edestruct (may_test_next_step ν (s' ++ μ :: s2)) as (t & hlt & heqt).
    edestruct (eq_spec t r) as (u & hlu & hequ).
    { eauto with mdb. }
    destruct (nb_delay nb hlt hlu) as (v & l1 & (t' & l2 & heq')).
    exists v. split; [eassumption |].
    destruct (may_test_next_step ν (s' ++ s2)) as (w & hlw & heqw).
    eapply backwards_nb_determinacy; try eassumption.
    etransitivity; [eassumption |].
    etransitivity; [eassumption |].
    etransitivity; [eassumption | now symmetry].
Qed.

Lemma gen_lts_mu_in_the_middle' (s1 s2 : trace A) (μ : A) (t : T) :
  Forall non_blocking s1 ->
  gen (s1 ++ μ :: s2) ⟶⋍[μ] t -> t ⋍ gen (s1 ++ s2).
Proof.
  revert s2 μ t.
  induction s1 as [| ν s']; intros s2 μ t his HypTr; simpl in *.
  - destruct HypTr as (e & HypTr & equiv).
    assert (e ⋍ gen s2) by (eapply may_test_determinacy; eauto).
    etransitivity; [symmetry; exact equiv | assumption].
  - inversion his as [| ? ? nb' his']; subst.
    destruct (decide (non_blocking μ)) as [nb | not_nb].
    + assert (HypTr' : gen ((ν :: s') ++ μ :: s2) ⟶⋍[μ] gen ((ν :: s') ++ s2)).
      { eapply gen_lts_mu_in_the_middle. constructor; eauto. }
      destruct HypTr as (e & HypTr & equiv).
      destruct HypTr' as (e' & HypTr' & equiv').
      assert (e ⋍ e') by (eapply nb_determinacy; eauto).
      etransitivity; [symmetry; exact equiv |].
      etransitivity; eauto.
    + destruct HypTr as (e & HypTr & equiv).
      assert (HypTr' : gen (ν :: s' ++ μ :: s2) ⟶⋍[ν] gen (s' ++ μ :: s2)).
      { eapply may_test_next_step. }
      destruct HypTr' as (e' & HypTr' & equiv').
      assert (not_eq : μ ≠ ν) by (intro imp; rewrite imp in not_nb; contradiction).
      destruct (nb_confluence nb' not_eq HypTr' HypTr)
        as (t' & l2 & (t'' & l1 & heq)).
      edestruct (eq_spec (gen (s' ++ μ :: s2)) t' (ActExt μ)) as (v & hlv & heqv).
      { exists e'. split; [now symmetry | exact l2]. }
      assert (heq' : t' ⋍ gen (s' ++ s2)).
      { eapply IHs'; eauto. exists v. split; eauto. }
      destruct (may_test_next_step ν (s' ++ s2)) as (v' & hlv' & heqv').
      assert (final : e ⋍ gen (ν :: s' ++ s2)).
      { eapply backwards_nb_determinacy; eauto.
        etransitivity; [exact heq |].
        etransitivity; [exact heq' | now symmetry]. }
      etransitivity; [symmetry; exact equiv | exact final].
Qed.

(** ** Fatality is invariant under bisimilarity *)

Lemma never_outcome_eq (t t' : T) :
  t ⋍ t' -> never_outcome outcome t -> never_outcome outcome t'.
Proof.
  intros heq nt u e w happy.
  edestruct (eq_spec_wt t' t) as (e' & w' & heqe').
  { now symmetry. }
  { exact w. }
  eapply (nt u e'); [exact w' |].
  eapply outcome_preserved_by_eq; [exact happy | now symmetry].
Qed.

(** ** Inversion of an external action of the test

    The May counterpart of Must's [inversion_test_external_action]. Either the
    transition is a deviation — and then it is fatal — or it consumes an element
    [μ] taken from the *middle* of the trace, everything before it being
    non-blocking. [Forall non_blocking s1] is exactly the delay of outputs: the
    messages of [s1] are already floating, so [μ] is reachable past them. The
    residual test is the trace deprived of that element, [gen (s1 ++ s2)].

    Once the trace is exhausted, axiom (8) closes the base case. *)

Lemma inversion_may_test_b_external_action (s : trace A) (β' : A) (t : T) :
  gen s ⟶[β'] t -> blocking β' ->
  never_outcome outcome t \/
  Forall non_blocking s \/
  ∃ s1 s2 β, s = s1 ++ β :: s2
    /\ t ⋍ gen (s1 ++ s2)
    /\ β' = β
    /\ Forall non_blocking s1.
Proof.
  revert β' t.
  induction s as [| ν s' IH]; intros β' t l b.
  - (* the trace is exhausted: whatever [gen ε] still offers, [s] is all messages *)
    right. left. constructor.
  - destruct (decide (non_blocking ν)) as [nb | bν].
    + (* a floating message [ν] sits in front: NB-CONFLUENCE steps over it *)
      destruct (may_test_next_step ν s') as (v & lv & heqv).
      assert (not_eq : β' ≠ ν) by (intro imp; subst; contradiction).
      destruct (nb_confluence nb not_eq lv l) as (t' & l2 & (t'' & l1 & heq)).
      edestruct (eq_spec (gen s') t' (ActExt β')) as (v' & lv' & heqv').
      { exists v. split; [now symmetry | exact l2]. }
      destruct (IH β' v' lv' b)
        as [ fatal | [ his | (s1 & s2 & β & -> & equiv & -> & his) ] ].
      * (* fatal further down, and [t] only leads there through the message [ν] *)
        assert (nt' : never_outcome outcome t')
          by (eapply never_outcome_eq; [exact heqv' | exact fatal]).
        left. eapply (never_outcome_nb_back t t'' ν); [exact nb | exact l1 |].
        eapply (never_outcome_eq t' t''); [now symmetry | exact nt'].
      * (* nothing but messages below, and [ν] is one too *)
        right. left. constructor; assumption.
      * (* the element is consumed from the middle, [ν] joining the delayed prefix *)
        right. right. exists (ν :: s1), s2, β. repeat split; eauto.
        eapply gen_lts_mu_in_the_middle'.
        -- constructor; eauto.
        -- exists t. split; [exact l | reflexivity].
    + (* a blocking head: either the expected action, or a fatal deviation *)
      destruct (decide (β' = ν)) as [-> | neq].
      * right. right. exists ε, s', ν. repeat split; simpl; eauto with mdb.
        eapply may_test_follows_trace_determinacy; eauto.
      * left. eapply may_test_deviation_is_fatal; eauto.
Qed.

Lemma inversion_may_test_nb_external_action (s : trace A) (η' : A) (t : T) :
  gen s ⟶[η'] t -> non_blocking η' ->
  never_outcome outcome t \/
  Forall non_blocking s \/
  ∃ s1 s2 η, s = s1 ++ η :: s2
    /\ t ⋍ gen (s1 ++ s2)
    /\ η' = η
    /\ Forall non_blocking s1.
Proof.
  revert η' t.
  induction s as [| ν s' IH]; intros η' t l nb.
  - right. left. constructor.
  - destruct (may_test_next_step ν s') as (r & lr & heqr).
    destruct (decide (ν = η')) as [-> | not_eq].
    + (* the head itself: NB-DETERMINACY *)
      right. right. exists ε, s', η'. repeat split; simpl; eauto with mdb.
      transitivity r; [eapply (nb_determinacy nb l lr) | exact heqr].
    + destruct (decide (non_blocking ν)) as [nbν | bν].
      * (* [ν] is a floating message: step over it and recurse *)
        destruct (nb_confluence nb not_eq l lr)
          as (t' & l2 & (t'' & l1 & heq)).
        edestruct (eq_spec (gen s') t'' (ActExt η')) as (v & lv & heqv).
        { exists r. split; [now symmetry | exact l1]. }
        destruct (IH η' v lv nb)
          as [ fatal | [ his | (s1 & s2 & η & -> & equiv & -> & his) ] ].
        -- assert (nt'' : never_outcome outcome t'')
             by (eapply never_outcome_eq; [exact heqv | exact fatal]).
           left. eapply (never_outcome_nb_back t t' ν); [exact nbν | exact l2 |].
           eapply never_outcome_eq; [exact heq | exact nt''].
        -- right. left. constructor; assumption.
        -- right. right. exists (ν :: s1), s2, η. repeat split; eauto.
           eapply gen_lts_mu_in_the_middle'.
           ++ constructor; eauto.
           ++ exists t. split; [exact l | reflexivity].
      * (* a blocking head and [η' ≠ ν] : a deviation, hence fatal *)
        left. eapply may_test_deviation_is_fatal; eauto.
Qed.

Lemma inversion_may_test_external_action (s : trace A) (μ' : A) (t : T) :
  gen s ⟶[μ'] t ->
  never_outcome outcome t \/
  Forall non_blocking s \/
  ∃ s1 s2 μ, s = s1 ++ μ :: s2
    /\ t ⋍ gen (s1 ++ s2)
    /\ μ' = μ
    /\ Forall non_blocking s1.
Proof.
  intro l. destruct (decide (non_blocking μ')) as [nb | b].
  - eapply inversion_may_test_nb_external_action; eauto.
  - eapply inversion_may_test_b_external_action; eauto.
Qed.

(** ** Inversion of a silent move of the test

    Three ways for [gen s] to compute on its own.

    - It reaches success. Note this does *not* force [s = ε]: the trailing
      [𝛕 • ①] may fire while messages are still pending — but then, and only then,
      every element left in [s] is a floating message ([Forall non_blocking s]).
    - It deviates, and dies.
    - It talks to *itself*: a floating message [η] is consumed by one of its own
      later inputs [μ], with [dual μ η]. That is the second disjunct of NB-TAU,
      and it consumes a whole *pair* of trace elements at once — the May
      counterpart of Must's [inversion_test_tau_action]. *)

Lemma inversion_may_test_tau_action (s : trace A) (t : T) :
  gen s ⟶ t ->
  never_outcome outcome t \/
  Forall non_blocking s \/
  ∃ η μ s1 s2 s3,
    s = s1 ++ [η] ++ s2 ++ [μ] ++ s3
    /\ t ⋍ gen (s1 ++ s2 ++ s3)
    /\ non_blocking η
    /\ Forall non_blocking s1
    /\ Forall non_blocking s2
    /\ dual μ η.
Proof.
  revert t.
  induction s as [| μ' s' IH]; intros t l.
  - (* the trace is exhausted *)
    right. left. constructor.
  - destruct (decide (non_blocking μ')) as [nb | bμ'].
    + destruct (may_test_next_step μ' s') as (r & lr & heqr).
      destruct (nb_tau nb lr l)
        as [ (r1 & l1 & (r2 & l2 & heq)) | (μ & duo & (r'' & l'' & heq'')) ].
      * (* the silent move happens under the message [μ'], which stays pending *)
        edestruct (eq_spec (gen s') r1 τ) as (v & lv & heqv).
        { exists r. split; [now symmetry | exact l1]. }
        destruct (IH v lv)
          as [ fatal
             | [ his
               | (η & μ & s1 & s2 & s3 & -> & equiv & hη & his1 & his2 & duo) ] ].
        -- (* fatal below, and [t] only reaches it by emitting [μ'] *)
           left.
           eapply (never_outcome_nb_back t r2 μ'); [exact nb | exact l2 |].
           eapply (never_outcome_eq v r2); [| exact fatal].
           etransitivity; [exact heqv | now symmetry].
        -- (* nothing but messages below, and [μ'] is one too *)
           right. left. constructor; assumption.
        -- (* a self-communication below: [μ'] joins the floating prefix *)
           right. right. exists η, μ, (μ' :: s1), s2, s3. simpl.
           split; [reflexivity |].
           split.
           { destruct (may_test_next_step μ' (s1 ++ s2 ++ s3)) as (w & lw & heqw).
             eapply backwards_nb_determinacy; [exact nb | exact l2 | exact lw |].
             etransitivity; [exact heq |].
             etransitivity; [symmetry; exact heqv |].
             etransitivity; [exact equiv | now symmetry]. }
           split; [exact hη |].
           split; [constructor; assumption |].
           split; [exact his2 | exact duo].
      * (* the message [μ'] is swallowed by one of the test's own later inputs *)
        edestruct (eq_spec (gen s') r'' (ActExt μ)) as (t0 & lt0 & heqt0).
        { exists r. split; [now symmetry | exact l'']. }
        destruct (inversion_may_test_external_action s' μ t0 lt0)
          as [ fatal | [ his | (s1 & s2 & μ'' & -> & equiv & -> & his) ] ].
        -- left.
           eapply (never_outcome_eq t0 t); [| exact fatal].
           etransitivity; [exact heqt0 | exact heq''].
        -- right. left. constructor; assumption.
        -- right. right. exists μ', μ'', ε, s1, s2. simpl.
           split; [reflexivity |].
           split.
           { etransitivity; [symmetry; exact heq'' |].
             etransitivity; [symmetry; exact heqt0 | exact equiv]. }
           split; [exact nb |].
           split; [constructor |].
           split; [exact his | exact duo].
    + (* a blocking head: the test cannot compute on its own without dying *)
      left. eapply may_test_tau_on_blocking_is_fatal; eauto.
Qed.

End May_tests.
