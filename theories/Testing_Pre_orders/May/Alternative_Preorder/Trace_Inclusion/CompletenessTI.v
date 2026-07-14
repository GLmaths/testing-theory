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
From TestingTheory Require Import ActTau gLts Bisimulation Lts_OBA Lts_OBA_FB Lts_FW WeakTransitions
    Testing_Predicate InteractionBetweenLts FiniteImageLTS Lts_Finite_Output_Chain
    MultisetLTSConstruction ForwarderConstruction May LiftMay DefinitionTI.

Import ListNotations.

(** * Completeness of the trace-inclusion preorder for May

      [p ⊑ₘₐᵧ q  →  p ≼ₜᵢ q]   (for forwarders)

    Given a trace [s] of [p], we exhibit a test that [p] passes and that forces
    [q] to perform [s] too.  As for Must, that test is not built here: it is
    *axiomatised* by a generator [gen : trace A -> T] ([may_test_spec] below).

    The file has three parts.

    - The test side: what [gen s] can do.  Two inversion lemmas
      ([inversion_may_test_external_action], [inversion_may_test_tau_action])
      account for every move of the test, mirroring Must's.
    - The process side: what a forwarder can absorb ([fw_insert_pair],
      [fw_anticipate_inputs]).  This is the only place the forwarder axioms are
      used — and they are used in full, [gLtsCNenabled] would not do.
    - [completeness_core], which meets the two. *)

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

(** * The process side: what a forwarder can absorb

    Everything the test "misses" — a pair it swallowed by talking to itself, an
    input it postponed — must be filled back in on the process side. That is
    exactly what the forwarder axioms are for, and this is the *only* place where
    they are used.

    [gLtsCNenabled] would not be enough: it gives the outgoing leg of [boomerang]
    ("some [β]-transition exists") but not the return leg [q1 ⟶[η] q], which is
    what says that the absorbed message is *kept* — and hence that [q1] can still
    do whatever [q] could. A CN-enabled LTS that *discards* its inputs satisfies
    the axiom and breaks both lemmas below. *)

Section Forwarder_absorption.

Context `{gLtsObaFWQ : @gLtsObaFW Q A H gLtsEqQ gLtsObaQ}.

(** ** A forwarder can insert a dual pair anywhere

    BOOMERANG receives [co η] and keeps it; [delay_wt_non_blocking_action] carries
    the pending [η] across the whole run [I]; then it is emitted. The run in
    between is untouched, so the pair can be wrapped around any segment. *)

Lemma fw_insert_pair (q q' : Q) (η : A) (I v : trace A) :
  non_blocking η -> q ⟹[I ++ v] q' ->
  ∃ q'', q ⟹[co η :: I ++ η :: v] q''.
Proof.
  intros nb w.
  assert (duo : dual (co η) η).
  { symmetry. exact (proj2_sig (exists_dual η)). }
  destruct (boomerang q η (co η)) as (q1 & Hb).
  destruct (Hb nb duo) as (lβ & lη).
  eapply wt_split in w as (qa & w1 & w2).
  assert (lsc : q1 ⟶⋍[η] q) by (exists q; split; [exact lη | reflexivity]).
  destruct (delay_wt_non_blocking_action nb lsc w1)
    as (t & wt1 & (ta & lta & heqta)).
  edestruct (eq_spec_wt qa ta) as (q'' & wq'' & heqq'').
  { now symmetry. }
  { exact w2. }
  exists q''.
  eapply wt_act; [exact lβ |].
  eapply wt_concat; [exact wt1 |].
  eapply wt_act; [exact lta | exact wq''].
Qed.

(** ** A forwarder can anticipate an input

    Here the return leg of BOOMERANG is not enough on its own: absorbing [β] early
    leaves the message [η] pending, and the run still contains the *later* [β] we
    were trying to move. FWD-FEEDBACK is what annihilates the two — the buffered
    message is fed back internally instead of leaving and coming back. *)

Lemma fw_anticipate_input (q q' : Q) (α β η : A) (u : trace A) :
  non_blocking η -> dual β η ->
  q ⟹[α :: β :: u] q' -> ∃ q'', q ⟹[β :: α :: u] q''.
Proof.
  intros nb duo w.
  destruct (boomerang q η β) as (q1 & Hb).
  destruct (Hb nb duo) as (lβ & lη).
  (* peel the run apart: q ⟹{α} qa ⟹{β} qb ⟹[u] q' *)
  eapply wt_pop in w as (qa & wα & w).
  eapply wt_pop in w as (qb & wβ & wu).
  (* absorb β up front, then carry the pending η across the α-step *)
  assert (lsc : q1 ⟶⋍[η] q) by (exists q; split; [exact lη | reflexivity]).
  destruct (delay_wt_non_blocking_action nb lsc wα)
    as (t & wt1 & (ta & lta & heqta)).
  (* replay the β-step from [ta] *)
  edestruct (eq_spec_wt qa ta) as (z & wz & heqz).
  { now symmetry. }
  { exact wβ. }
  eapply wt_decomp_one in wz as (x & y & wx & lxy & wy).
  (* carry the pending η across the silent prefix of that β-step *)
  assert (lsc2 : t ⟶⋍[η] ta) by (exists ta; split; [exact lta | reflexivity]).
  destruct (delay_wt_non_blocking_action nb lsc2 wx)
    as (t2 & wt2 & (x' & lx' & heqx')).
  (* transport the β-step onto [x'] *)
  edestruct (eq_spec x' y (ActExt β)) as (y' & ly' & heqy').
  { exists x. split; [now symmetry | exact lxy]. }
  (* FWD-FEEDBACK: the pending η meets that β and they cancel out *)
  assert (feed : ∃ y'', t2 ⟹ y'' /\ y'' ⋍ y').
  { destruct (fwd_feedback nb duo lx' ly') as [ (y0 & lτ & heq0) | heq0 ].
    - exists y0. split; [eapply wt_tau; [exact lτ | eapply wt_nil] | exact heq0].
    - exists t2. split; [eapply wt_nil | exact heq0]. }
  destruct feed as (y'' & wy'' & heqy'').
  (* and the rest of the run replays from there *)
  edestruct (eq_spec_wt qb z) as (r1 & wr1 & heqr1).
  { now symmetry. }
  { exact wu. }
  assert (wyu : y ⟹[u] r1) by (eapply wt_push_nil_left; [exact wy | exact wr1]).
  edestruct (eq_spec_wt y y') as (r2 & wr2 & heqr2).
  { now symmetry. }
  { exact wyu. }
  edestruct (eq_spec_wt y' y'') as (r3 & wr3 & heqr3).
  { now symmetry. }
  { exact wr2. }
  assert (wA : q1 ⟹[[α]] y'').
  { eapply wt_push_nil_right; [| exact wy''].
    eapply wt_push_nil_right; [exact wt1 | exact wt2]. }
  exists r3.
  eapply wt_act; [exact lβ |].
  eapply (wt_concat q1 y'' r3 [α] u); [exact wA | exact wr3].
Qed.

(** ** ... hence a whole block of them *)

Lemma fw_anticipate_inputs (q q' : Q) (α : A) (I v : trace A) :
  Forall exist_co_nba I ->
  q ⟹[α :: I ++ v] q' -> ∃ q'', q ⟹[I ++ α :: v] q''.
Proof.
  revert q q' α v.
  induction I as [| β I' IH]; intros q q' α v hI w; simpl in *.
  - exists q'. exact w.
  - inversion hI as [| ? ? (η & nb & duo) hI']; subst.
    destruct (fw_anticipate_input q q' α β η (I' ++ v) nb duo w) as (q0 & w0).
    eapply wt_pop in w0 as (q1 & w1 & w2).
    destruct (IH q1 q0 α v hI' w2) as (q2 & w3).
    exists q2. eapply wt_push_left; [exact w1 | exact w3].
Qed.

(** ** The co-trace of a non-blocking trace is a trace of inputs *)

Lemma Forall_exist_co_nba_of_non_blocking (s : trace A) :
  Forall non_blocking s -> Forall exist_co_nba (coₜ s).
Proof.
  induction s as [| η s' IH]; intro his; simpl.
  - constructor.
  - inversion his as [| ? ? nb his']; subst.
    constructor.
    + exists η. split; [exact nb |].
      symmetry. exact (proj2_sig (exists_dual η)).
    + eapply IH; exact his'.
Qed.

Lemma Forall_exist_co_nba_of_co (s : trace A) :
  Forall non_blocking (coₜ s) -> Forall exist_co_nba s.
Proof.
  induction s as [| μ s' IH]; intro his; simpl in *.
  - constructor.
  - inversion his as [| ? ? nb his']; subst.
    constructor.
    + exists (co μ). split; [exact nb | exact (proj2_sig (exists_dual μ))].
    + eapply IH; exact his'.
Qed.

(** ** A forwarder can always run a whole block of inputs — BOOMERANG, plainly *)

Lemma fw_run_inputs (I : trace A) :
  Forall exist_co_nba I -> ∀ q : Q, ∃ q', q ⟹[I] q'.
Proof.
  induction I as [| β I' IH]; intros hI q.
  - exists q. eapply wt_nil.
  - inversion hI as [| ? ? (η & nb & duo) hI']; subst.
    destruct (boomerang q η β) as (q1 & Hb).
    destruct (Hb nb duo) as (lβ & _).
    destruct (IH hI' q1) as (q' & w).
    exists q'. eapply wt_act; [exact lβ | exact w].
Qed.

End Forwarder_absorption.

(** * Completeness *)

Section Completeness_ti.

Context `{gLtsObaFWQ : @gLtsObaFW Q A H gLtsEqQ gLtsObaQ}.
Context `{gLtsT : !gLtsEq T H, gLtsObaT : !gLtsOba T, !Testing_Predicate outcome _}.
Context {QInter : Prop_of_Inter Q T A dual}.
Context {gen : trace A -> T} {gen_spec : may_test_spec gen}.

(** A test that some process may pass can obviously still reach success. *)

Lemma never_outcome_false_of_may (q : Q) (t : T) :
  q may_pass t -> ¬ never_outcome outcome t.
Proof.
  intros hm nt.
  eapply may_to_wt in hm as (s0 & q0 & e & _ & wc & happy).
  eapply nt; eauto.
Qed.

(** ** The core of completeness

    If [q] passes the test attesting [s], then [q] really does perform [s].

    The induction on [may] meets the test at every one of its moves, and each is
    answered by one of the two inversion lemmas:

    - the test synchronises: the action is pulled from the middle of the trace,
      past a prefix of postponed outputs. Those are *inputs* on the process side,
      and [fw_anticipate_inputs] moves them back in front.
    - the test computes silently: either it swallowed a dual pair by talking to
      itself — and [fw_insert_pair] puts that pair back into the process run, by
      BOOMERANG — or it succeeded with messages still pending, and then everything
      left of [s] is an input, which [fw_run_inputs] performs outright.
    - the test deviates: impossible, [q] passes it, so success is still reachable.
    - the test is already successful: impossible, [gen] is never good. *)

Lemma completeness_core (q : Q) (t : T) :
  q may_pass t -> ∀ s, t ⋍ gen (coₜ s) -> ∃ q', q ⟹[s] q'.
Proof.
  intro hm.
  induction hm as [ q t happy
                  | q t q0 nh pt hm IH
                  | q t t' nh et hm IH
                  | q t q0 μ1 t' μ2 nh inter trS trC hm IH ];
    intros s heq.
  - (* the test is good — impossible: [gen] is never good *)
    exfalso. eapply (may_test_ungood (coₜ s)).
    eapply outcome_preserved_by_eq; [exact happy | exact heq].
  - (* the process moves on its own *)
    destruct (IH s heq) as (q' & w).
    exists q'. eapply wt_tau; [exact pt | exact w].
  - (* the test moves on its own *)
    edestruct (eq_spec (gen (coₜ s)) t' τ) as (t'' & l'' & heq'').
    { exists t. split; [now symmetry | exact et]. }
    destruct (inversion_may_test_tau_action (coₜ s) t'' l'')
      as [ fatal
         | [ his
           | (η & μ & s1 & s2 & s3 & eqs & equiv & hη & his1 & his2 & duo) ] ].
    + (* a deviation: but [q] passes the test, so success is still reachable *)
      exfalso. eapply (never_outcome_false_of_may q t'); [exact hm |].
      eapply (never_outcome_eq t'' t'); [exact heq'' | exact fatal].
    + (* what is left of [s] is all inputs: the forwarder performs them outright *)
      eapply (fw_run_inputs s).
      eapply Forall_exist_co_nba_of_co; exact his.
    + (* the test talked to itself: give the pair back to the forwarder *)
      assert (heta : η = co μ) by (eapply unique_nb; exact duo).
      destruct (IH (coₜ (s1 ++ s2 ++ s3))) as (q' & w).
      { rewrite <- dual_trace_is_involutive.
        etransitivity; [symmetry; exact heq'' | exact equiv]. }
      rewrite map_app in w. rewrite map_app in w.
      eapply wt_split in w as (qa & wa & wb).
      destruct (fw_insert_pair qa q' η (coₜ s2) (coₜ s3) hη wb) as (qc & wc).
      exists qc.
      assert (hs : s = coₜ s1 ++ (co η :: coₜ s2 ++ η :: coₜ s3)).
      { transitivity (coₜ (coₜ s)); [eapply dual_trace_is_involutive |].
        rewrite eqs. repeat rewrite map_app. simpl.
        rewrite <- heta. reflexivity. }
      rewrite hs.
      eapply wt_concat; [exact wa | exact wc].
  - (* the process and the test synchronise *)
    edestruct (eq_spec (gen (coₜ s)) t' (ActExt μ2)) as (t'' & l'' & heq'').
    { exists t. split; [now symmetry | exact trC]. }
    destruct (inversion_may_test_external_action (coₜ s) μ2 t'' l'')
      as [ fatal | [ his | (s1 & s2 & μ & eqs & equiv & -> & his) ] ].
    + exfalso. eapply (never_outcome_false_of_may q0 t'); [exact hm |].
      eapply (never_outcome_eq t'' t'); [exact heq'' | exact fatal].
    + (* same escape as above: everything left of [s] is an input *)
      eapply (fw_run_inputs s).
      eapply Forall_exist_co_nba_of_co; exact his.
    + assert (hm2 : μ = co μ1) by (eapply unique_nb; exact inter).
      assert (hmu : co μ = μ1)
        by (rewrite hm2; symmetry; eapply dual_is_involutive).
      destruct (IH (coₜ (s1 ++ s2))) as (q' & w).
      { rewrite <- dual_trace_is_involutive.
        etransitivity; [symmetry; exact heq'' | exact equiv]. }
      rewrite map_app in w.
      assert (w2 : q ⟹[μ1 :: coₜ s1 ++ coₜ s2] q')
        by (eapply wt_act; [exact trS | exact w]).
      destruct (fw_anticipate_inputs q q' μ1 (coₜ s1) (coₜ s2)
                  (Forall_exist_co_nba_of_non_blocking s1 his) w2) as (q'' & w3).
      exists q''.
      assert (hs : s = coₜ s1 ++ μ1 :: coₜ s2).
      { transitivity (coₜ (coₜ s)); [eapply dual_trace_is_involutive |].
        rewrite eqs. rewrite map_app. simpl. rewrite hmu. reflexivity. }
      rewrite hs. exact w3.
Qed.

End Completeness_ti.

(** ** Completeness, for forwarders *)

Theorem completeness_ti_fw `{
  gLtsObaFWP : @gLtsObaFW P A H gLtsEqP gLtsObaP,
  gLtsObaFWQ : @gLtsObaFW Q A H gLtsEqQ gLtsObaQ,
  gLtsT : !gLtsEq T H, gLtsObaT : !gLtsOba T, !Testing_Predicate outcome _}

  {_ : Prop_of_Inter P T A dual}
  {_ : Prop_of_Inter Q T A dual}

  {gen : trace A -> T} {gspec : may_test_spec gen}

  (p : P) (q : Q) :
  p ⊑ₘₐᵧ q -> p ≼ₜᵢ q.
Proof.
  intros hctx s (p' & wp).
  (* [p] follows [s], so it passes the test attesting [s] *)
  destruct (may_test_runs (coₜ s)) as (e & we & happy).
  assert (hmp : p may_pass (gen (coₜ s))) by (eapply wt_to_may; eauto).
  eapply hctx in hmp.
  (* hence so does [q] — and then [q] really did perform [s] *)
  eapply (completeness_core q (gen (coₜ s)) hmp s).
  reflexivity.
Qed.

(** ** Completeness, for feedback LTSs, through the forwarder construction

    An LTS with only the feedback axioms is not a forwarder, but [toFW] makes one
    of it ([toFWObaFW]) and the construction is transparent for [may]
    ([lift_fw_ctx_pre]).  The trace inclusion is then read on the *lifted*
    processes — which is the right statement: on the raw LTS it would be false,
    since e.g. [𝟘] and [a?.𝟘] are May-equivalent while their raw traces differ. *)

Theorem completeness_ti_fb `{
    @gLtsObaFB P A H gLtsEqP gLtsObaP, !FiniteOutputChain_LtsOba P, !FiniteImagegLts P A,
    @gLtsObaFB Q A H gLtsEqQ gLtsObaQ, !FiniteOutputChain_LtsOba Q, !FiniteImagegLts Q A,
    @gLtsObaFB T A H gLtsEqT gLtsObaT, !FiniteOutputChain_LtsOba T, !Testing_Predicate outcome _}

  {_ : Prop_of_Inter P (MO A) A fw_inter}
  {_ : Prop_of_Inter (P * MO A) T A dual}
  {_ : Prop_of_Inter P T A dual}

  {_ : Prop_of_Inter Q (MO A) A fw_inter}
  {_ : Prop_of_Inter (Q * MO A) T A dual}
  {_ : Prop_of_Inter Q T A dual}

  {gen : trace A -> T} {gspec : may_test_spec gen}

  (p : P) (q : Q) :
  p ⊑ₘₐᵧ q -> (p, ∅ : MO A) ≼ₜᵢ (q, ∅ : MO A).
Proof.
  intro hctx.
  eapply completeness_ti_fw.
  eapply (proj1 (lift_fw_ctx_pre p q)). exact hctx.
Qed.
