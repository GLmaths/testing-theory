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
    MultisetLTSConstruction ForwarderConstruction May LiftMay DefinitionTI MayTestSpec.

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

(** [never_outcome], [may_test_spec], and its [May_tests] section
    (determinacy, inversion lemmas, [may_test_runs], etc.) now live in
    [MayTestSpec.v], shared with [CompletenessTIco.v]. *)

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
