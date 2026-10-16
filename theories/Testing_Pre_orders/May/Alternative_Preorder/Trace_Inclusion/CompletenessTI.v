(* begin hide *)
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
(* end hide *)

From Stdlib.Lists Require Import List.
From stdpp Require Import base decidable.
From TestingTheory Require Import ActTau gLts Bisimulation Lts_OBA Lts_OBA_FB Lts_FW WeakTransitions
    Testing_Predicate InteractionBetweenLts FiniteImageLTS Lts_Finite_Non_Blocking_Chain
    MultisetLTSConstruction ForwarderConstruction May LiftMay DefinitionTI MayTestSpec.

Import ListNotations.
(** **** Completeness of the trace-inclusion preorder for May *)

Section Forwarder_absorption.

Context `{gLtsObaFWQ : @gLtsObaFW Q A H gLtsEqQ gLtsObaQ}.

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

(** **** A forwarder can anticipate an input *)

Lemma fw_anticipate_input (q q' : Q) (𝜆 β η : A) (u : trace A) :
  non_blocking η -> dual β η ->
  q ⟹[𝜆 :: β :: u] q' -> ∃ q'', q ⟹[β :: 𝜆 :: u] q''.
Proof.
  intros nb duo w.
  destruct (boomerang q η β) as (q1 & Hb).
  destruct (Hb nb duo) as (lβ & lη).
  eapply wt_pop in w as (qa & w𝜆 & w).
  eapply wt_pop in w as (qb & wβ & wu).
  assert (lsc : q1 ⟶⋍[η] q) by (exists q; split; [exact lη | reflexivity]).
  destruct (delay_wt_non_blocking_action nb lsc w𝜆)
    as (t & wt1 & (ta & lta & heqta)).
  edestruct (eq_spec_wt qa ta) as (z & wz & heqz).
  { now symmetry. }
  { exact wβ. }
  eapply wt_decomp_one in wz as (x & y & wx & lxy & wy).
  assert (lsc2 : t ⟶⋍[η] ta) by (exists ta; split; [exact lta | reflexivity]).
  destruct (delay_wt_non_blocking_action nb lsc2 wx)
    as (t2 & wt2 & (x' & lx' & heqx')).
  edestruct (eq_spec x' y (ActExt β)) as (y' & ly' & heqy').
  { exists x. split; [now symmetry | exact lxy]. }
  assert (feed : ∃ y'', t2 ⟹ y'' /\ y'' ⋍ y').
  { destruct (fwd_feedback nb duo lx' ly') as [ (y0 & lτ & heq0) | heq0 ].
    - exists y0. split; [eapply wt_tau; [exact lτ | eapply wt_nil] | exact heq0].
    - exists t2. split; [eapply wt_nil | exact heq0]. }
  destruct feed as (y'' & wy'' & heqy'').
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
  assert (wA : q1 ⟹[[𝜆]] y'').
  { eapply wt_push_nil_right; [| exact wy''].
    eapply wt_push_nil_right; [exact wt1 | exact wt2]. }
  exists r3.
  eapply wt_act; [exact lβ |].
  eapply (wt_concat q1 y'' r3 [𝜆] u); [exact wA | exact wr3].
Qed.

Lemma fw_anticipate_inputs (q q' : Q) (𝜆 : A) (I v : trace A) :
  Forall exist_co_nba I ->
  q ⟹[𝜆 :: I ++ v] q' -> ∃ q'', q ⟹[I ++ 𝜆 :: v] q''.
Proof.
  revert q q' 𝜆 v.
  induction I as [| β I' IH]; intros q q' 𝜆 v hI w; simpl in *.
  - exists q'. exact w.
  - inversion hI as [| ? ? (η & nb & duo) hI']; subst.
    destruct (fw_anticipate_input q q' 𝜆 β η (I' ++ v) nb duo w) as (q0 & w0).
    eapply wt_pop in w0 as (q1 & w1 & w2).
    destruct (IH q1 q0 𝜆 v hI' w2) as (q2 & w3).
    exists q2. eapply wt_push_left; [exact w1 | exact w3].
Qed.

(** **** The co-trace of a non-blocking trace is a trace of inputs *)

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

(** ***** Completeness *)

Section Completeness_ti.

Context `{gLtsObaFWQ : @gLtsObaFW Q A H gLtsEqQ gLtsObaQ}.
Context {unique_nb : UniqueDual A}.
Context `{gLtsT : !gLtsEq T H, gLtsObaT : !gLtsOba T _, !Testing_Predicate outcome _}.
Context {QInter : Prop_of_Inter Q T A A dual}.
Context {gen : trace A -> T} {gen_spec : may_test_spec gen}.


Lemma never_outcome_false_of_may (q : Q) (t : T) :
  q may_pass t -> ¬ never_outcome outcome t.
Proof.
  intros hm.
  induction hm as [ p t happy | p t p' nh pt hm IH | p t t' nh et hm IH
                  | p t p' μ1 t' μ2 nh inter trS trC hm IH ]; intro nt.
  - exact (nt [] t (wt_nil t) happy).
  - exact (IH nt).
  - apply IH. intros u t2 w. exact (nt u t2 (wt_tau u t t' t2 et w)).
  - apply IH. intros u t2 w. exact (nt (μ2 :: u) t2 (wt_act μ2 u t t' t2 trC w)).
Qed.

(** **** The core of completeness *)

Lemma completeness_core (q : Q) (t : T) :
  q may_pass t -> ∀ s, t ⋍ gen (coₜ s) -> ∃ q', q ⟹[s] q'.
Proof.
  intro hm.
  induction hm as [ q t happy
                  | q t q0 nh pt hm IH
                  | q t t' nh et hm IH
                  | q t q0 μ1 t' μ2 nh inter trS trC hm IH ];
    intros s heq.
  - exfalso. eapply (may_test_ungood (coₜ s)).
    eapply outcome_preserved_by_eq; [exact happy | exact heq].
  - destruct (IH s heq) as (q' & w).
    exists q'. eapply wt_tau; [exact pt | exact w].
  - edestruct (eq_spec (gen (coₜ s)) t' τ) as (t'' & l'' & heq'').
    { exists t. split; [now symmetry | exact et]. }
    destruct (inversion_may_test_tau_action (coₜ s) t'' l'')
      as [ fatal
         | [ his
           | (η & μ & s1 & s2 & s3 & eqs & equiv & hη & his1 & his2 & duo) ] ].
    + exfalso. eapply (never_outcome_false_of_may q t'); [exact hm |].
      eapply (never_outcome_eq t'' t'); [exact heq'' | exact fatal].
    + eapply (fw_run_inputs s).
      eapply Forall_exist_co_nba_of_co; exact his.
    + assert (heta : η = co μ) by (eapply unique_nb; exact duo).
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
  - edestruct (eq_spec (gen (coₜ s)) t' (ActExt μ2)) as (t'' & l'' & heq'').
    { exists t. split; [now symmetry | exact trC]. }
    destruct (inversion_may_test_external_action (coₜ s) μ2 t'' l'')
      as [ fatal | [ his | (s1 & s2 & μ & eqs & equiv & -> & his) ] ].
    + exfalso. eapply (never_outcome_false_of_may q0 t'); [exact hm |].
      eapply (never_outcome_eq t'' t'); [exact heq'' | exact fatal].
    + eapply (fw_run_inputs s).
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

(** ***** Completeness, for forwarders *)

Theorem completeness_ti_fw `{
  gLtsObaFWP : @gLtsObaFW P A H gLtsEqP gLtsObaP,
  gLtsObaFWQ : @gLtsObaFW Q A H gLtsEqQ gLtsObaQ,
  gLtsT : !gLtsEq T H, gLtsObaT : !gLtsOba T _, !Testing_Predicate outcome _} {unique_nb : UniqueDual A}

  {_ : Prop_of_Inter P T A A dual}
  {_ : Prop_of_Inter Q T A A dual}

  {gen : trace A -> T} {gspec : may_test_spec gen}

  (p : P) (q : Q) :
  p ⊑ₘₐᵧ q -> p ≼ₜᵢ q.
Proof.
  intros hctx s (p' & wp).
  destruct (may_test_runs (coₜ s)) as (e & we & happy).
  assert (hmp : p may_pass (gen (coₜ s))) by (eapply wt_to_may; eauto).
  eapply hctx in hmp.
  eapply (completeness_core q (gen (coₜ s)) hmp s).
  reflexivity.
Qed.

(** ***** Completeness, for feedback LTSs *)

Theorem completeness_ti_fb `{
    @gLtsObaFB P A H gLtsEqP gLtsObaP, !FiniteNonBlockingChain_LtsOba P, !FiniteImagegLts P A,
    @gLtsObaFB Q A H gLtsEqQ gLtsObaQ, !FiniteNonBlockingChain_LtsOba Q, !FiniteImagegLts Q A,
    @gLtsObaFB T A H gLtsEqT gLtsObaT, !FiniteNonBlockingChain_LtsOba T, !Testing_Predicate outcome _} {unique_nb : UniqueDual A}

  {_ : Prop_of_Inter P (MO A) A A fw_inter}
  {_ : Prop_of_Inter (P * MO A) T A A dual}
  {_ : Prop_of_Inter P T A A dual}

  {_ : Prop_of_Inter Q (MO A) A A fw_inter}
  {_ : Prop_of_Inter (Q * MO A) T A A dual}
  {_ : Prop_of_Inter Q T A A dual}

  {gen : trace A -> T} {gspec : may_test_spec gen}

  (p : P) (q : Q) :
  p ⊑ₘₐᵧ q -> (p, ∅ : MO A) ≼ₜᵢ (q, ∅ : MO A).
Proof.
  intro hctx.
  eapply completeness_ti_fw.
  eapply (proj1 (lift_fw_ctx_pre p q)). exact hctx.
Qed.