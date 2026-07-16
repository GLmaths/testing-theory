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
    coWeakTransition Testing_Predicate InteractionBetweenLts FiniteImageLTS Lts_Finite_Output_Chain
    MultisetLTSConstruction ForwarderConstruction May LiftMay MayTestSpec CompletenessTI DefinitionTIco.

(** * Completeness of the co-trace-inclusion preorder for May

      [p ⊑ₘₐᵧ q  →  p ≼꜀ₒ₋ₜᵢ q]   (for forwarders)

    [completeness_core_co] is a genuine induction on [may], proven
    directly against [gen s] (the test performing the literal trace
    [s], per [DefinitionTIco.v]'s convention: the duality lives on the
    *process*, never on the test) and concluding [q ⟹ᶜᵒ[s] q'] — not a
    wrapper around [completeness_core]/[completeness_ti_fw]. It reuses
    the shared, trace-agnostic sub-machinery of [CompletenessTI.v]
    ([may_test_spec], the [May_tests] and [Forwarder_absorption]
    sections — [inversion_may_test_tau_action],
    [inversion_may_test_external_action], [fw_insert_pair],
    [fw_anticipate_inputs], [fw_run_inputs], [never_outcome_false_of_may],
    [never_outcome_eq], [EquivDef_inv2]), none of which depend on
    [coₜ]/[unique_nb] in their own statements — but never calls
    [completeness_core]/[completeness_ti_fw]/[completeness_ti_fb]
    themselves.

    Where the plain [completeness_core] peels a *canonical* dual
    ([coₜ]/[unique_nb]) off the test's own literal co-trace, this
    proof works the other way: it builds a plain (⟹[·]) witness for
    the *process* piecewise (via [cowt_split]/[cowt_to_wt_dual] on the
    induction hypothesis, [fw_insert_pair]/[fw_anticipate_inputs] to
    absorb/reorder it against the forwarder axioms), then packages the
    whole reassembled witness back into a co-answer in one
    [wt_to_cowt_dual] call, with an explicit [Forall2 dual] witness
    built compositionally ([ForAllHelper.Forall2_app]/[_cons]) — never
    picking a canonical dual. *)

Section Completeness_ti_co.

Context `{gLtsObaFWQ : @gLtsObaFW Q A H gLtsEqQ gLtsObaQ}.
Context `{gLtsT : !gLtsEq T H, gLtsObaT : !gLtsOba T, !Testing_Predicate outcome _}.
Context {QInter : Prop_of_Inter Q T A dual}.
Context {gen : trace A -> T} {gen_spec : may_test_spec gen}.

(** ** The core of completeness, co-native

    If [q] passes the test attesting [s] (literally), then [q] really
    does co-answer [s]. Mirrors [completeness_core]'s case-by-case
    structure but, since the test performs [s] literally (no [coₜ]
    detour), each inversion lemma already hands back genuine pieces of
    [s] itself — no canonical-dual bookkeeping needed to relate them
    back to [s]. *)

Lemma completeness_core_co (q : Q) (t : T) :
  q may_pass t -> ∀ s, t ⋍ gen s -> ∃ q', q ⟹ᶜᵒ[s] q'.
Proof.
  intro hm.
  induction hm as [ q t happy
                  | q t q0 nh pt hm IH
                  | q t t' nh et hm IH
                  | q t q0 μ1 t' μ2 nh inter trS trC hm IH ];
    intros s heq.
  - (* the test is good — impossible: [gen] is never good *)
    exfalso. eapply (may_test_ungood s).
    eapply outcome_preserved_by_eq; [exact happy | exact heq].
  - (* the process moves on its own *)
    destruct (IH s heq) as (q' & w).
    exists q'. eapply cowt_tau; [exact pt | exact w].
  - (* the test moves on its own *)
    edestruct (eq_spec (gen s) t' τ) as (t'' & l'' & heq'').
    { exists t. split; [now symmetry | exact et]. }
    destruct (inversion_may_test_tau_action s t'' l'')
      as [ fatal | [ his | (η & μ & s1 & s2 & s3 & eqs & equiv & hη & his1 & his2 & duo) ] ].
    + (* a deviation: but [q] passes the test, so success is still reachable *)
      exfalso. eapply (never_outcome_false_of_may q t'); [exact hm |].
      eapply (never_outcome_eq t'' t'); [exact heq'' | exact fatal].
    + (* what is left of [s] is all outputs: [q] co-answers them via BOOMERANG *)
      destruct (fw_run_inputs (coₜ s) (Forall_exist_co_nba_of_non_blocking s his) q) as (q' & w).
      assert (hd : ForAllHelper.Forall2 dual s (coₜ s)).
      { clear. induction s as [| ν s' IHs]; simpl.
        - constructor.
        - constructor; [exact (proj2_sig (exists_dual ν)) | exact IHs]. }
      exists q'. eapply wt_to_cowt_dual; [exact w | exact hd].
    + (* the test talked to itself: give the pair back to the process by BOOMERANG *)
      destruct (IH (s1 ++ s2 ++ s3)) as (qend & w).
      { etransitivity; [symmetry; exact heq'' | exact equiv]. }
      eapply cowt_split in w as (qa & w1 & w23).
      eapply cowt_split in w23 as (r2 & w2 & w3).
      eapply cowt_to_wt_dual in w2 as (I & hI & wI).
      eapply cowt_to_wt_dual in w3 as (v & hv & wv).
      assert (wIv : qa ⟹[I ++ v] qend) by (eapply wt_concat; [exact wI | exact wv]).
      destruct (fw_insert_pair qa qend η I v hη wIv) as (qc & wc).
      assert (hd : ForAllHelper.Forall2 dual (η :: s2 ++ μ :: s3) (co η :: I ++ η :: v)).
      { eapply ForAllHelper.Forall2_cons; [exact (proj2_sig (exists_dual η)) |].
        eapply ForAllHelper.Forall2_app; [exact hI |].
        eapply ForAllHelper.Forall2_cons; [exact duo | exact hv]. }
      eapply wt_to_cowt_dual in wc; [| exact hd].
      assert (wfull : q ⟹ᶜᵒ[s1 ++ (η :: s2 ++ μ :: s3)] qc)
        by (eapply cowt_concat; [exact w1 | exact wc]).
      exists qc. rewrite eqs. exact wfull.
  - (* the process and the test synchronise *)
    edestruct (eq_spec (gen s) t' (ActExt μ2)) as (t'' & l'' & heq'').
    { exists t. split; [now symmetry | exact trC]. }
    destruct (inversion_may_test_external_action s μ2 t'' l'')
      as [ fatal | [ his | (s1 & s2 & μ & eqs & equiv & -> & his) ] ].
    + exfalso. eapply (never_outcome_false_of_may q0 t'); [exact hm |].
      eapply (never_outcome_eq t'' t'); [exact heq'' | exact fatal].
    + (* same escape as above: everything left of [s] is co-answered outright *)
      destruct (fw_run_inputs (coₜ s) (Forall_exist_co_nba_of_non_blocking s his) q) as (q' & w).
      assert (hd : ForAllHelper.Forall2 dual s (coₜ s)).
      { clear. induction s as [| ν s' IHs]; simpl.
        - constructor.
        - constructor; [exact (proj2_sig (exists_dual ν)) | exact IHs]. }
      exists q'. eapply wt_to_cowt_dual; [exact w | exact hd].
    + (* [q]'s own move co-answers [μ], anticipated past the postponed prefix [s1] *)
      destruct (IH (s1 ++ s2)) as (qend & w).
      { etransitivity; [symmetry; exact heq'' | exact equiv]. }
      eapply cowt_split in w as (qa & w1 & w2).
      eapply cowt_to_wt_dual in w1 as (I & hI & wI).
      assert (hexist : Forall exist_co_nba I).
      { eapply EquivDef_inv2. exists s1.
        split; [exact his | eapply coConvergence.Forall2_dual_sym; exact hI]. }
      eapply cowt_to_wt_dual in w2 as (v & hv & wv).
      assert (w2'' : q ⟹[μ1 :: I ++ v] qend).
      { eapply wt_act; [exact trS |]. eapply wt_concat; [exact wI | exact wv]. }
      destruct (fw_anticipate_inputs q qend μ1 I v hexist w2'') as (q3 & w3').
      assert (hd2 : ForAllHelper.Forall2 dual (s1 ++ μ :: s2) (I ++ μ1 :: v)).
      { eapply ForAllHelper.Forall2_app; [exact hI |].
        eapply ForAllHelper.Forall2_cons; [eapply duo_sym; exact inter | exact hv]. }
      eapply wt_to_cowt_dual in w3'; [| exact hd2].
      exists q3. rewrite eqs. exact w3'.
Qed.

End Completeness_ti_co.

(** ** Completeness, for forwarders *)

Theorem completeness_ti_co_fw `{
  gLtsObaFWP : @gLtsObaFW P A H gLtsEqP gLtsObaP,
  gLtsObaFWQ : @gLtsObaFW Q A H gLtsEqQ gLtsObaQ,
  gLtsT : !gLtsEq T H, gLtsObaT : !gLtsOba T, !Testing_Predicate outcome _}

  {_ : Prop_of_Inter P T A dual}
  {_ : Prop_of_Inter Q T A dual}

  {gen : trace A -> T} {gspec : may_test_spec gen}

  (p : P) (q : Q) :
  p ⊑ₘₐᵧ q -> p ≼꜀ₒ₋ₜᵢ q.
Proof.
  intros hctx s (p' & wSco).
  (* [p] co-answers [s], so it passes the test attesting [s] literally *)
  destruct (may_test_runs s) as (e & we & happy).
  assert (hmp : p may_pass (gen s)) by (eapply wt_to_may_co; eauto).
  eapply hctx in hmp.
  (* hence so does [q] — and then [q] really does co-answer [s] *)
  eapply (completeness_core_co q (gen s) hmp s).
  reflexivity.
Qed.

(** ** Completeness, for feedback LTSs, through the forwarder construction *)

Theorem completeness_ti_co_fb `{
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
  p ⊑ₘₐᵧ q -> (p, ∅ : MO A) ≼꜀ₒ₋ₜᵢ (q, ∅ : MO A).
Proof.
  intro hctx.
  eapply completeness_ti_co_fw.
  eapply (proj1 (lift_fw_ctx_pre p q)). exact hctx.
Qed.
