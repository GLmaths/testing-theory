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
From TestingTheory Require Import ActTau gLts Bisimulation Lts_OBA WeakTransitions Testing_Predicate.

Import ListNotations.
(* * The axiomatised test attesting a trace, for May *)

(* ** Success is unreachable from [t] *)

Definition never_outcome `{gLts T A} (outcome : T -> Prop) (t : T) : Prop :=
  ∀ (u : trace A) (t' : T), t ⟹[u] t' -> ¬ outcome t'.

(* ** Axioms for the tests attesting a trace *)

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

Section May_tests.

Context `{gLtsT : @gLtsEq T A H, gLtsObaT : !gLtsOba T _, !Testing_Predicate outcome _}.
Context {gen : trace A -> T} {gen_spec : may_test_spec gen}.

(* ** Determinacy on the expected action, for every action *)

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

(* ** Fatality propagates backwards along a non-blocking action *)

Lemma outcome_reachable_nb_forward (u : trace A) (t e : T) :
  t ⟹[u] e -> outcome e ->
  ∀ (w : T) (η : A), non_blocking η -> t ⟶[η] w ->
  ∃ u' e', w ⟹[u'] e' /\ outcome e'.
Proof.
  intro wt.
  induction wt as [ x | u0 x y z l wt IH | μ u0 x y z l wt IH ];
    intros happy w η nb leta.
  - exists ε, w. split; [eapply wt_nil |].
    eapply outcome_preserved_by_lts_non_blocking_action; eauto.
  - destruct (nb_tau nb leta l)
      as [ (z0 & lz0 & (y' & ly' & heqy')) | (β & duo & (w2 & lw2 & heqw2)) ].
    + destruct (IH happy y' η nb ly') as (u' & e' & wu & happy').
      edestruct (eq_spec_wt y' z0 heqy' e' u' wu) as (e'' & wu' & heqe'').
      exists u', e''. split.
      * eapply wt_tau; [exact lz0 | exact wu'].
      * eapply outcome_preserved_by_eq; [exact happy' | now symmetry].
    + edestruct (eq_spec_wt y w2) as (e'' & wu' & heqe'').
      { now symmetry. }
      { exact wt. }
      exists (β :: u0), e''. split.
      * eapply wt_act; [exact lw2 | exact wu'].
      * eapply outcome_preserved_by_eq; [exact happy | now symmetry].
  - destruct (decide (μ = η)) as [-> | neq].
    + assert (heq : y ⋍ w) by (eapply nb_determinacy; eauto).
      edestruct (eq_spec_wt y w heq z u0 wt) as (e'' & wu' & heqe'').
      exists u0, e''. split; [exact wu' |].
      eapply outcome_preserved_by_eq; [exact happy | now symmetry].
    + destruct (nb_confluence nb neq leta l) as (r & lr & (y' & ly' & heqy')).
      destruct (IH happy y' η nb ly') as (u' & e' & wu & happy').
      edestruct (eq_spec_wt y' r heqy' e' u' wu) as (e'' & wu' & heqe'').
      exists (μ :: u'), e''. split.
      * eapply wt_act; [exact lr | exact wu'].
      * eapply outcome_preserved_by_eq; [exact happy' | now symmetry].
Qed.

Lemma never_outcome_nb_back (t w : T) (η : A) :
  non_blocking η -> t ⟶[η] w ->
  never_outcome outcome w -> never_outcome outcome t.
Proof.
  intros nb l nw u e wu happy.
  destruct (outcome_reachable_nb_forward u t e wu happy w η nb l)
    as (u' & e' & wu' & happy').
  eapply nw; eauto.
Qed.

(* ** The test does run its own trace, all the way to success *)

Lemma may_test_runs (r : trace A) : ∃ e, gen r ⟹[r] e /\ outcome e.
Proof.
  induction r as [ | μ r' IH ].
  - destruct may_test_can_compute as (e & le).
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

(* ** A trace element can be consumed from the middle of the trace *)
Lemma gen_lts_mu_in_the_middle (s1 s2 : trace A) (μ1 : A) :
  Forall non_blocking s1 -> gen (s1 ++ μ1 :: s2) ⟶⋍[μ1] gen (s1 ++ s2).
Proof.
  revert s2 μ1.
  induction s1 as [| μ2 s']; intros s2 μ1 his; simpl in *.
  - eapply (may_test_next_step μ1).
  - inversion his as [| ? ? nb his']; subst.
    destruct (IHs' s2 μ1 his') as (r & hlr & heqr).
    edestruct (may_test_next_step μ2 (s' ++ μ1 :: s2)) as (t & hlt & heqt).
    edestruct (eq_spec t r) as (u & hlu & hequ).
    { eauto with mdb. }
    destruct (nb_delay nb hlt hlu) as (v & l1 & (t' & l2 & heq')).
    exists v. split; [eassumption |].
    destruct (may_test_next_step μ2 (s' ++ s2)) as (w & hlw & heqw).
    eapply backwards_nb_determinacy; try eassumption.
    etransitivity; [eassumption |].
    etransitivity; [eassumption |].
    etransitivity; [eassumption | now symmetry].
Qed.

Lemma gen_lts_mu_in_the_middle' (s1 s2 : trace A) (μ1 : A) (t : T) :
  Forall non_blocking s1 ->
  gen (s1 ++ μ1 :: s2) ⟶⋍[μ1] t -> t ⋍ gen (s1 ++ s2).
Proof.
  revert s2 μ1 t.
  induction s1 as [| μ2 s']; intros s2 μ1 t his HypTr; simpl in *.
  - destruct HypTr as (e & HypTr & equiv).
    assert (e ⋍ gen s2) by (eapply may_test_determinacy; eauto).
    etransitivity; [symmetry; exact equiv | assumption].
  - inversion his as [| ? ? nb' his']; subst.
    destruct (decide (non_blocking μ1)) as [nb | not_nb].
    + assert (HypTr' : gen ((μ2 :: s') ++ μ1 :: s2) ⟶⋍[μ1] gen ((μ2 :: s') ++ s2)).
      { eapply gen_lts_mu_in_the_middle. constructor; eauto. }
      destruct HypTr as (e & HypTr & equiv).
      destruct HypTr' as (e' & HypTr' & equiv').
      assert (e ⋍ e') by (eapply nb_determinacy; eauto).
      etransitivity; [symmetry; exact equiv |].
      etransitivity; eauto.
    + destruct HypTr as (e & HypTr & equiv).
      assert (HypTr' : gen (μ2 :: s' ++ μ1 :: s2) ⟶⋍[μ2] gen (s' ++ μ1 :: s2)).
      { eapply may_test_next_step. }
      destruct HypTr' as (e' & HypTr' & equiv').
      assert (not_eq : μ1 ≠ μ2) by (intro imp; rewrite imp in not_nb; contradiction).
      destruct (nb_confluence nb' not_eq HypTr' HypTr)
        as (t' & l2 & (t'' & l1 & heq)).
      edestruct (eq_spec (gen (s' ++ μ1 :: s2)) t' (ActExt μ1)) as (v & hlv & heqv).
      { exists e'. split; [now symmetry | exact l2]. }
      assert (heq' : t' ⋍ gen (s' ++ s2)).
      { eapply IHs'; eauto. exists v. split; eauto. }
      destruct (may_test_next_step μ2 (s' ++ s2)) as (v' & hlv' & heqv').
      assert (final : e ⋍ gen (μ2 :: s' ++ s2)).
      { eapply backwards_nb_determinacy; eauto.
        etransitivity; [exact heq |].
        etransitivity; [exact heq' | now symmetry]. }
      etransitivity; [symmetry; exact equiv | exact final].
Qed.

(* ** Fatality is invariant under bisimilarity *)

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

(* ** Inversion of an external action of the test *)

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
  induction s as [| μ s' IH]; intros β' t l b.
  - right. left. constructor.
  - destruct (decide (non_blocking μ)) as [nb | bν].
    + destruct (may_test_next_step μ s') as (v & lv & heqv).
      assert (not_eq : β' ≠ μ) by (intro imp; subst; contradiction).
      destruct (nb_confluence nb not_eq lv l) as (t' & l2 & (t'' & l1 & heq)).
      edestruct (eq_spec (gen s') t' (ActExt β')) as (v' & lv' & heqv').
      { exists v. split; [now symmetry | exact l2]. }
      destruct (IH β' v' lv' b)
        as [ fatal | [ his | (s1 & s2 & β & -> & equiv & -> & his) ] ].
      * assert (nt' : never_outcome outcome t')
          by (eapply never_outcome_eq; [exact heqv' | exact fatal]).
        left. eapply (never_outcome_nb_back t t'' μ); [exact nb | exact l1 |].
        eapply (never_outcome_eq t' t''); [now symmetry | exact nt'].
      * right. left. constructor; assumption.
      * right. right. exists (μ :: s1), s2, β. repeat split; eauto.
        eapply gen_lts_mu_in_the_middle'.
        -- constructor; eauto.
        -- exists t. split; [exact l | reflexivity].
    + destruct (decide (β' = μ)) as [-> | neq].
      * right. right. exists ε, s', μ. repeat split; simpl; eauto with mdb.
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
  induction s as [| μ s' IH]; intros η' t l nb.
  - right. left. constructor.
  - destruct (may_test_next_step μ s') as (r & lr & heqr).
    destruct (decide (μ = η')) as [-> | not_eq].
    + right. right. exists ε, s', η'. repeat split; simpl; eauto with mdb.
      transitivity r; [eapply (nb_determinacy nb l lr) | exact heqr].
    + destruct (decide (non_blocking μ)) as [nbν | bν].
      * destruct (nb_confluence nb not_eq l lr)
          as (t' & l2 & (t'' & l1 & heq)).
        edestruct (eq_spec (gen s') t'' (ActExt η')) as (v & lv & heqv).
        { exists r. split; [now symmetry | exact l1]. }
        destruct (IH η' v lv nb)
          as [ fatal | [ his | (s1 & s2 & η & -> & equiv & -> & his) ] ].
        -- assert (nt'' : never_outcome outcome t'')
             by (eapply never_outcome_eq; [exact heqv | exact fatal]).
           left. eapply (never_outcome_nb_back t t' μ); [exact nbν | exact l2 |].
           eapply never_outcome_eq; [exact heq | exact nt''].
        -- right. left. constructor; assumption.
        -- right. right. exists (μ :: s1), s2, η. repeat split; eauto.
           eapply gen_lts_mu_in_the_middle'.
           ++ constructor; eauto.
           ++ exists t. split; [exact l | reflexivity].
      * left. eapply may_test_deviation_is_fatal; eauto.
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

(* ** Inversion of a silent move of the test *)

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
  - right. left. constructor.
  - destruct (decide (non_blocking μ')) as [nb | bμ'].
    + destruct (may_test_next_step μ' s') as (r & lr & heqr).
      destruct (nb_tau nb lr l)
        as [ (r1 & l1 & (r2 & l2 & heq)) | (μ & duo & (r'' & l'' & heq'')) ].
      * edestruct (eq_spec (gen s') r1 τ) as (v & lv & heqv).
        { exists r. split; [now symmetry | exact l1]. }
        destruct (IH v lv)
          as [ fatal
             | [ his
               | (η & μ & s1 & s2 & s3 & -> & equiv & hη & his1 & his2 & duo) ] ].
        -- left.
           eapply (never_outcome_nb_back t r2 μ'); [exact nb | exact l2 |].
           eapply (never_outcome_eq v r2); [| exact fatal].
           etransitivity; [exact heqv | now symmetry].
        -- right. left. constructor; assumption.
        -- right. right. exists η, μ, (μ' :: s1), s2, s3. simpl.
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
      * edestruct (eq_spec (gen s') r'' (ActExt μ)) as (t0 & lt0 & heqt0).
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
    + left. eapply may_test_tau_on_blocking_is_fatal; eauto.
Qed.

End May_tests.