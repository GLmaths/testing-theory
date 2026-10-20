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

From Stdlib Require ssreflect Setoid.
From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From Stdlib.Program Require Import Wf Equality.
From Stdlib.Wellfounded Require Import Inverse_Image.

From stdpp Require Import base countable finite gmap list finite base decidable finite gmap.

From TestingTheory Require Import SyncActions gLts Bisimulation Lts_OBA Lts_Finite_Non_Blocking_Chain Lts_FW Lts_OBA_FB Lts_CN
      Must Subset_Act InteractionBetweenLts ParallelLTSConstruction ForwarderConstruction
      Termination Convergence WeakTransitions Lift Testing_Predicate DefinitionAS MultisetLTSConstruction StateTransitionSystems.
From TestingTheory Require Import ActTau InFiniteSetHelper InListPropHelper.
From TestingTheory Require Import coWeakTransition coConvergence DefinitionASrel
      FiniteImageLTS coFiniteImage coSetLTSConstruction Label_Abstraction.LabelAbstraction SoundnessASsync LtsFW.
(* * Soundness for the co-acceptance-set preorder *)

(* ** Soundness on forwarders, one alphabet *)

Lemma soundness_fw_co `{
  gLtsEqP : @gLtsEq P A H, !coFiniteImagegLts P A, !LtsFW P A,
  gLtsT : !gLtsEq T H, !Testing_Predicate outcome _}

  `{PI : !Prop_of_Inter P T A A dual}

  (𝔸 : Label_abstraction P T)

  (p q : P) : p ≼꜀ₒ₋ₐₛ[ ρ[𝔸] ] q -> p ⊑ₘᵤₛₜᵢ q.
Proof.
  assert (CN : @gLtsCNenabled P A A H H _ SyncAction_of_dual).
  { apply MkgLtsCNenabled. intros p1 η nb.
    destruct (lfw_boomerang p1 η nb) as (p2 & l & _).
    exists (co η), p2. split; [exact (co_dual η) | exact l]. }
  pose proof (ParStsSpec_of_union gLtsEq_gLts gLtsT (SA := SyncAction_of_dual) (SY := PI)) as SU.
  intros h t hm.
  apply (must_transfer _ _ SU (ParStsSpec_of_inter _ _)).
  eapply (soundness_co_nb_enabled_co outcome 𝔸 (SA := SyncAction_of_dual) (CN := CN) (PI := PI) p q h t).
  exact (must_transfer _ _ (ParStsSpec_of_inter _ _) SU p t hm).
Qed.

(*
Inductive mustx_alt_co `{EA : !ExtAction A} `{gLtsT : !gLtsEq T EA} `{TP : @Testing_Predicate T A EA outcome _}
  `{gLtsP : @gLts P A EA, !FiniteImagegLts P A} {Hinter : @Prop_of_Inter P T A A dual EA gLtsP EA _}
  (X : gset P) (t : T) : Prop :=
| mx_now_alt_co (hh : outcome t) : mustx_alt_co X t
| mx_step_alt_co
    (nh : ¬ outcome t)
    (ex : forall (p : P), p ∈ X -> ∃ p', inter_step (p, t) τ p')
    (pt : forall X',
        X ⟶ X' ->
        mustx_alt_co X' t)
    (et : forall (t' : T), t ⟶ t' -> mustx_alt_co X t')
    (com : forall (t' : T) μ (X' : gset P),
        t ⟶[μ] t' ->
        X ⟹ᶜᵒ{μ} X' ->
        mustx_alt_co X' t')
  : mustx_alt_co X t.

#[global] Hint Constructors mustx_alt_co:mdb.
Global Notation "X 'must_alt_pass_x_co' t" := (mustx_alt_co X t) (at level 70).
*)

(* [mustx_iff_mustx_alt_co] bridges [mustx] to [mustx_alt_co] — depends on
   the (now commented-out) set-LTS-based [mustx_alt_co]. *)
(*
Section MustxIffMustxAltCo.

(* This bridge lemma needs [mustx] (⇒ [coFiniteImagegLts P A]) and
   [mustx_alt_co] (⇒ [FiniteImagegLts P A], for its toSET-based [pt] case)
   *)
Context `{EA : !ExtAction A}.
Context `{gLtsT : !gLtsEq T EA}.
Context `{TP : @Testing_Predicate T A EA outcome _}.
Context `{gLtsP : @gLts P A EA, !coFiniteImagegLts P A}.
#[local] Instance MustxIffMustxAltCo_FI_PP : FiniteImagegLts P A 
    := FiniteImagegLts_of_coFiniteImagegLts _.
Context `{Hinter : @Prop_of_Inter P T A A dual EA gLtsP EA _}.

Lemma mustx_iff_mustx_alt_co
  (X : gset P) (t : T) :
  X must_pass_x t <-> X must_alt_pass_x_co t.
Proof.
  split.
  - intro hmx. induction hmx; eauto.
    + constructor ;eauto.
    + eapply mx_step_alt_co; eauto.
      * intros. destruct H2;eauto. subst.
        assert (lts_tau_set_from_pset_spec1 X (cowt_tau_set_from_pset X)).
        { eapply cowt_tau_set_from_pset_ispec. }
        eauto.
      * intros t' μ X' hle hws.
        eapply (H1 t' (co μ) μ X'); eauto.
        -- symmetry. exact (proj2_sig (exists_dual μ)).
        -- intros q mem. eapply hws in mem as (p & mem & w).
           eapply cowt_to_wt_dual in w as (s' & hf & w').
           assert (Hy : exists y, s' = [y] /\ dual μ y).
           { inversion hf as [| ? y ? ? duo hf2]; subst. inversion hf2; subst. eauto. }
           destruct Hy as (y & -> & duo).
           assert (y = co μ) by (eapply unique_nb; exact duo).
           subst. exists p. eauto.
  - intro hmx. induction hmx; eauto.
    + constructor ;eauto.
    + eapply mx_step; eauto.
      * intros. assert (X' ⊆ cowt_tau_set_from_pset X).
        { intros p' mem'. eapply H2 in mem' as (p & mem & tr).
          eapply cowt_tau_set_from_pset_ispec;eauto. }
        assert (cowt_tau_set_from_pset X  ≠ ∅ ) by set_solver.
        assert (X ⟶ cowt_tau_set_from_pset X).
        { split ;eauto. }
        eapply H in H6. eapply mx_sub;eauto.
      * intros t' μ1 μ2 X' duo hle hws hneq.
        eapply (H1 t' μ2 X'); eauto.
        intros q mem. eapply hws in mem as (p & mem & w).
        exists p. split; eauto. eapply wt_to_cowt_dual with (s' := [μ1]); eauto.
        constructor; [symmetry; exact duo | constructor].
Qed.

End MustxIffMustxAltCo.
*)

(* ** Soundness for LTSs that can be lifted to forwarders, co variant *)

(*
Lemma soundness_co
  `{@gLtsObaFB P A H gLtsEqP gLtsObaP, !FiniteNonBlockingChain_LtsOba P, !FiniteImagegLts P A}
  `{@gLtsObaFB Q A H gLtsEqQ gLtsObaQ, !FiniteNonBlockingChain_LtsOba Q, !FiniteImagegLts Q A}
  `{@gLtsObaFB T A H gLtsEqT gLtsObaT, !FiniteNonBlockingChain_LtsOba T, !FiniteImagegLts T A}

  `{ !Testing_Predicate outcome _}

  {_ : Prop_of_Inter P T A A dual}
  {_ : Prop_of_Inter Q T A A dual}

  {_ : @Prop_of_Inter P (MO A) A A fw_inter H _ H MbgLts}
  {_ : @Prop_of_Inter (P * MO A) T A A dual H (inter_lts fw_inter) H _}

  {_ : @Prop_of_Inter Q (MO A) A A fw_inter H _ H MbgLts}
  {_ : @Prop_of_Inter (Q * MO A) T A A dual H (inter_lts fw_inter) H _}

  (* [soundness_fw_co], applied below at the forwarder-pair types [P * MO
     A]/[Q * MO A], now needs [coFiniteImagegLts] at that level. Unlike
     [FiniteImagegLts (P * MO A) A] (auto-derived from [FiniteImagegLts P
     A] by [ForwarderConstruction.v]'s [gLtsMBFinite] instance), no such
     forwarder-pair instance exists yet for [coFiniteImagegLts] (same gap
     noted in [EquivalenceASco.v]/[CompletenessASco.v]), so it is assumed
     directly here. *)
  `{!coFiniteImagegLts (P * MO A) A}
  `{!coFiniteImagegLts (Q * MO A) A}

  `{AbsPT : !AbsAction P T (αᴛᴇꜱᴛ : A → FinA) (αᴘʀᴏ : FinA → PreAct) }
  `{AbsQT : !AbsAction Q T (αᴛᴇꜱᴛ : A → FinA) (αᴘʀᴏ : FinA → PreAct) }

  (p : P) (q : Q) : p ▷ ∅ ≼꜀ₒ₋ₐₛ q ▷ ∅ -> p ⊑ₘᵤₛₜᵢ q.
Proof.
  intros halt t hm.
  eapply Lift.must_iff_must_fw in hm.
  eapply Lift.must_iff_must_fw.
  now eapply (soundness_fw_co (p ▷ ∅) (q ▷ ∅)).
Qed.
*)