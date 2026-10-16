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

From Stdlib.Unicode Require Import Utf8.
From Stdlib Require Import Relations.Relation_Definitions Classes.RelationClasses.
From stdpp Require Import base tactics decidable countable finite gmap list.
From TestingTheory Require Import ActTau gLts SyncActions Bisimulation Subset_Act
  InteractionBetweenLts MemAction InteractionUnion MemForwarder Termination
  coWeakTransition coConvergence coFiniteImage InListPropHelper
  StateTransitionSystems Testing_Predicate Must
  Label_Abstraction.LabelAbstraction LabelAdmissible DefinitionASrel
  Lts_OBA Lts_OBA_FB CompletenessASsync EquivalenceASsync.
(* begin hide *)
#[local] Hint Mode ExtAction ! : typeclass_instances.

Section Lift_eq.
  Context {P Aproc Atest : Type} `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest}.
  Context `{gLtsEqP : !gLtsEq P Hp}.

  Definition liftEq : gLtsEq P (@ExtAction_sum Aproc (MemAct Atest) Hp (@ExtAction_mem Atest Ht)) :=
    {| gLtsEq_gLts := lift_left_lts;
       eq_rel := eq_rel;
       eq_rel_eq := eq_rel_eq;
       eq_spec p q 𝜆 h := let '(ex_intro _ r (conj e l)) := h in lift_left_eq_spec p r q 𝜆 e l |}.
End Lift_eq.

Section Blocking_lift.
  Context {P Aproc Atest : Type} `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest}
    `{SA : !SyncAction Aproc Atest}.
  Context `{gLtsEqP : !gLtsEq P Hp}.
  Context (allblk : ∀ η : Atest, ¬ non_blocking η).

  Notation gP := (@gLtsEq_gLts P Aproc Hp gLtsEqP).
  Notation gL := (@gLtsEq_gLts P _ _ (@liftEq P Aproc Atest Hp Ht gLtsEqP)).

  Definition gLtsFWMem_lift : @gLtsFWMem P Aproc Atest Hp Ht SA liftEq.
  Proof.
    split; [intros p η nb | intros p1 p2 p3 η μ nb | intros p q r η 𝜆 nb];
      exfalso; exact (allblk η nb).
  Qed.

  Lemma coR_lift (p : P) (β : Atest) :
    β ∈ coR (H := gL) (SA := SyncAction_mem) p ↔ β ∈ coR (H := gP) (SA := SA) p.
  Proof.
    split.
    - intros ([μ | ζ] & acc & hs & b); [| by destruct acc].
      exists μ. split_and!; [exact acc | exact hs | exact b].
    - intros (μ & acc & hs & b). exists (inl μ). split_and!; [exact acc | exact hs | exact b].
  Qed.

  Lemma terminate_lift (p : P) : terminate (H := gL) p ↔ terminate (H := gP) p.
  Proof.
    split; induction 1 as [p _ IH]; constructor; intros q l; by apply IH.
  Qed.

  Lemma cowt_lift (p q : P) (s : trace Atest) :
    cowt (H := gL) (SA := SyncAction_mem) p s q ↔ cowt (H := gP) (SA := SA) p s q.
  Proof.
    split; induction 1 as [p | s p r t l w IH | μ μ' s p r t hs l w IH].
    - constructor.
    - eapply cowt_tau; [exact l | exact IH].
    - destruct μ' as [μ0 | ζ]; [| by destruct l]. eapply (cowt_act μ μ0); [exact hs | exact l | exact IH].
    - constructor.
    - eapply cowt_tau; [exact l | exact IH].
    - eapply (cowt_act μ (inl μ')); [exact hs | exact l | exact IH].
  Qed.

  Lemma cocnv_lift (p : P) (s : trace Atest) :
    cocnv (H := gL) (SA := SyncAction_mem) p s ↔ cocnv (H := gP) (SA := SA) p s.
  Proof.
    split; induction 1 as [p ht | p μ s ht hq IH].
    - constructor. by apply terminate_lift.
    - constructor; [by apply terminate_lift |]. intros q w. apply IH. by apply cowt_lift.
    - constructor. by apply terminate_lift.
    - constructor; [by apply terminate_lift |]. intros q w. apply IH. by apply cowt_lift.
  Qed.
End Blocking_lift.

Section Blocking_lift_pre.
  Context {P Q Aproc Atest : Type} `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest}
    `{SA : !SyncAction Aproc Atest}.
  Context `{gLtsEqP : !gLtsEq P Hp} `{gLtsEqQ : !gLtsEq Q Hp}.

  Notation gP := (@gLtsEq_gLts P Aproc Hp gLtsEqP).
  Notation gLP := (@gLtsEq_gLts P _ _ (@liftEq P Aproc Atest Hp Ht gLtsEqP)).
  Notation gQ := (@gLtsEq_gLts Q Aproc Hp gLtsEqQ).
  Notation gLQ := (@gLtsEq_gLts Q _ _ (@liftEq Q Aproc Atest Hp Ht gLtsEqQ)).

  Lemma bhv_pre_r_lift (R : relation Atest) (p : P) (q : Q) :
    bhv_pre_r (gLtsP := gLP) (gLtsQ := gLQ) (SA := SyncAction_mem) R p q ↔
    bhv_pre_r (gLtsP := gP) (gLtsQ := gQ) (SA := SA) R p q.
  Proof.
    split; intros [h1 h2]; split.
    - intros s hc. apply cocnv_lift, h1, cocnv_lift, hc.
    - intros s q' hc w st.
      destruct (h2 s q' (proj2 (cocnv_lift p s) hc) (proj2 (cowt_lift q q' s) w) st)
        as (p' & wp & stp & sub).
      exists p'. split_and!; [by apply cowt_lift | exact stp |].
      intros β hβ. destruct (sub β (proj2 (coR_lift p' β) hβ)) as (β' & hβ' & hR).
      exists β'. split; [by apply coR_lift | exact hR].
    - intros s hc. apply cocnv_lift, h1, cocnv_lift, hc.
    - intros s q' hc w st.
      destruct (h2 s q' (proj1 (cocnv_lift p s) hc) (proj1 (cowt_lift q q' s) w) st)
        as (p' & wp & stp & sub).
      exists p'. split_and!; [by apply cowt_lift | exact stp |].
      intros β hβ. destruct (sub β (proj1 (coR_lift p' β) hβ)) as (β' & hβ' & hR).
      exists β'. split; [by apply coR_lift | exact hR].
  Qed.
End Blocking_lift_pre.
Section Must_lift.
  Context {P T Aproc Atest : Type} `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest}
    `{SA : !SyncAction Aproc Atest}.
  Context `{gLtsEqP : !gLtsEq P Hp} `{gLtsT : !gLtsEq T Ht}
    {outcome : T → Prop} `{TP : !Testing_Predicate outcome gLtsT}.

  Notation gP := (@gLtsEq_gLts P Aproc Hp gLtsEqP).
  Notation gL := (@gLtsEq_gLts P _ _ (@liftEq P Aproc Atest Hp Ht gLtsEqP)).

  Context (STS : ParSts P T gP gLtsT) (SPEC : ParStsSpec P T gP gLtsT SA STS).
  Context (STSL : ParSts P T gL gLtsT) (SPECL : ParStsSpec P T gL gLtsT SyncAction_mem STSL).

  Lemma must_lift_to (p : P) (t : T) :
    must (gLtsP := gP) (SA := SA) (STS := STS) p t →
    must (gLtsP := gL) (SA := SyncAction_mem) (STS := STSL) p t.
  Proof.
    induction 1 as [p t ho | p t nh ex pt IHpt et IHet com IHcom].
    - by apply m_now.
    - apply m_step; [exact nh | | exact IHpt | exact IHet |].
      + destruct ex as (y & hy).
        apply (@par_step_inv _ _ _ _ _ _ _ _ _ _ SPEC) in hy
          as [(p' & -> & l) | [(t' & -> & l) | (p' & t' & μ1 & μ2 & -> & hs & l1 & l2)]].
        * exists (p', t). exact (@par_step_left _ _ _ _ _ _ _ _ _ _ SPECL p p' t l).
        * exists (p, t'). exact (@par_step_right _ _ _ _ _ _ _ _ _ _ SPECL p t t' l).
        * exists (p', t').
          exact (@par_step_sync _ _ _ _ _ _ _ _ _ _ SPECL p p' t t' (inl μ1) μ2 hs l1 l2).
      + intros p' t' [μ1 | ζ] μ2 hs l1 l2; [| by destruct l1].
        exact (IHcom p' t' μ1 μ2 hs l1 l2).
  Qed.

  Lemma must_lift_from (p : P) (t : T) :
    must (gLtsP := gL) (SA := SyncAction_mem) (STS := STSL) p t →
    must (gLtsP := gP) (SA := SA) (STS := STS) p t.
  Proof.
    induction 1 as [p t ho | p t nh ex pt IHpt et IHet com IHcom].
    - by apply m_now.
    - apply m_step; [exact nh | | exact IHpt | exact IHet |].
      + destruct ex as (y & hy).
        apply (@par_step_inv _ _ _ _ _ _ _ _ _ _ SPECL) in hy
          as [(p' & -> & l) | [(t' & -> & l) | (p' & t' & μ1 & μ2 & -> & hs & l1 & l2)]].
        * exists (p', t). exact (@par_step_left _ _ _ _ _ _ _ _ _ _ SPEC p p' t l).
        * exists (p, t'). exact (@par_step_right _ _ _ _ _ _ _ _ _ _ SPEC p t t' l).
        * destruct μ1 as [μ1 | ζ]; [| by destruct l1].
          exists (p', t').
          exact (@par_step_sync _ _ _ _ _ _ _ _ _ _ SPEC p p' t t' μ1 μ2 hs l1 l2).
      + intros p' t' μ1 μ2 hs l1 l2.
        exact (IHcom p' t' (inl μ1) μ2 hs l1 l2).
  Qed.
End Must_lift.

Section Inter_lift.
  Context {P T Aproc Atest : Type} `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest}
    `{SA : !SyncAction Aproc Atest}.
  Context `{gLtsEqP : !gLtsEq P Hp} `{gLtsT : !gLts T Ht}.

  Notation gP := (@gLtsEq_gLts P Aproc Hp gLtsEqP).
  Notation gL := (@gLtsEq_gLts P _ _ (@liftEq P Aproc Atest Hp Ht gLtsEqP)).

  Context `{PI : !@Prop_of_Inter P T Aproc Atest (@sync _ _ _ _ SA) Hp gP Ht gLtsT}.

  Program Definition lift_inter :
    @Prop_of_Inter P T (Aproc + MemAct Atest) Atest (@sync _ _ _ _ SyncAction_mem)
      ExtAction_sum gL Ht gLtsT :=
    {| lts_essential_actions_left p := set_map inl (lts_essential_actions_left p);
       lts_essential_actions_right := lts_essential_actions_right;
       lts_co_inter_action_left ξ p := set_map inl (lts_co_inter_action_left ξ p);
       lts_co_inter_action_right ξ t :=
         match ξ with inl μ => lts_co_inter_action_right μ t | inr _ => ∅ end |}.
  Next Obligation.
    intros p [μ | ζ] h.
    - assert (hμ : μ ∈ lts_essential_actions_left p)
        by (apply elem_of_map in h as (? & e & ?); by injection e as ->).
      exact (lts_essential_action_spec_left p μ hμ).
    - exfalso. apply elem_of_map in h as (? & e & _). done.
  Defined.
  Next Obligation. intros t ξ h. exact (lts_essential_action_spec_right t ξ h). Defined.
  Next Obligation.
    intros p [μ | ζ] p' t μ2 t' l1 l2 hs; [| by destruct l1].
    destruct (lts_essential_actions_spec_interact p μ p' t μ2 t' l1 l2 hs) as [h | h].
    - left. apply elem_of_map. by exists μ.
    - by right.
  Qed.
  Next Obligation.
    intros p p' ξ [μ | ζ] t hξ l hs; [| by destruct l].
    apply elem_of_map. exists μ. split; [done |].
    exact (lts_co_inter_action_spec_left p p' ξ μ t hξ l hs).
  Qed.
  Next Obligation.
    intros t t' ξ μ p hξ l hs. simpl in hξ.
    apply elem_of_map in hξ as (μ0 & -> & hμ0).
    exact (lts_co_inter_action_spec_right t t' μ0 μ p hμ0 l hs).
  Qed.
End Inter_lift.

Section CoFinite_lift.
  Context {P Aproc Atest : Type} `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest}
    `{SA : !SyncAction Aproc Atest}.
  Context `{gLtsEqP : !gLtsEq P Hp}.

  Notation gP := (@gLtsEq_gLts P Aproc Hp gLtsEqP).
  Notation gL := (@gLtsEq_gLts P _ _ (@liftEq P Aproc Atest Hp Ht gLtsEqP)).

  Context `{CFI : !@coFiniteImagegLts P Atest Aproc Hp gP Ht SA}.

  Lemma lift_sync_step_iff (p q : P) (𝜆 : Atest) :
    (∃ 𝜆', @sync _ _ _ _ SyncAction_mem 𝜆' 𝜆 ∧ lts_step (gLts := gL) p (ActExt 𝜆') q) ↔
    (∃ μ, sync μ 𝜆 ∧ p ⟶[μ] q).
  Proof.
    split.
    - intros ([μ | ζ] & hs & l); [by exists μ | by destruct l].
    - intros (μ & hs & l). by exists (inl μ).
  Qed.

  Definition lift_tau_finite (p : P) : Finite (dsig (λ q, lts_step (gLts := gL) p τ q)).
  Proof.
    unfold dsig.
    eapply (in_list_finite (map proj1_sig (enum (dsig (λ q, p ⟶ q))))).
    intros q h%bool_decide_unpack. apply list_elem_of_fmap.
    exists (dexist q h). split; [done | apply elem_of_enum].
  Defined.

  Definition lift_ext_dec (p : P) (𝜆 : Atest) q :
    Decision (∃ 𝜆', @sync _ _ _ _ SyncAction_mem 𝜆' 𝜆 ∧ lts_step (gLts := gL) p (ActExt 𝜆') q).
  Proof.
    destruct (decide (∃ μ, sync μ 𝜆 ∧ p ⟶[μ] q)) as [h | h]; [left | right];
      by rewrite lift_sync_step_iff.
  Defined.

  #[local] Existing Instance lift_ext_dec.

  Definition lift_ext_finite (p : P) (𝜆 : Atest) :
    Finite (dsig (λ q, ∃ 𝜆', @sync _ _ _ _ SyncAction_mem 𝜆' 𝜆 ∧ lts_step (gLts := gL) p (ActExt 𝜆') q)).
  Proof.
    unfold dsig.
    eapply (in_list_finite (map proj1_sig (enum (dsig (λ q, ∃ μ, sync μ 𝜆 ∧ p ⟶[μ] q))))).
    intros q h%bool_decide_unpack. apply list_elem_of_fmap.
    exists (dexist q (proj1 (lift_sync_step_iff p q 𝜆) h)). split; [done | apply elem_of_enum].
  Defined.

  Definition coFiniteImage_lift :
    @coFiniteImagegLts P Atest (Aproc + MemAct Atest) ExtAction_sum gL Ht SyncAction_mem :=
    @MkCoFlts P Atest (Aproc + MemAct Atest) ExtAction_sum gL Ht SyncAction_mem
      (@cofolts_states_countable P Atest Aproc Hp gP Ht SA CFI)
      lift_tau_finite lift_ext_dec lift_ext_finite.
End CoFinite_lift.
Section LA_lift.
  Context {P T Aproc Atest : Type} `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest}
    `{SA : !SyncAction Aproc Atest}.
  Context `{gLtsEqP : !gLtsEq P Hp} `{gLtsT : !gLts T Ht}.
  Context (R : relation Atest).

  Notation gP := (@gLtsEq_gLts P Aproc Hp gLtsEqP).
  Notation gL := (@gLtsEq_gLts P _ _ (@liftEq P Aproc Atest Hp Ht gLtsEqP)).

  Lemma LA_admissible_lift :
    @LA_admissible P T Aproc Hp gP Atest Ht gLtsT SA R →
    @LA_admissible P T (Aproc + MemAct Atest) ExtAction_sum gL Atest Ht gLtsT SyncAction_mem R.
  Proof.
    intros adm p β β'' b h mem.
    apply (proj1 (coR_lift (gLtsEqP := gLtsEqP) (SA := SA) p β'')) in mem.
    destruct (adm p β β'' b h mem) as (u & hu & hP).
    exists u. split; [exact (proj2 (coR_lift (gLtsEqP := gLtsEqP) (SA := SA) p u) hu) | exact hP].
  Qed.

  Context `{!Equivalence R} `{!RelDecision R}.

  Definition FinitaryLA_lift :
    @FinitaryLA P Aproc Hp gP Atest Ht SA R _ _ →
    @FinitaryLA P (Aproc + MemAct Atest) ExtAction_sum gL Atest Ht SyncAction_mem R _ _.
  Proof.
    intros fin. refine {| coR_absR := @coR_absR _ _ _ _ _ _ _ R _ _ fin |}.
    intros p x. rewrite (@coR_absR_spec _ _ _ _ _ _ _ R _ _ fin).
    split; intros (β & hβ & e); exists β; split; try exact e.
    - exact (proj2 (coR_lift (gLtsEqP := gLtsEqP) (SA := SA) p β) hβ).
    - exact (proj1 (coR_lift (gLtsEqP := gLtsEqP) (SA := SA) p β) hβ).
  Defined.
End LA_lift.

Section Blocking_characterisation.
  Context {P Q T Aproc Atest : Type} `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest}
    `{SA : !SyncAction Aproc Atest}.
  Context (allblk : ∀ η : Atest, ¬ non_blocking η).
  Context (R : relation Atest) `{!Equivalence R} `{!RelDecision R}.
  Context (outcome : T → Prop).

  Context `{gLtsEqT : !gLtsEq T Ht} `{gLtsObaT : !gLtsOba T} `{!gLtsObaFB T Atest}.
  Context `{TP : !Testing_Predicate outcome gLtsEqT}.

  Context `{gLtsEqP : !gLtsEq P Hp} `{gLtsEqQ : !gLtsEq Q Hp}.

  Notation gP := (@gLtsEq_gLts P Aproc Hp gLtsEqP).
  Notation gQ := (@gLtsEq_gLts Q Aproc Hp gLtsEqQ).
  Notation gT := (@gLtsEq_gLts T Atest Ht gLtsEqT).

  Context (PIP : @Prop_of_Inter P T Aproc Atest (@sync _ _ _ _ SA) Hp gP Ht gT)
          (PIQ : @Prop_of_Inter Q T Aproc Atest (@sync _ _ _ _ SA) Hp gQ Ht gT).
  Context (CFIP : @coFiniteImagegLts P Atest Aproc Hp gP Ht SA)
          (CFIQ : @coFiniteImagegLts Q Atest Aproc Hp gQ Ht SA).
  Context (STSP : ParSts P T gP gLtsEqT) (SPECP : ParStsSpec P T gP gLtsEqT SA STSP)
          (STSQ : ParSts Q T gQ gLtsEqT) (SPECQ : ParStsSpec Q T gQ gLtsEqT SA STSQ).
  Context (AdmP : @LA_admissible P T Aproc Hp gP Atest Ht gT SA R)
          (AdmQ : @LA_admissible Q T Aproc Hp gQ Atest Ht gT SA R).
  Context (FinP : @FinitaryLA P Aproc Hp gP Atest Ht SA R _ _)
          (FinQ : @FinitaryLA Q Aproc Hp gQ Atest Ht SA R _ _).

  Context (tconv : list Atest → T) `{!test_convergence_spec tconv}.
  Context (ta : gset (LA_quotient R) → list Atest → T)
          `{!test_co_acceptance_set_spec (LA_quotient R) ta (LA_class R)}.

  Theorem equivalence_rel_blocking (p : P) (q : Q) :
    @ctx_pre P Aproc Hp gP Q gQ T Atest Ht gLtsEqT outcome TP SA STSP STSQ p q ↔
    bhv_pre_r (gLtsP := gP) (gLtsQ := gQ) (SA := SA) R p q.
  Proof.
    rewrite <- (bhv_pre_r_lift R p q).
    rewrite <- (equivalence_fw_rel_and_must_i_sync_co_trace R outcome tconv ta p q
                  (gLtsEqP := liftEq) (FWP := gLtsFWMem_lift allblk)
                  (SYP := lift_inter (PI := PIP)) (CFIP := coFiniteImage_lift (CFI := CFIP))
                  (AdmP := LA_admissible_lift R AdmP) (FinP := FinitaryLA_lift R FinP)
                  (gLtsEqQ := liftEq) (FWQ := gLtsFWMem_lift allblk)
                  (SYQ := lift_inter (PI := PIQ)) (CFIQ := coFiniteImage_lift (CFI := CFIQ))
                  (AdmQ := LA_admissible_lift R AdmQ) (FinQ := FinitaryLA_lift R FinQ)).
    pose proof (@ParStsSpec_of_union P T _ _ _ _ _ gLtsEqT SyncAction_mem (lift_inter (PI := PIP))) as SLP.
    pose proof (@ParStsSpec_of_union Q T _ _ _ _ _ gLtsEqT SyncAction_mem (lift_inter (PI := PIQ))) as SLQ.
    split; intros h t hm.
    - eapply (must_lift_to STSQ SPECQ _ SLQ), h, (must_lift_from STSP SPECP _ SLP), hm.
    - eapply (must_lift_from STSQ SPECQ _ SLQ), h, (must_lift_to STSP SPECP _ SLP), hm.
  Qed.
End Blocking_characterisation.
(* end hide *)
