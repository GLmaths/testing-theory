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
  Label_Abstraction.LabelAbstraction Label_Abstraction.Decidable_dichotomic DefinitionASrel
  Lts_OBA CompletenessASsync EquivalenceASsync Sum_LTS.
(* begin hide *)
#[local] Hint Mode ExtAction ! : typeclass_instances.

Section Lift_eq.
  Context {P Ap At : Type} `{Hp : ExtAction Ap} `{Ht : ExtAction At}.
  Context `{gLtsEqP : !gLtsEq P Hp}.

  Definition liftEq : gLtsEq P (@ExtAction_sum Ap (MemAct At) Hp (@ExtAction_mem At Ht)) :=
    {| gLtsEq_gLts := lift_left_lts;
       eq_rel := eq_rel;
       eq_rel_eq := eq_rel_eq;
       eq_spec p q 𝜆 h := let '(ex_intro _ r (conj e l)) := h in lift_left_eq_spec p r q 𝜆 e l |}.
End Lift_eq.

Section Blocking_lift.
  Context {P Ap At : Type} `{Hp : ExtAction Ap} `{Ht : ExtAction At}
    `{SA : !SyncAction Ap At}.
  Context `{gLtsEqP : !gLtsEq P Hp}.
  Context (allblk : ∀ η : At, ¬ non_blocking η).

  Notation gP := (@gLtsEq_gLts P Ap Hp gLtsEqP).
  Notation gL := (@gLtsEq_gLts P _ _ (@liftEq P Ap At Hp Ht gLtsEqP)).

  Definition gLtsFWMem_lift : @gLtsFWMem P Ap At Hp Ht SA liftEq.
  Proof.
    split; [intros p η nb | intros p1 p2 p3 η μ nb | intros p q r η 𝜆 nb];
      exfalso; exact (allblk η nb).
  Qed.

  Lemma coR_lift (p : P) (β : At) :
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

  Lemma cowt_lift (p q : P) (s : trace At) :
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

  Lemma cocnv_lift (p : P) (s : trace At) :
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
  Context {P Ap At : Type} `{Hp : ExtAction Ap} `{Ht : ExtAction At}
    `{SA : !SyncAction Ap At}.
  Context `{gLtsEqP : !gLtsEq P Hp}.

  Notation gP := (@gLtsEq_gLts P Ap Hp gLtsEqP).
  Notation gL := (@gLtsEq_gLts P _ _ (@liftEq P Ap At Hp Ht gLtsEqP)).

  Lemma map_coR_lift {PreA : Type} (Γ : At → PreA) (p : P) x :
    x ∈ ⌈ Γ ⌉ (coR (H := gL) (SA := SyncAction_mem) p) ↔ x ∈ ⌈ Γ ⌉ (coR (H := gP) (SA := SA) p).
  Proof.
    split; intros (β & hβ & ->); exists β; split;
      [by apply coR_lift | done | by apply coR_lift | done].
  Qed.

  Lemma bhv_pre_lift {PreA : Type} (Γ : At → PreA) (p q : P) :
    cnv_acceptance_set_preorder_on_co_trace (gLtsP := gL) (SA := SyncAction_mem) Γ p q ↔
    cnv_acceptance_set_preorder_on_co_trace (gLtsP := gP) (SA := SA) Γ p q.
  Proof.
    split; intros [h1 h2]; split.
    - intros s hc. apply cocnv_lift, h1, cocnv_lift, hc.
    - intros s q' hc w st.
      destruct (h2 s q' (proj2 (cocnv_lift p s) hc) (proj2 (cowt_lift q q' s) w) st)
        as (p' & wp & stp & sub).
      exists p'. split_and!; [by apply cowt_lift | exact stp |].
      intros x hx. apply map_coR_lift, sub, map_coR_lift, hx.
    - intros s hc. apply cocnv_lift, h1, cocnv_lift, hc.
    - intros s q' hc w st.
      destruct (h2 s q' (proj1 (cocnv_lift p s) hc) (proj1 (cowt_lift q q' s) w) st)
        as (p' & wp & stp & sub).
      exists p'. split_and!; [by apply cowt_lift | exact stp |].
      intros x hx. apply map_coR_lift, sub, map_coR_lift, hx.
  Qed.
End Blocking_lift_pre.

Section Must_lift.
  Context {P T Ap At : Type} `{Hp : ExtAction Ap} `{Ht : ExtAction At}
    `{SA : !SyncAction Ap At}.
  Context `{gLtsEqP : !gLtsEq P Hp} `{gLtsT : !gLtsEq T Ht}
    {outcome : T → Prop} `{TP : !Testing_Predicate outcome gLtsT}.

  Notation gP := (@gLtsEq_gLts P Ap Hp gLtsEqP).
  Notation gL := (@gLtsEq_gLts P _ _ (@liftEq P Ap At Hp Ht gLtsEqP)).

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
  Context {P T Ap At : Type} `{Hp : ExtAction Ap} `{Ht : ExtAction At}
    `{SA : !SyncAction Ap At}.
  Context `{gLtsEqP : !gLtsEq P Hp} `{gLtsT : !gLts T Ht}.

  Notation gP := (@gLtsEq_gLts P Ap Hp gLtsEqP).
  Notation gL := (@gLtsEq_gLts P _ _ (@liftEq P Ap At Hp Ht gLtsEqP)).

  Context `{PI : !@Prop_of_Inter P T Ap At (@sync _ _ _ _ SA) Hp gP Ht gLtsT}.

  Program Definition lift_inter :
    @Prop_of_Inter P T (Ap + MemAct At) At (@sync _ _ _ _ SyncAction_mem)
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
  Context {P Ap At : Type} `{Hp : ExtAction Ap} `{Ht : ExtAction At}
    `{SA : !SyncAction Ap At}.
  Context `{gLtsEqP : !gLtsEq P Hp}.

  Notation gP := (@gLtsEq_gLts P Ap Hp gLtsEqP).
  Notation gL := (@gLtsEq_gLts P _ _ (@liftEq P Ap At Hp Ht gLtsEqP)).

  Context `{CFI : !@coFiniteImagegLts P At Ap Hp gP Ht SA}.

  Lemma lift_sync_step_iff (p q : P) (𝜆 : At) :
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

  Definition lift_ext_dec (p : P) (𝜆 : At) q :
    Decision (∃ 𝜆', @sync _ _ _ _ SyncAction_mem 𝜆' 𝜆 ∧ lts_step (gLts := gL) p (ActExt 𝜆') q).
  Proof.
    destruct (decide (∃ μ, sync μ 𝜆 ∧ p ⟶[μ] q)) as [h | h]; [left | right];
      by rewrite lift_sync_step_iff.
  Defined.

  #[local] Existing Instance lift_ext_dec.

  Definition lift_ext_finite (p : P) (𝜆 : At) :
    Finite (dsig (λ q, ∃ 𝜆', @sync _ _ _ _ SyncAction_mem 𝜆' 𝜆 ∧ lts_step (gLts := gL) p (ActExt 𝜆') q)).
  Proof.
    unfold dsig.
    eapply (in_list_finite (map proj1_sig (enum (dsig (λ q, ∃ μ, sync μ 𝜆 ∧ p ⟶[μ] q))))).
    intros q h%bool_decide_unpack. apply list_elem_of_fmap.
    exists (dexist q (proj1 (lift_sync_step_iff p q 𝜆) h)). split; [done | apply elem_of_enum].
  Defined.

  Definition coFiniteImage_lift :
    @coFiniteImagegLts P At (Ap + MemAct At) ExtAction_sum gL Ht SyncAction_mem :=
    @MkCoFlts P At (Ap + MemAct At) ExtAction_sum gL Ht SyncAction_mem
      (@cofolts_states_countable P At Ap Hp gP Ht SA CFI)
      lift_tau_finite lift_ext_dec lift_ext_finite.
End CoFinite_lift.

Section Label_abstraction_lift.
  Context {P T Ap At : Type} `{Hp : ExtAction Ap} `{Ht : ExtAction At}
    `{SA : !SyncAction Ap At}.
  Context `{gLtsEqP : !gLtsEq P Hp} `{gLtsT : !gLts T Ht}.

  Notation gP := (@gLtsEq_gLts P Ap Hp gLtsEqP).
  Notation gL := (@gLtsEq_gLts P _ _ (@liftEq P Ap At Hp Ht gLtsEqP)).

  Definition CoEnable_PO_lift (C : @CoEnable_PO P Ap Hp gP At Ht SA) :
    @CoEnable_PO P (Ap + MemAct At) ExtAction_sum gL At Ht SyncAction_mem.
  Proof.
    refine (@CEPO.MkCoEnable_PO P (Ap + MemAct At) ExtAction_sum gL At Ht SyncAction_mem
              (CEPO.label_preorder P (CoEnable_PO := C))
              (@CEPO.label_preorder_is_a_preorder P Ap Hp gP At Ht SA C) _).
    intros μ μ' le p mem.
    apply (proj2 (coR_lift (SA := SA) p μ)).
    apply (@CEPO.coR_reverse_inclusion P Ap Hp gP At Ht SA C μ μ' le p).
    exact (proj1 (coR_lift (SA := SA) p μ') mem).
  Defined.

  Definition Label_abstraction_lift (𝔸 : @Label_abstraction P T Ap At Hp Ht gP gLtsT SA) :
    @Label_abstraction P T (Ap + MemAct At) At ExtAction_sum Ht gL gLtsT SyncAction_mem.
  Proof.
    refine (@MkLA P T (Ap + MemAct At) At ExtAction_sum Ht gL gLtsT SyncAction_mem
              (EPO (Label_abstraction := 𝔸)) (CoEnable_PO_lift (CEPO (Label_abstraction := 𝔸)))
              (Label_abstraction_dec (Label_abstraction := 𝔸))).
  Defined.

  Definition Dichotomic_lift {PreA : Type} (Γ : At → PreA) :
    @Dichotomic P Ap At PreA Hp Ht gP SA Γ →
    @Dichotomic P (Ap + MemAct At) At PreA ExtAction_sum Ht gL SyncAction_mem Γ.
  Proof.
    intros D p q hp hq. destruct (D p q hp hq) as [sub | (x & hx & hnx)]; [left | right].
    - intros x hx. apply map_coR_lift, sub, map_coR_lift, hx.
    - exists x. split; [by apply map_coR_lift | intros h; apply hnx, map_coR_lift, h].
  Defined.
End Label_abstraction_lift.

Section Blocking_characterisation.
  Context {P T Ap At : Type} `{Hp : ExtAction Ap} `{Ht : ExtAction At}
    `{SA : !SyncAction Ap At}.
  Context (allblk : ∀ η : At, ¬ non_blocking η).
  Context (outcome : T → Prop).

  Context `{gLtsEqT : !gLtsEq T Ht} `{gLtsObaT : !gLtsOba T _}.
  Context `{TP : !Testing_Predicate outcome gLtsEqT}.

  Context `{gLtsEqP : !gLtsEq P Hp}.

  Notation gP := (@gLtsEq_gLts P Ap Hp gLtsEqP).
  Notation gT := (@gLtsEq_gLts T At Ht gLtsEqT).

  Context `{PIP : !@Prop_of_Inter P T Ap At (@sync _ _ _ _ SA) Hp gP Ht gT}.
  Context (CFIP : @coFiniteImagegLts P At Ap Hp gP Ht SA).

  Context (𝔸 : @Label_abstraction P T Ap At Hp Ht gP gT SA).
  Context (DichP : @Dichotomic P Ap At (At / 𝔸) Hp Ht gP SA ρ[𝔸]).

  Context (tconv : trace At → T) `{!test_convergence_spec tconv}.
  Context (ta : gset (At / 𝔸) → trace At → T)
          `{TA : !test_co_acceptance_set_spec ta ρ[𝔸] }.

  Theorem equivalence_blocking (p q : P) :
    p ⊆ₘᵤₛₜᵢ q ↔
    p ≼꜀ₒ₋ₐₛ[ ρ[𝔸] ] q.
  Proof.
    pose proof (@ParStsSpec_of_union P T _ _ _ _ _ gLtsEqT SyncAction_mem (lift_inter (PI := PIP))) as SLP.
    pose proof (equivalence_fw_label_abstraction outcome (Label_abstraction_lift 𝔸) tconv ta p q
                  (gLtsEqP := liftEq) (FWP := gLtsFWMem_lift allblk)
                  (SYP := lift_inter (PI := PIP)) (CFIP := coFiniteImage_lift (CFI := CFIP))
                  (DichP := Dichotomic_lift ρ[𝔸] DichP)) as E.
    rewrite <- (bhv_pre_lift ρ[𝔸] p q).
    split.
    - intros h. apply (proj1 E). intros t hm.
      eapply (must_lift_to _ (ParStsSpec_of_union gP gLtsEqT) _ SLP), h,
        (must_lift_from _ (ParStsSpec_of_union gP gLtsEqT) _ SLP), hm.
    - intros h. apply (proj2 E) in h. intros t hm.
      eapply (must_lift_from _ (ParStsSpec_of_union gP gLtsEqT) _ SLP), h,
        (must_lift_to _ (ParStsSpec_of_union gP gLtsEqT) _ SLP), hm.
  Qed.
End Blocking_characterisation.
Section Blocking_characterisation_P_Q.
  Context {P Q T A1 A2 At : Type} `{H1 : ExtAction A1} `{H2 : ExtAction A2} `{Ht : ExtAction At}.
  Context `{SA1 : !SyncAction A1 At} `{SA2 : !SyncAction A2 At}.
  Context (allblk : ∀ η : At, ¬ non_blocking η).
  Context (outcome : T → Prop).

  Context `{gLtsEqT : !gLtsEq T Ht} `{gLtsObaT : !gLtsOba T _}.
  Context `{TP : !Testing_Predicate outcome gLtsEqT}.

  Context (gLtsEqP : gLtsEq P H1) (gLtsEqQ : gLtsEq Q H2).

  Notation gP := (@gLtsEq_gLts P A1 H1 gLtsEqP).
  Notation gQ := (@gLtsEq_gLts Q A2 H2 gLtsEqQ).
  Notation gT := (@gLtsEq_gLts T At Ht gLtsEqT).
  Notation gLP := (@lift_left_lts A1 A2 H1 H2 P gP).
  Notation gLQ := (@lift_right_lts A1 A2 H1 H2 Q gQ).

  Context (PIP : @Prop_of_Inter P T A1 At (@sync _ _ _ _ SA1) H1 gP Ht gT).
  Context (PIQ : @Prop_of_Inter Q T A2 At (@sync _ _ _ _ SA2) H2 gQ Ht gT).
  Context (CFIP : @coFiniteImagegLts P At A1 H1 gP Ht SA1)
          (CFIQ : @coFiniteImagegLts Q At A2 H2 gQ Ht SA2).

  #[local] Hint Extern 0 (ExtAction (A1 + A2)) => exact (@ExtAction_sum A1 A2 H1 H2) : typeclass_instances.
  #[local] Instance SAPQ : SyncAction (A1 + A2) At := @SyncAction_sum A1 A2 H1 H2 At Ht SA1 SA2.
  #[local] Instance gLtsEqPQ : gLtsEq (P + Q) (@ExtAction_sum A1 A2 H1 H2) :=
    gLtsEq_sum (gLtsEqP := gLtsEqP) (gLtsEqQ := gLtsEqQ).
  #[local] Instance gLPi : gLts P (@ExtAction_sum A1 A2 H1 H2) := gLP.
  #[local] Instance gLQi : gLts Q (@ExtAction_sum A1 A2 H1 H2) := gLQ.
  #[local] Instance PIPQ : @Prop_of_Inter (P + Q) T (A1 + A2) At (@sync _ _ _ _ SAPQ)
                             ExtAction_sum gLts_sum Ht gT := Prop_of_Inter_sum PIP PIQ.
  #[local] Instance PILP : @Prop_of_Inter P T (A1 + A2) At (@sync _ _ _ _ SAPQ)
                             ExtAction_sum gLP Ht gT := lift_left_inter PIP.
  #[local] Instance PILQ : @Prop_of_Inter Q T (A1 + A2) At (@sync _ _ _ _ SAPQ)
                             ExtAction_sum gLQ Ht gT := lift_right_inter PIQ.

  Notation gPQ := (@gLtsEq_gLts (P + Q) (A1 + A2) ExtAction_sum gLtsEqPQ).

  Context (𝔸 : @Label_abstraction (P + Q) T (A1 + A2) At ExtAction_sum Ht gPQ gT SAPQ).
  Context (DichPQ : @Dichotomic (P + Q) (A1 + A2) At (At / 𝔸) ExtAction_sum Ht gPQ SAPQ ρ[𝔸]).

  Context (tconv : trace At → T) `{!test_convergence_spec tconv}.
  Context (ta : gset (At / 𝔸) → trace At → T)
          `{TA : !test_co_acceptance_set_spec ta ρ[𝔸] }.

  Theorem equivalence_blocking_sum (p : P) (q : Q) :
    p ⊆ₘᵤₛₜᵢ q ↔
    (inl p : P + Q) ≼꜀ₒ₋ₐₛ[ ρ[𝔸] ] (inr q).
  Proof.
    rewrite <- (equivalence_blocking (gLtsEqP := gLtsEqPQ) (SA := SAPQ) (PIP := PIPQ) allblk outcome
                  (coFiniteImage_sum (CFIP := CFIP) (CFIQ := CFIQ)) 𝔸 DichPQ tconv ta (inl p) (inr q)).
    split; intros h t hm.
    - eapply (must_inr_to PIP PIQ), h, (must_inl_from PIP PIQ _ _ hm p eq_refl).
    - eapply (must_inr_from PIP PIQ (inr q) t); [| done].
      eapply h, (must_inl_to PIP PIQ), hm.
  Qed.
End Blocking_characterisation_P_Q.
(* end hide *)
