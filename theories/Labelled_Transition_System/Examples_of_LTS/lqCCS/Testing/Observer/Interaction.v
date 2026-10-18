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
(* begin hide *)
From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list numbers finite sets gmap gmultiset.
From TestingTheory Require Import lqCCS.Harmony_Lemma.Lifted lqCCS.Harmony_Lemma.Paths lqCCS.Harmony_Lemma.States lqCCS.Language.Quantum.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.Program lqCCS.Language.Succ lqCCS.Language.Congruence
  lqCCS.Language.LTS lqCCS.Language.FwLTS.
From TestingTheory Require Import ActTau InListPropHelper
  gLts Bisimulation Lts_OBA Lts_OBA_FB Lts_FW Lts_Finite_Non_Blocking_Chain
  FiniteImageLTS coFiniteImage Subset_Act Termination Convergence WeakTransitions
  coWeakTransition coConvergence StateTransitionSystems
  InteractionBetweenLts MultisetLTSConstruction ForwarderConstruction
  ParallelLTSConstruction SetLTSConstruction
  Must MustE Lift Testing_Predicate
  DefinitionAS Completeness Equivalence
  CompletenessASco SoundnessASco EquivalenceASco TestSpecBridge.
From TestingTheory Require Import lqCCS.Testing.Observer.LTS lqCCS.Testing.Observer.Tests.
(* The lift of an abstraction to the forwarder in [DefinitionAS.v] rests on an
    [Admitted] obligation; as for Erlang, it is replaced below. *)
Remove Hints PreActActionForFW FinitaryPreActActionForFW : typeclass_instances.

Section Characterisation.
  Context `{QM : QuantumModel} `{SC : !Countable St}.

  Notation pconf := (proc * St)%type.

  #[global] Program Instance pconf_FiniteImage : FiniteImagegLts pconf lact.
  Next Obligation.
    intros x 𝜆. eapply (in_list_finite (lsuccs x 𝜆)).
    intros y Hy%bool_decide_unpack. exact Hy.
  Defined.

  Lemma pfw_dual_image_iff (x y : pconf * MO lact) (𝜆 : lact) :
    (∃ 𝜆', dual 𝜆' 𝜆 ∧ x ⟶[𝜆'] y) ↔ x ⟶[co 𝜆] y.
  Proof.
    split.
    - intros (𝜆' & hd & hl). assert (𝜆' = co 𝜆) as ->; [| done].
      apply lact_UniqueDual. by symmetry.
    - intros hl. exists (co 𝜆). split; [| done].
      symmetry. exact (proj2_sig (exists_dual 𝜆)).
  Qed.

  #[global] Instance pconf_FW_coFiniteImage : coFiniteImagegLts (pconf * MO lact) lact.
  Proof.
    unshelve refine {|
      cofolts_states_countable := folts_states_countable;
      cofolts_tau_next_states_finite := _;
      cofolts_next_states_decidable := _;
      cofolts_next_states_finite := _;
    |}.
    - intros p 𝜆 q. destruct (decide (p ⟶[co 𝜆] q)) as [h | h].
      + left. by apply pfw_dual_image_iff.
      + right. intros hc. apply h. by apply pfw_dual_image_iff.
    - intros p 𝜆. unfold dsig.
      eapply (in_list_finite (map proj1_sig (finite.enum (dsig (fun q => p ⟶[co 𝜆] q))))).
      intros q hq%bool_decide_unpack.
      apply list_elem_of_fmap. apply pfw_dual_image_iff in hq.
      exists (dexist q hq). split; [reflexivity | eapply elem_of_enum].
  Defined.

  (* *** What a process accepts *)

  Lemma pmo_out x μ : μ ∈ dom (fmo x) → ∃ c v, μ = LOut c v.
  Proof. intros (c & v & -> & _)%gmultiset_elem_of_dom%fmo_elem. eauto. Qed.

  Lemma pmo_step x μ : μ ∈ dom (fmo x) → ∃ y, x ⟶[μ] y.
  Proof.
    intros Hin%gmultiset_elem_of_dom. destruct (fmo_witness x μ Hin) as [y [_ Hs]]. eauto.
  Qed.

  Lemma pmo_of_step x c v y : x ⟶[LOut c v] y → LOut c v ∈ dom (fmo x).
  Proof.
    intros Hs. apply gmultiset_elem_of_dom. apply pconf_step_def in Hs.
    by eapply fmo_spec1.
  Qed.

  Lemma p_accepts_op (x : pconf) E qs : x ⟶[LOp E qs].
  Proof.
    destruct x as [P ρ].
    assert (Hs : (P, ρ) ⟶[LOp E qs] (P, sop_apply E qs ρ)) by (apply pconf_step_def; constructor).
    apply (lts_performs_spec2 (P, ρ) (ActExt (LOp E qs))). eexists. exact Hs.
  Qed.

  Lemma p_meas_code (x : pconf) M qs n y :
    x ⟶[LMeas M qs n] y → x.2 ≠ szero ∧ ∃ k : Out (meas_of M qs), n = code _ k.
  Proof.
    intros Hs. apply pconf_step_def in Hs.
    inversion Hs as [| | | | | |P ρ M' qs' k Hn]; subst. simpl. split; [|eauto].
    intros ->. apply Hn. unfold meas_branch. apply app_szero.
  Qed.

  Lemma p_accepts_meas (x : pconf) M qs : x.2 ≠ szero → ∃ n, x ⟶[LMeas M qs n].
  Proof.
    destruct x as [P ρ]. intros Hρ. simpl in Hρ.
    destruct (meas_nonzero_branch M qs ρ Hρ) as (k & Hk).
    exists (code _ k).
    assert (Hs : (P, ρ) ⟶[LMeas M qs (code _ k)] (P, meas_branch M qs k ρ))
      by (apply pconf_step_def; by constructor).
    apply (lts_performs_spec2 (P, ρ) (ActExt (LMeas M qs (code _ k)))).
    eexists. exact Hs.
  Qed.

  Lemma p_meas_all (x : pconf) :
    (∃ M qs n, x ⟶[LMeas M qs n]) → ∀ M qs, ∃ n, x ⟶[LMeas M qs n].
  Proof.
    intros (M & qs & n & Hacc) M' qs'. apply lts_performs_spec1 in Hacc as (y & Hs).
    apply p_accepts_meas. by apply p_meas_code in Hs as [? _].
  Qed.

  (* The same for the forwarder: the mailbox takes no part in the memory. *)
  Lemma fw_step_mem (x : pconf * MO lact) μ y :
    x ⟶[μ] y → ¬ is_out μ → (∀ c v, μ ≠ LIn c v) → ∃ p', x.1 ⟶[μ] p'.
  Proof.
    destruct x as [p m]. intros Hs Hb Hi.
    inversion Hs as [𝜆0 a1 a2 b0 l|𝜆0 a0 b1 b2 l|μ1 μ2 a1 a2 b1 b2 eq l1 l2]; subst.
    - simpl. by exists a2.
    - inversion l; subst; exfalso;
        destruct μ as [c v|c v| |]; simpl in *; subst; simpl in *;
        first [by apply Hb | (eapply Hi; reflexivity) | tauto].
  Qed.

  Lemma fw_accepts_op (x : pconf * MO lact) E qs : x ⟶[LOp E qs].
  Proof.
    destruct x as [p m].
    pose proof (p_accepts_op p E qs) as Hr.
    apply lts_performs_spec1 in Hr as (p' & Hs).
    assert (Hs' : (p, m) ⟶[LOp E qs] (p', m)) by (by apply ParLeft).
    apply (lts_performs_spec2 (p, m) (ActExt (LOp E qs))). eexists. exact Hs'.
  Qed.

  Lemma fw_meas_all (x : pconf * MO lact) :
    (∃ M qs n, x ⟶[LMeas M qs n]) → ∀ M qs, ∃ n, x ⟶[LMeas M qs n].
  Proof.
    destruct x as [p m]. intros (M & qs & n & Hacc) M' qs'.
    apply lts_performs_spec1 in Hacc as (y & Hs).
    destruct (fw_step_mem _ _ _ Hs ltac:(by intros ?) ltac:(done)) as (p' & Hp).
    simpl in Hp. apply pconf_step_def in Hp.
    assert (Hacc : p ⟶[LMeas M qs n]).
    { apply (lts_performs_spec2 p (ActExt (LMeas M qs n))).
      eexists. apply pconf_step_def. exact Hp. }
    destruct (p_meas_all p (ex_intro _ M (ex_intro _ qs (ex_intro _ n Hacc))) M' qs')
      as (n' & Hn').
    exists n'. apply lts_performs_spec1 in Hn' as (p'' & Hs').
    assert (Hs'' : (p, m) ⟶[LMeas M' qs' n'] (p'', m)) by (by apply ParLeft).
    apply (lts_performs_spec2 (p, m) (ActExt (LMeas M' qs' n'))).
    eexists. exact Hs''.
  Qed.

  (* *** A process and an observer *)

  Lemma ess_right_step Q μ : μ ∈ dom (tmo Q) ∪ tmem Q → ∃ Q', Q ⟶[μ] Q'.
  Proof.
    intros [Hin|Hin]%elem_of_union.
    - apply gmultiset_elem_of_dom in Hin. by apply tmo_step.
    - by apply tmem_step.
  Qed.

  (* Every synchronisation goes through an output of the process, or an
      output or a memory action of the observer. *)
  Lemma cover_test μ1 Q μ2 Q' :
    Q ⟶[μ2] Q' → μ2 = lco μ1 → (∀ M qs n, μ1 = LMeas M qs n → ∃ k, n = code (meas_of M qs) k) →
    is_out μ1 ∨ μ2 ∈ dom (tmo Q) ∪ tmem Q.
  Proof.
    intros Ht -> Hcode. destruct μ1 as [c v|c v|E qs|M qs n].
    - by left.
    - right. apply elem_of_union_l, gmultiset_elem_of_dom. exact (tmo_of_step _ _ _ _ Ht).
    - right. apply elem_of_union_r. exact (tmem_of_op _ _ _ _ Ht).
    - right. apply elem_of_union_r. destruct (Hcode M qs n eq_refl) as (k & ->).
      exact (tmem_of_meas _ _ _ _ _ Ht).
  Qed.

  #[global] Program Instance pconf_Inter_test : Prop_of_Inter pconf proc lact lact dual :=
    {| lts_essential_actions_left x := dom (fmo x) ;
       lts_essential_actions_right Q := dom (tmo Q) ∪ tmem Q ;
       lts_co_inter_action_left ξ _ := {[ lco ξ ]} ;
       lts_co_inter_action_right ξ _ := {[ lco ξ ]} |}.
  Next Obligation. intros x ξ hin. apply step_witness. by apply pmo_step. Defined.
  Next Obligation. intros Q ξ hin. apply step_witness. by apply ess_right_step. Defined.
  Next Obligation.
    intros x μ1 x' Q μ2 Q' hl1 hl2 hinter.
    assert (Hcode : ∀ M qs n, μ1 = LMeas M qs n → ∃ k, n = code (meas_of M qs) k).
    { intros M qs n ->. apply p_meas_code in hl1 as [_ Hk]. exact Hk. }
    destruct (cover_test μ1 Q μ2 Q' hl2 hinter Hcode) as [Ho|Hr]; [|by right].
    left. destruct μ1 as [c v| | |]; try done. exact (pmo_of_step _ _ _ _ hl1).
  Defined.
  Next Obligation.
    intros x x' ξ μ Q hmem hl hinter; simpl in *. subst. rewrite lco_involutive. set_solver.
  Defined.
  Next Obligation.
    intros Q Q' ξ μ x hmem hl hinter; simpl in *. subst. set_solver.
  Defined.

  #[global] Program Instance pconf_Inter_FW_test :
    Prop_of_Inter (pconf * MO lact) proc lact lact dual :=
    {| lts_essential_actions_left p := dom (fmo p.1) ∪ dom (MO_without_not_nb p.2) ;
       lts_essential_actions_right Q := dom (tmo Q) ∪ tmem Q ;
       lts_co_inter_action_left ξ _ := {[ lco ξ ]} ;
       lts_co_inter_action_right ξ _ := {[ lco ξ ]} |}.
  Next Obligation.
    intros (x, m) ξ hin. simpl in *.
    destruct (decide (ξ ∈ dom (MO_without_not_nb m))) as [hm | hm].
    - apply gmultiset_elem_of_dom in hm.
      apply lts_MO_nb_with_nb_spec1 in hm as (nb & hmem).
      assert (m = {[+ ξ +]} ⊎ (m ∖ {[+ ξ +]})) as heq by multiset_solver.
      exists (x, m ∖ {[+ ξ +]}). apply ParRight.
      rewrite heq at 1. by apply lts_multiset_minus.
    - assert (ξ ∈ dom (fmo x)) as hx by set_solver.
      destruct (step_witness x ξ (pmo_step x ξ hx)) as (y & hl).
      exists (y, m). by apply ParLeft.
  Defined.
  Next Obligation. intros Q ξ hin. apply step_witness. by apply ess_right_step. Defined.
  Next Obligation.
    intros (x, m) μ1 (x', m') Q μ2 Q' hl1 hl2 hinter.
    assert (Hcode : ∀ M qs n, μ1 = LMeas M qs n → ∃ k, n = code (meas_of M qs) k).
    { intros M qs n ->.
      destruct (fw_step_mem _ _ _ hl1 ltac:(by intros ?) ltac:(done)) as (p' & Hp).
      apply p_meas_code in Hp as [_ Hk]. exact Hk. }
    destruct (cover_test μ1 Q μ2 Q' hl2 hinter Hcode) as [Ho|Hr]; [|by right].
    simpl. left. destruct μ1 as [c v| | |]; try done. inversion hl1; subst.
      + apply elem_of_union. left. by eapply pmo_of_step.
      + apply elem_of_union. right.
        assert (non_blocking (LOut c v)) as nb by done.
        eapply non_blocking_action_in_ms in l; eauto.
        apply gmultiset_elem_of_dom.
        apply (lts_MO_nb_with_nb_spec2 (LOut c v) _ nb). multiset_solver.
  Defined.
  Next Obligation.
    intros x x' ξ μ Q hmem hl hinter; simpl in *. subst. rewrite lco_involutive. set_solver.
  Defined.
  Next Obligation.
    intros Q Q' ξ μ x hmem hl hinter; simpl in *. subst. set_solver.
  Defined.

  (* *** The abstraction *)

  #[global] Program Instance pconf_AbsAction :
    AbsAction (gLtsT := obs_gLtsEq) pconf proc lαᴛᴇꜱᴛ lαᴘʀᴏ.
  Next Obligation.
    intros t β β' hb hb' heq hmem. exact (obs_abs_test t β β' hb hb' heq hmem).
  Qed.
  Next Obligation.
    intros x β β' hb hb' heq hmem.
    exact (abs_prog_core x (p_accepts_op x) (p_meas_all x) β β' hb' heq hmem).
  Qed.

  Definition coR_abs_lq (x : pconf) : gset lpre :=
    set_map (λ μ, lαᴘʀᴏ (lαᴛᴇꜱᴛ μ)) (dom (fmo x)) ∪ {[ POpAll ]}
    ∪ (if decide (x.2 = szero) then ∅ else {[ PMeasAll ]}).

  #[global] Program Instance pconf_FinitaryAbsAction :
    FinitaryAbsAction (gLtsT := obs_gLtsEq) pconf proc lαᴛᴇꜱᴛ lαᴘʀᴏ :=
    {| coR_abs := coR_abs_lq |}.
  Next Obligation.
    intros x pre_μ hmem. unfold coR_abs_lq in hmem.
    apply elem_of_union in hmem as [hmem|hmem]; [apply elem_of_union in hmem as [hmem|hmem]|].
    - apply elem_of_map in hmem as (ξ & -> & hin).
      destruct (pmo_out x ξ hin) as (c & v & ->).
      exists (LIn c v). split; [|done].
      exists (LOut c v). split_and!; [|done|by intros ?].
      destruct (pmo_step x _ hin) as (y & hl).
      apply (lts_performs_spec2 x (ActExt (LOut c v))). eexists. exact hl.
    - apply elem_of_singleton in hmem as ->.
      exists (LOp 0 []). split; [|done].
      exists (LOp 0 []). split_and!; [apply p_accepts_op|done|by intros ?].
    - case_decide as Hz; [set_solver|]. apply elem_of_singleton in hmem as ->.
      destruct (p_accepts_meas x 0 [] Hz) as (n & Hn).
      exists (LMeas 0 [] n). split; [|done].
      exists (LMeas 0 [] n). split_and!; [done|done|by intros ?].
  Qed.
  Next Obligation.
    intros pre_μ x (μ & (μ2 & haccept & hsync & hb) & ->).
    simpl in hsync. subst μ. unfold coR_abs_lq.
    apply lts_performs_spec1 in haccept as (y & hl).
    destruct μ2 as [c v|c v|E qs|M qs n].
    - apply elem_of_union_l, elem_of_union_l, elem_of_map.
      exists (LOut c v). split; [done|]. by eapply pmo_of_step.
    - exfalso. by apply hb.
    - apply elem_of_union_l, elem_of_union_r. simpl. set_solver.
    - apply elem_of_union_r. apply p_meas_code in hl as [Hz _].
      rewrite decide_False by done. simpl. set_solver.
  Qed.

  #[global] Program Instance pconf_AbsAction_FW :
    AbsAction (gLtsT := obs_gLtsEq) (pconf * MO lact) proc lαᴛᴇꜱᴛ lαᴘʀᴏ.
  Next Obligation.
    intros t β β' hb hb' heq hmem. exact (obs_abs_test t β β' hb hb' heq hmem).
  Qed.
  Next Obligation.
    intros x β β' hb hb' heq hmem.
    exact (abs_prog_core x (fw_accepts_op x) (fw_meas_all x) β β' hb' heq hmem).
  Qed.

  #[global] Program Instance pconf_FinitaryAbsAction_FW :
    FinitaryAbsAction (gLtsT := obs_gLtsEq) (pconf * MO lact) proc lαᴛᴇꜱᴛ lαᴘʀᴏ :=
    {| FinitaryAbsAction_Abs := pconf_AbsAction_FW ;
       coR_abs p := coR_abs p.1
                    ∪ dom (gmultiset_map (fun x => lαᴘʀᴏ (lαᴛᴇꜱᴛ (co x)))
                             (MO_without_not_nb p.2)) |}.
  Next Obligation.
    intros p pre_mu hmem. destruct p as (p, m). simpl in *.
    apply elem_of_union in hmem. destruct hmem as [in_p | in_M].
    + change (pre_mu ∈ coR_abs p) in in_p. eapply coR_abs_spec1 in in_p.
      destruct in_p as (μ & mem & eq). subst.
      exists μ. split.
      - destruct mem as (μ2 & tr & duo & b).
        eapply lts_performs_spec1 in tr as (p2 & tr).
        exists μ2. repeat split; eauto.
        eapply lts_performs_spec2. exists (p2 ▷ m).
        eapply ParLeft. exact tr.
      - eauto.
    + simpl in *. eapply gmultiset_elem_of_dom, elem_of_gmultiset_map in in_M.
      destruct in_M as (μ & eq & mem).
      apply (lts_MO_nb_with_nb_spec1 μ m) in mem as Hmem. destruct Hmem as (nb & mem2).
      exists (co μ). split; [|exact eq].
      exists μ. split_and!.
      - eapply lts_performs_spec2.
        exists (p, m ∖ {[+ μ +]}).
        eapply ParRight.
        assert (m = {[+ μ +]} ⊎ (m ∖ {[+ μ +]})) as eqm by multiset_solver.
        rewrite eqm at 1.
        eapply lts_multiset_minus. exact nb.
      - exact (proj2_sig (exists_dual μ)).
      - eapply dual_blocks; [exact nb|]. symmetry. exact (proj2_sig (exists_dual μ)).
  Qed.
  Next Obligation.
    intros pre_mu p hmem. destruct hmem as (μ & mem & eq). subst.
    destruct p as (p, m). destruct mem as (μ2 & tr & duo & b).
    eapply lts_performs_spec1 in tr as ((p2 , m2) & eq).
    inversion eq; subst; simpl in *.
    + eapply elem_of_union. left.
      change (lαᴘʀᴏ (lαᴛᴇꜱᴛ μ) ∈ coR_abs p). eapply coR_abs_spec2.
      exists μ. split; [|reflexivity]. exists μ2.
      split_and!; [eapply lts_performs_spec2; eexists; exact l|exact duo|exact b].
    + eapply elem_of_union. right.
      eapply gmultiset_elem_of_dom, elem_of_gmultiset_map.
      destruct (decide (non_blocking μ2)) as [nb2 | b2].
      - exists μ2. split; eauto.
        * assert (μ = co μ2) as ->; [| eauto]. eapply lact_UniqueDual; eauto.
        * eapply non_blocking_action_in_ms in l; eauto. subst.
          apply (lts_MO_nb_with_nb_spec2 μ2 _ nb2). multiset_solver.
      - assert (blocking μ2) as Imp; eauto.
        eapply blocking_action_in_ms in Imp as (mem2 & duo2 & nb2); eauto.
        eapply lact_UniqueDual in duo; eauto. subst. contradiction.
  Qed.

  (* ** The characterisations *)

  (* The must preorder on lqCCS processes [(P, ρ)], on traces. *)
  Corollary must_iff_acceptance_set_lqCCS (x y : pconf) :
    x ⊑ₘᵤₛₜᵢ y ↔ (x ▷ (∅ : MO lact)) ≼ₐₛ (y ▷ (∅ : MO lact)).
  Proof. exact (equivalence_acc_set_and_must_i x y). Qed.
End Characterisation.
(* end hide *)
