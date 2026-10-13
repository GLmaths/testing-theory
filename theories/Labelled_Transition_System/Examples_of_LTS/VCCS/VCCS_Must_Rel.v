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

From Stdlib.Unicode Require Import Utf8.
From Stdlib Require Import Relations.Relation_Definitions Classes.RelationClasses.
From stdpp Require Import base tactics decidable countable finite gmap gmultiset list.
From TestingTheory Require Import ActTau gLts SyncActions Bisimulation Subset_Act
  InteractionBetweenLts MultisetLTSConstruction MemAction InteractionUnion MemForwarder
  ForwarderMem LiftMem InputOutputActions VCCS_Instance coFiniteImage VCCS_CoFiniteImage InListPropHelper
  Testing_Predicate Must VCCS_ta_tc_gen
  LabelAbstraction LabelAdmissible LabelAdmissibleFw DefinitionASrel EquivalenceASsync BridgeASsync BlockingLift.
From TestingTheory Require Completeness CompletenessASsync.

#[local] Hint Mode ExtAction ! : typeclass_instances.

Section VCCS_Mem.
  Context `{VP : VCCS_Parameters}.

  Notation A := (ExtAct TypeOfActions).

  Definition vccs_mem_ess (m : MO (MemAct A)) : gset (MemAct A) :=
    filter (λ a, non_blocking a) (dom m).

  Definition vccs_mem_co_left (ξ : MemAct A) (p : proc) : gset A :=
    match ξ with msg η => {[ co η ]} | cobar _ => ∅ end.

  Lemma vccs_mem_ess_spec (m : MO (MemAct A)) ξ :
    ξ ∈ vccs_mem_ess m → {m' | m ⟶[ξ] m'}.
  Proof.
    intros h. unfold vccs_mem_ess in h. apply elem_of_filter in h as [nb hd].
    apply gmultiset_elem_of_dom in hd.
    exists (m ∖ {[+ ξ +]}).
    rewrite (gmultiset_disj_union_difference' ξ m hd) at 1.
    by apply lts_multiset_minus.
  Defined.

  #[global] Program Instance VCCS_Inter_mem :
    Prop_of_Inter proc (MO (MemAct A)) A (MemAct A) fw_inter_mem :=
    {| lts_essential_actions_left p := ∅;
       lts_essential_actions_right := vccs_mem_ess;
       lts_co_inter_action_left := vccs_mem_co_left;
       lts_co_inter_action_right ξ m := ∅ |}.
  Next Obligation. intros p ξ h. exfalso. set_solver. Defined.
  Next Obligation. intros m ξ h. exact (vccs_mem_ess_spec m ξ h). Defined.
  Next Obligation.
    intros p μ1 p' m μ2 m' l1 l2 hi. right.
    destruct μ2 as [η | η]; simpl in hi; [| done].
    destruct hi as [_ nb]. apply mem_msg_inv in l2 as [-> _].
    simpl. unfold vccs_mem_ess. apply elem_of_filter. split; [exact nb |].
    apply gmultiset_elem_of_dom. multiset_solver.
  Qed.
  Next Obligation.
    intros p p' ξ μ m hm l hi.
    destruct ξ as [η | η]; simpl in hi; [| done].
    destruct hi as [hs _]. simpl.
    rewrite (VCCS_UniqueDual μ η); [set_solver | by symmetry].
  Qed.
  Next Obligation. intros m m' ξ μ p h. exfalso. set_solver. Qed.
End VCCS_Mem.
Section VCCS_Fw_test.
  Context `{VP : VCCS_Parameters}.

  Notation A := (ExtAct TypeOfActions).

  #[local] Existing Instance toFwEq.

  Definition vccs_fw_ess (pm : proc * MO (MemAct A)) : gset (A + MemAct A) :=
    set_map (λ a, inl (ActOut a)) (outputs_of pm.1) ∪ set_map inr (vccs_mem_ess pm.2).

  Definition vccs_test_ess (q : proc) : gset A := set_map ActOut (outputs_of q).

  Definition vccs_fw_co_left (ξ : A) (pm : proc * MO (MemAct A)) : gset (A + MemAct A) :=
    match ξ with
    | ActOut a => {[ inl (ActIn a); inr (cobar (ActOut a)) ]}
    | ActIn a => {[ inl (ActOut a); inr (msg (ActOut a)) ]}
    end.

  Definition vccs_fw_co_right (ξ : A + MemAct A) (q : proc) : gset A :=
    match ξ with
    | inl μ => {[ co μ ]}
    | inr (msg η) => {[ co η ]}
    | inr (cobar η) => {[ η ]}
    end.

  Lemma vccs_fw_ess_spec (pm : proc * MO (MemAct A)) ξ :
    ξ ∈ vccs_fw_ess pm → {y | pm ⟶[ξ] y}.
  Proof.
    destruct pm as (p, m). intros h. unfold vccs_fw_ess in h. simpl in h.
    destruct ξ as [μ | ζ].
    - destruct μ as [a | a].
      + exfalso. apply elem_of_union in h as [h | h]; apply elem_of_map in h as (? & e & _); done.
      + assert (ha : a ∈ outputs_of p).
        { apply elem_of_union in h as [h | h]; apply elem_of_map in h as (? & e & h); [| done].
          by injection e as ->. }
        destruct (outputs_of_spec2 p a ha) as (q & l).
        exists (q, m). by apply fw_inl.
    - assert (hζ : ζ ∈ vccs_mem_ess m).
      { apply elem_of_union in h as [h | h]; apply elem_of_map in h as (? & e & h); [done |].
        by injection e as ->. }
      destruct (vccs_mem_ess_spec m ζ hζ) as (m' & l).
      exists (p, m'). by apply (ParRight (ActExt (inr ζ))).
  Defined.

  Lemma vccs_test_ess_spec (q : proc) ξ :
    ξ ∈ vccs_test_ess q → {q' | q ⟶[ξ] q'}.
  Proof.
    intros h. unfold vccs_test_ess in h. destruct ξ as [a | a].
    - exfalso. apply elem_of_map in h as (? & e & _). done.
    - apply outputs_of_spec2. apply elem_of_map in h as (? & e & h). by injection e as ->.
  Defined.

  #[global] Program Instance VCCS_Inter_fw_test :
    Prop_of_Inter (proc * MO (MemAct A)) proc (A + MemAct A) A sync :=
    {| lts_essential_actions_left := vccs_fw_ess;
       lts_essential_actions_right := vccs_test_ess;
       lts_co_inter_action_left := vccs_fw_co_left;
       lts_co_inter_action_right := vccs_fw_co_right |}.
  Next Obligation. intros. exact (vccs_fw_ess_spec _ _ H). Defined.
  Next Obligation. intros. exact (vccs_test_ess_spec _ _ H). Defined.
  Next Obligation.
    intros [p m] μ1 y q μ2 q' l1 l2 hs. simpl in hs.
    destruct μ1 as [μ | [η | η]]; simpl in hs.
    - apply fw_inl_inv in l1 as (p' & -> & l1).
      destruct μ as [a | a].
      + right. apply simplify_match_input in hs. subst.
        change (ActOut a ∈ vccs_test_ess q). unfold vccs_test_ess.
        apply elem_of_map. exists a. split; [done | by eapply outputs_of_spec1].
      + left. change (inl (ActOut a) ∈ vccs_fw_ess (p, m)). unfold vccs_fw_ess.
        apply elem_of_union_l, elem_of_map. exists a. split; [done |].
        by eapply outputs_of_spec1.
    - apply fw_msg_inv in l1 as (m' & -> & -> & nb). left.
      change (inr (msg η) ∈ vccs_fw_ess (p, {[+ msg η +]} ⊎ m')). unfold vccs_fw_ess.
      apply elem_of_union_r, elem_of_map. exists (msg η). split; [done |].
      unfold vccs_mem_ess. apply elem_of_filter. split; [exact nb |].
      apply gmultiset_elem_of_dom. simpl. multiset_solver.
    - apply fw_cobar_inv in l1 as [-> nb]. destruct nb.
  Qed.
  Next Obligation.
    intros [p m] y ξ μ q hξ l hs. unfold vccs_test_ess in hξ.
    apply elem_of_map in hξ as (a & -> & _). simpl.
    destruct μ as [μ | [η | η]]; simpl in hs.
    - destruct μ as [b | b]; [| by apply simplify_match_output in hs].
      apply simplify_match_input in hs. injection hs as ->. set_solver.
    - exfalso. apply fw_msg_inv in l as (m' & _ & _ & nb). destruct nb.
    - subst. set_solver.
  Qed.
  Next Obligation.
    intros q q' ξ μ pm hξ l hs. simpl.
    destruct ξ as [μ0 | [η | η]]; simpl in hs.
    - rewrite (VCCS_UniqueDual μ μ0 hs). set_solver.
    - rewrite (VCCS_UniqueDual μ η hs). set_solver.
    - subst. set_solver.
  Qed.
End VCCS_Fw_test.
Section VCCS_Fw_cofinite.
  Context `{VP : VCCS_Parameters}.

  Notation A := (ExtAct TypeOfActions).

  #[local] Existing Instance toFwEq.

  Definition vccs_fw_tau_set (p : proc) (m : MO (MemAct A)) : list (proc * MO (MemAct A)) :=
    map (λ q, (`q, m)) (enum (dsig (λ q, p ⟶ q)))
    ++ (elements m ≫= (λ a, match a with
          | msg η => map (λ q, (`q, m ∖ {[+ msg η +]}))
                       (enum (dsig (λ q, ∃ α' : A, sync α' η ∧ p ⟶[α'] q)))
          | cobar _ => []
          end)).

  Lemma vccs_fw_tau_set_spec (p : proc) (m : MO (MemAct A)) y :
    (p, m) ⟶ y → y ∈ vccs_fw_tau_set p m.
  Proof.
    intros l. apply fw_tau_inv in l as [(p' & -> & l) | (p' & μ & η & m' & -> & l & hs & nb & ->)].
    - apply elem_of_app. left. apply list_elem_of_fmap.
      exists (dexist p' l). split; [done | apply elem_of_enum].
    - apply elem_of_app. right. apply list_elem_of_bind. exists (msg η). split.
      + apply list_elem_of_fmap. exists (dexist p' (ex_intro _ μ (conj hs l))). split.
        * simpl. f_equal. multiset_solver.
        * apply elem_of_enum.
      + apply gmultiset_elem_of_elements. multiset_solver.
  Qed.

  Lemma vccs_fw_sync_iff (pm y : proc * MO (MemAct A)) (α : A) :
    (∃ α', sync α' α ∧ pm ⟶[α'] y) ↔
      pm ⟶[inl (co α)] y ∨ pm ⟶[inr (msg (co α))] y ∨ pm ⟶[inr (cobar α)] y.
  Proof.
    split.
    - intros ([μ | [η | η]] & hs & l); simpl in hs.
      + left. rewrite <- (VCCS_UniqueDual μ α); [exact l | by symmetry].
      + right; left. rewrite <- (VCCS_UniqueDual η α); [exact l | by symmetry].
      + right; right. by subst.
    - intros [l | [l | l]].
      + exists (inl (co α)). split; [| exact l]. simpl. symmetry. exact (proj2_sig (exists_dual α)).
      + exists (inr (msg (co α))). split; [| exact l]. simpl. symmetry. exact (proj2_sig (exists_dual α)).
      + exists (inr (cobar α)). split; [| exact l]. done.
  Qed.

  Definition vccs_fw_ext_set (p : proc) (m : MO (MemAct A)) (α : A) : list (proc * MO (MemAct A)) :=
    map (λ q, (`q, m)) (enum (dsig (λ q, ∃ α' : A, sync α' α ∧ p ⟶[α'] q)))
    ++ [(p, m ∖ {[+ msg (co α) +]}); (p, {[+ msg α +]} ⊎ m)].

  Lemma vccs_fw_ext_set_spec (p : proc) (m : MO (MemAct A)) (α : A) y :
    (∃ α', sync α' α ∧ (p, m) ⟶[α'] y) → y ∈ vccs_fw_ext_set p m α.
  Proof.
    intros ([μ | [η | η]] & hs & l); simpl in hs.
    - apply fw_inl_inv in l as (p' & -> & l).
      apply elem_of_app. left. apply list_elem_of_fmap.
      exists (dexist p' (ex_intro _ μ (conj hs l))). split; [done | apply elem_of_enum].
    - apply fw_msg_inv in l as (m' & -> & -> & nb).
      rewrite (VCCS_UniqueDual η α) by (by symmetry).
      apply elem_of_app. right. apply elem_of_cons. left. f_equal. multiset_solver.
    - apply fw_cobar_inv in l as [-> nb]. subst.
      apply elem_of_app. right. right. left.
  Qed.

  Definition vccs_fw_tau_finite (pm : proc * MO (MemAct A)) : Finite (dsig (λ y, pm ⟶ y)).
  Proof.
    destruct pm as (p, m). unfold dsig.
    eapply (in_list_finite (vccs_fw_tau_set p m)).
    intros y h%bool_decide_unpack. by apply vccs_fw_tau_set_spec.
  Defined.

  Definition vccs_fw_ext_dec (pm : proc * MO (MemAct A)) (α : A) y :
    Decision (∃ α', sync α' α ∧ pm ⟶[α'] y).
  Proof.
    destruct (decide (pm ⟶[inl (co α)] y ∨ pm ⟶[inr (msg (co α))] y ∨ pm ⟶[inr (cobar α)] y))
      as [h | h]; [left | right]; by rewrite vccs_fw_sync_iff.
  Defined.

  #[local] Existing Instance vccs_fw_ext_dec.

  Definition vccs_fw_ext_finite (pm : proc * MO (MemAct A)) (α : A) :
    Finite (dsig (λ y, ∃ α', sync α' α ∧ pm ⟶[α'] y)).
  Proof.
    destruct pm as (p, m). unfold dsig.
    eapply (in_list_finite (vccs_fw_ext_set p m α)).
    intros y h%bool_decide_unpack. by apply vccs_fw_ext_set_spec.
  Defined.

  #[global] Instance VCCS_fw_coFiniteImage : coFiniteImagegLts (proc * MO (MemAct A)) A :=
    {| cofolts_states_countable := _;
       cofolts_tau_next_states_finite := vccs_fw_tau_finite;
       cofolts_next_states_decidable := vccs_fw_ext_dec;
       cofolts_next_states_finite := vccs_fw_ext_finite |}.
End VCCS_Fw_cofinite.

Section VCCS_Rel.
  Context `{VP : VCCS_Parameters}.

  Notation A := (ExtAct TypeOfActions).

  Definition Γᴠ (μ : A) : PreAct := 𝝳ᴠᴄᴄꜱ (Φᴠᴄᴄꜱ μ).
  Definition Rᴠ : relation A := ker_rel Γᴠ.

  Definition VCCS_Inter_sync : Prop_of_Inter proc proc A A sync := Interaction_between_parallel_VCCS.

  Definition vccs_repr (x : PreAct) : A :=
    match x with
    | Inputs_on c => ActIn (c , cst O)
    | Outputs_on c => ActOut (c , cst O)
    end.

  Lemma vccs_repr_spec x : 𝝳ᴠᴄᴄꜱ (Φᴠᴄᴄꜱ (vccs_repr x)) = x.
  Proof. by destruct x. Qed.

  Definition VCCS_admissible : @LA_admissible proc proc A _ _ A _ _ _ Rᴠ :=
    LA_admissible_of_AbsAction (AbsPT := AbsVCCS).

  Definition VCCS_finitary : FinitaryLA proc Rᴠ :=
    FinitaryLA_of_Finitary vccs_repr vccs_repr_spec (FA := FinitaryAbsVCCS).

  Lemma VCCS_admissible_mem : LA_admissible_mem (T := proc) Rᴠ.
  Proof. intros η β β'' nb. destruct nb. Qed.

  Definition vccs_co_rep (η : A) : list A := [].

  Lemma vccs_co_rep_sub η x : non_blocking η → x ∈ vccs_co_rep η → dual η x.
  Proof. intros nb. destruct nb. Qed.

  Lemma vccs_co_rep_cover η β : non_blocking η → dual η β → ∃ x, x ∈ vccs_co_rep η ∧ Rᴠ β x.
  Proof. intros nb. destruct nb. Qed.

  #[local] Existing Instance VCCS_Inter_sync.

  #[local] Instance VCCS_tconv_core : CompletenessASsync.test_convergence_spec gen_conv :=
    test_convergence_spec_bridge gen_conv gen_conv_gen_spec_conv_inst.

  #[local] Instance VCCS_ta_core :
    CompletenessASsync.test_co_acceptance_set_spec (LA_quotient Rᴠ) (ta_ker Γᴠ gen_acc) (LA_class Rᴠ) :=
    ta_ker_bridge Γᴠ gen_acc gen_acc_gen_spec_acc_inst.

  Definition must_iff_rel_VCCS :=
    equivalence_rel_and_must_i_sync_co_trace_proc (P := proc) (Q := proc) (T := proc)
      Rᴠ good_VCCS
      VCCS_admissible VCCS_finitary VCCS_admissible VCCS_finitary
      VCCS_admissible_mem vccs_co_rep vccs_co_rep_sub vccs_co_rep_cover
      gen_conv (ta_ker Γᴠ gen_acc).
End VCCS_Rel.

Section VCCS_Rel_std.
  Context `{VP : VCCS_Parameters}.

  Notation A := (ExtAct TypeOfActions).

  Definition VCCS_union_sts : ParSts proc proc _ VCCS_gLtsEq :=
    @ParSts_of_union proc proc A A _ _ _ VCCS_gLtsEq SyncAction_of_dual VCCS_Inter_sync.

  Lemma VCCS_ctx_std_union (p q : proc) :
    p ⊑ₘᵤₛₜᵢ q ↔
      @ctx_pre proc A _ _ proc _ proc A _ VCCS_gLtsEq good_VCCS _ SyncAction_of_dual
        VCCS_union_sts VCCS_union_sts p q.
  Proof.
    pose proof (@ParStsSpec_of_union proc proc A A _ _ _ VCCS_gLtsEq SyncAction_of_dual VCCS_Inter_sync) as SU.
    split; intros h t hp.
    - eapply (must_transfer _ _ _ SU), h, (must_transfer _ _ SU _), hp.
    - eapply (must_transfer _ _ SU _), h, (must_transfer _ _ _ SU), hp.
  Qed.

  Definition must_iff_rel_VCCS_std (p q : proc) :=
    iff_trans (VCCS_ctx_std_union p q) (must_iff_rel_VCCS p q).
End VCCS_Rel_std.
Section VCCS_Rel_direct.
  Context `{VP : VCCS_Parameters}.

  Notation A := (ExtAct TypeOfActions).

  #[local] Instance VCCS_tconv_core' : CompletenessASsync.test_convergence_spec gen_conv :=
    test_convergence_spec_bridge gen_conv gen_conv_gen_spec_conv_inst.

  #[local] Instance VCCS_ta_core' :
    CompletenessASsync.test_co_acceptance_set_spec (LA_quotient Rᴠ) (ta_ker Γᴠ gen_acc) (LA_class Rᴠ) :=
    ta_ker_bridge Γᴠ gen_acc gen_acc_gen_spec_acc_inst.

  Lemma vccs_all_blocking (η : A) : ¬ non_blocking η.
  Proof. intros nb. destruct nb. Qed.

  Definition must_iff_rel_VCCS_direct :=
    equivalence_rel_blocking (P := proc) (Q := proc) (T := proc)
      vccs_all_blocking Rᴠ good_VCCS
      VCCS_Inter_sync VCCS_Inter_sync VCCS_gLtsCoFiniteImage VCCS_gLtsCoFiniteImage
      (ParSts_of_inter _ VCCS_gLtsEq) (ParStsSpec_of_inter _ VCCS_gLtsEq)
      (ParSts_of_inter _ VCCS_gLtsEq) (ParStsSpec_of_inter _ VCCS_gLtsEq)
      VCCS_admissible VCCS_admissible VCCS_finitary VCCS_finitary
      gen_conv (ta_ker Γᴠ gen_acc).
End VCCS_Rel_direct.
(* end hide *)
