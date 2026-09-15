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
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base tactics decidable countable list gmap.
From TestingTheory Require Import ActTau gLts InputOutputActions Bisimulation Testing_Predicate Completeness
  PAL_Syntax PAL_Alt_LTS PAL_Alt_Congruence PAL_Alt_Phi PAL_Alt_AbsAction PAL_Good PAL_Alt_Tests.

(* * The tests of the alternative LTS of PAL satisfy the specifications of [Completeness]

   With [⋍ = cgr]:
   - [gen_test_spec]: for [gen s = gen_test s p] with [p] closed and not
     good, the axioms (1)-(6) of [test_spec];
   - [t_conv_convergence_spec]: [test_convergence_spec] for [t_conv];
   - [ta_co_acceptance_set_spec]: [test_co_acceptance_set_spec] for [ta],
     with [Γ = 𝝳ᴇᴠ ∘ Φᴀᴘᴀʟ], that is the event of the label. *)

Section PAL_Alt_TestSpec.
  Context (Val : Type) `{Countable Val} `{!Inhabited Val}.

  Notation term := (term Val).
  Notation eot := (eot Val).
  Notation label := (label Val).
  Notation ltemplate := (ltemplate Val).
  Notation ltuple := (ltuple Val).
  Notation PALA_Act := (PALA_Act Val).
  Notation Event := (Event Val).
  Notation good := (good_PAL Val).
  Notation gen_test := (gen_test Val).
  Notation isucc := (isucc Val).
  Notation ac_t := (ac_t Val).
  Notation guard_l := (guard_l Val).
  Notation pattern_from := (pattern_from Val).
  Notation it_from := (it_from Val).
  Notation lf_tfield := (lf_tfield Val).
  Notation lf_ofield := (lf_ofield Val).

  (** Infer the action type of [⟶], [⟶[μ]], ... from the LTS on terms. *)
  #[local] Hint Mode ExtAction ! : typeclass_instances.
  Open Scope pal_scope.


  (** ** Guards *)

  (** The variables of [guard_l k] are at least [k]. *)
  Lemma subst_guard_skip (σ : vsubst Val) j v k l :
    j < k → subst_bexp ((j, v) :: σ) (guard_l k l) = subst_bexp σ (guard_l k l).
  Proof.
    revert k. induction l as [|f l IH]; intros k hlt; [done |].
    destruct f; simpl; [| apply IH; lia | apply IH; lia].
    rewrite decide_False by lia. f_equal. apply IH. lia.
  Qed.

  (** After receiving [ltuple l'], the guard of [l] says whether [l'] is [l]. *)
  Lemma eval_guard k l l' :
    ltemplate l' = ltemplate l →
    eval_bexp (subst_bexp (build_subst (it_from k (ltemplate l)) (ltuple l')) (guard_l k l))
    = Some (bool_decide (ltuple l' = ltuple l)).
  Proof.
    revert k l'. induction l as [|f l IH]; intros k l';
      unfold PAL_Alt_LTS.ltemplate, PAL_Alt_LTS.ltuple in *; intros e.
    - destruct l'; [| discriminate]. simpl. by rewrite ?bool_decide_true.
    - destruct l' as [|f' l']; [discriminate |]. simpl in e. injection e as ef e.
      destruct f, f'; simpl in ef; try discriminate; simpl.
      + rewrite decide_True by done. rewrite subst_guard_skip by lia. rewrite IH by done. simpl.
        f_equal. repeat case_bool_decide; simpl; congruence.
      + rewrite IH by done. f_equal. injection ef as <-.
        repeat case_bool_decide; simpl; congruence.
      + rewrite IH by done. f_equal. repeat case_bool_decide; simpl; congruence.
  Qed.

  (** ** Closed terms *)

  Definition closed (E : term) := ∀ σ : vsubst Val, subst_term σ E = E.

  Lemma subst_eot_to_tuple σ (ot : eot) : subst_tuple σ (eot_to_tuple ot) = eot_to_tuple ot.
  Proof.
    induction ot as [|[|v] ot IH]; [done | ..];
      unfold subst_tuple, eot_to_tuple in *; simpl; by rewrite IH.
  Qed.

  Lemma subst_pattern_from σ i tp : subst_tuple σ (pattern_from i tp) = pattern_from i tp.
  Proof.
    revert i. induction tp as [|[|v|] tp IH]; intros i; [done | ..];
      unfold subst_tuple in *; simpl; by rewrite IH.
  Qed.

  Lemma vlookup_elem (σ : vsubst Val) x v : vlookup σ x = Some v → (x, v) ∈ σ.
  Proof.
    induction σ as [|[y w] σ IH]; simpl; [done |].
    case_decide as hxy; intros e.
    - injection e as <-. subst. apply elem_of_cons. by left.
    - apply elem_of_cons. right. by apply IH.
  Qed.

  Lemma vlookup_drop xs (σ : vsubst Val) x : x ∈ xs → vlookup (vsubst_drop xs σ) x = None.
  Proof.
    intros hx. destruct (vlookup (vsubst_drop xs σ) x) as [w|] eqn:e; [| done].
    apply vlookup_elem in e. unfold vsubst_drop in e.
    apply list_elem_of_filter in e as [hp _]. simpl in hp.
    rewrite bool_decide_true in hp by done. by destruct hp.
  Qed.

  Lemma subst_guard_none (σ : vsubst Val) k l :
    (∀ x, x ∈ tuple_formals (pattern_from k (map lf_tfield l)) → vlookup σ x = None) →
    subst_bexp σ (guard_l k l) = guard_l k l.
  Proof.
    revert k. induction l as [|f l IH]; intros k hnone; [done |].
    destruct f; simpl in *.
    - rewrite (hnone k) by (simpl; set_solver). f_equal. apply IH.
      intros x hx. apply hnone. simpl. set_solver.
    - apply IH. intros x hx. apply hnone. simpl. set_solver.
    - apply IH. intros x hx. apply hnone. simpl. set_solver.
  Qed.

  Lemma gen_test_closed s p : closed p → closed (gen_test s p).
  Proof.
    intros hp. induction s as [|[l|ot] s IH]; intros σ; simpl; [apply hp | |].
    - rewrite subst_pattern_from, IH, subst_guard_none; [done |].
      intros x hx. by apply vlookup_drop.
    - by rewrite subst_eot_to_tuple, IH.
  Qed.

  Lemma isucc_closed : closed isucc.
  Proof. by intros σ. Qed.

  Lemma ac_t_closed e : closed (ac_t e).
  Proof. intros σ. destruct e; simpl; by rewrite ?subst_eot_to_tuple, ?subst_pattern_from. Qed.

  Lemma sum_ac_closed E : closed (sum_ac Val E).
  Proof.
    intros σ. unfold sum_ac. induction (elements E) as [|e l IH]; simpl; [done |].
    rewrite IH. f_equal. apply ac_t_closed.
  Qed.

  (** ** Steps of the tests *)

  Lemma par_nil_l_cgr (E : term) : (𝟘 ‖ E) ⋍ E.
  Proof. etransitivity; [apply cgr_once, cgr_par_com | apply cgr_once, cgr_par_nil]. Qed.

  (** Steps of an input on the pattern of a template. *)
  Lemma in_pattern_step_inv tp E μ q :
    (in( pattern_from 0 tp ) • E) ⟶[μ] q →
    ∃ l, μ = AIn Val l ∧ ltemplate l = tp ∧ q = subst_term (build_subst (it_from 0 tp) (ltuple l)) E.
  Proof.
    intros h. inversion h; subst.
    match goal with hev : eval_in_tuple _ = Some _ |- _ =>
      rewrite eval_pattern_from in hev; injection hev as <- end.
    match goal with ht : template_of _ _ = _ |- _ => rewrite template_of_it_from in ht end.
    eexists. split_and!; [done | by symmetry | done].
  Qed.

  (** Steps of the output of a test. *)
  Lemma out_lmerge_step_inv ot F μ q :
    ((out( eot_to_tuple ot ) • 𝟘) ⌊ F) ⟶[μ] q → μ = AOut Val ot ∧ q = (𝟘 ‖ F).
  Proof.
    intros h. inversion h; subst.
    match goal with h' : lts_step_a _ (t_out _ _) _ _ |- _ => inversion h'; subst end.
    match goal with hev : eval_out_tuple _ = Some _ |- _ =>
      rewrite eval_out_eot_to_tuple in hev; injection hev as <- end.
    done.
  Qed.

  Lemma gen_test_ext_inv p β s μ t :
    closed p → gen_test (β :: s) p ⟶[μ] t →
    (μ = β ∧ t ⋍ gen_test s p) ∨ (μ ≠ β ∧ good t).
  Proof.
    intros hp. destruct β as [l|ot]; cbn [gen_test]; intros h; inversion h; subst.
    - match goal with h' : lts_step_a _ (t_in _ _) _ _ |- _ =>
        apply in_pattern_step_inv in h' as (l0 & -> & htp & ->) end.
      cbn [subst_term]. rewrite (gen_test_closed s p hp).
      pose proof (eval_guard 0 l l0 htp) as hg.
      destruct (decide (ltuple l0 = ltuple l)) as [heq | hne].
      + assert (l0 = l) as -> by (apply (label_inj Val); [done | done]).
        left. split; [done |]. apply cgr_once, cgr_if_true. rewrite hg. by rewrite bool_decide_true.
      + right. split.
        * intros e. injection e as <-. by apply hne.
        * apply good_if_false; [| apply good_success]. rewrite hg. by rewrite bool_decide_false.
    - match goal with h' : lts_step_a _ isucc _ _ |- _ => inversion h' end.
    - match goal with h' : lts_step_a _ (t_lmerge _ _) _ _ |- _ =>
        apply out_lmerge_step_inv in h' as [-> ->] end.
      left. split; [done | apply par_nil_l_cgr].
    - match goal with h' : lts_step_a _ isucc _ _ |- _ => inversion h' end.
  Qed.

  Lemma gen_test_next p μ s : closed p → gen_test (μ :: s) p ⟶⋍[μ] gen_test s p.
  Proof.
    intros hp. destruct μ as [l|ot].
    - assert (gen_test (AIn _ l :: s) p ⟶[AIn _ l]
        (subst_term (build_subst (it_from 0 (ltemplate l)) (ltuple l))
           (IF guard_l 0 l THEN gen_test s p ELSE ✓))) as hstep.
      { cbn [gen_test]. apply aar4_l, aar1; [apply eval_pattern_from | by rewrite template_of_it_from]. }
      destruct (gen_test_ext_inv p (AIn _ l) s (AIn _ l) _ hp hstep) as [[_ heq] | [hne _]].
      + by exists (subst_term (build_subst (it_from 0 (ltemplate l)) (ltuple l))
             (IF guard_l 0 l THEN gen_test s p ELSE ✓)).
      + by destruct hne.
    - exists (𝟘 ‖ gen_test s p). split.
      + cbn [gen_test]. apply aar4_l, aar6, aar3, eval_out_eot_to_tuple.
      + apply par_nil_l_cgr.
  Qed.

  Lemma gen_test_tau_good p β s t : gen_test (β :: s) p ⟶ t → good t.
  Proof.
    intros h. destruct β as [l|ot]; simpl in h; inversion h; subst.
    - match goal with h' : lts_step_a _ (t_in _ _) τ _ |- _ => inversion h' end.
    - apply good_echoice_r. by eapply isucc_tau_good.
    - match goal with h' : lts_step_a _ (t_lmerge _ _) τ _ |- _ => inversion h'; subst end.
      match goal with h' : lts_step_a _ (t_out _ _) τ _ |- _ => inversion h'; subst end. congruence.
    - apply good_echoice_r. by eapply isucc_tau_good.
  Qed.

  (** ** The tests of one event *)

  Lemma ac_t_ext_inv e μ q : ac_t e ⟶[μ] q → Φᴀᴘᴀʟ Val μ = e ∧ good q.
  Proof.
    destruct e as [tp|ot]; cbn [ac_t]; intros h.
    - apply in_pattern_step_inv in h as (l & -> & htp & ->).
      split; [cbn [Φᴀᴘᴀʟ]; by rewrite htp | apply good_success].
    - apply out_lmerge_step_inv in h as [-> ->].
      split; [done | apply good_par_r, good_success].
  Qed.

  Lemma ac_t_no_tau e q : ¬ ac_t e ⟶ q.
  Proof.
    destruct e as [tp|ot]; simpl; intros h; inversion h; subst.
    match goal with h' : lts_step_a _ (t_out _ _) τ _ |- _ => inversion h'; subst end. congruence.
  Qed.

  Lemma ac_t_step e : ∃ μ q, ac_t e ⟶[μ] q ∧ Φᴀᴘᴀʟ Val μ = e.
  Proof.
    destruct e as [tp|ot]; simpl.
    - exists (AIn _ (label_witness Val tp)). eexists. split.
      + apply aar1; [apply eval_pattern_from |].
        by rewrite template_of_it_from, ltemplate_label_witness.
      + cbn [Φᴀᴘᴀʟ]. by rewrite ltemplate_label_witness.
    - exists (AOut _ ot). eexists. split; [| done].
      apply aar6, aar3, eval_out_eot_to_tuple.
  Qed.

  Notation sum_list l := (foldr (λ e acc, ac_t e □ acc) 𝟘 l).

  Lemma sum_list_ext_inv l μ q : sum_list l ⟶[μ] q → Φᴀᴘᴀʟ Val μ ∈ l ∧ good q.
  Proof.
    revert q. induction l as [|e l IH]; simpl; intros q h; inversion h; subst.
    - match goal with h' : lts_step_a _ (ac_t _) _ _ |- _ => apply ac_t_ext_inv in h' as [-> hg] end.
      split; [apply elem_of_cons; by left | done].
    - match goal with h' : lts_step_a _ (foldr _ _ _) _ _ |- _ => apply IH in h' as [hin hg] end.
      split; [apply elem_of_cons; by right | done].
  Qed.

  Lemma sum_list_no_tau l q : ¬ sum_list l ⟶ q.
  Proof.
    revert q. induction l as [|e l IH]; simpl; intros q h; inversion h; subst;
      [eapply ac_t_no_tau; eassumption | eapply IH; eassumption].
  Qed.

  Lemma sum_list_step l e : e ∈ l → ∃ μ q, sum_list l ⟶[μ] q ∧ Φᴀᴘᴀʟ Val μ = e.
  Proof.
    induction l as [|e' l IH]; intros hin; [by apply elem_of_nil in hin |].
    apply elem_of_cons in hin as [<- | hin].
    - destruct (ac_t_step e) as (μ & q & hq & he). exists μ, q. split; [| done].
      simpl. by apply aar4_l.
    - destruct (IH hin) as (μ & q & hq & he). exists μ, q. split; [| done].
      simpl. by apply aar4_r.
  Qed.

  Lemma no_step_refuses (p : term) α : (∀ q, ¬ p ⟶{α} q) → p ↛{α}.
  Proof.
    intros hn. destruct (decide (p ↛{α})) as [h|h]; [done |].
    destruct (lts_refuses_spec1 p α h) as [q hq]. by destruct (hn q).
  Qed.

  (** ** Instances *)

  Lemma gen_test_spec p : closed p → ¬ good p → test_spec (λ s, gen_test s p).
  Proof.
    intros hp hpg. split.
    - intros [|μ s]; [done | apply gen_test_cons_not_good].
    - intros μ s. by apply gen_test_next.
    - intros β s _. destruct (gen_test_cons_tau_good Val β s p) as (t & ht & _). by exists t.
    - intros β s t _. apply gen_test_tau_good.
    - intros β s t _ h. by destruct (gen_test_ext_inv p β s β t hp h) as [[_ ?] | [hne _]].
    - intros t β μ s _ h hne. by destruct (gen_test_ext_inv p β s μ t hp h) as [[? _] | [_ ?]].
  Qed.

  #[global] Instance t_conv_test_spec : test_spec (t_conv Val).
  Proof. apply gen_test_spec; [apply isucc_closed | apply isucc_not_good]. Qed.

  #[global] Instance t_conv_convergence_spec : test_convergence_spec (t_conv Val).
  Proof.
    split.
    - apply _.
    - intros μ. apply no_step_refuses. intros q h. inversion h.
    - eexists. apply isucc_tau.
    - intros e. apply isucc_tau_good.
  Qed.

  #[global] Instance ta_co_acceptance_set_spec :
    test_co_acceptance_set_spec Event (ta Val) (λ x, 𝝳ᴇᴠ Val (Φᴀᴘᴀʟ Val x)).
  Proof.
    split.
    - intros E. apply gen_test_spec; [apply sum_ac_closed | apply sum_ac_not_good].
    - intros E. apply no_step_refuses. apply sum_list_no_tau.
    - intros E η nb. destruct nb.
    - intros E β e _ h. apply sum_list_ext_inv in h as [hin _].
      unfold 𝝳ᴇᴠ. by apply elem_of_elements.
    - intros E pβ hin. destruct (sum_list_step (elements E) pβ) as (μ & q & hq & he);
        [by apply elem_of_elements |].
      exists q, μ. split; [exact hq | exact he].
    - intros β e' E _ h. by apply sum_list_ext_inv in h as [_ ?].
  Qed.
End PAL_Alt_TestSpec.
