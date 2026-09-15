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
  PAL_Syntax PAL_Template_LTS PAL_Template_Congruence PAL_Good PAL_Template_AbsAction PAL_Template_Tests.

(* * The tests of the alternative LTS of PAL satisfy the specifications of [Completeness]

   With [⋍ = cgr]:
   - [gen_test_spec]: for [gen s = gen_test s p] with [p] closed and not
     good, the axioms (1)-(6) of [test_spec];
   - [t_conv_convergence_spec]: [test_convergence_spec] for [t_conv];
   - [ta_co_acceptance_set_spec]: [test_co_acceptance_set_spec] for [ta],
     with [Γ = 𝝳ᴘᴀʟ ∘ Φᴘᴀʟ] (the identity). *)

Section PAL_T_TestSpec.
  Context (Val : Type) `{Countable Val}.

  Notation term := (term Val).
  Notation eot := (eot Val).
  Notation PALT_Act := (PALT_Act Val).
  Notation good := (good_PAL Val).
  Notation gen_test := (gen_test Val).
  Notation isucc := (isucc Val).
  Notation ac_t := (ac_t Val).

  (** Infer the action type of [⟶], [⟶[μ]], ... from the LTS on terms. *)
  #[local] Hint Mode ExtAction ! : typeclass_instances.

  (** ** Closed terms *)

  Definition closed (E : term) := ∀ σ : vsubst Val, subst_term σ E = E.

  Lemma subst_eot_to_tuple σ (ot : eot) : subst_tuple σ (eot_to_tuple ot) = eot_to_tuple ot.
  Proof.
    induction ot as [|[|v] ot IH]; [done | ..];
      unfold subst_tuple, eot_to_tuple in *; simpl; by rewrite IH.
  Qed.

  Lemma gen_test_closed s p : closed p → closed (gen_test s p).
  Proof.
    intros hp. induction s as [|[ot|ot] s IH]; intros σ; simpl; [apply hp | |];
      by rewrite subst_eot_to_tuple, IH.
  Qed.

  Lemma isucc_closed : closed isucc.
  Proof. by intros σ. Qed.

  Lemma ac_t_closed β : closed (ac_t β).
  Proof. intros σ. destruct β; simpl; by rewrite subst_eot_to_tuple. Qed.

  Lemma sum_ac_closed E : closed (sum_ac Val E).
  Proof.
    intros σ. unfold sum_ac. induction (elements E) as [|e l IH]; simpl; [done |].
    rewrite IH. f_equal. apply ac_t_closed.
  Qed.

  (** ** Steps of the tests *)

  Lemma par_nil_l_cgr (E : term) : t_par t_nil E ⋍ E.
  Proof. etransitivity; [apply cgr_once, cgr_par_com | apply cgr_once, cgr_par_nil]. Qed.

  Lemma gen_test_ext_inv p β s μ t :
    closed p → gen_test (β :: s) p ⟶[μ] t → μ = β ∧ t ⋍ gen_test s p.
  Proof.
    intros hp. destruct β as [ot|ot]; simpl; intros h; inversion h; subst.
    - match goal with h' : lts_step_t _ (t_in _ _) _ _ |- _ => inversion h'; subst end.
      match goal with hev : eval_in_tuple _ = Some _ |- _ =>
        rewrite eval_in_eot_to_tuple_t in hev; injection hev as <- end.
      match goal with hm : tuple_match _ _ |- _ => apply tuple_match_eot_to_eit_t in hm as -> end.
      split; [done |]. by rewrite (gen_test_closed s p hp).
    - match goal with h' : lts_step_t _ isucc _ _ |- _ => inversion h' end.
    - match goal with h' : lts_step_t _ (t_lmerge _ _) _ _ |- _ => inversion h'; subst end.
      match goal with h' : lts_step_t _ (t_out _ _) _ _ |- _ => inversion h'; subst end.
      match goal with hev : eval_out_tuple _ = Some _ |- _ =>
        rewrite eval_out_eot_to_tuple_t in hev; injection hev as <- end.
      split; [done | apply par_nil_l_cgr].
    - match goal with h' : lts_step_t _ isucc _ _ |- _ => inversion h' end.
  Qed.

  Lemma gen_test_next p μ s : closed p → gen_test (μ :: s) p ⟶⋍[μ] gen_test s p.
  Proof.
    intros hp. destruct μ as [ot|ot].
    - exists (subst_term (build_subst (eot_to_eit Val ot) ot) (gen_test s p)). split.
      + simpl. apply tar4_l, tar1; [apply eval_in_eot_to_tuple_t | by apply tuple_match_eot_to_eit_t].
      + by rewrite (gen_test_closed s p hp).
    - exists (t_par t_nil (gen_test s p)). split.
      + simpl. apply tar4_l, tar6, tar3, eval_out_eot_to_tuple_t.
      + apply par_nil_l_cgr.
  Qed.

  Lemma gen_test_tau_good p β s t : gen_test (β :: s) p ⟶ t → good t.
  Proof.
    intros h. destruct β as [ot|ot]; simpl in h; inversion h; subst.
    - match goal with h' : lts_step_t _ (t_in _ _) τ _ |- _ => inversion h' end.
    - apply good_echoice_r. by eapply isucc_tau_good.
    - match goal with h' : lts_step_t _ (t_lmerge _ _) τ _ |- _ => inversion h'; subst end.
      match goal with h' : lts_step_t _ (t_out _ _) τ _ |- _ => inversion h'; subst end. congruence.
    - apply good_echoice_r. by eapply isucc_tau_good.
  Qed.

  Lemma ac_t_ext_inv β μ q : ac_t β ⟶[μ] q → μ = β ∧ good q.
  Proof.
    destruct β as [ot|ot]; simpl; intros h; inversion h; subst.
    - match goal with hev : eval_in_tuple _ = Some _ |- _ =>
        rewrite eval_in_eot_to_tuple_t in hev; injection hev as <- end.
      match goal with hm : tuple_match _ _ |- _ => apply tuple_match_eot_to_eit_t in hm as -> end.
      split; [done | apply good_success].
    - match goal with h' : lts_step_t _ (t_out _ _) _ _ |- _ => inversion h'; subst end.
      match goal with hev : eval_out_tuple _ = Some _ |- _ =>
        rewrite eval_out_eot_to_tuple_t in hev; injection hev as <- end.
      split; [done | apply good_par_r, good_success].
  Qed.

  Lemma ac_t_no_tau β q : ¬ ac_t β ⟶ q.
  Proof.
    destruct β as [ot|ot]; simpl; intros h; inversion h; subst.
    match goal with h' : lts_step_t _ (t_out _ _) τ _ |- _ => inversion h'; subst end. congruence.
  Qed.

  Lemma ac_t_step β : ∃ q, ac_t β ⟶[β] q.
  Proof.
    destruct β as [ot|ot]; simpl; eexists.
      apply tar1; [apply eval_in_eot_to_tuple_t | by apply tuple_match_eot_to_eit_t].
    - apply tar6, tar3, eval_out_eot_to_tuple_t.
  Qed.

  Notation sum_list l := (foldr (λ β acc, t_echoice (ac_t β) acc) t_nil l).

  Lemma sum_list_ext_inv l μ q : sum_list l ⟶[μ] q → μ ∈ l ∧ good q.
  Proof.
    revert q. induction l as [|β l IH]; simpl; intros q h; inversion h; subst.
    - match goal with h' : lts_step_t _ (ac_t _) _ _ |- _ => apply ac_t_ext_inv in h' as [-> hg] end.
      split; [apply elem_of_cons; by left | done].
    - match goal with h' : lts_step_t _ (foldr _ _ _) _ _ |- _ => apply IH in h' as [hin hg] end.
      split; [apply elem_of_cons; by right | done].
  Qed.

  Lemma sum_list_no_tau l q : ¬ sum_list l ⟶ q.
  Proof.
    revert q. induction l as [|β l IH]; simpl; intros q h; inversion h; subst;
      [eapply ac_t_no_tau; eassumption | eapply IH; eassumption].
  Qed.

  Lemma sum_list_step l β : β ∈ l → ∃ q, sum_list l ⟶[β] q.
  Proof.
    induction l as [|β' l IH]; intros hin; [by apply elem_of_nil in hin |].
    apply elem_of_cons in hin as [<- | hin].
    - destruct (ac_t_step β) as [q hq]. exists q. simpl. by apply tar4_l.
    - destruct (IH hin) as [q hq]. exists q. simpl. by apply tar4_r.
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
    - intros β s t _ h. by apply gen_test_ext_inv in h as [_ ?].
    - intros t β μ s _ h hne. by apply gen_test_ext_inv in h as [-> _].
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
    test_co_acceptance_set_spec PALT_Act (ta Val) (λ β, 𝝳ᴘᴀʟ Val (Φᴘᴀʟ Val β)).
  Proof.
    split.
    - intros E. apply gen_test_spec; [apply sum_ac_closed | apply sum_ac_not_good].
    - intros E. apply no_step_refuses. apply sum_list_no_tau.
    - intros E η nb. destruct nb.
    - intros E β e _ h. apply sum_list_ext_inv in h as [hin _].
      cbv [𝝳ᴘᴀʟ Φᴘᴀʟ]. by apply elem_of_elements.
    - intros E pβ hin. destruct (sum_list_step (elements E) pβ) as [q hq]; [by apply elem_of_elements |].
      exists q, pβ. split; [exact hq | done].
    - intros β e' E _ h. by apply sum_list_ext_inv in h as [_ ?].
  Qed.
End PAL_T_TestSpec.
