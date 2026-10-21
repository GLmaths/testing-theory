(* begin hide *)
(*
   Copyright (c) 2024 Gaëtan Lopez <glopez@irif.fr>

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


From stdpp Require Import base countable finite gmap list gmultiset strings.

From TestingTheory Require Import ActTau gLts VACCS.Language.gLts_Instance VACCS_Good Bisimulation
  InputOutputActions Completeness ParallelLTSConstruction InputOutputActions
  Label_Abstraction.LabelAbstraction VACCS.Language.Label_Abstraction.
From TestingTheory Require CompletenessASco TestSpecBridge.
Export VACCS.Language.gLts_Instance VACCS_Good.
Section VACCS_ta_tc.

Context `{VP : VACCS_Parameters}.

Fixpoint gen_test_raw Vs (s : trace (ExtAct TypeOfActions)) p {struct s}:=
  match s with
  | [] => p
  | ActIn (c , v) :: s' => match Vs with
                            | [] => (g 𝟘)     (*whatever*)
                            | ActIn (c , v') :: s'' => (c ? • (If ( bvar 0 ==  NewVar_in_Data 0 v' )
                                   Then (gen_test_raw (NewVar_in_trace 0 s'') s' (NewVar 0 p))
                                   Else ①)) + (𝛕 • ①)
                            | ActOut (c , v') :: s'' => (g 𝟘)
                            end
  | ActOut (c , v) :: s' => match Vs with
                            | [] => (g 𝟘)     (*whatever*)
                            | ActIn (c , v') :: s'' => (g 𝟘)     (*whatever*)
                            | ActOut (c , v') :: s'' => (c ! v' • 𝟘) ‖ (gen_test_raw s'' s' p)
                            end
  end.

Definition gen_test s p := gen_test_raw s s p.

Lemma All_According_to_gen_test s s' d k p :
  subst_in_proc k d (gen_test_raw (NewVar_in_trace k s') s (NewVar k p)) = gen_test_raw s' s p.
Proof.
  revert d k p s'. induction s
    as (s & Hlength) using
         (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
  destruct s; intros; simpl in *.
  - eapply NewVar_subst_cancel.
  - destruct e as [ (*Input*) (c , v) | (*Output*) (c , v)].
    + case_eq (NewVar_in_trace k s').
      * intros. case_eq s'.
        -- intros. subst. simpl. reflexivity.
        -- intros. subst. simpl. case_eq e.
           ++ intros. destruct a. subst. simpl in *. inversion H.
           ++ intros. subst. destruct a. reflexivity.
      * intros. case_eq e.
        -- intros. destruct a. subst. case_eq s'.
           ++ intros. subst. inversion H.
           ++ intros. subst. case_eq e.
              ** intros. destruct a. subst. simpl in H. inversion H. subst.
                 simpl. assert (k = 0+k)%nat as eq1 by eauto with arith.
                 assert (subst_Data (S k) (Succ_bvar d) (NewVar_in_Data 0 (NewVar_in_Data k v1)) 
                        = NewVar_in_Data 0 v1) as eq.
                 { rewrite eq1 at 2. rewrite<- New_Var_And_NewVar_in_Data.
                   simpl in *. eapply subst_NewVar_Data_cancel. }
                 rewrite eq. assert (subst_in_proc (S k) (Succ_bvar d) (gen_test_raw
                            (NewVar_in_trace 0 (NewVar_in_trace k l0)) s
                            (NewVar 0 (NewVar k p))) = gen_test_raw (NewVar_in_trace 0 l0) s (NewVar 0 p)) as eq2.
                 { rewrite eq1 at 3. rewrite<- New_Var_And_NewVar. rewrite eq1 at 2.
                   rewrite<- New_Var_And_NewVar_in_Trace. simpl in *.
                 { eapply Hlength; eauto with arith. } }
                 rewrite eq2. eauto.
              ** intros. subst. simpl in *. destruct a. inversion H.
        -- intros. subst. destruct a. case_eq s'.
           ++ intros. subst. simpl. inversion H.
           ++ intros. case_eq e.
              ** subst. intros. subst. simpl in *. destruct a. inversion H.
              ** intros. subst. destruct a. simpl. reflexivity.
    + case_eq s'.
      * intros. simpl. reflexivity.
      * intros. subst. simpl.
        case_eq (NewVar_in_label k e).
        -- intros. case_eq a. intros. subst. case_eq e.
           ++ intros. subst. destruct a. simpl. reflexivity.
           ++ intros. subst. inversion H. destruct a. inversion H1.
        -- intros. case_eq a. intros. subst. case_eq e.
           ++ intros. destruct a. subst. inversion H.
           ++ intros. subst. inversion H. destruct a. simpl.
              inversion H1. subst. rewrite subst_NewVar_Data_cancel.
              assert (subst_in_proc k d (gen_test_raw (NewVar_in_trace k l) s (NewVar k p))
                  = gen_test_raw l s p) as eq1.
              { eapply Hlength; eauto with arith. }
              rewrite eq1. eauto.
Qed.

Lemma gen_test_lts_mu μ s p :
   (gen_test (μ :: s) p) ⟶⋍[μ] (gen_test s p).
Proof.
  intros. destruct μ as [ (* Input *) (c , v) | (* Output *) (c , v) ].
  - unfold gen_test. simpl in *.
    eexists. split.
    + eapply lts_choiceL. eapply lts_input.
    + simpl. rewrite subst_NewVar_Data_cancel.
      etrans. eapply cgr_if_true.
      * eapply Eval_simpl_true. eauto.
      * rewrite All_According_to_gen_test. reflexivity.
  - simpl in *. exists (𝟘 ‖ gen_test s p). split.
    + unfold gen_test. simpl.
      constructor. constructor.
    + etrans. eapply cgr_par_com. eapply cgr_par_nil.
Qed.

Lemma gen_test_ungood_if p : ¬ good_VACCS p -> forall s, ¬ good_VACCS (gen_test s p).
Proof.
  unfold gen_test.
  intros nhp s nhg.
  induction s as [|μ s']; simpl in *.
  - contradiction.
  - destruct μ; destruct a; subst.
    + inversion nhg; subst. destruct H0; inversion H.
    + inversion nhg; subst. destruct H0. inversion H. contradiction.
Qed.

Lemma gen_test_gen_spec_out_lts_tau_ex s p :
  (exists q, lts p τ q) -> exists e, lts (gen_test s p) τ e.
Proof.
  unfold gen_test.
  intros hq. induction s; [| simpl; destruct a ].
  + eauto with cgr.
  + destruct a. simpl. destruct IHs. eexists; eauto with cgr.
  + destruct a. simpl. destruct IHs. eexists; eauto with cgr.
Qed.

Lemma gen_test_gen_spec_out_lts_tau_ex_inst a s p :
  exists e', lts (gen_test (ActIn a :: s) p) τ e'.
Proof. unfold gen_test. simpl. destruct a. eauto with cgr. Qed.

Lemma gen_test_gen_spec_out_lts_tau_good a s e p :
  lts (gen_test (ActIn a :: s) p) τ e -> good_VACCS e.
Proof.
  unfold gen_test. simpl. destruct a.
  inversion 1; subst; inversion H4; subst; eauto with ccs.
Qed.

Lemma gen_test_gen_spec_out_lts_mu_uniq e a s p :
  lts (gen_test (ActIn a :: s) p) (ActExt $ ActIn a) e -> e ≡ gen_test s p.
Proof.
  unfold gen_test. simpl. destruct a.
  intros. inversion H; subst; inversion H4; subst; eauto.
  simpl. rewrite subst_NewVar_Data_cancel. rewrite All_According_to_gen_test.
  eapply cgr_if_true_step. rewrite Eval_simpl_true; eauto. 
Qed.

Inductive Well_Defined_Trace : trace (ExtAct TypeOfActions) -> Prop :=
| empty_list_is_always_defined : Well_Defined_Trace ε
| cons_is_defined_up_to_data : forall a s, Well_Defined_ExtAction a -> Well_Defined_Trace s
                                                    -> Well_Defined_Trace (a :: s).

Lemma gen_test_gen_spec_good_not_mu e a μ' s p :
  lts (gen_test (ActIn a :: s) p) (ActExt $ μ') e -> μ' ≠ ActIn a -> good_VACCS e.
Proof.
  intros tr neq. unfold gen_test in tr. simpl in *.
  destruct a. inversion tr.
  + subst. inversion H3. subst.
    simpl in *. rewrite subst_NewVar_Data_cancel in *.
    assert (v0 ≠ v) as neq'.
    { intro. subst. contradiction. }
    eapply Eval_simpl_false_gen in neq'.
    assert ((If v0 == v
               Then gen_test_raw (NewVar_in_trace 0 s) s (NewVar 0 p) ^ v0
               Else ①) ≡ ①).
    { eapply cgr_if_false_step; eauto. }
    eapply good_preserved_by_cgr_step; eauto. eapply good_success.
    eapply cgr_if_false_rev_step; eauto.
  + subst. inversion H3.
Qed.

Fixpoint unroll_fw (L : list PreAct) : gproc :=
  match L with
  | [] => 𝟘
  | Inputs c :: l => (c ? • ①) + unroll_fw l
  end.

Definition gen_acc (G : gset PreAct) s := gen_test s (g (unroll_fw (elements G))).

Lemma unroll_a_eq_perm (xs ys : list PreAct) : xs ≡ₚ ys -> (g (unroll_fw xs)) ≡* (g (unroll_fw ys)).
Proof.
  intro hperm. induction hperm; simpl; eauto with *.
  - destruct x; eauto. eapply cgr_fullchoice; eauto with *.
  - destruct y ; destruct x.
    + etrans. symmetry. eapply cgr_choice_assoc. etrans. eapply cgr_fullchoice.
      eapply cgr_choice_com. reflexivity. eapply cgr_choice_assoc.
Qed.

Lemma not_good_P G : ¬ (good_VACCS (gen_acc G ε)).
Proof.
  intros imp.
  unfold gen_acc in imp. unfold gen_test in imp.
  simpl in *. induction G using set_ind_L. 
  + rewrite elements_empty in imp.
    simpl in *. inversion imp.
  + eapply elements_union_singleton in H.
    eapply unroll_a_eq_perm in H. simpl in *. destruct x.
    * eapply good_preserved_by_cgr in H; eauto. inversion H; subst.
      destruct H1.
      - inversion H0.
      - eauto.
Qed.

#[global] Program Instance gen_acc_gen_test_inst G 
    : test_spec (fun s => gen_acc G s).
Next Obligation.
  intros g s hh. eapply gen_test_ungood_if; try eassumption.
  eapply not_good_P; eauto.
Qed.
Next Obligation.
  intros. eapply gen_test_lts_mu.
Qed.
Next Obligation.
  intros. destruct β.
  + eapply gen_test_gen_spec_out_lts_tau_ex_inst.
  + exfalso. eapply H. simpl. unfold non_blocking_output. unfold is_output. exists a; eauto.
Qed.
Next Obligation.
  intros. destruct β.
  + eapply gen_test_gen_spec_out_lts_tau_good. simpl in H. eassumption.
  + exfalso. eapply H. simpl. unfold non_blocking_output. unfold is_output. exists a; eauto.
Qed.
Next Obligation.
  intros. destruct β.
  + unfold eq_rel. simpl. constructor. eapply gen_test_gen_spec_out_lts_mu_uniq. eassumption.
  + exfalso. eapply H. simpl. unfold non_blocking_output. unfold is_output. exists a; eauto.
Qed.
Next Obligation.
  intros G t'. intros. simpl in *.
  destruct β.
  + simpl in *. eapply gen_test_gen_spec_good_not_mu in H0; eauto.
  + exfalso. eapply H. simpl. unfold non_blocking_output. unfold is_output. exists a; eauto.
Qed.

Lemma gen_acc_does_not_not_blocking_actions : forall l p a, ¬ (lts (unroll_fw l) (ActExt $ ActOut a) p).
Proof.
  intros g.
  induction g as [| b g'].
  - cbn. intros p a R. inversion R.
  - cbn. intros p a R. destruct b.
    + inversion R; subst.
      * inversion H3.
      * eapply IHg'. eauto.
Qed.

Lemma gen_acc_does_not_tau : forall g p, ~ lts (unroll_fw g) τ p.
Proof.
  intros g.
  induction g as [| b g'].
  - cbn. intros p R. inversion R.
  - cbn. intros p R. destruct b.
    + inversion R; subst.
      * inversion H3.
      * eapply IHg'. eauto.
Qed.

Lemma gen_acc_gen_spec_acc_nil_mem_lts_inp G c : Inputs c ∈ G 
          -> exists r v, lts (gen_acc G []) (ActExt $ ActIn ((c , v))) r.
Proof.
  remember G. revert g Heqg c.
  induction G using set_ind_L; intros g0 Heqg0 c mem.
  - intros. subst. inversion mem.
  - assert (hn : {[x]} ## X) by set_solver.
    destruct (decide (x = Inputs c)).
    + subst.
      set (h := elements_disj_union {[Inputs c]} X hn).
      cbn. assert (exists p, lts (unroll_fw ((Inputs c) :: elements X)) (ActExt $ ActIn (c , cst O)) p).
      simpl. eauto with cgr.
      destruct H0 as (r & hl).
      edestruct (eq_spec (g (unroll_fw (elements ({[Inputs c]} ∪ X)))) r (ActExt $ ActIn (c , cst O))) 
          as (p & hlt & heqt).
      exists (unroll_fw (Inputs c :: elements X)).
      split. eapply unroll_a_eq_perm.
      replace (elements {[Inputs c]}) with [Inputs c] in h. eauto.
      now rewrite elements_singleton.
      simpl in *. eapply hl. eauto.
    + assert (mem' : Inputs c ∈ X) by set_solver.
      edestruct (IHG X eq_refl c mem') as (r & hlr); eauto.
      destruct x.
      * destruct hlr. unfold gen_acc in H0. unfold gen_test in H0.
        simpl in *.
        edestruct (eq_spec (g (unroll_fw (elements ({[Inputs c0]} ∪ X))))
             r  (ActExt $ ActIn (c , x))) as (p & hlt & heqt).
        exists (g (unroll_fw (Inputs c0 :: elements X))).
        split. eapply unroll_a_eq_perm.
        set (h := elements_disj_union {[Inputs c0]} X hn).
        replace (elements {[Inputs c0]}) with [Inputs c0] in h. eauto.
        now rewrite elements_singleton. simpl in *.
        eapply lts_choiceR. eauto. subst. eauto.
Qed.

#[global] Program Instance gen_acc_gen_spec_acc_inst
  : test_co_acceptance_set_spec gen_acc (fun x => αᴘᴠᴀᴄᴄꜱ (αᴛᴠᴀᴄᴄꜱ x)).
Next Obligation.
  intros g. simpl. unfold proc_stable. intros hne. apply hne.
  apply leibniz_equiv. intros x. split; [intros mem | set_solver].
  eapply lts_set_spec0 in mem.
  now eapply gen_acc_does_not_tau in mem.
Qed.
Next Obligation.
  intros g a. simpl. unfold proc_stable. cbn. intro nb.
  unfold non_blocking_output in nb. destruct nb as (c & eq); subst. intros H. now apply H.
Qed.
Next Obligation.
  intros g.
  induction g using set_ind_L; intros.
  - inversion H0.
  - destruct β.
    * edestruct (eq_spec (g (unroll_fw (x :: elements X))) e (ActExt (ActIn a))) as (p & hlt & heqt).
      ++ exists (gen_acc ({[x]} ∪ X) []).
         split.
         +++ eapply unroll_a_eq_perm.
             assert (hn : {[x]} ## X) by set_solver.
             set (h := elements_disj_union {[x]} X hn).
             replace (elements {[x]}) with [x] in h. symmetry. eauto.
             now rewrite elements_singleton.
         +++ eassumption.
      ++ cbn in hlt. destruct x.
         +++ inversion hlt; subst. 
             ** inversion H6; subst. set_solver.
             ** set_solver.
    * destruct H0. exists a. reflexivity.
Qed.
Next Obligation.
  intros. destruct pβ.
  + eapply gen_acc_gen_spec_acc_nil_mem_lts_inp in H; eauto.
    destruct H as (r & v & Tr). exists r , (ActIn $ (c , v)). split; eauto.
Qed.
Next Obligation.
  intros a e' g. revert a e'.
  induction g using set_ind_L; intros a e' b hl.
  - inversion hl.
  - edestruct (eq_spec (g (unroll_fw (x :: elements X))) e' (ActExt a)) as (p & hlt & heqt).
    ++ exists (gen_acc ({[x]} ∪ X) []).
       split; eauto.
       eapply unroll_a_eq_perm.
       assert (hn : {[x]} ## X) by set_solver.
       set (h := elements_disj_union {[x]} X hn).
       replace (elements {[x]}) with [x] in h
           by now rewrite elements_singleton.
       symmetry. eauto.
    ++ simpl in hlt. destruct x.
       +++ inversion hlt; subst.
           ++++ inversion H4; subst. simpl in *. eapply good_preserved_by_cgr; eauto. constructor.
           ++++ eapply good_preserved_by_cgr. eapply IHg; eauto. eauto.
Qed.

Definition gen_conv s := gen_test s (𝛕 • ①).

#[global] Program Instance gen_conv_gen_test_inst
: test_spec gen_conv.
Next Obligation.
  intros s hh. eapply gen_test_ungood_if; try eassumption.
  intro hh0. inversion hh0.
Qed.
Next Obligation.
  intros. eapply gen_test_lts_mu.
Qed.
Next Obligation.
  intros. destruct β.
  + eapply gen_test_gen_spec_out_lts_tau_ex_inst.
  + exfalso. eapply H. simpl. unfold non_blocking_output. unfold is_output. exists a; eauto.
Qed.
Next Obligation.
  intros. destruct β.
  + eapply gen_test_gen_spec_out_lts_tau_good. simpl in H. eassumption.
  + exfalso. eapply H. simpl. unfold non_blocking_output. unfold is_output. exists a; eauto.
Qed.
Next Obligation.
  intros. destruct β.
  + unfold eq_rel. simpl. constructor. eapply gen_test_gen_spec_out_lts_mu_uniq. eassumption.
  + exfalso. eapply H. simpl. unfold non_blocking_output. unfold is_output. exists a; eauto.
Qed.
Next Obligation.
  intros t'. intros. simpl in *.
  destruct β.
  + eapply gen_test_gen_spec_good_not_mu in H0; eauto.
  + exfalso. eapply H. exists a; eauto.
Qed.

#[global] Program Instance gen_conv_gen_spec_conv_inst 
  : test_convergence_spec gen_conv.
Next Obligation.
  intros [a|a]; simpl; unfold proc_stable; cbn; eauto.
Qed.
Next Obligation. cbn. eauto with cgr. Qed.
Next Obligation. intros e l. cbn in l. inversion l; subst; simpl; eauto with ccs. Qed.

End VACCS_ta_tc.

Section VACCS_ta_𝔸.

Context `{VP : VACCS_Parameters}.

Notation A := (ExtAct TypeOfActions).

Definition pfx_𝔸 (μ : A) : gproc :=
  match μ with
  | ActIn (c , _) => c ? • ①
  | ActOut _ => 𝟘
  end.

Fixpoint unroll_𝔸 (L : list (A / 𝔸ᴠᴀᴄᴄꜱ)) : gproc :=
  match L with
  | [] => 𝟘
  | x :: l => pfx_𝔸 (`x) + unroll_𝔸 l
  end.

Definition gen_acc_𝔸 (E : gset (A / 𝔸ᴠᴀᴄᴄꜱ)) s := gen_test s (g (unroll_𝔸 (elements E))).

Lemma unroll_𝔸_lts L a r :
  lts (g (unroll_𝔸 L)) a r → ∃ x, x ∈ L ∧ lts (g (pfx_𝔸 (`x))) a r.
Proof.
  induction L as [| x L IH]; simpl; intros h; inversion h; subst.
  - exists x. split; [apply list_elem_of_here | assumption].
  - destruct IH as (y & hy & hl); [assumption |].
    exists y. split; [by apply list_elem_of_further | exact hl].
Qed.

Lemma unroll_𝔸_lts_rev x L a r :
  x ∈ L → lts (g (pfx_𝔸 (`x))) a r → lts (g (unroll_𝔸 L)) a r.
Proof.
  induction L as [| y L IH]; intros hx hl; [by apply elem_of_nil in hx |]. simpl.
  apply elem_of_cons in hx as [-> | hx]; [by apply lts_choiceL | apply lts_choiceR; by apply IH].
Qed.

Lemma class_of_repr_𝔸 (x : A / 𝔸ᴠᴀᴄᴄꜱ) : ρ[𝔸ᴠᴀᴄᴄꜱ] (`x) = x.
Proof. exact (@LA_repr_spec _ _ _ (LA_class_surj _) x). Qed.

Lemma pfx_𝔸_lts μ a r :
  lts (g (pfx_𝔸 μ)) a r →
  ∃ c v w, μ = ActIn (c , v) ∧ a = ActExt (ActIn (c , w)) ∧ good_VACCS r.
Proof.
  destruct μ as [[c v]|[c v]]; simpl; intros h; inversion h; subst.
  exists c, v, v0. split; [done |]. split; [done |]. simpl. constructor.
Qed.

Lemma not_good_𝔸 L : ¬ good_VACCS (g (unroll_𝔸 L)).
Proof.
  induction L as [| x L IH]; simpl; intros imp; inversion imp; subst.
  match goal with h : _ ∨ _ |- _ => destruct h as [hg | hg] end.
  - destruct x as [[[c v]|[c v]] hx]; simpl in hg; inversion hg.
  - exact (IH hg).
Qed.

#[global] Program Instance gen_acc_𝔸_test_inst E : test_spec (fun s => gen_acc_𝔸 E s).
Next Obligation.
  intros E s hh. eapply gen_test_ungood_if; try eassumption. apply not_good_𝔸.
Qed.
Next Obligation.
  intros. eapply gen_test_lts_mu.
Qed.
Next Obligation.
  intros. destruct β.
  + eapply gen_test_gen_spec_out_lts_tau_ex_inst.
  + exfalso. eapply H. simpl. unfold non_blocking_output. unfold is_output. exists a; eauto.
Qed.
Next Obligation.
  intros. destruct β.
  + eapply gen_test_gen_spec_out_lts_tau_good. simpl in H. eassumption.
  + exfalso. eapply H. simpl. unfold non_blocking_output. unfold is_output. exists a; eauto.
Qed.
Next Obligation.
  intros. destruct β.
  + unfold eq_rel. simpl. constructor. eapply gen_test_gen_spec_out_lts_mu_uniq. eassumption.
  + exfalso. eapply H. simpl. unfold non_blocking_output. unfold is_output. exists a; eauto.
Qed.
Next Obligation.
  intros E t'. intros. simpl in *.
  destruct β.
  + simpl in *. eapply gen_test_gen_spec_good_not_mu in H0; eauto.
  + exfalso. eapply H. simpl. unfold non_blocking_output. unfold is_output. exists a; eauto.
Qed.

#[global] Instance gen_acc_𝔸_spec :
  CompletenessASco.test_co_acceptance_set_spec gen_acc_𝔸 ρ[𝔸ᴠᴀᴄᴄꜱ].
Proof.
  constructor.
  - intros E. apply TestSpecBridge.test_spec_of_plain, gen_acc_𝔸_test_inst.
  - intros E h. apply lts_performs_spec1 in h as (r & h). cbn in h.
    apply unroll_𝔸_lts in h as (x & _ & h).
    by apply pfx_𝔸_lts in h as (c & v & w & _ & e & _).
  - intros E η nb h. apply lts_performs_spec1 in h as (r & h). cbn in h.
    apply unroll_𝔸_lts in h as (x & _ & h).
    apply pfx_𝔸_lts in h as (c & v & w & _ & e & _).
    injection e as ->. destruct nb as (? & ?). discriminate.
  - intros E β e b h. cbn in h.
    apply unroll_𝔸_lts in h as (x & hx & h).
    apply pfx_𝔸_lts in h as (c & v & w & ex & e' & _). injection e' as ->.
    assert (hc : ρ[𝔸ᴠᴀᴄᴄꜱ] (ActIn (c , w)) = x).
    { rewrite <- (class_of_repr_𝔸 x), ex. by apply class_eq_vaccs. }
    rewrite hc. by apply elem_of_elements.
  - intros E x hx (β0 & b0 & e0).
    destruct (blocking_is_input β0 b0) as ([c v] & ->).
    assert (hk : vaccs_ker (ActIn (c , v)) (`x)).
    { apply class_eq_vaccs_inv. by rewrite class_of_repr_𝔸. }
    remember (`x) as μx eqn:ex. destruct μx as [[c' v']|[c' v']]; simpl in hk; [| contradiction].
    eexists. exists (ActIn (c' , v')). split.
    + cbn. apply (unroll_𝔸_lts_rev x); [by apply elem_of_elements |].
      rewrite <- ex. simpl. constructor.
    + rewrite <- (class_of_repr_𝔸 x). f_equal. exact ex.
  - intros β e' E b h. cbn in h.
    apply unroll_𝔸_lts in h as (x & _ & h).
    by apply pfx_𝔸_lts in h as (? & ? & ? & _ & _ & hg).
Qed.

End VACCS_ta_𝔸.
