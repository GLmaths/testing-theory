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
From stdpp Require Import base gmultiset countable decidable list propset.
From TestingTheory Require Import ActTau pMust_almost_sure.
From TestingTheory Require Import lqCCS.General_definition.Algebra lqCCS.quantum_mem.Syntax lqCCS.quantum_mem.Quantum_Weights.
From TestingTheory Require Import lqCCS.lqCCS_prog.Syntax lqCCS.Helper.De_Brujin_lemmas lqCCS.General_definition.Parallel_choice_LTS lqCCS.quantum_mem.LTS lqCCS.lqCCS_prog.LTS lqCCS.lqCCS_par_Qmem.LTS lqCCS.lqCCS_process.LTS.LTS lqCCS.Helper.Conf_labels lqCCS.Helper.Label_lemmas lqCCS.lqCCS_prog.Congruence lqCCS.Testing.Scheduled lqCCS.Testing.Observer_predicates lqCCS.Helper.Tag_lemmas lqCCS.Testing.DistLTS lqCCS.Testing.Programs lqCCS.Testing.Observers.

#[local] Open Scope lqccs_scope.

Section Rec_Observers.
  Context `{lqP : lqCCS_Parameters}.

Lemma prog_step_out_chan_r P t c v P' :
  obsrb P = true → P ⟶ₚ{c ! v}[{[+ t +]}] P' → c ∈ out_chans P.
Proof.
  intros Hob Hs. remember ({[+ t +]}) as k eqn:Es. remember (c ! v) as 𝜆 eqn:El.
  revert Hob Es El.
  induction Hs as [g k 𝜆 P' Hg| | | | | | | | | ]; intros Hob Es El; simplify_eq; simpl in *.
  - exfalso. remember (c ! v) as 𝜆 eqn:El. revert El.
    induction Hg; intros El; simplify_eq; simpl in Hob.
    + apply andb_prop in Hob as [[Hob _]%andb_prop _]. by apply IHHg.
    + apply andb_prop in Hob as [[_ Hob]%andb_prop _]. by apply IHHg.
  - by apply list_elem_of_singleton.
  - apply andb_prop in Hob as [Hob _]. apply elem_of_app. left. by apply IHHs.
  - apply andb_prop in Hob as [_ Hob]. apply elem_of_app. right. by apply IHHs.
  - apply andb_prop in Hob as [Hob _]. apply elem_of_app. left. by apply IHHs.
  - apply andb_prop in Hob as [_ Hob]. apply elem_of_app. right. by apply IHHs.
Qed.

Lemma prog_step_in_chan_r P t c v P' :
  obsrb P = true → P ⟶ₚ{c ? v}[{[+ t +]}] P' → c ∈ in_chans P.
Proof.
  intros Hob Hs. remember ({[+ t +]}) as k eqn:Es. remember (c ? v) as 𝜆 eqn:El.
  revert Hob Es El.
  induction Hs as [g k 𝜆 P' Hg| | | | | | | | | ]; intros Hob Es El; simplify_eq; simpl in *.
  - remember (c ? v) as 𝜆 eqn:El. revert El.
    induction Hg; intros El; simplify_eq; simpl in *.
    + by left.
    + apply andb_prop in Hob as [[Hob _]%andb_prop _]. apply elem_of_app. left. by apply IHHg.
    + apply andb_prop in Hob as [[_ Hob]%andb_prop _]. apply elem_of_app. right. by apply IHHg.
  - apply andb_prop in Hob as [Hob _]. apply elem_of_app. left. by apply IHHs.
  - apply andb_prop in Hob as [_ Hob]. apply elem_of_app. right. by apply IHHs.
  - apply andb_prop in Hob as [Hob _]. apply elem_of_app. left. by apply IHHs.
  - apply andb_prop in Hob as [_ Hob]. apply elem_of_app. right. by apply IHHs.
Qed.

Lemma prog_step_chans_sub_r P k 𝜆 P' :
  obsrb P = true → P ⟶ₚ{𝜆}[k] P' →
  (∀ c, c ∈ out_chans P' → c ∈ out_chans P) ∧ (∀ c, c ∈ in_chans P' → c ∈ in_chans P).
Proof.
  intros Hob Hs.
  induction Hs as [g k 𝜆 P' Hg| |e P Q k 𝜆 P' He Hp IH|e P Q k 𝜆 Q' He Hp IH
                  |P Q k 𝜆 P' Hp IH|P Q k 𝜆 Q' Hp IH|P Q t t' c v P' Q' Hp IHp Hq IHq
                  |P Q t t' c v P' Q' Hp IHp Hq IHq| |t P]; simpl in Hob; simplify_eq.
  - revert Hob. induction Hg as [| | | | |g1 g2 k 𝜆 P' Hg IH|g1 g2 k 𝜆 P' Hg IH]; intros Hob; simpl.
    + split; intros x; done.
    + rewrite out_chans_subst, in_chans_subst. split; [done|]. intros x Hc. by right.
    + done.
    + rewrite out_chans_subst, in_chans_subst. done.
    + done.
    + apply andb_prop in Hob as [[Hob _]%andb_prop _]. destruct (IH Hob) as [H1 H2].
      split; intros x Hc; apply elem_of_app; left; auto.
    + apply andb_prop in Hob as [[_ Hob]%andb_prop _]. destruct (IH Hob) as [H1 H2].
      split; intros x Hc; apply elem_of_app; right; auto.
  - split; intros x Hc; by apply elem_of_nil in Hc.
  - apply andb_prop in Hob as [Hob _]. destruct (IH Hob) as [H1 H2].
    split; intros x Hc; apply elem_of_app; left; auto.
  - apply andb_prop in Hob as [_ Hob]. destruct (IH Hob) as [H1 H2].
    split; intros x Hc; apply elem_of_app; right; auto.
  - apply andb_prop in Hob as [Hob _]. destruct (IH Hob) as [H1 H2].
    split; intros x Hc; apply elem_of_app in Hc as [Hc|Hc]; apply elem_of_app; auto.
  - apply andb_prop in Hob as [_ Hob]. destruct (IH Hob) as [H1 H2].
    split; intros x Hc; apply elem_of_app in Hc as [Hc|Hc]; apply elem_of_app; auto.
  - apply andb_prop in Hob as [HobP HobQ]. destruct (IHp HobP) as [H1 H2]. destruct (IHq HobQ) as [H3 H4].
    split; intros x Hc; apply elem_of_app in Hc as [Hc|Hc]; apply elem_of_app; auto.
  - apply andb_prop in Hob as [HobP HobQ]. destruct (IHp HobP) as [H1 H2]. destruct (IHq HobQ) as [H3 H4].
    split; intros x Hc; apply elem_of_app in Hc as [Hc|Hc]; apply elem_of_app; auto.
  - split; intros x Hc.
    + apply (out_chans_pr_subst 0) in Hc as [Hc|Hc]; [done| |done]. simpl in Hc. by rewrite out_chans_tren in Hc.
    + apply (in_chans_pr_subst 0) in Hc as [Hc|Hc]; [done| |done]. simpl in Hc. by rewrite in_chans_tren in Hc.
Qed.

Lemma co_succ_complete_r T t μ T' :
  obsrb T = true → T ⟶ₚ{ActExt μ}[{[+ t +]}] T' →
  ∃ a, co_tag a = t ∧ co_act a = ActExt μ ∧ T' ∈ co_succ T a.
Proof.
  intros Hob Hs. remember ({[+ t +]}) as k eqn:Es. remember (ActExt μ) as 𝜆 eqn:El.
  revert t μ Es El Hob.
  induction Hs as [g k 𝜆 P' Hg|t' c e v He|e P Q k 𝜆 P' He Hp IH|e P Q k 𝜆 Q' He Hp IH
                  |P Q k 𝜆 P' Hp IH|P Q k 𝜆 Q' Hp IH|P Q t1 t2|P Q t1 t2|P k 𝜆 P' Hp IH|t' P];
    intros t μ Es El Hob; simplify_eq; simpl in Hob.
  - (* guard *)
    enough (∃ a, co_tag a = t ∧ co_act a = ActExt μ ∧ P' ∈ gco_succ g a) as (a & ? & ? & ?)
      by (exists a; by simpl).
    remember ({[+ t +]}) as k eqn:Es. remember (ActExt μ) as 𝜆 eqn:El. revert t μ Es El Hob.
    induction Hg as [t' P|t' c v P|t' U es qs P Hq|t' M es qs n P Hq|t' es qs P Hq|g1 g2 k 𝜆 P' Hg IH|g1 g2 k 𝜆 P' Hg IH];
      intros t μ Es El Hob; simplify_eq; simpl in Hob.
    + exists (CoIn t c v). simpl. split; [done|]. split; [done|]. rewrite decide_True; [|done].
      by apply list_elem_of_singleton.
    + exists (CoOp t U qs). simpl. split; [done|]. split; [done|]. rewrite decide_True; [|done].
      by apply list_elem_of_singleton.
    + exists (CoMeas t M qs n). simpl. split; [done|]. split; [done|]. rewrite decide_True; [|done].
      by apply list_elem_of_singleton.
    + exists (CoInit t qs). simpl. split; [done|]. split; [done|]. rewrite decide_True; [|done].
      by apply list_elem_of_singleton.
    + apply andb_prop in Hob as [[Hob _]%andb_prop _].
      destruct (IH _ _ eq_refl eq_refl Hob) as (a & ? & ? & Hin). exists a. simpl.
      split; [done|]. split; [done|]. apply elem_of_app. by left.
    + apply andb_prop in Hob as [[_ Hob]%andb_prop _].
      destruct (IH _ _ eq_refl eq_refl Hob) as (a & ? & ? & Hin). exists a. simpl.
      split; [done|]. split; [done|]. apply elem_of_app. by right.
  - exists (CoOut t c v). simpl. split; [done|]. split; [done|]. rewrite decide_True; [|done].
    by apply list_elem_of_singleton.
  - apply andb_prop in Hob as [Hob _]. destruct (IH _ _ eq_refl eq_refl Hob) as (a & ? & ? & Hin).
    exists a. simpl. rewrite He. done.
  - apply andb_prop in Hob as [_ Hob]. destruct (IH _ _ eq_refl eq_refl Hob) as (a & ? & ? & Hin).
    exists a. simpl. rewrite He. done.
  - apply andb_prop in Hob as [Hob _]. destruct (IH _ _ eq_refl eq_refl Hob) as (a & ? & ? & Hin).
    exists a. simpl. split; [done|]. split; [done|]. apply elem_of_app. left.
    apply list_elem_of_fmap. by exists P'.
  - apply andb_prop in Hob as [_ Hob]. destruct (IH _ _ eq_refl eq_refl Hob) as (a & ? & ? & Hin).
    exists a. simpl. split; [done|]. split; [done|]. apply elem_of_app. right.
    apply list_elem_of_fmap. by exists Q'.
Qed.

Lemma gobs_success_stuck_r g k 𝜆 P' : gobsrb g = true → gsuccessb g = true → g ↛ᵍ{𝜆}[k] P'.
Proof.
  intros Hob Hsu Hg. induction Hg; simpl in *; try done;
    apply andb_prop in Hob as [_ Hn]; by rewrite Hsu in Hn.
Qed.

Lemma obs_step_r T k 𝜆 T' : obsr T → T ⟶ₚ{𝜆}[k] T' → obsr T'.
Proof.
  intros [Hob Hdis] Hs. revert Hob Hdis.
  induction Hs as [g k 𝜆 P' Hg|t c e v He|e P Q k 𝜆 P' He Hp IH|e P Q k 𝜆 Q' He Hp IH
                  |P Q k 𝜆 P' Hp IH|P Q k 𝜆 Q' Hp IH|P Q t t' c v P' Q' Hp IHp Hq IHq
                  |P Q t t' c v P' Q' Hp IHp Hq IHq|P k 𝜆 P' Hp IH|t P];
    intros Hob Hdis; simpl in Hob.
  - revert Hob Hdis. induction Hg; intros Hob Hdis; simpl in Hob.
    + done.
    + split; [by rewrite obsrb_subst|]. intros x. rewrite out_chans_subst, in_chans_subst.
      intros Hc Hc'. apply (Hdis x); simpl; [done|by right].
    + split; [done|]. intros x Hc Hc'. by apply (Hdis x).
    + split; [by rewrite obsrb_subst|]. intros x. rewrite out_chans_subst, in_chans_subst.
      intros Hc Hc'. by apply (Hdis x).
    + split; [done|]. intros x Hc Hc'. by apply (Hdis x).
    + apply andb_prop in Hob as [[Hob _]%andb_prop _]. apply IHHg; [done|].
      intros x Hc Hc'. apply (Hdis x); simpl; apply elem_of_app; by left.
    + apply andb_prop in Hob as [[_ Hob]%andb_prop _]. apply IHHg; [done|].
      intros x Hc Hc'. apply (Hdis x); simpl; apply elem_of_app; by right.
  - split; [done|]. intros x Hc. by apply elem_of_nil in Hc.
  - apply andb_prop in Hob as [Hob _]. apply IH; [done|].
    intros x Hc Hc'. apply (Hdis x); simpl; apply elem_of_app; by left.
  - apply andb_prop in Hob as [_ Hob]. apply IH; [done|].
    intros x Hc Hc'. apply (Hdis x); simpl; apply elem_of_app; by right.
  - apply andb_prop in Hob as [HobP HobQ].
    assert (HP' : obsr P').
    { apply IH; [done|]. intros x Hc Hc'. apply (Hdis x); simpl; apply elem_of_app; by left. }
    destruct HP' as [HobP' HdisP].
    split; [simpl; by rewrite HobP', HobQ|].
    intros x Hc Hc'. simpl in Hc, Hc'. apply elem_of_app in Hc as [Hc|Hc]; apply elem_of_app in Hc' as [Hc'|Hc'].
    + by apply (HdisP x).
    + apply (Hdis x); simpl; apply elem_of_app; [left; by apply (proj1 (prog_step_chans_sub_r _ _ _ _ HobP Hp))|by right].
    + apply (Hdis x); simpl; apply elem_of_app; [by right|left; by apply (proj2 (prog_step_chans_sub_r _ _ _ _ HobP Hp))].
    + apply (Hdis x); simpl; apply elem_of_app; by right.
  - apply andb_prop in Hob as [HobP HobQ].
    assert (HQ' : obsr Q').
    { apply IH; [done|]. intros x Hc Hc'. apply (Hdis x); simpl; apply elem_of_app; by right. }
    destruct HQ' as [HobQ' HdisQ].
    split; [simpl; by rewrite HobP, HobQ'|].
    intros x Hc Hc'. simpl in Hc, Hc'. apply elem_of_app in Hc as [Hc|Hc]; apply elem_of_app in Hc' as [Hc'|Hc'].
    + apply (Hdis x); simpl; apply elem_of_app; by left.
    + apply (Hdis x); simpl; apply elem_of_app; [by left|right; by apply (proj2 (prog_step_chans_sub_r _ _ _ _ HobQ Hp))].
    + apply (Hdis x); simpl; apply elem_of_app; [right; by apply (proj1 (prog_step_chans_sub_r _ _ _ _ HobQ Hp))|by left].
    + by apply (HdisQ x).
  - exfalso. apply andb_prop in Hob as [HobP HobQ]. apply (Hdis c); simpl; apply elem_of_app; [left|right].
    + by eapply prog_step_out_chan_r.
    + by eapply prog_step_in_chan_r.
  - exfalso. apply andb_prop in Hob as [HobP HobQ]. apply (Hdis c); simpl; apply elem_of_app; [right|left].
    + by eapply prog_step_out_chan_r.
    + by eapply prog_step_in_chan_r.
  - done.
  - split.
    + apply obsrb_pr_subst; [done|]. simpl. by rewrite obsrb_tren.
    + intros x Hc Hc'.
      apply (out_chans_pr_subst 0) in Hc as [Hc|Hc]; [| |done]; apply (in_chans_pr_subst 0) in Hc' as [Hc'|Hc']; try done;
        simpl in Hc, Hc'; rewrite ?out_chans_tren in Hc; rewrite ?in_chans_tren in Hc'; exact (Hdis x Hc Hc').
Qed.

Lemma obs_tau_r T k T' : obsr T → T ⟶ₚ{τ}[k] T' → ∃ t, k = {[+ t +]} ∧ T' ∈ co_succ T (CoUnfold t).
Proof.
  intros [Hob Hdis] Hs. remember τ as 𝜆 eqn:El. revert Hob Hdis El.
  induction Hs as [g k 𝜆 P' Hg|t c e v He|e P Q k 𝜆 P' He Hp IH|e P Q k 𝜆 Q' He Hp IH
                  |P Q k 𝜆 P' Hp IH|P Q k 𝜆 Q' Hp IH|P Q t t' c v P' Q' Hp IHp Hq IHq
                  |P Q t t' c v P' Q' Hp IHp Hq IHq|P k 𝜆 P' Hp IH|t P];
    intros Hob Hdis El; simplify_eq; simpl in Hob.
  - exfalso. clear Hdis. remember τ as 𝜆0 eqn:El. revert Hob El.
    induction Hg; intros Hob El; simplify_eq; simpl in Hob; try done.
    + apply andb_prop in Hob as [[Hob _]%andb_prop _]. by apply (IHHg Hob).
    + apply andb_prop in Hob as [[_ Hob]%andb_prop _]. by apply (IHHg Hob).
  - apply andb_prop in Hob as [Hob _].
    destruct (IH Hob ltac:(intros x Hc Hc'; apply (Hdis x); simpl; apply elem_of_app; by left) eq_refl) as (t & -> & Hin).
    exists t. split; [done|]. simpl. by rewrite He.
  - apply andb_prop in Hob as [_ Hob].
    destruct (IH Hob ltac:(intros x Hc Hc'; apply (Hdis x); simpl; apply elem_of_app; by right) eq_refl) as (t & -> & Hin).
    exists t. split; [done|]. simpl. by rewrite He.
  - apply andb_prop in Hob as [Hob _].
    destruct (IH Hob ltac:(intros x Hc Hc'; apply (Hdis x); simpl; apply elem_of_app; by left) eq_refl) as (t & -> & Hin).
    exists t. split; [done|]. simpl. apply elem_of_app. left. apply list_elem_of_fmap. by exists P'.
  - apply andb_prop in Hob as [_ Hob].
    destruct (IH Hob ltac:(intros x Hc Hc'; apply (Hdis x); simpl; apply elem_of_app; by right) eq_refl) as (t & -> & Hin).
    exists t. split; [done|]. simpl. apply elem_of_app. right. apply list_elem_of_fmap. by exists Q'.
  - exfalso. apply andb_prop in Hob as [HobP HobQ]. apply (Hdis c); simpl; apply elem_of_app; [left|right].
    + by eapply prog_step_out_chan_r.
    + by eapply prog_step_in_chan_r.
  - exfalso. apply andb_prop in Hob as [HobP HobQ]. apply (Hdis c); simpl; apply elem_of_app; [right|left].
    + by eapply prog_step_out_chan_r.
    + by eapply prog_step_in_chan_r.
  - exists t. split; [done|]. simpl. rewrite decide_True; [by left|done].
Qed.

Lemma obs_success_step_r T k 𝜆 T' : obsrb T = true → T ⟶ₚ{𝜆}[k] T' → success T → success T'.
Proof.
  unfold success. intros Hob Hs. revert Hob.
  induction Hs as [g k 𝜆 P' Hg|t c e v He|e P Q k 𝜆 P' He Hp IH|e P Q k 𝜆 Q' He Hp IH
                  |P Q k 𝜆 P' Hp IH|P Q k 𝜆 Q' Hp IH|P Q t t' c v P' Q' Hp IHp Hq IHq
                  |P Q t t' c v P' Q' Hp IHp Hq IHq|P k 𝜆 P' Hp IH|t P];
    intros Hob Hsu; simpl in *; try done.
  - exfalso. by eapply gobs_success_stuck_r.
  - apply andb_prop in Hob as [Hob _]. rewrite He in Hsu. by apply IH.
  - apply andb_prop in Hob as [_ Hob]. rewrite He in Hsu. by apply IH.
  - apply andb_prop in Hob as [Hob _]. apply orb_prop in Hsu as [Hsu|Hsu].
    + by rewrite (IH Hob Hsu).
    + rewrite Hsu. apply orb_true_r.
  - apply andb_prop in Hob as [_ Hob]. apply orb_prop in Hsu as [Hsu|Hsu].
    + by rewrite Hsu.
    + rewrite (IH Hob Hsu). apply orb_true_r.
  - apply andb_prop in Hob as [HobP HobQ]. apply orb_prop in Hsu as [Hsu|Hsu].
    + by rewrite (IHp HobP Hsu).
    + rewrite (IHq HobQ Hsu). apply orb_true_r.
  - apply andb_prop in Hob as [HobP HobQ]. apply orb_prop in Hsu as [Hsu|Hsu].
    + by rewrite (IHp HobP Hsu).
    + rewrite (IHq HobQ Hsu). apply orb_true_r.
Qed.

Lemma tnodes_obsr T : obsr T → ∀ z T', T' ∈ tnodes T z → obsr T'.
Proof.
  intros HT z. induction z as [|a z IH] using rev_ind; intros T' Hin.
  - rewrite tnodes_nil in Hin. apply list_elem_of_singleton in Hin. by subst.
  - apply tnodes_app_elem in Hin as (T0 & HT0 & Hin).
    exact (obs_step_r _ _ _ _ (IH T0 HT0) (co_succ_step _ _ _ Hin)).
Qed.

Definition wobserver (T : prog) : Prop :=
  (∀ z T', T' ∈ tnodes T z → obsr T')
  ∧ (∀ z, length (tnodes T z) ≤ 1)
  ∧ (∀ z z' t c v c' v' T', T' ∈ tnodes T (z ++ [CoOut t c v] ++ z') → co_succ T' (CoOut t c' v') = []).

Lemma observer_w T : observer T → wobserver T.
Proof.
  intros HT. split; [|split].
  - intros z T' HT'. apply obsr_obs. exact (tnodes_obs T (proj1 HT) z T' HT').
  - exact (observer_le1 T HT).
  - exact (proj2 (proj2 (proj2 HT))).
Qed.

Definition observer_r (T : prog) : Prop :=
  obsr T
  ∧ (∀ t x y, (t, x) ∈ tagged (tren tag_base T) → (t, y) ∈ tagged (tren tag_base T) → x = y)
  ∧ (∀ z, length (tnodes T z) ≤ 1)
  ∧ (∀ z z' t c v c' v' T', T' ∈ tnodes T (z ++ [CoOut t c v] ++ z') → co_succ T' (CoOut t c' v') = []).

Lemma observer_r_w T : observer_r T → wobserver T.
Proof.
  intros (HT & _ & Hl & Ho). split; [|split]; [|done|done]. exact (tnodes_obsr T HT).
Qed.

Lemma tnodes_unique_w T z T1 T2 :
  wobserver T → T1 ∈ tnodes T z → T2 ∈ tnodes T z → T1 = T2.
Proof.
  intros HT H1 H2. pose proof (proj1 (proj2 HT) z) as Hl.
  destruct (tnodes T z) as [|T0 [|]]; simpl in Hl; try lia.
  - by apply elem_of_nil in H1.
  - apply list_elem_of_singleton in H1, H2. congruence.
Qed.

Lemma succ_at_tnodes_w T z T' :
  wobserver T → T' ∈ tnodes T z → succ_at T z = true ↔ success T'.
Proof.
  intros HT Hin. unfold succ_at. rewrite existsb_exists. split.
  - intros (T0 & HT0%list_elem_of_In & Hs). by rewrite (tnodes_unique_w T z T' T0).
  - intros Hs. exists T'. split; [by apply list_elem_of_In|done].
Qed.

Lemma succ_at_persists_w T z z' :
  wobserver T → succ_at T z = true → tnodes T (z ++ z') ≠ [] → succ_at T (z ++ z') = true.
Proof.
  intros HT. induction z' as [|a z' IH] using rev_ind; intros Hs Hne.
  - by rewrite app_nil_r in *.
  - rewrite app_assoc in *. destruct (tnodes T ((z ++ z') ++ [a])) as [|T'' l] eqn:E; [by exfalso; apply Hne|].
    assert (Hin : T'' ∈ tnodes T ((z ++ z') ++ [a])) by (rewrite E; by left).
    apply tnodes_app_elem in Hin as (T' & HT' & Hin').
    apply (succ_at_tnodes_w T _ T'' HT); [rewrite E; by left|].
    assert (Hob : obsrb T' = true) by exact (proj1 (proj1 HT (z ++ z') T' HT')).
    assert (Hs' : success T').
    { apply (succ_at_tnodes_w T _ T' HT HT'). apply IH; [done|]. intros E'. rewrite E' in HT'. by apply elem_of_nil in HT'. }
    exact (obs_success_step_r _ _ _ _ Hob (co_succ_step _ _ _ Hin') Hs').
Qed.

Lemma S_T_tnodes_w T z T' : wobserver T → T' ∈ tnodes T z → S_T T z = true ↔ success T'.
Proof.
  intros HT Hin. split.
  - intros (i & Hi & Hs)%S_T_spec.
    rewrite <- (succ_at_tnodes_w T z T' HT Hin), <- (take_drop i z).
    apply succ_at_persists_w; [done|done|]. rewrite take_drop. intros E. rewrite E in Hin. by apply elem_of_nil in Hin.
  - intros Hs. apply S_T_spec. exists (length z). split; [done|].
    rewrite take_ge; [|done]. by apply (succ_at_tnodes_w T z T').
Qed.

Definition rtagged (T : prog) (t : tag) (x : okind) : Prop := (tag_base t, x) ∈ tagged (tren tag_base T).

Lemma tnodes_rtagged T z T' t x : T' ∈ tnodes T z → (t, x) ∈ tagged T' → rtagged T t x.
Proof.
  revert T' t x. induction z as [|a z IH] using rev_ind; intros T' t x Hin Hk.
  - rewrite tnodes_nil in Hin. apply list_elem_of_singleton in Hin. subst T'. unfold rtagged.
    rewrite tagged_tren. apply list_elem_of_fmap. by exists (t, x).
  - apply tnodes_app_elem in Hin as (T0 & HT0 & Hin). unfold rtagged.
    assert (Hk' : (tag_base t, x) ∈ tagged (tren tag_base T')).
    { rewrite tagged_tren. apply list_elem_of_fmap. by exists (t, x). }
    assert (Hstep : ∃ k 𝜆, T0 ⟶ₚ{𝜆}[k] T') by (pose proof (co_succ_step _ _ _ Hin); eauto).
    destruct Hstep as (k & 𝜆 & Hp).
    pose proof (prog_step_tagged _ _ _ _ _ Hp Hk') as Hk0. rewrite tagged_tren in Hk0.
    apply list_elem_of_fmap in Hk0 as ([t0 x0] & E & Hk0). simpl in E. injection E as E1 E2. subst x0.
    pose proof (IH T0 t0 x HT0 Hk0) as H0. unfold rtagged in H0. by rewrite E1.
Qed.
Lemma eff_out_keep_w T z C t c v Tn T' :
  wobserver T → Tn ∈ tnodes T z → T' ∈ tnodes T (eff z C) → co_succ Tn (CoOut t c v) ≠ [] →
  t ∉ (λ m : msg, m.1.1) <$> C → co_succ T' (CoOut t c v) ≠ [].
Proof.
  intros HT HTn. unfold eff. revert T'. induction C as [|m C IH] using rev_ind; intros T' HT' Hne Hk.
  - simpl in HT'. rewrite app_nil_r in HT'. by rewrite (tnodes_unique_w T z T' Tn HT HT' HTn).
  - rewrite fmap_app, app_assoc in HT'. simpl in HT'.
    apply tnodes_app_elem in HT' as (T0 & HT0 & H0).
    rewrite fmap_app in Hk. apply not_elem_of_app in Hk as [HkC Hkm].
    apply (co_succ_out_keep T0 _ _ _ _ _ H0).
    + apply IH; [done|done|done].
    + intros c' v' E. injection E as E _ _. apply Hkm. rewrite E. simpl. by left.
Qed.

End Rec_Observers.

(* end hide *)
