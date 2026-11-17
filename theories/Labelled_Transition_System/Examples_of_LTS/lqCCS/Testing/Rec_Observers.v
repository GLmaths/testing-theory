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
From stdpp Require Import base countable decidable list propset.
From TestingTheory Require Import ActTau pMust_almost_sure.
From TestingTheory Require Import lqCCS.Language.Algebra lqCCS.Language.Quantum lqCCS.Language.Quantum_Weights.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.LTS lqCCS.Language.Congruence lqCCS.Testing.Scheduled lqCCS.Testing.DistLTS lqCCS.Testing.Programs lqCCS.Testing.Observers.

#[local] Open Scope lqccs_scope.

Section LqP.
  Context `{LP : lqCCS_Parameters}.

Fixpoint obsrb (T : proc) : bool :=
  match T with
  | PSend _ _ _ | PVar _ => true
  | PIte _ P Q | P ∥ Q => obsrb P && obsrb Q
  | ν _ => false
  | PRec _ _ P => obsrb P
  | PG g => gobsrb g
  end
with gobsrb (g : guard) : bool :=
  match g with
  | GNil _ | ① => true
  | PTau _ ∙ _ => false
  | _ ∙ P => obsrb P
  | (g1 + g2)%lq => gobsrb g1 && gobsrb g2 && negb (gsuccessb g1 || gsuccessb g2)
  end.

Definition obsr (T : proc) : Prop := obsrb T = true ∧ chan_disjoint T.

Lemma obsrb_obsb T : obsb T = true → obsrb T = true
with gobsrb_gobsb g : gobsb g = true → gobsrb g = true.
Proof.
  - destruct T; simpl; intros H; try done.
    + apply andb_prop in H as [H1 H2]. by rewrite (obsrb_obsb _ H1), (obsrb_obsb _ H2).
    + apply andb_prop in H as [H1 H2]. by rewrite (obsrb_obsb _ H1), (obsrb_obsb _ H2).
    + by apply gobsrb_gobsb.
  - destruct g; simpl; intros H; try done.
    + destruct 𝜆; try done; by apply obsrb_obsb.
    + apply andb_prop in H as [[H1 H2]%andb_prop H3]. by rewrite (gobsrb_gobsb _ H1), (gobsrb_gobsb _ H2), H3.
Qed.

Lemma obsr_obs T : obs T → obsr T.
Proof. intros [H1 H2]. split; [by apply obsrb_obsb|done]. Qed.

Lemma obsrb_subst k v P : obsrb (subst k v P) = obsrb P
with gobsrb_gsubst k v g : gobsrb (gsubst k v g) = gobsrb g.
Proof.
  - destruct P; simpl; try done; try (by rewrite !obsrb_subst); try apply gobsrb_gsubst.
  - destruct g; simpl; try done; try (by rewrite !gobsrb_gsubst, !gsuccessb_gsubst);
      try (destruct 𝜆; simpl; try done; apply obsrb_subst).
Qed.

Lemma obsrb_shiftv k P : obsrb (shiftv k P) = obsrb P
with gobsrb_gshiftv k g : gobsrb (gshiftv k g) = gobsrb g.
Proof.
  - destruct P; simpl; try done; try (by rewrite !obsrb_shiftv); try apply gobsrb_gshiftv.
  - destruct g; simpl; try done; try (by rewrite !gobsrb_gshiftv, !gsuccessb_gshiftv);
      try (destruct 𝜆; simpl; try done; apply obsrb_shiftv).
Qed.

Lemma obsrb_shiftv_iter n P : obsrb (Nat.iter n (shiftv 0) P) = obsrb P.
Proof. induction n as [|n IH]; simpl; [done|]. by rewrite obsrb_shiftv. Qed.

Lemma out_chans_shiftv_iter n P : out_chans (Nat.iter n (shiftv 0) P) = out_chans P.
Proof. induction n as [|n IH]; simpl; [done|]. by rewrite out_chans_shiftv. Qed.

Lemma in_chans_shiftv_iter n P : in_chans (Nat.iter n (shiftv 0) P) = in_chans P.
Proof. induction n as [|n IH]; simpl; [done|]. by rewrite in_chans_shiftv. Qed.

Lemma gsuccessb_gtren f g : gsuccessb (gtren f g) = gsuccessb g.
Proof. induction g as [es| |𝜆 P|g1 IH1 g2 IH2]; simpl; try done. by rewrite IH1, IH2. Qed.

Lemma obsrb_tren f P : obsrb (tren f P) = obsrb P
with gobsrb_gtren f g : gobsrb (gtren f g) = gobsrb g.
Proof.
  - destruct P; simpl; try done; try (by rewrite !obsrb_tren); try apply gobsrb_gtren.
  - destruct g; simpl; try done; try (by rewrite !gobsrb_gtren, !gsuccessb_gtren);
      try (destruct 𝜆; simpl; try done; apply obsrb_tren).
Qed.

Lemma out_chans_tren f P : out_chans (tren f P) = out_chans P
with gout_chans_gtren f g : gout_chans (gtren f g) = gout_chans g.
Proof.
  - destruct P; simpl; try done; try (by rewrite !out_chans_tren); try apply out_chans_tren;
      try apply gout_chans_gtren.
  - destruct g; simpl; try done; try (by rewrite !gout_chans_gtren);
      try (destruct 𝜆; simpl; apply out_chans_tren).
Qed.

Lemma in_chans_tren f P : in_chans (tren f P) = in_chans P
with gin_chans_gtren f g : gin_chans (gtren f g) = gin_chans g.
Proof.
  - destruct P; simpl; try done; try (by rewrite !in_chans_tren); try apply in_chans_tren;
      try apply gin_chans_gtren.
  - destruct g; simpl; try done; try (by rewrite !gin_chans_gtren);
      try (destruct 𝜆; simpl; try apply in_chans_tren; by rewrite in_chans_tren).
Qed.

Lemma gsuccessb_gpr_subst X g Q : gsuccessb (gpr_subst X g Q) = gsuccessb g.
Proof. induction g as [es| |𝜆 P|g1 IH1 g2 IH2]; simpl; try done. by rewrite IH1, IH2. Qed.

Lemma obsrb_pr_subst X P Q : obsrb P = true → obsrb Q = true → obsrb (P ⦃ Q // X ⦄) = true
with gobsrb_gpr_subst X g Q : gobsrb g = true → obsrb Q = true → gobsrb (gpr_subst X g Q) = true.
Proof.
  - destruct P; simpl; intros HP HQ; try done.
    + apply andb_prop in HP as [H1 H2]. by rewrite (obsrb_pr_subst _ _ _ H1 HQ), (obsrb_pr_subst _ _ _ H2 HQ).
    + apply andb_prop in HP as [H1 H2]. by rewrite (obsrb_pr_subst _ _ _ H1 HQ), (obsrb_pr_subst _ _ _ H2 HQ).
    + by case_decide.
    + case_decide; simpl; [done|]. by apply obsrb_pr_subst.
    + by apply gobsrb_gpr_subst.
  - destruct g; simpl; intros Hg HQ; try done.
    + destruct 𝜆; try done; apply obsrb_pr_subst; try done; by rewrite obsrb_shiftv_iter.
    + apply andb_prop in Hg as [[H1 H2]%andb_prop H3].
      by rewrite (gobsrb_gpr_subst _ _ _ H1 HQ), (gobsrb_gpr_subst _ _ _ H2 HQ), !gsuccessb_gpr_subst, H3.
Qed.

Lemma out_chans_pr_subst X P Q c :
  obsrb P = true → c ∈ out_chans (P ⦃ Q // X ⦄) → c ∈ out_chans P ∨ c ∈ out_chans Q
with gout_chans_gpr_subst X g Q c :
  gobsrb g = true → c ∈ gout_chans (gpr_subst X g Q) → c ∈ gout_chans g ∨ c ∈ out_chans Q.
Proof.
  - destruct P; simpl; intros HP Hc; try done.
    + by left.
    + apply andb_prop in HP as [H1 H2].
      apply elem_of_app in Hc as [Hc|Hc]; [apply (out_chans_pr_subst X) in Hc as [Hc|Hc]; [| |done]|
        apply (out_chans_pr_subst X) in Hc as [Hc|Hc]; [| |done]]; auto; left; apply elem_of_app; auto.
    + apply andb_prop in HP as [H1 H2].
      apply elem_of_app in Hc as [Hc|Hc]; [apply (out_chans_pr_subst X) in Hc as [Hc|Hc]; [| |done]|
        apply (out_chans_pr_subst X) in Hc as [Hc|Hc]; [| |done]]; auto; left; apply elem_of_app; auto.
    + case_decide; [by right|by left].
    + case_decide; simpl in Hc; [by left|]. by apply (out_chans_pr_subst X).
    + by apply (gout_chans_gpr_subst X).
  - destruct g as [es| |𝜆 P|g1 g2]; simpl; intros Hg Hc.
    + by apply elem_of_nil in Hc.
    + by apply elem_of_nil in Hc.
    + destruct 𝜆; try done; apply (out_chans_pr_subst X) in Hc as [Hc|Hc]; try done; auto;
        rewrite out_chans_shiftv_iter in Hc; auto.
    + apply andb_prop in Hg as [[H1 H2]%andb_prop _].
      apply elem_of_app in Hc as [Hc|Hc]; [apply (gout_chans_gpr_subst X) in Hc as [Hc|Hc]; [| |done]|
        apply (gout_chans_gpr_subst X) in Hc as [Hc|Hc]; [| |done]]; auto; left; apply elem_of_app; auto.
Qed.

Lemma in_chans_pr_subst X P Q c :
  obsrb P = true → c ∈ in_chans (P ⦃ Q // X ⦄) → c ∈ in_chans P ∨ c ∈ in_chans Q
with gin_chans_gpr_subst X g Q c :
  gobsrb g = true → c ∈ gin_chans (gpr_subst X g Q) → c ∈ gin_chans g ∨ c ∈ in_chans Q.
Proof.
  - destruct P; simpl; intros HP Hc; try (by apply elem_of_nil in Hc); try done.
    + apply andb_prop in HP as [H1 H2].
      apply elem_of_app in Hc as [Hc|Hc]; [apply (in_chans_pr_subst X) in Hc as [Hc|Hc]; [| |done]|
        apply (in_chans_pr_subst X) in Hc as [Hc|Hc]; [| |done]]; auto; left; apply elem_of_app; auto.
    + apply andb_prop in HP as [H1 H2].
      apply elem_of_app in Hc as [Hc|Hc]; [apply (in_chans_pr_subst X) in Hc as [Hc|Hc]; [| |done]|
        apply (in_chans_pr_subst X) in Hc as [Hc|Hc]; [| |done]]; auto; left; apply elem_of_app; auto.
    + case_decide; [by right|by left].
    + case_decide; simpl in Hc; [by left|]. by apply (in_chans_pr_subst X).
    + by apply (gin_chans_gpr_subst X).
  - destruct g as [es| |𝜆 P|g1 g2]; simpl; intros Hg Hc.
    + by apply elem_of_nil in Hc.
    + by apply elem_of_nil in Hc.
    + destruct 𝜆; simpl in Hg, Hc |- *; try done.
      1: apply elem_of_cons in Hc as [->|Hc]; [left; by left|]; apply (in_chans_pr_subst X) in Hc as [Hc|Hc];
           [left; by right| |done]; rewrite ?in_chans_shiftv in Hc; right; exact Hc.
      all: apply (in_chans_pr_subst X) in Hc as [Hc|Hc]; [by left| |done]; rewrite ?in_chans_shiftv in Hc;
           right; exact Hc.
    + apply andb_prop in Hg as [[H1 H2]%andb_prop _].
      apply elem_of_app in Hc as [Hc|Hc]; [apply (gin_chans_gpr_subst X) in Hc as [Hc|Hc]; [| |done]|
        apply (gin_chans_gpr_subst X) in Hc as [Hc|Hc]; [| |done]]; auto; left; apply elem_of_app; auto.
Qed.

Lemma prog_step_out_chan_r P t c v P' :
  obsrb P = true → prog_step P (CTag t) (ActExt (PrOut c v)) P' → c ∈ out_chans P.
Proof.
  intros Hob Hs. remember (CTag t) as s eqn:Es. remember (ActExt (PrOut c v)) as l eqn:El.
  revert Hob Es El.
  induction Hs as [g s l P' Hg| | | | | | | | | ]; intros Hob Es El; simplify_eq; simpl in *.
  - exfalso. remember (ActExt (PrOut c v)) as l eqn:El. revert El.
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
  obsrb P = true → prog_step P (CTag t) (ActExt (PrIn c v)) P' → c ∈ in_chans P.
Proof.
  intros Hob Hs. remember (CTag t) as s eqn:Es. remember (ActExt (PrIn c v)) as l eqn:El.
  revert Hob Es El.
  induction Hs as [g s l P' Hg| | | | | | | | | ]; intros Hob Es El; simplify_eq; simpl in *.
  - remember (ActExt (PrIn c v)) as l eqn:El. revert El.
    induction Hg; intros El; simplify_eq; simpl in *.
    + by left.
    + apply andb_prop in Hob as [[Hob _]%andb_prop _]. apply elem_of_app. left. by apply IHHg.
    + apply andb_prop in Hob as [[_ Hob]%andb_prop _]. apply elem_of_app. right. by apply IHHg.
  - apply andb_prop in Hob as [Hob _]. apply elem_of_app. left. by apply IHHs.
  - apply andb_prop in Hob as [_ Hob]. apply elem_of_app. right. by apply IHHs.
  - apply andb_prop in Hob as [Hob _]. apply elem_of_app. left. by apply IHHs.
  - apply andb_prop in Hob as [_ Hob]. apply elem_of_app. right. by apply IHHs.
Qed.

Lemma prog_step_chans_sub_r P s l P' :
  obsrb P = true → prog_step P s l P' →
  (∀ c, c ∈ out_chans P' → c ∈ out_chans P) ∧ (∀ c, c ∈ in_chans P' → c ∈ in_chans P).
Proof.
  intros Hob Hs.
  induction Hs as [g s l P' Hg| |e P Q s l P' He Hp IH|e P Q s l Q' He Hp IH
                  |P Q s l P' Hp IH|P Q s l Q' Hp IH|P Q t t' c v P' Q' Hp IHp Hq IHq
                  |P Q t t' c v P' Q' Hp IHp Hq IHq| |t X P]; simpl in Hob; simplify_eq.
  - revert Hob. induction Hg as [| | | | |g1 g2 s l P' Hg IH|g1 g2 s l P' Hg IH]; intros Hob; simpl.
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
    + apply (out_chans_pr_subst X) in Hc as [Hc|Hc]; [done| |done]. simpl in Hc. by rewrite out_chans_tren in Hc.
    + apply (in_chans_pr_subst X) in Hc as [Hc|Hc]; [done| |done]. simpl in Hc. by rewrite in_chans_tren in Hc.
Qed.

Lemma co_succ_complete_r T k α T' :
  obsrb T = true → prog_step T (CTag k) (ActExt α) T' →
  ∃ a, co_tag a = k ∧ co_act a = α ∧ T' ∈ co_succ T a.
Proof.
  intros Hob Hs. remember (CTag k) as s eqn:Es. remember (ActExt α) as l eqn:El.
  revert k α Es El Hob.
  induction Hs as [g s l P' Hg|t c e v He|e P Q s l P' He Hp IH|e P Q s l Q' He Hp IH
                  |P Q s l P' Hp IH|P Q s l Q' Hp IH| | |P s l P' Hp IH|t X P];
    intros k α Es El Hob; simplify_eq; simpl in Hob.
  - (* guard *)
    enough (∃ a, co_tag a = k ∧ co_act a = α ∧ P' ∈ gco_succ g a) as (a & ? & ? & ?)
      by (exists a; by simpl).
    remember (CTag k) as s eqn:Es. remember (ActExt α) as l eqn:El. revert k α Es El Hob.
    induction Hg as [| t c v P|t E es qs P Hq|t M es qs n P Hq|t es qs P Hq|g1 g2 s l P' Hg IH|g1 g2 s l P' Hg IH];
      intros k α Es El Hob; simplify_eq; simpl in Hob.
    + exists (CoIn k c v). simpl. split; [done|]. split; [done|]. rewrite decide_True; [|done].
      by apply list_elem_of_singleton.
    + exists (CoOp k E qs). simpl. split; [done|]. split; [done|]. rewrite decide_True; [|done].
      by apply list_elem_of_singleton.
    + exists (CoMeas k M qs n). simpl. split; [done|]. split; [done|]. rewrite decide_True; [|done].
      by apply list_elem_of_singleton.
    + exists (CoInit k qs). simpl. split; [done|]. split; [done|]. rewrite decide_True; [|done].
      by apply list_elem_of_singleton.
    + apply andb_prop in Hob as [[Hob _]%andb_prop _].
      destruct (IH _ _ eq_refl eq_refl Hob) as (a & ? & ? & Hin). exists a. simpl.
      split; [done|]. split; [done|]. apply elem_of_app. by left.
    + apply andb_prop in Hob as [[_ Hob]%andb_prop _].
      destruct (IH _ _ eq_refl eq_refl Hob) as (a & ? & ? & Hin). exists a. simpl.
      split; [done|]. split; [done|]. apply elem_of_app. by right.
  - exists (CoOut k c v). simpl. split; [done|]. split; [done|]. rewrite decide_True; [|done].
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

Lemma gobs_success_stuck_r g s l P' : gobsrb g = true → gsuccessb g = true → ¬ prog_gstep g s l P'.
Proof.
  intros Hob Hsu Hg. induction Hg; simpl in *; try done;
    apply andb_prop in Hob as [_ Hn]; by rewrite Hsu in Hn.
Qed.

Lemma obs_step_r T s l T' : obsr T → prog_step T s l T' → obsr T'.
Proof.
  intros [Hob Hdis] Hs. revert Hob Hdis.
  induction Hs as [g s l P' Hg|t c e v He|e P Q s l P' He Hp IH|e P Q s l Q' He Hp IH
                  |P Q s l P' Hp IH|P Q s l Q' Hp IH|P Q t t' c v P' Q' Hp IHp Hq IHq
                  |P Q t t' c v P' Q' Hp IHp Hq IHq|P s l P' Hp IH|t X P];
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
      apply (out_chans_pr_subst X) in Hc as [Hc|Hc]; [| |done]; apply (in_chans_pr_subst X) in Hc' as [Hc'|Hc']; try done;
        simpl in Hc, Hc'; rewrite ?out_chans_tren in Hc; rewrite ?in_chans_tren in Hc'; exact (Hdis x Hc Hc').
Qed.

Lemma obs_tau_r T s T' : obsr T → prog_step T s τ T' → ∃ t, s = CTag t ∧ T' ∈ co_succ T (CoInit t []).
Proof.
  intros [Hob Hdis] Hs. remember τ as l eqn:El. revert Hob Hdis El.
  induction Hs as [g s l P' Hg|t c e v He|e P Q s l P' He Hp IH|e P Q s l Q' He Hp IH
                  |P Q s l P' Hp IH|P Q s l Q' Hp IH|P Q t t' c v P' Q' Hp IHp Hq IHq
                  |P Q t t' c v P' Q' Hp IHp Hq IHq|P s l P' Hp IH|t X P];
    intros Hob Hdis El; simplify_eq; simpl in Hob.
  - exfalso. clear Hdis. remember τ as l0 eqn:El. revert Hob El.
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

Lemma obs_success_step_r T s l T' : obsrb T = true → prog_step T s l T' → success T → success T'.
Proof.
  unfold success. intros Hob Hs. revert Hob.
  induction Hs as [g s l P' Hg|t c e v He|e P Q s l P' He Hp IH|e P Q s l Q' He Hp IH
                  |P Q s l P' Hp IH|P Q s l Q' Hp IH|P Q t t' c v P' Q' Hp IHp Hq IHq
                  |P Q t t' c v P' Q' Hp IHp Hq IHq|P s l P' Hp IH|t X P];
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

Lemma tnodes_obsr T : obsr T → ∀ n T', T' ∈ tnodes T n → obsr T'.
Proof.
  intros HT n. induction n as [|a n IH] using rev_ind; intros T' Hin.
  - rewrite tnodes_nil in Hin. apply list_elem_of_singleton in Hin. by subst.
  - apply tnodes_app_elem in Hin as (T0 & HT0 & Hin).
    destruct (co_succ_step _ _ _ Hin) as [Hs|[_ Hs]]; exact (obs_step_r _ _ _ _ (IH T0 HT0) Hs).
Qed.

Definition wobserver (T : proc) : Prop :=
  (∀ n T', T' ∈ tnodes T n → obsr T')
  ∧ (∀ n, length (tnodes T n) ≤ 1)
  ∧ (∀ n m k c v c' v' T', T' ∈ tnodes T (n ++ [CoOut k c v] ++ m) → co_succ T' (CoOut k c' v') = []).

Lemma observer_w T : observer T → wobserver T.
Proof.
  intros HT. split; [|split].
  - intros n T' HT'. apply obsr_obs. exact (tnodes_obs T (proj1 HT) n T' HT').
  - exact (observer_le1 T HT).
  - exact (proj2 (proj2 (proj2 HT))).
Qed.

Definition observer_r (T : proc) : Prop :=
  obsr T
  ∧ (∀ k x y, (k, x) ∈ tagged (tren tag_base T) → (k, y) ∈ tagged (tren tag_base T) → x = y)
  ∧ (∀ n, length (tnodes T n) ≤ 1)
  ∧ (∀ n m k c v c' v' T', T' ∈ tnodes T (n ++ [CoOut k c v] ++ m) → co_succ T' (CoOut k c' v') = []).

Lemma observer_r_w T : observer_r T → wobserver T.
Proof.
  intros (HT & _ & Hl & Ho). split; [|split]; [|done|done]. exact (tnodes_obsr T HT).
Qed.

Lemma tnodes_unique_w T n T1 T2 :
  wobserver T → T1 ∈ tnodes T n → T2 ∈ tnodes T n → T1 = T2.
Proof.
  intros HT H1 H2. pose proof (proj1 (proj2 HT) n) as Hl.
  destruct (tnodes T n) as [|T0 [|]]; simpl in Hl; try lia.
  - by apply elem_of_nil in H1.
  - apply list_elem_of_singleton in H1, H2. congruence.
Qed.

Lemma succ_at_tnodes_w T n T' :
  wobserver T → T' ∈ tnodes T n → succ_at T n = true ↔ success T'.
Proof.
  intros HT Hin. unfold succ_at. rewrite existsb_exists. split.
  - intros (T0 & HT0%list_elem_of_In & Hs). by rewrite (tnodes_unique_w T n T' T0).
  - intros Hs. exists T'. split; [by apply list_elem_of_In|done].
Qed.

Lemma succ_at_persists_w T n m :
  wobserver T → succ_at T n = true → tnodes T (n ++ m) ≠ [] → succ_at T (n ++ m) = true.
Proof.
  intros HT. induction m as [|a m IH] using rev_ind; intros Hs Hne.
  - by rewrite app_nil_r in *.
  - rewrite app_assoc in *. destruct (tnodes T ((n ++ m) ++ [a])) as [|T'' l] eqn:E; [by exfalso; apply Hne|].
    assert (Hin : T'' ∈ tnodes T ((n ++ m) ++ [a])) by (rewrite E; by left).
    apply tnodes_app_elem in Hin as (T' & HT' & Hin').
    apply (succ_at_tnodes_w T _ T'' HT); [rewrite E; by left|].
    assert (Hob : obsrb T' = true) by exact (proj1 (proj1 HT (n ++ m) T' HT')).
    assert (Hs' : success T').
    { apply (succ_at_tnodes_w T _ T' HT HT'). apply IH; [done|]. intros E'. rewrite E' in HT'. by apply elem_of_nil in HT'. }
    destruct (co_succ_step _ _ _ Hin') as [Hp|[_ Hp]]; exact (obs_success_step_r _ _ _ _ Hob Hp Hs').
Qed.

Lemma S_T_tnodes_w T n T' : wobserver T → T' ∈ tnodes T n → S_T T n = true ↔ success T'.
Proof.
  intros HT Hin. split.
  - intros (i & Hi & Hs)%S_T_spec.
    rewrite <- (succ_at_tnodes_w T n T' HT Hin), <- (take_drop i n).
    apply succ_at_persists_w; [done|done|]. rewrite take_drop. intros E. rewrite E in Hin. by apply elem_of_nil in Hin.
  - intros Hs. apply S_T_spec. exists (length n). split; [done|].
    rewrite take_ge; [|done]. by apply (succ_at_tnodes_w T n T').
Qed.

Definition rtagged (T : proc) (k : tag) (x : okind) : Prop := (tag_base k, x) ∈ tagged (tren tag_base T).

Lemma tnodes_rtagged T n T' k x : T' ∈ tnodes T n → (k, x) ∈ tagged T' → rtagged T k x.
Proof.
  revert T' k x. induction n as [|a n IH] using rev_ind; intros T' k x Hin Hk.
  - rewrite tnodes_nil in Hin. apply list_elem_of_singleton in Hin. subst T'. unfold rtagged.
    rewrite tagged_tren. apply list_elem_of_fmap. by exists (k, x).
  - apply tnodes_app_elem in Hin as (T0 & HT0 & Hin). unfold rtagged.
    assert (Hk' : (tag_base k, x) ∈ tagged (tren tag_base T')).
    { rewrite tagged_tren. apply list_elem_of_fmap. by exists (k, x). }
    assert (Hstep : ∃ s l, prog_step T0 s l T') by (destruct (co_succ_step _ _ _ Hin) as [Hp|[_ Hp]]; eauto).
    destruct Hstep as (s & l & Hp).
    pose proof (prog_step_tagged _ _ _ _ _ Hp Hk') as Hk0. rewrite tagged_tren in Hk0.
    apply list_elem_of_fmap in Hk0 as ([k0 x0] & E & Hk0). simpl in E. injection E as E1 E2. subst x0.
    pose proof (IH T0 k0 x HT0 Hk0) as H0. unfold rtagged in H0. by rewrite E1.
Qed.
Lemma eff_out_keep_w T n C k c v Tn T' :
  wobserver T → Tn ∈ tnodes T n → T' ∈ tnodes T (eff n C) → co_succ Tn (CoOut k c v) ≠ [] →
  k ∉ (λ m : msg, m.1.1) <$> C → co_succ T' (CoOut k c v) ≠ [].
Proof.
  intros HT HTn. unfold eff. revert T'. induction C as [|m C IH] using rev_ind; intros T' HT' Hne Hk.
  - simpl in HT'. rewrite app_nil_r in HT'. by rewrite (tnodes_unique_w T n T' Tn HT HT' HTn).
  - rewrite fmap_app, app_assoc in HT'. simpl in HT'.
    apply tnodes_app_elem in HT' as (T0 & HT0 & H0).
    rewrite fmap_app in Hk. apply not_elem_of_app in Hk as [HkC Hkm].
    apply (co_succ_out_keep T0 _ _ _ _ _ H0).
    + apply IH; [done|done|done].
    + intros c' v' E. injection E as E _ _. apply Hkm. rewrite E. simpl. by left.
Qed.

End LqP.

(* end hide *)
