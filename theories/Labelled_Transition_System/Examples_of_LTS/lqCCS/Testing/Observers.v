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
(* begin hide *)
(* * lqCCS: deterministic observers and their shape

    The observers of the characterisation are the programs with [①] whose
    offers at a point of the interaction depend only on the co-trace that led
    there: no [τ] prefix, no recursion, no restriction, no channel used both
    for input and for output (no communication inside the observer), and
    [①] never in a sum with a prefix (success is persistent).  For them the
    state after a co-trace is computed by [co_succ], and the shape of the
    observer is its menu [I_T] (the offers at every node) and its success
    nodes [S_T]. *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list.
From TestingTheory Require Import ActTau pMust_almost_sure.
From TestingTheory Require Import lqCCS.Language.Algebra lqCCS.Language.Quantum lqCCS.Language.Quantum_Weights.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.LTS lqCCS.Language.Congruence lqCCS.Testing.Scheduled lqCCS.Testing.DistLTS lqCCS.Testing.Programs.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

(* ** Success is invariant under congruence *)

Lemma successb_ren f P : successb (ren f P) = successb P
with gsuccessb_gren f g : gsuccessb (gren f g) = gsuccessb g.
Proof.
  - destruct P; simpl; try done.
    + destruct (eval e) as [[b| |]|]; try done. destruct b; apply successb_ren.
    + by rewrite !successb_ren.
  - destruct g; simpl; try done. by rewrite !gsuccessb_gren.
Qed.

Lemma cgr_step_successb :
  (∀ P Q, cgr_step P Q → successb P = successb Q) ∧ (∀ g h, gcgr_step g h → gsuccessb g = gsuccessb h).
Proof.
  apply cgr_gcgr_step_ind; simpl; intros; try done;
    try (by rewrite orb_false_r); try apply orb_comm; try apply orb_assoc;
    try (by rewrite !successb_ren);
    try (match goal with Hx : _ = _ |- _ => by rewrite Hx end).
Qed.

Lemma cgr_successb P Q : P ≡* Q → successb P = successb Q.
Proof.
  induction 1 as [|P Q R [Hpq|Hqp] _ IH]; [done| |].
  - rewrite <- IH. by apply cgr_step_successb.
  - rewrite <- IH. symmetry. by apply cgr_step_successb.
Qed.

Lemma cgr_success P Q : P ≡* Q → success P ↔ success Q.
Proof. intros Hc. unfold success. by rewrite (cgr_successb _ _ Hc). Qed.

(* ** The class of observers *)

Fixpoint obsb (T : proc) : bool :=
  match T with
  | PSend _ _ _ => true
  | PIte _ P Q | P ∥ Q => obsb P && obsb Q
  | ν _ | PVar _ | PRec _ _ _ => false
  | PG g => gobsb g
  end
with gobsb (g : guard) : bool :=
  match g with
  | GNil _ | ① => true
  | PTau _ ∙ _ => false
  | _ ∙ P => obsb P
  | (g1 + g2)%lq => gobsb g1 && gobsb g2 && negb (gsuccessb g1 || gsuccessb g2)
  end.

Fixpoint out_chans (T : proc) : list channel :=
  match T with
  | PSend _ c _ => [c]
  | PIte _ P Q | P ∥ Q => out_chans P ++ out_chans Q
  | ν P | PRec _ _ P => out_chans P
  | PVar _ => []
  | PG g => gout_chans g
  end
with gout_chans (g : guard) : list channel :=
  match g with
  | GNil _ | ① => []
  | _ ∙ P => out_chans P
  | (g1 + g2)%lq => gout_chans g1 ++ gout_chans g2
  end.

Fixpoint in_chans (T : proc) : list channel :=
  match T with
  | PSend _ _ _ | PVar _ => []
  | PIte _ P Q | P ∥ Q => in_chans P ++ in_chans Q
  | ν P | PRec _ _ P => in_chans P
  | PG g => gin_chans g
  end
with gin_chans (g : guard) : list channel :=
  match g with
  | GNil _ | ① => []
  | PRecv _ c ∙ P => c :: in_chans P
  | _ ∙ P => in_chans P
  | (g1 + g2)%lq => gin_chans g1 ++ gin_chans g2
  end.

Definition chan_disjoint (T : proc) : Prop := ∀ c, c ∈ out_chans T → c ∉ in_chans T.

Definition obs (T : proc) : Prop := obsb T = true ∧ chan_disjoint T.

(* ** The observer after a co-action *)

Fixpoint co_succ (T : proc) (a : coact) : list proc :=
  match T with
  | PSend k' c' e =>
      match a with
      | CoOut k c v => if decide (k = k' ∧ c = c' ∧ eval e = Some v) then [𝟘] else []
      | _ => []
      end
  | PIte e P Q =>
      match eval e with
      | Some (VBool true) => co_succ P a
      | Some (VBool false) => co_succ Q a
      | _ => []
      end
  | P ∥ Q => ((λ P', P' ∥ Q) <$> co_succ P a) ++ ((λ Q', P ∥ Q') <$> co_succ Q a)
  | ν _ | PVar _ | PRec _ _ _ => []
  | PG g => gco_succ g a
  end
with gco_succ (g : guard) (a : coact) : list proc :=
  match g with
  | GNil _ | ① => []
  | 𝜆 ∙ P =>
      match 𝜆, a with
      | PRecv k' c', CoIn k c v => if decide (k = k' ∧ c = c') then [P ⟦ v ⟧] else []
      | POp k' E' es, CoOp k E qs =>
          if decide (k = k' ∧ E = E' ∧ eval_qubits es = Some qs) then [P] else []
      | PMeas k' M' es, CoMeas k M qs n =>
          if decide (k = k' ∧ M = M' ∧ eval_qubits es = Some qs) then [P ⟦ VNat n ⟧] else []
      | PInit k' es, CoInit k qs => if decide (k = k' ∧ eval_qubits es = Some qs) then [P] else []
      | _, _ => []
      end
  | (g1 + g2)%lq => gco_succ g1 a ++ gco_succ g2 a
  end.

Lemma co_succ_sound T a T' : T' ∈ co_succ T a → prog_step T (CTag (co_tag a)) (ActExt (co_act a)) T'
with gco_succ_sound g a T' : T' ∈ gco_succ g a → prog_gstep g (CTag (co_tag a)) (ActExt (co_act a)) T'.
Proof.
  - destruct T; simpl; intros Hin.
    + destruct a; try by apply elem_of_nil in Hin.
      case_decide as Hd; [|by apply elem_of_nil in Hin].
      destruct Hd as (-> & -> & He). apply list_elem_of_singleton in Hin. subst. simpl. by constructor.
    + destruct (eval e) as [[[]| |]|] eqn:He; try by apply elem_of_nil in Hin.
      * apply pr_iteT; [done|]. by apply co_succ_sound.
      * apply pr_iteF; [done|]. by apply co_succ_sound.
    + apply elem_of_app in Hin as [(P' & -> & Hin)%list_elem_of_fmap|(Q' & -> & Hin)%list_elem_of_fmap].
      * apply pr_parL. by apply co_succ_sound.
      * apply pr_parR. by apply co_succ_sound.
    + by apply elem_of_nil in Hin.
    + by apply elem_of_nil in Hin.
    + by apply elem_of_nil in Hin.
    + by apply gco_succ_sound.
  - destruct g; simpl; intros Hin.
    + by apply elem_of_nil in Hin.
    + by apply elem_of_nil in Hin.
    + destruct 𝜆, a; try by apply elem_of_nil in Hin.
      * case_decide as Hd; [|by apply elem_of_nil in Hin]. destruct Hd as (-> & ->).
        apply list_elem_of_singleton in Hin. subst. simpl. by constructor.
      * case_decide as Hd; [|by apply elem_of_nil in Hin]. destruct Hd as (-> & -> & He).
        apply list_elem_of_singleton in Hin. subst. simpl. by constructor.
      * case_decide as Hd; [|by apply elem_of_nil in Hin]. destruct Hd as (-> & -> & He).
        apply list_elem_of_singleton in Hin. subst. simpl. by constructor.
      * case_decide as Hd; [|by apply elem_of_nil in Hin]. destruct Hd as (-> & He).
        apply list_elem_of_singleton in Hin. subst. simpl. by constructor.
    + apply elem_of_app in Hin as [Hin|Hin].
      * apply pr_sumL. by apply gco_succ_sound.
      * apply pr_sumR. by apply gco_succ_sound.
Qed.

Lemma co_succ_complete T k α T' :
  obsb T = true → prog_step T (CTag k) (ActExt α) T' →
  ∃ a, co_tag a = k ∧ co_act a = α ∧ T' ∈ co_succ T a.
Proof.
  intros Hob Hs. remember (CTag k) as s eqn:Es. remember (ActExt α) as l eqn:El.
  revert k α Es El Hob.
  induction Hs as [g s l P' Hg|t c e v He|e P Q s l P' He Hp IH|e P Q s l Q' He Hp IH
                  |P Q s l P' Hp IH|P Q s l Q' Hp IH| | |P s l P' Hp IH|t X P] using prog_step_guard_ind;
    intros k α Es El Hob; simplify_eq; simpl in Hob.
  - (* guard *)
    enough (∃ a, co_tag a = k ∧ co_act a = α ∧ P' ∈ gco_succ g a) as (a & ? & ? & ?)
      by (exists a; by simpl).
    remember (CTag k) as s eqn:Es. remember (ActExt α) as l eqn:El. revert k α Es El Hob.
    induction Hg as [| t c v P|t E es qs P Hq|t M es qs n P Hq|t es qs P Hq|g1 g2 s l P' Hg IH|g1 g2 s l P' Hg IH] using prog_gstep_ind;
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

(* ** The channels of the actions of an observer *)

Lemma prog_step_out_chan P t c v P' :
  obsb P = true → prog_step P (CTag t) (ActExt (PrOut c v)) P' → c ∈ out_chans P.
Proof.
  intros Hob Hs. remember (CTag t) as s eqn:Es. remember (ActExt (PrOut c v)) as l eqn:El.
  revert Hob Es El.
  induction Hs as [g s l P' Hg| | | | | | | | | ] using prog_step_guard_ind; intros Hob Es El; simplify_eq; simpl in *.
  - exfalso. remember (ActExt (PrOut c v)) as l eqn:El. revert El.
    induction Hg using prog_gstep_ind; intros El; simplify_eq; simpl in Hob.
    + apply andb_prop in Hob as [[Hob _]%andb_prop _]. by apply IHHg.
    + apply andb_prop in Hob as [[_ Hob]%andb_prop _]. by apply IHHg.
  - by apply list_elem_of_singleton.
  - apply andb_prop in Hob as [Hob _]. apply elem_of_app. left. by apply IHHs.
  - apply andb_prop in Hob as [_ Hob]. apply elem_of_app. right. by apply IHHs.
  - apply andb_prop in Hob as [Hob _]. apply elem_of_app. left. by apply IHHs.
  - apply andb_prop in Hob as [_ Hob]. apply elem_of_app. right. by apply IHHs.
Qed.

Lemma prog_step_in_chan P t c v P' :
  obsb P = true → prog_step P (CTag t) (ActExt (PrIn c v)) P' → c ∈ in_chans P.
Proof.
  intros Hob Hs. remember (CTag t) as s eqn:Es. remember (ActExt (PrIn c v)) as l eqn:El.
  revert Hob Es El.
  induction Hs as [g s l P' Hg| | | | | | | | | ] using prog_step_guard_ind; intros Hob Es El; simplify_eq; simpl in *.
  - remember (ActExt (PrIn c v)) as l eqn:El. revert El.
    induction Hg using prog_gstep_ind; intros El; simplify_eq; simpl in *.
    + by left.
    + apply andb_prop in Hob as [[Hob _]%andb_prop _]. apply elem_of_app. left. by apply IHHg.
    + apply andb_prop in Hob as [[_ Hob]%andb_prop _]. apply elem_of_app. right. by apply IHHg.
  - apply andb_prop in Hob as [Hob _]. apply elem_of_app. left. by apply IHHs.
  - apply andb_prop in Hob as [_ Hob]. apply elem_of_app. right. by apply IHHs.
  - apply andb_prop in Hob as [Hob _]. apply elem_of_app. left. by apply IHHs.
  - apply andb_prop in Hob as [_ Hob]. apply elem_of_app. right. by apply IHHs.
Qed.

(* ** Observers have no silent step and stay observers *)

Lemma obs_no_tau T : obs T → ∀ s T', ¬ prog_step T s τ T'.
Proof.
  intros [Hob Hdis] s T' Hs. remember τ as l eqn:El. revert Hob Hdis El.
  induction Hs as [g s l P' Hg| |e P Q s l P' He Hp IH|e P Q s l Q' He Hp IH
                  |P Q s l P' Hp IH|P Q s l Q' Hp IH|P Q t t' c v P' Q' Hp Hq|P Q t t' c v P' Q' Hp Hq| | ] using prog_step_guard_ind;
    intros Hob Hdis El; simplify_eq; simpl in Hob.
  - remember τ as l eqn:El. revert Hob El.
    induction Hg as [| | | | |g1 g2 s l P' Hg IH|g1 g2 s l P' Hg IH] using prog_gstep_ind; intros Hob El; simplify_eq; simpl in Hob.
    + apply andb_prop in Hob as [[Hob _]%andb_prop _]. apply IH; [|done|done].
      intros c Hc Hc'. apply (Hdis c); simpl; apply elem_of_app; by left.
    + apply andb_prop in Hob as [[_ Hob]%andb_prop _]. apply IH; [|done|done].
      intros c Hc Hc'. apply (Hdis c); simpl; apply elem_of_app; by right.
  - apply andb_prop in Hob as [Hob _]. apply IH; [done| |done].
    intros c Hc Hc'. apply (Hdis c); simpl; apply elem_of_app; by left.
  - apply andb_prop in Hob as [_ Hob]. apply IH; [done| |done].
    intros c Hc Hc'. apply (Hdis c); simpl; apply elem_of_app; by right.
  - apply andb_prop in Hob as [Hob _]. apply IH; [done| |done].
    intros c Hc Hc'. apply (Hdis c); simpl; apply elem_of_app; by left.
  - apply andb_prop in Hob as [_ Hob]. apply IH; [done| |done].
    intros c Hc Hc'. apply (Hdis c); simpl; apply elem_of_app; by right.
  - apply andb_prop in Hob as [HobP HobQ]. apply (Hdis c); simpl; apply elem_of_app; [left|right].
    + by eapply prog_step_out_chan.
    + by eapply prog_step_in_chan.
  - apply andb_prop in Hob as [HobP HobQ]. apply (Hdis c); simpl; apply elem_of_app; [right|left].
    + by eapply prog_step_out_chan.
    + by eapply prog_step_in_chan.
Qed.

(* ** Observers stay observers, and their success persists *)

Lemma gsuccessb_gsubst k v g : gsuccessb (gsubst k v g) = gsuccessb g.
Proof. induction g; simpl; try done. by rewrite IHg1, IHg2. Qed.


Lemma obsb_subst k v P : obsb (subst k v P) = obsb P
with gobsb_gsubst k v g : gobsb (gsubst k v g) = gobsb g.
Proof.
  - destruct P; simpl; try done; try (by rewrite !obsb_subst); try apply gobsb_gsubst.
  - destruct g; simpl; try done; try (by rewrite !gobsb_gsubst, !gsuccessb_gsubst);
      try (destruct 𝜆; simpl; try done; apply obsb_subst).
Qed.

Lemma out_chans_subst k v P : out_chans (subst k v P) = out_chans P
with gout_chans_gsubst k v g : gout_chans (gsubst k v g) = gout_chans g.
Proof.
  - destruct P; simpl; try done; try (by rewrite !out_chans_subst); try apply out_chans_subst;
      try apply gout_chans_gsubst.
  - destruct g; simpl; try done; try (by rewrite !gout_chans_gsubst);
      try (destruct 𝜆; simpl; apply out_chans_subst).
Qed.

Lemma in_chans_subst k v P : in_chans (subst k v P) = in_chans P
with gin_chans_gsubst k v g : gin_chans (gsubst k v g) = gin_chans g.
Proof.
  - destruct P; simpl; try done; try (by rewrite !in_chans_subst); try apply in_chans_subst;
      try apply gin_chans_gsubst.
  - destruct g; simpl; try done; try (by rewrite !gin_chans_gsubst);
      try (destruct 𝜆; simpl; try apply in_chans_subst; by rewrite in_chans_subst).
Qed.

Lemma prog_step_chans_sub P s l P' :
  obsb P = true → prog_step P s l P' →
  (∀ c, c ∈ out_chans P' → c ∈ out_chans P) ∧ (∀ c, c ∈ in_chans P' → c ∈ in_chans P).
Proof.
  intros Hob Hs.
  induction Hs as [g s l P' Hg| |e P Q s l P' He Hp IH|e P Q s l Q' He Hp IH
                  |P Q s l P' Hp IH|P Q s l Q' Hp IH|P Q t t' c v P' Q' Hp IHp Hq IHq
                  |P Q t t' c v P' Q' Hp IHp Hq IHq| | ] using prog_step_guard_ind; simpl in Hob; simplify_eq.
  - revert Hob. induction Hg as [| | | | |g1 g2 s l P' Hg IH|g1 g2 s l P' Hg IH] using prog_gstep_ind; intros Hob; simpl.
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
Qed.

(* The derivative of an observer by a visible action. *)
Lemma obs_step T k α T' : obs T → prog_step T (CTag k) (ActExt α) T' → obs T'.
Proof.
  intros [Hob Hdis] Hs. remember (CTag k) as s eqn:Es. remember (ActExt α) as l eqn:El.
  revert Hob Hdis Es El.
  induction Hs as [g s l P' Hg| |e P Q s l P' He Hp IH|e P Q s l Q' He Hp IH
                  |P Q s l P' Hp IH|P Q s l Q' Hp IH| | | | ] using prog_step_guard_ind;
    intros Hob Hdis Es El; simplify_eq; simpl in Hob.
  - revert Hob Hdis. induction Hg as [| | | | |g1 g2 s l P' Hg IH|g1 g2 s l P' Hg IH] using prog_gstep_ind;
      intros Hob Hdis; simplify_eq; simpl in Hob.
    + split; [by rewrite obsb_subst|]. intros x. rewrite out_chans_subst, in_chans_subst.
      intros Hc Hc'. apply (Hdis x); simpl; [done|by right].
    + split; [done|]. intros x Hc Hc'. by apply (Hdis x).
    + split; [by rewrite obsb_subst|]. intros x. rewrite out_chans_subst, in_chans_subst.
      intros Hc Hc'. by apply (Hdis x).
    + split; [done|]. intros x Hc Hc'. by apply (Hdis x).
    + apply andb_prop in Hob as [[Hob _]%andb_prop _]. apply IH; [done|].
      intros x Hc Hc'. apply (Hdis x); simpl; apply elem_of_app; by left.
    + apply andb_prop in Hob as [[_ Hob]%andb_prop _]. apply IH; [done|].
      intros x Hc Hc'. apply (Hdis x); simpl; apply elem_of_app; by right.
  - split; [done|]. intros x Hc. by apply elem_of_nil in Hc.
  - apply andb_prop in Hob as [Hob _]. apply IH; [done| |done|done].
    intros x Hc Hc'. apply (Hdis x); simpl; apply elem_of_app; by left.
  - apply andb_prop in Hob as [_ Hob]. apply IH; [done| |done|done].
    intros x Hc Hc'. apply (Hdis x); simpl; apply elem_of_app; by right.
  - apply andb_prop in Hob as [HobP HobQ].
    assert (HP' : obs P').
    { apply IH; [done| |done|done]. intros x Hc Hc'. apply (Hdis x); simpl; apply elem_of_app; by left. }
    destruct HP' as [HobP' HdisP].
    split; [simpl; by rewrite HobP', HobQ|].
    intros x Hc Hc'. simpl in Hc, Hc'. apply elem_of_app in Hc as [Hc|Hc]; apply elem_of_app in Hc' as [Hc'|Hc'].
    + by apply (HdisP x).
    + apply (Hdis x); simpl; apply elem_of_app; [left; by apply (proj1 (prog_step_chans_sub _ _ _ _ HobP Hp))|by right].
    + apply (Hdis x); simpl; apply elem_of_app; [by right|left; by apply (proj2 (prog_step_chans_sub _ _ _ _ HobP Hp))].
    + apply (Hdis x); simpl; apply elem_of_app; by right.
  - apply andb_prop in Hob as [HobP HobQ].
    assert (HQ' : obs Q').
    { apply IH; [done| |done|done]. intros x Hc Hc'. apply (Hdis x); simpl; apply elem_of_app; by right. }
    destruct HQ' as [HobQ' HdisQ].
    split; [simpl; by rewrite HobP, HobQ'|].
    intros x Hc Hc'. simpl in Hc, Hc'. apply elem_of_app in Hc as [Hc|Hc]; apply elem_of_app in Hc' as [Hc'|Hc'].
    + apply (Hdis x); simpl; apply elem_of_app; by left.
    + apply (Hdis x); simpl; apply elem_of_app; [by left|right; by apply (proj2 (prog_step_chans_sub _ _ _ _ HobQ Hp))].
    + apply (Hdis x); simpl; apply elem_of_app; [right; by apply (proj1 (prog_step_chans_sub _ _ _ _ HobQ Hp))|by left].
    + by apply (HdisQ x).
Qed.

Lemma gobs_success_stuck g s l P' : gobsb g = true → gsuccessb g = true → ¬ prog_gstep g s l P'.
Proof.
  intros Hob Hsu Hg. induction Hg using prog_gstep_ind; simpl in *; try done;
    apply andb_prop in Hob as [_ Hn]; by rewrite Hsu in Hn.
Qed.

Lemma obs_success_step T k α T' :
  obsb T = true → prog_step T (CTag k) (ActExt α) T' → success T → success T'.
Proof.
  unfold success. intros Hob Hs. remember (CTag k) as s eqn:Es. remember (ActExt α) as l eqn:El.
  revert Hob Es El.
  induction Hs as [g s l P' Hg| |e P Q s l P' He Hp IH|e P Q s l Q' He Hp IH
                  |P Q s l P' Hp IH|P Q s l Q' Hp IH| | | | ] using prog_step_guard_ind;
    intros Hob Es El Hsu; simplify_eq; simpl in *.
  - exfalso. by eapply gobs_success_stuck.
  - apply andb_prop in Hob as [Hob _]. rewrite He in Hsu. by apply IH.
  - apply andb_prop in Hob as [_ Hob]. rewrite He in Hsu. by apply IH.
  - apply andb_prop in Hob as [Hob _]. apply orb_prop in Hsu as [Hsu|Hsu].
    + rewrite (IH Hob eq_refl eq_refl Hsu). done.
    + rewrite Hsu. apply orb_true_r.
  - apply andb_prop in Hob as [_ Hob]. apply orb_prop in Hsu as [Hsu|Hsu].
    + by rewrite Hsu.
    + rewrite (IH Hob eq_refl eq_refl Hsu). apply orb_true_r.
Qed.

(* ** The states of an observer at a node, its menu and its success nodes *)

Definition tnodes (T : proc) (n : node) : list proc :=
  fold_left (λ Ts a, concat ((λ T', co_succ T' a) <$> Ts)) n [T].

Lemma tnodes_nil T : tnodes T [] = [T].
Proof. done. Qed.

Lemma tnodes_app T n a : tnodes T (n ++ [a]) = concat ((λ T', co_succ T' a) <$> tnodes T n).
Proof. unfold tnodes. by rewrite fold_left_app. Qed.

Lemma tnodes_app_elem T n a T'' :
  T'' ∈ tnodes T (n ++ [a]) ↔ ∃ T', T' ∈ tnodes T n ∧ T'' ∈ co_succ T' a.
Proof.
  rewrite tnodes_app, list_elem_of_In, in_concat. split.
  - intros (l & Hl & Hin). apply list_elem_of_In, list_elem_of_fmap in Hl as (T' & -> & HT').
    exists T'. split; [done|]. by apply list_elem_of_In.
  - intros (T' & HT' & Hin). exists (co_succ T' a). split; [|by apply list_elem_of_In].
    apply list_elem_of_In, list_elem_of_fmap. by exists T'.
Qed.

Lemma tnodes_obs T : obs T → ∀ n T', T' ∈ tnodes T n → obs T'.
Proof.
  intros HT n. induction n as [|a n IH] using rev_ind; intros T' Hin.
  - rewrite tnodes_nil in Hin. apply list_elem_of_singleton in Hin. by subst.
  - apply tnodes_app_elem in Hin as (T0 & HT0 & Hin). apply (obs_step T0 (co_tag a) (co_act a)).
    + by apply IH.
    + by apply co_succ_sound.
Qed.

(* ** Tags of observers *)

Definition kind_of (a : coact) : okind :=
  match a with
  | CoOut _ _ _ => KOut | CoIn _ _ _ => KIn | CoOp _ _ _ => KOp | CoMeas _ _ _ _ => KMeas | CoInit _ _ => KInit
  end.

Lemma co_succ_tagged T a T' : T' ∈ co_succ T a → (co_tag a, kind_of a) ∈ tagged T
with gco_succ_tagged g a T' : T' ∈ gco_succ g a → (co_tag a, kind_of a) ∈ gtagged g.
Proof.
  - destruct T; simpl; intros Hin.
    + destruct a; try by apply elem_of_nil in Hin. case_decide as Hd; [|by apply elem_of_nil in Hin].
      destruct Hd as (-> & -> & _). simpl. by left.
    + destruct (eval e) as [[[]| |]|]; try (by apply elem_of_nil in Hin);
        apply elem_of_app; [left|right]; by eapply co_succ_tagged.
    + apply elem_of_app in Hin as [(P' & -> & Hin)%list_elem_of_fmap|(Q' & -> & Hin)%list_elem_of_fmap];
        apply elem_of_app; [left|right]; by eapply co_succ_tagged.
    + by apply elem_of_nil in Hin.
    + by apply elem_of_nil in Hin.
    + by apply elem_of_nil in Hin.
    + by eapply gco_succ_tagged.
  - destruct g; simpl; intros Hin.
    + by apply elem_of_nil in Hin.
    + by apply elem_of_nil in Hin.
    + destruct 𝜆, a; try (by apply elem_of_nil in Hin).
      all: case_decide as Hd; [|by apply elem_of_nil in Hin].
      * destruct Hd as (-> & ->). simpl. by left.
      * destruct Hd as (-> & -> & _). simpl. by left.
      * destruct Hd as (-> & -> & _). simpl. by left.
      * destruct Hd as (-> & _). simpl. by left.
    + apply elem_of_app in Hin as [Hin|Hin]; apply elem_of_app; [left|right]; by eapply gco_succ_tagged.
Qed.

Lemma co_succ_sublist T a T' : obsb T = true → T' ∈ co_succ T a → tagged T' `sublist_of` tagged T
with gco_succ_sublist g a T' : gobsb g = true → T' ∈ gco_succ g a → tagged T' `sublist_of` gtagged g.
Proof.
  - destruct T; simpl; intros Hob Hin.
    + destruct a; try by apply elem_of_nil in Hin. case_decide as Hd; [|by apply elem_of_nil in Hin].
      apply list_elem_of_singleton in Hin. subst. simpl. apply sublist_nil_l.
    + apply andb_prop in Hob as [HobP HobQ].
      destruct (eval e) as [[[]| |]|]; try by apply elem_of_nil in Hin.
      * apply sublist_inserts_r. by eapply co_succ_sublist.
      * apply sublist_inserts_l. by eapply co_succ_sublist.
    + apply andb_prop in Hob as [HobP HobQ].
      apply elem_of_app in Hin as [(P' & -> & Hin)%list_elem_of_fmap|(Q' & -> & Hin)%list_elem_of_fmap]; simpl.
      * apply sublist_app; [by eapply co_succ_sublist|done].
      * apply sublist_app; [done|by eapply co_succ_sublist].
    + done.
    + done.
    + done.
    + by eapply gco_succ_sublist.
  - destruct g; simpl; intros Hob Hin.
    + by apply elem_of_nil in Hin.
    + by apply elem_of_nil in Hin.
    + destruct 𝜆, a; try (by apply elem_of_nil in Hin).
      all: case_decide as Hd; [|by apply elem_of_nil in Hin];
        apply list_elem_of_singleton in Hin; subst; simpl; try rewrite tagged_subst; by apply sublist_cons.
    + apply andb_prop in Hob as [[Hob1 Hob2]%andb_prop _].
      apply elem_of_app in Hin as [Hin|Hin].
      * apply sublist_inserts_r. by eapply gco_succ_sublist.
      * apply sublist_inserts_l. by eapply gco_succ_sublist.
Qed.

Lemma co_succ_unique T a T1 T2 :
  obsb T = true → NoDup (tags T) → T1 ∈ co_succ T a → T2 ∈ co_succ T a → T1 = T2
with gco_succ_unique g a T1 T2 :
  gobsb g = true → NoDup (map fst (gtagged g)) → T1 ∈ gco_succ g a → T2 ∈ gco_succ g a → T1 = T2.
Proof.
  - unfold tags. destruct T as [t c e|e P Q|P Q|P|X|t X P|g]; simpl; intros Hob Hnd H1 H2.
    + destruct a; try by apply elem_of_nil in H1. case_decide; [|by apply elem_of_nil in H1].
      apply list_elem_of_singleton in H1, H2. congruence.
    + apply andb_prop in Hob as [HobP HobQ]. rewrite map_app in Hnd. apply NoDup_app in Hnd as (Hn1 & _ & Hn2).
      destruct (eval e) as [[[]| |]|]; try (by apply elem_of_nil in H1);
        [by eapply (co_succ_unique P)|by eapply (co_succ_unique Q)].
    + apply andb_prop in Hob as [HobP HobQ]. rewrite map_app in Hnd. apply NoDup_app in Hnd as (Hn1 & Hdis & Hn2).
      apply elem_of_app in H1 as [(P1 & -> & H1)%list_elem_of_fmap|(Q1 & -> & H1)%list_elem_of_fmap];
        apply elem_of_app in H2 as [(P2 & -> & H2)%list_elem_of_fmap|(Q2 & -> & H2)%list_elem_of_fmap].
      * f_equal. by eapply (co_succ_unique P).
      * exfalso. apply (Hdis (co_tag a)).
        { apply list_elem_of_fmap. eexists. split; [|by eapply co_succ_tagged]. done. }
        { apply list_elem_of_fmap. eexists. split; [|by eapply co_succ_tagged]. done. }
      * exfalso. apply (Hdis (co_tag a)).
        { apply list_elem_of_fmap. eexists. split; [|by eapply co_succ_tagged]. done. }
        { apply list_elem_of_fmap. eexists. split; [|by eapply co_succ_tagged]. done. }
      * f_equal. by eapply (co_succ_unique Q).
    + by apply elem_of_nil in H1.
    + by apply elem_of_nil in H1.
    + by apply elem_of_nil in H1.
    + by eapply gco_succ_unique.
  - destruct g; simpl; intros Hob Hnd H1 H2.
    + by apply elem_of_nil in H1.
    + by apply elem_of_nil in H1.
    + destruct 𝜆, a; try (by apply elem_of_nil in H1).
      all: case_decide; [|by apply elem_of_nil in H1]; apply list_elem_of_singleton in H1, H2; congruence.
    + apply andb_prop in Hob as [[Hob1 Hob2]%andb_prop _]. rewrite map_app in Hnd.
      apply NoDup_app in Hnd as (Hn1 & Hdis & Hn2).
      apply elem_of_app in H1 as [H1|H1]; apply elem_of_app in H2 as [H2|H2].
      * by eapply (gco_succ_unique g1).
      * exfalso. apply (Hdis (co_tag a)).
        { apply list_elem_of_fmap. eexists. split; [|by eapply gco_succ_tagged]. done. }
        { apply list_elem_of_fmap. eexists. split; [|by eapply gco_succ_tagged]. done. }
      * exfalso. apply (Hdis (co_tag a)).
        { apply list_elem_of_fmap. eexists. split; [|by eapply gco_succ_tagged]. done. }
        { apply list_elem_of_fmap. eexists. split; [|by eapply gco_succ_tagged]. done. }
      * by eapply (gco_succ_unique g2).
Qed.

(* An observer: a tag names one kind of prefix, there is one state at each
    node, and an output that has been consumed is not offered again. *)
Definition observer (T : proc) : Prop :=
  obs T
  ∧ (∀ k x y, (k, x) ∈ tagged T → (k, y) ∈ tagged T → x = y)
  ∧ (∀ n, length (tnodes T n) ≤ 1)
  ∧ (∀ n m k c v c' v' T', T' ∈ tnodes T (n ++ [CoOut k c v] ++ m) → co_succ T' (CoOut k c' v') = []).

Lemma tnodes_tags T : obs T → ∀ n T', T' ∈ tnodes T n → tagged T' `sublist_of` tagged T.
Proof.
  intros HT n. induction n as [|a n IH] using rev_ind; intros T' Hin.
  - rewrite tnodes_nil in Hin. apply list_elem_of_singleton in Hin. by subst.
  - apply tnodes_app_elem in Hin as (T0 & HT0 & Hin). etrans; [|by apply IH].
    apply (co_succ_sublist T0 a); [|done]. by apply (tnodes_obs T HT n).
Qed.

Lemma tnodes_nodup T n T' : obs T → NoDup (tags T) → T' ∈ tnodes T n → NoDup (tags T').
Proof.
  intros HT Hnd Hin. unfold tags in *. eapply sublist_NoDup; [exact Hnd|].
  apply (fmap_sublist fst). by eapply tnodes_tags.
Qed.

Lemma co_succ_len T a : obsb T = true → NoDup (tags T) → length (co_succ T a) ≤ 1
with gco_succ_len g a : gobsb g = true → NoDup (map fst (gtagged g)) → length (gco_succ g a) ≤ 1.
Proof.
  - unfold tags. destruct T as [t c e|e P Q|P Q|P|X|t X P|g]; simpl; intros Hob Hnd.
    + destruct a; simpl; try lia. case_decide; simpl; lia.
    + apply andb_prop in Hob as [HobP HobQ]. rewrite map_app in Hnd. apply NoDup_app in Hnd as (Hn1 & _ & Hn2).
      destruct (eval e) as [[[]| |]|]; simpl; try lia; by apply co_succ_len.
    + apply andb_prop in Hob as [HobP HobQ]. rewrite map_app in Hnd. apply NoDup_app in Hnd as (Hn1 & Hdis & Hn2).
      rewrite length_app, !length_fmap.
      pose proof (co_succ_len P a HobP Hn1) as HlP. pose proof (co_succ_len Q a HobQ Hn2) as HlQ.
      destruct (co_succ P a) as [|P1 l1] eqn:E1; simpl; [lia|].
      destruct (co_succ Q a) as [|Q1 l2] eqn:E2; simpl.
      * simpl in HlP. lia.
      * exfalso. apply (Hdis (co_tag a)).
        { apply list_elem_of_fmap. eexists. split; [|apply (co_succ_tagged P a P1); rewrite E1; by left]. done. }
        { apply list_elem_of_fmap. eexists. split; [|apply (co_succ_tagged Q a Q1); rewrite E2; by left]. done. }
    + simpl. lia.
    + simpl. lia.
    + simpl. lia.
    + by apply gco_succ_len.
  - destruct g; simpl; intros Hob Hnd.
    + lia.
    + lia.
    + destruct 𝜆, a; simpl; try lia; case_decide; simpl; lia.
    + apply andb_prop in Hob as [[Hob1 Hob2]%andb_prop _]. rewrite map_app in Hnd.
      apply NoDup_app in Hnd as (Hn1 & Hdis & Hn2). rewrite length_app.
      pose proof (gco_succ_len g1 a Hob1 Hn1) as Hl1. pose proof (gco_succ_len g2 a Hob2 Hn2) as Hl2.
      destruct (gco_succ g1 a) as [|P1 l1] eqn:E1; simpl; [lia|].
      destruct (gco_succ g2 a) as [|Q1 l2] eqn:E2; simpl.
      * simpl in Hl1. lia.
      * exfalso. apply (Hdis (co_tag a)).
        { apply list_elem_of_fmap. eexists. split; [|apply (gco_succ_tagged g1 a P1); rewrite E1; by left]. done. }
        { apply list_elem_of_fmap. eexists. split; [|apply (gco_succ_tagged g2 a Q1); rewrite E2; by left]. done. }
Qed.

Lemma nodup_le1 T : obs T → NoDup (tags T) → ∀ n, length (tnodes T n) ≤ 1.
Proof.
  intros HT Hnd n. induction n as [|a n IH] using rev_ind; [done|].
  rewrite tnodes_app. destruct (tnodes T n) as [|T0 [|]] eqn:E; simpl in IH; try lia; simpl; [done|].
  rewrite app_nil_r. apply co_succ_len.
  - apply (tnodes_obs T HT n). rewrite E. by left.
  - apply (tnodes_nodup T n); [done|done|]. rewrite E. by left.
Qed.

Lemma observer_le1 T : observer T → ∀ n, length (tnodes T n) ≤ 1.
Proof. intros HT. apply HT. Qed.

Lemma tnodes_unique T n T1 T2 :
  observer T → T1 ∈ tnodes T n → T2 ∈ tnodes T n → T1 = T2.
Proof.
  intros HT H1 H2. pose proof (observer_le1 T HT n) as Hl.
  destruct (tnodes T n) as [|T0 [|]]; simpl in Hl; try lia.
  - by apply elem_of_nil in H1.
  - apply list_elem_of_singleton in H1, H2. congruence.
Qed.

(* Kinds: a tag of an observer names one kind of prefix, at every node. *)
Lemma tagged_kind_unique (L : list (tag * okind)) k x y :
  NoDup (map fst L) → (k, x) ∈ L → (k, y) ∈ L → x = y.
Proof.
  induction L as [|[k' z] L IH]; intros Hnd Hx Hy; [by apply elem_of_nil in Hx|].
  simpl in Hnd. apply NoDup_cons in Hnd as [Hk Hnd].
  apply elem_of_cons in Hx as [Hx|Hx]; apply elem_of_cons in Hy as [Hy|Hy].
  - congruence.
  - exfalso. injection Hx as -> ->. apply Hk. apply list_elem_of_fmap. by exists (k', y).
  - exfalso. injection Hy as -> ->. apply Hk. apply list_elem_of_fmap. by exists (k', x).
  - by apply IH.
Qed.

Lemma observer_kind T n1 n2 T1 T2 a1 a2 :
  observer T → T1 ∈ tnodes T n1 → T2 ∈ tnodes T n2 →
  co_succ T1 a1 ≠ [] → co_succ T2 a2 ≠ [] → co_tag a1 = co_tag a2 → kind_of a1 = kind_of a2.
Proof.
  intros HT H1 H2 Hne1 Hne2 Hk.
  destruct (co_succ T1 a1) as [|T1' l1] eqn:E1; [done|].
  destruct (co_succ T2 a2) as [|T2' l2] eqn:E2; [done|].
  assert (Hin1 : (co_tag a1, kind_of a1) ∈ tagged T)
    by (eapply elem_of_submseteq; [apply (co_succ_tagged T1 a1 T1'); rewrite E1; by left|];
        apply sublist_submseteq; by eapply tnodes_tags; [apply HT|]).
  assert (Hin2 : (co_tag a2, kind_of a2) ∈ tagged T)
    by (eapply elem_of_submseteq; [apply (co_succ_tagged T2 a2 T2'); rewrite E2; by left|];
        apply sublist_submseteq; by eapply tnodes_tags; [apply HT|]).
  rewrite Hk in Hin1. exact (proj1 (proj2 HT) _ _ _ Hin1 Hin2).
Qed.

(* ** Outputs: consuming one commutes with every other co-action, keeps
    success, and removes its tag *)

Lemma co_succ_out_swap T k c v b T1 T2 :
  T1 ∈ co_succ T (CoOut k c v) → T2 ∈ co_succ T1 b →
  ∃ T1', T1' ∈ co_succ T b ∧ T2 ∈ co_succ T1' (CoOut k c v).
Proof.
  revert T1 T2. induction T as [t c' e|e P IHP Q IHQ|P IHP Q IHQ|P IH|X|t X P IH|g]; simpl;
    intros T1 T2 H1 H2.
  - case_decide; [|by apply elem_of_nil in H1]. apply list_elem_of_singleton in H1. subst.
    simpl in H2. by apply elem_of_nil in H2.
  - destruct (eval e) as [[[]| |]|]; try (by apply elem_of_nil in H1); eauto.
  - apply elem_of_app in H1 as [(P1 & -> & H1)%list_elem_of_fmap|(Q1 & -> & H1)%list_elem_of_fmap];
      simpl in H2;
      apply elem_of_app in H2 as [(P2 & -> & H2)%list_elem_of_fmap|(Q2 & -> & H2)%list_elem_of_fmap].
    + destruct (IHP _ _ H1 H2) as (P1' & HP1' & HP2). exists (P1' ∥ Q). split.
      * apply elem_of_app. left. apply list_elem_of_fmap. by exists P1'.
      * simpl. apply elem_of_app. left. apply list_elem_of_fmap. by exists P2.
    + exists (P ∥ Q2). split.
      * apply elem_of_app. right. apply list_elem_of_fmap. by exists Q2.
      * simpl. apply elem_of_app. left. apply list_elem_of_fmap. by exists P1.
    + exists (P2 ∥ Q). split.
      * apply elem_of_app. left. apply list_elem_of_fmap. by exists P2.
      * simpl. apply elem_of_app. right. apply list_elem_of_fmap. by exists Q1.
    + destruct (IHQ _ _ H1 H2) as (Q1' & HQ1' & HQ2). exists (P ∥ Q1'). split.
      * apply elem_of_app. right. apply list_elem_of_fmap. by exists Q1'.
      * simpl. apply elem_of_app. right. apply list_elem_of_fmap. by exists Q2.
  - by apply elem_of_nil in H1.
  - by apply elem_of_nil in H1.
  - by apply elem_of_nil in H1.
  - exfalso. clear -H1. induction g; simpl in H1; try by apply elem_of_nil in H1.
    + destruct 𝜆; by apply elem_of_nil in H1.
    + apply elem_of_app in H1 as [H1|H1]; auto.
Qed.

Lemma co_succ_out_successb T k c v T' :
  T' ∈ co_succ T (CoOut k c v) → successb T' = successb T.
Proof.
  revert T'. induction T as [t c' e|e P IHP Q IHQ|P IHP Q IHQ|P IH|X|t X P IH|g]; simpl; intros T' H1.
  - case_decide; [|by apply elem_of_nil in H1]. apply list_elem_of_singleton in H1. by subst.
  - destruct (eval e) as [[[]| |]|]; try (by apply elem_of_nil in H1); auto.
  - apply elem_of_app in H1 as [(P1 & -> & H1)%list_elem_of_fmap|(Q1 & -> & H1)%list_elem_of_fmap]; simpl.
    + by rewrite (IHP _ H1).
    + by rewrite (IHQ _ H1).
  - by apply elem_of_nil in H1.
  - by apply elem_of_nil in H1.
  - by apply elem_of_nil in H1.
  - exfalso. clear -H1. induction g; simpl in H1; try by apply elem_of_nil in H1.
    + destruct 𝜆; by apply elem_of_nil in H1.
    + apply elem_of_app in H1 as [H1|H1]; auto.
Qed.

Lemma co_succ_out_tag_gone T k c v T' :
  NoDup (tags T) → T' ∈ co_succ T (CoOut k c v) → k ∉ tags T'.
Proof.
  unfold tags. revert T'. induction T as [t c' e|e P IHP Q IHQ|P IHP Q IHQ|P IH|X|t X P IH|g]; simpl;
    intros T' Hnd H1.
  - case_decide; [|by apply elem_of_nil in H1]. apply list_elem_of_singleton in H1. subst. simpl.
    by intros ?%elem_of_nil.
  - rewrite map_app in Hnd. apply NoDup_app in Hnd as (Hn1 & Hdis & Hn2).
    destruct (eval e) as [[[]| |]|]; try (by apply elem_of_nil in H1); auto.
  - rewrite map_app in Hnd. apply NoDup_app in Hnd as (Hn1 & Hdis & Hn2).
    apply elem_of_app in H1 as [(P1 & -> & H1)%list_elem_of_fmap|(Q1 & -> & H1)%list_elem_of_fmap]; simpl;
      rewrite map_app; intros [Hk|Hk]%elem_of_app.
    + by apply (IHP _ Hn1 H1).
    + apply (Hdis k); [|done]. apply list_elem_of_fmap. eexists. split; [|by eapply co_succ_tagged]. done.
    + apply (Hdis k); [done|]. apply list_elem_of_fmap. eexists. split; [|by eapply co_succ_tagged]. done.
    + by apply (IHQ _ Hn2 H1).
  - by apply elem_of_nil in H1.
  - by apply elem_of_nil in H1.
  - by apply elem_of_nil in H1.
  - exfalso. clear -H1. induction g; simpl in H1; try by apply elem_of_nil in H1.
    + destruct 𝜆; by apply elem_of_nil in H1.
    + apply elem_of_app in H1 as [H1|H1]; auto.
Qed.

Lemma tnodes_tag_gone T n k c v m T' :
  obs T → NoDup (tags T) → T' ∈ tnodes T (n ++ [CoOut k c v] ++ m) → k ∉ tags T'.
Proof.
  intros HT Hnd. revert T'. induction m as [|b m IH] using rev_ind; intros T' Hin.
  - rewrite app_nil_r in Hin. apply tnodes_app_elem in Hin as (T0 & HT0 & H0).
    apply (co_succ_out_tag_gone T0 k c v T'); [|done]. by apply (tnodes_nodup T n).
  - rewrite !app_assoc in Hin. apply tnodes_app_elem in Hin as (T0 & HT0 & H0). rewrite <- !app_assoc in HT0.
    intros Hk. apply (IH T0 HT0). unfold tags in *. eapply elem_of_submseteq; [exact Hk|].
    apply sublist_submseteq, (fmap_sublist fst). apply (co_succ_sublist T0 b T'); [|done].
    rewrite !app_assoc in HT0. by apply (tnodes_obs T HT ((n ++ [CoOut k c v]) ++ m)).
Qed.

(* Terms whose tags are all distinct are observers. *)
Lemma observer_of_nodup T : obs T → NoDup (tags T) → observer T.
Proof.
  intros HT Hnd. split; [done|]. split; [|split].
  - intros k x y. apply tagged_kind_unique, Hnd.
  - by apply nodup_le1.
  - intros n m k c v c' v' T' Hin. destruct (co_succ T' (CoOut k c' v')) as [|T'' l] eqn:E; [done|].
    exfalso. apply (tnodes_tag_gone T n k c v m T' HT Hnd Hin). unfold tags. apply list_elem_of_fmap.
    exists (k, KOut). split; [done|]. apply (co_succ_tagged T' (CoOut k c' v') T''). rewrite E. by left.
Qed.

(* The offer answered by a co-action. *)
Definition offer_of (a : coact) : offer :=
  match a with
  | CoOut k c v => OffOut k c v
  | CoIn k c _ => OffIn k c
  | CoOp k E qs => OffOp k E qs
  | CoMeas k M qs _ => OffMeas k M qs
  | CoInit k qs => OffInit k qs
  end.

(* The menu of [T] at the node [n]. *)
Definition menu (T : proc) (n : node) (o : offer) : Prop :=
  ∃ T' a, T' ∈ tnodes T n ∧ offer_of a = o ∧ co_succ T' a ≠ [].

(* The success nodes of [T]: a prefix of the node has a successful state. *)
Definition succ_at (T : proc) (n : node) : bool := existsb successb (tnodes T n).

Definition S_T (T : proc) (n : node) : bool :=
  existsb (λ i, succ_at T (take i n)) (seq 0 (S (length n))).

Lemma S_T_spec T n : S_T T n = true ↔ ∃ i, i ≤ length n ∧ succ_at T (take i n) = true.
Proof.
  unfold S_T. rewrite existsb_exists. split.
  - intros (i & Hi%in_seq & Hs). exists i. split; [lia|done].
  - intros (i & Hi & Hs). exists i. split; [apply in_seq; lia|done].
Qed.

Lemma S_T_ext_closed T : ext_closed (S_T T).
Proof.
  intros n a Hn. apply S_T_spec in Hn as (i & Hi & Hs). apply S_T_spec. exists i.
  rewrite length_app. split; [simpl; lia|]. rewrite take_app_le; [done|lia].
Qed.

Lemma succ_at_tnodes T n T' :
  observer T → T' ∈ tnodes T n → succ_at T n = true ↔ success T'.
Proof.
  intros HT Hin. unfold succ_at. rewrite existsb_exists. split.
  - intros (T0 & HT0%list_elem_of_In & Hs). by rewrite (tnodes_unique T n T' T0).
  - intros Hs. exists T'. split; [by apply list_elem_of_In|done].
Qed.

(* Success persists along the co-actions. *)
Lemma succ_at_persists T n m :
  observer T → succ_at T n = true → tnodes T (n ++ m) ≠ [] → succ_at T (n ++ m) = true.
Proof.
  intros HT. induction m as [|a m IH] using rev_ind; intros Hs Hne.
  - by rewrite app_nil_r in *.
  - rewrite app_assoc in *. destruct (tnodes T ((n ++ m) ++ [a])) as [|T'' l] eqn:E; [by exfalso; apply Hne|].
    assert (Hin : T'' ∈ tnodes T ((n ++ m) ++ [a])) by (rewrite E; by left).
    apply tnodes_app_elem in Hin as (T' & HT' & Hin').
    apply (succ_at_tnodes T _ T'' HT); [rewrite E; by left|].
    apply (obs_success_step T' (co_tag a) (co_act a)).
    + by apply (tnodes_obs T (proj1 HT) (n ++ m)).
    + by apply co_succ_sound.
    + apply (succ_at_tnodes T _ T' HT HT'). apply IH; [done|]. intros E'. rewrite E' in HT'. by apply elem_of_nil in HT'.
Qed.

Lemma S_T_tnodes T n T' : observer T → T' ∈ tnodes T n → S_T T n = true ↔ success T'.
Proof.
  intros HT Hin. split.
  - intros (i & Hi & Hs)%S_T_spec.
    rewrite <- (succ_at_tnodes T n T' HT Hin), <- (take_drop i n).
    apply succ_at_persists; [done|done|]. rewrite take_drop. intros E. rewrite E in Hin. by apply elem_of_nil in Hin.
  - intros Hs. apply S_T_spec. exists (length n). split; [done|].
    rewrite take_ge; [|done]. by apply (succ_at_tnodes T n T').
Qed.

(* Consuming an output keeps every other enabled co-action. *)
Lemma co_succ_out_keep T k c v b T1 :
  T1 ∈ co_succ T (CoOut k c v) → co_succ T b ≠ [] →
  (∀ c' v', b ≠ CoOut k c' v') → co_succ T1 b ≠ [].
Proof.
  revert T1. induction T as [t c' e|e P IHP Q IHQ|P IHP Q IHQ|P IH|X|t X P IH|g]; simpl;
    intros T1 H1 Hb Hne.
  - case_decide as Hd; [|by apply elem_of_nil in H1]. destruct Hd as (-> & -> & He).
    destruct b; try done. case_decide as Hd'; [|done]. destruct Hd' as (-> & -> & _).
    exfalso. by eapply Hne.
  - destruct (eval e) as [[[]| |]|]; try (by apply elem_of_nil in H1);
      [by apply (IHP _ H1)|by apply (IHQ _ H1)].
  - apply elem_of_app in H1 as [(P1 & -> & H1)%list_elem_of_fmap|(Q1 & -> & H1)%list_elem_of_fmap]; simpl.
    + intros E. apply app_eq_nil in E as [E1 E2]. apply fmap_nil_inv in E1, E2. apply Hb.
      assert (co_succ P b = []) as ->.
      { destruct (co_succ P b) eqn:EP; [done|]. exfalso.
        assert (Hp : p :: l ≠ []) by done. exact (IHP _ H1 Hp Hne E1). }
      by rewrite E2.
    + intros E. apply app_eq_nil in E as [E1 E2]. apply fmap_nil_inv in E1, E2. apply Hb.
      assert (co_succ Q b = []) as ->.
      { destruct (co_succ Q b) eqn:EQ; [done|]. exfalso.
        assert (Hq : p :: l ≠ []) by done. exact (IHQ _ H1 Hq Hne E2). }
      by rewrite E1.
  - by apply elem_of_nil in H1.
  - by apply elem_of_nil in H1.
  - by apply elem_of_nil in H1.
  - exfalso. clear -H1. induction g; simpl in H1; try by apply elem_of_nil in H1.
    + destruct 𝜆; by apply elem_of_nil in H1.
    + apply elem_of_app in H1 as [H1|H1]; auto.
Qed.

(* An input accepts every value, a measurement every outcome. *)
Lemma co_succ_in_val T k c v v' : co_succ T (CoIn k c v) ≠ [] → co_succ T (CoIn k c v') ≠ []
with gco_succ_in_val g k c v v' : gco_succ g (CoIn k c v) ≠ [] → gco_succ g (CoIn k c v') ≠ [].
Proof.
  - destruct T as [t c' e|e P Q|P Q|P|X|t X P|g]; simpl; intros H; try done.
    + destruct (eval e) as [[[]| |]|]; try done; by eapply co_succ_in_val.
    + intros E. apply app_eq_nil in E as [E1 E2]. apply fmap_nil_inv in E1, E2. apply H.
      assert (co_succ P (CoIn k c v) = []) as ->.
      { destruct (co_succ P (CoIn k c v)) eqn:E; [done|]. exfalso.
        apply (co_succ_in_val P k c v v'); [by rewrite E|done]. }
      assert (co_succ Q (CoIn k c v) = []) as ->.
      { destruct (co_succ Q (CoIn k c v)) eqn:E; [done|]. exfalso.
        apply (co_succ_in_val Q k c v v'); [by rewrite E|done]. }
      done.
    + by eapply gco_succ_in_val.
  - destruct g as [es| |𝜆 P|g1 g2]; simpl; intros H; try done.
    + destruct 𝜆; try done. by case_decide.
    + intros E. apply app_eq_nil in E as [E1 E2]. apply H.
      assert (gco_succ g1 (CoIn k c v) = []) as ->.
      { destruct (gco_succ g1 (CoIn k c v)) eqn:E; [done|]. exfalso.
        apply (gco_succ_in_val g1 k c v v'); [by rewrite E|done]. }
      assert (gco_succ g2 (CoIn k c v) = []) as ->.
      { destruct (gco_succ g2 (CoIn k c v)) eqn:E; [done|]. exfalso.
        apply (gco_succ_in_val g2 k c v v'); [by rewrite E|done]. }
      done.
Qed.

Lemma co_succ_meas_out T k M qs n n' :
  co_succ T (CoMeas k M qs n) ≠ [] → co_succ T (CoMeas k M qs n') ≠ []
with gco_succ_meas_out g k M qs n n' :
  gco_succ g (CoMeas k M qs n) ≠ [] → gco_succ g (CoMeas k M qs n') ≠ [].
Proof.
  - destruct T as [t c' e|e P Q|P Q|P|X|t X P|g]; simpl; intros H; try done.
    + destruct (eval e) as [[[]| |]|]; try done; by eapply co_succ_meas_out.
    + intros E. apply app_eq_nil in E as [E1 E2]. apply fmap_nil_inv in E1, E2. apply H.
      assert (co_succ P (CoMeas k M qs n) = []) as ->.
      { destruct (co_succ P (CoMeas k M qs n)) eqn:E; [done|]. exfalso.
        apply (co_succ_meas_out P k M qs n n'); [by rewrite E|done]. }
      assert (co_succ Q (CoMeas k M qs n) = []) as ->.
      { destruct (co_succ Q (CoMeas k M qs n)) eqn:E; [done|]. exfalso.
        apply (co_succ_meas_out Q k M qs n n'); [by rewrite E|done]. }
      done.
    + by eapply gco_succ_meas_out.
  - destruct g as [es| |𝜆 P|g1 g2]; simpl; intros H; try done.
    + destruct 𝜆; try done. by case_decide.
    + intros E. apply app_eq_nil in E as [E1 E2]. apply H.
      assert (gco_succ g1 (CoMeas k M qs n) = []) as ->.
      { destruct (gco_succ g1 (CoMeas k M qs n)) eqn:E; [done|]. exfalso.
        apply (gco_succ_meas_out g1 k M qs n n'); [by rewrite E|done]. }
      assert (gco_succ g2 (CoMeas k M qs n) = []) as ->.
      { destruct (gco_succ g2 (CoMeas k M qs n)) eqn:E; [done|]. exfalso.
        apply (gco_succ_meas_out g2 k M qs n n'); [by rewrite E|done]. }
      done.
Qed.

(* ** The effective node: the visible node followed by the consumed outputs *)

Definition eff (n : node) (C : list msg) : node := n ++ (co_of_msg <$> C).

Lemma tnodes_app_nonempty T n m : tnodes T (n ++ m) ≠ [] → tnodes T n ≠ [].
Proof.
  induction m as [|a m IH] using rev_ind; intros Hne.
  - by rewrite app_nil_r in Hne.
  - apply IH. intros E. apply Hne. rewrite app_assoc, tnodes_app, E. done.
Qed.

(* A co-action enabled after consumed outputs was enabled before them, and
    performing it before or after the consumptions reaches the same states. *)
Lemma eff_swap T n C b T' T'' :
  T' ∈ tnodes T (eff n C) → T'' ∈ co_succ T' b →
  ∃ Tn Tb, Tn ∈ tnodes T n ∧ Tb ∈ co_succ Tn b ∧ T'' ∈ tnodes T (eff (n ++ [b]) C).
Proof.
  unfold eff. revert T' T''. induction C as [|m C IH] using rev_ind; intros T' T'' H1 H2.
  - simpl in *. rewrite app_nil_r in H1 |- *. exists T', T''. split; [done|]. split; [done|].
    apply tnodes_app_elem. by exists T'.
  - rewrite fmap_app, app_assoc in H1. simpl in H1.
    apply tnodes_app_elem in H1 as (T0 & HT0 & H0).
    destruct (co_succ_out_swap _ _ _ _ _ _ _ H0 H2) as (T1 & HT1 & HT'').
    destruct (IH _ _ HT0 HT1) as (Tn & Tb & HTn & HTb & HT1').
    exists Tn, Tb. split; [done|]. split; [done|].
    rewrite fmap_app, app_assoc. simpl. apply tnodes_app_elem. by exists T1.
Qed.

(* An output enabled before the consumptions, not among them, is still enabled. *)
Lemma eff_out_keep T n C k c v Tn T' :
  observer T → Tn ∈ tnodes T n → T' ∈ tnodes T (eff n C) → co_succ Tn (CoOut k c v) ≠ [] →
  k ∉ (λ m : msg, m.1.1) <$> C → co_succ T' (CoOut k c v) ≠ [].
Proof.
  intros HT HTn. unfold eff. revert T'. induction C as [|m C IH] using rev_ind; intros T' HT' Hne Hk.
  - simpl in HT'. rewrite app_nil_r in HT'. by rewrite (tnodes_unique T n T' Tn HT HT' HTn).
  - rewrite fmap_app, app_assoc in HT'. simpl in HT'.
    apply tnodes_app_elem in HT' as (T0 & HT0 & H0).
    rewrite fmap_app in Hk. apply not_elem_of_app in Hk as [HkC Hkm].
    apply (co_succ_out_keep T0 _ _ _ _ _ H0).
    + apply IH; [done|done|done].
    + intros c' v' E. injection E as E _ _. apply Hkm. rewrite E. simpl. by left.
Qed.

(* ** The outputs offered by an observer *)

Fixpoint out_msgs (T : proc) : list msg :=
  match T with
  | PSend k c e => match eval e with Some v => [(k, c, v)] | None => [] end
  | PIte e P Q =>
      match eval e with
      | Some (VBool true) => out_msgs P
      | Some (VBool false) => out_msgs Q
      | _ => []
      end
  | P ∥ Q => out_msgs P ++ out_msgs Q
  | _ => []
  end.

Lemma out_msgs_spec T k c v : (k, c, v) ∈ out_msgs T ↔ co_succ T (CoOut k c v) ≠ [].
Proof.
  induction T as [t c' e|e P IHP Q IHQ|P IHP Q IHQ|P IH|X|t X P IH|g]; simpl.
  - destruct (eval e) as [v0|] eqn:He.
    + rewrite list_elem_of_singleton. case_decide as Hd; split.
      * done.
      * intros _. destruct Hd as (-> & -> & E). by simplify_eq.
      * intros E. simplify_eq. exfalso. by apply Hd.
      * done.
    + split; [by intros ?%elem_of_nil|]. case_decide as Hd; [|done]. destruct Hd as (_ & _ & E). congruence.
  - destruct (eval e) as [[[]| |]|]; try (split; [by intros ?%elem_of_nil|done]); done.
  - rewrite elem_of_app, IHP, IHQ. split.
    + intros [H1|H1] E; apply app_eq_nil in E as [E1 E2]; apply fmap_nil_inv in E1, E2; done.
    + intros Hne. destruct (co_succ P (CoOut k c v)) eqn:E1; [|by left]. right. intros E2.
      apply Hne. by rewrite E2.
  - split; [by intros ?%elem_of_nil|done].
  - split; [by intros ?%elem_of_nil|done].
  - split; [by intros ?%elem_of_nil|done].
  - split; [by intros ?%elem_of_nil|]. intros Hne. exfalso. apply Hne. clear.
    induction g; simpl; try done. destruct 𝜆; done. by rewrite IHg1, IHg2.
Qed.

(* The outputs of [T] at the node [n]. *)
Definition O_T (T : proc) (n : node) : list msg := concat (out_msgs <$> tnodes T n).

Lemma O_T_spec T n k c v :
  (k, c, v) ∈ O_T T n ↔ ∃ T', T' ∈ tnodes T n ∧ co_succ T' (CoOut k c v) ≠ [].
Proof.
  unfold O_T. rewrite list_elem_of_In, in_concat. split.
  - intros (l & Hl & Hin). apply list_elem_of_In, list_elem_of_fmap in Hl as (T' & -> & HT').
    exists T'. split; [done|]. apply out_msgs_spec. by apply list_elem_of_In.
  - intros (T' & HT' & Hne). exists (out_msgs T'). split.
    + apply list_elem_of_In, list_elem_of_fmap. by exists T'.
    + apply list_elem_of_In. by apply out_msgs_spec.
Qed.
(* end hide *)
