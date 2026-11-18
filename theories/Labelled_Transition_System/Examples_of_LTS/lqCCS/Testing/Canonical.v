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
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base gmultiset countable decidable list.
From TestingTheory Require Import ActTau pMust_almost_sure pMust_smyth pMust_transfer pMust_canonical.
From TestingTheory Require Import lqCCS.General_definition.Algebra lqCCS.quantum_mem.Syntax lqCCS.quantum_mem.Quantum_Weights.
From TestingTheory Require Import lqCCS.lqCCS_prog.Syntax lqCCS.Helper.De_Brujin_lemmas lqCCS.General_definition.Parallel_choice_LTS lqCCS.quantum_mem.LTS lqCCS.lqCCS_prog.LTS lqCCS.lqCCS_par_Qmem.LTS lqCCS.lqCCS_process.LTS.LTS lqCCS.Helper.Conf_labels lqCCS.Helper.Label_lemmas lqCCS.Testing.Scheduled lqCCS.Testing.Observer_predicates lqCCS.Helper.Tag_lemmas lqCCS.Testing.DistLTS lqCCS.Testing.Programs lqCCS.Testing.Observers lqCCS.Testing.Smyth_Soundness.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

Section Canonical.
  Context `{lqP : lqCCS_Parameters}.

Section Mass.
  Context `{QM : QuantumModel}.

  Lemma tr_outs_nz M qs ρ :
    foldr (λ t acc, W_add (tr (M ⦅qs⦆[t] · ρ)) acc) W_zero (outs_nz (meas_of M qs) ρ) = tr ρ.
  Proof.
    rewrite <- (meas_tr M qs ρ), br_sum.
    fold (sum (map (λ t, one ⋅ kraus (meas_of M qs) t) (outs (meas_of M qs)))).
    rewrite app_ssum, tr_ssum, !map_map. unfold outs_nz.
    generalize (outs (meas_of M qs)) as l. intros l.
    induction l as [|t l IH]; [done|]. simpl. rewrite filter_cons. rewrite comp_1l.
    case_decide as Hk; simpl.
    - by rewrite IH.
    - rewrite Hk, tr_szero, W_add_zero. exact IH.
  Qed.

  Lemma dmass_one {C} (x : C * weight) : dmass [x] = tr x.2.
  Proof. apply W_add_zero_r. Qed.

  Lemma dmass_cons {C} (x : C * weight) (A : dist C) : dmass (x :: A) = W_add (tr x.2) (dmass A).
  Proof. done. Qed.

  Lemma sched_step_mass ρ R k Δ : sched_step ρ R k Δ → dmass Δ = tr ρ.
  Proof.
    inversion 1 as [? Hp|U qs ? Hp|qs ? Hp|M qs Rs R0 Hp0 Hf]; subst.
    - apply dmass_one.
    - rewrite dmass_one. apply sop_tr.
    - rewrite dmass_one. apply init_tr.
    - rewrite <- (tr_outs_nz M qs ρ). clear -Hf. induction Hf as [|t R1 ks Rs _ _ IH]; [done|].
      change (dmass ((R1, M ⦅qs⦆[t] · ρ) :: zip_with (λ t R', (R', M ⦅qs⦆[t] · ρ)) ks Rs)
        = W_add (tr (M ⦅qs⦆[t] · ρ)) (foldr (λ t acc, W_add (tr (M ⦅qs⦆[t] · ρ)) acc) W_zero ks)).
      by rewrite dmass_cons, IH.
  Qed.

  Lemma dmass_map_snd {A B} (f : A → B) (Δ : dist A) :
    dmass (map (λ x, (f x.1, x.2)) Δ) = dmass Δ.
  Proof. induction Δ as [|x Δ IH]; [done|]. by rewrite map_cons, !dmass_cons, IH. Qed.

  Lemma cstep_mass I O ρ c it Δ : cstep I O ρ c it Δ → dmass Δ = tr ρ.
  Proof.
    intros Hcv%cstep_cases. inversion Hcv as [z P C k Δ0 Hs| | | | |z P C t M qs t' HI|]; subst.
    - rewrite <- (sched_step_mass _ _ _ _ Hs). exact (dmass_map_snd (λ P', (z, (P', C))) Δ0).
    - apply dmass_one.
    - apply dmass_one.
    - rewrite dmass_one. apply sop_tr.
    - rewrite dmass_one. apply init_tr.
    - rewrite <- (tr_outs_nz M qs ρ). generalize (outs_nz (meas_of M qs) ρ) as ns. intros ns.
      induction ns as [|n ns IH]; [done|]. by rewrite map_cons, dmass_cons, IH.
    - apply dmass_one.
  Qed.

  Lemma cstep_ich J O ρ c k Δ :
    cstep J O ρ c (ICh k) Δ → (∀ J', cstep J' O ρ c (ICh k) Δ) ∧ ∀ y, y ∈ Δ → y.1.1 = c.1.
  Proof.
    inversion 1; subst; split.
    - intros J'. by constructor.
    - intros y (x & -> & _)%list_elem_of_fmap. done.
    - intros J'. by econstructor.
    - intros y ->%list_elem_of_singleton. done.
  Qed.

  Lemma cstep_off J O ρ c t t' Δ :
    cstep J O ρ c (IOff t t') Δ →
    ∃ o, J c.1 o ∧ (∀ J', J' c.1 o → cstep J' O ρ c (IOff t t') Δ) ∧ ∀ y, y ∈ Δ → ∃ a, offer_of a = o ∧ y.1.1 = c.1 ++ [a].
  Proof.
    intros Hcv%cstep_cases. inversion Hcv as [| |z P C t1 d v t2 P' HI Hp|z P C t1 U' qs t2 HI|z P C t1 q t2 HI|z P C t1 M qs t2 HI|z P C t1 t2 HI]; subst.
    - exists (OffIn t d). split; [done|]. split; [intros J' HJ'; by apply cs_in|].
      intros y ->%list_elem_of_singleton. by exists (CoIn t d v).
    - exists (OffOp t U' qs). split; [done|]. split; [intros J' HJ'; by apply cs_op|].
      intros y ->%list_elem_of_singleton. by exists (CoOp t U' qs).
    - exists (OffInit t q). split; [done|]. split; [intros J' HJ'; by apply cs_init|].
      intros y ->%list_elem_of_singleton. by exists (CoInit t q).
    - exists (OffMeas t M qs). split; [done|]. split; [intros J' HJ'; by apply cs_meas|].
      intros y (n & -> & _)%list_elem_of_fmap. by exists (CoMeas t M qs n).
    - exists (OffUnfold t). split; [done|]. split; [intros J' HJ'; by apply cs_unfold|].
      intros y ->%list_elem_of_singleton. by exists (CoUnfold t).
  Qed.

  Lemma cstep_nonempty J O ρ c it Δ : ρ ≠ szero → cstep J O ρ c it Δ → Δ ≠ [].
  Proof.
    intros Hρ. intros Hcv%cstep_cases. inversion Hcv as [z P C k Δ0 Hs| | | | |z P C t M qs t' HI|]; subst; try done.
    - intros E0. apply fmap_nil_inv in E0. subst Δ0. exact (sched_step_nonempty _ _ _ _ Hρ Hs eq_refl).
    - intros E0. apply fmap_nil_inv in E0. exact (outs_nz_nonempty M qs ρ Hρ E0).
  Qed.
End Mass.

#[global] Instance WeightLaws_of_QuantumModel `{QM : QuantumModel} : WeightLaws := {|
  prob_add_comm := W_add_comm;
  prob_add_assoc := W_add_assoc;
  prob_add_zero := W_add_zero;
  prob_zero_le := W_zero_le;
  prob_add_mono := W_add_mono;
|}.

Notation comp := (node * (prog * list msg))%type (only parsing).

Definition lq_menu `{QM : QuantumModel} (O : node → list msg) : MenuSts comp item coact offer.
Proof.
  refine {| mnode := λ c : comp, c.1; moffer := offer_of; mstep := λ J ρ c σ Δ, cstep J O ρ c σ Δ;
            mfree := λ σ, match σ with ICh _ => True | IOff _ _ => False end; msch := IOff 0 0 |}.
  - intros J ρ c [k|t t'] Δ Hf Hc; [exact (cstep_ich _ _ _ _ _ _ Hc)|done].
  - intros J ρ c [k|t t'] Δ Hf Hc; [done|exact (cstep_off _ _ _ _ _ _ _ Hc)].
  - intros J ρ c σ Δ Hc. exact (cstep_mass _ _ _ _ _ _ Hc).
  - intros J ρ c σ Δ Hρ Hc. exact (cstep_nonempty _ _ _ _ _ _ Hρ Hc).
  - intros J ρ c σ Δ Hρ Hc. exact (cstep_nonzero _ _ _ _ _ _ Hρ Hc).
Defined.

Definition alt_free `{QM : QuantumModel} (p q : prog * St) : Prop :=
  ∀ O, malt_free (M := lq_menu O) (λ _, True) (dinit p) (dinit q).

Lemma alt_pre_menu `{QM : QuantumModel} (p q : prog * St) :
  p ≼ q ↔ ∀ O, malt_pre (M := lq_menu O) (λ _, True) (dinit p) (dinit q).
Proof.
  split.
  - intros Hp O I S _ HS. exact (Hp I O S HS).
  - intros Hp I O S HS. exact (Hp O I S (λ _ _ _, Logic.I) HS).
Qed.

Theorem alt_free_iff `{QM : QuantumModel} (DC : dep_choice) (p q : prog * St) :
  q.2 ≠ szero → alt_free p q ↔ p ≼ q.
Proof.
  intros Hq. rewrite alt_pre_menu. unfold alt_free. split; intros Hp O.
  - apply (malt_free_iff (M := lq_menu O) _ DC); [| |apply Hp].
    + intros x ->%list_elem_of_singleton. done.
    + intros x ->%list_elem_of_singleton. exact Hq.
  - apply (malt_free_iff (M := lq_menu O) _ DC); [| |apply Hp].
    + intros x ->%list_elem_of_singleton. done.
    + intros x ->%list_elem_of_singleton. exact Hq.
Qed.

Lemma single_op_item `{QM : QuantumModel} O z t U0 qs ρ c it Δ :
  cstep (single z (OffOp t U0 qs)) O ρ c it Δ →
  (∀ J, cstep J O ρ c it Δ) ∨ ∃ t', it = IOff t t'.
Proof.
  intros Hcv%cstep_cases. inversion Hcv as [? ? ? k Δ0 Hs|? ? ? t1 d v t' P' HE HkC Hp|? ? ? t1 d v t' P' HI Hp|? ? ? t1 U' qs' t' HI|? ? ? t1 qs' t' HI|? ? ? t1 M qs' t' HI|? ? ? t1 t' HI]; subst.
  - left. intros J. by constructor.
  - left. intros J. by econstructor.
  - destruct HI as [_ Ho]. discriminate Ho.
  - destruct HI as [_ Ho]. injection Ho as -> _ _. right. by exists t'.
  - destruct HI as [_ Ho]. discriminate Ho.
  - destruct HI as [_ Ho]. discriminate Ho.
  - destruct HI as [_ Ho]. discriminate Ho.
Qed.

Theorem convergence `{QM : QuantumModel} (p q : prog * St) O S I r w t :
  p ≼ q → ext_closed S → run_word (M := lq_menu O) I S (dinit q) r w →
  (∀ n, ¬ dstable (SchedSts0 := dlts I O S) (r n)) → (∀ n t', w n ≠ IOff t t') →
  ∃ r', is_run (SchedSts0 := mdlts (M := lq_menu O) (Jstar (M := lq_menu O) (λ _, True) I S r w) (Sstar (M := lq_menu O) (λ _, True) I S r w)) Stay (dinit p) r'
    ∧ ((∀ n, ¬ dstable (SchedSts0 := mdlts (M := lq_menu O) (Jstar (M := lq_menu O) (λ _, True) I S r w) (Sstar (M := lq_menu O) (λ _, True) I S r w)) (r' n))
       ∨ ∀ v, prob_lt v (tr p.2) → ∃ m, prob_le v (succ_mass (SchedSts0 := dlts I O S) r m)).
Proof.
  intros Hpre HS Hw Hdiv Hfresh.
  assert (Hq0 : ∀ x, x ∈ dinit q → mnode (MenuSts := lq_menu O) x.1 = []).
  { intros x Hx. apply list_elem_of_singleton in Hx. by subst x. }
  assert (Hen : ∀ J (c : comp) ρ, J (mnode (MenuSts := lq_menu O) c) (OffOp t 0 []) → ∃ σ Δ, mstep (MenuSts := lq_menu O) J ρ c σ Δ).
  { intros J [z [P C]] ρ HJ. eexists (IOff t 0), _. exact (cs_op _ _ ρ z P C t 0 [] 0 HJ). }
  assert (Hf : ∀ z n ρ (c : comp) Δ, mstep (MenuSts := lq_menu O) (single z (OffOp t 0 [])) ρ c (w n) Δ → ∀ J', mstep (MenuSts := lq_menu O) J' ρ c (w n) Δ).
  { intros z n ρ c Δ Hc. destruct (single_op_item _ _ _ _ _ _ _ _ _ Hc) as [Hall|(t' & Ht)]; [exact Hall|].
    exfalso. exact (Hfresh n t' Ht). }
  destruct (mconvergence (M := lq_menu O) _ (dinit p) (dinit q) (proj1 (alt_pre_menu p q) Hpre O)
    Hq0 S HS I r w (OffOp t 0 []) (λ _ _ _, Logic.I) Logic.I Hw Hdiv Hen Hf) as (r' & Hr' & Hc).
  exists r'. split; [done|]. destruct Hc as [Hc|Hc]; [by left|right]. intros v Hv. apply Hc.
  assert (E : dmass (dinit p) = tr p.2) by exact (dmass_one (([], (p.1, [])), p.2)).
  rewrite E. exact Hv.
Qed.

Definition plain (z : node) : Prop := ∀ t c v, CoOut t c v ∉ z.

Lemma plain_app z a : plain z → (∀ t c v, a ≠ CoOut t c v) → plain (z ++ [a]).
Proof.
  intros Hn Ha t c v Hin. apply elem_of_app in Hin as [Hin|Hin]; [exact (Hn t c v Hin)|].
  apply list_elem_of_singleton in Hin. exact (Ha t c v (eq_sym Hin)).
Qed.

Lemma cstep_outputs `{QM : QuantumModel} I O O' ρ c σ Δ :
  (∀ m, m ∈ O c.1 → m ∈ O' c.1) → cstep I O ρ c σ Δ → cstep I O' ρ c σ Δ.
Proof.
  intros HO Hs. destruct Hs as [z P C k Δ0 Hss|z P C t d v t' P' Hin HkC Hp|z P C o 𝜆 t' k Λ HI Hv Ht Ha|z P C t t' HI].
  - by apply cs_ch.
  - apply cs_recv; [|done|done]. by apply HO.
  - by eapply cs_dual.
  - by apply cs_unfold.
Qed.

Lemma cstep_plain `{QM : QuantumModel} I O ρ c σ Δ :
  cstep I O ρ c σ Δ → plain c.1 → ∀ y, y ∈ Δ → plain y.1.1.
Proof.
  intros Hs Hpl.
  apply cstep_cases in Hs. inversion Hs as [z P C k Δ0 Hss|z P C t d v t' P' Hin HkC Hp|z P C t d v t' P' HI Hp
                  |z P C t U' qs t' HI|z P C t q t' HI|z P C t M qs t' HI|z P C t t' HI]; subst; simpl in *.
  - by intros y (x & -> & _)%list_elem_of_fmap.
  - by intros y ->%list_elem_of_singleton.
  - intros y ->%list_elem_of_singleton. by apply plain_app.
  - intros y ->%list_elem_of_singleton. by apply plain_app.
  - intros y ->%list_elem_of_singleton. by apply plain_app.
  - intros y (x & -> & _)%list_elem_of_fmap. by apply plain_app.
  - intros y ->%list_elem_of_singleton. by apply plain_app.
Qed.

Lemma outputs_agree `{QM : QuantumModel} I O O' S (D : dist comp) :
  (∀ z m, plain z → S z = false → (m ∈ O z ↔ m ∈ O' z)) → (∀ x, x ∈ D → plain x.1.1) →
  agree_on (dlts I O S) (dlts I O' S) D.
Proof.
  intros HO HD c ρ Hin. split; [done|]. intros Hns σ Δ. pose proof (HD _ Hin) as Hpl. simpl in Hpl, Hns.
  assert (HSc : S c.1 = false) by (destruct (S c.1) eqn:E; [by destruct Hns|done]).
  split; apply cstep_outputs; intros m Hm; by apply (HO c.1 m Hpl HSc).
Qed.

Lemma dinit_plain `{QM : QuantumModel} (p : prog * St) x : x ∈ dinit p → plain x.1.1.
Proof. intros ->%list_elem_of_singleton t c v Hin. by apply elem_of_nil in Hin. Qed.

Lemma smyth_outputs `{QM : QuantumModel} I O O' S (p q : prog * St) :
  (∀ z m, plain z → S z = false → (m ∈ O z ↔ m ∈ O' z)) →
  smyth_le (SchedSts0 := dlts I O S) Stay (dinit p) (dinit q) →
  smyth_le (SchedSts0 := dlts I O' S) Stay (dinit p) (dinit q).
Proof.
  intros HO Hle r2 Hr2.
  assert (HO' : ∀ z m, plain z → S z = false → (m ∈ O' z ↔ m ∈ O z)) by (intros z m Hn Hs; symmetry; by apply HO).
  pose proof (run_inv (dlts I O' S) (λ c : comp, plain c.1) (λ ρ c σ Δ Hc Hs, cstep_plain I O' ρ c σ Δ Hs Hc)
                _ r2 Hr2 (dinit_plain q)) as Hpl2.
  assert (Hr2' : is_run (SchedSts0 := dlts I O S) Stay (dinit q) r2).
  { apply (agree_run (dlts I O' S) (dlts I O S) Stay _ r2); [|done].
    intros n. apply outputs_agree; [done|]. intros x Hx. exact (Hpl2 n x Hx). }
  destruct (Hle r2 Hr2') as (r1 & Hr1 & Hrle).
  pose proof (run_inv (dlts I O S) (λ c : comp, plain c.1) (λ ρ c σ Δ Hc Hs, cstep_plain I O ρ c σ Δ Hs Hc)
                _ r1 Hr1 (dinit_plain p)) as Hpl1.
  exists r1. split; [|exact Hrle].
  apply (agree_run (dlts I O S) (dlts I O' S) Stay _ r1); [|done].
  intros n. apply outputs_agree; [done|]. intros x Hx. exact (Hpl1 n x Hx).
Qed.

Definition typed (K : tag → okind) (o : offer) : Prop := off_kind o = K (off_tag o).

Definition real_off `{QM : QuantumModel} (p q : prog * St) (Ch : channel → Prop) (K : tag → okind)
    (o : offer) : Prop :=
  typed K o ∧ off_tag o ∉ otags p.1 ∧ off_tag o ∉ otags q.1 ∧ ∀ t c, o = OffIn t c → ¬ Ch c.

Definition RealT `{QM : QuantumModel} (p q : prog * St) (O : node → list msg) (Ch : channel → Prop)
    (K : tag → okind) (I : node → offer → Prop) (S : node → bool) : Prop :=
  (∃ T, obs_for p q T ∧ (∀ z m, plain z → S z = false → (m ∈ O z ↔ m ∈ O_T T z)) ∧ I = menu T ∧ S = S_T T
        ∧ (∀ c, c ∈ out_chans T → Ch c) ∧ ∀ t x, (t, x) ∈ tagged T → K t = x)
  ∧ ∀ z o, I z o → real_off p q Ch K o.

Definition alt_free_obs `{QM : QuantumModel} (p q : prog * St) : Prop :=
  ∀ O Ch K, (∀ t, K t ≠ KRec) → malt_free_on (M := lq_menu O) (real_off p q Ch K) (RealT p q O Ch K) (dinit p) (dinit q).

Definition kinds_of (T : prog) (t : tag) : okind :=
  match find (λ x, bool_decide (x.1 = t)) (tagged T) with Some x => x.2 | None => KOut end.

Lemma kinds_of_tagged `{QM : QuantumModel} T t x : observer T → (t, x) ∈ tagged T → kinds_of T t = x.
Proof.
  intros HT Hin. unfold kinds_of.
  destruct (find (λ y, bool_decide (y.1 = t)) (tagged T)) as [y|] eqn:E.
  - apply find_some in E as [Hy Hk]. apply bool_decide_eq_true in Hk. destruct y as [t' x']. simpl in *. subst t'.
    apply (proj1 (proj2 HT) t); [by apply list_elem_of_In|exact Hin].
  - exfalso. pose proof (find_none _ _ E (t, x) (proj1 (list_elem_of_In _ _) Hin)) as Hf.
    simpl in Hf. by rewrite bool_decide_eq_false in Hf.
Qed.

Lemma tagged_norec T t : obsb T = true → (t, KRec) ∉ tagged T
with gtagged_norec g t : gobsb g = true → (t, KRec) ∉ gtagged g.
Proof.
  - destruct T; simpl; intros Hob Hin.
    + apply list_elem_of_singleton in Hin. discriminate Hin.
    + apply andb_prop in Hob as [H1 H2]. apply elem_of_app in Hin as [Hin|Hin];
        [exact (tagged_norec _ _ H1 Hin)|exact (tagged_norec _ _ H2 Hin)].
    + apply andb_prop in Hob as [H1 H2]. apply elem_of_app in Hin as [Hin|Hin];
        [exact (tagged_norec _ _ H1 Hin)|exact (tagged_norec _ _ H2 Hin)].
    + discriminate Hob.
    + discriminate Hob.
    + discriminate Hob.
    + exact (gtagged_norec _ _ Hob Hin).
  - destruct g; simpl; intros Hob Hin.
    + by apply elem_of_nil in Hin.
    + by apply elem_of_nil in Hin.
    + apply elem_of_cons in Hin as [Hin|Hin]; [destruct π; discriminate Hin|].
      destruct π; try discriminate Hob; exact (tagged_norec _ _ Hob Hin).
    + apply andb_prop in Hob as [[H1 H2]%andb_prop _]. apply elem_of_app in Hin as [Hin|Hin];
        [exact (gtagged_norec _ _ H1 Hin)|exact (gtagged_norec _ _ H2 Hin)].
Qed.

Lemma kinds_of_norec T t : obsb T = true → kinds_of T t ≠ KRec.
Proof.
  intros Hob. unfold kinds_of. destruct (find (λ y, bool_decide (y.1 = t)) (tagged T)) as [[t' x]|] eqn:E; [|done].
  apply find_some in E as [Hy _]. simpl. intros ->. exact (tagged_norec T t' Hob (proj2 (list_elem_of_In _ _) Hy)).
Qed.

Lemma menu_typed `{QM : QuantumModel} T z o : observer T → menu T z o → typed (kinds_of T) o.
Proof.
  intros HT Hm. unfold typed. symmetry. apply (kinds_of_tagged T _ _ HT). exact (menu_kind T HT z o Hm).
Qed.

Lemma tnodes_chans T : obs T → ∀ z T', T' ∈ tnodes T z →
  (∀ c, c ∈ out_chans T' → c ∈ out_chans T) ∧ (∀ c, c ∈ in_chans T' → c ∈ in_chans T).
Proof.
  intros HT z. induction z as [|a z IH] using rev_ind; intros T' Hin.
  - rewrite tnodes_nil in Hin. apply list_elem_of_singleton in Hin. subst. split; intros c Hc; exact Hc.
  - apply tnodes_app_elem in Hin as (T0 & HT0 & Hin). destruct (IH T0 HT0) as [Ho Hi].
    destruct (prog_step_chans_sub T0 _ _ T' (proj1 (tnodes_obs T HT z T0 HT0)) (co_succ_sound T0 a T' (proj1 (tnodes_obs T HT z T0 HT0)) Hin)) as [Ho0 Hi0].
    split; intros c Hc; [exact (Ho c (Ho0 c Hc))|exact (Hi c (Hi0 c Hc))].
Qed.

Lemma menu_real `{QM : QuantumModel} (p q : prog * St) T z o :
  obs_for p q T → menu T z o → real_off p q (λ c, c ∈ out_chans T) (kinds_of T) o.
Proof.
  intros [HT Hpq] Hm. split; [exact (menu_typed T z o HT Hm)|].
  assert (Ht : off_tag o ∈ tags T).
  { unfold tags. apply list_elem_of_fmap. exists (off_tag o, off_kind o). split; [done|]. exact (menu_kind T HT z o Hm). }
  destruct (Hpq _ Ht) as [Htp Htq]. split; [exact Htp|]. split; [exact Htq|].
  intros t c -> Hc1.
  destruct Hm as (T' & a & HT' & Ha & Hne). destruct a as [|t' c' v| | | |]; try discriminate Ha.
  simpl in Ha. injection Ha as -> ->.
  destruct (co_succ T' (CoIn t c v)) as [|T'' l] eqn:E; [done|].
  assert (HT'' : T'' ∈ co_succ T' (CoIn t c v)) by (rewrite E; by left).
  pose proof (prog_step_in_chan T' t c v T'' (proj1 (tnodes_obs T (proj1 HT) z T' HT')) (co_succ_sound _ _ _ (proj1 (tnodes_obs T (proj1 HT) z T' HT')) HT'')) as Hc.
  exact (proj2 (proj1 HT) c Hc1 (proj2 (tnodes_chans T (proj1 HT) z T' HT') c Hc)).
Qed.

Lemma alt_pre_obs_menu `{QM : QuantumModel} (p q : prog * St) :
  alt_pre_obs Stay p q ↔ ∀ O Ch K, (∀ t, K t ≠ KRec) → malt_pre_on (M := lq_menu O) (RealT p q O Ch K) (dinit p) (dinit q).
Proof.
  split.
  - intros Hp O Ch K _ I S ((T & HT & HO & -> & -> & _) & _).
    exact (smyth_outputs (menu T) (O_T T) O (S_T T) p q (λ z m Hn Hs, iff_sym (HO z m Hn Hs)) (Hp T HT)).
  - intros Hp T HT. refine (Hp (O_T T) (λ c, c ∈ out_chans T) (kinds_of T) (λ t, kinds_of_norec T t (proj1 (proj1 (proj1 HT)))) (menu T) (S_T T) _).
    split; [|intros z o Hm; exact (menu_real p q T z o HT Hm)].
    exists T. split; [done|]. split; [done|]. split; [done|]. split; [done|]. split; [done|].
    intros t x Hin. exact (kinds_of_tagged T t x (proj1 HT) Hin).
Qed.

Theorem alt_free_obs_sound `{QM : QuantumModel} (DC : dep_choice) (p q : prog * St) :
  q.2 ≠ szero →
  alt_free_obs p q → ctx_pre_sm_on Stay (obs_for p q) p q.
Proof.
  intros Hz Hf. apply (alt_pre_obs_iff Stay DC p q), alt_pre_obs_menu. intros O Ch K HKr.
  apply (malt_free_on_sound (M := lq_menu O) (real_off p q Ch K) _ (λ I S HR, proj2 HR) DC); [| |by apply Hf].
  - intros x ->%list_elem_of_singleton. done.
  - intros x ->%list_elem_of_singleton. exact Hz.
Qed.

Theorem alt_free_obs_complete `{QM : QuantumModel} (DC : dep_choice) (p q : prog * St) :
    (∀ O Ch K, (∀ t, K t ≠ KRec) → MenuReal (M := lq_menu O) (real_off p q Ch K) (RealT p q O Ch K) (dinit p) (dinit q)) →
  ctx_pre_sm_on Stay (obs_for p q) p q → alt_free_obs p q.
Proof.
  intros HM Hc O Ch K HKr. apply (malt_free_on_complete (M := lq_menu O)); [by apply HM|].
  apply (proj1 (alt_pre_obs_menu p q)); [exact (proj2 (alt_pre_obs_iff Stay DC p q) Hc)|exact HKr].
Qed.

End Canonical.

Notation comp := (node * (prog * list msg))%type (only parsing).

(* end hide *)
