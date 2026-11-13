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
From stdpp Require Import base countable decidable list.
From TestingTheory Require Import ActTau pMust_almost_sure pMust_smyth pMust_transfer pMust_canonical.
From TestingTheory Require Import lqCCS.Language.Algebra lqCCS.Language.Quantum lqCCS.Language.Quantum_Weights.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.LTS lqCCS.Testing.Scheduled lqCCS.Testing.DistLTS lqCCS.Testing.Programs lqCCS.Testing.Observers lqCCS.Testing.Smyth_Soundness.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

Section Mass.
  Context `{QM : QuantumModel}.

  Lemma tr_outs_nz M qs ρ :
    foldr (λ k acc, W_add (tr (meas_branch M qs k ρ)) acc) W_zero (outs_nz M qs ρ) = tr ρ.
  Proof.
    rewrite <- (meas_tr M qs ρ), br_sum.
    fold (sum (map (λ k, one ⋅ kraus (meas_of M qs) k) (outs (meas_of M qs)))).
    rewrite app_ssum, tr_ssum, !map_map. unfold outs_nz.
    generalize (outs (meas_of M qs)) as l. intros l.
    induction l as [|k l IH]; [done|]. simpl. rewrite filter_cons. rewrite comp_1l.
    case_decide as Hk; simpl.
    - by rewrite IH.
    - unfold meas_branch in Hk. rewrite Hk, tr_szero, W_add_zero. exact IH.
  Qed.

  Lemma dmass_one {C} (x : C * weight) : dmass [x] = tr x.2.
  Proof. apply W_add_zero_r. Qed.

  Lemma dmass_cons {C} (x : C * weight) (A : dist C) : dmass (x :: A) = W_add (tr x.2) (dmass A).
  Proof. done. Qed.

  Lemma sched_step_mass ρ R s Δ : sched_step ρ R s Δ → dmass Δ = tr ρ.
  Proof.
    inversion 1 as [? Hp|E qs ? Hp|qs ? Hp|M qs Rs R0 Hp0 Hf]; subst.
    - apply dmass_one.
    - rewrite dmass_one. apply sop_tr.
    - rewrite dmass_one. apply init_tr.
    - rewrite <- (tr_outs_nz M qs ρ). clear -Hf. induction Hf as [|k R1 ks Rs _ _ IH]; [done|].
      change (dmass ((R1, meas_branch M qs k ρ) :: zip_with (λ k R', (R', meas_branch M qs k ρ)) ks Rs)
        = W_add (tr (meas_branch M qs k ρ)) (foldr (λ k acc, W_add (tr (meas_branch M qs k ρ)) acc) W_zero ks)).
      by rewrite dmass_cons, IH.
  Qed.

  Lemma dmass_map_snd {A B} (f : A → B) (Δ : dist A) :
    dmass (map (λ x, (f x.1, x.2)) Δ) = dmass Δ.
  Proof. induction Δ as [|x Δ IH]; [done|]. by rewrite map_cons, !dmass_cons, IH. Qed.

  Lemma cstep_mass I O ρ c it Δ : cstep I O ρ c it Δ → dmass Δ = tr ρ.
  Proof.
    inversion 1 as [n P C E s Δ0 Hs| | | | |n P C E k M qs t HI]; subst.
    - rewrite <- (sched_step_mass _ _ _ _ Hs). exact (dmass_map_snd (λ P', (n, (P', C, E))) Δ0).
    - apply dmass_one.
    - apply dmass_one.
    - rewrite dmass_one. apply sop_tr.
    - rewrite dmass_one. apply init_tr.
    - rewrite <- (tr_outs_nz M qs ρ). generalize (outs_nz M qs ρ) as ks. intros ks.
      induction ks as [|k' ks IH]; [done|]. by rewrite map_cons, dmass_cons, IH.
  Qed.

  Lemma cstep_ich J O ρ c s Δ :
    cstep J O ρ c (ICh s) Δ → (∀ J', cstep J' O ρ c (ICh s) Δ) ∧ ∀ y, y ∈ Δ → y.1.1 = c.1.
  Proof.
    inversion 1; subst; split.
    - intros J'. by constructor.
    - intros y (x & -> & _)%list_elem_of_fmap. done.
    - intros J'. by econstructor.
    - intros y ->%list_elem_of_singleton. done.
  Qed.

  Lemma cstep_off J O ρ c k t Δ :
    cstep J O ρ c (IOff k t) Δ →
    ∃ o, J c.1 o ∧ (∀ J', J' c.1 o → cstep J' O ρ c (IOff k t) Δ) ∧ ∀ y, y ∈ Δ → ∃ a, offer_of a = o ∧ y.1.1 = c.1 ++ [a].
  Proof.
    inversion 1 as [| |n P C E k' d v t' P' HI Hp|n P C E k' E' qs t' HI|n P C E k' qs t' HI|n P C E k' M qs t' HI]; subst.
    - exists (OffIn k d). split; [done|]. split; [intros J' HJ'; by apply cs_in|].
      intros y ->%list_elem_of_singleton. by exists (CoIn k d v).
    - exists (OffOp k E' qs). split; [done|]. split; [intros J' HJ'; by apply cs_op|].
      intros y ->%list_elem_of_singleton. by exists (CoOp k E' qs).
    - exists (OffInit k qs). split; [done|]. split; [intros J' HJ'; by apply cs_init|].
      intros y ->%list_elem_of_singleton. by exists (CoInit k qs).
    - exists (OffMeas k M qs). split; [done|]. split; [intros J' HJ'; by apply cs_meas|].
      intros y (k'' & -> & _)%list_elem_of_fmap. by exists (CoMeas k M qs (code _ k'')).
  Qed.

  Lemma cstep_nonempty J O ρ c it Δ : ρ ≠ szero → cstep J O ρ c it Δ → Δ ≠ [].
  Proof.
    intros Hρ. inversion 1 as [n P C E s Δ0 Hs| | | | |n P C E k M qs t HI]; subst; try done.
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

Notation comp := (node * (proc * list msg * list msg))%type (only parsing).

Definition lq_menu `{QM : QuantumModel} (O : node → list msg) : MenuSts comp item coact offer.
Proof.
  refine {| mnode := λ c : comp, c.1; moffer := offer_of; mstep := λ J ρ c σ Δ, cstep J O ρ c σ Δ;
            mfree := λ σ, match σ with ICh _ => True | IOff _ _ => False end; msch := IOff 0 0 |}.
  - intros J ρ c [s|k t] Δ Hf Hc; [exact (cstep_ich _ _ _ _ _ _ Hc)|done].
  - intros J ρ c [s|k t] Δ Hf Hc; [done|exact (cstep_off _ _ _ _ _ _ _ Hc)].
  - intros J ρ c σ Δ Hc. exact (cstep_mass _ _ _ _ _ _ Hc).
  - intros J ρ c σ Δ Hρ Hc. exact (cstep_nonempty _ _ _ _ _ _ Hρ Hc).
  - intros J ρ c σ Δ Hρ Hc. exact (cstep_nonzero _ _ _ _ _ _ Hρ Hc).
Defined.

Definition alt_free `{QM : QuantumModel} (p q : proc * St) : Prop :=
  ∀ O, malt_free (M := lq_menu O) (λ _, True) (dinit O p) (dinit O q).

Lemma alt_pre_menu `{QM : QuantumModel} (p q : proc * St) :
  alt_pre Stay p q ↔ ∀ O, malt_pre (M := lq_menu O) (λ _, True) (dinit O p) (dinit O q).
Proof.
  split.
  - intros Hp O I S _ HS. exact (Hp I O S HS).
  - intros Hp I O S HS. exact (Hp O I S (λ _ _ _, Logic.I) HS).
Qed.

Theorem alt_free_iff `{QM : QuantumModel} (DC : dep_choice) (p q : proc * St) :
  q.2 ≠ szero → alt_free p q ↔ alt_pre Stay p q.
Proof.
  intros Hq. rewrite alt_pre_menu. unfold alt_free. split; intros Hp O.
  - apply (malt_free_iff (M := lq_menu O) _ DC); [| |apply Hp].
    + intros x ->%list_elem_of_singleton. done.
    + intros x ->%list_elem_of_singleton. exact Hq.
  - apply (malt_free_iff (M := lq_menu O) _ DC); [| |apply Hp].
    + intros x ->%list_elem_of_singleton. done.
    + intros x ->%list_elem_of_singleton. exact Hq.
Qed.

Lemma single_op_item `{QM : QuantumModel} O n k E0 qs ρ c it Δ :
  cstep (single n (OffOp k E0 qs)) O ρ c it Δ →
  (∀ J, cstep J O ρ c it Δ) ∨ ∃ t, it = IOff k t.
Proof.
  inversion 1 as [? ? ? ? s Δ0 Hs|? ? ? ? k' d v t P' HE HkC Hp|? ? ? ? k' d v t P' HI Hp|? ? ? ? k' E' qs' t HI|? ? ? ? k' qs' t HI|? ? ? ? k' M qs' t HI]; subst.
  - left. intros J. by constructor.
  - left. intros J. by econstructor.
  - destruct HI as [_ Ho]. discriminate Ho.
  - destruct HI as [_ Ho]. injection Ho as -> _ _. right. by exists t.
  - destruct HI as [_ Ho]. discriminate Ho.
  - destruct HI as [_ Ho]. discriminate Ho.
Qed.

Theorem convergence `{QM : QuantumModel} (p q : proc * St) O S I r w k :
  alt_pre Stay p q → ext_closed S → run_word (M := lq_menu O) I S (dinit O q) r w →
  (∀ i, ¬ dstable (SchedSts0 := dlts I O S) (r i)) → (∀ i t, w i ≠ IOff k t) →
  ∃ r', is_run (SchedSts0 := mdlts (M := lq_menu O) (Jstar (M := lq_menu O) (λ _, True) I S r w) (Sstar (M := lq_menu O) (λ _, True) I S r w)) Stay (dinit O p) r'
    ∧ ((∀ i, ¬ dstable (SchedSts0 := mdlts (M := lq_menu O) (Jstar (M := lq_menu O) (λ _, True) I S r w) (Sstar (M := lq_menu O) (λ _, True) I S r w)) (r' i))
       ∨ ∀ v, prob_lt v (tr p.2) → ∃ m, prob_le v (succ_mass (SchedSts0 := dlts I O S) r m)).
Proof.
  intros Hpre HS Hw Hdiv Hfresh.
  assert (Hq0 : ∀ x, x ∈ dinit O q → mnode (MenuSts := lq_menu O) x.1 = []).
  { intros x Hx. apply list_elem_of_singleton in Hx. by subst x. }
  assert (Hen : ∀ J (c : comp) ρ, J (mnode (MenuSts := lq_menu O) c) (OffOp k 0 []) → ∃ σ Δ, mstep (MenuSts := lq_menu O) J ρ c σ Δ).
  { intros J [n [[P C] E0]] ρ HJ. eexists (IOff k 0), _. exact (cs_op _ _ ρ n P C E0 k 0 [] 0 HJ). }
  assert (Hf : ∀ n i ρ (c : comp) Δ, mstep (MenuSts := lq_menu O) (single n (OffOp k 0 [])) ρ c (w i) Δ → ∀ J', mstep (MenuSts := lq_menu O) J' ρ c (w i) Δ).
  { intros n i ρ c Δ Hc. destruct (single_op_item _ _ _ _ _ _ _ _ _ Hc) as [Hall|(t & Ht)]; [exact Hall|].
    exfalso. exact (Hfresh i t Ht). }
  destruct (mconvergence (M := lq_menu O) _ (dinit O p) (dinit O q) (proj1 (alt_pre_menu p q) Hpre O)
    Hq0 S HS I r w (OffOp k 0 []) (λ _ _ _, Logic.I) Logic.I Hw Hdiv Hen Hf) as (r' & Hr' & Hc).
  exists r'. split; [done|]. destruct Hc as [Hc|Hc]; [by left|right]. intros v Hv. apply Hc.
  assert (E : dmass (dinit O p) = tr p.2) by exact (dmass_one (([], (p.1, [], O [])), p.2)).
  rewrite E. exact Hv.
Qed.

Definition plain (n : node) : Prop := ∀ k c v, CoOut k c v ∉ n.

Lemma plain_app n a : plain n → (∀ k c v, a ≠ CoOut k c v) → plain (n ++ [a]).
Proof.
  intros Hn Ha k c v Hin. apply elem_of_app in Hin as [Hin|Hin]; [exact (Hn k c v Hin)|].
  apply list_elem_of_singleton in Hin. exact (Ha k c v (eq_sym Hin)).
Qed.

Definition reO (O' : node → list msg) (c : comp) : comp := (c.1, (c.2.1.1, c.2.1.2, O' c.1)).

Lemma cstep_reO `{QM : QuantumModel} I O O' ρ c σ Δ :
  (∀ m, m ∈ O c.1 → m ∈ O' c.1) → plain c.1 → c.2.2 = O c.1 → cstep I O ρ c σ Δ →
  cstep I O' ρ (reO O' c) σ (map (λ x, (reO O' x.1, x.2)) Δ)
  ∧ ∀ y, y ∈ Δ → plain y.1.1 ∧ y.1.2.2 = O y.1.1.
Proof.
  intros HO Hpl HE Hs.
  inversion Hs as [n P C E s Δ0 Hss|n P C E k d v t P' Hin HkC Hp|n P C E k d v t P' HI Hp
                  |n P C E k E' qs t HI|n P C E k qs t HI|n P C E k M qs t HI]; subst; unfold reO; simpl in *.
  - split.
    + rewrite map_map. exact (cs_ch I O' ρ n P C (O' n) s Δ0 Hss).
    + intros y (x & -> & _)%list_elem_of_fmap. by split.
  - split.
    + apply cs_recv; [|done|done]. apply HO. by rewrite <- HE.
    + intros y ->%list_elem_of_singleton. by split.
  - split; [by apply cs_in|]. intros y ->%list_elem_of_singleton. split; [|done]. by apply plain_app.
  - split; [by apply cs_op|]. intros y ->%list_elem_of_singleton. split; [|done]. by apply plain_app.
  - split; [by apply cs_init|]. intros y ->%list_elem_of_singleton. split; [|done]. by apply plain_app.
  - split.
    + rewrite map_map. exact (cs_meas I O' ρ n P C (O' n) k M qs t HI).
    + intros y (x & -> & _)%list_elem_of_fmap. split; [|done]. by apply plain_app.
Qed.

Lemma smyth_reO `{QM : QuantumModel} I O O' S (p q : proc * St) :
  (∀ n m, plain n → S n = false → (m ∈ O n ↔ m ∈ O' n)) →
  smyth_le (SchedSts0 := dlts I O S) Stay (dinit O p) (dinit O q) →
  smyth_le (SchedSts0 := dlts I O' S) Stay (dinit O' p) (dinit O' q).
Proof.
  intros HO Hle.
  assert (Hres : smyth_le (SchedSts0 := dlts I O' S) Stay
            (map (λ x, (reO O' x.1, x.2)) (dinit O p)) (map (λ x, (reO O' x.1, x.2)) (dinit O q))).
  { apply (morph_smyth (dlts I O S) (dlts I O' S) (reO O') (reO O)
             (λ c, plain c.1 ∧ c.2.2 = O c.1) (λ c, plain c.1 ∧ c.2.2 = O' c.1)); [| | | | | | | | |exact Hle].
    - intros c. split; intros Hc; exact Hc.
    - intros ρ c σ Δ [Hpl HE] Hns Hs.
      assert (HSc : S c.1 = false) by (destruct (S c.1) eqn:E; [by destruct Hns|done]).
      exact (cstep_reO I O O' ρ c σ Δ (λ m Hm, proj1 (HO c.1 m Hpl HSc) Hm) Hpl HE Hs).
    - intros ρ [n [[P C] E]] σ Δ' [Hpl HE] Hns Hs. simpl in *. subst E.
      assert (HSc : S n = false) by (destruct (S n) eqn:E; [by destruct Hns|done]).
      destruct (cstep_reO I O' O ρ (reO O' (n, (P, C, O n))) σ Δ' (λ m Hm, proj2 (HO n m Hpl HSc) Hm) Hpl eq_refl Hs) as [Hs' _].
      eexists. exact Hs'.
    - intros c. split; intros Hc; exact Hc.
    - intros ρ c σ Δ [Hpl HE] Hns Hs.
      assert (HSc : S c.1 = false) by (destruct (S c.1) eqn:E; [by destruct Hns|done]).
      exact (cstep_reO I O' O ρ c σ Δ (λ m Hm, proj2 (HO c.1 m Hpl HSc) Hm) Hpl HE Hs).
    - intros ρ [n [[P C] E]] σ Δ' [Hpl HE] Hns Hs. simpl in *. subst E.
      assert (HSc : S n = false) by (destruct (S n) eqn:E; [by destruct Hns|done]).
      destruct (cstep_reO I O O' ρ (reO O (n, (P, C, O' n))) σ Δ' (λ m Hm, proj1 (HO n m Hpl HSc) Hm) Hpl eq_refl Hs) as [Hs' _].
      eexists. exact Hs'.
    - intros x ->%list_elem_of_singleton. split; [|done]. intros k c v Hin. by apply elem_of_nil in Hin.
    - intros x Hx. change (x ∈ [(([], (q.1, [], O' [])), q.2)]) in Hx. apply list_elem_of_singleton in Hx.
      subst x. split; [|done]. intros k c v Hin. by apply elem_of_nil in Hin.
    - done. }
  exact Hres.
Qed.

Definition typed (K : tag → okind) (o : offer) : Prop := off_kind o = K (off_tag o).

Definition real_off `{QM : QuantumModel} (p q : proc * St) (Ch : channel → Prop) (K : tag → okind)
    (o : offer) : Prop :=
  typed K o ∧ off_tag o ∉ tags p.1 ∧ off_tag o ∉ tags q.1 ∧ ∀ k c, o = OffIn k c → ¬ Ch c.

Definition RealT `{QM : QuantumModel} (p q : proc * St) (O : node → list msg) (Ch : channel → Prop)
    (K : tag → okind) (I : node → offer → Prop) (S : node → bool) : Prop :=
  (∃ T, obs_for p q T ∧ (∀ n m, plain n → S n = false → (m ∈ O n ↔ m ∈ O_T T n)) ∧ I = menu T ∧ S = S_T T
        ∧ (∀ c, c ∈ out_chans T → Ch c) ∧ ∀ k x, (k, x) ∈ tagged T → K k = x)
  ∧ ∀ n o, I n o → real_off p q Ch K o.

Definition alt_free_obs `{QM : QuantumModel} (p q : proc * St) : Prop :=
  ∀ O Ch K, malt_free_on (M := lq_menu O) (real_off p q Ch K) (RealT p q O Ch K) (dinit O p) (dinit O q).

Definition kinds_of (T : proc) (k : tag) : okind :=
  match find (λ x, bool_decide (x.1 = k)) (tagged T) with Some x => x.2 | None => KOut end.

Lemma kinds_of_tagged `{QM : QuantumModel} T k x : observer T → (k, x) ∈ tagged T → kinds_of T k = x.
Proof.
  intros HT Hin. unfold kinds_of.
  destruct (find (λ y, bool_decide (y.1 = k)) (tagged T)) as [y|] eqn:E.
  - apply find_some in E as [Hy Hk]. apply bool_decide_eq_true in Hk. destruct y as [k' x']. simpl in *. subst k'.
    apply (proj1 (proj2 HT) k); [by apply list_elem_of_In|exact Hin].
  - exfalso. pose proof (find_none _ _ E (k, x) (proj1 (list_elem_of_In _ _) Hin)) as Hf.
    simpl in Hf. by rewrite bool_decide_eq_false in Hf.
Qed.

Lemma menu_typed `{QM : QuantumModel} T n o : observer T → menu T n o → typed (kinds_of T) o.
Proof.
  intros HT Hm. unfold typed. symmetry. apply (kinds_of_tagged T _ _ HT). exact (menu_kind T HT n o Hm).
Qed.

Lemma tnodes_chans T : obs T → ∀ n T', T' ∈ tnodes T n →
  (∀ c, c ∈ out_chans T' → c ∈ out_chans T) ∧ (∀ c, c ∈ in_chans T' → c ∈ in_chans T).
Proof.
  intros HT n. induction n as [|a n IH] using rev_ind; intros T' Hin.
  - rewrite tnodes_nil in Hin. apply list_elem_of_singleton in Hin. subst. split; intros c Hc; exact Hc.
  - apply tnodes_app_elem in Hin as (T0 & HT0 & Hin). destruct (IH T0 HT0) as [Ho Hi].
    destruct (prog_step_chans_sub T0 _ _ T' (proj1 (tnodes_obs T HT n T0 HT0)) (co_succ_sound T0 a T' Hin)) as [Ho0 Hi0].
    split; intros c Hc; [exact (Ho c (Ho0 c Hc))|exact (Hi c (Hi0 c Hc))].
Qed.

Lemma menu_real `{QM : QuantumModel} (p q : proc * St) T n o :
  obs_for p q T → menu T n o → real_off p q (λ c, c ∈ out_chans T) (kinds_of T) o.
Proof.
  intros [HT Hpq] Hm. split; [exact (menu_typed T n o HT Hm)|].
  assert (Ht : off_tag o ∈ tags T).
  { unfold tags. apply list_elem_of_fmap. exists (off_tag o, off_kind o). split; [done|]. exact (menu_kind T HT n o Hm). }
  destruct (Hpq _ Ht) as [Htp Htq]. split; [exact Htp|]. split; [exact Htq|].
  intros k c -> Hc1.
  destruct Hm as (T' & a & HT' & Ha & Hne). destruct a as [|k' c' v| | |]; try discriminate Ha.
  simpl in Ha. injection Ha as -> ->.
  destruct (co_succ T' (CoIn k c v)) as [|T'' l] eqn:E; [done|].
  assert (HT'' : T'' ∈ co_succ T' (CoIn k c v)) by (rewrite E; by left).
  pose proof (prog_step_in_chan T' k c v T'' (proj1 (tnodes_obs T (proj1 HT) n T' HT')) (co_succ_sound _ _ _ HT'')) as Hc.
  exact (proj2 (proj1 HT) c Hc1 (proj2 (tnodes_chans T (proj1 HT) n T' HT') c Hc)).
Qed.

Lemma alt_pre_obs_menu `{QM : QuantumModel} (p q : proc * St) :
  alt_pre_obs Stay p q ↔ ∀ O Ch K, malt_pre_on (M := lq_menu O) (RealT p q O Ch K) (dinit O p) (dinit O q).
Proof.
  split.
  - intros Hp O Ch K I S ((T & HT & HO & -> & -> & _) & _).
    exact (smyth_reO (menu T) (O_T T) O (S_T T) p q (λ n m Hn Hs, iff_sym (HO n m Hn Hs)) (Hp T HT)).
  - intros Hp T HT. refine (Hp (O_T T) (λ c, c ∈ out_chans T) (kinds_of T) (menu T) (S_T T) _).
    split; [|intros n o Hm; exact (menu_real p q T n o HT Hm)].
    exists T. split; [done|]. split; [done|]. split; [done|]. split; [done|]. split; [done|].
    intros k x Hin. exact (kinds_of_tagged T k x (proj1 HT) Hin).
Qed.

Theorem alt_free_obs_sound `{QM : QuantumModel} (DC : dep_choice) (p q : proc * St) :
  q.2 ≠ szero →
  alt_free_obs p q → ctx_pre_sm_on Stay (obs_for p q) p q.
Proof.
  intros Hz Hf. apply (alt_pre_obs_iff Stay DC p q), alt_pre_obs_menu. intros O Ch K.
  apply (malt_free_on_sound (M := lq_menu O) (real_off p q Ch K) _ (λ I S HR, proj2 HR) DC); [| |apply Hf].
  - intros x ->%list_elem_of_singleton. done.
  - intros x ->%list_elem_of_singleton. exact Hz.
Qed.

Theorem alt_free_obs_complete `{QM : QuantumModel} (DC : dep_choice) (p q : proc * St) :
    (∀ O Ch K, MenuReal (M := lq_menu O) (real_off p q Ch K) (RealT p q O Ch K) (dinit O p) (dinit O q)) →
  ctx_pre_sm_on Stay (obs_for p q) p q → alt_free_obs p q.
Proof.
  intros HM Hc O Ch K. apply (malt_free_on_complete (M := lq_menu O)); [apply HM|].
  apply (proj1 (alt_pre_obs_menu p q)). exact (proj2 (alt_pre_obs_iff Stay DC p q) Hc).
Qed.
(* end hide *)
