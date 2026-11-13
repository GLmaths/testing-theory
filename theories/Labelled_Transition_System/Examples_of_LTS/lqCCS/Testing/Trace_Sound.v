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
From Stdlib.Bool Require Import Bool.
From Stdlib.Logic Require Import Classical ClassicalDescription.
From Stdlib Require Import Lia.
Import ListNotations.
From stdpp Require Import base countable decidable list.
From TestingTheory Require Import ActTau pMust_scheduled pMust_almost_sure pMust_smyth pMust_transfer pMust_canonical.
From TestingTheory Require Import lqCCS.Language.Algebra lqCCS.Language.Quantum lqCCS.Language.Quantum_Weights.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.LTS lqCCS.Testing.Scheduled lqCCS.Testing.DistLTS lqCCS.Testing.Programs lqCCS.Testing.Observers lqCCS.Testing.Smyth_Soundness lqCCS.Testing.Canonical lqCCS.Testing.Pull lqCCS.Testing.Head lqCCS.Testing.Modes lqCCS.Testing.Syn lqCCS.Testing.Assembly lqCCS.Testing.Final lqCCS.Testing.Trace lqCCS.Testing.Build lqCCS.Testing.Trace_Complete.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

Lemma co_succ_out_same T k c v c' v' T1 :
  T1 ∈ co_succ T (CoOut k c v) → co_succ T (CoOut k c' v') ≠ [] → (c, v) ≠ (c', v') →
  co_succ T1 (CoOut k c' v') ≠ [].
Proof.
  revert T1. induction T as [t c0 e|e P IHP Q IHQ|P IHP Q IHQ|P IH|X|t X P IH|g]; simpl; intros T1 H1 Hb Hne.
  - repeat case_decide; try (by apply elem_of_nil in H1); try done. exfalso. apply Hne.
    repeat match goal with Hx : _ ∧ _ |- _ => destruct Hx end. congruence.
  - destruct (eval e) as [[[]| |]|]; try (by apply elem_of_nil in H1); eauto.
  - apply elem_of_app in H1 as [(P1 & -> & H1)%list_elem_of_fmap|(Q1 & -> & H1)%list_elem_of_fmap]; simpl;
      intros Hnil; apply app_eq_nil in Hnil as [N1 N2]; apply fmap_nil_inv in N1, N2.
    + apply (IHP P1 H1); [|done|done]. intros EP. apply Hb. by rewrite EP, N2.
    + apply (IHQ Q1 H1); [|done|done]. intros EQ. apply Hb. by rewrite N1, EQ.
  - by apply elem_of_nil in H1.
  - by apply elem_of_nil in H1.
  - by apply elem_of_nil in H1.
  - rewrite gco_out in H1. by apply elem_of_nil in H1.
Qed.

Lemma O_T_fun T n k c v c' v' :
  observer T → (k, c, v) ∈ O_T T n → (k, c', v') ∈ O_T T n → c = c' ∧ v = v'.
Proof.
  intros HT (X & HX & Hne)%O_T_spec (X' & HX' & Hne')%O_T_spec.
  rewrite (tnodes_unique T n X' X HT HX' HX) in Hne'.
  destruct (decide ((c, v) = (c', v'))) as [[= -> ->]|Hd]; [done|]. exfalso.
  destruct (co_succ X (CoOut k c v)) as [|X1 l] eqn:E1; [done|].
  assert (H1 : X1 ∈ co_succ X (CoOut k c v)) by (rewrite E1; by left).
  apply (co_succ_out_same X k c v c' v' X1 H1 Hne' Hd).
  apply (proj2 (proj2 (proj2 HT)) n [] k c v c' v' X1). rewrite app_nil_r. apply tnodes_app_elem. by exists X.
Qed.

Lemma O_T_mono T n a m :
  observer T → (∀ k c v, a ≠ CoOut k c v) → tnodes T (n ++ [a]) ≠ [] → m ∈ O_T T n → m ∈ O_T T (n ++ [a]).
Proof.
  destruct m as [[k c] v]. intros HT Ha Hne (X & HX & Hout)%O_T_spec.
  destruct (tnodes T (n ++ [a])) as [|Y l] eqn:Et; [done|].
  assert (HY : Y ∈ tnodes T (n ++ [a])) by (rewrite Et; by left). pose proof HY as HY0.
  apply tnodes_app_elem in HY as (X0 & HX0 & HYa). rewrite (tnodes_unique T n X0 X HT HX0 HX) in HYa.
  destruct (co_succ X (CoOut k c v)) as [|X1 l1] eqn:E1; [done|].
  assert (H1 : X1 ∈ co_succ X (CoOut k c v)) by (rewrite E1; by left).
  assert (Hb : co_succ X1 a ≠ []).
  { apply (co_succ_out_keep X k c v a X1 H1); [|intros c' v'; apply Ha].
    intros E. rewrite E in HYa. by apply elem_of_nil in HYa. }
  destruct (co_succ X1 a) as [|X2 l2] eqn:E2; [done|].
  assert (H2 : X2 ∈ co_succ X1 a) by (rewrite E2; by left).
  destruct (co_succ_out_swap X k c v a X1 X2 H1 H2) as (Y' & HY' & H3).
  assert (HYn : Y' ∈ tnodes T (n ++ [a])) by (apply tnodes_app_elem; by exists X).
  rewrite (tnodes_unique T _ Y' Y HT HYn HY0) in H3.
  apply O_T_spec. exists Y. split; [done|]. intros En. rewrite En in H3. by apply elem_of_nil in H3.
Qed.

Lemma dsum_elem {A B} (R : A → list B → Prop) (D : list A) (Δs : list (list B)) x :
  Forall2 R D Δs → x ∈ concat Δs → ∃ y Δ, y ∈ D ∧ Δ ∈ Δs ∧ R y Δ ∧ x ∈ Δ.
Proof.
  induction 1 as [|y Δ D Δs Hy _ IH]; simpl; intros Hx; [by apply elem_of_nil in Hx|].
  apply elem_of_app in Hx as [Hx|Hx].
  - exists y, Δ. split; [by left|]. split; [by left|done].
  - destruct (IH Hx) as (y' & Δ' & H1' & H2' & H3' & H4'). exists y', Δ'. split; [by right|]. split; [by right|done].
Qed.

Lemma reO_id (O : node → list msg) (c : comp) : c.2.2 = O c.1 → reO O c = c.
Proof. destruct c as [n [[P C] E]]. simpl. intros ->. done. Qed.

Section Snd.
  Context `{QM : QuantumModel} (p q : proc * St).
  Context (O : node → list msg) (Ch : channel → Prop) (K : tag → okind) (T : proc).
  Context (r : nat → dist comp) (w : nat → item).

  Notation Ok := (real_off p q Ch K).

  Hypothesis HT : obs_for p q T.
  Hypothesis HO : ∀ n m, plain n → S_T T n = false → (m ∈ O n ↔ m ∈ O_T T n).
  Hypothesis HCh : ∀ c, c ∈ out_chans T → Ch c.
  Hypothesis HokI : ∀ n o, menu T n o → Ok o.
  Hypothesis Hw : run_word (M := lq_menu O) (menu T) (S_T T) (dinit O q) r w.
  Hypothesis Hfin : fin (visited r).
  Hypothesis Hz : q.2 ≠ szero.

  Definition O' (n : node) : list msg := if excluded_middle_informative (visited r n) then O n else [].

  Definition S' (n : node) : bool :=
    S_T T n || (if excluded_middle_informative (visited r n) then false else true).

  Lemma O'_vis n : visited r n → O' n = O n.
  Proof. intros Hv. unfold O'. by destruct (excluded_middle_informative (visited r n)). Qed.

  Lemma S'_vis n : visited r n → S' n = S_T T n.
  Proof.
    intros Hv. unfold S'. destruct (excluded_middle_informative (visited r n)); [by rewrite orb_false_r|done].
  Qed.

  Lemma S'_nvis n : ¬ visited r n → S' n = true ∧ O' n = [].
  Proof.
    intros Hv. unfold S', O'. destruct (excluded_middle_informative (visited r n)); [done|].
    split; [apply orb_true_r|done].
  Qed.

  Lemma S'_up n : S_T T n = true → S' n = true.
  Proof. unfold S'. by intros ->. Qed.

  Lemma S'_false n : S' n = false → visited r n ∧ S_T T n = false.
  Proof.
    intros Hs. destruct (classic (visited r n)) as [Hv|Hv].
    - split; [done|]. by rewrite <- (S'_vis n Hv).
    - rewrite (proj1 (S'_nvis n Hv)) in Hs. discriminate Hs.
  Qed.

  Lemma q_inv i x : x ∈ r i → plain x.1.1 ∧ x.1.2.2 = O x.1.1.
  Proof.
    refine (run_inv (mdlts (M := lq_menu O) (menu T) (S_T T)) (λ c : comp, plain c.1 ∧ c.2.2 = O c.1) _
              (dinit O q) r _ _ i x).
    - intros ρ c σ Δ [Hpl HE] Hs y Hy. exact (proj2 (cstep_reO (menu T) O O ρ c σ Δ (λ m Hm, Hm) Hpl HE Hs) y Hy).
    - exact (run_word_is_run (M := lq_menu O) _ _ _ _ _ Hw).
    - intros x0 ->%list_elem_of_singleton. split; [intros k c v Hin; by apply elem_of_nil in Hin|done].
  Qed.

  Lemma vis_run i x : x ∈ r i → ∀ n m, x.1.1 = n ++ m → visited r n.
  Proof.
    revert x. induction i as [|i IH]; intros x Hx n m E.
    - exists 0, x.1, x.2. split; [by destruct x|]. rewrite (proj1 Hw) in Hx.
      apply list_elem_of_singleton in Hx. subst x. simpl in *. symmetry in E. by apply app_eq_nil in E as [-> _].
    - pose proof Hx as Hx0. destruct (proj2 Hw i) as [(_ & Δs & HF & Eq)|(_ & Eq)]; [|rewrite Eq in Hx; by eapply IH].
      rewrite Eq in Hx. destruct (dsum_elem _ _ _ x HF Hx) as ([c ρ] & Δ & Hc & _ & Hstep & HxΔ). simpl in Hstep.
      destruct Hstep as [(_ & Hs)|(_ & ->)].
      + destruct (mstep_cell (M := lq_menu O) _ _ _ _ _ Hs) as [[_ Hn]|(o & _ & _ & Ht)].
        * apply (IH (c, ρ) Hc n m). rewrite <- E. symmetry. exact (Hn x HxΔ : x.1.1 = c.1).
        * destruct (Ht x HxΔ) as (a & _ & Ea). change (x.1.1 = c.1 ++ [a]) in Ea.
          destruct m as [|b m _] using rev_ind.
          -- rewrite app_nil_r in E. subst n. exists (Datatypes.S i), x.1, x.2. split; [by destruct x|done].
          -- rewrite Ea, app_assoc in E. apply app_inj_tail in E as [E _]. exact (IH (c, ρ) Hc n m E).
      + apply list_elem_of_singleton in HxΔ. subst x. exact (IH (c, ρ) Hc n m E).
  Qed.

  Lemma vis_prefix n m : visited r (n ++ m) → visited r n.
  Proof. intros (i & c & ρ & Hin & E). exact (vis_run i (c, ρ) Hin n m E). Qed.

  Lemma q_vis i c ρ : (c, ρ) ∈ r i → visited r c.1.
  Proof. intros Hin. by exists i, c, ρ. Qed.

  Lemma q_S' i c ρ : (c, ρ) ∈ r i → S' c.1 = S_T T c.1.
  Proof. intros Hin. exact (S'_vis _ (q_vis i c ρ Hin)). Qed.

  Lemma Q3 J i c ρ σ : (c, ρ) ∈ r i → ((∃ Δ, cstep J O ρ c σ Δ) ↔ (∃ Δ, cstep J O' ρ c σ Δ)).
  Proof.
    intros Hin. destruct (q_inv i (c, ρ) Hin) as [Hpl HE]. pose proof (q_vis i c ρ Hin) as Hv. simpl in Hpl, HE.
    assert (HE' : c.2.2 = O' c.1) by (by rewrite (O'_vis _ Hv)).
    split; intros [Δ Hs].
    - assert (Hsub : ∀ m, m ∈ O c.1 → m ∈ O' c.1) by (intros m Hm; by rewrite (O'_vis _ Hv)).
      destruct (cstep_reO J O O' ρ c σ Δ Hsub Hpl HE Hs) as [Hs' _]. rewrite (reO_id O' c HE') in Hs'. eauto.
    - assert (Hsub : ∀ m, m ∈ O' c.1 → m ∈ O c.1) by (intros m Hm; by rewrite <- (O'_vis _ Hv)).
      destruct (cstep_reO J O' O ρ c σ Δ Hsub Hpl HE' Hs) as [Hs' _]. rewrite (reO_id O c HE) in Hs'. eauto.
  Qed.

  Lemma Q1 J i c ρ σ Δ : (c, ρ) ∈ r i → (∀ y, y ∈ Δ → visited r y.1.1) →
    cstep J O ρ c σ Δ → cstep J O' ρ c σ Δ.
  Proof.
    intros Hin HvΔ Hs. destruct (q_inv i (c, ρ) Hin) as [Hpl HE]. pose proof (q_vis i c ρ Hin) as Hv.
    simpl in Hpl, HE. assert (HE' : c.2.2 = O' c.1) by (by rewrite (O'_vis _ Hv)).
    assert (Hsub : ∀ m, m ∈ O c.1 → m ∈ O' c.1) by (intros m Hm; by rewrite (O'_vis _ Hv)).
    destruct (cstep_reO J O O' ρ c σ Δ Hsub Hpl HE Hs) as [Hs' Hall]. rewrite (reO_id O' c HE') in Hs'.
    match type of Hs' with cstep _ _ _ _ _ ?D0 => assert (Em : D0 = Δ) end.
    { rewrite <- (map_id Δ) at 2. apply map_ext_in. intros [y ρy] Hy%list_elem_of_In. simpl. f_equal.
      apply reO_id. pose proof (HvΔ _ Hy) as Hvy. pose proof (proj2 (Hall _ Hy)) as HEy. simpl in Hvy, HEy |- *.
      rewrite (O'_vis _ Hvy). exact HEy. }
    by rewrite Em in Hs'.
  Qed.

  Lemma Q2 J i c ρ σ Δ : (c, ρ) ∈ r i → (∀ y, y ∈ Δ → visited r y.1.1) →
    cstep J O' ρ c σ Δ → cstep J O ρ c σ Δ.
  Proof.
    intros Hin HvΔ Hs. destruct (q_inv i (c, ρ) Hin) as [Hpl HE]. pose proof (q_vis i c ρ Hin) as Hv.
    simpl in Hpl, HE. assert (HE' : c.2.2 = O' c.1) by (by rewrite (O'_vis _ Hv)).
    assert (Hsub : ∀ m, m ∈ O' c.1 → m ∈ O c.1) by (intros m Hm; by rewrite <- (O'_vis _ Hv)).
    destruct (cstep_reO J O' O ρ c σ Δ Hsub Hpl HE' Hs) as [Hs' Hall]. rewrite (reO_id O c HE) in Hs'.
    match type of Hs' with cstep _ _ _ _ _ ?D0 => assert (Em : D0 = Δ) end.
    { rewrite <- (map_id Δ) at 2. apply map_ext_in. intros [y ρy] Hy%list_elem_of_In. simpl. f_equal.
      apply reO_id. pose proof (HvΔ _ Hy) as Hvy. pose proof (proj2 (Hall _ Hy)) as HEy. simpl in Hvy, HEy |- *.
      rewrite <- (O'_vis _ Hvy). exact HEy. }
    by rewrite Em in Hs'.
  Qed.

  Lemma q_run' : run_word (M := lq_menu O') (menu T) S' (dinit O' q) r w.
  Proof.
    destruct Hw as [E0 Hr]. split.
    - rewrite E0. unfold dinit. rewrite O'_vis; [done|]. exists 0, ([], (q.1, [], O [])), q.2.
      split; [rewrite E0; by left|done].
    - intros i. destruct (Hr i) as [(Hm & Δs & HF & Eq)|(Hst & Eq)].
      + left. split.
        * destruct Hm as (c & ρ & Δ & Hin & Hns & Hs).
          destruct (proj1 (Q3 (menu T) i c ρ (w i) Hin) (ex_intro _ Δ Hs)) as [Δ' Hs'].
          exists c, ρ, Δ'. split; [done|]. split; [|exact Hs'].
          change (¬ S' c.1 = true). rewrite (q_S' i c ρ Hin). exact Hns.
        * exists Δs. split; [|done]. refine (Forall2_mem_impl _ _ _ _ HF _). intros [c ρ] Δ Hin HΔ Hstep.
          simpl in Hstep |- *. destruct Hstep as [(Hns & Hs)|(Hd & ->)].
          -- left. split; [change (¬ S' c.1 = true); rewrite (q_S' i c ρ Hin); exact Hns|].
             apply (Q1 (menu T) i c ρ (w i) Δ Hin); [|exact Hs]. intros [cy ρy] Hy.
             exists (Datatypes.S i), cy, ρy. split; [|done]. rewrite Eq. exact (elem_of_dsum Δ Δs _ HΔ Hy).
          -- right. split; [|done]. destruct Hd as [Hsc|Hno].
             ++ left. change (S' c.1 = true). rewrite (q_S' i c ρ Hin). exact Hsc.
             ++ right. intros Δ' Hs'.
                destruct (proj2 (Q3 (menu T) i c ρ (w i) Hin) (ex_intro _ Δ' Hs')) as [Δ0 Hs0]. exact (Hno Δ0 Hs0).
      + right. split; [|done]. intros σ (c & ρ & Δ & Hin & Hns & Hs).
        destruct (proj2 (Q3 (menu T) i c ρ σ Hin) (ex_intro _ Δ Hs)) as [Δ0 Hs0]. apply (Hst σ).
        exists c, ρ, Δ0. split; [done|]. split; [|exact Hs0].
        change (¬ S_T T c.1 = true). rewrite <- (q_S' i c ρ Hin). exact Hns.
  Qed.

  Notation U' := (used_by O' S' r w).
  Notation U := (cells (M := lq_menu O) (S_T T) r w).

  Lemma Hrun0' : run_word (M := lq_menu O') (menu T) S' (r 0) r w.
  Proof. destruct q_run' as [E Hr]. split; [done|exact Hr]. Qed.

  Lemma Hrun0 : run_word (M := lq_menu O) (menu T) (S_T T) (r 0) r w.
  Proof. destruct Hw as [E Hr]. split; [done|exact Hr]. Qed.

  Lemma Hinit' (J : node → offer → Prop) x :
    x ∈ r 0 → visited_ok (M := lq_menu O') J (mnode (MenuSts := lq_menu O') x.1).
  Proof.
    rewrite (proj1 Hw). intros ->%list_elem_of_singleton m a m2 E. simpl in E. destruct m; discriminate E.
  Qed.

  Lemma Hinit0 (J : node → offer → Prop) x :
    x ∈ r 0 → visited_ok (M := lq_menu O) J (mnode (MenuSts := lq_menu O) x.1).
  Proof.
    rewrite (proj1 Hw). intros ->%list_elem_of_singleton m a m2 E. simpl in E. destruct m; discriminate E.
  Qed.

  Lemma q_nz i x : x ∈ r i → x.2 ≠ szero.
  Proof.
    intros Hx.
    refine (run_weights (SchedSts0 := mdlts (M := lq_menu O) (menu T) (S_T T)) Stay (λ ρ, ρ ≠ szero)
              (λ ρ c σ Δ Hg Hs, mstep_nonzero (menu T) ρ c σ Δ Hg Hs) (dinit O q) r
              (run_word_is_run (M := lq_menu O) _ _ _ _ _ Hw) _ i x Hx).
    intros y ->%list_elem_of_singleton. exact Hz.
  Qed.

  Lemma U'_sub n o : U' n o → menu T n o.
  Proof. exact (cells_sub (M := lq_menu O') (menu T) S' r w Hrun0' (Hinit' _) n o). Qed.

  Lemma U_sub n o : U n o → menu T n o.
  Proof. exact (cells_sub (M := lq_menu O) (menu T) (S_T T) r w Hrun0 (Hinit0 _) n o). Qed.

  Lemma HrunU' : run_word (M := lq_menu O') U' S' (r 0) r w.
  Proof. exact (run_cells (M := lq_menu O') (menu T) S' r w Hrun0' (Hinit' _) q_nz). Qed.

  Lemma HrunU : run_word (M := lq_menu O) U (S_T T) (r 0) r w.
  Proof. exact (run_cells (M := lq_menu O) (menu T) (S_T T) r w Hrun0 (Hinit0 _) q_nz). Qed.

  Lemma comp' : computation q O' S' r w.
  Proof.
    split.
    - rewrite <- (proj1 q_run'). exact HrunU'.
    - exact Hfin.
  Qed.

  Lemma vis_plain n : visited r n → plain n.
  Proof. intros (i & c & ρ & Hin & <-). exact (proj1 (q_inv i (c, ρ) Hin)). Qed.

  Lemma coh' : coherent p q O' S' Ch K r w.
  Proof.
    split; [|split; [|split; [|split; [|split]]]].
    - intros n a Hs. destruct (S' (n ++ [a])) eqn:E; [done|]. destruct (S'_false _ E) as [Hv Hf].
      pose proof (vis_prefix n [a] Hv) as Hvn. rewrite (S'_vis n Hvn) in Hs.
      rewrite (S_T_ext_closed T n a Hs) in Hf. discriminate Hf.
    - exact S'_nvis.
    - intros n o Hu. exact (HokI n o (U'_sub n o Hu)).
    - intros n k c v Hs Hin. destruct (S'_false n Hs) as [Hv Hf]. rewrite (O'_vis n Hv) in Hin.
      apply (HO n _ (vis_plain n Hv) Hf) in Hin. apply O_T_spec in Hin as (X & HX & Hne).
      assert (Hm : menu T n (OffOut k c v)) by (exists X, (CoOut k c v); done).
      destruct (HokI _ _ Hm) as (Hty & Hp & Hq & _). unfold typed in Hty. simpl in Hty, Hp, Hq.
      split; [by symmetry|]. split; [done|]. split; [done|]. apply HCh.
      destruct (co_succ X (CoOut k c v)) as [|X1 l] eqn:E; [done|].
      assert (HX1 : X1 ∈ co_succ X (CoOut k c v)) by (rewrite E; by left).
      pose proof (prog_step_out_chan X k c v X1 (proj1 (tnodes_obs T (proj1 (proj1 HT)) n X HX))
                    (co_succ_sound _ _ _ HX1)) as Hc.
      exact (proj1 (tnodes_chans T (proj1 (proj1 HT)) n X HX) c Hc).
    - intros n k c v c' v' Hs Hi1 Hi2. destruct (S'_false n Hs) as [Hv Hf]. rewrite (O'_vis n Hv) in Hi1, Hi2.
      apply (HO n _ (vis_plain n Hv) Hf) in Hi1, Hi2. exact (O_T_fun T n k c v c' v' (proj1 HT) Hi1 Hi2).
    - intros n a m Hs Hin. destruct (S'_false _ Hs) as [Hv Hf]. pose proof (vis_prefix n [a] Hv) as Hvn.
      rewrite (O'_vis _ Hv). rewrite (O'_vis _ Hvn) in Hin.
      assert (Esn : S_T T n = false).
      { destruct (S_T T n) eqn:Esn; [|done]. rewrite (S_T_ext_closed T n a Esn) in Hf. discriminate Hf. }
      pose proof (vis_plain _ Hv) as Hpl. destruct (plain_snoc n a Hpl) as [Hpn Ha].
      apply (HO _ _ Hpl Hf). apply (HO n _ Hpn Esn) in Hin. apply O_T_mono; [exact (proj1 HT)|exact Ha| |exact Hin].
      destruct Hv as (i & c0 & ρ0 & Hin0 & E0).
      pose proof (visited_run (M := lq_menu O) (menu T) (S_T T) r w Hrun0 (Hinit0 _) i (c0, ρ0) Hin0 n a []) as Hmn.
      destruct Hmn as (X & a' & HX & Ea & Hne); [simpl; by rewrite E0|].
      destruct (co_succ X a) as [|Y l] eqn:EY.
      + exfalso. apply Hne. exact (co_succ_offer X a a' (eq_sym Ea) EY).
      + intros Enil. assert (HY : Y ∈ tnodes T (n ++ [a])).
        { apply tnodes_app_elem. exists X. split; [done|]. rewrite EY. by left. }
        rewrite Enil in HY. by apply elem_of_nil in HY.
  Qed.

  Lemma cells_eq' n o : U' n o ↔ U n o.
  Proof.
    unfold used_by, cells. split; intros (i & c & ρ & Δ & Hin & Hs & Hnf & Hne & Hst & Hall); exists i, c, ρ, Δ;
      (split; [done|]); pose proof (q_S' i c ρ Hin) as ES;
      assert (HvΔ : ∀ y, y ∈ Δ → visited r y.1.1)
        by (intros [cy ρy] Hy; exact (q_vis (Datatypes.S i) cy ρy (Hall _ Hy))).
    - split; [change (S_T T c.1 = false); change (S' c.1 = false) in Hs; congruence|].
      split; [exact Hnf|]. split; [done|]. split; [|done]. exact (Q2 (single n o) i c ρ (w i) Δ Hin HvΔ Hst).
    - split; [change (S' c.1 = false); change (S_T T c.1 = false) in Hs; congruence|].
      split; [exact Hnf|]. split; [done|]. split; [|done]. exact (Q1 (single n o) i c ρ (w i) Δ Hin HvΔ Hst).
  Qed.

  Lemma stable_eq i :
    dstable (SchedSts0 := mdlts (M := lq_menu O') U' S') (r i)
    ↔ dstable (SchedSts0 := mdlts (M := lq_menu O) U (S_T T)) (r i).
  Proof.
    split; intros Hst σ (c & ρ & Δ & Hin & Hns & Hs); apply (Hst σ); pose proof (q_S' i c ρ Hin) as ES.
    - destruct (proj1 (Q3 U i c ρ σ Hin) (ex_intro _ Δ Hs)) as [Δ' Hs'].
      exists c, ρ, Δ'. split; [done|]. split; [change (¬ S' c.1 = true); rewrite ES; exact Hns|].
      exact (mstep_mono (M := lq_menu O') U U' ρ c σ Δ' (λ n o, proj2 (cells_eq' n o)) Hs').
    - destruct (proj2 (Q3 U' i c ρ σ Hin) (ex_intro _ Δ Hs)) as [Δ' Hs'].
      exists c, ρ, Δ'. split; [done|]. split; [change (¬ S_T T c.1 = true); rewrite <- ES; exact Hns|].
      exact (mstep_mono (M := lq_menu O) U' U ρ c σ Δ' (λ n o, proj1 (cells_eq' n o)) Hs').
  Qed.

  Lemma dstep_eq i :
    dstep (SchedSts0 := mdlts (M := lq_menu O') U' S') Stay (r i) (w i) (r (Datatypes.S i))
    ↔ dstep (SchedSts0 := mdlts (M := lq_menu O) U (S_T T)) Stay (r i) (w i) (r (Datatypes.S i)).
  Proof.
    split; intros Hd.
    - destruct (proj2 HrunU i) as [Hd'|[Hst _]]; [done|]. exfalso.
      exact (dstep_not_stable _ _ _ _ Hd (proj2 (stable_eq i) Hst)).
    - destruct (proj2 HrunU' i) as [Hd'|[Hst _]]; [done|]. exfalso.
      exact (dstep_not_stable _ _ _ _ Hd (proj1 (stable_eq i) Hst)).
  Qed.

  Lemma refused_eq' n o :
    refused (M := lq_menu O') U' S' r w n o ↔ refused (M := lq_menu O) U (S_T T) r w n o.
  Proof.
    unfold refused. split; intros (i & c & ρ & Hin & Hs & Hd); exists i, c, ρ; (split; [done|]);
      pose proof (q_S' i c ρ Hin) as ES.
    - split; [change (S_T T c.1 = false); change (S' c.1 = false) in Hs; congruence|].
      destruct Hd as [(Hd & Hno & Δ & Hex)|(Hst & σ & Δ & Hex)]; [left|right].
      + split; [exact (proj1 (dstep_eq i) Hd)|]. split.
        * intros Δ0 Hm. destruct (proj1 (Q3 U i c ρ (w i) Hin) (ex_intro _ Δ0 Hm)) as [Δ1 Hm1].
          apply (Hno Δ1). exact (mstep_mono (M := lq_menu O') U U' ρ c (w i) Δ1 (λ n' o', proj2 (cells_eq' n' o')) Hm1).
        * exact (proj2 (Q3 (single n o) i c ρ (w i) Hin) (ex_intro _ Δ Hex)).
      + split; [exact (proj1 (stable_eq i) Hst)|]. exists σ.
        exact (proj2 (Q3 (single n o) i c ρ σ Hin) (ex_intro _ Δ Hex)).
    - split; [change (S' c.1 = false); change (S_T T c.1 = false) in Hs; congruence|].
      destruct Hd as [(Hd & Hno & Δ & Hex)|(Hst & σ & Δ & Hex)]; [left|right].
      + split; [exact (proj2 (dstep_eq i) Hd)|]. split.
        * intros Δ0 Hm. destruct (proj2 (Q3 U' i c ρ (w i) Hin) (ex_intro _ Δ0 Hm)) as [Δ1 Hm1].
          apply (Hno Δ1). exact (mstep_mono (M := lq_menu O) U' U ρ c (w i) Δ1 (λ n' o', proj1 (cells_eq' n' o')) Hm1).
        * exact (proj1 (Q3 (single n o) i c ρ (w i) Hin) (ex_intro _ Δ Hex)).
      + split; [exact (proj2 (stable_eq i) Hst)|]. exists σ.
        exact (proj1 (Q3 (single n o) i c ρ σ Hin) (ex_intro _ Δ Hex)).
  Qed.

  Notation J' := (Jstar (M := lq_menu O') Ok U' S' r w).
  Notation Ss' := (Sstar (M := lq_menu O') Ok U' S' r w).
  Notation JY := (Jstar (M := lq_menu O) Ok U (S_T T) r w).
  Notation SsY := (Sstar (M := lq_menu O) Ok U (S_T T) r w).

  Lemma Jstar_eq' n o : J' n o ↔ JY n o.
  Proof. unfold Jstar. rewrite cells_eq', refused_eq'. done. Qed.

  Lemma crossed_eq' n :
    crossed (M := lq_menu O') Ok U' S' r w n ↔ crossed (M := lq_menu O) Ok U (S_T T) r w n.
  Proof.
    unfold crossed. split; intros (m & a & m2 & E & HJ & HnI); exists m, a, m2; (split; [done|]); split.
    - by apply Jstar_eq'.
    - intros Hu. apply HnI. by apply cells_eq'.
    - by apply Jstar_eq'.
    - intros Hu. apply HnI. by apply cells_eq'.
  Qed.

  Lemma Ss_sub n : SsY n = true → Ss' n = true.
  Proof.
    intros [Hs|Hc]%Sstar_inv.
    - apply Sstar_S. by apply S'_up.
    - apply Sstar_crossed. by apply crossed_eq'.
  Qed.

  Lemma snd_main (DC : dep_choice) : alt_trace p q →
    ∃ r', is_run (SchedSts0 := mdlts (M := lq_menu O) JY SsY) Stay (dinit O p) r'
        ∧ run_le (SchedSts0 := mdlts (M := lq_menu O) JY SsY) r' r.
  Proof.
    intros Halt. destruct (Halt O' S' Ch K r w coh' comp') as (r2 & Hr2 & Hle2). unfold trace_sts, trace_menu, trace_succ in Hr2, Hle2.
    set (S1 := mdlts (M := lq_menu O') J' Ss') in *.
    set (S2 := mdlts (M := lq_menu O) J' Ss').
    set (S3 := mdlts (M := lq_menu O) JY SsY).
    assert (Hsucc : ∀ c : comp, psuccess (SchedSts := S1) c ↔ psuccess (SchedSts := S2) (reO O c)).
    { intros c. split; intros Hc; exact Hc. }
    assert (Hsub : ∀ n m, m ∈ O' n → m ∈ O n).
    { intros n m. unfold O'. destruct (excluded_middle_informative (visited r n)); [done|by intros ?%elem_of_nil]. }
    pose proof (morph_run S1 S2 (reO O) (λ c : comp, plain c.1 ∧ c.2.2 = O' c.1) Hsucc) as Hmor.
    assert (HrX : is_run (SchedSts0 := S2) Stay (dinit O p)
              (λ i, map (λ x : comp * weight, (reO O x.1, x.2)) (r2 i))).
    { refine (Hmor _ _ (dinit O' p) r2 _ Hr2).
      - intros ρ c σ Δ [Hpl HE] Hns Hs. exact (cstep_reO J' O' O ρ c σ Δ (Hsub c.1) Hpl HE Hs).
      - intros ρ [n [[P C] E]] σ Δ' [Hpl HE] Hns Hs. simpl in Hpl, HE. subst E.
        assert (Hv : visited r n).
        { destruct (S' n) eqn:Es; [exfalso; apply Hns; exact (Sstar_S (M := lq_menu O') Ok U' S' r w n Es)|].
          exact (proj1 (S'_false n Es)). }
        assert (Hsub' : ∀ m, m ∈ O n → m ∈ O' n) by (intros m Hm; by rewrite (O'_vis n Hv)).
        destruct (cstep_reO J' O O' ρ (reO O (n, (P, C, O' n))) σ Δ' Hsub' Hpl eq_refl Hs) as [Hs' _].
        eexists. exact Hs'.
      - intros x ->%list_elem_of_singleton. split; [|done]. intros k c v Hin. by apply elem_of_nil in Hin. }
    destruct (replay S3 S2
      (λ ρ c σ Δ Hs, mstep_mono (M := lq_menu O) JY J' ρ c σ Δ (λ n o, proj2 (Jstar_eq' n o)) Hs)
      (λ ρ c σ Δ Hs _, or_introl (mstep_mono (M := lq_menu O) J' JY ρ c σ Δ (λ n o, proj1 (Jstar_eq' n o)) Hs))
      (λ c Hc, Ss_sub _ Hc) (λ ρ c σ Δ Hs, mstep_mass _ _ _ _ _ Hs) (λ ρ c σ Δ Hs, mstep_mass _ _ _ _ _ Hs)
      DC _ _ _ HrX (Sim_refl _ _)) as (r' & Hr' & Hm).
    exists r'. split; [exact Hr'|]. intros n v Hv. destruct (Hm n) as (m & Hmm).
    assert (Hlt : v <ₚ succ_mass (SchedSts0 := S1) r2 m).
    { unfold succ_mass in *. rewrite (morph_succ S1 S2 (reO O) Hsucc (r2 m)).
      destruct Hv as [Hv1 Hv2]. split; [by etransitivity|]. intros Hb. apply Hv2. by etransitivity. }
    destruct (Hle2 m v Hlt) as (m' & Hm'). exists m'. unfold succ_mass in *.
    erewrite dmass_of_congr; [exact Hm'|]. intros c ρ Hin.
    change (SsY c.1 = true ↔ Ss' c.1 = true).
    rewrite (Sstar_visited (M := lq_menu O) Ok U (S_T T) r w HrunU (Hinit0 _) m' c ρ Hin).
    rewrite (Sstar_visited (M := lq_menu O') Ok U' S' r w HrunU' (Hinit' _) m' c ρ Hin).
    change (S_T T c.1 = true ↔ S' c.1 = true). by rewrite (q_S' m' c ρ Hin).
  Qed.
End Snd.

Definition finitary `{QM : QuantumModel} (p q : proc * St) : Prop :=
  ∀ O Ch K I S (r : nat → dist comp) w, RealT p q O Ch K I S → run_word (M := lq_menu O) I S (dinit O q) r w →
    fin (visited r).

Theorem trace_sound `{QM : QuantumModel} (DC : dep_choice) (p q : proc * St) :
  q.2 ≠ szero → finitary p q →
  alt_trace p q → ctx_pre_sm_on Stay (obs_for p q) p q.
Proof.
  intros Hz Hconv Halt. apply (proj2 (alt_free_obs_iff DC p q Hz)).
  intros O Ch K I S HR r w Hw. pose proof (Hconv O Ch K I S r w HR Hw) as HN.
  destruct HR as ((T & HT & HO & -> & -> & HCh & HK) & HokI).
  exact (snd_main p q O Ch K T r w HT HO HCh HokI Hw HN Hz DC Halt).
Qed.

Theorem trace_characterisation `{QM : QuantumModel} (DC : dep_choice) (p q : proc * St) :
  q.2 ≠ szero → finitary p q →
  (ctx_pre_sm_on Stay (obs_for p q) p q ↔ alt_trace p q).
Proof.
  intros Hz Hconv. split; [exact (trace_complete DC p q Hz)|exact (trace_sound DC p q Hz Hconv)].
Qed.
(* end hide *)
