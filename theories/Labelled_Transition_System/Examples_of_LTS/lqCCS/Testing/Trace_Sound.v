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
From stdpp Require Import base gmultiset countable decidable list.
From TestingTheory Require Import ActTau pMust_scheduled pMust_almost_sure pMust_smyth pMust_transfer pMust_canonical.
From TestingTheory Require Import lqCCS.General_definition.Algebra lqCCS.quantum_mem.Syntax lqCCS.quantum_mem.Quantum_Weights.
From TestingTheory Require Import lqCCS.Testing.Rec_Observers.
From TestingTheory Require Import lqCCS.lqCCS_prog.Syntax lqCCS.Helper.De_Brujin_lemmas lqCCS.General_definition.Parallel_choice_LTS lqCCS.quantum_mem.LTS lqCCS.lqCCS_prog.LTS lqCCS.lqCCS_par_Qmem.LTS lqCCS.lqCCS_process.LTS.LTS lqCCS.Helper.Conf_labels lqCCS.Helper.Label_lemmas lqCCS.Testing.Scheduled lqCCS.Testing.Observer_predicates lqCCS.Helper.Tag_lemmas lqCCS.Testing.DistLTS lqCCS.Testing.Programs lqCCS.Testing.Observers lqCCS.Testing.Smyth_Soundness lqCCS.Testing.Canonical lqCCS.Testing.Pull lqCCS.Testing.Head lqCCS.Testing.Modes lqCCS.Testing.Syn lqCCS.Testing.Assembly lqCCS.Testing.Final lqCCS.Testing.Trace lqCCS.Testing.Build lqCCS.Testing.Trace_Complete.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

Section Trace_Sound.
  Context `{lqP : lqCCS_Parameters}.

Lemma co_succ_out_same T t c v c' v' T1 :
  T1 ∈ co_succ T (CoOut t c v) → co_succ T (CoOut t c' v') ≠ [] → (c, v) ≠ (c', v') →
  co_succ T1 (CoOut t c' v') ≠ [].
Proof.
  revert T1. induction T as [t' c0 e|e P IHP Q IHQ|P IHP Q IHQ|P IH|X|t' P IH|g]; simpl; intros T1 H1 Hb Hne.
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

Lemma O_T_fun T z t c v c' v' :
  wobserver T → (t, c, v) ∈ O_T T z → (t, c', v') ∈ O_T T z → c = c' ∧ v = v'.
Proof.
  intros HT (X & HX & Hne)%O_T_spec (X' & HX' & Hne')%O_T_spec.
  rewrite (tnodes_unique_w T z X' X HT HX' HX) in Hne'.
  destruct (decide ((c, v) = (c', v'))) as [[= -> ->]|Hd]; [done|]. exfalso.
  destruct (co_succ X (CoOut t c v)) as [|X1 l] eqn:E1; [done|].
  assert (H1 : X1 ∈ co_succ X (CoOut t c v)) by (rewrite E1; by left).
  apply (co_succ_out_same X t c v c' v' X1 H1 Hne' Hd).
  apply (proj2 (proj2 HT) z [] t c v c' v' X1). rewrite app_nil_r. apply tnodes_app_elem. by exists X.
Qed.

Lemma O_T_mono T z a m :
  wobserver T → (∀ t c v, a ≠ CoOut t c v) → tnodes T (z ++ [a]) ≠ [] → m ∈ O_T T z → m ∈ O_T T (z ++ [a]).
Proof.
  destruct m as [[t c] v]. intros HT Ha Hne (X & HX & Hout)%O_T_spec.
  destruct (tnodes T (z ++ [a])) as [|Y l] eqn:Et; [done|].
  assert (HY : Y ∈ tnodes T (z ++ [a])) by (rewrite Et; by left). pose proof HY as HY0.
  apply tnodes_app_elem in HY as (X0 & HX0 & HYa). rewrite (tnodes_unique_w T z X0 X HT HX0 HX) in HYa.
  destruct (co_succ X (CoOut t c v)) as [|X1 l1] eqn:E1; [done|].
  assert (H1 : X1 ∈ co_succ X (CoOut t c v)) by (rewrite E1; by left).
  assert (Hb : co_succ X1 a ≠ []).
  { apply (co_succ_out_keep X t c v a X1 H1); [|intros c' v'; apply Ha].
    intros E. rewrite E in HYa. by apply elem_of_nil in HYa. }
  destruct (co_succ X1 a) as [|X2 l2] eqn:E2; [done|].
  assert (H2 : X2 ∈ co_succ X1 a) by (rewrite E2; by left).
  destruct (co_succ_out_swap X t c v a X1 X2 H1 H2) as (Y' & HY' & H3).
  assert (HYn : Y' ∈ tnodes T (z ++ [a])) by (apply tnodes_app_elem; by exists X).
  rewrite (tnodes_unique_w T _ Y' Y HT HYn HY0) in H3.
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

Section Snd.
  Context `{QM : QuantumModel} (p q : prog * St).
  Context (O : node → list msg) (Ch : channel → Prop) (K : tag → okind) (T : prog).
  Context (r : nat → dist comp) (w : nat → item).

  Notation Ok := (real_off p q Ch K).

  Hypothesis HW : wobserver T.
  Hypothesis Hchans : ∀ z X c, X ∈ tnodes T z → c ∈ out_chans X → c ∈ out_chans T.
  Hypothesis HO : ∀ z m, plain z → S_T T z = false → (m ∈ O z ↔ m ∈ O_T T z).
  Hypothesis HCh : ∀ c, c ∈ out_chans T → Ch c.
  Hypothesis HokI : ∀ z o, menu T z o → Ok o.
  Hypothesis Hw : run_word (M := lq_menu O) (menu T) (S_T T) (dinit q) r w.
  Hypothesis Hz : q.2 ≠ szero.

  Definition O' (z : node) : list msg := if excluded_middle_informative (visited r z) then O z else [].

  Definition S' (z : node) : bool :=
    S_T T z || (if excluded_middle_informative (visited r z) then false else true).

  Lemma O'_vis z : visited r z → O' z = O z.
  Proof. intros Hv. unfold O'. by destruct (excluded_middle_informative (visited r z)). Qed.

  Lemma S'_vis z : visited r z → S' z = S_T T z.
  Proof.
    intros Hv. unfold S'. destruct (excluded_middle_informative (visited r z)); [by rewrite orb_false_r|done].
  Qed.

  Lemma S'_nvis z : ¬ visited r z → S' z = true ∧ O' z = [].
  Proof.
    intros Hv. unfold S', O'. destruct (excluded_middle_informative (visited r z)); [done|].
    split; [apply orb_true_r|done].
  Qed.

  Lemma S'_up z : S_T T z = true → S' z = true.
  Proof. unfold S'. by intros ->. Qed.

  Lemma S'_false z : S' z = false → visited r z ∧ S_T T z = false.
  Proof.
    intros Hs. destruct (classic (visited r z)) as [Hv|Hv].
    - split; [done|]. by rewrite <- (S'_vis z Hv).
    - rewrite (proj1 (S'_nvis z Hv)) in Hs. discriminate Hs.
  Qed.

  Lemma q_inv n x : x ∈ r n → plain x.1.1.
  Proof.
    refine (run_inv (mdlts (M := lq_menu O) (menu T) (S_T T)) (λ c : comp, plain c.1) _
              (dinit q) r _ _ n x).
    - intros ρ c σ Δ Hpl Hs y Hy. exact (cstep_plain (menu T) O ρ c σ Δ Hs Hpl y Hy).
    - exact (run_word_is_run (M := lq_menu O) _ _ _ _ _ Hw).
    - exact (dinit_plain q).
  Qed.

  Lemma vis_run n x : x ∈ r n → ∀ z z', x.1.1 = z ++ z' → visited r z.
  Proof.
    revert x. induction n as [|n IH]; intros x Hx z z' E.
    - exists 0, x.1, x.2. split; [by destruct x|]. rewrite (proj1 Hw) in Hx.
      apply list_elem_of_singleton in Hx. subst x. simpl in *. symmetry in E. by apply app_eq_nil in E as [-> _].
    - pose proof Hx as Hx0. destruct (proj2 Hw n) as [(_ & Δs & HF & Eq)|(_ & Eq)]; [|rewrite Eq in Hx; by eapply IH].
      rewrite Eq in Hx. destruct (dsum_elem _ _ _ x HF Hx) as ([c ρ] & Δ & Hc & _ & Hstep & HxΔ). simpl in Hstep.
      destruct Hstep as [(_ & Hs)|(_ & ->)].
      + destruct (mstep_cell (M := lq_menu O) _ _ _ _ _ Hs) as [[_ Hn]|(o & _ & _ & Ht)].
        * apply (IH (c, ρ) Hc z z'). rewrite <- E. symmetry. exact (Hn x HxΔ : x.1.1 = c.1).
        * destruct (Ht x HxΔ) as (a & _ & Ea). change (x.1.1 = c.1 ++ [a]) in Ea.
          destruct z' as [|b z' _] using rev_ind.
          -- rewrite app_nil_r in E. subst z. exists (Datatypes.S n), x.1, x.2. split; [by destruct x|done].
          -- rewrite Ea, app_assoc in E. apply app_inj_tail in E as [E _]. exact (IH (c, ρ) Hc z z' E).
      + apply list_elem_of_singleton in HxΔ. subst x. exact (IH (c, ρ) Hc z z' E).
  Qed.

  Lemma vis_prefix z z' : visited r (z ++ z') → visited r z.
  Proof. intros (n & c & ρ & Hin & E). exact (vis_run n (c, ρ) Hin z z' E). Qed.

  Lemma q_vis n c ρ : (c, ρ) ∈ r n → visited r c.1.
  Proof. intros Hin. by exists n, c, ρ. Qed.

  Lemma q_S' n c ρ : (c, ρ) ∈ r n → S' c.1 = S_T T c.1.
  Proof. intros Hin. exact (S'_vis _ (q_vis n c ρ Hin)). Qed.

  Lemma Q1 J n c ρ σ Δ : (c, ρ) ∈ r n → cstep J O ρ c σ Δ → cstep J O' ρ c σ Δ.
  Proof.
    intros Hin. pose proof (q_vis n c ρ Hin) as Hv. apply cstep_outputs. intros m Hm. by rewrite (O'_vis _ Hv).
  Qed.

  Lemma Q2 J n c ρ σ Δ : (c, ρ) ∈ r n → cstep J O' ρ c σ Δ → cstep J O ρ c σ Δ.
  Proof.
    intros Hin. pose proof (q_vis n c ρ Hin) as Hv. apply cstep_outputs. intros m Hm. by rewrite <- (O'_vis _ Hv).
  Qed.

  Lemma Q3 J n c ρ σ : (c, ρ) ∈ r n → ((∃ Δ, cstep J O ρ c σ Δ) ↔ (∃ Δ, cstep J O' ρ c σ Δ)).
  Proof.
    intros Hin. split; intros [Δ Hs]; exists Δ; [by eapply Q1|by eapply Q2].
  Qed.

  Lemma q_run' : run_word (M := lq_menu O') (menu T) S' (dinit q) r w.
  Proof.
    destruct Hw as [E0 Hr]. split.
    - exact E0.
    - intros n. destruct (Hr n) as [(Hm & Δs & HF & Eq)|(Hst & Eq)].
      + left. split.
        * destruct Hm as (c & ρ & Δ & Hin & Hns & Hs).
          destruct (proj1 (Q3 (menu T) n c ρ (w n) Hin) (ex_intro _ Δ Hs)) as [Δ' Hs'].
          exists c, ρ, Δ'. split; [done|]. split; [|exact Hs'].
          change (¬ S' c.1 = true). rewrite (q_S' n c ρ Hin). exact Hns.
        * exists Δs. split; [|done]. refine (Forall2_mem_impl _ _ _ _ HF _). intros [c ρ] Δ Hin HΔ Hstep.
          simpl in Hstep |- *. destruct Hstep as [(Hns & Hs)|(Hd & ->)].
          -- left. split; [change (¬ S' c.1 = true); rewrite (q_S' n c ρ Hin); exact Hns|].
             exact (Q1 (menu T) n c ρ (w n) Δ Hin Hs).
          -- right. split; [|done]. destruct Hd as [Hsc|Hno].
             ++ left. change (S' c.1 = true). rewrite (q_S' n c ρ Hin). exact Hsc.
             ++ right. intros Δ' Hs'.
                destruct (proj2 (Q3 (menu T) n c ρ (w n) Hin) (ex_intro _ Δ' Hs')) as [Δ0 Hs0]. exact (Hno Δ0 Hs0).
      + right. split; [|done]. intros σ (c & ρ & Δ & Hin & Hns & Hs).
        destruct (proj2 (Q3 (menu T) n c ρ σ Hin) (ex_intro _ Δ Hs)) as [Δ0 Hs0]. apply (Hst σ).
        exists c, ρ, Δ0. split; [done|]. split; [|exact Hs0].
        change (¬ S_T T c.1 = true). rewrite <- (q_S' n c ρ Hin). exact Hns.
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
    rewrite (proj1 Hw). intros ->%list_elem_of_singleton z' a z2 E. simpl in E. destruct z'; discriminate E.
  Qed.

  Lemma Hinit0 (J : node → offer → Prop) x :
    x ∈ r 0 → visited_ok (M := lq_menu O) J (mnode (MenuSts := lq_menu O) x.1).
  Proof.
    rewrite (proj1 Hw). intros ->%list_elem_of_singleton z' a z2 E. simpl in E. destruct z'; discriminate E.
  Qed.

  Lemma q_nz n x : x ∈ r n → x.2 ≠ szero.
  Proof.
    intros Hx.
    refine (run_weights (SchedSts0 := mdlts (M := lq_menu O) (menu T) (S_T T)) Stay (λ ρ, ρ ≠ szero)
              (λ ρ c σ Δ Hg Hs, mstep_nonzero (menu T) ρ c σ Δ Hg Hs) (dinit q) r
              (run_word_is_run (M := lq_menu O) _ _ _ _ _ Hw) _ n x Hx).
    intros y ->%list_elem_of_singleton. exact Hz.
  Qed.

  Lemma U'_sub z o : U' z o → menu T z o.
  Proof. exact (cells_sub (M := lq_menu O') (menu T) S' r w Hrun0' (Hinit' _) z o). Qed.

  Lemma U_sub z o : U z o → menu T z o.
  Proof. exact (cells_sub (M := lq_menu O) (menu T) (S_T T) r w Hrun0 (Hinit0 _) z o). Qed.

  Lemma HrunU' : run_word (M := lq_menu O') U' S' (r 0) r w.
  Proof. exact (run_cells (M := lq_menu O') (menu T) S' r w Hrun0' (Hinit' _) q_nz). Qed.

  Lemma HrunU : run_word (M := lq_menu O) U (S_T T) (r 0) r w.
  Proof. exact (run_cells (M := lq_menu O) (menu T) (S_T T) r w Hrun0 (Hinit0 _) q_nz). Qed.

  Lemma run' : run_word (M := lq_menu O') (used_by O' S' r w) S' (dinit q) r w.
  Proof. rewrite <- (proj1 q_run'). exact HrunU'. Qed.

  Lemma vis_plain z : visited r z → plain z.
  Proof. intros (n & c & ρ & Hin & <-). exact (q_inv n (c, ρ) Hin). Qed.

  Lemma coh' : coherent p q O' S' Ch K r w.
  Proof.
    split; [|split; [|split; [|split; [|split]]]].
    - intros z a Hs. destruct (S' (z ++ [a])) eqn:E; [done|]. destruct (S'_false _ E) as [Hv Hf].
      pose proof (vis_prefix z [a] Hv) as Hvn. rewrite (S'_vis z Hvn) in Hs.
      rewrite (S_T_ext_closed T z a Hs) in Hf. discriminate Hf.
    - exact S'_nvis.
    - intros z o Hu. exact (HokI z o (U'_sub z o Hu)).
    - intros z t c v Hs Hin. destruct (S'_false z Hs) as [Hv Hf]. rewrite (O'_vis z Hv) in Hin.
      apply (HO z _ (vis_plain z Hv) Hf) in Hin. apply O_T_spec in Hin as (X & HX & Hne).
      assert (Hm : menu T z (OffOut t c v)) by (exists X, (CoOut t c v); done).
      destruct (HokI _ _ Hm) as (Hty & Hp & Hq & _). unfold typed in Hty. simpl in Hty, Hp, Hq.
      split; [by symmetry|]. split; [done|]. split; [done|]. apply HCh.
      destruct (co_succ X (CoOut t c v)) as [|X1 l] eqn:E; [done|].
      assert (HX1 : X1 ∈ co_succ X (CoOut t c v)) by (rewrite E; by left).
      pose proof (co_succ_step _ _ _ HX1) as Hst.
      pose proof (prog_step_out_chan_r X t c v X1 (proj1 (proj1 HW z X HX)) Hst) as Hc.
      exact (Hchans z X c HX Hc).
    - intros z t c v c' v' Hs Hi1 Hi2. destruct (S'_false z Hs) as [Hv Hf]. rewrite (O'_vis z Hv) in Hi1, Hi2.
      apply (HO z _ (vis_plain z Hv) Hf) in Hi1, Hi2. exact (O_T_fun T z t c v c' v' HW Hi1 Hi2).
    - intros z a m Hs Hin. destruct (S'_false _ Hs) as [Hv Hf]. pose proof (vis_prefix z [a] Hv) as Hvn.
      rewrite (O'_vis _ Hv). rewrite (O'_vis _ Hvn) in Hin.
      assert (Esn : S_T T z = false).
      { destruct (S_T T z) eqn:Esn; [|done]. rewrite (S_T_ext_closed T z a Esn) in Hf. discriminate Hf. }
      pose proof (vis_plain _ Hv) as Hpl. destruct (plain_snoc z a Hpl) as [Hpn Ha].
      apply (HO _ _ Hpl Hf). apply (HO z _ Hpn Esn) in Hin. apply O_T_mono; [exact HW|exact Ha| |exact Hin].
      destruct Hv as (n & c0 & ρ0 & Hin0 & E0).
      pose proof (visited_run (M := lq_menu O) (menu T) (S_T T) r w Hrun0 (Hinit0 _) n (c0, ρ0) Hin0 z a []) as Hmn.
      destruct Hmn as (X & a' & HX & Ea & Hne); [simpl; by rewrite E0|].
      destruct (co_succ X a) as [|Y l] eqn:EY.
      + exfalso. apply Hne. exact (co_succ_offer X a a' (eq_sym Ea) EY).
      + intros Enil. assert (HY : Y ∈ tnodes T (z ++ [a])).
        { apply tnodes_app_elem. exists X. split; [done|]. rewrite EY. by left. }
        rewrite Enil in HY. by apply elem_of_nil in HY.
  Qed.

  Lemma cells_eq' z o : U' z o ↔ U z o.
  Proof.
    unfold used_by, cells. split; intros (n & c & ρ & Δ & Hin & Hs & Hnf & Hne & Hst & Hall); exists n, c, ρ, Δ;
      (split; [done|]); pose proof (q_S' n c ρ Hin) as ES.
    - split; [change (S_T T c.1 = false); change (S' c.1 = false) in Hs; congruence|].
      split; [exact Hnf|]. split; [done|]. split; [|done]. exact (Q2 (single z o) n c ρ (w n) Δ Hin Hst).
    - split; [change (S' c.1 = false); change (S_T T c.1 = false) in Hs; congruence|].
      split; [exact Hnf|]. split; [done|]. split; [|done]. exact (Q1 (single z o) n c ρ (w n) Δ Hin Hst).
  Qed.

  Lemma stable_eq n :
    dstable (SchedSts0 := mdlts (M := lq_menu O') U' S') (r n)
    ↔ dstable (SchedSts0 := mdlts (M := lq_menu O) U (S_T T)) (r n).
  Proof.
    split; intros Hst σ (c & ρ & Δ & Hin & Hns & Hs); apply (Hst σ); pose proof (q_S' n c ρ Hin) as ES.
    - destruct (proj1 (Q3 U n c ρ σ Hin) (ex_intro _ Δ Hs)) as [Δ' Hs'].
      exists c, ρ, Δ'. split; [done|]. split; [change (¬ S' c.1 = true); rewrite ES; exact Hns|].
      exact (mstep_mono (M := lq_menu O') U U' ρ c σ Δ' (λ z o, proj2 (cells_eq' z o)) Hs').
    - destruct (proj2 (Q3 U' n c ρ σ Hin) (ex_intro _ Δ Hs)) as [Δ' Hs'].
      exists c, ρ, Δ'. split; [done|]. split; [change (¬ S_T T c.1 = true); rewrite <- ES; exact Hns|].
      exact (mstep_mono (M := lq_menu O) U' U ρ c σ Δ' (λ z o, proj1 (cells_eq' z o)) Hs').
  Qed.

  Lemma dstep_eq n :
    dstep (SchedSts0 := mdlts (M := lq_menu O') U' S') Stay (r n) (w n) (r (Datatypes.S n))
    ↔ dstep (SchedSts0 := mdlts (M := lq_menu O) U (S_T T)) Stay (r n) (w n) (r (Datatypes.S n)).
  Proof.
    split; intros Hd.
    - destruct (proj2 HrunU n) as [Hd'|[Hst _]]; [done|]. exfalso.
      exact (dstep_not_stable _ _ _ _ Hd (proj2 (stable_eq n) Hst)).
    - destruct (proj2 HrunU' n) as [Hd'|[Hst _]]; [done|]. exfalso.
      exact (dstep_not_stable _ _ _ _ Hd (proj1 (stable_eq n) Hst)).
  Qed.

  Lemma refused_eq' z o :
    refused (M := lq_menu O') U' S' r w z o ↔ refused (M := lq_menu O) U (S_T T) r w z o.
  Proof.
    unfold refused. split; intros (n & c & ρ & Hin & Hs & Hd); exists n, c, ρ; (split; [done|]);
      pose proof (q_S' n c ρ Hin) as ES.
    - split; [change (S_T T c.1 = false); change (S' c.1 = false) in Hs; congruence|].
      destruct Hd as [(Hd & Hno & Δ & Hex)|(Hst & σ & Δ & Hex)]; [left|right].
      + split; [exact (proj1 (dstep_eq n) Hd)|]. split.
        * intros Δ0 Hm. destruct (proj1 (Q3 U n c ρ (w n) Hin) (ex_intro _ Δ0 Hm)) as [Δ1 Hm1].
          apply (Hno Δ1). exact (mstep_mono (M := lq_menu O') U U' ρ c (w n) Δ1 (λ z1 o', proj2 (cells_eq' z1 o')) Hm1).
        * exact (proj2 (Q3 (single z o) n c ρ (w n) Hin) (ex_intro _ Δ Hex)).
      + split; [exact (proj1 (stable_eq n) Hst)|]. exists σ.
        exact (proj2 (Q3 (single z o) n c ρ σ Hin) (ex_intro _ Δ Hex)).
    - split; [change (S' c.1 = false); change (S_T T c.1 = false) in Hs; congruence|].
      destruct Hd as [(Hd & Hno & Δ & Hex)|(Hst & σ & Δ & Hex)]; [left|right].
      + split; [exact (proj2 (dstep_eq n) Hd)|]. split.
        * intros Δ0 Hm. destruct (proj2 (Q3 U' n c ρ (w n) Hin) (ex_intro _ Δ0 Hm)) as [Δ1 Hm1].
          apply (Hno Δ1). exact (mstep_mono (M := lq_menu O) U' U ρ c (w n) Δ1 (λ z1 o', proj1 (cells_eq' z1 o')) Hm1).
        * exact (proj1 (Q3 (single z o) n c ρ (w n) Hin) (ex_intro _ Δ Hex)).
      + split; [exact (proj2 (stable_eq n) Hst)|]. exists σ.
        exact (proj1 (Q3 (single z o) n c ρ σ Hin) (ex_intro _ Δ Hex)).
  Qed.

  Notation J' := (Jstar (M := lq_menu O') Ok U' S' r w).
  Notation Ss' := (Sstar (M := lq_menu O') Ok U' S' r w).
  Notation JY := (Jstar (M := lq_menu O) Ok U (S_T T) r w).
  Notation SsY := (Sstar (M := lq_menu O) Ok U (S_T T) r w).

  Lemma Jstar_eq' z o : J' z o ↔ JY z o.
  Proof. unfold Jstar. rewrite cells_eq', refused_eq'. done. Qed.

  Lemma crossed_eq' z :
    crossed (M := lq_menu O') Ok U' S' r w z ↔ crossed (M := lq_menu O) Ok U (S_T T) r w z.
  Proof.
    unfold crossed. split; intros (z' & a & z2 & E & HJ & HnI); exists z', a, z2; (split; [done|]); split.
    - by apply Jstar_eq'.
    - intros Hu. apply HnI. by apply cells_eq'.
    - by apply Jstar_eq'.
    - intros Hu. apply HnI. by apply cells_eq'.
  Qed.

  Lemma Ss_sub z : SsY z = true → Ss' z = true.
  Proof.
    intros [Hs|Hc]%Sstar_inv.
    - apply Sstar_S. by apply S'_up.
    - apply Sstar_crossed. by apply crossed_eq'.
  Qed.

  Lemma snd_main (DC : dep_choice) :
    (coherent p q O' S' Ch K r w → run_word (M := lq_menu O') (used_by O' S' r w) S' (dinit q) r w →
      ∃ r2, is_run (SchedSts0 := trace_sts p q O' S' Ch K r w) Stay (dinit p) r2
          ∧ run_le (SchedSts0 := trace_sts p q O' S' Ch K r w) r2 r) →
    ∃ r', is_run (SchedSts0 := mdlts (M := lq_menu O) JY SsY) Stay (dinit p) r'
        ∧ run_le (SchedSts0 := mdlts (M := lq_menu O) JY SsY) r' r.
  Proof.
    intros Halt. destruct (Halt coh' run') as (r2 & Hr2 & Hle2). unfold trace_sts, trace_menu, trace_succ in Hr2, Hle2.
    set (S1 := mdlts (M := lq_menu O') J' Ss') in *.
    set (S2 := mdlts (M := lq_menu O) J' Ss').
    set (S3 := mdlts (M := lq_menu O) JY SsY).
    assert (Hsub : ∀ z m, m ∈ O' z → m ∈ O z).
    { intros z m. unfold O'. destruct (excluded_middle_informative (visited r z)); [done|by intros ?%elem_of_nil]. }
    assert (HrX : is_run (SchedSts0 := S2) Stay (dinit p) r2).
    { apply (agree_run S1 S2 Stay _ r2); [|exact Hr2].
      intros n c ρ Hin. split; [done|]. intros Hns σ Δ.
      assert (Hv : visited r c.1).
      { destruct (S' c.1) eqn:Es; [exfalso; apply Hns; exact (Sstar_S (M := lq_menu O') Ok U' S' r w c.1 Es)|].
        exact (proj1 (S'_false c.1 Es)). }
      split; apply cstep_outputs; intros m Hm; [exact (Hsub c.1 m Hm)|by rewrite (O'_vis c.1 Hv)]. }
    destruct (replay S3 S2
      (λ ρ c σ Δ Hs, mstep_mono (M := lq_menu O) JY J' ρ c σ Δ (λ z o, proj2 (Jstar_eq' z o)) Hs)
      (λ ρ c σ Δ Hs _, or_introl (mstep_mono (M := lq_menu O) J' JY ρ c σ Δ (λ z o, proj1 (Jstar_eq' z o)) Hs))
      (λ c Hc, Ss_sub _ Hc) (λ ρ c σ Δ Hs, mstep_mass _ _ _ _ _ Hs) (λ ρ c σ Δ Hs, mstep_mass _ _ _ _ _ Hs)
      DC _ _ _ HrX (Sim_refl _ _)) as (r' & Hr' & Hm).
    exists r'. split; [exact Hr'|]. intros n v Hv. destruct (Hm n) as (m & Hmm).
    assert (Hlt : v <ₚ succ_mass (SchedSts0 := S1) r2 m).
    { unfold succ_mass in *.
      destruct Hv as [Hv1 Hv2]. split; [by etransitivity|]. intros Hb. apply Hv2. by etransitivity. }
    destruct (Hle2 m v Hlt) as (m' & Hm'). exists m'. unfold succ_mass in *.
    erewrite dmass_of_congr; [exact Hm'|]. intros c ρ Hin.
    change (SsY c.1 = true ↔ Ss' c.1 = true).
    rewrite (Sstar_visited (M := lq_menu O) Ok U (S_T T) r w HrunU (Hinit0 _) m' c ρ Hin).
    rewrite (Sstar_visited (M := lq_menu O') Ok U' S' r w HrunU' (Hinit' _) m' c ρ Hin).
    change (S_T T c.1 = true ↔ S' c.1 = true). by rewrite (q_S' m' c ρ Hin).
  Qed.
End Snd.

Definition finitary `{QM : QuantumModel} (p q : prog * St) : Prop :=
  ∀ O Ch K I S (r : nat → dist comp) w, RealT p q O Ch K I S → run_word (M := lq_menu O) I S (dinit q) r w →
    fin (visited r).

Theorem trace_sound `{QM : QuantumModel} (DC : dep_choice) (p q : prog * St) :
  q.2 ≠ szero → finitary p q →
  alt_trace p q → ctx_pre_sm_on Stay (obs_for p q) p q.
Proof.
  intros Hz Hconv Halt. apply (proj2 (alt_free_obs_iff DC p q Hz)).
  intros O Ch K HKr I S HR r w Hw. pose proof (Hconv O Ch K I S r w HR Hw) as HN.
  destruct HR as ((T & HT & HO & -> & -> & HCh & HK) & HokI).
  refine (snd_main p q O Ch K T r w (observer_w T (proj1 HT)) _ HO HCh HokI Hw Hz DC
            (λ Hc Hw', Halt _ _ Ch K r w HKr Hc (conj Hw' HN))).
  intros z X c HX Hc. exact (proj1 (tnodes_chans T (proj1 (proj1 HT)) z X HX) c Hc).
Qed.

Theorem trace_characterisation `{QM : QuantumModel} (DC : dep_choice) (p q : prog * St) :
  q.2 ≠ szero → finitary p q →
  (ctx_pre_sm_on Stay (obs_for p q) p q ↔ alt_trace p q).
Proof.
  intros Hz Hconv. split; [exact (trace_complete DC p q Hz)|exact (trace_sound DC p q Hz Hconv)].
Qed.

End Trace_Sound.

(* end hide *)
