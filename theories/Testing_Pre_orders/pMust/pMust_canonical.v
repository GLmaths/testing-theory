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
From Stdlib.Logic Require Import Classical_Prop Classical_Pred_Type ClassicalDescription.
From Stdlib.Arith Require Import Wf_nat.
Import ListNotations.
From stdpp Require Import base decidable list.
From TestingTheory Require Import pMust_scheduled pMust_almost_sure pMust_smyth pMust_transfer.

Class WeightLaws `{Weights} := MkWeightLaws {
  prob_add_comm a b : prob_add a b = prob_add b a;
  prob_add_assoc a b c : prob_add a (prob_add b c) = prob_add (prob_add a b) c;
  prob_add_zero a : prob_add prob_zero a = a;
  prob_zero_le a : prob_zero ≤ₚ a;
  prob_add_mono a b c : a ≤ₚ b → prob_add a c ≤ₚ prob_add b c;
}.

Section Mass.
  Context `{WeightLaws}.

  Lemma prob_add_zero_r a : prob_add a prob_zero = a.
  Proof. by rewrite prob_add_comm, prob_add_zero. Qed.

  Lemma prob_add_mono2 a b c d : a ≤ₚ b → c ≤ₚ d → prob_add a c ≤ₚ prob_add b d.
  Proof.
    intros Hab Hcd. etransitivity; [by apply prob_add_mono|].
    rewrite (prob_add_comm b c), (prob_add_comm b d). by apply prob_add_mono.
  Qed.

  Context {C : Type}.

  Lemma dmass_app (A B : dist C) : dmass (A ++ B) = prob_add (dmass A) (dmass B).
  Proof.
    induction A as [|x A IH]; simpl.
    - by rewrite prob_add_zero.
    - by rewrite IH, prob_add_assoc.
  Qed.

  Lemma dmass_of_app (good : C → Prop) `{∀ c, Decision (good c)} (A B : dist C) :
    dmass_of good (A ++ B) = prob_add (dmass_of good A) (dmass_of good B).
  Proof.
    induction A as [|x A IH]; simpl.
    - by rewrite prob_add_zero.
    - rewrite IH. case_decide; [by rewrite prob_add_assoc|done].
  Qed.

  Lemma dmass_of_le (good : C → Prop) `{∀ c, Decision (good c)} (A : dist C) :
    dmass_of good A ≤ₚ dmass A.
  Proof.
    induction A as [|x A IH]; simpl.
    - reflexivity.
    - case_decide.
      + apply prob_add_mono2; [reflexivity|done].
      + etransitivity; [exact IH|]. rewrite <- (prob_add_zero (dmass A)) at 1. apply prob_add_mono, prob_zero_le.
  Qed.

  Lemma dmass_of_all (good : C → Prop) `{∀ c, Decision (good c)} (A : dist C) :
    (∀ x, x ∈ A → good x.1) → dmass_of good A = dmass A.
  Proof.
    induction A as [|x A IH]; intros Hall; [done|]. simpl.
    rewrite decide_True; [|apply Hall; by left].
    rewrite IH; [done|]. intros y Hy. apply Hall. by right.
  Qed.

  Lemma dmass_of_congr (good good' : C → Prop) `{∀ c, Decision (good c)} `{∀ c, Decision (good' c)} (D : dist C) :
    (∀ c ρ, (c, ρ) ∈ D → good c ↔ good' c) → dmass_of good D = dmass_of good' D.
  Proof.
    induction D as [|[c ρ] D IH]; intros Hg; [done|]. simpl. rewrite IH.
    - assert (Hc : good c ↔ good' c) by (apply (Hg c ρ); by left).
      case_decide as Ha; case_decide as Hb; try done; exfalso; tauto.
    - intros c' ρ' Hin. apply (Hg c' ρ'). by right.
  Qed.

  Lemma dsum_cons (Δ : dist C) Δs : dsum (Δ :: Δs) = Δ ++ dsum Δs.
  Proof. done. Qed.

  Lemma dsum_app (A B : list (dist C)) : dsum (A ++ B) = dsum A ++ dsum B.
  Proof. apply concat_app. Qed.

  Lemma elem_of_dsum (Δ : dist C) Δs y : Δ ∈ Δs → y ∈ Δ → y ∈ dsum Δs.
  Proof. unfold dsum. rewrite !list_elem_of_In, in_concat. intros Ha Hb. by exists Δ. Qed.
End Mass.

Lemma Forall2_mem_impl {A B} (R R' : A → B → Prop) (l : list A) (k : list B) :
  Forall2 R l k → (∀ x y, x ∈ l → y ∈ k → R x y → R' x y) → Forall2 R' l k.
Proof.
  induction 1 as [|x y l k Hxy _ IH]; intros Hi; constructor.
  - apply Hi; [by left|by left|done].
  - apply IH. intros a b Ha Hb. apply Hi; by right.
Qed.

Section Agree.
  Context `{WeightLaws} {C Sch : Type} (S1 S2 : SchedSts C Sch).

  Definition agree_on (D : dist C) : Prop :=
    ∀ c ρ, (c, ρ) ∈ D → (psuccess (SchedSts := S1) c ↔ psuccess (SchedSts := S2) c)
      ∧ (¬ psuccess (SchedSts := S1) c → ∀ σ Δ, sstep (SchedSts := S1) ρ c σ Δ ↔ sstep (SchedSts := S2) ρ c σ Δ).

  Lemma agree_comp_step L D c ρ σ Δ : agree_on D → (c, ρ) ∈ D →
    comp_step (SchedSts0 := S1) L ρ c σ Δ → comp_step (SchedSts0 := S2) L ρ c σ Δ.
  Proof.
    intros HA Hin Hc. destruct (HA c ρ Hin) as [Hp Hm]. destruct Hc as [[Hns Hs]|[Hst ->]].
    - left. split; [intros Hc; apply Hns, Hp, Hc|apply (Hm Hns), Hs].
    - right. split.
      + destruct (classic (psuccess (SchedSts := S1) c)) as [Hc|Hc]; [left; apply Hp, Hc|].
        destruct Hst as [Hc'|Hn]; [by destruct Hc|right; intros Δ' Hs; apply (Hn Δ'), (Hm Hc), Hs].
      + destruct L; [done|]. simpl. case_decide as Ha; case_decide as Hb; try done; exfalso; tauto.
  Qed.

  Lemma agree_dstep L D σ D' : agree_on D →
    dstep (SchedSts0 := S1) L D σ D' → dstep (SchedSts0 := S2) L D σ D'.
  Proof.
    intros HA [(c & ρ & Δ & Hin & Hns & Hs) (Δs & HF & ->)]. split.
    - destruct (HA c ρ Hin) as [Hp Hm]. exists c, ρ, Δ. split; [done|].
      split; [intros Hc; apply Hns, Hp, Hc|apply (Hm Hns), Hs].
    - exists Δs. split; [|done]. apply (Forall2_mem_impl _ _ _ _ HF).
      intros [c' ρ'] Δ' Hx _ Hc. exact (agree_comp_step L D c' ρ' σ Δ' HA Hx Hc).
  Qed.

  Lemma agree_dstable D : agree_on D → dstable (SchedSts0 := S1) D → dstable (SchedSts0 := S2) D.
  Proof.
    intros HA Hst σ (c & ρ & Δ & Hin & Hns & Hs). apply (Hst σ). destruct (HA c ρ Hin) as [Hp Hm].
    assert (Hn1 : ¬ psuccess (SchedSts := S1) c) by (intros Hc; apply Hns, Hp, Hc).
    exists c, ρ, Δ. split; [done|]. split; [done|apply (Hm Hn1), Hs].
  Qed.

  Lemma agree_run L D r : (∀ i, agree_on (r i)) →
    is_run (SchedSts0 := S1) L D r → is_run (SchedSts0 := S2) L D r.
  Proof.
    intros HA [Hr0 Hr]. split; [done|]. intros i. destruct (Hr i) as [(σ & Hs)|[Hst Ei]].
    - left. exists σ. exact (agree_dstep L _ σ _ (HA i) Hs).
    - right. split; [exact (agree_dstable _ (HA i) Hst)|done].
  Qed.

  Lemma agree_succ_mass r n : agree_on (r n) →
    succ_mass (SchedSts0 := S1) r n = succ_mass (SchedSts0 := S2) r n.
  Proof. intros HA. unfold succ_mass. apply dmass_of_congr. intros c ρ Hin. exact (proj1 (HA c ρ Hin)). Qed.
End Agree.

Section Sub.
  Context `{WeightLaws} {C Sch : Type} (S1 S2 : SchedSts C Sch).

  Hypothesis Hsucc : ∀ c, psuccess (SchedSts := S1) c ↔ psuccess (SchedSts := S2) c.
  Hypothesis Hsub : ∀ ρ c σ Δ, sstep (SchedSts := S1) ρ c σ Δ → sstep (SchedSts := S2) ρ c σ Δ.
  Hypothesis Hact : ∀ ρ c σ Δ, sstep (SchedSts := S2) ρ c σ Δ →
    (∃ ρ' c' Δ', sstep (SchedSts := S1) ρ' c' σ Δ') → ∃ Δ', sstep (SchedSts := S1) ρ c σ Δ'.
  Hypothesis Hstab : ∀ ρ c σ Δ, sstep (SchedSts := S2) ρ c σ Δ → ∃ σ' Δ', sstep (SchedSts := S1) ρ c σ' Δ'.

  Lemma sub_dstep D σ D' : dstep (SchedSts0 := S1) Stay D σ D' → dstep (SchedSts0 := S2) Stay D σ D'.
  Proof.
    intros [(c & ρ & Δ & Hin & Hns & Hs) (Δs & HF & ->)]. split.
    - exists c, ρ, Δ. split; [done|]. split; [intros Hc; apply Hns, Hsucc, Hc|apply Hsub, Hs].
    - exists Δs. split; [|done]. eapply Forall2_impl; [exact HF|].
      intros [c' ρ'] Δ' [[Hn Hs']|[Hst ->]]; simpl in *.
      + left. split; [intros Hc; apply Hn, Hsucc, Hc|apply Hsub, Hs'].
      + right. split; [|done]. destruct Hst as [Hc|Hno]; [left; apply Hsucc, Hc|]. right.
        intros Δ2 Hs2. destruct (Hact _ _ _ _ Hs2) as (Δ3 & Hs3); [by exists ρ, c, Δ|]. exact (Hno Δ3 Hs3).
  Qed.

  Lemma sub_dstable D : dstable (SchedSts0 := S1) D → dstable (SchedSts0 := S2) D.
  Proof.
    intros Hst σ (c & ρ & Δ & Hin & Hns & Hs). destruct (Hstab _ _ _ _ Hs) as (σ' & Δ' & Hs').
    apply (Hst σ'). exists c, ρ, Δ'. split; [done|]. split; [intros Hc; apply Hns, Hsucc, Hc|done].
  Qed.

  Lemma sub_run D r : is_run (SchedSts0 := S1) Stay D r → is_run (SchedSts0 := S2) Stay D r.
  Proof.
    intros [Hr0 Hr]. split; [done|]. intros i. destruct (Hr i) as [(σ & Hs)|[Hst Ei]].
    - left. exists σ. exact (sub_dstep _ σ _ Hs).
    - right. split; [exact (sub_dstable _ Hst)|done].
  Qed.
End Sub.

Section RunInv.
  Context `{WeightLaws} {C Sch : Type} (SS : SchedSts C Sch) (P : C → Prop).
  Hypothesis Hstep : ∀ ρ c σ Δ, P c → sstep (SchedSts := SS) ρ c σ Δ → ∀ y, y ∈ Δ → P y.1.

  Lemma comps_inv (D : dist C) σ Δs :
    Forall2 (λ cρ Δ, comp_step (SchedSts0 := SS) Stay cρ.2 cρ.1 σ Δ) D Δs →
    (∀ x, x ∈ D → P x.1) → ∀ x, x ∈ dsum Δs → P x.1.
  Proof.
    induction 1 as [|[c ρ] Δ D Δs Hc _ IH]; intros HD x Hx; [by apply elem_of_nil in Hx|].
    change (x ∈ Δ ++ dsum Δs) in Hx. apply elem_of_app in Hx as [Hx|Hx].
    - assert (Hc0 : P c) by (apply (HD (c, ρ)); by left). destruct Hc as [[_ Hs]|[_ ->]].
      + exact (Hstep _ _ _ _ Hc0 Hs x Hx).
      + apply list_elem_of_singleton in Hx. by subst.
    - apply IH; [|done]. intros y Hy. apply HD. by right.
  Qed.

  Lemma dstep_inv (D : dist C) σ D' :
    dstep (SchedSts0 := SS) Stay D σ D' → (∀ x, x ∈ D → P x.1) → ∀ x, x ∈ D' → P x.1.
  Proof. intros (_ & Δs & HF & ->) HD. exact (comps_inv D σ Δs HF HD). Qed.

  Lemma run_inv (D : dist C) r :
    is_run (SchedSts0 := SS) Stay D r → (∀ x, x ∈ D → P x.1) → ∀ i x, x ∈ r i → P x.1.
  Proof.
    intros [E Hr] HD i. induction i as [|i IH]; [by rewrite E|].
    destruct (Hr i) as [(σ & Hs)|[_ ->]]; [exact (dstep_inv _ σ _ Hs IH)|done].
  Qed.
End RunInv.

Section Morph.
  Context `{WeightLaws} {C C' Sch : Type} (S1 : SchedSts C Sch) (S2 : SchedSts C' Sch).
  Context (f : C → C') (Inv : C → Prop).

  Notation fd := (map (λ x : C * weight, (f x.1, x.2))).

  Definition inv_on (D : dist C) : Prop := ∀ x, x ∈ D → Inv x.1.

  Hypothesis Hsucc : ∀ c, psuccess (SchedSts := S1) c ↔ psuccess (SchedSts := S2) (f c).

  Lemma morph_succ D :
    dmass_of (psuccess (SchedSts := S1)) D = dmass_of (psuccess (SchedSts := S2)) (fd D).
  Proof.
    induction D as [|[c ρ] D IH]; [done|]. simpl. rewrite IH.
    case_decide as Ha; case_decide as Hb; try done; exfalso; [apply Hb, Hsucc, Ha|apply Ha, Hsucc, Hb].
  Qed.

  Hypothesis Hfwd : ∀ ρ c σ Δ, Inv c → ¬ psuccess (SchedSts := S1) c → sstep (SchedSts := S1) ρ c σ Δ →
    sstep (SchedSts := S2) ρ (f c) σ (fd Δ) ∧ ∀ y, y ∈ Δ → Inv y.1.
  Hypothesis Hbwd : ∀ ρ c σ Δ', Inv c → ¬ psuccess (SchedSts := S1) c → sstep (SchedSts := S2) ρ (f c) σ Δ' →
    ∃ Δ, sstep (SchedSts := S1) ρ c σ Δ.

  Lemma morph_comps D σ Δs : inv_on D →
    Forall2 (λ cρ Δ, comp_step (SchedSts0 := S1) Stay cρ.2 cρ.1 σ Δ) D Δs →
    Forall2 (λ cρ Δ, comp_step (SchedSts0 := S2) Stay cρ.2 cρ.1 σ Δ) (fd D) (map fd Δs) ∧ inv_on (dsum Δs).
  Proof.
    intros HI HF. induction HF as [|[c ρ] Δ D Δs Hc HF IH].
    - split; [constructor|]. intros x Hx. by apply elem_of_nil in Hx.
    - destruct IH as [IH1 IH2]; [intros x Hx; apply HI; by right|].
      assert (Hic : Inv c) by (apply (HI (c, ρ)); by left). simpl in Hc. split.
      + constructor; [|exact IH1]. simpl. destruct Hc as [[Hns Hs]|[Hst ->]].
        * left. split; [intros Hc; apply Hns, Hsucc, Hc|exact (proj1 (Hfwd _ _ _ _ Hic Hns Hs))].
        * right. split; [|done]. destruct (classic (psuccess (SchedSts := S1) c)) as [Hc|Hc]; [left; by apply Hsucc|].
          destruct Hst as [Hc'|Hno]; [by destruct Hc|right].
          intros Δ2 Hs2. destruct (Hbwd _ _ _ _ Hic Hc Hs2) as (Δ3 & Hs3). exact (Hno Δ3 Hs3).
      + intros x Hx. change (x ∈ Δ ++ dsum Δs) in Hx. apply elem_of_app in Hx as [Hx|Hx]; [|by apply IH2].
        destruct Hc as [[Hns Hs]|[Hst ->]]; [exact (proj2 (Hfwd _ _ _ _ Hic Hns Hs) x Hx)|].
        apply list_elem_of_singleton in Hx. by subst.
  Qed.

  Lemma morph_dstep D σ D' : inv_on D → dstep (SchedSts0 := S1) Stay D σ D' →
    dstep (SchedSts0 := S2) Stay (fd D) σ (fd D') ∧ inv_on D'.
  Proof.
    intros HI [(c & ρ & Δ & Hin & Hns & Hs) (Δs & HF & ->)].
    destruct (morph_comps D σ Δs HI HF) as [HF' HI']. split; [|done]. split.
    - exists (f c), ρ, (fd Δ). split; [apply list_elem_of_fmap; by exists (c, ρ)|].
      split; [intros Hc; apply Hns, Hsucc, Hc|]. exact (proj1 (Hfwd ρ c σ Δ (HI (c, ρ) Hin) Hns Hs)).
    - exists (map fd Δs). split; [done|]. unfold dsum. by rewrite concat_map.
  Qed.

  Lemma morph_dstable D : inv_on D → dstable (SchedSts0 := S1) D → dstable (SchedSts0 := S2) (fd D).
  Proof.
    intros HI Hst σ (c' & ρ & Δ' & Hin & Hns & Hs).
    apply list_elem_of_fmap in Hin as ([c ρ0] & E & Hin). simpl in E. injection E as -> ->.
    assert (Hn1 : ¬ psuccess (SchedSts := S1) c) by (intros Hc; apply Hns, Hsucc, Hc).
    destruct (Hbwd _ _ _ _ (HI _ Hin) Hn1 Hs) as (Δ & Hs1). apply (Hst σ). exists c, ρ0, Δ.
    split; [done|]. split; [done|done].
  Qed.

  Lemma morph_run D r : inv_on D → is_run (SchedSts0 := S1) Stay D r →
    is_run (SchedSts0 := S2) Stay (fd D) (λ i, fd (r i)).
  Proof.
    intros HI [Hr0 Hr].
    assert (Hall : ∀ i, inv_on (r i)).
    { induction i as [|i IH]; [by rewrite Hr0|].
      destruct (Hr i) as [(σ & Hs)|[_ E]]; [exact (proj2 (morph_dstep _ _ _ IH Hs))|by rewrite E]. }
    split; [simpl; by rewrite Hr0|]. intros i. destruct (Hr i) as [(σ & Hs)|[Hst E]].
    - left. exists σ. exact (proj1 (morph_dstep _ _ _ (Hall i) Hs)).
    - right. split; [exact (morph_dstable _ (Hall i) Hst)|by rewrite E].
  Qed.
End Morph.

Section MorphSmyth.
  Context `{WeightLaws} {C C' Sch : Type} (S1 : SchedSts C Sch) (S2 : SchedSts C' Sch).
  Context (f : C → C') (g : C' → C) (Inv1 : C → Prop) (Inv2 : C' → Prop).

  Notation fd := (map (λ x : C * weight, (f x.1, x.2))).
  Notation gd := (map (λ x : C' * weight, (g x.1, x.2))).

  Hypothesis HsF : ∀ c, psuccess (SchedSts := S1) c ↔ psuccess (SchedSts := S2) (f c).
  Hypothesis HfF : ∀ ρ c σ Δ, Inv1 c → ¬ psuccess (SchedSts := S1) c → sstep (SchedSts := S1) ρ c σ Δ →
    sstep (SchedSts := S2) ρ (f c) σ (fd Δ) ∧ ∀ y, y ∈ Δ → Inv1 y.1.
  Hypothesis HbF : ∀ ρ c σ Δ', Inv1 c → ¬ psuccess (SchedSts := S1) c → sstep (SchedSts := S2) ρ (f c) σ Δ' →
    ∃ Δ, sstep (SchedSts := S1) ρ c σ Δ.
  Hypothesis HsG : ∀ c, psuccess (SchedSts := S2) c ↔ psuccess (SchedSts := S1) (g c).
  Hypothesis HfG : ∀ ρ c σ Δ, Inv2 c → ¬ psuccess (SchedSts := S2) c → sstep (SchedSts := S2) ρ c σ Δ →
    sstep (SchedSts := S1) ρ (g c) σ (gd Δ) ∧ ∀ y, y ∈ Δ → Inv2 y.1.
  Hypothesis HbG : ∀ ρ c σ Δ', Inv2 c → ¬ psuccess (SchedSts := S2) c → sstep (SchedSts := S1) ρ (g c) σ Δ' →
    ∃ Δ, sstep (SchedSts := S2) ρ c σ Δ.

  Theorem morph_smyth Dp Dq :
    inv_on Inv1 Dp → inv_on Inv2 (fd Dq) → gd (fd Dq) = Dq →
    smyth_le (SchedSts0 := S1) Stay Dp Dq → smyth_le (SchedSts0 := S2) Stay (fd Dp) (fd Dq).
  Proof.
    intros HIp HIq Egf Hle r2' Hr2'.
    pose proof (morph_run S2 S1 g Inv2 HsG HfG HbG _ _ HIq Hr2') as Hr2. rewrite Egf in Hr2.
    destruct (Hle _ Hr2) as (r1 & Hr1 & Hrl). exists (λ i, fd (r1 i)).
    split; [exact (morph_run S1 S2 f Inv1 HsF HfF HbF _ _ HIp Hr1)|].
    intros n v Hv. unfold succ_mass in *. rewrite <- (morph_succ S1 S2 f HsF (r1 n)) in Hv.
    destruct (Hrl n v Hv) as (m & Hm). exists m. rewrite (morph_succ S2 S1 g HsG (r2' m)). exact Hm.
  Qed.
End MorphSmyth.

Definition fin {A} (P : A → Prop) : Prop := ∃ l : list A, ∀ x, P x → x ∈ l.

Lemma fin_mono {A} (P Q : A → Prop) : (∀ x, P x → Q x) → fin Q → fin P.
Proof. intros HPQ (l & Hl). exists l. intros x Hx. apply Hl, HPQ, Hx. Qed.

Lemma fin_false {A} : fin (λ _ : A, False).
Proof. exists []. intros x []. Qed.

Lemma fin_eq {A} (a : A) : fin (λ x, x = a).
Proof. exists [a]. intros x ->. by left. Qed.

Lemma fin_elem {A} (l : list A) : fin (λ x, x ∈ l).
Proof. by exists l. Qed.

Lemma fin_uniq {A} (P : A → Prop) : (∀ x y, P x → P y → x = y) → fin P.
Proof.
  intros Hu. destruct (classic (∃ x, P x)) as [(a & Ha)|Hn].
  - exists [a]. intros x Hx. rewrite (Hu x a Hx Ha). by left.
  - exists []. intros x Hx. exfalso. apply Hn. by exists x.
Qed.

Lemma fin_or {A} (P Q : A → Prop) : fin P → fin Q → fin (λ x, P x ∨ Q x).
Proof.
  intros (l1 & H1) (l2 & H2). exists (l1 ++ l2).
  intros x [Hx|Hx]; apply elem_of_app; [left; by apply H1|right; by apply H2].
Qed.

Lemma fin_bind {A B} (P : A → Prop) (Q : A → B → Prop) :
  fin P → (∀ x, P x → fin (Q x)) → fin (λ y, ∃ x, P x ∧ Q x y).
Proof.
  intros (l & Hl) HQ.
  assert (Hall : ∀ l0 : list A, ∃ l' : list B, ∀ x, x ∈ l0 → P x → ∀ y, Q x y → y ∈ l').
  { induction l0 as [|a l0 (l' & IH)].
    - exists []. intros x Hx. by apply elem_of_nil in Hx.
    - destruct (classic (P a)) as [Ha|Ha].
      + destruct (HQ a Ha) as (la & Hla). exists (la ++ l'). intros x Hx HPx y Hy. apply elem_of_app.
        apply elem_of_cons in Hx as [->|Hx]; [left; by apply Hla|right; by apply (IH x)].
      + exists l'. intros x Hx HPx y Hy. apply elem_of_cons in Hx as [->|Hx]; [done|by apply (IH x)]. }
  destruct (Hall l) as (l' & Hl'). exists l'. intros y (x & HPx & Hy). exact (Hl' x (Hl x HPx) HPx y Hy).
Qed.

Lemma fin_img {A B} (f : A → B) (P : A → Prop) : fin P → fin (λ y, ∃ x, P x ∧ y = f x).
Proof. intros HP. apply (fin_bind P (λ x y, y = f x) HP). intros x _. apply fin_eq. Qed.

Lemma fin_lists {A} (P : A → Prop) n : fin P → fin (λ l : list A, length l = n ∧ Forall P l).
Proof.
  intros HP. induction n as [|n IH].
  - apply (fin_mono _ (λ l, l = [])); [|apply fin_eq]. intros [|a l] [Hlen _]; [done|discriminate].
  - apply (fin_mono _ (λ l, ∃ a, P a ∧ ∃ l', (length l' = n ∧ Forall P l') ∧ l = a :: l')).
    + intros [|a l] [Hlen HF]; [discriminate|]. apply Forall_cons in HF as [Ha HF].
      exists a. split; [done|]. exists l. split; [|done]. split; [by injection Hlen|done].
    + apply (fin_bind P _ HP). intros a _. exact (fin_img (cons a) _ IH).
Qed.

Section Konig.
  Context `{WeightLaws} {C Sch : Type} (SS : SchedSts C Sch) (good : dist C → Prop).

  Definition rstep (D D' : dist C) : Prop :=
    (∃ σ, dstep (SchedSts0 := SS) Stay D σ D') ∨ (dstable (SchedSts0 := SS) D ∧ D' = D).

  Definition path (D : dist C) (N : nat) : Prop :=
    ∃ f : nat → dist C, f 0 = D ∧ (∀ i, i < N → rstep (f i) (f (S i))) ∧ ∀ i, i ≤ N → good (f i).

  Lemma path_mono D N M : M ≤ N → path D N → path D M.
  Proof. intros HM (f & Hf0 & Hs & Hg). exists f. split; [done|]. split; intros i Hi; [apply Hs|apply Hg]; lia. Qed.

  Lemma path_succ D N : path D (S N) → ∃ D', rstep D D' ∧ path D' N.
  Proof.
    intros (f & Hf0 & Hs & Hg). exists (f 1). split.
    - rewrite <- Hf0. apply Hs. lia.
    - exists (λ i, f (S i)). split; [done|]. split; intros i Hi; [apply Hs|apply Hg]; lia.
  Qed.

  Lemma bound_list (l : list (dist C)) (P : dist C → Prop) :
    (∀ x, x ∈ l → P x → ∃ N, ¬ path x N) → ∃ M, ∀ x, x ∈ l → P x → ¬ path x M.
  Proof.
    induction l as [|x l IH]; intros Hl.
    - exists 0. intros y Hy. by apply elem_of_nil in Hy.
    - destruct IH as (M1 & HM1); [intros y Hy; apply Hl; by right|].
      destruct (classic (P x)) as [Hx|Hx].
      + assert (Hx0 : x ∈ x :: l) by by left.
        destruct (Hl x Hx0 Hx) as (N & HN). exists (Nat.max N M1).
        intros y Hy HPy Hp. apply elem_of_cons in Hy as [->|Hy].
        * apply HN. apply (path_mono _ (Nat.max N M1)); [lia|done].
        * apply (HM1 y Hy HPy). apply (path_mono _ (Nat.max N M1)); [lia|done].
      + exists M1. intros y Hy HPy. apply elem_of_cons in Hy as [->|Hy]; [done|exact (HM1 y Hy HPy)].
  Qed.

  Hypothesis Hfin : ∀ D, ∃ l : list (dist C), ∀ D', rstep D D' → D' ∈ l.

  Lemma path_step D : (∀ N, path D N) → ∃ D', rstep D D' ∧ ∀ N, path D' N.
  Proof.
    intros Hp. destruct (Hfin D) as (l & Hl). apply NNPP. intros Hn.
    destruct (bound_list l (rstep D)) as (M & HM).
    { intros x _ Hx. apply NNPP. intros Hc. apply Hn. exists x. split; [done|].
      intros N. apply NNPP. intros HN. apply Hc. by exists N. }
    destruct (path_succ D M (Hp (S M))) as (D' & Hs & HD'). exact (HM D' (Hl D' Hs) Hs HD').
  Qed.

  Theorem konig (DC : dep_choice) D :
    (∀ N, path D N) → ∃ r, is_run (SchedSts0 := SS) Stay D r ∧ ∀ i, good (r i).
  Proof.
    intros Hp.
    destruct (DC _ (λ x y, (∀ N, path x N) → rstep x y ∧ ∀ N, path y N) D) as (f & Hf0 & Hf).
    { intros x. destruct (classic (∀ N, path x N)) as [Hx|Hx].
      - destruct (path_step x Hx) as (y & Hy). exists y. intros _. exact Hy.
      - exists x. intros Hc. by exfalso. }
    assert (Hall : ∀ i N, path (f i) N).
    { intros i. induction i as [|i IH]; [by rewrite Hf0|]. exact (proj2 (Hf i IH)). }
    exists f. split; [split; [done|]|].
    - intros i. destruct (proj1 (Hf i (Hall i))) as [Hs|Hs]; [by left|by right].
    - intros i. destruct (Hall i 0) as (g & Hg0 & _ & Hg). rewrite <- Hg0. apply Hg. lia.
  Qed.
End Konig.

Section Branching.
  Context `{WeightLaws} {C Sch : Type} (SS : SchedSts C Sch).

  Definition lifts (D X : dist C) : Prop :=
    ∃ Δs, Forall2 (λ cρ Δ, Δ = rest (SchedSts0 := SS) Stay cρ.1 cρ.2 ∨ ∃ σ, sstep (SchedSts := SS) cρ.2 cρ.1 σ Δ) D Δs
          ∧ X = dsum Δs.

  Hypothesis Hc : ∀ ρ c, fin (λ Δ, ∃ σ, sstep (SchedSts := SS) ρ c σ Δ).

  Lemma lifts_fin D : fin (lifts D).
  Proof.
    induction D as [|[c ρ] D IH].
    - apply (fin_mono _ (λ X, X = [])); [|apply fin_eq]. intros X (Δs & HF & ->).
      apply Forall2_nil_inv_l in HF. by subst.
    - apply (fin_mono _ (λ X, ∃ Δ, (Δ = rest (SchedSts0 := SS) Stay c ρ ∨ ∃ σ, sstep (SchedSts := SS) ρ c σ Δ)
                               ∧ ∃ X', lifts D X' ∧ X = Δ ++ X')).
      + intros X (Δs & HF & ->). apply Forall2_cons_inv_l in HF as (Δ & Δs' & Hd & HF & ->).
        exists Δ. split; [exact Hd|]. exists (dsum Δs'). split; [by exists Δs'|done].
      + apply fin_bind; [apply fin_or; [apply fin_eq|apply Hc]|]. intros Δ _. exact (fin_img (app Δ) _ IH).
  Qed.

  Lemma rstep_fin D : fin (rstep SS D).
  Proof.
    apply (fin_mono _ (λ X, X = D ∨ lifts D X)); [|apply fin_or; [apply fin_eq|apply lifts_fin]].
    intros D' [(σ & _ & Δs & HF & ->)|[_ ->]]; [right|by left]. exists Δs. split; [|done].
    eapply Forall2_impl; [exact HF|]. intros [c ρ] Δ [[_ Hs]|[_ ->]]; simpl; [right; by exists σ|by left].
  Qed.
End Branching.

Section Replay.
  Context `{WeightLaws} {C Sch : Type} (SI SJ : SchedSts C Sch).
  Notation FI := (psuccess (SchedSts := SI)).
  Notation FJ := (psuccess (SchedSts := SJ)).
  Notation sI := (sstep (SchedSts := SI)).
  Notation sJ := (sstep (SchedSts := SJ)).
  Notation stepI := (comp_step (SchedSts0 := SI) Stay).
  Notation stepJ := (comp_step (SchedSts0 := SJ) Stay).
  Notation dstepI := (dstep (SchedSts0 := SI) Stay).
  Notation dstepJ := (dstep (SchedSts0 := SJ) Stay).
  Notation dmovesI := (dmoves (SchedSts0 := SI)).
  Notation dmovesJ := (dmoves (SchedSts0 := SJ)).
  Notation dstableI := (dstable (SchedSts0 := SI)).
  Notation dstableJ := (dstable (SchedSts0 := SJ)).
  Hypothesis Hmono : ∀ ρ c σ Δ, sI ρ c σ Δ → sJ ρ c σ Δ.
  Hypothesis Hfree : ∀ ρ c σ Δ, sJ ρ c σ Δ → ¬ FJ c → sI ρ c σ Δ ∨ ∀ y, y ∈ Δ → FJ y.1.
  Hypothesis HS : ∀ c, FI c → FJ c.
  Hypothesis HmI : ∀ ρ c σ Δ, sI ρ c σ Δ → dmass Δ = mass ρ.
  Hypothesis HmJ : ∀ ρ c σ Δ, sJ ρ c σ Δ → dmass Δ = mass ρ.

  Inductive Sim : dist C → dist C → Prop :=
  | Sim_nil : Sim [] []
  | Sim_same x D D' : ¬ FJ x.1 → Sim D D' → Sim (x :: D) (x :: D')
  | Sim_frz F Θ D D' : (∀ x, x ∈ F → FJ x.1) → dmass F = dmass Θ → Sim D D' → Sim (F ++ D) (Θ ++ D').

  Lemma Sim_app A B E G : Sim A B → Sim E G → Sim (A ++ E) (B ++ G).
  Proof.
    induction 1 as [|x D D' Hx _ IH|F Θ D D' HF Hm _ IH]; intros HE.
    - done.
    - rewrite <- !app_comm_cons. by constructor; [|apply IH].
    - rewrite <- !app_assoc. by constructor; [| |apply IH].
  Qed.

  Lemma Sim_refl D : Sim D D.
  Proof.
    induction D as [|x D IH]; [constructor|].
    destruct (decide (FJ x.1)) as [E|E].
    - apply (Sim_frz [x] [x] D D); [|done|done]. intros y ->%list_elem_of_singleton. done.
    - by constructor.
  Qed.

  Lemma Sim_frz' F Θ : (∀ x, x ∈ F → FJ x.1) → dmass F = dmass Θ → Sim F Θ.
  Proof.
    intros HF Hm. rewrite <- (app_nil_r F), <- (app_nil_r Θ). by constructor; [| |constructor].
  Qed.

  Lemma Sim_mem D D' x : Sim D D' → x ∈ D → ¬ FJ x.1 → x ∈ D'.
  Proof.
    induction 1 as [|y D D' Hy _ IH|F Θ D D' HF _ _ IH]; intros Hx Hs.
    - done.
    - apply elem_of_cons in Hx as [->|Hx]; [by left|right; by apply IH].
    - apply elem_of_app in Hx as [Hx|Hx].
      + apply HF in Hx. done.
      + apply elem_of_app. right. by apply IH.
  Qed.

  Lemma Sim_succ D D' : Sim D D' → dmass_of FI D' ≤ₚ dmass_of FJ D.
  Proof.
    induction 1 as [|x D D' Hx _ IH|F Θ D D' HF Hm _ IH].
    - reflexivity.
    - simpl. rewrite decide_False; [rewrite decide_False; [done|done]|]. intros Hs%HS. done.
    - rewrite !dmass_of_app. apply prob_add_mono2; [|done].
      rewrite (dmass_of_all FJ F HF), Hm. apply dmass_of_le.
  Qed.

  Lemma point_mass (c : C) ρ : dmass (rest Stay c ρ) = mass ρ.
  Proof. simpl. apply prob_add_zero_r. Qed.

  Lemma stepI_mass ρ c σ Δ : stepI ρ c σ Δ → dmass Δ = mass ρ.
  Proof.
    intros [(_ & Hs)|(_ & ->)]; [by eapply HmI|apply (point_mass c ρ)].
  Qed.

  Lemma stepI_exists ρ c σ : ∃ Δ, stepI ρ c σ Δ.
  Proof.
    destruct (decide (FI c)) as [Es|Es].
    - eexists. right. split; [left; exact Es|done].
    - destruct (classic (∃ Δ, sI ρ c σ Δ)) as [(Δ & Hz)|Hz].
      + exists Δ. left. by split.
      + eexists. right. split; [right; intros Δ' H'; apply Hz; by exists Δ'|done].
  Qed.

  Lemma stepsI_exist (Θ : dist C) σ : ∃ Δs, Forall2 (λ x Δ, stepI x.2 x.1 σ Δ) Θ Δs.
  Proof.
    induction Θ as [|x Θ (Δs & IH)]; [by exists []; constructor|].
    destruct (stepI_exists x.2 x.1 σ) as (Δ & Hz). exists (Δ :: Δs). by constructor.
  Qed.

  Lemma stepsI_mass (Θ : dist C) σ Δs :
    Forall2 (λ x Δ, stepI x.2 x.1 σ Δ) Θ Δs → dmass (dsum Δs) = dmass Θ.
  Proof.
    induction 1 as [|x Δ Θ Δs Hx _ IH]; [done|]. rewrite dsum_cons, dmass_app, IH.
    by rewrite (stepI_mass _ _ _ _ Hx).
  Qed.

  Lemma frozen_steps (F : dist C) σ Δs :
    (∀ x, x ∈ F → FJ x.1) → Forall2 (λ x Δ, stepJ x.2 x.1 σ Δ) F Δs → dsum Δs = F.
  Proof.
    intros HF Hz. induction Hz as [|[c ρ] Δ F Δs Hx _ IH]; [done|]. rewrite dsum_cons.
    assert (Hc : FJ c) by (apply (HF (c, ρ)); by left).
    destruct Hx as [(Hns & _)|(_ & ->)]; [exfalso; by apply Hns|]. simpl.
    f_equal. apply IH. intros y Hy. apply HF. by right.
  Qed.

  Lemma Sim_elem x σ Δ :
    ¬ FJ x.1 → stepJ x.2 x.1 σ Δ → ∃ Δ', stepI x.2 x.1 σ Δ' ∧ Sim Δ Δ'.
  Proof.
    intros Hx [(_ & Hs)|(Hst & ->)].
    - destruct (Hfree _ _ _ _ Hs Hx) as [HI|HF].
      + exists Δ. split; [|apply Sim_refl]. left. split; [|exact HI]. intros Hs'%HS. done.
      + destruct (stepI_exists x.2 x.1 σ) as (Δ' & Hz). exists Δ'. split; [done|].
        apply Sim_frz'; [exact HF|]. rewrite (stepI_mass _ _ _ _ Hz). by eapply HmJ.
    - exists (rest (SchedSts0 := SI) Stay x.1 x.2). split.
      + right. split; [|done]. right. intros Δ' H'. destruct Hst as [Hs|Hno]; [done|].
        by apply (Hno Δ'), Hmono.
      + apply Sim_refl.
  Qed.

  Lemma Sim_core D D' σ Δs :
    Sim D D' → Forall2 (λ x Δ, stepJ x.2 x.1 σ Δ) D Δs →
    ∃ Δs', Forall2 (λ x Δ, stepI x.2 x.1 σ Δ) D' Δs' ∧ Sim (dsum Δs) (dsum Δs').
  Proof.
    intros Hz. revert Δs. induction Hz as [|x D D' Hx _ IH|F Θ D D' HF Hm _ IH]; intros Δs HΔ.
    - inversion HΔ; subst. exists []. split; constructor.
    - inversion HΔ as [|? Δ ? Δs0 Hs Hrest]; subst.
      destruct (IH _ Hrest) as (Δs' & Hs' & HSim). destruct (Sim_elem x σ Δ Hx Hs) as (Δ' & H' & HΔ').
      exists (Δ' :: Δs'). split; [by constructor|]. rewrite !dsum_cons. by apply Sim_app.
    - apply Forall2_app_inv_l in HΔ as (Δ1 & Δ2 & Ha & Hb & ->).
      destruct (IH _ Hb) as (Δs' & Hs' & HSim). destruct (stepsI_exist Θ σ) as (Δs1 & HΘ).
      exists (Δs1 ++ Δs'). split; [by apply Forall2_app|]. rewrite !dsum_app.
      rewrite (frozen_steps F σ Δ1 HF Ha). apply Sim_app; [|done]. apply Sim_frz'; [exact HF|].
      rewrite Hm. symmetry. exact (stepsI_mass Θ σ Δs1 HΘ).
  Qed.

  Lemma Sim_step D D' σ D2 :
    Sim D D' → dstepJ D σ D2 → dmovesI D' σ → ∃ D2', dstepI D' σ D2' ∧ Sim D2 D2'.
  Proof.
    intros Hz (_ & Δs & HΔ & ->) Hm. destruct (Sim_core _ _ _ _ Hz HΔ) as (Δs' & Hs & HSim).
    exists (dsum Δs'). split; [|done]. split; [done|]. by exists Δs'.
  Qed.

  Lemma Sim_stable D D' σ Δs :
    Sim D D' → (∀ x, x ∈ D → ¬ FJ x.1 → ∀ Δ, ¬ sJ x.2 x.1 σ Δ) →
    Forall2 (λ x Δ, stepI x.2 x.1 σ Δ) D' Δs → Sim D (dsum Δs).
  Proof.
    intros Hz. revert Δs. induction Hz as [|x D D' Hx _ IH|F Θ D D' HF Hm _ IH]; intros Δs Hst HΔ.
    - inversion HΔ; subst. apply Sim_nil.
    - inversion HΔ as [|? Δ ? Δs0 Hs Hrest]; subst. rewrite dsum_cons.
      destruct Hs as [(_ & Hs)|(_ & ->)].
      + exfalso. assert (Hmem : x ∈ x :: D) by (by left). exact (Hst x Hmem Hx Δ (Hmono _ _ _ _ Hs)).
      + destruct x as [c ρ]. change (Sim ((c, ρ) :: D) ((c, ρ) :: dsum Δs0)).
        apply Sim_same; [done|]. apply IH; [|done]. intros y Hy. apply Hst. by right.
    - apply Forall2_app_inv_l in HΔ as (Δ1 & Δ2 & Ha & Hb & ->). rewrite dsum_app.
      constructor; [done| |].
      + rewrite Hm. symmetry. exact (stepsI_mass Θ σ Δ1 Ha).
      + apply IH; [|done]. intros y Hy. apply Hst. apply elem_of_app. by right.
  Qed.

  Definition live (D : dist C) : nat := length (filter (λ x, ¬ FJ x.1) D).

  Lemma live_app A B : live (A ++ B) = live A + live B.
  Proof. unfold live. by rewrite filter_app, length_app. Qed.

  Lemma live_zero Δ : (∀ y, y ∈ Δ → FJ y.1) → live Δ = 0.
  Proof.
    induction Δ as [|y Δ IH]; intros HF; [done|]. unfold live in *. rewrite filter_cons_False.
    - apply IH. intros z Hz. apply HF. by right.
    - intros Hn. apply Hn, HF. by left.
  Qed.

  Lemma live_elem x σ Δ :
    (¬ FJ x.1 → ∀ Δ', ¬ sI x.2 x.1 σ Δ') → stepJ x.2 x.1 σ Δ →
    live Δ ≤ live [x] ∧ ((¬ FJ x.1 ∧ ∃ Δ', sJ x.2 x.1 σ Δ') → live Δ < live [x]).
  Proof.
    intros Hno [(Hns & Hs)|(Hst & ->)].
    - destruct (Hfree _ _ _ _ Hs Hns) as [HI|HF]; [exfalso; by apply (Hno Hns Δ)|].
      assert (Hz0 : live Δ = 0) by (by apply live_zero).
      assert (Ha : live [x] = 1).
      { unfold live. rewrite filter_cons_True; [done|exact Hns]. }
      rewrite Hz0, Ha. split; [lia|intros _; lia].
    - destruct x as [c ρ]. split; [exact (Nat.le_refl _)|]. intros (Hx & Δ' & Hz'). exfalso. destruct Hst as [Hs|Hno'].
      + done.
      + exact (Hno' Δ' Hz').
  Qed.

  Lemma live_steps D σ Δs :
    (∀ x, x ∈ D → ¬ FJ x.1 → ∀ Δ', ¬ sI x.2 x.1 σ Δ') →
    Forall2 (λ x Δ, stepJ x.2 x.1 σ Δ) D Δs →
    live (dsum Δs) ≤ live D ∧ (dmovesJ D σ → live (dsum Δs) < live D).
  Proof.
    intros Hno Hz. induction Hz as [|x Δ D Δs Hx _ IH].
    - split; [done|]. intros (c & ρ & Δ & Hin & _). by apply elem_of_nil in Hin.
    - assert (HlD : live (x :: D) = live [x] + live D).
      { change (x :: D) with ([x] ++ D). apply live_app. }
      destruct IH as [IH1 IH2]; [intros y Hy; apply Hno; by right|].
      assert (Hmem : x ∈ x :: D) by (by left).
      destruct (live_elem x σ Δ (Hno x Hmem) Hx) as [Ha Hb].
      rewrite dsum_cons, live_app, HlD. split; [lia|].
      intros (c & ρ & Δ0 & Hin & Hns & Hs). apply elem_of_cons in Hin as [Hin|Hin].
      + subst x. specialize (Hb (conj Hns (ex_intro _ Δ0 Hs))). simpl in *. lia.
      + assert (live (dsum Δs) < live D); [|lia]. apply IH2. by exists c, ρ, Δ0.
  Qed.

  Lemma no_moves_rest D' σ Δs :
    (∀ c ρ Δ, (c, ρ) ∈ D' → ¬ (¬ FI c ∧ sI ρ c σ Δ)) →
    Forall2 (λ x Δ, stepI x.2 x.1 σ Δ) D' Δs → dsum Δs = D'.
  Proof.
    intros Hno Hz. induction Hz as [|[c ρ] Δ D' Δs Hx _ IH]; [done|]. rewrite dsum_cons.
    destruct Hx as [(Hns & Hs)|(_ & ->)].
    - exfalso. apply (Hno c ρ Δ); [by left|]. by split.
    - simpl. f_equal. apply IH. intros c' ρ' Δ' Hin. apply Hno. by right.
  Qed.

  Lemma Sim_skip D D' σ D2 :
    Sim D D' → dstepJ D σ D2 → ¬ dmovesI D' σ → Sim D2 D' ∧ live D2 < live D.
  Proof.
    intros Hz (Hm & Δs & HΔ & ->) Hno. destruct (Sim_core _ _ _ _ Hz HΔ) as (Δs' & Hs & HSim).
    assert (Hno' : ∀ c ρ Δ, (c, ρ) ∈ D' → ¬ (¬ FI c ∧ sI ρ c σ Δ)).
    { intros c ρ Δ Hin [Hn Hc]. apply Hno. exists c, ρ, Δ. by split; [|split]. }
    rewrite (no_moves_rest D' σ Δs' Hno' Hs) in HSim. split; [done|].
    apply (live_steps D σ Δs); [|done|done]. intros [c ρ] Hx Hs' Δ' Hc.
    apply (Hno' c ρ Δ'); [by eapply (Sim_mem D D')|]. split; [|exact Hc].
    intros Hsc%HS. done.
  Qed.

  Lemma walk r : is_run (SchedSts0 := SJ) Stay (r 0) r →
    ∀ k i D', live (r i) = k → Sim (r i) D' → ¬ dstableI D' →
      ∃ i2 D2 σ, i ≤ i2 ∧ dstepI D' σ D2 ∧ Sim (r i2) D2.
  Proof.
    intros [_ Hr] k. induction k as [k IH] using lt_wf_ind. intros i D' Hk Hz Hns.
    assert (Hmv : ∃ σ, dmovesI D' σ).
    { apply not_all_not_ex. intros Hall. apply Hns. intros σ. apply Hall. }
    destruct (Hr i) as [(σ & Hst)|(Hst & Eq)].
    - destruct (classic (dmovesI D' σ)) as [Hm|Hm].
      + destruct (Sim_step _ _ _ _ Hz Hst Hm) as (D2 & Ha & Hb).
        exists (S i), D2, σ. split; [lia|]. by split.
      + destruct (Sim_skip _ _ _ _ Hz Hst Hm) as (Ha & Hb).
        destruct (IH (live (r (S i))) ltac:(lia) (S i) D' eq_refl Ha Hns) as (i2 & D2 & σ' & Hi & Hs & HS2).
        exists i2, D2, σ'. split; [lia|]. by split.
    - destruct Hmv as (σ & Hm). destruct (stepsI_exist D' σ) as (Δs & HΔ).
      exists i, (dsum Δs), σ. split; [done|]. split.
      + split; [done|]. by exists Δs.
      + apply (Sim_stable _ D' σ); [done| |done]. intros x Hx Hxs Δ Hc. apply (Hst σ).
        destruct x as [c ρ]. exists c, ρ, Δ. by split; [|split].
  Qed.

  Theorem replay (DC : dep_choice) D0 D0' r :
    is_run (SchedSts0 := SJ) Stay D0 r → Sim D0 D0' →
    ∃ r', is_run (SchedSts0 := SI) Stay D0' r' ∧
      ∀ n, ∃ m, succ_mass (SchedSts0 := SI) r' n ≤ₚ succ_mass (SchedSts0 := SJ) r m.
  Proof.
    intros Hr HSim. assert (Hr0 : is_run (SchedSts0 := SJ) Stay (r 0) r).
    { destruct Hr as [E Hr]. split; [done|exact Hr]. }
    set (N := λ x y : nat * dist C, Sim (r x.1) x.2 →
      Sim (r y.1) y.2 ∧ ((∃ σ, dstepI x.2 σ y.2) ∨ (dstableI x.2 ∧ y.2 = x.2))).
    destruct (DC _ N (0, D0')) as (f & Hf0 & Hf).
    { intros [i D']. destruct (classic (Sim (r i) D')) as [Hz|Hz].
      - destruct (classic (dstableI D')) as [Hs|Hs].
        + exists (i, D'). intros _. split; [done|]. by right.
        + destruct (walk r Hr0 _ i D' eq_refl Hz Hs) as (i2 & D2 & σ & _ & Ha & Hb).
          exists (i2, D2). intros _. split; [done|]. left. by exists σ.
      - exists (0, []). intros H'. by exfalso. }
    assert (Hinv : ∀ n, Sim (r (f n).1) (f n).2).
    { induction n as [|n IH]; [|by apply Hf]. rewrite Hf0. simpl. destruct Hr as [-> _]. done. }
    exists (λ n, (f n).2). split.
    - split; [by rewrite Hf0|]. intros n. destruct (Hf n (Hinv n)) as (_ & [Hs|Hs]); [by left|by right].
    - intros n. exists (f n).1. exact (Sim_succ _ _ (Hinv n)).
  Qed.
End Replay.

Class MenuSts (C Sch A Off : Type) `{Weights} := MkMenuSts {
    mnode : C → list A;
    moffer : A → Off;
    mstep : (list A → Off → Prop) → weight → C → Sch → dist C → Prop;
    mfree : Sch → Prop;
    msch : Sch;
    mstep_free J ρ c σ Δ : mfree σ → mstep J ρ c σ Δ →
      (∀ J', mstep J' ρ c σ Δ) ∧ ∀ y, y ∈ Δ → mnode y.1 = mnode c;
    mstep_off J ρ c σ Δ : ¬ mfree σ → mstep J ρ c σ Δ →
      ∃ o, J (mnode c) o ∧ (∀ J', J' (mnode c) o → mstep J' ρ c σ Δ) ∧
        ∀ y, y ∈ Δ → ∃ a, moffer a = o ∧ mnode y.1 = mnode c ++ [a];
    mstep_mass J ρ c σ Δ : mstep J ρ c σ Δ → dmass Δ = mass ρ;
    mstep_nonempty J ρ c σ Δ : ρ ≠ weight_zero → mstep J ρ c σ Δ → Δ ≠ [];
    mstep_nonzero J ρ c σ Δ : ρ ≠ weight_zero → mstep J ρ c σ Δ → ∀ x, x ∈ Δ → x.2 ≠ weight_zero;
  }.

Section Canonical.
  Context `{WeightLaws} {C Sch A Off : Type} `{M : !MenuSts C Sch A Off} (Ok : Off → Prop).
  Notation node := (list A).

  Definition mdlts (J : node → Off → Prop) (S : node → bool) : SchedSts C Sch :=
    {| sstep := mstep J; psuccess := λ c, S (mnode c) = true |}.

  Definition mext_closed (S : node → bool) : Prop := ∀ n a, S n = true → S (n ++ [a]) = true.

  Definition malt_pre (Dp Dq : dist C) : Prop :=
    ∀ I S, (∀ n o, I n o → Ok o) → mext_closed S → smyth_le (SchedSts0 := mdlts I S) Stay Dp Dq.

  Definition single (n : node) (o : Off) : node → Off → Prop := λ n' o', n' = n ∧ o' = o.

  Lemma mstep_cell J ρ c σ Δ :
    mstep J ρ c σ Δ →
    ((∀ J', mstep J' ρ c σ Δ) ∧ ∀ y, y ∈ Δ → mnode y.1 = mnode c)
    ∨ ∃ o, J (mnode c) o ∧ (∀ J', J' (mnode c) o → mstep J' ρ c σ Δ) ∧
        ∀ y, y ∈ Δ → ∃ a, moffer a = o ∧ mnode y.1 = mnode c ++ [a].
  Proof.
    intros Hs. destruct (classic (mfree σ)) as [Hf|Hf].
    - left. exact (mstep_free _ _ _ _ _ Hf Hs).
    - right. exact (mstep_off _ _ _ _ _ Hf Hs).
  Qed.

  Lemma mstep_mono (I J : node → Off → Prop) ρ c σ Δ :
    (∀ n o, I n o → J n o) → mstep I ρ c σ Δ → mstep J ρ c σ Δ.
  Proof.
    intros HIJ Hs. destruct (mstep_cell _ _ _ _ _ Hs) as [[Hall _]|(o & Ho & HJ & _)]; [apply Hall|].
    apply HJ, HIJ, Ho.
  Qed.

  Definition run_word (I : node → Off → Prop) (S : node → bool) (D : dist C)
      (r : nat → dist C) (w : nat → Sch) : Prop :=
    r 0 = D ∧ ∀ i, dstep (SchedSts0 := mdlts I S) Stay (r i) (w i) (r (Datatypes.S i))
                 ∨ (dstable (SchedSts0 := mdlts I S) (r i) ∧ r (Datatypes.S i) = r i).

  Lemma is_run_word (DC : dep_choice) I S D r :
    is_run (SchedSts0 := mdlts I S) Stay D r → ∃ w, run_word I S D r w.
  Proof.
    intros [Hr0 Hr].
    set (N := λ x y : nat * Sch, y.1 = Datatypes.S x.1 ∧
      (dstep (SchedSts0 := mdlts I S) Stay (r x.1) y.2 (r (Datatypes.S x.1))
       ∨ (dstable (SchedSts0 := mdlts I S) (r x.1) ∧ r (Datatypes.S x.1) = r x.1))).
    destruct (DC _ N (0, msch)) as (f & Hf0 & Hf).
    { intros [i it]. destruct (Hr i) as [(σ & Hs)|Hs].
      - exists (Datatypes.S i, σ). split; [done|]. by left.
      - exists (Datatypes.S i, msch). split; [done|]. by right. }
    assert (Hidx : ∀ n, (f n).1 = n).
    { induction n as [|n IH]; [by rewrite Hf0|]. rewrite (proj1 (Hf n)). by rewrite IH. }
    exists (λ i, (f (Datatypes.S i)).2). split; [done|]. intros i.
    pose proof (proj2 (Hf i)) as Hs. by rewrite Hidx in Hs.
  Qed.

  Section Star.
    Context (I : node → Off → Prop) (S : node → bool) (r : nat → dist C) (w : nat → Sch).

    Definition refused (n : node) (o : Off) : Prop :=
      ∃ i c ρ, (c, ρ) ∈ r i ∧ S (mnode c) = false ∧
        ((dstep (SchedSts0 := mdlts I S) Stay (r i) (w i) (r (Datatypes.S i))
          ∧ (∀ Δ, ¬ mstep I ρ c (w i) Δ) ∧ ∃ Δ, mstep (single n o) ρ c (w i) Δ)
         ∨ (dstable (SchedSts0 := mdlts I S) (r i) ∧ ∃ σ Δ, mstep (single n o) ρ c σ Δ)).

    Definition Jstar (n : node) (o : Off) : Prop := I n o ∨ (Ok o ∧ ¬ refused n o).

    Definition crossed (n : node) : Prop :=
      ∃ m a m2, n = m ++ [a] ++ m2 ∧ Jstar m (moffer a) ∧ ¬ I m (moffer a).

    Definition Sstar (n : node) : bool :=
      S n || (if excluded_middle_informative (crossed n) then true else false).

    Lemma Sstar_S n : S n = true → Sstar n = true.
    Proof. unfold Sstar. intros ->. done. Qed.

    Lemma Sstar_crossed n : crossed n → Sstar n = true.
    Proof. unfold Sstar. intros Hc. destruct (excluded_middle_informative (crossed n)); [|done]. apply orb_true_r. Qed.

    Lemma Sstar_inv n : Sstar n = true → S n = true ∨ crossed n.
    Proof.
      unfold Sstar. destruct (S n); [by left|]. destruct (excluded_middle_informative (crossed n)); [by right|done].
    Qed.

    Lemma Sstar_ext : mext_closed S → mext_closed Sstar.
    Proof.
      intros HS n a [Hs|(m & b & m2 & -> & Hc)]%Sstar_inv.
      - by apply Sstar_S, HS.
      - apply Sstar_crossed. exists m, b, (m2 ++ [a]). split; [|done]. by rewrite !app_assoc.
    Qed.

    Definition visited_ok (n : node) : Prop := ∀ m a m2, n = m ++ [a] ++ m2 → I m (moffer a).

    Lemma visited_step ρ c σ Δ y :
      visited_ok (mnode c) → mstep I ρ c σ Δ → y ∈ Δ → visited_ok (mnode y.1).
    Proof.
      intros Hv Hc Hy. destruct (mstep_cell _ _ _ _ _ Hc) as [[_ Hn]|(o & Ho & _ & Ht)].
      - rewrite (Hn y Hy). exact Hv.
      - destruct (Ht y Hy) as (a & <- & Ey). intros m b m2 Em. rewrite Ey in Em.
        destruct m2 as [|z m2 _] using rev_ind.
        + simpl in Em. apply app_inj_tail in Em as [<- <-]. done.
        + rewrite !app_assoc in Em. apply app_inj_tail in Em as [Em ->]. apply (Hv m b m2). rewrite <- !app_assoc in Em. done.
    Qed.

    Hypothesis Hrun : run_word I S (r 0) r w.
    Hypothesis Hinit : ∀ x, x ∈ r 0 → visited_ok (mnode x.1).

    Lemma visited_run i x : x ∈ r i → visited_ok (mnode x.1).
    Proof.
      revert x. induction i as [|i IH]; [exact Hinit|]. intros x Hx.
      destruct (proj2 Hrun i) as [(_ & Δs & HΔ & Eq)|(_ & Eq)]; [|rewrite Eq in Hx; by apply IH].
      rewrite Eq in Hx. clear Eq.
      assert (Hall : ∀ y Δ, y ∈ r i → comp_step (SchedSts0 := mdlts I S) Stay y.2 y.1 (w i) Δ → x ∈ Δ → visited_ok (mnode x.1)).
      { intros [c ρ] Δ Hy [(_ & Hs)|(_ & ->)] Hin.
        - exact (visited_step ρ c (w i) Δ x (IH (c, ρ) Hy) Hs Hin).
        - apply list_elem_of_singleton in Hin. subst x. exact (IH (c, ρ) Hy). }
      revert HΔ Hx Hall. generalize (r i) as D. intros D HΔ. induction HΔ as [|y Δ D Δs Hy _ IH2]; intros Hx Hall.
      - by apply elem_of_nil in Hx.
      - rewrite dsum_cons in Hx. apply elem_of_app in Hx as [Hx|Hx].
        + apply (Hall y Δ); [by left|done|done].
        + apply IH2; [done|]. intros z Δ' Hz. apply Hall. by right.
    Qed.

    Lemma Sstar_visited i c ρ : (c, ρ) ∈ r i → Sstar (mnode c) = S (mnode c).
    Proof.
      intros Hc. pose proof (visited_run i (c, ρ) Hc) as Hv. simpl in Hv.
      destruct (Sstar (mnode c)) eqn:Es.
      - apply Sstar_inv in Es as [Es|(m & a & m2 & Em & _ & Hn)]; [done|]. exfalso. apply Hn. by apply (Hv m a m2).
      - destruct (S (mnode c)) eqn:E; [|done]. rewrite (Sstar_S _ E) in Es. done.
    Qed.

    Lemma no_star_move i c ρ σ Δ :
      (c, ρ) ∈ r i → S (mnode c) = false → mstep Jstar ρ c σ Δ →
      (∀ Δ', ¬ mstep I ρ c σ Δ') →
      ((dstep (SchedSts0 := mdlts I S) Stay (r i) (w i) (r (Datatypes.S i)) ∧ σ = w i)
       ∨ dstable (SchedSts0 := mdlts I S) (r i)) → False.
    Proof.
      intros Hc Hs Hstep Hno Hact. destruct (mstep_cell _ _ _ _ _ Hstep) as [[Hall _]|(o & Ho & HJ & _)].
      - by apply (Hno Δ), Hall.
      - destruct Ho as [HI|[_ Hnr]]; [by apply (Hno Δ), HJ|]. apply Hnr. exists i, c, ρ. split; [done|]. split; [done|].
        assert (Hsg : mstep (single (mnode c) o) ρ c σ Δ) by (apply HJ; done).
        destruct Hact as [[Ha ->]|Ha].
        + left. split; [done|]. split; [done|]. by exists Δ.
        + right. split; [done|]. by exists σ, Δ.
    Qed.

    Lemma run_star : run_word Jstar Sstar (r 0) r w.
    Proof.
      split; [done|]. intros i. destruct (proj2 Hrun i) as [Ha|(Ha & Eq)].
      - left. destruct Ha as (Hm & Δs & HΔ & Eq). split.
        + destruct Hm as (c & ρ & Δ & Hin & Hns & Hs). exists c, ρ, Δ. split; [done|]. split.
          * change (¬ Sstar (mnode c) = true). rewrite (Sstar_visited i c ρ Hin). exact Hns.
          * apply (mstep_mono I); [intros n o Hn; by left|exact Hs].
        + exists Δs. split; [|done]. refine (Forall2_mem_impl _ _ _ _ HΔ _). intros [c ρ] Δ Hin _ Hstep.
          simpl in *. pose proof (Sstar_visited i c ρ Hin) as ES. destruct Hstep as [(Hns & Hs)|(Hst & ->)].
          * left. split.
            { change (¬ Sstar (mnode c) = true). rewrite ES. exact Hns. }
            apply (mstep_mono I); [intros n o Hn; by left|exact Hs].
          * right. split; [|done]. destruct (S (mnode c)) eqn:E.
            { left. change (Sstar (mnode c) = true). by rewrite ES. }
            right. intros Δ' Hc. destruct Hst as [Hs|Hno]; [change (S (mnode c) = true) in Hs; congruence|].
            apply (no_star_move i c ρ (w i) Δ' Hin E Hc Hno). left. split; [|done].
            split; [exact Hm|]. exists Δs. split; [exact HΔ|exact Eq].
      - right. split; [|done]. intros σ (c & ρ & Δ & Hin & Hns & Hs).
        assert (ES := Sstar_visited i c ρ Hin). destruct (S (mnode c)) eqn:E.
        + apply Hns. change (Sstar (mnode c) = true). by rewrite ES.
        + refine (no_star_move i c ρ σ Δ Hin E Hs _ (or_intror Ha)). intros Δ' Hc. apply (Ha σ). exists c, ρ, Δ'. split; [done|]. split; [|exact Hc].
          change (¬ S (mnode c) = true). congruence.
    Qed.
    Lemma run_sandwich (J' : node → Off → Prop) (S' : node → bool) :
      (∀ i c ρ, (c, ρ) ∈ r i → S' (mnode c) = S (mnode c)) →
      (∀ i c ρ o, (c, ρ) ∈ r i → S (mnode c) = false → I (mnode c) o → J' (mnode c) o) →
      (∀ i c ρ o, (c, ρ) ∈ r i → S (mnode c) = false → J' (mnode c) o → Jstar (mnode c) o) →
      run_word J' S' (r 0) r w.
    Proof.
      intros HS' HIJ HJs.
      assert (Hup : ∀ i c ρ σ Δ, (c, ρ) ∈ r i → S (mnode c) = false → mstep I ρ c σ Δ → mstep J' ρ c σ Δ).
      { intros i c ρ σ Δ Hin E Hs. destruct (mstep_cell _ _ _ _ _ Hs) as [[Hall _]|(o & Ho & HJ & _)]; [apply Hall|].
        apply HJ. exact (HIJ i c ρ o Hin E Ho). }
      assert (Hdown : ∀ i c ρ σ Δ, (c, ρ) ∈ r i → S (mnode c) = false → mstep J' ρ c σ Δ → mstep Jstar ρ c σ Δ).
      { intros i c ρ σ Δ Hin E Hs. destruct (mstep_cell _ _ _ _ _ Hs) as [[Hall _]|(o & Ho & HJ & _)]; [apply Hall|].
        apply HJ. exact (HJs i c ρ o Hin E Ho). }
      split; [done|]. intros i. destruct (proj2 Hrun i) as [Ha|(Ha & Eq)].
      - left. destruct Ha as (Hm & Δs & HΔ & Eq). split.
        + destruct Hm as (c & ρ & Δ & Hin & Hns & Hs). exists c, ρ, Δ. split; [done|].
          assert (E : S (mnode c) = false) by (destruct (S (mnode c)) eqn:E0; [by destruct Hns|done]). split.
          * change (¬ S' (mnode c) = true). rewrite (HS' i c ρ Hin). exact Hns.
          * exact (Hup i c ρ _ _ Hin E Hs).
        + exists Δs. split; [|done]. refine (Forall2_mem_impl _ _ _ _ HΔ _). intros [c ρ] Δ Hin _ Hstep.
          simpl in *. pose proof (HS' i c ρ Hin) as ES. destruct Hstep as [(Hns & Hs)|(Hst & ->)].
          * left. assert (E : S (mnode c) = false) by (destruct (S (mnode c)) eqn:E0; [by destruct Hns|done]). split.
            { change (¬ S' (mnode c) = true). rewrite ES. exact Hns. }
            exact (Hup i c ρ _ _ Hin E Hs).
          * right. split; [|done]. destruct (S (mnode c)) eqn:E.
            { left. change (S' (mnode c) = true). by rewrite ES. }
            right. intros Δ' Hc. destruct Hst as [Hs|Hno]; [change (S (mnode c) = true) in Hs; congruence|].
            apply (no_star_move i c ρ (w i) Δ' Hin E (Hdown i c ρ _ _ Hin E Hc) Hno). left. split; [|done].
            split; [exact Hm|]. exists Δs. split; [exact HΔ|exact Eq].
      - right. split; [|done]. intros σ (c & ρ & Δ & Hin & Hns & Hs).
        assert (ES := HS' i c ρ Hin). destruct (S (mnode c)) eqn:E.
        + apply Hns. change (S' (mnode c) = true). by rewrite ES.
        + refine (no_star_move i c ρ σ Δ Hin E (Hdown i c ρ _ _ Hin E Hs) _ (or_intror Ha)).
          intros Δ' Hc. apply (Ha σ). exists c, ρ, Δ'. split; [done|]. split; [|exact Hc].
          change (¬ S (mnode c) = true). congruence.
    Qed.
  End Star.

  Definition cells (S : node → bool) (r : nat → dist C) (w : nat → Sch) (n : node) (o : Off) : Prop :=
    ∃ i c ρ Δ, (c, ρ) ∈ r i ∧ S (mnode c) = false ∧ ¬ mfree (w i) ∧ Δ ≠ [] ∧
      mstep (single n o) ρ c (w i) Δ ∧ ∀ y, y ∈ Δ → y ∈ r (Datatypes.S i).

  Section Free.
    Context (I : node → Off → Prop) (S : node → bool) (r : nat → dist C) (w : nat → Sch).
    Hypothesis Hrun : run_word I S (r 0) r w.
    Hypothesis Hinit : ∀ x, x ∈ r 0 → visited_ok I (mnode x.1).
    Hypothesis Hnz : ∀ i x, x ∈ r i → x.2 ≠ weight_zero.
    Hypothesis HokI : ∀ n o, I n o → Ok o.
    Notation U := (cells S r w).

    Lemma cells_sub n o : U n o → I n o.
    Proof.
      intros (i & c & ρ & Δ & _ & _ & Ef & Hne & Hc & Hsub).
      destruct (mstep_off _ _ _ _ _ Ef Hc) as (o' & [En Eo] & _ & Ht). subst o'.
      destruct Δ as [|y Δ]; [done|].
      assert (Hy : y ∈ y :: Δ) by (by left).
      destruct (Ht y Hy) as (a & <- & Ey).
      pose proof (visited_run I S r w Hrun Hinit (Datatypes.S i) y (Hsub y Hy)) as Hv.
      assert (Ei : I (mnode c) (moffer a)) by (apply (Hv (mnode c) a []); exact Ey). by rewrite <- En.
    Qed.

    Lemma U_of_I i c ρ Δ :
      (c, ρ) ∈ r i → S (mnode c) = false → mstep I ρ c (w i) Δ → (∀ y, y ∈ Δ → y ∈ r (Datatypes.S i)) →
      mstep U ρ c (w i) Δ.
    Proof.
      intros Hin Hs Hc Hsub. destruct (classic (mfree (w i))) as [Ef|Ef].
      - exact (proj1 (mstep_free _ _ _ _ _ Ef Hc) U).
      - destruct (mstep_off _ _ _ _ _ Ef Hc) as (o & _ & HJ & _). apply HJ.
        exists i, c, ρ, Δ. split; [done|]. split; [done|]. split; [done|]. split.
        + exact (mstep_nonempty _ _ _ _ _ (Hnz i (c, ρ) Hin) Hc).
        + split; [|done]. by apply HJ.
    Qed.

    Lemma chosen i c ρ Δ :
      dstep (SchedSts0 := mdlts I S) Stay (r i) (w i) (r (Datatypes.S i)) →
      (c, ρ) ∈ r i → S (mnode c) = false → mstep I ρ c (w i) Δ →
      ∃ Δ0, mstep I ρ c (w i) Δ0 ∧ ∀ y, y ∈ Δ0 → y ∈ r (Datatypes.S i).
    Proof.
      intros (_ & Δs & HΔ & Eq) Hin Hs Hc.
      destruct (Forall2_elem_of_l _ _ _ _ HΔ Hin) as (Δ0 & HΔ0 & [(_ & Hc0)|(Hst & _)]).
      - exists Δ0. split; [exact Hc0|]. intros y Hy. rewrite Eq. by apply (elem_of_dsum Δ0).
      - exfalso. destruct Hst as [Hst|Hst]; [change (S (mnode c) = true) in Hst; congruence|exact (Hst Δ Hc)].
    Qed.

    Lemma run_cells : run_word U S (r 0) r w.
    Proof.
      split; [done|]. intros i. destruct (proj2 Hrun i) as [Ha|(Ha & Eq)].
      - left. pose proof Ha as Ha'. destruct Ha as (Hm & Δs & HΔ & Eq). split.
        + destruct Hm as (c & ρ & Δ & Hin & Hns & Hs).
          assert (Hsf : S (mnode c) = false) by (destruct (S (mnode c)) eqn:E; [exfalso; by apply Hns|done]).
          destruct (chosen i c ρ Δ Ha' Hin Hsf Hs) as (Δ0 & Hc0 & Hsub).
          exists c, ρ, Δ0. split; [done|]. split; [done|]. exact (U_of_I i c ρ Δ0 Hin Hsf Hc0 Hsub).
        + exists Δs. split; [|done]. refine (Forall2_mem_impl _ _ _ _ HΔ _). intros [c ρ] Δ Hin Hmem Hst. simpl in *.
          destruct Hst as [(Hns & Hs)|(Hst & ->)].
          * left. split; [done|]. apply (U_of_I i); [done| |done|].
            { destruct (S (mnode c)) eqn:E; [exfalso; by apply Hns|done]. }
            intros y Hy. rewrite Eq. by apply (elem_of_dsum Δ).
          * right. split; [|done]. destruct Hst as [Hst|Hst]; [by left|right]. intros Δ' Hc.
            apply (Hst Δ'). exact (mstep_mono U I _ _ _ _ cells_sub Hc).
      - right. split; [|done]. intros σ (c & ρ & Δ & Hin & Hns & Hs). apply (Ha σ).
        exists c, ρ, Δ. split; [done|]. split; [done|]. exact (mstep_mono U I _ _ _ _ cells_sub Hs).
    Qed.

    Lemma I_sub_star n o : I n o → Jstar U S r w n o.
    Proof.
      intros HI. destruct (classic (U n o)) as [HU|HU]; [by left|right]. split; [exact (HokI n o HI)|].
      intros (i & c & ρ & Hin & Hs & Hcase).
      assert (HIs : ∀ σ Δ, mstep (single n o) ρ c σ Δ → mstep I ρ c σ Δ).
      { intros σ Δ. apply mstep_mono. intros n' o' [-> ->]. exact HI. }
      destruct Hcase as [(Ha & Hno & Δ & Hc)|(Hst & σ & Δ & Hc)].
      - destruct (proj2 Hrun i) as [HaI|(HstI & _)].
        + destruct (chosen i c ρ Δ HaI Hin Hs (HIs _ _ Hc)) as (Δ0 & Hc0 & Hsub).
          exact (Hno Δ0 (U_of_I i c ρ Δ0 Hin Hs Hc0 Hsub)).
        + destruct Ha as ((c' & ρ' & Δ' & Hin' & Hns' & Hs') & _). apply (HstI (w i)).
          exists c', ρ', Δ'. split; [done|]. split; [done|]. exact (mstep_mono U I _ _ _ _ cells_sub Hs').
      - destruct (proj2 Hrun i) as [HaI|(HstI & _)].
        + destruct HaI as ((c' & ρ' & Δ' & Hin' & Hns' & Hs') & HaRest).
          assert (Hsf : S (mnode c') = false) by (destruct (S (mnode c')) eqn:E; [exfalso; by apply Hns'|done]).
          destruct (chosen i c' ρ' Δ' (conj (ex_intro _ c' (ex_intro _ ρ' (ex_intro _ Δ' (conj Hin' (conj Hns' Hs'))))) HaRest) Hin' Hsf Hs') as (Δ0 & Hc0 & Hsub).
          apply (Hst (w i)). exists c', ρ', Δ0. split; [done|]. split; [done|]. exact (U_of_I i c' ρ' Δ0 Hin' Hsf Hc0 Hsub).
        + apply (HstI σ). exists c, ρ, Δ. split; [done|]. split.
          * change (¬ S (mnode c) = true). congruence.
          * exact (HIs _ _ Hc).
    Qed.
  End Free.

  Definition malt_canon (Dp Dq : dist C) : Prop :=
    ∀ S, mext_closed S → ∀ I r w, (∀ n o, I n o → Ok o) → run_word I S Dq r w →
      ∃ r', is_run (SchedSts0 := mdlts (Jstar I S r w) (Sstar I S r w)) Stay Dp r'
        ∧ run_le (SchedSts0 := mdlts (Jstar I S r w) (Sstar I S r w)) r' r.

  Definition malt_free (Dp Dq : dist C) : Prop :=
    ∀ S, mext_closed S → ∀ r w, (∀ n o, cells S r w n o → Ok o) → run_word (cells S r w) S Dq r w →
      ∃ r', is_run (SchedSts0 := mdlts (Jstar (cells S r w) S r w) (Sstar (cells S r w) S r w)) Stay Dp r'
        ∧ run_le (SchedSts0 := mdlts (Jstar (cells S r w) S r w) (Sstar (cells S r w) S r w)) r' r.

  Lemma init_visited (Dq : dist C) (I : node → Off → Prop) :
    (∀ x, x ∈ Dq → mnode x.1 = []) → ∀ x, x ∈ Dq → visited_ok I (mnode x.1).
  Proof.
    intros Hq x Hx m a m2 E. rewrite (Hq x Hx) in E. exfalso. destruct m; discriminate E.
  Qed.

  Lemma star_pre (Dp Dq : dist C) : malt_pre Dp Dq → (∀ x, x ∈ Dq → mnode x.1 = []) → malt_canon Dp Dq.
  Proof.
    intros Hpre Hq S HS I r w HokI Hw.
    assert (Hrun : run_word I S (r 0) r w) by (split; [done|apply Hw]).
    assert (Hi : ∀ x, x ∈ r 0 → visited_ok I (mnode x.1)).
    { rewrite (proj1 Hw). by apply init_visited. }
    pose proof (run_star I S r w Hrun Hi) as Hstar.
    refine (Hpre (Jstar I S r w) (Sstar I S r w) _ (Sstar_ext I S r w HS) r _).
    { intros n o [Hn|[Ho _]]; [exact (HokI n o Hn)|done]. }
    split; [apply Hw|]. intros i. destruct (proj2 Hstar i) as [Ha|Ha]; [left; by exists (w i)|by right].
  Qed.

  Lemma run_word_is_run I S D r w : run_word I S D r w → is_run (SchedSts0 := mdlts I S) Stay D r.
  Proof.
    intros [E Hr]. split; [done|]. intros i. destruct (Hr i) as [Ha|Ha]; [left; by exists (w i)|by right].
  Qed.

  Lemma free_down (DC : dep_choice) (Dp Dq : dist C) I S r2 w rs :
    (∀ x, x ∈ Dq → mnode x.1 = []) → (∀ x, x ∈ Dq → x.2 ≠ weight_zero) →
    (∀ n o, I n o → Ok o) → run_word I S Dq r2 w →
    is_run (SchedSts0 := mdlts (Jstar (cells S r2 w) S r2 w) (Sstar (cells S r2 w) S r2 w)) Stay Dp rs →
    run_le (SchedSts0 := mdlts (Jstar (cells S r2 w) S r2 w) (Sstar (cells S r2 w) S r2 w)) rs r2 →
    ∃ r', is_run (SchedSts0 := mdlts I S) Stay Dp r' ∧ run_le (SchedSts0 := mdlts I S) r' r2.
  Proof.
    intros Hq0 Hq HokI Hw Hrs Hle.
    assert (Hrun : run_word I S (r2 0) r2 w) by (split; [done|apply Hw]).
    assert (Hi : ∀ x, x ∈ r2 0 → visited_ok I (mnode x.1)).
    { rewrite (proj1 Hw). by apply init_visited. }
    assert (Hnz : ∀ i x, x ∈ r2 i → x.2 ≠ weight_zero).
    { intros i. exact (run_weights (SchedSts0 := mdlts I S) Stay (λ ρ, ρ ≠ weight_zero)
        (λ ρ c σ Δ Hg Hs, mstep_nonzero I ρ c σ Δ Hg Hs) Dq r2 (run_word_is_run _ _ _ _ _ Hw) Hq i). }
    pose proof (run_cells I S r2 w Hrun Hi Hnz) as HrU.
    set (U := cells S r2 w) in *.
    assert (HiU : ∀ x, x ∈ r2 0 → visited_ok U (mnode x.1)).
    { rewrite (proj1 Hw). by apply init_visited. }
    assert (Hfree : ∀ ρ c σ Δ, mstep (Jstar U S r2 w) ρ c σ Δ → ¬ (Sstar U S r2 w (mnode c) = true) →
      mstep I ρ c σ Δ ∨ ∀ y, y ∈ Δ → Sstar U S r2 w (mnode y.1) = true).
    { intros ρ c σ Δ Hs _.
      destruct (mstep_cell _ _ _ _ _ Hs) as [[Hall _]|(o' & Ho & HJ & Ht)]; [left; apply Hall|].
      destruct (classic (I (mnode c) o')) as [HI|HI]; [left; by apply HJ|]. right. intros y Hy.
      destruct (Ht y Hy) as (a & <- & Ey).
      assert (Hcr : crossed U S r2 w (mnode c ++ [a])).
      { exists (mnode c), a, []. split; [done|]. split; [done|]. intros HU. apply HI.
        exact (cells_sub I S r2 w Hrun Hi _ _ HU). }
      pose proof (Sstar_crossed U S r2 w _ Hcr) as Hz. rewrite <- Ey in Hz. exact Hz. }
    destruct (replay (mdlts I S) (mdlts (Jstar U S r2 w) (Sstar U S r2 w))
      (λ ρ c σ Δ Hs, mstep_mono I _ ρ c σ Δ (I_sub_star I S r2 w Hrun Hi Hnz HokI) Hs)
      Hfree (λ c Hc, Sstar_S U S r2 w _ Hc) (λ ρ c σ Δ Hs, mstep_mass _ _ _ _ _ Hs) (λ ρ c σ Δ Hs, mstep_mass _ _ _ _ _ Hs)
      DC _ _ rs Hrs (Sim_refl _ _)) as (r' & Hr' & Hm).
    exists r'. split; [done|]. intros n v Hv. destruct (Hm n) as (m & Hmm).
    assert (Hlt : v <ₚ succ_mass (SchedSts0 := mdlts (Jstar U S r2 w) (Sstar U S r2 w)) rs m).
    { destruct Hv as [Hv1 Hv2]. split; [by etransitivity|]. intros Hb. apply Hv2. by etransitivity. }
    destruct (Hle m v Hlt) as (m' & Hm').
    exists m'. unfold succ_mass in *. erewrite dmass_of_congr; [exact Hm'|].
    intros c ρ Hin. simpl. rewrite (Sstar_visited U S r2 w HrU HiU m' c ρ Hin). done.
  Qed.

  Theorem malt_free_iff (DC : dep_choice) (Dp Dq : dist C) :
    (∀ x, x ∈ Dq → mnode x.1 = []) → (∀ x, x ∈ Dq → x.2 ≠ weight_zero) →
    malt_free Dp Dq ↔ malt_pre Dp Dq.
  Proof.
    intros Hq0 Hq. split.
    - intros Hf I S HokI HS r2 Hr2. destruct (is_run_word DC _ _ _ _ Hr2) as (w & Hw).
      assert (Hrun : run_word I S (r2 0) r2 w) by (split; [done|apply Hw]).
      assert (Hi : ∀ x, x ∈ r2 0 → visited_ok I (mnode x.1)).
      { rewrite (proj1 Hw). by apply init_visited. }
      assert (Hnz : ∀ i x, x ∈ r2 i → x.2 ≠ weight_zero).
      { intros i. exact (run_weights (SchedSts0 := mdlts I S) Stay (λ ρ, ρ ≠ weight_zero)
          (λ ρ c σ Δ Hg Hs, mstep_nonzero I ρ c σ Δ Hg Hs) Dq r2 Hr2 Hq i). }
      pose proof (run_cells I S r2 w Hrun Hi Hnz) as HrU.
      assert (HrU' : run_word (cells S r2 w) S Dq r2 w) by (split; [apply Hw|apply HrU]).
      destruct (Hf S HS r2 w (λ n o Hc, HokI n o (cells_sub I S r2 w Hrun Hi n o Hc)) HrU') as (rs & Hrs & Hle).
      exact (free_down DC Dp Dq I S r2 w rs Hq0 Hq HokI Hw Hrs Hle).
    - intros Hpre S HS r w Hok Hw. exact (star_pre Dp Dq Hpre Hq0 S HS _ r w Hok Hw).
  Qed.

  Section Real.
    Context (Real : (node → Off → Prop) → (node → bool) → Prop).
    Hypothesis Hreal : ∀ I S, Real I S → ∀ n o, I n o → Ok o.

    Definition malt_pre_on (Dp Dq : dist C) : Prop :=
      ∀ I S, Real I S → smyth_le (SchedSts0 := mdlts I S) Stay Dp Dq.

    Definition malt_free_on (Dp Dq : dist C) : Prop :=
      ∀ I S, Real I S → ∀ r w, run_word I S Dq r w →
        ∃ r', is_run (SchedSts0 := mdlts (Jstar (cells S r w) S r w) (Sstar (cells S r w) S r w)) Stay Dp r'
          ∧ run_le (SchedSts0 := mdlts (Jstar (cells S r w) S r w) (Sstar (cells S r w) S r w)) r' r.

    Definition MenuReal (Dp Dq : dist C) : Prop :=
      ∀ I S r w, Real I S → run_word I S Dq r w →
        ∃ I0 S0, Real I0 S0 ∧ is_run (SchedSts0 := mdlts I0 S0) Stay Dq r
          ∧ (∀ i c ρ, (c, ρ) ∈ r i → S0 (mnode c) = Sstar (cells S r w) S r w (mnode c))
          ∧ ∀ r0, is_run (SchedSts0 := mdlts I0 S0) Stay Dp r0 →
              ∃ r', is_run (SchedSts0 := mdlts (Jstar (cells S r w) S r w) (Sstar (cells S r w) S r w)) Stay Dp r'
                ∧ ∀ n, ∃ m, succ_mass (SchedSts0 := mdlts (Jstar (cells S r w) S r w) (Sstar (cells S r w) S r w)) r' n
                     ≤ₚ succ_mass (SchedSts0 := mdlts I0 S0) r0 m.

    Theorem malt_free_on_sound (DC : dep_choice) (Dp Dq : dist C) :
      (∀ x, x ∈ Dq → mnode x.1 = []) → (∀ x, x ∈ Dq → x.2 ≠ weight_zero) →
      malt_free_on Dp Dq → malt_pre_on Dp Dq.
    Proof.
      intros Hq0 Hq Hf I S HR r2 Hr2. destruct (is_run_word DC _ _ _ _ Hr2) as (w & Hw).
      destruct (Hf I S HR r2 w Hw) as (rs & Hrs & Hle).
      exact (free_down DC Dp Dq I S r2 w rs Hq0 Hq (Hreal I S HR) Hw Hrs Hle).
    Qed.

    Theorem malt_free_on_complete (Dp Dq : dist C) :
      MenuReal Dp Dq → malt_pre_on Dp Dq → malt_free_on Dp Dq.
    Proof.
      intros HM Hpre I S HR r w Hw.
      destruct (HM I S r w HR Hw) as (I0 & S0 & HR0 & Hr0 & HS0 & Hconv).
      destruct (Hpre I0 S0 HR0 r Hr0) as (r0 & Hr0' & Hle).
      destruct (Hconv r0 Hr0') as (r' & Hr' & Hm).
      exists r'. split; [done|]. intros n v Hv. destruct (Hm n) as (m & Hmm).
      assert (Hlt : v <ₚ succ_mass (SchedSts0 := mdlts I0 S0) r0 m).
      { destruct Hv as [Hv1 Hv2]. split; [by etransitivity|]. intros Hb. apply Hv2. by etransitivity. }
      destruct (Hle m v Hlt) as (m' & Hm').
      exists m'. unfold succ_mass in *. erewrite dmass_of_congr; [exact Hm'|].
      intros c ρ Hin. simpl. rewrite (HS0 m' c ρ Hin). done.
    Qed.

    Definition MenuAgree (Dp Dq : dist C) : Prop :=
      ∀ I S r w, Real I S → run_word I S Dq r w →
        ∃ I0 S0, Real I0 S0 ∧ is_run (SchedSts0 := mdlts I0 S0) Stay Dq r
          ∧ (∀ i c ρ, (c, ρ) ∈ r i → S0 (mnode c) = Sstar (cells S r w) S r w (mnode c))
          ∧ ∀ r0, is_run (SchedSts0 := mdlts I0 S0) Stay Dp r0 →
              ∀ i, agree_on (mdlts I0 S0) (mdlts (Jstar (cells S r w) S r w) (Sstar (cells S r w) S r w)) (r0 i).

    Lemma menu_agree_real (Dp Dq : dist C) : MenuAgree Dp Dq → MenuReal Dp Dq.
    Proof.
      intros HA I S r w HR Hw. destruct (HA I S r w HR Hw) as (I0 & S0 & HR0 & Hr & HS0 & Hag).
      exists I0, S0. split; [done|]. split; [done|]. split; [done|]. intros r0 Hr0.
      exists r0. split; [exact (agree_run _ _ Stay Dp r0 (Hag r0 Hr0) Hr0)|].
      intros n. exists n. rewrite (agree_succ_mass _ _ r0 n (Hag r0 Hr0 n)). done.
    Qed.

    Definition MenuTrunc (Dp Dq : dist C) : Prop :=
      ∀ I S r w, Real I S → run_word I S Dq r w →
        ∃ J0, (∀ r', is_run (SchedSts0 := mdlts J0 (Sstar (cells S r w) S r w)) Stay Dp r' →
                    is_run (SchedSts0 := mdlts (Jstar (cells S r w) S r w) (Sstar (cells S r w) S r w)) Stay Dp r')
          ∧ (∀ D, ∃ l : list (dist C), ∀ D', rstep (mdlts J0 (Sstar (cells S r w) S r w)) D D' → D' ∈ l)
          ∧ ∀ N, ∃ IN SN, Real IN SN ∧ is_run (SchedSts0 := mdlts IN SN) Stay Dq r
              ∧ (∀ i c ρ, (c, ρ) ∈ r i → SN (mnode c) = Sstar (cells S r w) S r w (mnode c))
              ∧ ∀ r0, is_run (SchedSts0 := mdlts IN SN) Stay Dp r0 →
                  ∀ i, i ≤ N → agree_on (mdlts IN SN) (mdlts J0 (Sstar (cells S r w) S r w)) (r0 i).

    Theorem malt_free_on_trunc (DC : dep_choice) (Dp Dq : dist C) :
      MenuTrunc Dp Dq → malt_pre_on Dp Dq → malt_free_on Dp Dq.
    Proof.
      intros HT Hpre I S HR r w Hw.
      destruct (HT I S r w HR Hw) as (J0 & HJ0 & Hfin & Hfam).
      set (Ss := Sstar (cells S r w) S r w) in *.
      set (Js := Jstar (cells S r w) S r w) in *.
      destruct (konig (mdlts J0 Ss) (λ D, ∀ v, v <ₚ dmass_of (psuccess (SchedSts := mdlts Js Ss)) D →
                      ∃ m, v ≤ₚ succ_mass (SchedSts0 := mdlts Js Ss) r m) Hfin DC Dp) as (r' & Hr' & Hg).
      { intros N. destruct (Hfam N) as (IN & SN & HRN & HrN & HSN & Hag).
        destruct (Hpre IN SN HRN r HrN) as (r0 & Hr0 & Hle).
        exists r0. split; [exact (proj1 Hr0)|]. split.
        - intros i Hi. assert (Hi' : i ≤ N) by lia.
          destruct (proj2 Hr0 i) as [(σ & Hs)|[Hst E]].
          + left. exists σ. exact (agree_dstep _ _ Stay _ σ _ (Hag r0 Hr0 i Hi') Hs).
          + right. split; [exact (agree_dstable _ _ _ (Hag r0 Hr0 i Hi') Hst)|exact E].
        - intros i Hi v Hv.
          assert (Hc : ∀ c ρ, (c, ρ) ∈ r0 i →
            psuccess (SchedSts := mdlts IN SN) c ↔ psuccess (SchedSts := mdlts Js Ss) c).
          { intros c ρ Hin. exact (proj1 (Hag r0 Hr0 i Hi c ρ Hin)). }
          assert (Hlt : v <ₚ succ_mass (SchedSts0 := mdlts IN SN) r0 i).
          { unfold succ_mass. rewrite (dmass_of_congr _ _ (r0 i) Hc). exact Hv. }
          destruct (Hle i v Hlt) as (m & Hm). exists m.
          assert (Hc' : ∀ c ρ, (c, ρ) ∈ r m →
            psuccess (SchedSts := mdlts IN SN) c ↔ psuccess (SchedSts := mdlts Js Ss) c).
          { intros c ρ Hin. simpl. rewrite (HSN m c ρ Hin). done. }
          unfold succ_mass in *. rewrite <- (dmass_of_congr _ _ (r m) Hc'). exact Hm. }
      exists r'. split; [exact (HJ0 r' Hr')|]. intros n v Hv. exact (Hg n v Hv).
    Qed.
  End Real.

  Lemma run_mass I S (D : dist C) r' :
    is_run (SchedSts0 := mdlts I S) Stay D r' → ∀ i, dmass (r' i) = dmass D.
  Proof.
    intros [Hi0 Hr]. induction i as [|i IH]; [by rewrite Hi0|]. rewrite <- IH.
    destruct (Hr i) as [(σ & _ & Δs & HΔ & ->)|(_ & ->)]; [|done].
    exact (stepsI_mass (mdlts I S) (mdlts I S) (λ ρ c σ' Δ Hs, mstep_mass _ _ _ _ _ Hs) _ σ Δs HΔ).
  Qed.

  Theorem mconvergence (Dp Dq : dist C) :
    malt_pre Dp Dq → (∀ x, x ∈ Dq → mnode x.1 = []) →
    ∀ S, mext_closed S → ∀ I r w o, (∀ n o', I n o' → Ok o') → Ok o → run_word I S Dq r w →
      (∀ i, ¬ dstable (SchedSts0 := mdlts I S) (r i)) →
      (∀ J c ρ, J (mnode c) o → ∃ σ Δ, mstep J ρ c σ Δ) →
      (∀ n i ρ c Δ, mstep (single n o) ρ c (w i) Δ → ∀ J', mstep J' ρ c (w i) Δ) →
      ∃ r', is_run (SchedSts0 := mdlts (Jstar I S r w) (Sstar I S r w)) Stay Dp r'
        ∧ ((∀ i, ¬ dstable (SchedSts0 := mdlts (Jstar I S r w) (Sstar I S r w)) (r' i))
           ∨ ∀ v, v <ₚ dmass Dp → ∃ m, v ≤ₚ succ_mass (SchedSts0 := mdlts I S) r m).
  Proof.
    intros Hpre Hq0 S HS I r w o HokI Hoko Hw Hdiv Hen Hfresh.
    destruct (star_pre Dp Dq Hpre Hq0 S HS I r w HokI Hw) as (r' & Hr' & Hle).
    exists r'. split; [done|].
    destruct (classic (∀ i, ¬ dstable (SchedSts0 := mdlts (Jstar I S r w) (Sstar I S r w)) (r' i))) as [Hn|Hn]; [by left|].
    right. apply not_all_not_ex in Hn as (i & Hst).
    assert (Hnr : ∀ n, ¬ refused I S r w n o).
    { intros n (j & c & ρ & _ & _ & [(_ & Hno & Δ & Hc)|(Hsj & _)]).
      - exact (Hno Δ (Hfresh _ _ _ _ _ Hc I)).
      - exact (Hdiv j Hsj). }
    assert (Hall : ∀ x, x ∈ r' i → Sstar I S r w (mnode x.1) = true).
    { intros [c ρ] Hin. destruct (Sstar I S r w (mnode c)) eqn:Es; [done|]. exfalso.
      assert (HJ : Jstar I S r w (mnode c) o) by (right; split; [exact Hoko|apply Hnr]).
      destruct (Hen _ c ρ HJ) as (σ & Δ & Hs). apply (Hst σ). exists c, ρ, Δ. split; [exact Hin|]. split; [|exact Hs].
      change (¬ Sstar I S r w (mnode c) = true). congruence. }
    intros v Hv.
    assert (Hm : dmass_of (psuccess (SchedSts := mdlts (Jstar I S r w) (Sstar I S r w))) (r' i) = dmass Dp).
    { rewrite (dmass_of_all _ (r' i) Hall). exact (run_mass _ _ _ _ Hr' i). }
    assert (Hlt : v <ₚ succ_mass (SchedSts0 := mdlts (Jstar I S r w) (Sstar I S r w)) r' i) by (unfold succ_mass; by rewrite Hm).
    destruct (Hle i v Hlt) as (m & Hmm). exists m. unfold succ_mass in *.
    assert (Hrun : run_word I S (r 0) r w) by (split; [done|apply Hw]).
    assert (Hi : ∀ x, x ∈ r 0 → visited_ok I (mnode x.1)).
    { rewrite (proj1 Hw). by apply init_visited. }
    erewrite dmass_of_congr; [exact Hmm|]. intros c ρ Hin. simpl. rewrite (Sstar_visited I S r w Hrun Hi m c ρ Hin). done.
  Qed.
End Canonical.
(* end hide *)
