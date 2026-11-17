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
From Stdlib.Logic Require Import Classical_Prop ClassicalDescription.
From Stdlib.Arith Require Import Wf_nat.
Import ListNotations.
From stdpp Require Import base decidable list.
From TestingTheory Require Import pMust_scheduled pMust_smyth pMust_transfer pMust_canonical pMust_inductive pMust_cotrace.

Lemma filter_none {B} (P : B → Prop) `{∀ x, Decision (P x)} (l : list B) :
  (∀ y, y ∈ l → ¬ P y) → filter P l = [].
Proof.
  induction l as [|x l IH]; intros Hn; [done|].
  rewrite filter_cons_False; [|apply Hn; by left]. apply IH. intros y Hy. apply Hn. by right.
Qed.

Lemma filter_all {B} (P : B → Prop) `{∀ x, Decision (P x)} (l : list B) :
  (∀ y, y ∈ l → P y) → filter P l = l.
Proof.
  induction l as [|x l IH]; intros Ha; [done|].
  rewrite filter_cons_True; [|apply Ha; by left]. f_equal. apply IH. intros y Hy. apply Ha. by right.
Qed.

Lemma least_nat (P : nat → Prop) i k : i ≤ k → P k → ∃ k0, i ≤ k0 ∧ P k0 ∧ ∀ k', i ≤ k' → k' < k0 → ¬ P k'.
Proof.
  revert i. induction k as [k IH] using lt_wf_ind. intros i Hik Hk.
  destruct (classic (∃ k', i ≤ k' ∧ k' < k ∧ P k')) as [(k' & H1 & H2 & H3)|Hn].
  - exact (IH k' H2 i H1 H3).
  - exists k. split; [done|]. split; [done|]. intros k' H1 H2 H3. apply Hn. by exists k'.
Qed.

Section Lists.
  Context `{WeightLaws} {C : Type}.

  Lemma dmass_of_split (P : C * weight → Prop) `{∀ x, Decision (P x)} (g : C → Prop) `{∀ c, Decision (g c)}
      (D : dist C) :
    dmass_of g D = prob_add (dmass_of g (filter P D)) (dmass_of g (filter (λ x, ¬ P x) D)).
  Proof.
    induction D as [|x D IH]; simpl; [by rewrite prob_add_zero|].
    rewrite !filter_cons. destruct (decide (P x)) as [Hx|Hx].
    - rewrite (decide_False (P := ¬ P x)) by tauto. simpl. rewrite IH. case_decide; [by rewrite prob_add_assoc|done].
    - rewrite (decide_True (P := ¬ P x)) by done. simpl. rewrite IH. case_decide; [|done].
      rewrite prob_add_assoc, (prob_add_comm (mass x.2)), <- prob_add_assoc. done.
  Qed.

  Lemma dmass_of_mono (g g' : C → Prop) `{∀ c, Decision (g c)} `{∀ c, Decision (g' c)} (D : dist C) :
    (∀ x, x ∈ D → g x.1 → g' x.1) → dmass_of g D ≤ₚ dmass_of g' D.
  Proof.
    induction D as [|x D IH]; intros Hg; simpl; [reflexivity|].
    assert (IH' : dmass_of g D ≤ₚ dmass_of g' D) by (apply IH; intros y Hy; apply Hg; by right).
    case_decide as Ha; case_decide as Hb.
    - apply prob_add_mono2; [reflexivity|exact IH'].
    - exfalso. apply Hb, Hg; [by left|done].
    - etransitivity; [exact IH'|]. rewrite <- (prob_add_zero (dmass_of g' D)) at 1.
      apply prob_add_mono, prob_zero_le.
    - exact IH'.
  Qed.

  Lemma dmass_of_none (g : C → Prop) `{∀ c, Decision (g c)} (D : dist C) :
    (∀ x, x ∈ D → ¬ g x.1) → dmass_of g D = prob_zero.
  Proof.
    induction D as [|x D IH]; intros Hn; [done|]. simpl.
    rewrite decide_False; [|apply Hn; by left]. apply IH. intros y Hy. apply Hn. by right.
  Qed.

  Lemma dmass_of_const (g : C → Prop) `{∀ c, Decision (g c)} (Δ : dist C) c ρ :
    (∀ y, y ∈ Δ → (g y.1 ↔ g c)) → dmass Δ = mass ρ → dmass_of g Δ = dmass_of g [(c, ρ)].
  Proof.
    intros Hg Hm. simpl. case_decide as Hc.
    - rewrite prob_add_zero_r, <- Hm. apply dmass_of_all. intros y Hy. by apply Hg.
    - apply dmass_of_none. intros y Hy Hy'. apply Hc. exact (proj1 (Hg y Hy) Hy').
  Qed.

  Lemma forall2_exists {B} (R : C * weight → B → Prop) (D : dist C) :
    (∀ x, x ∈ D → ∃ y, R x y) → ∃ l, Forall2 R D l.
  Proof.
    induction D as [|x D IH]; intros Hx; [by exists []|].
    destruct (Hx x) as (y & Hy); [by left|]. destruct IH as (l & Hl); [intros z Hz; apply Hx; by right|].
    exists (y :: l). by constructor.
  Qed.

  Section Sel.
    Context (P : C * weight → Prop) `{∀ x, Decision (P x)}.

    Fixpoint dsel (L : dist C) (Δs : list (dist C)) : dist C :=
      match L, Δs with
      | x :: L', Δ :: Δs' => (if decide (P x) then Δ else []) ++ dsel L' Δs'
      | _, _ => []
      end.

    Lemma dsum_keep (g : C → Prop) `{∀ c, Decision (g c)} R L Δs :
      Forall2 R L Δs →
      (∀ x Δ, R x Δ → P x → Δ = [x]) →
      (∀ x Δ, R x Δ → ¬ P x → (∀ y, y ∈ Δ → ¬ P y ∧ (g y.1 ↔ g x.1)) ∧ dmass Δ = mass x.2) →
      filter P (dsum Δs) = filter P L ∧ dmass_of g (dsum Δs) = dmass_of g L.
    Proof.
      intros HF Hsh Hdp. induction HF as [|x Δ L Δs HR _ [IH1 IH2]]; [done|].
      rewrite dsum_cons, filter_app, dmass_of_app, IH1, IH2, filter_cons. case_decide as Hx.
      - rewrite (Hsh x Δ HR Hx). simpl. rewrite filter_cons, (decide_True (P := P x)) by done. simpl.
        split; [done|]. case_decide; [by rewrite prob_add_zero_r|by rewrite prob_add_zero].
      - destruct (Hdp x Δ HR Hx) as [Hy Hm].
        rewrite (dmass_of_const g Δ x.1 x.2); [|intros y Hy'; exact (proj2 (Hy y Hy'))|exact Hm].
        assert (Hf : filter P Δ = []).
        { apply filter_none. intros y Hy'. exact (proj1 (Hy y Hy')). }
        rewrite Hf. simpl. destruct x as [c ρ]. simpl. split; [done|]. case_decide; [by rewrite prob_add_zero_r|by rewrite prob_add_zero].
    Qed.

    Lemma dsel_filter (Q : C * weight → Prop) `{∀ x, Decision (Q x)} R L Δs :
      Forall2 R L Δs → (∀ x Δ, R x Δ → ¬ P x → ∀ y, y ∈ Δ → ¬ Q y) →
      filter Q (dsum Δs) = filter Q (dsel L Δs).
    Proof.
      intros HF Hdp. induction HF as [|x Δ L Δs HR _ IH]; [done|].
      rewrite dsum_cons. cbn [dsel]. rewrite !filter_app, IH. case_decide as Hx; [done|]. simpl.
      rewrite (filter_none Q Δ); [done|]. exact (Hdp x Δ HR Hx).
    Qed.

    Lemma dsel_mass (g : C → Prop) `{∀ c, Decision (g c)} R L Δs :
      Forall2 R L Δs → (∀ x Δ, R x Δ → ¬ P x → dmass_of g Δ = dmass_of g [x]) →
      dmass_of g (dsum Δs) = prob_add (dmass_of g (dsel L Δs)) (dmass_of g (filter (λ x, ¬ P x) L)).
    Proof.
      intros HF Hdp. induction HF as [|x Δ L Δs HR _ IH]; [simpl; by rewrite prob_add_zero|].
      rewrite dsum_cons, filter_cons. cbn [dsel]. rewrite !dmass_of_app, IH. case_decide as Hx.
      - rewrite (decide_False (P := ¬ P x)) by tauto. by rewrite prob_add_assoc.
      - rewrite (decide_True (P := ¬ P x)) by done. rewrite (Hdp x Δ HR Hx). simpl.
        rewrite prob_add_zero. case_decide; [|by rewrite prob_add_zero].
        rewrite prob_add_zero_r, !prob_add_assoc, (prob_add_comm (mass x.2)). done.
    Qed.

    Lemma merge (R1 R2 : C * weight → dist C → Prop) L Δs D :
      Forall2 R1 L Δs → filter P D = filter P L → (∀ x Δ, P x → R1 x Δ → R2 x Δ) →
      (∀ x, x ∈ D → ¬ P x → ∃ Δ, R2 x Δ) →
      ∃ ΔsD, Forall2 R2 D ΔsD ∧ dsel D ΔsD = dsel L Δs.
    Proof.
      intros HF. revert D. induction HF as [|y Δ L Δs HR HF IH]; intros D HD H12 Hex.
      - induction D as [|x D IHD]; [by exists []|].
        rewrite filter_cons in HD. case_decide as Hx; [discriminate HD|].
        destruct (Hex x) as (Δ & HΔ); [by left|done|].
        destruct IHD as (ΔsD & HF & Hs); [done|intros z Hz; apply Hex; by right|].
        exists (Δ :: ΔsD). split; [by constructor|]. simpl. rewrite decide_False by done. exact Hs.
      - induction D as [|x D IHD].
        + rewrite filter_cons in HD. case_decide as Hy; [discriminate HD|].
          destruct (IH [] HD H12) as (ΔsD & HFD & Hs); [intros z Hz; by apply elem_of_nil in Hz|].
          inversion HFD; subst. exists []. split; [done|]. simpl. rewrite decide_False by done. exact Hs.
        + rewrite filter_cons in HD. destruct (decide (P x)) as [Hx|Hx].
          * rewrite filter_cons in HD. destruct (decide (P y)) as [Hy|Hy].
            -- injection HD as <- HD.
               destruct (IH D HD H12) as (ΔsD & HFD & Hs); [intros z Hz; apply Hex; by right|].
               exists (Δ :: ΔsD). split; [constructor; [exact (H12 x Δ Hx HR)|exact HFD]|].
               simpl. rewrite !decide_True by done. by rewrite Hs.
            -- destruct (IH (x :: D)) as (ΔsD & HFD & Hs); [by rewrite filter_cons_True|done|done|].
               exists ΔsD. split; [exact HFD|]. simpl. rewrite decide_False by done. exact Hs.
          * destruct (Hex x) as (Δx & HΔx); [by left|done|].
            destruct IHD as (ΔsD & HFD & Hs); [done|intros z Hz; apply Hex; by right|].
            exists (Δx :: ΔsD). split; [by constructor|]. simpl. rewrite decide_False by done. exact Hs.
    Qed.
  End Sel.
End Lists.

Section Fair.
  Context `{WeightLaws} {C Sch A Off : Type} `{M : !MenuSts C Sch A Off}.
  Notation node := (list A).

  Definition fair (S : node → bool) (r : nat → dist C) (w : nat → Sch) : Prop :=
    ∀ i c ρ, (∀ j, i ≤ j → (c, ρ) ∈ r j) → S (mnode c) = false →
      (∀ σ Δ, ¬ mstep (cells S r w) ρ c σ Δ)
      ∧ ∀ σ o Δ, mstep (single (mnode c) o) ρ c σ Δ → refused (cells S r w) S r w (mnode c) o.

  Lemma ext_closed_app (S : node → bool) (n m : node) : mext_closed S → S n = true → S (n ++ m) = true.
  Proof.
    intros HS. revert n. induction m as [|a m IH] using rev_ind; intros n Hn; [by rewrite app_nil_r|].
    rewrite app_assoc. apply HS. by apply IH.
  Qed.

  Lemma deep_step Mx J ρ c σ Δ : Mx ≤ length (mnode c) → mstep J ρ c σ Δ →
    ∀ y, y ∈ Δ → Mx ≤ length (mnode y.1) ∧ take Mx (mnode y.1) = take Mx (mnode c).
  Proof.
    intros Hl Hs y Hy. destruct (mstep_cell _ _ _ _ _ Hs) as [[_ Hn]|(o & _ & _ & Hn)].
    - rewrite (Hn y Hy). done.
    - destruct (Hn y Hy) as (a & _ & ->). rewrite length_app. split; [simpl; lia|].
      rewrite take_app_le; [done|lia].
  Qed.

  Lemma comp_step_exists (SS : SchedSts C Sch) σ (x : C * weight) :
    ∃ Δ, comp_step (SchedSts0 := SS) Stay x.2 x.1 σ Δ.
  Proof.
    destruct (classic (∃ Δ, ¬ psuccess (SchedSts := SS) x.1 ∧ sstep (SchedSts := SS) x.2 x.1 σ Δ))
      as [(Δ & HΔ)|Hn].
    - exists Δ. by left.
    - exists (rest Stay x.1 x.2). right. split; [|done].
      destruct (classic (psuccess (SchedSts := SS) x.1)) as [Hs|Hs]; [by left|right].
      intros Δ' HΔ'. apply Hn. by exists Δ'.
  Qed.

  Lemma forall2_dsum_elem {B} (R : B → dist C → Prop) (L : list B) Δs y :
    Forall2 R L Δs → y ∈ dsum Δs → ∃ x Δ, x ∈ L ∧ R x Δ ∧ y ∈ Δ.
  Proof.
    induction 1 as [|x Δ L Δs HR _ IH]; intros Hy; [by apply elem_of_nil in Hy|].
    rewrite dsum_cons in Hy. apply elem_of_app in Hy as [Hy|Hy].
    - exists x, Δ. split; [by left|done].
    - destruct (IH Hy) as (x' & Δ' & Hx & HR' & Hy'). exists x', Δ'. split; [by right|done].
  Qed.

  Lemma not_true_false (b : bool) : ¬ b = true → b = false.
  Proof. by destruct b. Qed.

  Lemma ref_cells I Sx (r : nat → dist C) w : run_word I Sx (r 0) r w →
    (∀ x, x ∈ r 0 → visited_ok I (mnode x.1)) → (∀ i x, x ∈ r i → x.2 ≠ weight_zero) →
    ∀ n o, refused (cells Sx r w) Sx r w n o ↔ refused I Sx r w n o.
  Proof.
    intros Hrun Hinit Hnz n o. pose proof (run_cells I Sx r w Hrun Hinit Hnz) as Hrc.
    pose proof (cells_sub I Sx r w Hrun Hinit) as Hsub.
    assert (Hup : ∀ i c ρ Δ, (c, ρ) ∈ r i → Sx (mnode c) = false → mstep I ρ c (w i) Δ →
      dstep (SchedSts0 := mdlts I Sx) Stay (r i) (w i) (r (Datatypes.S i)) → ∃ Δ0, mstep (cells Sx r w) ρ c (w i) Δ0).
    { intros i c ρ Δ Hin Hs Hc Hd. destruct (chosen I Sx r w i c ρ Δ Hd Hin Hs Hc) as (Δ0 & Hc0 & Hsub0).
      exists Δ0. exact (U_of_I I Sx r w Hnz i c ρ Δ0 Hin Hs Hc0 Hsub0). }
    split; intros (i & c & ρ & Hin & Hs & Hcase); exists i, c, ρ; split; [done| |done| ]; split; try done.
    - destruct Hcase as [(Hd & Hno & Hsg)|(Hst & Hsg)].
      + left. destruct (proj2 Hrun i) as [HdI|(HstI & _)].
        * split; [exact HdI|]. split; [|exact Hsg]. intros Δ' Hc'.
          destruct (Hup i c ρ Δ' Hin Hs Hc' HdI) as (Δ0 & HΔ0). exact (Hno Δ0 HΔ0).
        * exfalso. destruct Hd as ((c' & ρ' & Δ' & Hin' & Hns' & Hs') & _). apply (HstI (w i)).
          exists c', ρ', Δ'. split; [done|]. split; [done|]. exact (mstep_mono _ _ _ _ _ _ Hsub Hs').
      + right. split; [|exact Hsg]. destruct (proj2 Hrun i) as [HdI|(HstI & _)]; [|exact HstI].
        exfalso. pose proof HdI as ((c' & ρ' & Δ' & Hin' & Hns' & Hs') & _).
        destruct (Hup i c' ρ' Δ' Hin' (not_true_false _ Hns') Hs' HdI) as (Δ0 & HΔ0).
        apply (Hst (w i)). exists c', ρ', Δ0. split; [done|]. split; [done|exact HΔ0].
    - destruct Hcase as [(Hd & Hno & Hsg)|(Hst & Hsg)].
      + left. destruct (proj2 Hrc i) as [Hdc|(Hstc & _)].
        * split; [exact Hdc|]. split; [|exact Hsg]. intros Δ' Hc'. exact (Hno Δ' (mstep_mono _ _ _ _ _ _ Hsub Hc')).
        * exfalso. pose proof Hd as ((c' & ρ' & Δ' & Hin' & Hns' & Hs') & _).
          destruct (Hup i c' ρ' Δ' Hin' (not_true_false _ Hns') Hs' Hd) as (Δ0 & HΔ0).
          apply (Hstc (w i)). exists c', ρ', Δ0. split; [done|]. split; [done|exact HΔ0].
      + right. split; [|exact Hsg]. intros σ (c' & ρ' & Δ' & Hin' & Hns' & Hs'). apply (Hst σ).
        exists c', ρ', Δ'. split; [done|]. split; [done|exact (mstep_mono _ _ _ _ _ _ Hsub Hs')].
  Qed.

  Definition cells_lt (k : nat) (S : node → bool) (r : nat → dist C) (w : nat → Sch) (n : node) (o : Off) : Prop :=
    ∃ i c ρ Δ, Datatypes.S i < k ∧ (c, ρ) ∈ r i ∧ S (mnode c) = false ∧ ¬ mfree (w i) ∧ Δ ≠ [] ∧
      mstep (single n o) ρ c (w i) Δ ∧ ∀ y, y ∈ Δ → y ∈ r (Datatypes.S i).

  Definition refused_lt (k : nat) (I : node → Off → Prop) (S : node → bool) (r : nat → dist C) (w : nat → Sch)
      (n : node) (o : Off) : Prop :=
    ∃ i c ρ, Datatypes.S i < k ∧ (c, ρ) ∈ r i ∧ S (mnode c) = false ∧
      ((dstep (SchedSts0 := mdlts I S) Stay (r i) (w i) (r (Datatypes.S i))
          ∧ (∀ Δ, ¬ mstep I ρ c (w i) Δ) ∧ ∃ Δ, mstep (single n o) ρ c (w i) Δ)
       ∨ (dstable (SchedSts0 := mdlts I S) (r i) ∧ ∃ σ Δ, mstep (single n o) ρ c σ Δ)).

  Lemma single_node n o ρ c σ Δ : ¬ mfree σ → mstep (single n o) ρ c σ Δ → n = mnode c.
  Proof. intros Hf Hs. destruct (mstep_off _ _ _ _ _ Hf Hs) as (o' & [En _] & _). done. Qed.

  Section Trunc.
    Context (S : node → bool) (r : nat → dist C) (w : nat → Sch) (Mx : nat).
    Notation U := (cells S r w).
    Hypothesis Hw : run_word U S (r 0) r w.
    Hypothesis HS : mext_closed S.
    Hypothesis Hfair : fair S r w.

    Definition shallow (x : C * weight) : Prop := length (mnode x.1) < Mx.
    #[local] Instance shallow_dec x : Decision (shallow x).
    Proof. unfold shallow. apply _. Defined.
    Definition IM (n : node) (o : Off) : Prop := U n o ∧ length n < Mx.
    Definition SM (n : node) : bool := S n || bool_decide (Mx < length n).
    Definition Pf (c : C) : Prop := Mx ≤ length (mnode c) ∧ S (take Mx (mnode c)) = true.
    #[local] Instance Pf_dec c : Decision (Pf c).
    Proof. unfold Pf. apply _. Defined.

    Definition Inv (i : nat) (D : dist C) : Prop :=
      filter shallow D = filter shallow (r i) ∧ (∀ x, x ∈ D → length (mnode x.1) ≤ Mx)
      ∧ dmass_of Pf D = dmass_of Pf (r i).

    Lemma SM_eq n : length n ≤ Mx → SM n = S n.
    Proof. intros Hl. unfold SM. rewrite bool_decide_false; [apply orb_false_r|lia]. Qed.

    Lemma agree_sh c ρ σ Δ : length (mnode c) < Mx → (mstep U ρ c σ Δ ↔ mstep IM ρ c σ Δ).
    Proof.
      intros Hl. split; intros Hs.
      - destruct (mstep_cell _ _ _ _ _ Hs) as [[Hall _]|(o & Ho & HJ & _)]; [apply Hall|].
        apply HJ. split; done.
      - apply (mstep_mono IM U); [intros n o [Hn _]; exact Hn|exact Hs].
    Qed.

    Lemma frontier c ρ σ Δ : Mx ≤ length (mnode c) → mstep IM ρ c σ Δ → ∀ y, y ∈ Δ → mnode y.1 = mnode c.
    Proof.
      intros Hl Hs y Hy. destruct (mstep_cell _ _ _ _ _ Hs) as [[_ Hn]|(o & [_ Ho] & _ & _)]; [exact (Hn y Hy)|lia].
    Qed.

    Lemma pf_shallow_zero (D : dist C) : dmass_of Pf (filter shallow D) = prob_zero.
    Proof.
      apply dmass_of_none. intros x Hx [Hl _]. apply list_elem_of_filter in Hx as [Hx _].
      unfold shallow in Hx. lia.
    Qed.

    Lemma pf_deep (D : dist C) : dmass_of Pf D = dmass_of Pf (filter (λ x, ¬ shallow x) D).
    Proof. rewrite (dmass_of_split shallow Pf D), pf_shallow_zero. apply prob_add_zero. Qed.

    Lemma in_shallow i D x : Inv i D → x ∈ D → shallow x → x ∈ r i.
    Proof.
      intros [HD _] Hx Hsh. assert (Hf : x ∈ filter shallow D) by (apply list_elem_of_filter; done).
      rewrite HD in Hf. exact (proj2 (proj1 (list_elem_of_filter _ _ _) Hf)).
    Qed.

    Lemma frozen i D σ D' : Inv i D →
      (∀ x Δ, x ∈ D → shallow x → S (mnode x.1) = false → ¬ mstep U x.2 x.1 σ Δ) →
      dstep (SchedSts0 := mdlts IM SM) Stay D σ D' → Inv i D'.
    Proof.
      intros HI Hno (_ & Δs & HF & ->).
      assert (HF' : Forall2 (λ x Δ, x ∈ D ∧ comp_step (SchedSts0 := mdlts IM SM) Stay x.2 x.1 σ Δ) D Δs).
      { refine (Forall2_mem_impl _ _ _ _ HF _). intros x Δ Hx _ Hc. by split. }
      destruct HI as (HD1 & HD2 & HD3).
      destruct (dsum_keep shallow Pf _ _ _ HF') as [E1 E2].
      - intros [c ρ] Δ [Hin Hc] Hsh. destruct Hc as [(Hns & Hs)|(_ & ->)]; [|done].
        exfalso. assert (Hl : length (mnode c) < Mx) by exact Hsh.
        apply (Hno (c, ρ) Δ Hin Hsh).
        + simpl in Hns. rewrite SM_eq in Hns by lia. simpl. destruct (S (mnode c)); [by exfalso|done].
        + exact (proj2 (agree_sh c ρ σ Δ Hl) Hs).
      - intros [c ρ] Δ [Hin Hc] Hsh. assert (Hl : Mx ≤ length (mnode c)) by (unfold shallow in Hsh; simpl in Hsh; lia).
        destruct Hc as [(Hns & Hs)|(_ & ->)].
        + split; [|exact (mstep_mass _ _ _ _ _ Hs)]. intros y Hy.
          pose proof (frontier c ρ σ Δ Hl Hs y Hy) as Ey. unfold shallow, Pf. simpl. rewrite Ey. tauto.
        + split; [intros y Hy; change (y ∈ [(c, ρ)]) in Hy; apply list_elem_of_singleton in Hy; subst y; done|].
          simpl. by rewrite prob_add_zero_r.
      - split; [by rewrite E1|]. split; [|by rewrite E2].
        intros y Hy. destruct (forall2_dsum_elem _ _ _ y HF Hy) as ([c ρ] & Δ & Hx & Hc & Hy').
        destruct Hc as [(_ & Hs)|(_ & ->)].
        + destruct (decide (length (mnode c) < Mx)) as [Hl|Hl].
          * pose proof (mstep_depth _ _ _ _ _ y Hs Hy'). simpl in *. lia.
          * rewrite (frontier c ρ σ Δ ltac:(lia) Hs y Hy'). exact (HD2 _ Hx).
        + change (y ∈ [(c, ρ)]) in Hy'. apply list_elem_of_singleton in Hy'. subst y. exact (HD2 _ Hx).
    Qed.

    Lemma skip i D : Inv i D → ¬ dmoves (SchedSts0 := mdlts IM SM) D (w i) → Inv (Datatypes.S i) D.
    Proof.
      intros HI Hnm. pose proof HI as (HD1 & HD2 & HD3).
      destruct (proj2 Hw i) as [(_ & Δs & HF & E)|(_ & E)]; [|unfold Inv; rewrite E; exact HI].
      assert (HF' : Forall2 (λ x Δ, x ∈ r i ∧ comp_step (SchedSts0 := mdlts U S) Stay x.2 x.1 (w i) Δ) (r i) Δs).
      { refine (Forall2_mem_impl _ _ _ _ HF _). intros x Δ Hx _ Hc. by split. }
      destruct (dsum_keep shallow Pf _ _ _ HF') as [E1 E2].
      - intros [c ρ] Δ [Hin Hc] Hsh. destruct Hc as [(Hns & Hs)|(_ & ->)]; [|done].
        exfalso. assert (Hl : length (mnode c) < Mx) by exact Hsh. apply Hnm. exists c, ρ, Δ. split.
        + assert (Hx : (c, ρ) ∈ filter shallow (r i)) by (apply list_elem_of_filter; done).
          rewrite <- HD1 in Hx. exact (proj2 (proj1 (list_elem_of_filter _ _ _) Hx)).
        + split.
          * simpl. rewrite SM_eq by lia. exact Hns.
          * exact (proj1 (agree_sh c ρ (w i) Δ Hl) Hs).
      - intros [c ρ] Δ [Hin Hc] Hsh. assert (Hl : Mx ≤ length (mnode c)) by (unfold shallow in Hsh; simpl in Hsh; lia).
        destruct Hc as [(Hns & Hs)|(_ & ->)].
        + split; [|exact (mstep_mass _ _ _ _ _ Hs)]. intros y Hy.
          destruct (deep_step Mx _ _ _ _ _ Hl Hs y Hy) as [Hly Ht].
          unfold shallow, Pf. simpl. rewrite Ht. split; [lia|]. split; intros [_ Hs']; split; done || lia.
        + split; [intros y Hy; change (y ∈ [(c, ρ)]) in Hy; apply list_elem_of_singleton in Hy; subst y; done|].
          simpl. by rewrite prob_add_zero_r.
      - split; [by rewrite HD1, E, E1|]. split; [done|]. by rewrite HD3, E, E2.
    Qed.

    Lemma move i D : Inv i D → dmoves (SchedSts0 := mdlts IM SM) D (w i) →
      ∃ D', dstep (SchedSts0 := mdlts IM SM) Stay D (w i) D' ∧ Inv (Datatypes.S i) D'.
    Proof.
      intros HI Hm. pose proof HI as (HD1 & HD2 & HD3).
      destruct (proj2 Hw i) as [(_ & Δs & HF & E)|(Hst & E)].
      2: { destruct (forall2_exists _ D (λ x _, comp_step_exists (mdlts IM SM) (w i) x)) as (Δs & HF).
           assert (Hd : dstep (SchedSts0 := mdlts IM SM) Stay D (w i) (dsum Δs)) by (split; [exact Hm|by exists Δs]).
           exists (dsum Δs). split; [exact Hd|]. unfold Inv. rewrite E.
           apply (frozen i D (w i)); [exact HI| |exact Hd].
           intros x Δ Hx Hsh Hns Hs. apply (Hst (w i)). exists x.1, x.2, Δ.
           split; [destruct x; exact (in_shallow i D _ HI Hx Hsh)|]. split; [simpl; rewrite Hns; discriminate|exact Hs]. }
      set (R1 := λ x Δ, x ∈ r i ∧ comp_step (SchedSts0 := mdlts U S) Stay x.2 x.1 (w i) Δ).
      set (R2 := λ x Δ, x ∈ D ∧ comp_step (SchedSts0 := mdlts IM SM) Stay x.2 x.1 (w i) Δ).
      assert (HF1 : Forall2 R1 (r i) Δs) by (refine (Forall2_mem_impl _ _ _ _ HF _); intros x Δ Hx _ Hc; by split).
      destruct (merge shallow R1 R2 (r i) Δs D HF1 HD1) as (ΔsD & HFD & Hsel).
      - intros [c ρ] Δ Hsh [Hin Hc]. assert (Hl : length (mnode c) < Mx) by exact Hsh. split.
        + assert (Hx : (c, ρ) ∈ filter shallow (r i)) by (apply list_elem_of_filter; done).
          rewrite <- HD1 in Hx. exact (proj2 (proj1 (list_elem_of_filter _ _ _) Hx)).
        + destruct Hc as [(Hns & Hs)|(Hst & ->)].
          * left. split; [simpl; rewrite SM_eq by lia; exact Hns|exact (proj1 (agree_sh c ρ (w i) Δ Hl) Hs)].
          * right. split; [|done]. destruct Hst as [Hs|Hs].
            -- left. simpl. rewrite SM_eq by lia. exact Hs.
            -- right. intros Δ' Hs'. exact (Hs Δ' (proj2 (agree_sh c ρ (w i) Δ' Hl) Hs')).
      - intros x Hx _. destruct (comp_step_exists (mdlts IM SM) (w i) x) as (Δ & HΔ). exists Δ. by split.
      - assert (HFD' : Forall2 (λ x Δ, comp_step (SchedSts0 := mdlts IM SM) Stay x.2 x.1 (w i) Δ) D ΔsD).
        { refine (Forall2_mem_impl _ _ _ _ HFD _). intros x Δ _ _ [_ Hc]. exact Hc. }
        assert (Hd : dstep (SchedSts0 := mdlts IM SM) Stay D (w i) (dsum ΔsD)) by (split; [exact Hm|by exists ΔsD]).
        assert (H2 : ∀ x Δ, R2 x Δ → ¬ shallow x → (∀ y, y ∈ Δ → mnode y.1 = mnode x.1) ∧ dmass Δ = mass x.2).
        { intros [c ρ] Δ [Hin Hc] Hsh. assert (Hl : Mx ≤ length (mnode c)) by (unfold shallow in Hsh; simpl in Hsh; lia).
          destruct Hc as [(_ & Hs)|(_ & ->)].
          - split; [exact (frontier c ρ (w i) Δ Hl Hs)|exact (mstep_mass _ _ _ _ _ Hs)].
          - split; [intros y Hy; change (y ∈ [(c, ρ)]) in Hy; apply list_elem_of_singleton in Hy; by subst y|].
            simpl. by rewrite prob_add_zero_r. }
        assert (H1 : ∀ x Δ, R1 x Δ → ¬ shallow x →
          (∀ y, y ∈ Δ → Mx ≤ length (mnode y.1) ∧ take Mx (mnode y.1) = take Mx (mnode x.1)) ∧ dmass Δ = mass x.2).
        { intros [c ρ] Δ [Hin Hc] Hsh. assert (Hl : Mx ≤ length (mnode c)) by (unfold shallow in Hsh; simpl in Hsh; lia).
          destruct Hc as [(_ & Hs)|(_ & ->)].
          - split; [exact (deep_step Mx _ _ _ _ _ Hl Hs)|exact (mstep_mass _ _ _ _ _ Hs)].
          - split; [intros y Hy; change (y ∈ [(c, ρ)]) in Hy; apply list_elem_of_singleton in Hy; by subst y|].
            simpl. by rewrite prob_add_zero_r. }
        exists (dsum ΔsD). split; [exact Hd|]. split; [|split].
        + rewrite E, (dsel_filter shallow shallow R2 D ΔsD HFD), Hsel, <- (dsel_filter shallow shallow R1 (r i) Δs HF1).
          * done.
          * intros x Δ HR Hsh y Hy Hy'. destruct (H1 x Δ HR Hsh) as [Hy1 _]. destruct (Hy1 y Hy) as [Hl _].
            unfold shallow in Hy'. lia.
          * intros x Δ HR Hsh y Hy. unfold shallow. rewrite (proj1 (H2 x Δ HR Hsh) y Hy). exact Hsh.
        + intros y Hy. destruct (forall2_dsum_elem _ _ _ y HFD Hy) as ([c ρ] & Δ & Hx & [_ Hc] & Hy').
          destruct Hc as [(_ & Hs)|(_ & ->)].
          * destruct (decide (length (mnode c) < Mx)) as [Hl|Hl].
            -- pose proof (mstep_depth _ _ _ _ _ y Hs Hy'). simpl in *. lia.
            -- rewrite (frontier c ρ (w i) Δ ltac:(lia) Hs y Hy'). exact (HD2 _ Hx).
          * change (y ∈ [(c, ρ)]) in Hy'. apply list_elem_of_singleton in Hy'. subst y. exact (HD2 _ Hx).
        + rewrite E, (dsel_mass shallow Pf R2 D ΔsD HFD), Hsel, (dsel_mass shallow Pf R1 (r i) Δs HF1).
          * f_equal. rewrite <- !pf_deep. exact HD3.
          * intros [c ρ] Δ HR Hsh. destruct (H1 _ Δ HR Hsh) as [Hy Hmass]. apply dmass_of_const; [|exact Hmass].
            intros y Hy'. destruct (Hy y Hy') as [Hl Ht]. unfold Pf. simpl in *. rewrite Ht.
            assert (Hc : Mx ≤ length (mnode c)) by (unfold shallow in Hsh; simpl in Hsh; lia). tauto.
          * intros [c ρ] Δ HR Hsh. destruct (H2 _ Δ HR Hsh) as [Hy Hmass]. apply dmass_of_const; [|exact Hmass].
            intros y Hy'. unfold Pf. simpl in *. rewrite (Hy y Hy'). done.
    Qed.

    Lemma succ_le i D : Inv i D →
      dmass_of (λ c, SM (mnode c) = true) D ≤ₚ dmass_of (λ c, S (mnode c) = true) (r i).
    Proof.
      intros (HD1 & HD2 & HD3).
      rewrite (dmass_of_congr _ (λ c, S (mnode c) = true) D); [|intros c ρ Hin; rewrite SM_eq; [done|exact (HD2 _ Hin)]].
      rewrite (dmass_of_split shallow _ D), (dmass_of_split shallow _ (r i)), HD1.
      apply prob_add_mono2; [reflexivity|].
      rewrite (dmass_of_congr (λ c, S (mnode c) = true) Pf (filter (λ x, ¬ shallow x) D)).
      - rewrite <- pf_deep, HD3, pf_deep. apply dmass_of_mono. intros [c ρ] _ [_ Hs]. simpl.
        rewrite <- (take_drop Mx (mnode c)). apply ext_closed_app; [exact HS|exact Hs].
      - intros c ρ Hin. apply list_elem_of_filter in Hin as [Hsh Hin]. pose proof (HD2 _ Hin) as Hl.
        unfold shallow in Hsh. simpl in *. unfold Pf. rewrite take_ge by lia. split; [intros Hs; split; [lia|done]|tauto].
    Qed.

    Hypothesis Hq0 : ∀ x, x ∈ r 0 → mnode x.1 = [].

    Notation Tmoves := (dmoves (SchedSts0 := mdlts IM SM)).
    Notation TDstep := (dstep (SchedSts0 := mdlts IM SM) Stay).
    Notation Tstable := (dstable (SchedSts0 := mdlts IM SM)).
    Notation Qstable := (dstable (SchedSts0 := mdlts U S)).

    Record st := mkst { s_i : nat; s_D : dist C; s_b : bool; s_σ : Sch }.

    Definition Good (x : st) : Prop :=
      Inv (s_i x) (s_D x) ∧ (s_b x = true → ∀ k, s_i x ≤ k → filter shallow (r k) = filter shallow (r (s_i x))).

    Definition StepRel (x y : st) : Prop :=
      (s_b x = false ∧ s_b y = false ∧ ∃ k, s_i x ≤ k ∧ (∀ k', s_i x ≤ k' → k' < k → ¬ Tmoves (s_D x) (w k'))
         ∧ Tmoves (s_D x) (w k) ∧ s_σ y = w k ∧ s_i y = Datatypes.S k ∧ TDstep (s_D x) (w k) (s_D y))
      ∨ (s_b y = true ∧ s_i y = s_i x ∧ (s_b x = true ∨ ∀ k, s_i x ≤ k → ¬ Tmoves (s_D x) (w k))
         ∧ (TDstep (s_D x) (s_σ y) (s_D y) ∨ (Tstable (s_D x) ∧ s_D y = s_D x))).

    Lemma skips i k D : Inv i D → i ≤ k → (∀ k', i ≤ k' → k' < k → ¬ Tmoves D (w k')) → Inv k D.
    Proof.
      intros HI Hik Hn. induction k as [|k IH].
      - assert (i = 0) by lia. by subst.
      - destruct (decide (i = Datatypes.S k)) as [->|Hne]; [done|].
        apply skip; [apply IH; [lia|intros k' H1 H2; apply Hn; lia]|apply Hn; lia].
    Qed.

    Lemma persist i D : Inv i D → (∀ k, i ≤ k → ¬ Tmoves D (w k)) →
      ∀ k, i ≤ k → filter shallow (r k) = filter shallow (r i).
    Proof.
      intros HI Hn k Hk. pose proof (skips i k D HI Hk (λ k' H1 _, Hn k' H1)) as [Hk1 _].
      rewrite <- Hk1. exact (proj1 HI).
    Qed.

    Lemma persist_in i x : (∀ k, i ≤ k → filter shallow (r k) = filter shallow (r i)) →
      x ∈ r i → shallow x → ∀ k, i ≤ k → x ∈ r k.
    Proof.
      intros Hp Hx Hsh k Hk. assert (Hf : x ∈ filter shallow (r i)) by (apply list_elem_of_filter; done).
      rewrite <- (Hp k Hk) in Hf. exact (proj2 (proj1 (list_elem_of_filter _ _ _) Hf)).
    Qed.

    Lemma persist_frozen i D : (∀ k, i ≤ k → filter shallow (r k) = filter shallow (r i)) → Inv i D →
      ∀ σ x Δ, x ∈ D → shallow x → S (mnode x.1) = false → ¬ mstep U x.2 x.1 σ Δ.
    Proof.
      intros Hp HI σ [c ρ] Δ Hx Hsh Hs. pose proof (in_shallow i D _ HI Hx Hsh) as Hi.
      exact (proj1 (Hfair i c ρ (persist_in i (c, ρ) Hp Hi Hsh) Hs) σ Δ).
    Qed.

    Lemma step_exists (x : st) : Good x → ∃ y, Good y ∧ StepRel x y.
    Proof.
      destruct x as [i D b σ0]. intros [HI Hb]. simpl in *.
      destruct (classic (b = false ∧ ∃ k, i ≤ k ∧ Tmoves D (w k))) as [[-> (k & Hik & Hk)]|Hn].
      - destruct (least_nat (λ k, Tmoves D (w k)) i k Hik Hk) as (k0 & H1 & H2 & H3).
        destruct (move k0 D (skips i k0 D HI H1 H3) H2) as (D' & Hd & HI').
        exists (mkst (Datatypes.S k0) D' false (w k0)). split; [split; [exact HI'|done]|].
        left. simpl. split; [done|]. split; [done|]. exists k0. done.
      - assert (Hnm : b = true ∨ ∀ k, i ≤ k → ¬ Tmoves D (w k)).
        { destruct b; [by left|right]. intros k Hk Hm. apply Hn. split; [done|]. by exists k. }
        assert (Hp : ∀ k, i ≤ k → filter shallow (r k) = filter shallow (r i)).
        { destruct Hnm as [->|Hnm]; [by apply Hb|exact (persist i D HI Hnm)]. }
        destruct (classic (Tstable D)) as [Hst|Hst].
        + exists (mkst i D true msch). split; [split; [exact HI|intros _; exact Hp]|].
          right. simpl. split; [done|]. split; [done|]. split; [exact Hnm|]. by right.
        + assert (Hm : ∃ σ, Tmoves D σ).
          { apply NNPP. intros Hc. apply Hst. intros σ Hσ. apply Hc. by exists σ. }
          destruct Hm as (σ & Hσ). destruct (dstep_exists (SS := mdlts IM SM) Stay D σ Hσ) as (D' & Hd).
          exists (mkst i D' true σ). split.
          * split; [|intros _; exact Hp]. simpl.
            exact (frozen i D σ D' HI (λ x Δ Hx Hsh Hs, persist_frozen i D Hp HI σ x Δ Hx Hsh Hs) Hd).
          * right. simpl. split; [done|]. split; [done|]. split; [exact Hnm|]. by left.
    Qed.

    Lemma construction (DC : dep_choice) :
      ∃ f : nat → st, f 0 = mkst 0 (r 0) false msch ∧ ∀ j, Good (f j) ∧ StepRel (f j) (f (Datatypes.S j)).
    Proof.
      destruct (DC st (λ x y, Good x → Good y ∧ StepRel x y) (mkst 0 (r 0) false msch)) as (f & Hf0 & Hf).
      { intros x. destruct (classic (Good x)) as [Hg|Hg].
        - destruct (step_exists x Hg) as (y & Hy). exists y. intros _. exact Hy.
        - exists x. intros Hc. by exfalso. }
      assert (HG : ∀ j, Good (f j)).
      { intros j. induction j as [|j IH]; [|exact (proj1 (Hf j IH))].
        rewrite Hf0. split; [|simpl; discriminate]. split; [done|]. split; [|done].
        intros x Hx. simpl in Hx. rewrite (Hq0 x Hx). simpl. lia. }
      exists f. split; [done|]. intros j. split; [exact (HG j)|exact (proj2 (Hf j (HG j)))].
    Qed.

    Section Built.
      Context (f : nat → st).
      Hypothesis Hf0 : f 0 = mkst 0 (r 0) false msch.
      Hypothesis Hf : ∀ j, Good (f j) ∧ StepRel (f j) (f (Datatypes.S j)).

      Definition rr (j : nat) : dist C := s_D (f j).
      Definition ww (j : nat) : Sch := s_σ (f (Datatypes.S j)).

      Lemma trun_run : run_word IM SM (r 0) rr ww.
      Proof.
        split; [unfold rr; by rewrite Hf0|]. intros j. unfold rr, ww.
        destruct (proj2 (Hf j)) as [(_ & _ & k & _ & _ & _ & Hσ & _ & Hd)|(_ & _ & _ & [Hd|[Hst E]])].
        - left. rewrite Hσ. exact Hd.
        - left. exact Hd.
        - right. split; [exact Hst|exact E].
      Qed.

      Lemma Qrun : is_run (SchedSts0 := mdlts U S) Stay (r 0) r.
      Proof. exact (run_word_is_run _ _ _ _ _ Hw). Qed.

      Lemma depth_r t x : x ∈ r t → length (mnode x.1) ≤ t.
      Proof. exact (run_depth _ _ _ _ Qrun Hq0 t x). Qed.

      Lemma stable_from t t' : Qstable (r t) → t ≤ t' → r t' = r t.
      Proof.
        intros Hst Ht. induction t' as [|t' IH]; [assert (t = 0) by lia; by subst|].
        destruct (decide (t = Datatypes.S t')) as [->|Hne]; [done|].
        assert (IH' : r t' = r t) by (apply IH; lia).
        destruct (proj2 Hw t') as [Hd|[_ E]].
        - exfalso. rewrite IH' in Hd. exact (dstep_not_stable _ _ _ _ Hd Hst).
        - rewrite E. exact IH'.
      Qed.

      Lemma align_step t j : s_i (f j) = t → s_D (f j) = r t → s_b (f j) = false → t < Mx → ¬ Qstable (r t) →
        ww j = w t ∧ TDstep (r t) (w t) (rr (Datatypes.S j)) ∧ s_i (f (Datatypes.S j)) = Datatypes.S t
          ∧ s_b (f (Datatypes.S j)) = false.
      Proof.
        intros E1 E2 E3 Ht Hst.
        destruct (proj2 Hw t) as [Hd|[Hs _]]; [|done].
        assert (Hmv : Tmoves (r t) (w t)).
        { destruct Hd as ((c & ρ & Δ & Hin & Hns & Hs) & _). exists c, ρ, Δ. split; [done|].
          pose proof (depth_r t (c, ρ) Hin) as Hl. simpl in Hl.
          split; [simpl; rewrite SM_eq by lia; exact Hns|exact (proj1 (agree_sh c ρ (w t) Δ ltac:(lia)) Hs)]. }
        unfold rr, ww.
        destruct (proj2 (Hf j)) as [(Hb & Hb' & k & H1 & H2 & H3 & H4 & H5 & H6)|(_ & _ & [Hb|Hn] & _)].
        - rewrite E1 in H1, H2. rewrite E2 in H2, H3, H6.
          assert (Ek : k = t).
          { destruct (decide (k = t)) as [|Hne]; [done|]. exfalso. apply (H2 t); [lia|lia|exact Hmv]. }
          subst k. split; [exact H4|]. split; [exact H6|]. split; [exact H5|exact Hb'].
        - rewrite E3 in Hb. discriminate.
        - exfalso. apply (Hn t); [rewrite E1; lia|rewrite E2; exact Hmv].
      Qed.

      Lemma align t : t < Mx → (∀ t', t' < t → ¬ Qstable (r t')) →
        ∃ j, s_i (f j) = t ∧ s_D (f j) = r t ∧ s_b (f j) = false.
      Proof.
        induction t as [|t IH]; intros Ht Hns.
        - exists 0. rewrite Hf0. done.
        - destruct IH as (j & E1 & E2 & E3); [lia|intros t' Ht'; apply Hns; lia|].
          destruct (align_step t j E1 E2 E3 ltac:(lia) (Hns t ltac:(lia))) as (_ & Hd & E4 & E5).
          exists (Datatypes.S j). split; [exact E4|]. split; [|exact E5].
          pose proof (proj1 (proj1 (proj1 (Hf (Datatypes.S j))))) as Hfl. rewrite E4 in Hfl.
          transitivity (filter shallow (s_D (f (Datatypes.S j)))).
          + symmetry. apply filter_all. intros y Hy.
            change (y ∈ rr (Datatypes.S j)) in Hy. destruct Hd as (_ & Δs & HF & E). rewrite E in Hy.
            assert (Hd0 : ∀ x, x ∈ r t → length (mnode x.1) ≤ t) by exact (depth_r t).
            pose proof (comps_depth _ _ _ _ _ _ HF Hd0 y Hy). unfold shallow. lia.
          + rewrite Hfl. apply filter_all. intros y Hy. pose proof (depth_r _ y Hy). unfold shallow. lia.
      Qed.

      Lemma rr0 : rr 0 = r 0.
      Proof. unfold rr. by rewrite Hf0. Qed.

      Lemma trun_run0 : run_word IM SM (rr 0) rr ww.
      Proof. rewrite rr0. exact trun_run. Qed.

      Lemma trun_init x : x ∈ rr 0 → visited_ok IM (mnode x.1).
      Proof. rewrite rr0. exact (init_visited (r 0) IM Hq0 x). Qed.

      Lemma not_stable_before t : ¬ Qstable (r t) → ∀ t', t' < t → ¬ Qstable (r t').
      Proof. intros Hmv t' Ht' Hst. apply Hmv. rewrite (stable_from t' t Hst ltac:(lia)). exact Hst. Qed.

      Lemma SM_false_S n : SM n = false → S n = false.
      Proof. unfold SM. intros E. apply orb_false_iff in E. exact (proj1 E). Qed.

      Lemma inv_at j : Inv (s_i (f j)) (rr j).
      Proof. exact (proj1 (proj1 (Hf j))). Qed.

      Lemma C1 n o : cells SM rr ww n o → U n o.
      Proof. intros Hc. exact (proj1 (cells_sub IM SM rr ww trun_run0 trun_init n o Hc)). Qed.

      Lemma C2 n o : cells_lt Mx S r w n o → cells SM rr ww n o.
      Proof.
        intros (t & c & ρ & Δ & Ht & Hin & Hs & Hfr & Hne & Hsg & Hsub).
        assert (En : n = mnode c) by exact (single_node _ _ _ _ _ _ Hfr Hsg).
        assert (HU : U n o) by (exists t, c, ρ, Δ; done).
        assert (Hmv : ¬ Qstable (r t)).
        { intros Hst. apply (Hst (w t)). exists c, ρ, Δ. split; [done|]. split; [simpl; rewrite Hs; discriminate|].
          destruct (mstep_off _ _ _ _ _ Hfr Hsg) as (o' & [_ Eo] & HJ & _). apply HJ. subst. exact HU. }
        destruct (align t ltac:(lia) (not_stable_before t Hmv)) as (j & E1 & E2 & E3).
        destruct (align_step t j E1 E2 E3 ltac:(lia) Hmv) as (Ew & _ & E4 & _).
        pose proof (inv_at (Datatypes.S j)) as [HI1 _]. rewrite E4 in HI1.
        exists j, c, ρ, Δ. split; [unfold rr; rewrite E2; done|].
        split; [rewrite SM_eq; [done|pose proof (depth_r t _ Hin); simpl in *; lia]|].
        split; [rewrite Ew; done|]. split; [done|]. split; [rewrite Ew; done|].
        intros y Hy. pose proof (Hsub y Hy) as Hy'.
        assert (Hf' : y ∈ filter shallow (r (Datatypes.S t))).
        { apply list_elem_of_filter. split; [|done]. pose proof (depth_r _ y Hy'). unfold shallow. lia. }
        rewrite <- HI1 in Hf'. exact (proj2 (proj1 (list_elem_of_filter _ _ _) Hf')).
      Qed.

      Lemma C3 n o : refused_lt Mx U S r w n o → refused IM SM rr ww n o.
      Proof.
        intros (t & c & ρ & Ht & Hin & Hs & [(Hd & Hno & Hsg)|(Hst & Hsg)]).
        - pose proof (dstep_not_stable _ _ _ _ Hd) as Hmv.
          destruct (align t ltac:(lia) (not_stable_before t Hmv)) as (j & E1 & E2 & E3).
          destruct (align_step t j E1 E2 E3 ltac:(lia) Hmv) as (Ew & Hd' & _ & _).
          exists j, c, ρ. split; [unfold rr; rewrite E2; done|].
          split; [rewrite SM_eq; [done|pose proof (depth_r t _ Hin); simpl in *; lia]|].
          left. split; [unfold rr at 1; rewrite E2, Ew; exact Hd'|]. rewrite Ew. split; [|exact Hsg].
          intros Δ' Hc'. apply (Hno Δ'). exact (mstep_mono IM U _ _ _ _ (λ n' o' H', proj1 H') Hc').
        - destruct (least_nat (λ t, Qstable (r t)) 0 t ltac:(lia) Hst) as (t0 & _ & Hst0 & Hmin).
          assert (Ht0 : t0 ≤ t).
          { destruct (decide (t0 ≤ t)) as [|Hlt]; [done|]. exfalso. exact (Hmin t ltac:(lia) ltac:(lia) Hst). }
          destruct (align t0 ltac:(lia) (λ t' Ht', Hmin t' ltac:(lia) Ht')) as (j & E1 & E2 & E3).
          assert (Et : r t = r t0) by exact (stable_from t0 t Hst0 Ht0).
          assert (HT : Tstable (r t0)).
          { intros σ (c' & ρ' & Δ' & Hin' & Hns' & Hs'). apply (Hst0 σ). exists c', ρ', Δ'. split; [done|].
            split; [|exact (mstep_mono IM U _ _ _ _ (λ n' o' H', proj1 H') Hs')].
            intros HS'. apply Hns'. simpl. unfold SM. simpl in HS'. rewrite HS'. done. }
          exists j, c, ρ. split; [unfold rr; rewrite E2, <- Et; done|].
          split; [rewrite SM_eq; [done|pose proof (depth_r t _ Hin); simpl in *; lia]|].
          right. split; [unfold rr; rewrite E2; exact HT|exact Hsg].
      Qed.

      Lemma C4 n o : length n < Mx → refused IM SM rr ww n o → refused U S r w n o.
      Proof.
        intros Hn (j & c & ρ & Hin & Hs & Hcase).
        assert (En : n = mnode c).
        { destruct Hcase as [(Hd & Hno & Δ & Hsg)|(Hst & σ & Δ & Hsg)].
          - destruct (classic (mfree (ww j))) as [Hfr|Hfr]; [|exact (single_node _ _ _ _ _ _ Hfr Hsg)].
            exfalso. apply (Hno Δ). exact (proj1 (mstep_free _ _ _ _ _ Hfr Hsg) IM).
          - destruct (classic (mfree σ)) as [Hfr|Hfr]; [|exact (single_node _ _ _ _ _ _ Hfr Hsg)].
            exfalso. apply (Hst σ). exists c, ρ, Δ. split; [done|].
            split; [simpl; rewrite Hs; discriminate|exact (proj1 (mstep_free _ _ _ _ _ Hfr Hsg) IM)]. }
        subst n. assert (Hsh : shallow (c, ρ)) by exact Hn.
        pose proof (SM_false_S _ Hs) as HsS.
        destruct (Hf j) as [[HI Hb] Hstep]. unfold rr in Hin.
        pose proof (in_shallow _ _ _ HI Hin Hsh) as Hi.
        destruct Hstep as [(Hb0 & _ & k & H1 & H2 & H3 & H4 & _ & _)|(_ & _ & Hnm & _)].
        - pose proof (skips _ k _ HI H1 H2) as HIk. pose proof (in_shallow _ _ _ HIk Hin Hsh) as Hk.
          destruct Hcase as [(Hd & Hno & Hsg)|(Hst & _)].
          + unfold ww in Hno, Hsg. rewrite H4 in Hno, Hsg.
            exists k, c, ρ. split; [done|]. split; [done|]. destruct (proj2 Hw k) as [Hdk|(Hstk & _)].
            * left. split; [exact Hdk|]. split; [|exact Hsg]. intros Δ' Hc'. apply (Hno Δ').
              exact (proj1 (agree_sh c ρ (w k) Δ' Hn) Hc').
            * right. split; [exact Hstk|]. destruct Hsg as (Δ & Hsg). exists (w k), Δ. exact Hsg.
          + exfalso. unfold rr in Hst. exact (Hst (w k) H3).
        - assert (Hp : ∀ k, s_i (f j) ≤ k → filter shallow (r k) = filter shallow (r (s_i (f j)))).
          { destruct Hnm as [Hbt|Hnm]; [exact (Hb Hbt)|exact (persist _ _ HI Hnm)]. }
          destruct (Hfair (s_i (f j)) c ρ (persist_in _ (c, ρ) Hp Hi Hsh) HsS) as [_ Href].
          destruct Hcase as [(_ & _ & Δ & Hsg)|(_ & σ & Δ & Hsg)]; exact (Href _ _ _ Hsg).
      Qed.

      Lemma built_props N : (∀ x, x ∈ r 0 → x.2 ≠ weight_zero) → N < Mx →
        (∀ n o, length n < N → (U n o → cells_lt Mx S r w n o) ∧ (refused U S r w n o → refused_lt Mx U S r w n o)) →
        run_word (cells SM rr ww) SM (r 0) rr ww
        ∧ (∀ n o, cells SM rr ww n o → U n o)
        ∧ (∀ n o, length n < N → (cells SM rr ww n o ↔ U n o)
             ∧ (refused (cells SM rr ww) SM rr ww n o ↔ refused U S r w n o))
        ∧ (∀ j, ∃ i, dmass_of (λ c, SM (mnode c) = true) (rr j) ≤ₚ dmass_of (λ c, S (mnode c) = true) (r i))
        ∧ (∀ j x, x ∈ rr j → length (mnode x.1) ≤ Mx).
      Proof.
        intros Hnz0 HN HT.
        assert (Hnz : ∀ j x, x ∈ rr j → x.2 ≠ weight_zero).
        { intros j. refine (run_weights (SchedSts0 := mdlts IM SM) Stay (λ ρ, ρ ≠ weight_zero)
            (λ ρ c σ Δ Hg Hs, mstep_nonzero IM ρ c σ Δ Hg Hs) (rr 0) rr (run_word_is_run _ _ _ _ _ trun_run0) _ j).
          rewrite rr0. exact Hnz0. }
        pose proof (run_cells IM SM rr ww trun_run0 trun_init Hnz) as Hrun.
        pose proof (ref_cells IM SM rr ww trun_run0 trun_init Hnz) as Href.
        split; [rewrite <- rr0; exact Hrun|]. split; [exact C1|]. split.
        - intros n o Hn. destruct (HT n o Hn) as [HTU HTR]. split; split.
          + exact (C1 n o).
          + intros HU. exact (C2 n o (HTU HU)).
          + intros HR. rewrite Href in HR. exact (C4 n o ltac:(lia) HR).
          + intros HR. rewrite Href. exact (C3 n o (HTR HR)).
        - split.
          + intros j. exists (s_i (f j)). exact (succ_le _ _ (inv_at j)).
          + intros j x Hx. exact (proj1 (proj2 (inv_at j)) x Hx).
      Qed.
    End Built.

    Theorem trunc_fair (DC : dep_choice) N : (∀ x, x ∈ r 0 → x.2 ≠ weight_zero) → N < Mx →
      (∀ n o, length n < N → (U n o → cells_lt Mx S r w n o) ∧ (refused U S r w n o → refused_lt Mx U S r w n o)) →
      ∃ r' w', run_word (cells SM r' w') SM (r 0) r' w'
        ∧ (∀ n o, cells SM r' w' n o → U n o)
        ∧ (∀ n o, length n < N → (cells SM r' w' n o ↔ U n o)
             ∧ (refused (cells SM r' w') SM r' w' n o ↔ refused U S r w n o))
        ∧ (∀ j, ∃ i, dmass_of (λ c, SM (mnode c) = true) (r' j) ≤ₚ dmass_of (λ c, S (mnode c) = true) (r i))
        ∧ (∀ j x, x ∈ r' j → length (mnode x.1) ≤ Mx).
    Proof.
      intros Hnz0 HN HT. destruct (construction DC) as (f & Hf0 & Hf).
      exists (rr f), (ww f). exact (built_props f Hf0 Hf N Hnz0 HN HT).
    Qed.
  End Trunc.
End Fair.

Section Limit.
  Context `{WeightLaws} {C Sch A Off : Type} `{M : !MenuSts C Sch A Off} (Ok : Off → Prop).
  Notation node := (list A).

  Theorem co_fair_limit (DC : dep_choice) (Dp Dq : dist C) (S : node → bool) (r : nat → dist C) (w : nat → Sch) :
    run_word (cells S r w) S Dq r w → mext_closed S → fair S r w →
    (∀ x, x ∈ Dq → mnode x.1 = []) → (∀ x, x ∈ Dq → x.2 ≠ weight_zero) → (∀ x, x ∈ Dp → mnode x.1 = []) →
    (∀ n o, cells S r w n o → Ok o) →
    (∀ D, ∃ l : list (dist C), ∀ D', rstep (mdlts (co_menu Ok (cells S r w) (refused (cells S r w) S r w))
        (co_success S (co_menu Ok (cells S r w) (refused (cells S r w) S r w)) (cells S r w))) D D' →
        ∃ D'', D'' ∈ l ∧ succ_eqv (mdlts (co_menu Ok (cells S r w) (refused (cells S r w) S r w))
          (co_success S (co_menu Ok (cells S r w) (refused (cells S r w) S r w)) (cells S r w))) D' D'') →
    (∀ N, ∃ Mx, N < Mx ∧ ∀ n o, length n < N →
        (cells S r w n o → cells_lt Mx S r w n o)
        ∧ (refused (cells S r w) S r w n o → refused_lt Mx (cells S r w) S r w n o)) →
    (∀ Mx r' w', run_word (cells (SM S Mx) r' w') (SM S Mx) Dq r' w' →
        (∀ n o, cells (SM S Mx) r' w' n o → cells S r w n o) → (∀ j x, x ∈ r' j → length (mnode x.1) ≤ Mx) →
        ∃ I π' R', co_run I (co_success (SM S Mx) (co_menu Ok (cells (SM S Mx) r' w')
                     (refused (cells (SM S Mx) r' w') (SM S Mx) r' w')) (cells (SM S Mx) r' w')) Dp π' R'
          ∧ co_below Ok (SM S Mx) (cells (SM S Mx) r' w') (refused (cells (SM S Mx) r' w') (SM S Mx) r' w')
              (λ i, co_dist (r' i)) I π' R') →
    ∃ I π' R', co_run I (co_success S (co_menu Ok (cells S r w) (refused (cells S r w) S r w)) (cells S r w)) Dp π' R'
      ∧ co_below Ok S (cells S r w) (refused (cells S r w) S r w) (λ i, co_dist (r i)) I π' R'.
  Proof.
    intros Hw HS Hfair Hq Hnz Hp0 Hok Hfin HT Halt.
    assert (Hw0 : run_word (cells S r w) S (r 0) r w) by (split; [done|apply Hw]).
    assert (Hq0 : ∀ x, x ∈ r 0 → mnode x.1 = []) by (rewrite (proj1 Hw); exact Hq).
    assert (Hnz0 : ∀ x, x ∈ r 0 → x.2 ≠ weight_zero) by (rewrite (proj1 Hw); exact Hnz).
    apply (co_limit Ok DC Dp Dq S (λ i, co_dist (r i)) (cells S r w) (refused (cells S r w) S r w));
      [by exists r, w|done|done|exact Hfin|].
    intros N. destruct (HT N) as (Mx & HN & HTN).
    destruct (trunc_fair S r w Mx Hw0 HS Hfair Hq0 DC N Hnz0 HN HTN) as (r' & w' & Hw' & Hsub & Hag & Hsucc & Hdep).
    rewrite (proj1 Hw) in Hw'.
    destruct (Halt Mx r' w' Hw' Hsub Hdep) as (I & π' & R' & Hrun & Hbel).
    exists (SM S Mx), (λ i, co_dist (r' i)), (cells (SM S Mx) r' w'),
      (refused (cells (SM S Mx) r' w') (SM S Mx) r' w'), I, π', R'.
    split; [by exists r', w'|]. split; [intros n o Hc; exact (Hok n o (Hsub n o Hc))|].
    split; [exact Hrun|]. split; [exact Hbel|].
    assert (HJ : ∀ n o, length n < N →
      (co_menu Ok (cells (SM S Mx) r' w') (refused (cells (SM S Mx) r' w') (SM S Mx) r' w') n o
       ↔ co_menu Ok (cells S r w) (refused (cells S r w) S r w) n o)).
    { intros n o Hn. destruct (Hag n o Hn) as [H1 H2]. unfold co_menu. rewrite H1, H2. done. }
    split; [exact HJ|]. split.
    - intros n Hn. unfold co_success. rewrite SM_eq by lia.
      assert (Hl : co_left (co_menu Ok (cells (SM S Mx) r' w') (refused (cells (SM S Mx) r' w') (SM S Mx) r' w'))
                     (cells (SM S Mx) r' w') n
                   ↔ co_left (co_menu Ok (cells S r w) (refused (cells S r w) S r w)) (cells S r w) n).
      { split; intros (m & a & m2 & En & Hj & Hu); exists m, a, m2; split; try done;
          (assert (Hm : length m < N) by (subst n; rewrite !length_app in Hn; simpl in Hn; lia)).
        - split; [exact (proj1 (HJ m _ Hm) Hj)|]. intros Hu'. apply Hu. exact (proj2 (proj1 (Hag m _ Hm)) Hu').
        - split; [exact (proj2 (HJ m _ Hm) Hj)|]. intros Hu'. apply Hu. exact (proj1 (proj1 (Hag m _ Hm)) Hu'). }
      destruct (excluded_middle_informative (co_left _ _ n)) as [Ha|Ha];
        destruct (excluded_middle_informative (co_left _ _ n)) as [Hb|Hb]; try done; exfalso; tauto.
    - intros m. destruct (Hsucc m) as (i & Hi). exists i. rewrite !co_dist_mass. exact Hi.
  Qed.
End Limit.
(* end hide *)
