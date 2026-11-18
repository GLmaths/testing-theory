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
From Stdlib Require Import Lia.
Import ListNotations.
From stdpp Require Import base gmultiset countable decidable list numbers.
From TestingTheory Require Import ActTau.
From TestingTheory Require Import lqCCS.lqCCS_prog.Syntax lqCCS.Helper_substitution.De_Brujin_lemmas lqCCS.General_definition.Parallel_choice_LTS lqCCS.quantum_mem.LTS lqCCS.lqCCS_prog.LTS lqCCS.lqCCS_par_Qmem.LTS lqCCS.lqCCS_process.LTS.LTS lqCCS.Testing.Scheduled lqCCS.Testing.Observer_predicates.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

Section LqP.
  Context `{LP : lqCCS_Parameters}.

(* ** Tags *)

Lemma prefix_tagged_subst k v 𝜆 : prefix_tagged (prefix_subst k v 𝜆) = prefix_tagged 𝜆.
Proof. by destruct 𝜆. Qed.

Lemma prefix_tagged_shift k 𝜆 : prefix_tagged (prefix_shift k 𝜆) = prefix_tagged 𝜆.
Proof. by destruct 𝜆. Qed.

Lemma prefix_tagged_ren f 𝜆 : prefix_tagged (prefix_ren f 𝜆) = prefix_tagged 𝜆.
Proof. by destruct 𝜆. Qed.

Lemma tagged_subst k v P : tagged (P ⁅ v // k ⁆ᵥ) = tagged P
with gtagged_gsubst k v g : gtagged (gsubst k v g) = gtagged g.
Proof.
  - destruct P; simpl; try done; try (by rewrite !tagged_subst); try apply gtagged_gsubst.
  - destruct g; simpl; try done; try (by rewrite !gtagged_gsubst).
    by rewrite prefix_tagged_subst, tagged_subst.
Qed.

Lemma tagged_shiftv k P : tagged (shiftv k P) = tagged P
with gtagged_gshiftv k g : gtagged (gshiftv k g) = gtagged g.
Proof.
  - destruct P; simpl; try done; try (by rewrite !tagged_shiftv); try apply gtagged_gshiftv.
  - destruct g; simpl; try done; try (by rewrite !gtagged_gshiftv).
    by rewrite prefix_tagged_shift, tagged_shiftv.
Qed.

Lemma tagged_ren f P : tagged (ren f P) = tagged P
with gtagged_gren f g : gtagged (gren f g) = gtagged g.
Proof.
  - destruct P; simpl; try done; try (by rewrite !tagged_ren); try apply gtagged_gren.
  - destruct g; simpl; try done; try (by rewrite !gtagged_gren).
    by rewrite prefix_tagged_ren, tagged_ren.
Qed.

Lemma tagged_shiftv_iter n P : tagged (Nat.iter n ⇧ᵥ P) = tagged P.
Proof. induction n as [|n IH]; simpl; [done|]. by rewrite tagged_shiftv. Qed.

Lemma tagged_rshift k P : tagged (rshift k P) = tagged P
with gtagged_grshift k g : gtagged (grshift k g) = gtagged g.
Proof.
  - destruct P; simpl; try done; try (by rewrite !tagged_rshift); try apply gtagged_grshift. by case_decide.
  - destruct g; simpl; try done; try (by rewrite !gtagged_grshift). by rewrite tagged_rshift.
Qed.

Lemma tagged_pr_subst k P Q x :
  x ∈ tagged (P ⁅ Q // k ⁆ₚ) → x ∈ tagged P ∨ x ∈ tagged Q
with gtagged_gpr_subst k g Q x :
  x ∈ gtagged (gpr_subst k g Q) → x ∈ gtagged g ∨ x ∈ tagged Q.
Proof.
  - destruct P; simpl; intros Hx.
    + by left.
    + apply elem_of_app in Hx as [Hx|Hx]; apply tagged_pr_subst in Hx as [Hx|Hx]; auto;
        left; apply elem_of_app; auto.
    + apply elem_of_app in Hx as [Hx|Hx]; apply tagged_pr_subst in Hx as [Hx|Hx]; auto;
        left; apply elem_of_app; auto.
    + apply tagged_pr_subst in Hx as [Hx|Hx]; [by left|]. right. by rewrite tagged_ren in Hx.
    + repeat case_decide; [by right| |]; simpl in Hx; by apply elem_of_nil in Hx.
    + apply elem_of_cons in Hx as [->|Hx]; [left; by left|].
      apply tagged_pr_subst in Hx as [Hx|Hx]; [left; by right|right; by rewrite tagged_rshift in Hx].
    + by apply (gtagged_gpr_subst k).
  - destruct g; simpl; intros Hx.
    + by left.
    + by left.
    + apply elem_of_cons in Hx as [->|Hx]; [left; by left|].
      apply tagged_pr_subst in Hx as [Hx|Hx]; [left; by right|]. right. by rewrite tagged_shiftv_iter in Hx.
    + apply elem_of_app in Hx as [Hx|Hx]; apply gtagged_gpr_subst in Hx as [Hx|Hx]; auto;
        left; apply elem_of_app; auto.
Qed.

Lemma prefix_tagged_tren f 𝜆 : prefix_tagged (prefix_tren f 𝜆) = (f (prefix_tagged 𝜆).1, (prefix_tagged 𝜆).2).
Proof. by destruct 𝜆. Qed.

Lemma tagged_tren f P : tagged (tren f P) = map (λ x, (f x.1, x.2)) (tagged P)
with gtagged_gtren f g : gtagged (gtren f g) = map (λ x, (f x.1, x.2)) (gtagged g).
Proof.
  - destruct P; simpl; rewrite ?map_app; try done; try (by rewrite !tagged_tren); try apply gtagged_gtren.
  - destruct g; simpl; rewrite ?map_app; try done; try (by rewrite !gtagged_gtren).
    by rewrite prefix_tagged_tren, tagged_tren.
Qed.

(* Along a step, the tags of a program only decrease, up to their generation. *)

(* ** Success and observers *)

Lemma successb_ren f P : successb (ren f P) = successb P
with gsuccessb_gren f g : gsuccessb (gren f g) = gsuccessb g.
Proof.
  - destruct P; simpl; try done.
    + destruct (eval e) as [[b| |]|]; try done. destruct b; apply successb_ren.
    + by rewrite !successb_ren.
  - destruct g; simpl; try done. by rewrite !gsuccessb_gren.
Qed.

Lemma gsuccessb_gsubst k v g : gsuccessb (gsubst k v g) = gsuccessb g.
Proof. induction g; simpl; try done. by rewrite IHg1, IHg2. Qed.


Lemma obsb_subst k v P : obsb (P ⁅ v // k ⁆ᵥ) = obsb P
with gobsb_gsubst k v g : gobsb (gsubst k v g) = gobsb g.
Proof.
  - destruct P; simpl; try done; try (by rewrite !obsb_subst); try apply gobsb_gsubst.
  - destruct g; simpl; try done; try (by rewrite !gobsb_gsubst, !gsuccessb_gsubst);
      try (destruct 𝜆; simpl; try done; apply obsb_subst).
Qed.

Lemma out_chans_subst k v P : out_chans (P ⁅ v // k ⁆ᵥ) = out_chans P
with gout_chans_gsubst k v g : gout_chans (gsubst k v g) = gout_chans g.
Proof.
  - destruct P; simpl; try done; try (by rewrite !out_chans_subst); try apply out_chans_subst;
      try apply gout_chans_gsubst.
  - destruct g; simpl; try done; try (by rewrite !gout_chans_gsubst);
      try (destruct 𝜆; simpl; apply out_chans_subst).
Qed.

Lemma in_chans_subst k v P : in_chans (P ⁅ v // k ⁆ᵥ) = in_chans P
with gin_chans_gsubst k v g : gin_chans (gsubst k v g) = gin_chans g.
Proof.
  - destruct P; simpl; try done; try (by rewrite !in_chans_subst); try apply in_chans_subst;
      try apply gin_chans_gsubst.
  - destruct g; simpl; try done; try (by rewrite !gin_chans_gsubst);
      try (destruct 𝜆; simpl; try apply in_chans_subst; by rewrite in_chans_subst).
Qed.

Lemma gsuccessb_gshiftv k g : gsuccessb (gshiftv k g) = gsuccessb g.
Proof. induction g as [es| |𝜆 P|g1 IH1 g2 IH2]; simpl; try done. by rewrite IH1, IH2. Qed.

Lemma obsb_shiftv k P : obsb (shiftv k P) = obsb P
with gobsb_gshiftv k g : gobsb (gshiftv k g) = gobsb g.
Proof.
  - destruct P; simpl; try done; try (by rewrite !obsb_shiftv); try apply gobsb_gshiftv.
  - destruct g; simpl; try done; try (by rewrite !gobsb_gshiftv, !gsuccessb_gshiftv);
      try (destruct 𝜆; simpl; try done; apply obsb_shiftv).
Qed.

Lemma out_chans_shiftv k P : out_chans (shiftv k P) = out_chans P
with gout_chans_gshiftv k g : gout_chans (gshiftv k g) = gout_chans g.
Proof.
  - destruct P; simpl; try done; try (by rewrite !out_chans_shiftv); try apply out_chans_shiftv;
      try apply gout_chans_gshiftv.
  - destruct g; simpl; try done; try (by rewrite !gout_chans_gshiftv);
      try (destruct 𝜆; simpl; apply out_chans_shiftv).
Qed.

Lemma in_chans_shiftv k P : in_chans (shiftv k P) = in_chans P
with gin_chans_gshiftv k g : gin_chans (gshiftv k g) = gin_chans g.
Proof.
  - destruct P; simpl; try done; try (by rewrite !in_chans_shiftv); try apply in_chans_shiftv;
      try apply gin_chans_gshiftv.
  - destruct g; simpl; try done; try (by rewrite !gin_chans_gshiftv);
      try (destruct 𝜆; simpl; try apply in_chans_shiftv; by rewrite in_chans_shiftv).
Qed.

(* ** Recursive observers *)

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

Lemma obsrb_subst k v P : obsrb (P ⁅ v // k ⁆ᵥ) = obsrb P
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

Lemma obsrb_shiftv_iter n P : obsrb (Nat.iter n ⇧ᵥ P) = obsrb P.
Proof. induction n as [|n IH]; simpl; [done|]. by rewrite obsrb_shiftv. Qed.

Lemma out_chans_shiftv_iter n P : out_chans (Nat.iter n ⇧ᵥ P) = out_chans P.
Proof. induction n as [|n IH]; simpl; [done|]. by rewrite out_chans_shiftv. Qed.

Lemma in_chans_shiftv_iter n P : in_chans (Nat.iter n ⇧ᵥ P) = in_chans P.
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

Lemma gsuccessb_grshift k g : gsuccessb (grshift k g) = gsuccessb g.
Proof. induction g as [es| |𝜆 P|g1 IH1 g2 IH2]; simpl; try done. by rewrite IH1, IH2. Qed.

Lemma obsrb_rshift k P : obsrb (rshift k P) = obsrb P
with gobsrb_grshift k g : gobsrb (grshift k g) = gobsrb g.
Proof.
  - destruct P; simpl; try done; try (by rewrite !obsrb_rshift); try apply gobsrb_grshift. by case_decide.
  - destruct g; simpl; try done; try (by rewrite !gobsrb_grshift, !gsuccessb_grshift);
      try (destruct 𝜆; simpl; try done; apply obsrb_rshift).
Qed.

Lemma out_chans_rshift k P : out_chans (rshift k P) = out_chans P
with gout_chans_grshift k g : gout_chans (grshift k g) = gout_chans g.
Proof.
  - destruct P; simpl; try done; try (by rewrite !out_chans_rshift); try apply out_chans_rshift;
      try apply gout_chans_grshift. by case_decide.
  - destruct g; simpl; try done; try (by rewrite !gout_chans_grshift);
      try (destruct 𝜆; simpl; apply out_chans_rshift).
Qed.

Lemma in_chans_rshift k P : in_chans (rshift k P) = in_chans P
with gin_chans_grshift k g : gin_chans (grshift k g) = gin_chans g.
Proof.
  - destruct P; simpl; try done; try (by rewrite !in_chans_rshift); try apply in_chans_rshift;
      try apply gin_chans_grshift. by case_decide.
  - destruct g; simpl; try done; try (by rewrite !gin_chans_grshift);
      try (destruct 𝜆; simpl; try apply in_chans_rshift; by rewrite in_chans_rshift).
Qed.

Lemma gsuccessb_gpr_subst k g Q : gsuccessb (gpr_subst k g Q) = gsuccessb g.
Proof. induction g as [es| |𝜆 P|g1 IH1 g2 IH2]; simpl; try done. by rewrite IH1, IH2. Qed.

Lemma obsrb_pr_subst k P Q : obsrb P = true → obsrb Q = true → obsrb (P ⁅ Q // k ⁆ₚ) = true
with gobsrb_gpr_subst k g Q : gobsrb g = true → obsrb Q = true → gobsrb (gpr_subst k g Q) = true.
Proof.
  - destruct P; simpl; intros HP HQ; try done.
    + apply andb_prop in HP as [H1 H2]. by rewrite (obsrb_pr_subst _ _ _ H1 HQ), (obsrb_pr_subst _ _ _ H2 HQ).
    + apply andb_prop in HP as [H1 H2]. by rewrite (obsrb_pr_subst _ _ _ H1 HQ), (obsrb_pr_subst _ _ _ H2 HQ).
    + by repeat case_decide.
    + apply obsrb_pr_subst; [done|by rewrite obsrb_rshift].
    + by apply gobsrb_gpr_subst.
  - destruct g; simpl; intros Hg HQ; try done.
    + destruct 𝜆; try done; apply obsrb_pr_subst; try done; by rewrite obsrb_shiftv_iter.
    + apply andb_prop in Hg as [[H1 H2]%andb_prop H3].
      by rewrite (gobsrb_gpr_subst _ _ _ H1 HQ), (gobsrb_gpr_subst _ _ _ H2 HQ), !gsuccessb_gpr_subst, H3.
Qed.

Lemma out_chans_pr_subst k P Q c :
  obsrb P = true → c ∈ out_chans (P ⁅ Q // k ⁆ₚ) → c ∈ out_chans P ∨ c ∈ out_chans Q
with gout_chans_gpr_subst k g Q c :
  gobsrb g = true → c ∈ gout_chans (gpr_subst k g Q) → c ∈ gout_chans g ∨ c ∈ out_chans Q.
Proof.
  - destruct P; simpl; intros HP Hc; try done.
    + by left.
    + apply andb_prop in HP as [H1 H2].
      apply elem_of_app in Hc as [Hc|Hc]; [apply (out_chans_pr_subst k) in Hc as [Hc|Hc]; [| |done]|
        apply (out_chans_pr_subst k) in Hc as [Hc|Hc]; [| |done]]; auto; left; apply elem_of_app; auto.
    + apply andb_prop in HP as [H1 H2].
      apply elem_of_app in Hc as [Hc|Hc]; [apply (out_chans_pr_subst k) in Hc as [Hc|Hc]; [| |done]|
        apply (out_chans_pr_subst k) in Hc as [Hc|Hc]; [| |done]]; auto; left; apply elem_of_app; auto.
    + repeat case_decide; [by right| |]; simpl in Hc; by apply elem_of_nil in Hc.
    + destruct (out_chans_pr_subst _ P _ c HP Hc) as [H|H]; [by left|right; by rewrite out_chans_rshift in H].
    + by apply (gout_chans_gpr_subst k).
  - destruct g as [es| |𝜆 P|g1 g2]; simpl; intros Hg Hc.
    + by apply elem_of_nil in Hc.
    + by apply elem_of_nil in Hc.
    + destruct 𝜆; try done; apply (out_chans_pr_subst k) in Hc as [Hc|Hc]; try done; auto;
        rewrite out_chans_shiftv_iter in Hc; auto.
    + apply andb_prop in Hg as [[H1 H2]%andb_prop _].
      apply elem_of_app in Hc as [Hc|Hc]; [apply (gout_chans_gpr_subst k) in Hc as [Hc|Hc]; [| |done]|
        apply (gout_chans_gpr_subst k) in Hc as [Hc|Hc]; [| |done]]; auto; left; apply elem_of_app; auto.
Qed.

Lemma in_chans_pr_subst k P Q c :
  obsrb P = true → c ∈ in_chans (P ⁅ Q // k ⁆ₚ) → c ∈ in_chans P ∨ c ∈ in_chans Q
with gin_chans_gpr_subst k g Q c :
  gobsrb g = true → c ∈ gin_chans (gpr_subst k g Q) → c ∈ gin_chans g ∨ c ∈ in_chans Q.
Proof.
  - destruct P; simpl; intros HP Hc; try (by apply elem_of_nil in Hc); try done.
    + apply andb_prop in HP as [H1 H2].
      apply elem_of_app in Hc as [Hc|Hc]; [apply (in_chans_pr_subst k) in Hc as [Hc|Hc]; [| |done]|
        apply (in_chans_pr_subst k) in Hc as [Hc|Hc]; [| |done]]; auto; left; apply elem_of_app; auto.
    + apply andb_prop in HP as [H1 H2].
      apply elem_of_app in Hc as [Hc|Hc]; [apply (in_chans_pr_subst k) in Hc as [Hc|Hc]; [| |done]|
        apply (in_chans_pr_subst k) in Hc as [Hc|Hc]; [| |done]]; auto; left; apply elem_of_app; auto.
    + repeat case_decide; [by right| |]; simpl in Hc; by apply elem_of_nil in Hc.
    + destruct (in_chans_pr_subst _ P _ c HP Hc) as [H|H]; [by left|right; by rewrite in_chans_rshift in H].
    + by apply (gin_chans_gpr_subst k).
  - destruct g as [es| |𝜆 P|g1 g2]; simpl; intros Hg Hc.
    + by apply elem_of_nil in Hc.
    + by apply elem_of_nil in Hc.
    + destruct 𝜆; simpl in Hg, Hc |- *; try done.
      1: apply elem_of_cons in Hc as [->|Hc]; [left; by left|]; apply (in_chans_pr_subst k) in Hc as [Hc|Hc];
           [left; by right| |done]; rewrite ?in_chans_shiftv in Hc; right; exact Hc.
      all: apply (in_chans_pr_subst k) in Hc as [Hc|Hc]; [by left| |done]; rewrite ?in_chans_shiftv in Hc;
           right; exact Hc.
    + apply andb_prop in Hg as [[H1 H2]%andb_prop _].
      apply elem_of_app in Hc as [Hc|Hc]; [apply (gin_chans_gpr_subst k) in Hc as [Hc|Hc]; [| |done]|
        apply (gin_chans_gpr_subst k) in Hc as [Hc|Hc]; [| |done]]; auto; left; apply elem_of_app; auto.
Qed.

End LqP.

(* end hide *)
