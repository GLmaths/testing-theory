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
From Stdlib.Bool Require Import Bool.
From Stdlib.Logic Require Import Classical_Prop.
From Stdlib Require Import Lia.
Import ListNotations.
From stdpp Require Import base countable decidable list.
From TestingTheory Require Import ActTau pMust_almost_sure pMust_smyth pMust_transfer pMust_canonical.
From TestingTheory Require Import lqCCS.Harmony_Lemma.Lifted lqCCS.Harmony_Lemma.Paths lqCCS.Harmony_Lemma.States lqCCS.Language.Quantum lqCCS.Language.Quantum_Weights.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.LTS lqCCS.Testing.Scheduled lqCCS.Testing.DistLTS lqCCS.Testing.Programs lqCCS.Testing.Observers lqCCS.Testing.Smyth_Soundness lqCCS.Testing.Canonical lqCCS.Testing.Pull lqCCS.Testing.Head lqCCS.Testing.Modes.

#[local] Open Scope lqccs_scope.

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

Section Syn.
  Context (TG : tag * okind → Prop) (OC IC : channel → Prop).

  Definition syn (Y : proc) : Prop :=
    obsb Y = true ∧ (∀ x, x ∈ tagged Y → TG x) ∧ (∀ c, c ∈ out_chans Y → OC c) ∧ (∀ c, c ∈ in_chans Y → IC c).

  Definition gsyn (g : guard) : Prop :=
    gobsb g = true ∧ gsuccessb g = false ∧ (∀ x, x ∈ gtagged g → TG x)
    ∧ (∀ c, c ∈ gout_chans g → OC c) ∧ (∀ c, c ∈ gin_chans g → IC c).

  Lemma syn_nil : syn 𝟘.
  Proof. split; [done|]. repeat split; intros x Hx; by apply elem_of_nil in Hx. Qed.

  Lemma syn_succ : syn (PG ①).
  Proof. split; [done|]. repeat split; intros x Hx; by apply elem_of_nil in Hx. Qed.

  Lemma syn_par P Q : syn P → syn Q → syn (P ∥ Q).
  Proof.
    intros (Ho1 & Ht1 & Hc1 & Hi1) (Ho2 & Ht2 & Hc2 & Hi2). split; [simpl; by rewrite Ho1, Ho2|].
    repeat split; intros x Hx; simpl in Hx; apply elem_of_app in Hx as [Hx|Hx]; auto.
  Qed.

  Lemma syn_par_inv P Q : syn (P ∥ Q) → syn P ∧ syn Q.
  Proof.
    intros (Ho & Ht & Hc & Hi). simpl in *. apply andb_prop in Ho as [Ho1 Ho2].
    split; (split; [done|]); repeat split; intros x Hx.
    - apply Ht, elem_of_app. by left.
    - apply Hc, elem_of_app. by left.
    - apply Hi, elem_of_app. by left.
    - apply Ht, elem_of_app. by right.
    - apply Hc, elem_of_app. by right.
    - apply Hi, elem_of_app. by right.
  Qed.

  Lemma syn_ite e P Q : syn P → syn Q → syn (PIte e P Q).
  Proof.
    intros (Ho1 & Ht1 & Hc1 & Hi1) (Ho2 & Ht2 & Hc2 & Hi2). split; [simpl; by rewrite Ho1, Ho2|].
    repeat split; intros x Hx; simpl in Hx; apply elem_of_app in Hx as [Hx|Hx]; auto.
  Qed.

  Lemma syn_ite_inv e P Q : syn (PIte e P Q) → syn P ∧ syn Q.
  Proof.
    intros (Ho & Ht & Hc & Hi). simpl in *. apply andb_prop in Ho as [Ho1 Ho2].
    split; (split; [done|]); repeat split; intros x Hx.
    - apply Ht, elem_of_app. by left.
    - apply Hc, elem_of_app. by left.
    - apply Hi, elem_of_app. by left.
    - apply Ht, elem_of_app. by right.
    - apply Hc, elem_of_app. by right.
    - apply Hi, elem_of_app. by right.
  Qed.

  Lemma syn_subst k v P : syn P → syn (subst k v P).
  Proof. unfold syn. by rewrite obsb_subst, tagged_subst, out_chans_subst, in_chans_subst. Qed.

  Lemma syn_shiftv k P : syn P → syn (shiftv k P).
  Proof. unfold syn. by rewrite obsb_shiftv, tagged_shiftv, out_chans_shiftv, in_chans_shiftv. Qed.

  Lemma syn_sh 𝜆 Q : syn Q → syn (sh 𝜆 Q).
  Proof.
    intros HQ. unfold sh. induction (prefix_binds 𝜆) as [|n IH]; simpl; [done|]. by apply syn_shiftv.
  Qed.

  Lemma syn_PG g : gsyn g → syn (PG g).
  Proof. intros (Ho & _ & Ht & Hc & Hi). by split. Qed.

  Lemma syn_bagof X : syn X → syn (bagof X).
  Proof.
    induction X as [t c e|e P IHP Q IHQ|P IHP Q IHQ|P IHP|x|t x P IHP|g]; simpl; intros HX; try apply syn_nil.
    - done.
    - apply syn_ite_inv in HX as [HP HQ]. destruct (eval e) as [[[]| |]|]; auto using syn_nil.
    - apply syn_par_inv in HX as [HP HQ]. apply syn_par; auto.
  Qed.

  Lemma syn_ns X : syn X → syn (ns X).
  Proof.
    induction X as [t c e|e P IHP Q IHQ|P IHP Q IHQ|P IHP|x|t x P IHP|g]; simpl; intros HX; try done.
    - apply syn_nil.
    - apply syn_ite_inv in HX as [HP HQ]. destruct (eval e) as [[[]| |]|]; auto using syn_nil.
    - apply syn_par_inv in HX as [HP HQ]. apply syn_par; auto.
  Qed.

  Definition hsynP (h : prefix * proc) : Prop :=
    syn h.2 ∧ TG (prefix_tagged h.1) ∧ (∀ t, h.1 ≠ PTau t) ∧ (∀ k c, h.1 = PRecv k c → IC c).

  Lemma gheads_syn g h : syn (PG g) → h ∈ gheads g → hsynP h.
  Proof.
    induction g as [es| |𝜆 P|g1 IH1 g2 IH2]; simpl; intros (Ho & Ht & Hc & Hi) Hin.
    - by apply elem_of_nil in Hin.
    - by apply elem_of_nil in Hin.
    - apply list_elem_of_singleton in Hin. subst h. simpl in *.
      assert (HP : syn P).
      { split; [by destruct 𝜆|]. split; [intros x Hx; apply Ht; by right|]. split; [done|].
        intros c Hc0. apply Hi. destruct 𝜆; simpl; try done. by right. }
      unfold hsynP. simpl. split; [done|]. split; [apply Ht; by left|].
      split; [intros t E; subst 𝜆; simpl in Ho; discriminate Ho|].
      intros k c E. subst 𝜆. apply Hi. simpl. by left.
    - simpl in *. apply andb_prop in Ho as [[Ho1 Ho2]%andb_prop _].
      apply elem_of_app in Hin as [Hin|Hin]; [apply IH1|apply IH2]; try done.
      + split; [done|]. repeat split; intros x Hx; [apply Ht|apply Hc|apply Hi]; apply elem_of_app; by left.
      + split; [done|]. repeat split; intros x Hx; [apply Ht|apply Hc|apply Hi]; apply elem_of_app; by right.
  Qed.

  Lemma heads_syn Z h : syn Z → h ∈ heads Z → hsynP h.
  Proof.
    revert h. induction Z as [t c e|e P IHP Q IHQ|P IHP Q IHQ|P IHP|x|t x P IHP|g]; simpl; intros h HZ Hin.
    - by apply elem_of_nil in Hin.
    - apply syn_ite_inv in HZ as [HP HQ]. destruct (eval e) as [[[]| |]|]; try (by apply elem_of_nil in Hin); auto.
    - apply syn_par_inv in HZ as [HP HQ].
      apply elem_of_app in Hin as [Hin|Hin]; apply list_elem_of_In, in_map_iff in Hin as (h0 & <- & Hin);
        apply list_elem_of_In in Hin.
      + destruct (IHP h0 HP Hin) as (H1 & H2 & H3 & H4). split; [|done]. simpl. apply syn_par; [done|by apply syn_sh].
      + destruct (IHQ h0 HQ Hin) as (H1 & H2 & H3 & H4). split; [|done]. simpl. apply syn_par; [by apply syn_sh|done].
    - by apply elem_of_nil in Hin.
    - by apply elem_of_nil in Hin.
    - by apply elem_of_nil in Hin.
    - exact (gheads_syn g h HZ Hin).
  Qed.

  Lemma syn_chain vs A d : (∀ v, syn (A v)) → syn d → syn (chain vs A d).
  Proof.
    intros HA Hd. induction vs as [|v vs IH]; simpl; [done|]. apply syn_ite; [|done]. by apply syn_shiftv.
  Qed.

  Lemma gsyn_pre 𝜆 P :
    (∀ t, 𝜆 ≠ PTau t) → TG (prefix_tagged 𝜆) → (∀ k c, 𝜆 = PRecv k c → IC c) → syn P → gsyn (𝜆 ∙ P).
  Proof.
    intros Hnt Htg Hic (Ho & Ht & Hc & Hi). split; [destruct 𝜆; simpl; try done; by destruct (Hnt t)|].
    split; [done|]. split; [|split; [done|]].
    - intros x Hx. simpl in Hx. apply elem_of_cons in Hx as [->|Hx]; auto.
    - intros c Hc0. destruct 𝜆; simpl in Hc0; auto. apply elem_of_cons in Hc0 as [->|Hc0]; [by eapply Hic|auto].
  Qed.

  Lemma gsyn_nil : gsyn (GNil []).
  Proof. split; [done|]. split; [done|]. repeat split; intros x Hx; by apply elem_of_nil in Hx. Qed.

  Lemma gsum_syn (l : list guard) : (∀ g, g ∈ l → gsyn g) → gsyn (gsum l).
  Proof.
    induction l as [|g l IH]; intros Hl; [apply gsyn_nil|].
    destruct (Hl g ltac:(by left)) as (Ho1 & Hs1 & Ht1 & Hc1 & Hi1).
    destruct IH as (Ho2 & Hs2 & Ht2 & Hc2 & Hi2); [intros g' Hg'; apply Hl; by right|].
    split; [simpl; by rewrite Ho1, Ho2, Hs1, Hs2|]. split; [simpl; by rewrite Hs1, Hs2|].
    repeat split; intros x Hx; simpl in Hx; apply elem_of_app in Hx as [Hx|Hx]; auto.
  Qed.

  Context (VL : list val) (reps : node → list offer) (wrapb : node → offer → bool).
  Hypothesis Hreps : ∀ m o, o ∈ reps m → TG (off_tag o, off_kind o) ∧ ∀ k c, o = OffIn k c → IC c.

  Lemma kont_syn rec m o a Z' : (∀ m' X', syn X' → syn (rec m' X')) → syn Z' → syn (kont wrapb rec m o a Z').
  Proof. intros Hrec HZ. unfold kont. destruct (wrapb m o); [apply syn_par; [apply syn_succ|done]|by apply Hrec]. Qed.

  Lemma dflt_syn m o D : syn D → syn (dflt wrapb m o D).
  Proof. intros HD. unfold dflt. destruct (wrapb m o); [apply syn_par; [apply syn_succ|done]|done]. Qed.

  Lemma hguard_syn rec m h g :
    (∀ m' X', syn X' → syn (rec m' X')) → hsynP h → hguard VL wrapb rec m h = Some g → gsyn g.
  Proof.
    intros Hrec (HD & Htg & Hnt & Hic) Hg. destruct h as [𝜆 D]. unfold hguard in Hg.
    destruct 𝜆 as [t|t c|t E es|t M es|t es]; simpl in *.
    - discriminate Hg.
    - injection Hg as <-. apply gsyn_pre; [done|done| |].
      + exact Hic.
      + apply syn_chain; [|by apply dflt_syn]. intros v. apply kont_syn; [done|by apply syn_subst].
    - destruct (eval_qubits es) as [qs|]; [|discriminate Hg]. injection Hg as <-.
      apply gsyn_pre; [done|done|done|]. by apply kont_syn.
    - destruct (eval_qubits es) as [qs|]; [|discriminate Hg]. injection Hg as <-.
      apply gsyn_pre; [done|done|done|]. apply syn_chain; [|by apply dflt_syn].
      intros v. destruct v; try apply syn_nil. apply kont_syn; [done|by apply syn_subst].
    - destruct (eval_qubits es) as [qs|]; [|discriminate Hg]. injection Hg as <-.
      apply gsyn_pre; [done|done|done|]. by apply kont_syn.
  Qed.

  Lemma rg_syn m o g : o ∈ reps m → rg o = Some g → gsyn g.
  Proof.
    intros Hin Hg. destruct (Hreps m o Hin) as [Htg Hic].
    destruct o as [k c v|k c|k E qs|k M qs|k qs]; simpl in *; [discriminate Hg|injection Hg as <-..];
      (apply gsyn_pre; [done|done| |apply syn_succ]); try done.
    intros k0 c0 [= <- <-]. by apply (Hic k c).
  Qed.

  Lemma hsum_syn rec m Z : (∀ m' X', syn X' → syn (rec m' X')) → syn Z → gsyn (hsum VL reps wrapb rec m Z).
  Proof.
    intros Hrec HZ. apply gsum_syn. intros g Hg.
    apply elem_of_app in Hg as [Hg|Hg]; apply list_elem_of_omap in Hg as (x & Hx & Eg).
    - exact (hguard_syn rec m x g Hrec (heads_syn Z x HZ Hx) Eg).
    - unfold repl in Hx. apply list_elem_of_filter in Hx as [_ Hx]. exact (rg_syn m x g Hx Eg).
  Qed.

  Lemma tn_syn f : ∀ m X, syn X → syn (tn VL reps wrapb f m X).
  Proof.
    induction f as [|f IH]; intros m X HX; simpl; [done|]. destruct (successb X); [done|].
    apply syn_par; [by apply syn_bagof|]. apply syn_PG, hsum_syn; [exact IH|by apply syn_ns].
  Qed.
End Syn.
(* end hide *)
