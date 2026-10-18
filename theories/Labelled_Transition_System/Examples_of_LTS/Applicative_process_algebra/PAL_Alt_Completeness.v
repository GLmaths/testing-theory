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
From stdpp Require Import base tactics decidable countable list gmap.
From TestingTheory Require Import ActTau gLts SyncActions Subset_Act Must
  DefinitionAS DefinitionASco CompletenessASco Label_Abstraction.Decidable_dichotomic
  PAL_Syntax PAL_Alt_LTS PAL_Alt_Phi PAL_Alt_AbsAction PAL_Alt_Congruence
  PAL_Good PAL_Must PAL_Alt_Tests PAL_Alt_TestSpec PAL_Alt_CoTraceHypotheses.

Notation term := (term nat).
Notation template := (template nat).
Notation eot := (eot nat).
Notation label := (label nat).

#[local] Hint Mode ExtAction ! : typeclass_instances.
#[local] Existing Instance list_exist_dec.

Definition tf_match (f : tfield nat) (o : out_field nat) : Prop :=
  match f, o with
  | tf_formal _, of_val _ => True
  | tf_val _ v, of_val w => v = w
  | tf_star _, of_star => True
  | _, _ => False
  end.

#[local] Instance tf_match_dec : RelDecision tf_match.
Proof. intros [] []; simpl; apply _. Defined.

Definition t_match (tp : template) (ot : eot) : Prop := Forall2 tf_match tp ot.

#[local] Instance t_match_dec : RelDecision t_match.
Proof. intros tp ot. unfold t_match. apply _. Defined.

Lemma t_match_label tp ot : t_match tp ot ↔ ∃ l, ltemplate nat l = tp ∧ ltuple nat l = ot.
Proof.
  unfold t_match, PAL_Alt_LTS.ltemplate, PAL_Alt_LTS.ltuple. split.
  - induction 1 as [| f o tp ot hf _ (l & <- & <-)].
    + by exists [].
    + destruct f as [| v |], o as [| w]; simpl in hf; try contradiction.
      * exists (lf_formal nat w :: l). done.
      * subst. exists (lf_val nat w :: l). done.
      * exists (lf_star nat :: l). done.
  - intros (l & <- & <-). induction l as [| g l IH]; simpl; constructor; [| exact IH].
    by destruct g.
Qed.

Lemma Γ_coR_iff (p : term) (x : Event nat) :
  x ∈ ⌈ αᴘᴇᴠ nat ∘ αᴛᴀᴘᴀʟ nat ⌉ (coR p) ↔
  (∃ ot, x = EvOut nat ot ∧ ∃ tp, tp ∈ collect_in_a nat p ∧ t_match tp ot)
  ∨ (∃ tp, x = EvIn nat tp ∧ ∃ ot, ot ∈ collect_out_a nat p ∧ t_match tp ot).
Proof.
  split.
  - intros (β & (μ & acc & hs & _) & ->).
    apply lts_performs_spec1 in acc as (q & hq).
    destruct μ as [l | ot], β as [l' | ot']; cbn in hs; try contradiction.
    + left. exists ot'. split; [reflexivity |].
      exists (ltemplate nat l). split.
      * apply list_elem_of_In. exact (in_step_in_collect_in_a nat p l q hq).
      * apply t_match_label. by exists l.
    + right. exists (ltemplate nat l'). split; [reflexivity |].
      exists ot. split.
      * apply list_elem_of_In. exact (out_step_in_collect_out_a nat p ot q hq).
      * apply t_match_label. by exists l'.
  - intros [(ot & -> & tp & hin & hm) | (tp & -> & ot & hin & hm)].
    + apply t_match_label in hm as (l & <- & <-).
      apply list_elem_of_In in hin.
      destruct (collect_in_a_step nat p l hin) as (q & hq).
      exists (AOut nat (ltuple nat l)). split; [| reflexivity].
      exists (AIn nat l). split; [apply lts_performs_spec2; by exists q |].
      split; [reflexivity | by intros []].
    + apply t_match_label in hm as (l & <- & <-).
      apply list_elem_of_In in hin.
      destruct (collect_out_witnesses_a nat p _ hin) as (q & hq).
      exists (AIn nat l). split; [| reflexivity].
      exists (AOut nat (ltuple nat l)). split; [apply lts_performs_spec2; by exists q |].
      split; [reflexivity | by intros []].
Qed.

Fixpoint tbound (tp : template) : nat :=
  match tp with
  | [] => 0
  | tf_val _ v :: tp' => v `max` tbound tp'
  | _ :: tp' => tbound tp'
  end.

Lemma tbound_spec tp v : tf_val nat v ∈ tp → v ≤ tbound tp.
Proof.
  induction tp as [| f tp IH]; intros hv; [by apply elem_of_nil in hv |].
  apply elem_of_cons in hv as [<- | hv]; simpl; [lia |].
  specialize (IH hv). destruct f; lia.
Qed.

Fixpoint tsbound (tps : list template) : nat :=
  match tps with
  | [] => 0
  | tp :: tps' => tbound tp `max` tsbound tps'
  end.

Lemma tsbound_spec tps tp : tp ∈ tps → tbound tp ≤ tsbound tps.
Proof.
  induction tps as [| tp' tps IH]; intros h; [by apply elem_of_nil in h |].
  apply elem_of_cons in h as [-> | h]; simpl; [lia |].
  specialize (IH h). lia.
Qed.

Fixpoint gen_pt (N : nat) (tp : template) : eot :=
  match tp with
  | [] => []
  | tf_formal _ :: tp' => of_val N :: gen_pt N tp'
  | tf_val _ v :: tp' => of_val v :: gen_pt N tp'
  | tf_star _ :: tp' => of_star :: gen_pt N tp'
  end.

Lemma t_match_gen_pt N tp : t_match tp (gen_pt N tp).
Proof. induction tp as [| [] tp IH]; simpl; constructor; simpl; done. Qed.

Lemma t_match_transfer N tp tp' ot :
  (∀ v, tf_val nat v ∈ tp' → v < N) →
  t_match tp' (gen_pt N tp) → t_match tp ot → t_match tp' ot.
Proof.
  unfold t_match. revert tp' ot.
  induction tp as [| f tp IH]; intros tp' ot hN h1 h2.
  - inversion h1; inversion h2; constructor.
  - destruct tp' as [| f' tp']; [destruct f; inversion h1 |].
    destruct ot as [| o ot]; [inversion h2 |].
    assert (hN0 : ∀ v, f' = tf_val nat v → v < N).
    { intros v ->. apply hN. apply list_elem_of_here. }
    assert (hN1 : ∀ v, tf_val nat v ∈ tp' → v < N).
    { intros v hv. apply hN. by apply list_elem_of_further. }
    destruct f as [| v |]; simpl in h1;
      apply Forall2_cons in h1 as [hf1 h1]; apply Forall2_cons in h2 as [hf2 h2];
      constructor; try exact (IH tp' ot hN1 h1 h2).
    + destruct f' as [| w |], o as [| u]; simpl in *; try done.
      specialize (hN0 w eq_refl). lia.
    + destruct o as [| u]; simpl in hf2; [contradiction | subst; exact hf1].
    + destruct o as [| u]; simpl in hf2; [| contradiction].
      destruct f'; simpl in hf1; done.
Qed.

Lemma list_sig {X} (l : list X) (Q : X → Prop) `{∀ x, Decision (Q x)} :
  (∃ x, x ∈ l ∧ Q x) → { x | x ∈ l ∧ Q x }.
Proof.
  induction l as [| y l IH]; intros h.
  - exfalso. destruct h as (x & hx & _). by apply elem_of_nil in hx.
  - destruct (decide (Q y)) as [hy | hy].
    + exists y. split; [apply list_elem_of_here | exact hy].
    + destruct IH as (x & hx & hq).
      * destruct h as (x & hx & hq). apply elem_of_cons in hx as [-> | hx]; [contradiction |].
        by exists x.
      * exists x. split; [by apply list_elem_of_further | exact hq].
Defined.

Lemma PALA_coR_dichotomy (p q : term) :
  (⌈ αᴘᴇᴠ nat ∘ αᴛᴀᴘᴀʟ nat ⌉ (coR p) ⊆ ⌈ αᴘᴇᴠ nat ∘ αᴛᴀᴘᴀʟ nat ⌉ (coR q))
  + { x | x ∈ ⌈ αᴘᴇᴠ nat ∘ αᴛᴀᴘᴀʟ nat ⌉ (coR p) ∧ x ∉ ⌈ αᴘᴇᴠ nat ∘ αᴛᴀᴘᴀʟ nat ⌉ (coR q) }.
Proof.
  set (N := S (tsbound (collect_in_a nat q))).
  destruct (decide (∃ tp, tp ∈ collect_in_a nat p ∧
              ¬ ∃ tp', tp' ∈ collect_in_a nat q ∧ t_match tp' (gen_pt N tp)))
    as [hex | hout].
  { destruct (list_sig _ _ hex) as (tp & htp & hno).
    right. exists (EvOut nat (gen_pt N tp)). split.
    - apply Γ_coR_iff. left. exists (gen_pt N tp). split; [reflexivity |].
      exists tp. split; [exact htp | apply t_match_gen_pt].
    - intros [(ot & e & tp' & htp' & hm) | (tp' & e & _)]%Γ_coR_iff; [| discriminate].
      injection e as <-. apply hno. by exists tp'. }
  destruct (decide (∃ ot, ot ∈ collect_out_a nat p ∧
              ∃ l, l ∈ labels_of nat ot ∧
                ¬ ∃ ot', ot' ∈ collect_out_a nat q ∧ t_match (ltemplate nat l) ot'))
    as [hex | hin].
  { destruct (list_sig _ _ hex) as (ot & hot & hl').
    destruct (list_sig _ _ hl') as (l & hl & hno).
    right. exists (EvIn nat (ltemplate nat l)). split.
    - apply Γ_coR_iff. right. exists (ltemplate nat l). split; [reflexivity |].
      exists ot. split; [exact hot |]. apply t_match_label. exists l. split; [reflexivity |].
      by apply labels_of_spec, list_elem_of_In.
    - intros [(ot' & e & _) | (tp' & e & ot' & hot' & hm)]%Γ_coR_iff; [discriminate |].
      injection e as <-. apply hno. by exists ot'. }
  left. intros x hx. apply Γ_coR_iff.
  apply Γ_coR_iff in hx as [(ot & -> & tp & htp & hm) | (tp & -> & ot & hot & hm)].
  - left. exists ot. split; [reflexivity |].
    destruct (decide (∃ tp', tp' ∈ collect_in_a nat q ∧ t_match tp' (gen_pt N tp)))
      as [(tp' & htp' & hm') | hn]; [| exfalso; apply hout; by exists tp].
    exists tp'. split; [exact htp' |].
    eapply (t_match_transfer N tp tp' ot); [| exact hm' | exact hm].
    intros v hv. pose proof (tbound_spec _ _ hv). pose proof (tsbound_spec _ _ htp'). lia.
  - right. exists tp. split; [reflexivity |].
    apply t_match_label in hm as (l & <- & <-).
    destruct (decide (∃ ot', ot' ∈ collect_out_a nat q ∧ t_match (ltemplate nat l) ot'))
      as [hp | hn]; [exact hp |].
    exfalso. apply hin. exists (ltuple nat l). split; [exact hot |].
    exists l. split; [by apply list_elem_of_In, labels_of_spec | exact hn].
Defined.

Theorem PAL_Alt_completeness (p q : term) :
  p ᴘᴀʟ⊑ₘᵤₛₜᵢ q →
  bhv_pre_co (AbsPT := AbsPALA nat) (AbsQT := AbsPALA nat) p q.
Proof.
  intros hpre.
  pose proof (completeness_fw_co (P := term) (Q := term) (T := term)
                (gLtsEqP := PALA_gLtsEq nat) (gLtsEqQ := PALA_gLtsEq nat)
                (gLtsEqT := PALA_gLtsEq nat) (αᴛᴇꜱᴛ := αᴛᴀᴘᴀʟ nat) (αᴘʀᴏ := αᴘᴇᴠ nat)
                (AbsPT := AbsPALA nat) (AbsQT := AbsPALA nat)
                (test_convergence_spec0 := hyp_test_convergence_spec nat)
                (test_co_acceptance_set_spec0 := hyp_test_co_acceptance_set_spec nat)
                (DichPQ := λ p' q' _ _, PALA_coR_dichotomy p' q')) as hc.
  exact (hc p q hpre).
Qed.
(* end hide *)
