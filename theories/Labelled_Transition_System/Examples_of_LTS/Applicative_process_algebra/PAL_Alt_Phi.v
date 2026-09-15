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
From stdpp Require Import base tactics decidable countable list gmap.
From TestingTheory Require Import ActTau gLts Subset_Act LabelAbstraction PAL_Syntax PAL_Alt_LTS.

(* * The abstraction Φ of the alternative labels of PAL

   [Φ] maps a label to an event of De Nicola–Pugliese (Definition 5.3):
   - [Φ (AIn l) = EvIn (ltemplate l)]: an input with template [ltemplate l],
     the event [(i, p)], whatever the received tuple;
   - [Φ (AOut ot) = EvOut ot]: an output of [ot], the event [(o, ot)].
   Results:
   - [abs_R_spec]: the events [Φ(R p)] of a process form the finite set [abs_R p];
   - [Φ_kernel]: [Φ μ = Φ μ'] iff every process accepting [μ] accepts [μ'].
     So the kernel of [Φ] is the largest [≈ᴛᴇꜱᴛ], and [Φ] is its canonical
     projection ([gLtsLAtest_PALA]). *)

Section PAL_Alt_Phi.
  Context (Val : Type) `{Countable Val} `{!Inhabited Val}.

  Notation term := (term Val).
  Notation tuple := (tuple Val).
  Notation eot := (eot Val).
  Notation eit := (eit Val).
  Notation template := (template Val).
  Notation label := (label Val).
  Notation ltemplate := (ltemplate Val).
  Notation ltuple := (ltuple Val).
  Notation PALA_Act := (PALA_Act Val).
  Notation step := (lts_step_a Val).

  (** Infer the action type of [↛[μ]] from the LTS on terms. *)
  #[local] Hint Mode ExtAction ! : typeclass_instances.
  Open Scope pal_scope.


  (** ** Events and [Φ] *)

  Inductive Event := EvIn (tp : template) | EvOut (ot : eot).

  #[global] Instance Event_eqdec : EqDecision Event.
  Proof. solve_decision. Defined.

  #[global] Instance Event_countable : Countable Event.
  Proof.
    refine (inj_countable'
      (λ e, match e with EvIn tp => inl tp | EvOut ot => inr ot end)
      (λ s, match s with inl tp => EvIn tp | inr ot => EvOut ot end)
      _).
    by intros [].
  Defined.

  Definition Φᴀᴘᴀʟ (μ : PALA_Act) : Event :=
    match μ with
    | AIn _ l => EvIn (ltemplate l)
    | AOut _ ot => EvOut ot
    end.

  (** ** Templates of the inputs of a term *)

  Fixpoint collect_in_a (E : term) : list template :=
    match E with
    | t_in t _ | t_read t _ =>
        match eval_in_tuple t with Some it => [template_of Val it] | None => [] end
    | t_echoice E1 E2 | t_par E1 E2 => collect_in_a E1 ++ collect_in_a E2
    | t_lmerge E1 _ => collect_in_a E1
    | t_if be E1 E2 =>
        match eval_bexp be with
        | Some true => collect_in_a E1
        | Some false => collect_in_a E2
        | None => []
        end
    | _ => []
    end.

  Lemma in_step_in_collect_in_a p l q :
    step p (ActExt (AIn _ l)) q → In (ltemplate l) (collect_in_a p).
  Proof.
    intros h. remember (ActExt (AIn _ l)) as α eqn:eq.
    induction h; try discriminate eq; simpl.
    - injection eq as ->. match goal with hev : eval_in_tuple _ = Some _ |- _ => rewrite hev end. by left.
    - injection eq as ->. match goal with hev : eval_in_tuple _ = Some _ |- _ => rewrite hev end. by left.
    - apply in_or_app. left. by apply IHh.
    - apply in_or_app. right. by apply IHh.
    - apply in_or_app. left. by apply IHh.
    - apply in_or_app. right. by apply IHh.
    - by apply IHh.
    - match goal with hb : eval_bexp _ = Some true |- _ => rewrite hb end. by apply IHh.
    - match goal with hb : eval_bexp _ = Some false |- _ => rewrite hb end. by apply IHh.
  Qed.

  Lemma collect_in_a_step p l :
    In (ltemplate l) (collect_in_a p) → ∃ q, step p (ActExt (AIn _ l)) q.
  Proof.
    induction p; intros hin; simpl in hin; try contradiction.
    - destruct (eval_in_tuple t) as [it|] eqn:ev; [| contradiction].
      destruct hin as [e | []]. eexists. by apply aar1.
    - destruct (eval_in_tuple t) as [it|] eqn:ev; [| contradiction].
      destruct hin as [e | []]. eexists. by apply aar2.
    - destruct (eval_bexp be) as [[]|] eqn:hbe; [| | contradiction].
      + destruct (IHp1 hin) as (q & hq). exists q. by apply aar7.
      + destruct (IHp2 hin) as (q & hq). exists q. by apply aar8.
    - apply in_app_iff in hin as [hin | hin].
      + destruct (IHp1 hin) as (q & hq). exists q. by apply aar4_l.
      + destruct (IHp2 hin) as (q & hq). exists q. by apply aar4_r.
    - apply in_app_iff in hin as [hin | hin].
      + destruct (IHp1 hin) as (q & hq). eexists. by apply aar5_l.
      + destruct (IHp2 hin) as (q & hq). eexists. by apply aar5_r.
    - destruct (IHp1 hin) as (q & hq). eexists. by apply aar6.
  Qed.

  (** An input only depends on the template of its label. *)
  Lemma in_retarget p l l' q :
    step p (ActExt (AIn _ l)) q → ltemplate l' = ltemplate l → ∃ q', step p (ActExt (AIn _ l')) q'.
  Proof. intros h e. apply collect_in_a_step. rewrite e. by eapply in_step_in_collect_in_a. Qed.

  (** A label of a template. *)
  Definition label_witness (tp : template) : label :=
    map (λ f, match f with
              | tf_formal _ => lf_formal Val inhabitant
              | tf_val _ v => lf_val Val v
              | tf_star _ => lf_star Val
              end) tp.

  Lemma ltemplate_label_witness tp : ltemplate (label_witness tp) = tp.
  Proof.
    induction tp as [|[|v|] tp IH]; [done | ..];
      unfold PAL_Alt_LTS.ltemplate, label_witness in *; simpl; by rewrite IH.
  Qed.

  (** ** The events of a process form a finite set *)

  Definition abs_R (p : term) : gset Event :=
    list_to_set (map EvIn (collect_in_a p) ++ map EvOut (collect_out_a Val p)).

  Lemma abs_R_spec p e : e ∈ abs_R p ↔ ∃ μ, ¬ p ↛[μ] ∧ Φᴀᴘᴀʟ μ = e.
  Proof.
    unfold abs_R. rewrite elem_of_list_to_set, list_elem_of_In, in_app_iff, !in_map_iff. split.
    - intros [(tp & <- & hin) | (ot & <- & hin)].
      + rewrite <- (ltemplate_label_witness tp) in hin.
        destruct (collect_in_a_step p _ hin) as (q & hq).
        exists (AIn _ (label_witness tp)). split.
        * intros href. eapply lts_refuses_spec2; [| exact href]. by exists q.
        * cbn [Φᴀᴘᴀʟ]. by rewrite ltemplate_label_witness.
      + destruct (collect_out_witnesses_a Val p ot hin) as [q hq].
        exists (AOut _ ot). split; [| done].
        intros href. eapply lts_refuses_spec2; [| exact href]. by exists q.
    - intros (μ & acc & <-). apply lts_refuses_spec1 in acc as (q & hq).
      destruct μ as [l|ot]; simpl.
      + left. exists (ltemplate l). split; [done | by eapply in_step_in_collect_in_a].
      + right. exists ot. split; [done | by eapply out_step_in_collect_out_a].
  Qed.

  (** ** The kernel of [Φ] is the largest [≈ᴛᴇꜱᴛ] *)

  (** Test side: labels with the same event are accepted by the same processes. *)
  Lemma Φ_test_spec (t : term) μ μ' : Φᴀᴘᴀʟ μ = Φᴀᴘᴀʟ μ' → ¬ t ↛[μ] → ¬ t ↛[μ'].
  Proof.
    intros e acc href. apply lts_refuses_spec1 in acc as (q & hq).
    destruct μ as [l|ot], μ' as [l'|ot']; simpl in e; try discriminate; injection e as e.
    - destruct (in_retarget t l l' q hq (eq_sym e)) as (q' & hq').
      eapply lts_refuses_spec2; [| exact href]. by exists q'.
    - subst. eapply lts_refuses_spec2; [| exact href]. by exists q.
  Qed.

  (** The pattern of template [tp], whose formal fields bind [i], [i+1], ... *)
  Fixpoint pattern_from (i : nat) (tp : template) : tuple :=
    match tp with
    | [] => []
    | f :: tp' =>
        match f with
        | tf_formal _ => ? i
        | tf_val _ v => ! ve_val v
        | tf_star _ => ⋆
        end :: pattern_from (S i) tp'
    end.

  Fixpoint it_from (i : nat) (tp : template) : eit :=
    match tp with
    | [] => []
    | f :: tp' =>
        match f with
        | tf_formal _ => if_formal i
        | tf_val _ v => if_val v
        | tf_star _ => if_star
        end :: it_from (S i) tp'
    end.

  Lemma eval_pattern_from i tp : eval_in_tuple (pattern_from i tp) = Some (it_from i tp).
  Proof.
    revert i. induction tp as [|[|v|] tp IH]; intros i; [done | ..];
      unfold eval_in_tuple in *; simpl; by rewrite IH.
  Qed.

  Lemma template_of_it_from i tp : template_of Val (it_from i tp) = tp.
  Proof.
    revert i. induction tp as [|[|v|] tp IH]; intros i; [done | ..];
      unfold template_of in *; simpl; by rewrite IH.
  Qed.

  Lemma eval_out_eot_to_tuple (ot : eot) : eval_out_tuple (eot_to_tuple ot) = Some ot.
  Proof.
    induction ot as [|[|v] ot IH]; [done | |]; unfold eval_out_tuple in *; simpl; by rewrite IH.
  Qed.

  (** A process accepting exactly the labels of an event. *)
  Definition probe (μ : PALA_Act) : term :=
    match μ with
    | AIn _ l => in( pattern_from 0 (ltemplate l) ) • 𝟘
    | AOut _ ot => out( eot_to_tuple ot ) • 𝟘
    end.

  Lemma probe_accepts μ : ¬ probe μ ↛[μ].
  Proof.
    intros href. eapply lts_refuses_spec2; [| exact href].
    destruct μ as [l|ot]; simpl; eexists.
    - apply aar1; [apply eval_pattern_from | apply template_of_it_from].
    - apply aar3, eval_out_eot_to_tuple.
  Qed.

  Lemma probe_only μ μ' : ¬ probe μ ↛[μ'] → Φᴀᴘᴀʟ μ' = Φᴀᴘᴀʟ μ.
  Proof.
    intros acc. apply lts_refuses_spec1 in acc as (q & hq).
    destruct μ as [l|ot]; unfold probe in hq; simpl in hq; inversion hq; subst.
    - match goal with hev : eval_in_tuple _ = Some _ |- _ =>
        rewrite eval_pattern_from in hev; injection hev as <- end.
      match goal with ht : template_of _ _ = _ |- _ => rewrite template_of_it_from in ht end.
      cbn [Φᴀᴘᴀʟ]. by f_equal.
    - match goal with hev : eval_out_tuple _ = Some _ |- _ =>
        rewrite eval_out_eot_to_tuple in hev; injection hev as <- end.
      done.
  Qed.

  Lemma Φ_complete μ μ' : (∀ t : term, ¬ t ↛[μ] → ¬ t ↛[μ']) → Φᴀᴘᴀʟ μ = Φᴀᴘᴀʟ μ'.
  Proof. intros h. symmetry. apply probe_only, h, probe_accepts. Qed.

  Theorem Φ_kernel μ μ' : Φᴀᴘᴀʟ μ = Φᴀᴘᴀʟ μ' ↔ (𝐏 μ : subset_of term) ⊆ 𝐏 μ'.
  Proof.
    split.
    - intros e p. unfold elem_of, Elements_of, 𝐏. by apply Φ_test_spec.
    - intros hsub. apply Φ_complete. intros t. apply hsub.
  Qed.

  (** ** [≈ᴛᴇꜱᴛ] *)

  Definition R_test_a (μ μ' : PALA_Act) : Prop := Φᴀᴘᴀʟ μ = Φᴀᴘᴀʟ μ'.

  Lemma R_test_a_equivalence : Equivalence R_test_a.
  Proof. unfold R_test_a. split; [done | by intros ?? | by intros ??? -> ->]. Qed.

  Lemma R_test_a_dec : RelDecision R_test_a.
  Proof. intros μ μ'. unfold R_test_a. apply _. Defined.

  Lemma R_test_a_spec μ μ' : R_test_a μ μ' → (𝐏 μ : subset_of term) ⊆ 𝐏 μ'.
  Proof. apply Φ_kernel. Qed.

  #[global] Instance gLtsLAtest_PALA : @gLtsLAtest term PALA_Act (PALA_ExtAction Val) (PALA_gLts Val) :=
    {| LA_test := R_test_a;
       LA_test_eq := R_test_a_equivalence;
       LA_test_dec := R_test_a_dec;
       LA_test_spec := R_test_a_spec |}.

  (** [R_test_a] is the largest [≈ᴛᴇꜱᴛ]. *)
  Lemma R_test_a_largest (R : PALA_Act → PALA_Act → Prop) :
    (∀ μ μ', R μ μ' → (𝐏 μ : subset_of term) ⊆ 𝐏 μ') → ∀ μ μ', R μ μ' → R_test_a μ μ'.
  Proof. intros hR μ μ' h. apply Φ_kernel, hR, h. Qed.
End PAL_Alt_Phi.
