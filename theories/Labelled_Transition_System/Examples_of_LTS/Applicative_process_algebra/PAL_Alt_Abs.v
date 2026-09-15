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
From stdpp Require Import base tactics decidable countable list gmap relations.
From TestingTheory Require Import ActTau gLts Subset_Act LabelAbstraction PAL_Syntax PAL_Alt_LTS
  PAL_Alt_Phi PAL_Alt_Delta.

(* * The abstraction [𝝳ᴀʟᴛ] on events, so that [𝝳ᴀʟᴛ ∘ Φᴀᴘᴀʟ] makes sense

   [𝝳ᴀᴘᴀʟ] ([PAL_Alt_Delta.v]) does not factor through [Φᴀᴘᴀʟ]: two inputs
   with the same template may receive different tuples. The map on events is
   the completion along [Φᴀᴘᴀʟ] of the projection [ρᴀʟᴛ] of the join of
   [≈ᴛᴇꜱᴛ] and [≈ᴘʀᴏ] ([LabelAbstraction.LA_complete]):
   - [𝝳ᴀʟᴛ (EvIn tp) = PIn (shape tp)]: the join relates [[v]], [[?]] and [[w]],
     so only the positions of the [⋆] fields remain;
   - [𝝳ᴀʟᴛ (EvOut ot) = POut ot].
   Results:
   - [ρᴀʟᴛ_proj]: [ρᴀʟᴛ = 𝝳ᴀʟᴛ ∘ Φᴀᴘᴀʟ] is the canonical projection of the join;
   - [𝝳ᴀʟᴛ_complete]: [𝝳ᴀʟᴛ] is the completion of [ρᴀʟᴛ] along [Φᴀᴘᴀʟ];
   - [prog_spec_injective]: any [κ] on events satisfying the process-side
     condition (2) of [AbsAction] is injective on the events [EvOut ⟨v⟩], all
     of which lie in [Φ(coR (in(?x).𝟘))] ([coR_p_formal]); so [κ(Φ(coR p))] is
     infinite as soon as [Val] is;
   - [𝝳ᴀʟᴛ_not_prog_spec]: [𝝳ᴀʟᴛ] itself does not satisfy condition (2). *)

Section PAL_Alt_Abs.
  Context (Val : Type) `{Countable Val} `{!Inhabited Val}.

  Notation term := (term Val).
  Notation eot := (eot Val).
  Notation template := (template Val).
  Notation label := (label Val).
  Notation ltemplate := (ltemplate Val).
  Notation ltuple := (ltuple Val).
  Notation PALA_Act := (PALA_Act Val).
  Notation Event := (Event Val).
  Notation R_test_a := (R_test_a Val).
  Notation R_prog_a := (R_prog_a Val).

  (** Infer the action type of [↛[μ]] from the LTS on terms. *)
  #[local] Hint Mode ExtAction ! : typeclass_instances.
  Open Scope pal_scope.


  #[local] Existing Instance R_test_a_equivalence.
  #[local] Existing Instance R_prog_a_equivalence.

  (** ** [𝝳ᴀʟᴛ] *)

  (** The positions of the [⋆] fields of a template. *)
  Definition shape (tp : template) : list bool :=
    map (λ f, match f with tf_star _ => true | _ => false end) tp.

  Inductive PreEvent := PIn (sh : list bool) | POut (ot : eot).

  #[global] Instance PreEvent_eqdec : EqDecision PreEvent.
  Proof. solve_decision. Defined.

  #[global] Instance PreEvent_countable : Countable PreEvent.
  Proof.
    refine (inj_countable'
      (λ e, match e with PIn sh => inl sh | POut ot => inr ot end)
      (λ s, match s with inl sh => PIn sh | inr ot => POut ot end)
      _).
    by intros [].
  Defined.

  Definition 𝝳ᴀʟᴛ (e : Event) : PreEvent :=
    match e with
    | EvIn _ tp => PIn (shape tp)
    | EvOut _ ot => POut ot
    end.

  Definition ρᴀʟᴛ (μ : PALA_Act) : PreEvent := 𝝳ᴀʟᴛ (Φᴀᴘᴀʟ Val μ).

  (** ** [ρᴀʟᴛ] is the projection of the join *)

  Definition is_star (o : out_field Val) : bool := match o with of_star => true | _ => false end.

  (** The shape of the template of a label only depends on its tuple. *)
  Lemma shape_ltemplate l : shape (ltemplate l) = map is_star (ltuple l).
  Proof. induction l as [|[] l IH]; [done | ..];
    unfold shape, PAL_Alt_LTS.ltemplate, PAL_Alt_LTS.ltuple in *; simpl; by rewrite IH. Qed.

  (** The same label with its actual fields made formal. *)
  Definition formalize (l : label) : label :=
    map (λ f, match f with lf_val _ v => lf_formal Val v | f => f end) l.

  Lemma ltuple_formalize l : ltuple (formalize l) = ltuple l.
  Proof. induction l as [|[] l IH]; [done | ..];
    unfold shape, formalize, PAL_Alt_LTS.ltemplate, PAL_Alt_LTS.ltuple in *; simpl; by rewrite IH. Qed.

  Lemma ltemplate_formalize l :
    ltemplate (formalize l) = map (λ b : bool, if b then tf_star Val else tf_formal Val) (shape (ltemplate l)).
  Proof. induction l as [|[] l IH]; [done | ..];
    unfold shape, formalize, PAL_Alt_LTS.ltemplate, PAL_Alt_LTS.ltuple in *; simpl; by rewrite IH. Qed.

  Lemma ρᴀʟᴛ_join μ μ' : ρᴀʟᴛ μ = ρᴀʟᴛ μ' → LA_equiv R_prog_a R_test_a μ μ'.
  Proof.
    destruct μ as [l|ot], μ' as [l'|ot']; cbn; intros e; try discriminate; injection e as e.
    - (* [l ≈ᴘʀᴏ formalize l ≈ᴛᴇꜱᴛ formalize l' ≈ᴘʀᴏ l'] *)
      assert (LA_equiv R_prog_a R_test_a (AIn _ l) (AIn _ (formalize l))) as h1.
      { apply (R_prog_LA_equiv R_prog_a R_test_a).
        unfold PAL_Alt_Delta.R_prog_a. cbn. by rewrite ltuple_formalize. }
      assert (LA_equiv R_prog_a R_test_a (AIn _ (formalize l)) (AIn _ (formalize l'))) as h2.
      { apply (R_test_LA_equiv R_prog_a R_test_a).
        unfold PAL_Alt_Phi.R_test_a. cbn. by rewrite !ltemplate_formalize, e. }
      assert (LA_equiv R_prog_a R_test_a (AIn _ (formalize l')) (AIn _ l')) as h3.
      { apply (R_prog_LA_equiv R_prog_a R_test_a).
        unfold PAL_Alt_Delta.R_prog_a. cbn. by rewrite ltuple_formalize. }
      unfold LA_equiv in *. eapply tc_transitive; [exact h1 | eapply tc_transitive; [exact h2 | exact h3]].
    - subst. by apply (R_test_LA_equiv R_prog_a R_test_a).
  Qed.

  #[global] Instance ρᴀʟᴛ_proj : LA_proj (LA_equiv R_prog_a R_test_a) ρᴀʟᴛ.
  Proof.
    apply (LA_equiv_proj R_prog_a R_test_a); [| | apply ρᴀʟᴛ_join].
    - intros μ μ' h. unfold ρᴀʟᴛ. unfold PAL_Alt_Phi.R_test_a in h. by rewrite h.
    - intros μ μ' h. unfold PAL_Alt_Delta.R_prog_a in h.
      destruct μ as [l|ot], μ' as [l'|ot']; cbn in *; try discriminate; injection h as h.
      + by rewrite !shape_ltemplate, h.
      + by subst.
  Qed.

  (** ** [𝝳ᴀʟᴛ] is the completion of [ρᴀʟᴛ] along [Φᴀᴘᴀʟ] *)

  #[global] Instance Φᴀᴘᴀʟ_proj : LA_proj R_test_a (Φᴀᴘᴀʟ Val).
  Proof. intros μ μ'. done. Qed.

  #[global] Instance Φᴀᴘᴀʟ_surj : LA_surj (Φᴀᴘᴀʟ Val).
  Proof.
    refine {| LA_repr e := match e with EvIn _ tp => AIn _ (label_witness Val tp) | EvOut _ ot => AOut _ ot end |}.
    intros [tp|ot]; cbn; [by rewrite ltemplate_label_witness | done].
  Defined.

  Lemma 𝝳ᴀʟᴛ_complete e : 𝝳ᴀʟᴛ e = LA_complete (Φᴀᴘᴀʟ Val) ρᴀʟᴛ e.
  Proof. by apply (LA_complete_unique (Φᴀᴘᴀʟ Val) ρᴀʟᴛ 𝝳ᴀʟᴛ). Qed.

  (** ** Condition (2) forces an injective abstraction of outputs *)

  Definition tuple1 (v : Val) : eot := [of_val v].

  (** [in(?x).𝟘] and [in(!v).𝟘] *)
  Definition p_formal : term := in( [? 0] ) • 𝟘.
  Definition p_val (v : Val) : term := in( [! ve_val v] ) • 𝟘.

  Lemma coR_p_formal v : AOut _ (tuple1 v) ∈ (coR p_formal : subset_of PALA_Act).
  Proof.
    exists (AIn _ [lf_formal Val v]). split_and!; [| done | intros []].
    apply PALA_refuses_spec2. eexists. by apply aar1.
  Qed.

  Lemma coR_p_val v : AOut _ (tuple1 v) ∈ (coR (p_val v) : subset_of PALA_Act).
  Proof.
    exists (AIn _ [lf_val Val v]). split_and!; [| done | intros []].
    apply PALA_refuses_spec2. eexists. by apply aar1.
  Qed.

  Lemma coR_p_val_only v μ : μ ∈ (coR (p_val v) : subset_of PALA_Act) → μ = AOut _ (tuple1 v).
  Proof.
    intros (μ2 & acc & hd & _). apply lts_refuses_spec1 in acc as (q & hq).
    unfold p_val in hq. cbn in hq. inversion hq; subst.
    match goal with hev : eval_in_tuple _ = Some _ |- _ => cbn in hev; injection hev as <- end.
    match goal with ht : template_of _ _ = _ |- _ =>
      destruct l as [|[w|w|] [|]]; cbn in ht; try discriminate; injection ht as -> end.
    destruct μ as [l'|ot]; cbn in hd; [contradiction |]. by subst.
  Qed.

  Theorem prog_spec_injective {B : Type} (κ : Event → B) :
    (∀ (p : term) (β β' : PALA_Act), κ (Φᴀᴘᴀʟ Val β) = κ (Φᴀᴘᴀʟ Val β') →
       Φᴀᴘᴀʟ Val β ∈ (⌈ Φᴀᴘᴀʟ Val ⌉ (coR p)) → Φᴀᴘᴀʟ Val β' ∈ (⌈ Φᴀᴘᴀʟ Val ⌉ (coR p))) →
    ∀ v w, κ (EvOut _ (tuple1 v)) = κ (EvOut _ (tuple1 w)) → v = w.
  Proof.
    intros h2 v w e.
    assert (Φᴀᴘᴀʟ Val (AOut _ (tuple1 w)) ∈ (⌈ Φᴀᴘᴀʟ Val ⌉ (coR (p_val v)))) as (x & hx & ex).
    { apply (h2 (p_val v) (AOut _ (tuple1 v))); [exact e |].
      exists (AOut _ (tuple1 v)). split; [apply coR_p_val | done]. }
    apply coR_p_val_only in hx. subst x. cbn in ex. injection ex. congruence.
  Qed.

  (** All the [EvOut ⟨v⟩] lie in [Φ(coR (in(?x).𝟘))]. *)
  Lemma Φ_coR_p_formal v : EvOut _ (tuple1 v) ∈ (⌈ Φᴀᴘᴀʟ Val ⌉ (coR p_formal)).
  Proof. exists (AOut _ (tuple1 v)). split; [apply coR_p_formal | done]. Qed.

  (** [𝝳ᴀʟᴛ] does not satisfy condition (2): [out⟨v⟩.𝟘] accepts [AIn [v]] but not [AIn [w]]. *)
  Lemma 𝝳ᴀʟᴛ_not_prog_spec v w : v ≠ w →
    let p := out( eot_to_tuple (tuple1 v) ) • 𝟘 in
    let β := AIn _ [lf_val Val v] in
    let β' := AIn _ [lf_val Val w] in
    𝝳ᴀʟᴛ (Φᴀᴘᴀʟ Val β) = 𝝳ᴀʟᴛ (Φᴀᴘᴀʟ Val β')
    ∧ Φᴀᴘᴀʟ Val β ∈ (⌈ Φᴀᴘᴀʟ Val ⌉ (coR p))
    ∧ Φᴀᴘᴀʟ Val β' ∉ (⌈ Φᴀᴘᴀʟ Val ⌉ (coR p)).
  Proof.
    intros hvw p β β'. split_and!.
    - done.
    - exists β. split; [| done].
      exists (AOut _ (tuple1 v)). split_and!; [| done | intros []].
      apply PALA_refuses_spec2. eexists. by apply aar3.
    - intros (x & (μ2 & acc & hd & _) & ex).
      apply lts_refuses_spec1 in acc as (q & hq). unfold p in hq. cbn in hq. inversion hq; subst.
      destruct x as [l|o]; cbn in hd, ex; [| discriminate].
      injection ex as ex.
      destruct l as [|[u|u|] [|]]; cbn in ex, hd; try discriminate.
      injection ex as <-. match goal with hev : eval_out_tuple _ = Some _ |- _ => cbn in hev; injection hev as hev end.
      congruence.
  Qed.
End PAL_Alt_Abs.
