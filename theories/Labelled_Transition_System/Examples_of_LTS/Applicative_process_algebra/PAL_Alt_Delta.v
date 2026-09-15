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

(* * The abstraction 𝝳 of the co-actions of PAL

   The counterpart of [Φ] ([PAL_Alt_Phi.v]) for [≈ᴘʀᴏ]: a label [μ] is seen
   through the processes accepting a dual of [μ], [co𝐏 μ].
   - [𝝳 (AIn l) = CoOut (ltuple l)]: the duals of [AIn l] are the outputs of
     [ltuple l], whatever the template;
   - [𝝳 (AOut ot) = CoIn ot]: the duals of [AOut ot] are the inputs receiving
     [ot], with any template.
   [𝝳_kernel]: [𝝳 μ = 𝝳 μ'] iff [co𝐏 μ ⊆ co𝐏 μ']. So the kernel of [𝝳] is the
   largest [≈ᴘʀᴏ], and [𝝳] is its canonical projection ([gLtsLAprog_PALA]).
   Unlike [Φ], [𝝳] forgets the template of an input: the co-actions of
   [in(?x).𝟘] are [AOut ⟨v⟩] for every [v], with pairwise distinct images. *)

Section PAL_Alt_Delta.
  Context (Val : Type) `{Countable Val}.

  Notation term := (term Val).
  Notation eot := (eot Val).
  Notation eit := (eit Val).
  Notation label := (label Val).
  Notation ltemplate := (ltemplate Val).
  Notation ltuple := (ltuple Val).
  Notation PALA_Act := (PALA_Act Val).
  Notation step := (lts_step_a Val).

  (** Infer the action type of [↛[μ]] from the LTS on terms. *)
  #[local] Hint Mode ExtAction ! : typeclass_instances.
  Open Scope pal_scope.


  (** ** Co-events and [𝝳] *)

  Inductive CoEvent := CoOut (ot : eot) | CoIn (ot : eot).

  #[global] Instance CoEvent_eqdec : EqDecision CoEvent.
  Proof. solve_decision. Defined.

  #[global] Instance CoEvent_countable : Countable CoEvent.
  Proof.
    refine (inj_countable'
      (λ e, match e with CoOut ot => inl ot | CoIn ot => inr ot end)
      (λ s, match s with inl ot => CoOut ot | inr ot => CoIn ot end)
      _).
    by intros [].
  Defined.

  Definition 𝝳ᴀᴘᴀʟ (μ : PALA_Act) : CoEvent :=
    match μ with
    | AIn _ l => CoOut (ltuple l)
    | AOut _ ot => CoIn ot
    end.

  Lemma co𝐏_iff (μ : PALA_Act) (p : term) :
    p ∈ (co𝐏 μ : subset_of term) ↔ ∃ μ', PALA_dual Val μ' μ ∧ ¬ p ↛[μ'].
  Proof. done. Qed.

  (** ** The kernel of [𝝳] is the largest [≈ᴘʀᴏ] *)

  (** Process side: labels with the same co-event have duals accepted by the same processes. *)
  Lemma 𝝳_prog_spec (p : term) μ μ' :
    𝝳ᴀᴘᴀʟ μ = 𝝳ᴀᴘᴀʟ μ' → p ∈ (co𝐏 μ : subset_of term) → p ∈ (co𝐏 μ' : subset_of term).
  Proof.
    rewrite !co𝐏_iff. intros e (μ'' & hd & acc). exists μ''. split; [| done].
    destruct μ as [l|ot], μ' as [l'|ot'], μ'' as [l''|ot'']; simpl in *; try done;
      injection e as e; congruence.
  Qed.

  Definition eot_to_eit (ot : eot) : eit :=
    map (λ o, match o with of_val v => if_val v | of_star => if_star end) ot.

  Lemma eval_in_eot_to_tuple (ot : eot) : eval_in_tuple (eot_to_tuple ot) = Some (eot_to_eit ot).
  Proof.
    induction ot as [|[|v] ot IH]; [done | |]; unfold eval_in_tuple in *; simpl; by rewrite IH.
  Qed.

  Lemma eval_out_eot_to_tuple (ot : eot) : eval_out_tuple (eot_to_tuple ot) = Some ot.
  Proof.
    induction ot as [|[|v] ot IH]; [done | |]; unfold eval_out_tuple in *; simpl; by rewrite IH.
  Qed.

  Lemma template_of_eot_to_eit (ot : eot) : template_of Val (eot_to_eit ot) = ltemplate (exact_label Val ot).
  Proof.
    induction ot as [|[|v] ot IH]; [done | ..];
      unfold template_of, PAL_Alt_LTS.ltemplate, exact_label, eot_to_eit in *; simpl; by rewrite IH.
  Qed.

  (** A template without formal field determines the received tuple. *)
  Lemma exact_template_ltuple (ot : eot) (l : label) :
    template_of Val (eot_to_eit ot) = ltemplate l → ltuple l = ot.
  Proof.
    revert l. induction ot as [|o ot IH]; intros [|f l] e; try discriminate; [done |].
    cbn in e. injection e as ef el. unfold PAL_Alt_LTS.ltuple in *. cbn. f_equal; [| by apply IH].
    destruct o, f; cbn in ef; try discriminate; by try injection ef as ->.
  Qed.

  (** A process accepting exactly the duals of the labels of a co-event. *)
  Definition coprobe (μ : PALA_Act) : term :=
    match μ with
    | AIn _ l => out( eot_to_tuple (ltuple l) ) • 𝟘
    | AOut _ ot => in( eot_to_tuple ot ) • 𝟘
    end.

  Lemma coprobe_accepts μ : coprobe μ ∈ (co𝐏 μ : subset_of term).
  Proof.
    apply co𝐏_iff. destruct μ as [l|ot]; simpl.
    - exists (AOut _ (ltuple l)). split; [done |].
      apply PALA_refuses_spec2. eexists. apply aar3, eval_out_eot_to_tuple.
    - exists (AIn _ (exact_label Val ot)). split; [apply ltuple_exact_label |].
      apply PALA_refuses_spec2. eexists.
      apply aar1; [apply eval_in_eot_to_tuple | apply template_of_eot_to_eit].
  Qed.

  Lemma coprobe_only μ μ' : coprobe μ ∈ (co𝐏 μ' : subset_of term) → 𝝳ᴀᴘᴀʟ μ' = 𝝳ᴀᴘᴀʟ μ.
  Proof.
    rewrite co𝐏_iff. intros (μ'' & hd & acc). apply lts_refuses_spec1 in acc as (q & hq).
    destruct μ as [l|ot]; unfold coprobe in hq; simpl in hq; inversion hq; subst.
    - match goal with hev : eval_out_tuple _ = Some _ |- _ =>
        rewrite eval_out_eot_to_tuple in hev; injection hev as <- end.
      destruct μ' as [l'|ot']; simpl in hd; [| done]. simpl. congruence.
    - match goal with hev : eval_in_tuple _ = Some _ |- _ =>
        rewrite eval_in_eot_to_tuple in hev; injection hev as <- end.
      match goal with ht : template_of _ _ = _ |- _ => apply exact_template_ltuple in ht end.
      destruct μ' as [l'|ot']; simpl in hd; [done |]. simpl. congruence.
  Qed.

  Lemma 𝝳_complete μ μ' :
    (∀ p : term, p ∈ (co𝐏 μ : subset_of term) → p ∈ (co𝐏 μ' : subset_of term)) → 𝝳ᴀᴘᴀʟ μ = 𝝳ᴀᴘᴀʟ μ'.
  Proof. intros h. symmetry. apply coprobe_only, h, coprobe_accepts. Qed.

  Theorem 𝝳_kernel μ μ' : 𝝳ᴀᴘᴀʟ μ = 𝝳ᴀᴘᴀʟ μ' ↔ (co𝐏 μ : subset_of term) ⊆ co𝐏 μ'.
  Proof.
    split.
    - intros e p. by apply 𝝳_prog_spec.
    - intros hsub. apply 𝝳_complete. intros p. apply hsub.
  Qed.

  (** ** [≈ᴘʀᴏ] *)

  Definition R_prog_a (μ μ' : PALA_Act) : Prop := 𝝳ᴀᴘᴀʟ μ = 𝝳ᴀᴘᴀʟ μ'.

  Lemma R_prog_a_equivalence : Equivalence R_prog_a.
  Proof. unfold R_prog_a. split; [done | by intros ?? | by intros ??? -> ->]. Qed.

  Lemma R_prog_a_dec : RelDecision R_prog_a.
  Proof. intros μ μ'. unfold R_prog_a. apply _. Defined.

  Lemma R_prog_a_spec μ μ' : R_prog_a μ μ' → (co𝐏 μ : subset_of term) ⊆ co𝐏 μ'.
  Proof. apply 𝝳_kernel. Qed.

  #[global] Instance gLtsLAprog_PALA : @gLtsLAprog term PALA_Act (PALA_ExtAction Val) (PALA_gLts Val) :=
    {| LA_prog := R_prog_a;
       LA_prog_eq := R_prog_a_equivalence;
       LA_prog_dec := R_prog_a_dec;
       LA_prog_spec := R_prog_a_spec |}.

  (** [R_prog_a] is the largest [≈ᴘʀᴏ]. *)
  Lemma R_prog_a_largest (R : PALA_Act → PALA_Act → Prop) :
    (∀ μ μ', R μ μ' → (co𝐏 μ : subset_of term) ⊆ co𝐏 μ') → ∀ μ μ', R μ μ' → R_prog_a μ μ'.
  Proof. intros hR μ μ' h. apply 𝝳_kernel, hR, h. Qed.
End PAL_Alt_Delta.
