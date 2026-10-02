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
From TestingTheory Require Import ActTau gLts SyncActions Bisimulation Subset_Act DefinitionAS
  PAL_Syntax PAL_Alt_LTS PAL_Alt_Congruence PAL_Alt_Phi
  Applicative_process_algebra PAL_Alt_Tau PAL_Label_Dilemma PAL_Label_Dilemma_Sync PAL_Alt_Dilemma
  Testing_Predicate CompletenessASco.

(* * PAL with outputs labelled by their receiver

   The alternative LTS ([PAL_Alt_LTS.v]) labels an input with its template
   and the received tuple, [AIn l], but an output only with its tuple,
   [AOut ot].  Here an output is labelled like the input that receives it:
   [ROut l] is the emission of [ltuple l] to a receiver of template
   [ltemplate l].  So an emission of [ot] carries one label per template
   matching [ot] (finitely many, [labels_of ot]), and the dual is unique:
   [RIn l] meets [ROut l] and nothing else.

   The LTS is a relabelling of [PAL_Alt_LTS]: [p ⟶[ROut l] q] iff
   [p ⟶[AOut (ltuple l)] q], with the same inputs and the same τ.  Hence
   - [PALR_tau_iff]: its τ are those of the alternative LTS, hence of PAL
     ([PAL_Alt_Tau.tau_iff]);
   - [PALR_sync_iff]: its synchronisations along [dual] are those of the
     alternative LTS, hence of PAL ([PAL_Alt_Dilemma.PALA_sync_iff]).

   Abstraction, with [Φ] the identity and [𝝳ᴿ] forgetting the values received
   at formal positions:
   - [𝝳ᴿ (ROut l) = PRecv (ltemplate l)]: a co-action [ROut l] of [p] stands
     for a reception of [p] with template [ltemplate l];
   - [𝝳ᴿ (RIn l) = PEmit l]: a co-action [RIn l] stands for an emission of
     [p] towards a receiver of label [l].
   [AbsPALR] proves the conditions (1) and (2) of [AbsAction], and
   [FinitaryPALR] the finiteness of [𝝳ᴿ (coR p)]: it is made of the templates
   of the receptions of [p] and the labels of its emissions. *)

Section PAL_Rcv.
  Context (Val : Type) `{Countable Val}.

  Notation term := (term Val).
  Notation eot := (eot Val).
  Notation template := (template Val).
  Notation label := (label Val).
  Notation ltemplate := (ltemplate Val).
  Notation ltuple := (ltuple Val).
  Notation PALA_Act := (PALA_Act Val).
  Notation step := (lts_step_a Val).

  (** ** Labels *)

  Inductive PALR_Act := RIn (l : label) | ROut (l : label).

  #[global] Instance PALR_Act_eqdec : EqDecision PALR_Act.
  Proof. solve_decision. Defined.

  #[global] Instance PALR_Act_countable : Countable PALR_Act.
  Proof.
    refine (inj_countable'
      (λ a, match a with RIn l => inl l | ROut l => inr l end)
      (λ s, match s with inl l => RIn l | inr l => ROut l end)
      _).
    by intros [].
  Defined.

  (** An input meets the output with the same label. *)
  Definition PALR_dual (μ η : PALR_Act) : Prop :=
    match μ, η with
    | RIn l, ROut l' | ROut l, RIn l' => l = l'
    | _, _ => False
    end.

  #[global] Instance PALR_dual_dec μ η : Decision (PALR_dual μ η).
  Proof. destruct μ, η; simpl; apply _. Defined.

  #[global] Instance PALR_dual_sym : Symmetric PALR_dual.
  Proof. by intros [] []. Qed.

  Definition PALR_non_blocking (_ : PALR_Act) : Prop := False.

  #[global] Instance PALR_non_blocking_dec a : Decision (PALR_non_blocking a).
  Proof. right. intros []. Defined.

  Definition PALR_exists_dual (μ : PALR_Act) : {η | PALR_dual μ η} :=
    match μ with
    | RIn l => exist _ (ROut l) eq_refl
    | ROut l => exist _ (RIn l) eq_refl
    end.

  #[global] Instance PALR_ExtAction : ExtAction PALR_Act := {|
    eqdec := PALR_Act_eqdec;
    countable := PALR_Act_countable;
    non_blocking := PALR_non_blocking;
    non_blocking_dec := PALR_non_blocking_dec;
    dual := PALR_dual;
    dual_dec := PALR_dual_dec;
    dual_blocks := λ _ _ nb _, match nb with end;
    duo_sym := PALR_dual_sym;
    exists_dual := PALR_exists_dual;
  |}.

  (** ** The LTS, by relabelling *)

  Definition to_a (α : Act PALR_Act) : Act PALA_Act :=
    match α with
    | τ => τ
    | ActExt (RIn l) => ActExt (AIn Val l)
    | ActExt (ROut l) => ActExt (AOut Val (ltuple l))
    end.

  Definition lts_step_r (p : term) (α : Act PALR_Act) (q : term) : Prop := step p (to_a α) q.

  #[global] Instance PALR_step_dec p α q : Decision (lts_step_r p α q).
  Proof. unfold lts_step_r. apply _. Defined.

  Definition PALR_refuses (p : term) (α : Act PALR_Act) : Prop := PALA_refuses Val p (to_a α).

  #[global] Instance PALR_refuses_dec p α : Decision (PALR_refuses p α).
  Proof. unfold PALR_refuses. apply _. Defined.

  Definition PALR_refuses_spec1 p α : ¬ PALR_refuses p α → {q | lts_step_r p α q} :=
    PALA_refuses_spec1 Val p (to_a α).

  Definition PALR_refuses_spec2 p α : {q | lts_step_r p α q} → ¬ PALR_refuses p α :=
    PALA_refuses_spec2 Val p (to_a α).

  #[global] Instance PALR_gLts : gLts term PALR_ExtAction :=
    @MkgLts term PALR_Act PALR_ExtAction lts_step_r term_eqdec PALR_step_dec
      PALR_refuses PALR_refuses_dec PALR_refuses_spec1 PALR_refuses_spec2.

  (** The structural congruence of the alternative LTS is a bisimulation here too. *)
  Lemma PALR_cgr_spec p q (α : Act PALR_Act) :
    (∃ r, cgr Val p r ∧ lts_step_r r α q) → (∃ r, lts_step_r p α r ∧ cgr Val r q).
  Proof. apply (PALA_cgr_spec Val p q (to_a α)). Qed.

  #[global] Instance PALR_gLtsEq : gLtsEq term PALR_ExtAction := {|
    gLtsEq_gLts := PALR_gLts;
    eq_rel := cgr Val;
    eq_rel_eq := cgr_equivalence Val;
    eq_spec := PALR_cgr_spec;
  |}.

  (** ** Same τ, same synchronisations *)

  Lemma PALR_tau_iff p q : lts_step_r p τ q ↔ step p τ q.
  Proof. done. Qed.

  Lemma PALR_sync_iff (p t p' t' : term) :
    (∃ μ1 μ2 : PALR_Act, PALR_dual μ1 μ2 ∧ lts_step_r p (ActExt μ1) p' ∧ lts_step_r t (ActExt μ2) t')
      ↔ (∃ μ1 μ2 : PALA_Act, PALA_dual Val μ1 μ2 ∧ step p (ActExt μ1) p' ∧ step t (ActExt μ2) t').
  Proof.
    split.
    - intros ([l1 | l1] & [l2 | l2] & hd & h1 & h2); simpl in hd; try done; subst.
      + exists (AIn Val l2), (AOut Val (ltuple l2)). by split_and!.
      + exists (AOut Val (ltuple l2)), (AIn Val l2). by split_and!.
    - intros ([l1 | ot1] & [l2 | ot2] & hd & h1 & h2); simpl in hd; try done; subst.
      + exists (RIn l1), (ROut l1). by split_and!.
      + exists (ROut l2), (RIn l2). by split_and!.
  Qed.

  (** ** The abstraction *)

  (** A reception, seen through its template; an emission, through the label
      of its receiver. *)
  Inductive PreR := PRecv (tp : template) | PEmit (l : label).

  #[global] Instance PreR_eqdec : EqDecision PreR.
  Proof. solve_decision. Defined.

  #[global] Instance PreR_countable : Countable PreR.
  Proof.
    refine (inj_countable'
      (λ e, match e with PRecv tp => inl tp | PEmit l => inr l end)
      (λ s, match s with inl tp => PRecv tp | inr l => PEmit l end)
      _).
    by intros [].
  Defined.

  Definition Φᴿ (μ : PALR_Act) : PALR_Act := μ.

  Definition 𝝳ᴿ (μ : PALR_Act) : PreR :=
    match μ with
    | ROut l => PRecv (ltemplate l)
    | RIn l => PEmit l
    end.

  #[local] Hint Mode ExtAction ! : typeclass_instances.

  (** What [coR] is made of. *)
  Lemma coR_PALR_iff (p : term) (η : PALR_Act) :
    η ∈ (coR p : subset_of PALR_Act) ↔
      match η with
      | ROut l => ∃ q, step p (ActExt (AIn Val l)) q
      | RIn l => ∃ q, step p (ActExt (AOut Val (ltuple l))) q
      end.
  Proof.
    split.
    - intros (μ2 & acc & hd & _). apply lts_refuses_spec1 in acc as (q & hq).
      destruct η as [l | l], μ2 as [l2 | l2]; cbn in hd; try done; subst; by exists q.
    - destruct η as [l | l]; intros (q & hq).
      + exists (ROut l). split_and!; [| done | intros []].
        apply lts_refuses_spec2. by exists q.
      + exists (RIn l). split_and!; [| done | intros []].
        apply lts_refuses_spec2. by exists q.
  Qed.

  #[global] Program Instance AbsPALR :
    @AbsAction term term PALR_Act PreR PALR_Act PALR_ExtAction Φᴿ 𝝳ᴿ
      PALR_Act PALR_ExtAction PALR_gLts PALR_gLtsEq SyncAction_of_dual.
  Next Obligation.
    (* (1): [Φᴿ] is the identity *)
    intros t β β' _ _ e acc. unfold Φᴿ in e. by subst.
  Qed.
  Next Obligation.
    (* (2): a reception only depends on its template *)
    intros p β β' _ _ e (x & hx & ex). unfold Φᴿ in *. subst x.
    exists β'. split; [| done].
    apply coR_PALR_iff in hx. apply coR_PALR_iff.
    destruct β as [l | l], β' as [l' | l']; cbn in e; try discriminate; injection e as e.
    - by subst.
    - destruct hx as (q & hq). by eapply in_retarget.
  Qed.

  (** ** Finiteness *)

  Context `{!Inhabited Val}.

  Definition coR_abs_PALR (p : term) : gset PreR :=
    list_to_set (map PRecv (collect_in_a Val p)
                 ++ map PEmit (concat (map (labels_of Val) (collect_out_a Val p)))).

  Lemma coR_abs_PALR_spec (p : term) (x : PreR) :
    x ∈ coR_abs_PALR p ↔ x ∈ ⌈ 𝝳ᴿ ∘ Φᴿ ⌉ (coR p).
  Proof.
    unfold coR_abs_PALR. rewrite elem_of_list_to_set, list_elem_of_In, in_app_iff, !in_map_iff.
    split.
    - intros [(tp & <- & hin) | (l & <- & hin)].
      + rewrite <- (ltemplate_label_witness Val tp) in hin.
        destruct (collect_in_a_step Val p _ hin) as (q & hq).
        exists (ROut (label_witness Val tp)). split.
        * apply coR_PALR_iff. by exists q.
        * cbn. by rewrite ltemplate_label_witness.
      + apply in_concat in hin as (ls & hls & hl). apply in_map_iff in hls as (ot & <- & hot).
        apply labels_of_spec in hl.
        destruct (collect_out_witnesses_a Val p ot hot) as [q hq].
        exists (RIn l). split; [| done].
        apply coR_PALR_iff. exists q. by rewrite hl.
    - intros (η & hη & ->). apply coR_PALR_iff in hη.
      destruct η as [l | l]; destruct hη as (q & hq); cbn.
      + right. exists l. split; [done |].
        apply in_concat. exists (labels_of Val (ltuple l)). split.
        * apply in_map_iff. exists (ltuple l). split; [done |].
          by eapply out_step_in_collect_out_a.
        * by apply labels_of_spec.
      + left. exists (ltemplate l). split; [done |]. by eapply in_step_in_collect_in_a.
  Qed.

  #[global] Program Instance FinitaryPALR :
    @FinitaryAbsAction term term PALR_Act PreR PALR_Act PALR_ExtAction Φᴿ 𝝳ᴿ
      PALR_Act PALR_ExtAction PALR_gLts PALR_gLtsEq SyncAction_of_dual _ _ :=
    {| coR_abs := coR_abs_PALR |}.
  Next Obligation. intros p x hx. by apply coR_abs_PALR_spec. Qed.
  Next Obligation. intros x p hx. by apply coR_abs_PALR_spec. Qed.
End PAL_Rcv.

(** ** Against PAL itself *)

(** The τ of [PAL_Rcv] are those of PAL. *)
Lemma PALR_tau_iff_PAL {Val : Type} `{Countable Val} (p q : term Val) :
  lts_step_r Val p τ q ↔ Applicative_process_algebra.lts_step Val p τ q.
Proof. apply (tau_iff Val). Qed.

(** A process and a test communicate along [dual] exactly when they
    synchronise in PAL. *)
Lemma PALR_sync_iff_PAL {Val : Type} `{Countable Val} (p t p' t' : term Val) :
  (∃ μ1 μ2 : PALR_Act Val, PALR_dual Val μ1 μ2
     ∧ lts_step_r Val p (ActExt μ1) p' ∧ lts_step_r Val t (ActExt μ2) t')
    ↔ PAL_sync p t p' t'.
Proof. rewrite PALR_sync_iff. apply PALA_sync_iff. Qed.

(** ** The price: no test generator satisfies [test_spec]

    [FinitaryPALR] meets the abstraction side, so by [no_labelling_sync] the
    test side must fail: an emission now carries several labels towards the
    same state, against condition (6). *)
Corollary PALR_no_test_spec {Val : Type} `{Countable Val} `{!Inhabited Val}
  (inj : nat → Val) `{!Inj eq eq inj}
  (outcome : term Val → Prop) {TP : Testing_Predicate outcome (PALR_gLtsEq Val)}
  (gen : list (PALR_Act Val) → term Val) :
  @test_spec (term Val) (PALR_Act Val) (PALR_ExtAction Val) (PALR_gLtsEq Val) outcome TP gen → False.
Proof.
  intros TS.
  apply (no_labelling_sync (Val := Val) (TS := TS) (Fin := FinitaryPALR Val)
           inj (Φᴿ Val) (𝝳ᴿ Val) outcome gen).
  - intros η [].
  - exact PALR_sync_iff_PAL.
Qed.
