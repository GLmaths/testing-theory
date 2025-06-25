(*
   Copyright (c) 2024 Nomadic Labs
   Copyright (c) 2024 Paul Laforgue <paul.laforgue@nomadic-labs.com>
   Copyright (c) 2024 Léo Stefanesco <leo.stefanesco@mpi-sws.org>

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

Require Import Coq.Unicode.Utf8.
Require Import Coq.Wellfounded.Inverse_Image.
Require Import Coq.Program.Equality.
From stdpp Require Import base countable finite gmap list finite base decidable finite gmap.
From Must Require Import TransitionSystems Must Soundness Equivalence Completeness.

CoInductive copre `{@FiniteLts A L HL LtsP, @FiniteLts B L HL LtsQ} (ps : gset A) (q : B) : Prop := {
    c_tau q' : q ⟶ q' -> copre ps q'
  ; c_now : (forall p, p ∈ ps -> p ⤓) -> q ↛ ->
            exists p p', p ∈ ps /\ p ⟹ p' /\ p' ↛ /\ lts_outputs p' ⊆ lts_outputs q
  ; c_step : forall μ q' ps', (forall p, p ∈ ps -> p ⇓ [μ]) ->
                         q ⟶[μ] q' -> wt_set_from_pset_spec ps [μ] ps' -> copre ps' q'
  ; c_cnv : (forall p, p ∈ ps -> p ⤓) -> q ⤓
  }.

Notation "p ⩽ q" := (copre p q) (at level 70).

Lemma copre_if_prex
  `{@FiniteLts A L HL LtsP, @FiniteLts B L HL LtsQ}
  (ps : gset A) (q : B) : ps ≼ₓ q -> ps ⩽ q.
Proof.
  revert ps q.
  cofix H2.
  intros ps q (hsub1 & hsub2).
  constructor.
  - intros q' l. eapply H2, bhvx_preserved_by_tau; eauto.
  - intros hterm hst.
    edestruct (hsub2 [] q) as (p' & hw & hstp' & hsub0).
    eapply wt_nil. eassumption. intros p' mem. constructor.
    eapply hterm. eauto. eauto.
  - intros μ q' ps' hcnv hw wtspec.
    eapply H2.
    eapply bhvx_preserved_by_mu; eauto.
    intros p0 mem0.
    edestruct (hcnv p0 mem0); eauto.
  - intros. edestruct (hsub1 []); eauto.
    intros. constructor. eauto.
Qed.

Lemma co_preserved_by_wt_nil
  `{@FiniteLts A L HL LtsP, @FiniteLts B L HL LtsQ}
  (ps : gset A) (q q' : B) : q ⟹ q' -> ps ⩽ q -> ps ⩽ q'.
Proof. intro hw. dependent induction hw; eauto. destruct 1. eauto. Qed.

Lemma prex1_if_copre
  `{@FiniteLts A L HL LtsP, @FiniteLts B L HL LtsQ}
  (ps : gset A) (q : B) : ps ⩽ q -> ps ≼ₓ1 q.
Proof.
  intros.
  intros s hcnv.
  revert ps q H1 hcnv.
  dependent induction s; intros ps q H1 hcnv; destruct H1.
  + constructor. eapply c_cnv0.
    intros. now destruct (hcnv p H1).
  +  assert (q ⤓) by (now eapply c_cnv0; intros; destruct (hcnv p H1)).
     assert (hcnv0 : ∀ p : A, p ∈ ps → p ⇓ [a]).
     intros p' mem'%hcnv.
     constructor. now destruct mem'.
     intros p1 hw1. inversion mem'; subst. eapply H6 in hw1. inversion hw1; subst.
     now constructor.
     now constructor.
     eapply cnv_act; eauto.
     intros q' hw.
     eapply wt_decomp_one in hw as (q0' & q1' & q1 & hlt & hw0').
     assert (hpre : ps ⩽ q). constructor; eauto.
     eapply IHs.
     ++ eapply co_preserved_by_wt_nil. eassumption.
        eapply (co_preserved_by_wt_nil ps q q0') in hpre. destruct hpre.
        eapply (c_step1 a q1'); eauto.
        eapply (wt_s_set_from_pset_ispec ps [a] hcnv0); eauto. eassumption.
     ++ intros p mem.
        edestruct (wt_s_set_from_pset_ispec ps [a] hcnv0).
        eapply H2 in mem as (p0 & hmem0%hcnv & hw0).
        inversion hmem0; subst. eauto.
Qed.

Lemma prex2_if_copre
  `{@FiniteLts A L HL LtsP, @FiniteLts B L HL LtsQ}
  (ps : gset A) (q : B) : ps ⩽ q -> ps ≼ₓ2 q.
Proof.
  revert ps q.
  intros ps q hsub s.
  revert ps q hsub.
  dependent induction s; intros ps q hsub.
  + intros q' hw hstq' hcnv.
    dependent induction hw; try rename p into q.
    ++ destruct hsub.
       edestruct c_now0.
       intros p0 mem0. edestruct (hcnv p0 mem0); eauto. eassumption.
       firstorder.
    ++ eapply IHhw; eauto. destruct hsub. eapply c_tau0. eassumption.
  + intros. rename a into μ.
    replace (μ :: s) with ([μ] ++ s) in H1 by eauto.
    eapply wt_split in H1 as (q0 & hw0 & hw1).
    eapply wt_decomp_one in hw0 as (q0' & q1' & q1 & hlt & hw0').
    assert (ps ⩽ q0') by (eapply co_preserved_by_wt_nil; eauto).
    assert (hcnv' : ∀ p : A, p ∈ ps → p ⇓ [μ]).
    intros. constructor. edestruct (H3 p H4); eauto.
    intros. constructor. eapply cnv_terminate.
    eapply cnv_preserved_by_wt_act; eauto.
    set (ps' := wt_s_set_from_pset ps [μ] hcnv').
    assert (ps ⩽ q0') by (eapply co_preserved_by_wt_nil; eauto).
    assert (ps' ⩽ q1'). destruct H1.
    eapply c_step0. eassumption. eassumption.
    eapply wt_s_set_from_pset_ispec.
    assert (ps' ⩽ q0) by (eapply co_preserved_by_wt_nil; eauto).
    edestruct (IHs ps' q0 H6 _ hw1 H2) as (r & memr & p' & hwr & hst & hsub').
    intros.
    edestruct (wt_s_set_from_pset_ispec ps [μ] hcnv').
    eapply H8 in H7 as (p0  & hmem0 & hw0).
    eapply cnv_preserved_by_wt_act; eauto.
    edestruct (wt_s_set_from_pset_ispec ps [μ] hcnv').
    eapply H7 in memr as (p0  & hmem0 & hw0).
    exists p0. split. eassumption. exists p'. split.
    eapply wt_push_left; eassumption.
    split; eauto.
Qed.


Theorem eqx `{@FiniteLts A L HL LtsP, @FiniteLts B L HL LtsQ} (X : gset A) (q : B) :
  X ≼ₓ q <-> X ⩽ q.
Proof.
  split.
  - eapply copre_if_prex.
  - intros hco. split. now eapply prex1_if_copre. now eapply prex2_if_copre.
Qed.

Section eq_contextual.

  Context `{LL : Label L}.
  Context `{LtsA : !Lts A L, !FiniteLts A L}.
  Context `{LtsB : !Lts B L, !FiniteLts B L}.
  Context `{LtsE : !Lts E L, !FiniteLts E L}.

  Context `{@LtsObaFB A L LL LtsA LtsEqA LtsObaA}.
  Context `{@LtsObaFB B L LL LtsB LtsEqB LtsObaB}.
  Context `{@LtsObaFB E L LL LtsE LtsEqE LtsObaE}.

  Context `{good : E -> Prop}.
  Context `{good_dec : forall e, Decision (good e)}.
  Context `{!Good E L good}.

  (* ************************************************** *)

  Context `{igen_conv : @gen_spec_conv  _ _ _ _ _ good Good0 gen_conv}.
  Context `{igen_acc : @gen_spec_acc _ _ _ _ _ good Good0 gen_acc}.

  Theorem eq_ctx (p : A) (q : B) :
    @pre_extensional A E _ _ _ good _ p q <-> {[ p ▷ (∅ : mb L) ]} ⩽ q ▷ (∅ : mb L).
  Proof.
    rewrite <- eqx, <- alt_set_singleton_iff.
    now rewrite equivalence_bhv_acc_ctx.
  Qed.
End eq_contextual.


Lemma coin_refl `{FiniteLts A L} {p : A} : {[ p ]} ⩽ p.
Proof. eapply eqx. eapply alt_set_singleton_iff. firstorder. Qed.

Lemma coin_union_l `{FiniteLts A L} : forall (X1 X2  : gset A) (q : A), X1 ⩽ q -> X1 ∪ X2 ⩽ q.
Proof.
  intros X1 X2 q Ho.
  eapply eqx. eapply eqx in Ho as (h1 & h2).
  split.
  - intros s hcnv.
    eapply h1. set_solver.
  - intros s p hw hst hcnv.
    destruct (h2 s p hw hst ltac:(set_solver)). set_solver.
Qed.

Lemma coin_union_r `{FiniteLts A L} : forall (X1 X2  : gset A) (q : A), X2   ⩽ q -> X1 ∪ X2 ⩽ q.
Proof.
  intros X1 X2 q Ho.
  eapply eqx. eapply eqx in Ho as (h1 & h2).
  split.
  - intros s hcnv.
    eapply h1. set_solver.
  - intros s p hw hst hcnv.
    destruct (h2 s p hw hst ltac:(set_solver)). set_solver.
Qed.

Lemma coin_elem_of `{FiniteLts A L} (p : A) X: p ∈ X -> X ⩽ p.
Proof.
intro Hin. setoid_rewrite (union_difference_singleton_L p X Hin).
apply coin_union_l, coin_refl.
Qed.

(* faster than set set_solver *)
Ltac set_tac :=
solve[apply elem_of_union_r; set_tac] ||
solve[apply elem_of_union_l; set_tac] ||
assumption ||
now apply elem_of_singleton_2.

(* TODO : should go with mb Lts construction *)
Lemma fw_wt `{FiniteLts A L} (t : A) q m:
  t ⟹ q -> (t ▷ m) ⟹ (q ▷ m).
Proof.
intro Ht. induction Ht.
- apply wt_nil.
- apply wt_tau with (q  ▷ m).
  + now constructor.
  + assumption.
- apply wt_act with (q ▷ m).
  + now constructor.
  + assumption.
Qed.

Lemma fw_wt_mb_com `{FiniteLts A L} (t : A) a q m:
  t ⟹{ActIn a} q -> (t ▷ {[+ a +]} ⊎ m) ⟹ (q ▷ m).
Proof.
intro Ht. dependent induction Ht.
- apply wt_tau with (q ▷ {[+ a +]} ⊎ m).
  + now constructor.
  + apply IHHt; trivial.
- apply wt_tau with (q  ▷ m).
  + now constructor.
  + now apply fw_wt.
Qed.

Lemma fw_wt_left `{FiniteLts A L} (t : A) q0 (M : mb L) μ :
  t ⟹{μ} q0 -> (t ▷ M) ⟹{μ} (q0 ▷ M).
Proof.
intros Ht.
dependent induction Ht.
- apply wt_tau with (q ▷ M).
  + now constructor.
  + apply IHHt; trivial.
- apply wt_act with (q ▷ M).
  + now constructor.
  + now apply fw_wt.
Qed.

Lemma copre_fw_inv_l `{FiniteLts A L} (p t: A):
  (∀ μ p', p ⟶{μ} p' <-> (p' = t /\ μ = τ)) ->
  forall M (X : gset (A * mb L)) (q : A * mb L),  {[t ▷ M]} ∪ {[p ▷ M]} ∪ X ⩽ q -> {[p ▷ M]} ∪ X ⩽ q.
Proof.
intros Hinv. cofix hco. intros M X q Hq.
assert(Hpt : (p ▷ M) ⟶ (t ▷ M)) by (apply lts_fw_p, Hinv; tauto).
constructor.
- intros q' Hq'. apply hco, Hq, Hq'.
- intros Ht Hs. destruct Hq as [ _ Hq _ _].
  destruct Hq as (p1 & p2 & Hin & Hcnv & Hs' & Hout).
  + intros p0 Hin. repeat rewrite elem_of_union in Hin.
    destruct Hin as [[Heqt | Heqp] | Hin].
    * apply elem_of_singleton_1 in Heqt. subst.
      apply terminate_preserved_by_lts_tau with (p ▷ M).
      -- apply Ht. set_tac.
      -- assumption.
    * apply elem_of_singleton_1 in Heqp. subst.
      apply Ht. set_tac.
    * apply Ht. set_tac.
  + trivial.
  + repeat rewrite elem_of_union in Hin.
    destruct Hin as [[Heqt | Heqp] | Hin].
    * apply elem_of_singleton_1 in Heqt. subst.
      exists (p ▷ M). exists p2. repeat split; trivial.
      -- set_tac.
      -- apply wt_tau with (t ▷ M); assumption.
      -- apply Hs'.
      -- apply Hs'.
    * apply elem_of_singleton_1 in Heqp. subst.
      exists (p ▷ M). exists p2. repeat split; trivial.
      -- set_tac.
      -- apply Hs'.
      -- apply Hs'.
    * exists p1. exists p2; intuition.
      apply elem_of_union_r. set_tac.
- intros μ q' ps' Hμ1 Hμ2 Hwt. eapply Hq; [| eassumption |].
  + intros p0 Hin. repeat rewrite elem_of_union in Hin.
    destruct Hin as [[Heqt | Heqp] | Hin].
    * apply elem_of_singleton_1 in Heqt. subst.
      apply cnv_preserved_by_lts_tau with (p ▷ M).
      -- apply Hμ1. set_tac.
      -- assumption.
    * apply elem_of_singleton_1 in Heqp. subst. apply Hμ1. set_tac.
    * apply Hμ1. set_tac.
  + destruct Hwt as [Hwt1 Hwt2].
    split.
    * intros p' Hp'. destruct (Hwt1 p' Hp') as [p0 [Hin Hp0]].
      repeat rewrite elem_of_union in Hin. destruct Hin as [Heqt | Hin].
      -- apply elem_of_singleton_1 in Heqt. subst.
         exists (p ▷ M). split; [set_tac|assumption].
      -- exists p0. split; [set_tac|assumption].
    * intros p' p'' Hin Hμ.
      repeat rewrite elem_of_union in Hin.
      destruct Hin as [[Heqt | Heqp] | Hin].
      -- apply elem_of_singleton_1 in Heqt. subst.
         eapply Hwt2 with (p ▷ M); [set_tac|].
         apply wt_tau with (t ▷ M); assumption.
      -- apply elem_of_singleton_1 in Heqp. subst.
         eapply Hwt2 with (p ▷ M); [set_tac|assumption].
      -- eapply Hwt2 with p'; [set_tac|]. apply Hμ.
- intros Ht. apply Hq. intros p0 Hin.
  repeat rewrite elem_of_union in Hin. destruct Hin as [[Heqt | Heqp] | Hin].
  + apply elem_of_singleton_1 in Heqt. subst.
    apply terminate_preserved_by_lts_tau with (p ▷ M).
    * apply Ht. set_tac.
    * now apply Hpt.
  + apply elem_of_singleton_1 in Heqp. subst.
    apply Ht. set_tac.
  + apply Ht. set_tac.
Qed.

Lemma copre_inv_l `{FiniteLts A L} (p : A) X t q : (p ⟶ t) -> (forall μ p', p ⟹{μ} p' <-> t ⟹{μ} p') ->
  {[t]} ∪ X ⩽ q -> {[p]} ∪ X ⩽ q.
Proof.
intros Hpt Hinv. revert q. cofix hco. intros q Hq.
constructor.
- intros q' Hq'. apply hco, Hq, Hq'.
- intros Ht Hs. destruct Hq as [ _ Hq _ _].
  destruct Hq as (p1 & p2 & Hin & Hcnv & Hs' & Hout).
  + intros p0 Hin. apply elem_of_union in Hin. destruct Hin as [Heqt | Hin].
    * apply elem_of_singleton_1 in Heqt. subst.
      apply terminate_preserved_by_lts_tau with p.
      -- apply Ht. set_tac.
      -- now apply Hpt.
    * apply Ht. set_tac.
  + trivial.
  + apply elem_of_union in Hin. destruct Hin as [Heqt | Hin].
    * apply elem_of_singleton_1 in Heqt. subst.
      exists p. exists p2. repeat split; trivial.
      -- set_tac.
      -- apply wt_tau with t; [|assumption].
          now apply Hpt. (* p ⟶ t *)
    * exists p1. exists p2; intuition.
      apply elem_of_union_r. set_tac.
- intros μ q' ps' Hμ1 Hμ2 Hwt. eapply Hq; [| eassumption |].
  + intros p0 Hin. apply elem_of_union in Hin. destruct Hin as [Heqt | Hin].
    * apply elem_of_singleton_1 in Heqt. subst.
      apply cnv_preserved_by_lts_tau with p.
      -- apply Hμ1. set_tac.
      -- now apply Hpt. (* p ⟶ t *)
    * apply Hμ1. set_tac.
  + destruct Hwt as [Hwt1 Hwt2].
    split.
    * intros p' Hp'. destruct (Hwt1 p' Hp') as [p0 [Hin Hp0]].
      apply elem_of_union in Hin. destruct Hin as [Heqt | Hin].
      -- apply elem_of_singleton_1 in Heqt. subst.
         exists t. split; [set_tac|now apply Hinv].
      -- exists p0. split; [set_tac|assumption].
    * intros p' p'' Hin Hμ.
      apply elem_of_union in Hin. destruct Hin as [Heqt | Hin].
      -- apply elem_of_singleton_1 in Heqt. subst.
         eapply Hwt2 with p; [set_tac|]. apply Hinv, Hμ.
      -- eapply Hwt2 with p'; [set_tac|]. apply Hμ.
- intros Ht. apply Hq. intros p0 Hin.
  apply elem_of_union in Hin. destruct Hin as [Heqt | Hin].
  + apply elem_of_singleton_1 in Heqt. subst.
    apply terminate_preserved_by_lts_tau with p.
    * apply Ht. set_tac.
    * now apply Hpt.
  + apply Ht. set_tac.
Qed.

