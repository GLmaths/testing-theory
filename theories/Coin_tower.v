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
From Coinduction Require Import all.
From Must Require Import TransitionSystems Must Soundness Equivalence Completeness.


(* TODO: define me using the coinduction library *)

Lemma cnv_wk `{@FiniteLts A L HL LtsP} {p a s} : p ⇓ a :: s -> p ⇓ [ a ] .
Proof.
  intros pw; depelim pw; constructor.
  - assumption.
  - intros q qw%H1; constructor.
    eapply cnv_terminate, qw.
Qed.

Section copre.
  Context `{@FiniteLts A L HL LtsP, @FiniteLts B L HL LtsQ}.

  Definition REL := gset A -> B -> Prop .

  Record copre_ (FIX : REL) (ps : gset A) (q : B) : Prop := {
    c_tau_ q' : q ⟶ q' -> FIX ps q'
  ; c_now_ : (forall p, p ∈ ps -> p ⤓) -> q ↛ ->
            exists p p', p ∈ ps /\ p ⟹ p' /\ p' ↛ /\ lts_outputs p' ⊆ lts_outputs q
  ; c_step_ : forall μ q' ps', (forall p, p ∈ ps -> p ⇓ [μ]) ->
                         q ⟶[μ] q' -> wt_set_from_pset_spec ps [μ] ps' -> FIX ps' q'
  ; c_cnv_ : (forall p, p ∈ ps -> p ⤓) -> q ⤓
  }.
  #[global] Arguments c_tau_ {FIX ps q}.
  #[global] Arguments c_now_ {FIX ps q}.
  #[global] Arguments c_step_ {FIX ps q}.
  #[global] Arguments c_cnv_ {FIX ps q}.

  Program Definition copre_m : mon REL := {| body := copre_ |} .
  Next Obligation.
    intros F1 F2 HF ps q h; constructor.
    - intros; apply HF, h.(c_tau_); auto.
    - exact h.(c_now_).
    - intros; eapply HF, h.(c_step_); auto.
    - exact h.(c_cnv_).
  Qed.

  Definition copre := gfp copre_m .

  Notation "p ⩽ q" := (copre p q) (at level 70).

  Lemma c_tau {ps q q'} : ps ⩽ q -> q ⟶ q' -> ps ⩽ q' .
  Proof.
    intros h%(gfp_pfp copre_m); intros; now apply h.(c_tau_).
  Qed.

  Lemma c_now {ps q}
    : ps ⩽ q
      -> (forall p, p ∈ ps -> p ⤓)
      -> q ↛
      -> exists p p', p ∈ ps
                /\ p ⟹ p'
                /\ p' ↛
                /\ lts_outputs p' ⊆ lts_outputs q .
  Proof.
    intros h%(gfp_pfp copre_m); intros; now apply h.(c_now_).
  Qed.

  Lemma c_step {ps ps' q q' μ}
    : ps ⩽ q
      -> (forall p, p ∈ ps -> p ⇓ [μ])
      -> q ⟶[μ] q'
      -> wt_set_from_pset_spec ps [μ] ps'
      -> ps' ⩽ q' .
  Proof.
    intros h%(gfp_pfp copre_m); intros; now eapply h.(c_step_); eauto.
  Qed.

  Lemma c_cnv {ps q}
    : ps ⩽ q
      -> (forall p, p ∈ ps -> p ⤓)
      -> q ⤓ .
  Proof.
    intros h%(gfp_pfp copre_m); intros; now eapply h.(c_cnv_); eauto.
  Qed.

  Lemma copre_if_prex (ps : gset A) (q : B) : ps ≼ₓ q -> ps ⩽ q.
  Proof.
    revert ps q; unfold copre.
    coinduction RR CIH.
    intros ps q (hsub1 & hsub2).
    constructor.
    - intros q' l.
      eapply CIH, bhvx_preserved_by_tau; eauto.
    - intros hterm hst.
      destruct (hsub2 [] q) as (p' & hw & hstp' & hsub0); eauto.
      + eapply wt_nil.
      + intros p' mem; constructor; now apply hterm.
    - intros μ q' ps' hcnv hw wtspec.
      eapply CIH, bhvx_preserved_by_mu; eauto.
      intros p0 mem0.
      now destruct (hcnv p0 mem0).
    - intros; edestruct (hsub1 []); eauto.
      intros; constructor; eauto.
  Qed.

  Lemma co_preserved_by_wt_nil
    (ps : gset A) (q q' : B) : q ⟹ q' -> ps ⩽ q -> ps ⩽ q'.
  Proof.
    intro hw.
    dependent induction hw; eauto.
    intro h.
    apply IHhw; eauto.
    now apply (c_tau h).
  Qed.

  (* TODO: this may replace the above at some point *)
  Lemma co_preserved_by_wt_nil' {PRE : Chain copre_m}
    (ps : gset A) (q q' : B) : q ⟹ q' -> elem PRE ps q -> elem PRE ps q'.
  Proof.
  Admitted.

  Lemma prex1_if_copre (ps : gset A) (q : B) : ps ⩽ q -> ps ≼ₓ1 q.
  Proof.
    intros hpq s; revert ps q hpq.
    dependent induction s;
      intros ps q hpq hcnv.
    + constructor; eapply (c_cnv hpq).
      intros; now destruct (hcnv p H1).
    + assert (q ⤓) by (now eapply (c_cnv hpq); intros; destruct (hcnv p H1)).
      assert (hcnv0 : ∀ p : A, p ∈ ps → p ⇓ [a]) by (intros; now eapply cnv_wk, hcnv).
      eapply cnv_act; eauto.
      intros q' hw.
      eapply wt_decomp_one in hw as (q0' & q1' & q1 & hlt & hw0').
      eapply IHs.
      ++ eapply co_preserved_by_wt_nil; eauto.
         eapply (co_preserved_by_wt_nil ps q q0') in hpq; eauto.
         eapply (c_step hpq); eauto.
         eapply (wt_s_set_from_pset_ispec ps [a] hcnv0); eauto.
      ++ intros p mem.
         edestruct (wt_s_set_from_pset_ispec ps [a] hcnv0).
         eapply H2 in mem as (p0 & hmem0%hcnv & hw0).
         inversion hmem0; subst. eauto.
  Qed.

  Lemma prex2_if_copre (ps : gset A) (q : B) : ps ⩽ q -> ps ≼ₓ2 q.
  Proof.
    intros hsub s; revert ps q hsub; dependent induction s; intros ps q hsub.
    + intros q' hw hstq' hcnv.
      dependent induction hw.
      * edestruct (c_now hsub).
        - intros p0 mem0; edestruct (hcnv p0 mem0); eauto.
        - eassumption.
        - firstorder.
      * eapply IHhw; eauto.
        apply (c_tau hsub); eauto.
    + intros q' hqq' hq hcnv; rename a into μ.
      change (μ :: s) with ([μ] ++ s) in hqq'.
      eapply wt_split in hqq' as (q0 & hw0 & hw1).
      eapply wt_decomp_one in hw0 as (q0' & q1' & q1 & hlt & hw0').
      assert (ps ⩽ q0') as hpq' by (eapply co_preserved_by_wt_nil; eauto).
      assert (hcnv' : ∀ p : A, p ∈ ps → p ⇓ [μ]) by (intros; now eapply cnv_wk, hcnv).
      set (ps' := wt_s_set_from_pset ps [μ] hcnv').
      assert (ps' ⩽ q1') as hpq''. {
        eapply (c_step hpq'); eauto.
        eapply wt_s_set_from_pset_ispec.
      }
      assert (ps' ⩽ q0) as hp'q by (eapply co_preserved_by_wt_nil; eauto).
      edestruct (IHs ps' q0 hp'q _ hw1 hq) as (r & memr & p' & hwr & hst & hsub').
      * intros.
        edestruct (wt_s_set_from_pset_ispec ps [μ] hcnv').
        eapply H2 in H1 as (p0 & hmem0 & hw0).
        eapply cnv_preserved_by_wt_act; eauto.
      * edestruct (wt_s_set_from_pset_ispec ps [μ] hcnv').
        eapply H1 in memr as (p0  & hmem0 & hw0).
        exists p0; split; [ auto | ].
        exists p'; split; [ | split; eauto ].
        eapply wt_push_left; eauto.
  Qed.


  Theorem eqx (X : gset A) (q : B) :
    X ≼ₓ q <-> X ⩽ q.
  Proof.
    split; [ eapply copre_if_prex | ].
    intros hco; split; [ now eapply prex1_if_copre | now eapply prex2_if_copre ].
  Qed.
End copre.

Notation "p ⩽ q" := (copre p q) (at level 70).

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


Lemma coin_refl `{FiniteLts A L} {PRE : Chain copre_m} {p : A} : elem PRE {[ p ]} p.
Proof.
  apply (gfp_chain PRE).
  eapply eqx.
  eapply alt_set_singleton_iff.
  firstorder.
Qed.

Lemma wt_set_union `{FiniteLts A L} (X1 X2 : gset A) (s : trace L) {ps}
  (Hcnv : ∀ p : A, p ∈ X1 ∪ X2 → p ⇓ s)
  : wt_set_from_pset_spec (X1 ∪ X2) s ps
    -> exists ps1 ps2, wt_set_from_pset_spec X1 s ps1
                 /\ wt_set_from_pset_spec X2 s ps2
                 /\ (ps = ps1 ∪ ps2) .
Proof.
  intros [Hw1 Hw2].
  assert(Hcnv1 : ∀ p : A, p ∈ X1 → p ⇓ s) by (intros; apply Hcnv; set_solver).
  assert(Hcnv2 : ∀ p : A, p ∈ X2 → p ⇓ s) by (intros; apply Hcnv; set_solver).
  exists (wt_s_set_from_pset X1 s Hcnv1).
  exists (wt_s_set_from_pset X2 s Hcnv2).
  do 2 (split; [apply wt_s_set_from_pset_ispec|]).
  apply leibniz_equiv.
  apply set_equiv. intro x; split; intro Hin.
  - destruct (Hw1 _ Hin) as (p & Hinp%elem_of_union & Hp).
    destruct Hinp as [Hin1 | Hin2].
    + eapply elem_of_union_l, wt_s_set_from_pset_ispec; eauto.
    + eapply elem_of_union_r, wt_s_set_from_pset_ispec; eauto.
  - rewrite elem_of_union in Hin.
    destruct Hin as [Hin | Hin];
    apply wt_s_set_from_pset_ispec in Hin as (p & Hin & Hp);
    eapply Hw2; eauto; set_solver.
Qed.

Global Instance Proper_elem `{FiniteLts A L} {PRE : Chain copre_m} :
  Proper ((≡) ==> (=) ==> (iff)) (elem PRE).
Proof.
  intros ?? HX ?? <-.
  now rewrite (leibniz_equiv _ _ HX).
Qed.

Global Instance Proper_lts_outputs `{TransitionSystems.LtsOba A L}:
  Proper ((eq_rel) ==> (=)) lts_outputs.
Proof.
  intros μ μ' Heq. apply leibniz_equiv.
  intros x. do 2 rewrite <- lts_oba_mo_spec1. now erewrite lts_oba_mo_eq; eauto.
Qed.

Global Instance Proper_lts_stable `{TransitionSystems.LtsOba A L}:
  Proper ((eq_rel) ==> (=) ==> (impl)) lts_stable.
Proof.
  intros p p' Heq α α' ? Hs; subst α'.
  case (decide (lts_stable p' α)); trivial. intro Hf.
  apply lts_stable_spec1 in Hf as (q & Hq).
  destruct (eq_spec p q α) as (r & Hr & Heqr).
  - eexists; split; eauto.
  - contradict Hs. apply lts_stable_spec2. eexists; eauto.
Qed.

(* In the case of a Lts with equivalence relation, the right hand side can also
  be rewritten *)
Global Instance Proper_eq_rel `{FiniteLts A L} `{!LtsEq A L}
  `{!TransitionSystems.LtsOba A L} {PRE : Chain copre_m}: 
  Proper ((≡) ==> (eq_rel) ==> (impl)) (elem PRE).
Proof.
  intros ?? HX ?? Heq. rewrite (leibniz_equiv _ _ HX). clear x HX.
  revert x0 y0 Heq y.
  apply tower; clear PRE.
  - intros P HP h x0 y0 y Heq R HR; simpl in *; eapply HP; eauto. now apply Heq.
  - intros Hc Heq x0 y0 Hequiv y h. constructor.
    + intros q Hq.
      destruct (eq_spec x0 q τ) as (r & Hr & Heqr).
      * exists y0. split; trivial.
      * eapply Heq; eauto. now apply h.
    + intros hp hq. apply h.(c_now_) in hp as (p & p' & Hin & Hpp' & Hs' & Hinc).
      * exists p; exists p'. now setoid_rewrite <- Hequiv.
      * now setoid_rewrite Hequiv.
    + intros μ q' ps' Hcnv Hq' Hwts.
      destruct (eq_spec x0 q' (ActExt μ)) as (r & Hr & Heqr).
      * exists y0. split; trivial.
      * eapply Heq; eauto. eapply h.(c_step_) with μ; eauto.
    + intro ht. eapply terminate_preserved_by_eq2; eauto. now apply h.(c_cnv_).
Qed.

Lemma coin_union_l `{FiniteLts A L} {PRE : Chain copre_m}
  : forall (X1 X2 : gset A) (q : A), elem PRE X1 q -> elem PRE (X1 ∪ X2) q.
Proof.
  apply tower; clear PRE.
  - intros P HP ??????; eapply HP; eauto.
  - intros PRE CIH X1 X2 q h.
    unfold copre_m, body.
    constructor.
    + intros q' hqq'; now apply CIH, h.(c_tau_).
    + intros hp hq.
      assert (hp_ : ∀ p : A, p ∈ X1 → p ⤓) by (intros ??; now apply hp, elem_of_union_l).
      destruct (h.(c_now_) hp_ hq) as [ p [ p' [ pi [ hpp' out ] ] ]].
      exists p, p'; split; eauto.
      now apply elem_of_union_l.
    + intros μ q' ps' hp hqq' hps'.
      destruct (wt_set_union _ _ _ hp hps') as [ ps1 [ ps2 [ h1 [ h2 -> ] ] ] ].
      apply CIH.
      eapply h.(c_step_); [ | exact hqq' | exact h1 ].
      intros p i; now apply hp, elem_of_union_l.
    + intros hp.
      apply h.(c_cnv_).
      intros p i; now apply hp, elem_of_union_l.
Qed.

Lemma coin_union_r `{FiniteLts A L} {PRE : Chain copre_m}
  : forall (X1 X2 : gset A) (q : A), elem PRE X2 q -> elem PRE (X1 ∪ X2) q.
Proof.
  apply tower; clear PRE.
  - intros P HP ??????; eapply HP; eauto.
  - intros PRE CIH X1 X2 q h.
    unfold copre_m, body.
    constructor.
    + intros q' hqq'; now apply CIH, h.(c_tau_).
    + intros hp hq.
      assert (hp_ : ∀ p : A, p ∈ X2 → p ⤓) by (intros ??; now apply hp, elem_of_union_r).
      destruct (h.(c_now_) hp_ hq) as [ p [ p' [ pi [ hpp' out ] ] ]].
      exists p, p'; split; eauto.
      now apply elem_of_union_r.
    + intros μ q' ps' hp hqq' hps'.
      destruct (wt_set_union _ _ _ hp hps') as [ ps1 [ ps2 [ h1 [ h2 -> ] ] ] ].
      apply CIH.
      eapply h.(c_step_); [ | exact hqq' | exact h2 ].
      intros p i; now apply hp, elem_of_union_r.
    + intros hp.
      apply h.(c_cnv_).
      intros p i; now apply hp, elem_of_union_r.
Qed.

Lemma coin_elem_of `{FiniteLts A L} {PRE : Chain copre_m} (p : A) X: p ∈ X -> elem PRE X p.
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

Lemma copre_fw_inv_l `{FiniteLts A L} {PRE : Chain (copre_m (A := A * mb L) (B := A * mb L))} (p t: A):
  (∀ μ p', p ⟶{μ} p' <-> (p' = t /\ μ = τ)) ->
  forall M (X : gset (A * mb L)) (q : A * mb L),
    elem PRE ({[t ▷ M]} ∪ {[p ▷ M]} ∪ X) q
    -> elem PRE ({[p ▷ M]} ∪ X) q.
Proof.
  intros Hinv; apply tower; clear PRE.
  - intros P HP ??????; eapply HP; eauto.
  - intros PRE CIH M X q Hq.
    assert (Hpt : (p ▷ M) ⟶ (t ▷ M)) by (apply lts_fw_p, Hinv; tauto).
    constructor.
    + intros q' Hq'.
      apply CIH, Hq, Hq'.
    + intros Ht Hs.
      destruct Hq as [ _ Hq _ _].
      destruct Hq as (p1 & p2 & Hin & Hcnv & Hs' & Hout).
      * intros p0 Hin. repeat rewrite elem_of_union in Hin.
        destruct Hin as [[Heqt | Heqp] | Hin].
        ++ apply elem_of_singleton_1 in Heqt. subst.
           apply terminate_preserved_by_lts_tau with (p ▷ M).
           -- apply Ht. set_tac.
           -- assumption.
        ++ apply elem_of_singleton_1 in Heqp. subst.
           apply Ht. set_tac.
        ++ apply Ht. set_tac.
      * trivial.
      * repeat rewrite elem_of_union in Hin.
        destruct Hin as [[Heqt | Heqp] | Hin].
        ++ apply elem_of_singleton_1 in Heqt. subst.
           exists (p ▷ M). exists p2. repeat split; trivial.
           -- set_tac.
           -- apply wt_tau with (t ▷ M); assumption.
           -- apply Hs'.
           -- apply Hs'.
        ++ apply elem_of_singleton_1 in Heqp. subst.
           exists (p ▷ M). exists p2. repeat split; trivial.
           -- set_tac.
           -- apply Hs'.
           -- apply Hs'.
        ++ exists p1. exists p2; intuition.
           apply elem_of_union_r. set_tac.
    + intros μ q' ps' Hμ1 Hμ2 Hwt. eapply Hq; [| eassumption |].
      * intros p0 Hin. repeat rewrite elem_of_union in Hin.
        destruct Hin as [[Heqt | Heqp] | Hin].
        ++ apply elem_of_singleton_1 in Heqt. subst.
           apply cnv_preserved_by_lts_tau with (p ▷ M).
           -- apply Hμ1. set_tac.
           -- assumption.
        ++ apply elem_of_singleton_1 in Heqp. subst. apply Hμ1. set_tac.
        ++ apply Hμ1. set_tac.
      * destruct Hwt as [Hwt1 Hwt2].
        split.
        ++ intros p' Hp'. destruct (Hwt1 p' Hp') as [p0 [Hin Hp0]].
           repeat rewrite elem_of_union in Hin. destruct Hin as [Heqt | Hin].
           -- apply elem_of_singleton_1 in Heqt. subst.
              exists (p ▷ M). split; [set_tac|assumption].
           -- exists p0. split; [set_tac|assumption].
        ++ intros p' p'' Hin Hμ.
           repeat rewrite elem_of_union in Hin.
           destruct Hin as [[Heqt | Heqp] | Hin].
           -- apply elem_of_singleton_1 in Heqt. subst.
              eapply Hwt2 with (p ▷ M); [set_tac|].
              apply wt_tau with (t ▷ M); assumption.
           -- apply elem_of_singleton_1 in Heqp. subst.
              eapply Hwt2 with (p ▷ M); [set_tac|assumption].
           -- eapply Hwt2 with p'; [set_tac|]. apply Hμ.
    + intros Ht. apply Hq. intros p0 Hin.
      repeat rewrite elem_of_union in Hin. destruct Hin as [[Heqt | Heqp] | Hin].
      * apply elem_of_singleton_1 in Heqt. subst.
        apply terminate_preserved_by_lts_tau with (p ▷ M).
        ++ apply Ht. set_tac.
        ++ now apply Hpt.
      * apply elem_of_singleton_1 in Heqp. subst.
        apply Ht. set_tac.
      * apply Ht. set_tac.
Qed.

Lemma copre_inv_l `{FiniteLts A L} {PRE : Chain copre_m} (p : A) X t q : (p ⟶ t) -> (forall μ p', p ⟹{μ} p' <-> t ⟹{μ} p') ->
  elem PRE ({[t]} ∪ X) q -> elem PRE ({[p]} ∪ X) q.
Proof.
  intros Hpt Hinv; revert q.
  apply tower; clear PRE.
  - intros P HP ????; eapply HP; eauto.
  - intros PRE CIH q h.
    constructor.
    + intros q' Hq'.
      now apply CIH, h.(c_tau_).
    + intros Ht Hs.
      destruct h.(c_now_) as [ p1 [ p' [ hp [ hpp' [ hp' ho ] ] ] ]]; eauto.
      * intros p0 Hin.
        apply elem_of_union in Hin; destruct Hin as [Heqt | Hin].
        -- apply elem_of_singleton_1 in Heqt; subst.
           apply terminate_preserved_by_lts_tau with p; eauto.
           apply Ht; set_tac.
        -- apply Ht; set_tac.
      * apply elem_of_union in hp; destruct hp as [Heqt | Hin].
        -- apply elem_of_singleton_1 in Heqt; subst.
           exists p, p'; repeat split; [ set_tac | | | ]; trivial.
           now apply wt_tau with t.
        -- exists p1, p'; intuition.
           now apply elem_of_union_r.
    + intros μ q' ps' hμ hqq' w.
      eapply h.(c_step_); eauto.
      * intros p0 hin; apply elem_of_union in hin; destruct hin as [Heqt | Hin].
        -- apply elem_of_singleton_1 in Heqt; subst.
           apply cnv_preserved_by_lts_tau with p; eauto.
           apply hμ; set_tac.
        -- apply hμ; set_tac.
      * destruct w as [Hwt1 Hwt2]; split.
        -- intros p' Hp'.
           destruct (Hwt1 p' Hp') as [p0 [Hin Hp0]].
           apply elem_of_union in Hin; destruct Hin as [Heqt | Hin].
           ++ apply elem_of_singleton_1 in Heqt; subst.
              exists t; split; [set_tac|now apply Hinv].
           ++ exists p0. split; [set_tac|assumption].
        -- intros p' p'' Hin Hμ.
           apply elem_of_union in Hin; destruct Hin as [Heqt | Hin].
           ++ apply elem_of_singleton_1 in Heqt; subst.
              eapply Hwt2 with p; [set_tac|]; apply Hinv, Hμ.
           ++ eapply Hwt2 with p'; [set_tac|]; apply Hμ.
    + intros Ht.
      apply h.(c_cnv_); intros p0 Hin.
      apply elem_of_union in Hin; destruct Hin as [Heqt | Hin].
      * apply elem_of_singleton_1 in Heqt; subst.
        apply terminate_preserved_by_lts_tau with p; eauto.
        apply Ht; set_tac.
      * apply Ht; set_tac.
Qed.

Definition eq_rel_set `{FiniteLts A L} `{!TransitionSystems.LtsEq A L} (X Y : gset A) :=
 (forall x, x ∈ X -> exists y, y ∈ Y ∧ eq_rel x y) ∧
 (forall y, y ∈ Y -> exists x, x ∈ X ∧ eq_rel y x).

Global Instance symmetric_eq_rel_set `{FiniteLts A L} `{!TransitionSystems.LtsEq A L}:
 Symmetric eq_rel_set.
Proof. intros x y. unfold eq_rel_set. intuition. Qed.

Global Instance reflexive_eq_rel_set `{FiniteLts A L} `{!TransitionSystems.LtsEq A L}:
 Reflexive eq_rel_set.
Proof. intro X; split; intros x Hx; exists x; intuition. Qed.

Global Instance equiv_eq_rel_set `{FiniteLts A L} `{!TransitionSystems.LtsEq A L}:
 Proper ((≡) ==> (≡) ==> (impl)) eq_rel_set.
Proof.
intros X X' HX Y Y' HY Heq. split; intros x Hx.
- apply HX, Heq in Hx as (y & Hy & Heq'). apply HY in Hy. eauto.
- apply HY, Heq in Hx as (y & Hy & Heq'). apply HX in Hy. eauto.
Qed.

Global Instance eq_rel_set_union `{FiniteLts A L} `{!TransitionSystems.LtsEq A L}:
  Proper ((eq_rel_set) ==> (eq_rel_set) ==> (eq_rel_set)) union.
Proof.
intros X X' HX Y Y' HY.
split; setoid_rewrite elem_of_union; intros x [Hx|Hx];
 (apply HX in Hx || apply HY in Hx); destruct Hx as (y & Hy & Heq); eauto.
Qed.
(*
Lemma wt_s_set_eq_rel_set `{FiniteLts A L} `{!TransitionSystems.LtsEq A L}:
  forall {X X' : list A} {s} hcnv hcnv',
 ((forall x, x ∈ X -> exists y, y ∈ X' ∧ eq_rel x y) ∧
 (forall y, y ∈ X' -> exists x, x ∈ X ∧ eq_rel y x)) ->
  eq_rel_set (wt_s_set_from_pset_xs X s hcnv) (wt_s_set_from_pset_xs X' s hcnv').
Proof.
induction X as [|p X]; intros X' s hcnv hcnv' [Heq1 Heq2]; simpl.
- destruct X' as [|p' X'].
  + reflexivity.
  + exfalso. destruct (Heq2 p') as (x & Hx & _); [auto with *|]. inversion Hx.
- destruct (Heq1 p) as (p' & Hp' & Heq); [auto with *|].
  pose (X'' := remove lts_state_eqdec p' X').
  apply eq_rel_set_union.
  + admit.
  + eapply IHX. split; intros x Hx.
    * destruct (Heq1 x) as (y & Hy & Heq); [auto with *|].
      exists y.
apply Heq1.
rewrite IHX.
unfold wt_s_set_from_pset, wt_s_set_from_pset_xs.
fold wt_s_set_from_pset_xs.
wt_s_set_from_pset_xs
*)

Lemma wt_set_from_pset_spec_eq_rel_set `{FiniteLts A L} `{!TransitionSystems.LtsEq A L}:
  forall {X X' s Y}, eq_rel_set X X' -> (∀ p : A, p ∈ X → p ⇓ s) ->
  wt_set_from_pset_spec X s Y
  -> exists Y', eq_rel_set Y Y' ∧ wt_set_from_pset_spec X' s Y'.
Proof.
intros X X' s Y HXX' Hcnv Hwt.
assert (hcnv' : ∀ p : A, p ∈ X' → p ⇓ s). {
  intros p Hp. apply HXX' in Hp as (p' & Hp' & Heqp').
  rewrite Heqp'. now apply Hcnv.
}
unshelve eexists (wt_s_set_from_pset X' s hcnv').
assert(Hps' := wt_s_set_from_pset_ispec X' s hcnv').
split; trivial. split.
- intros x Hx. apply Hwt in Hx as (p & Hin & Hp).
  apply HXX' in Hin as (x' & Hx' & Heq').
  eapply eq_spec_wt in Hp as (y & Hy & Heq''); [|exact Heq'].
  exists y; split; trivial. eapply Hps'; eauto. now symmetry.
- intros x Hx. apply Hps' in Hx as (p & Hin & Hp).
  apply HXX' in Hin as (x' & Hx' & Heq').
  eapply eq_spec_wt in Hp as (y & Hy & Heq''); [|exact Heq'].
  exists y; split; trivial. eapply Hwt; eauto. now symmetry.
Qed.


Global Instance Proper_eq_rel_set_l `{FiniteLts A L} `{!TransitionSystems.LtsEq A L}:
  Proper ((eq_rel) ==> (=) ==> (eq_rel_set)) (fun p X => {[p]} ∪ X).
Proof.
intros p p' HX ???; subst. apply eq_rel_set_union; trivial.
split; setoid_rewrite elem_of_singleton;
intros x Hx; subst; eexists; split; trivial. now symmetry.
Qed.


Global Instance copre_eq_rel_l `{TransitionSystems.LtsOba A L} `{!FiniteLts A L}
  {PRE : Chain copre_m}: Proper ((eq_rel_set) ==> (=) ==> (impl)) (elem PRE).
Proof.
  intros X X' HXX' q q' ?; subst q'.
  revert X X' q HXX'. apply tower; clear PRE.
  - intros P HP ???????; eapply HP; eauto.
  - intros PRE CIH X X' q hXX' h.
    constructor.
    + intros q' Hq'.
      now apply CIH with (X := X), h.(c_tau_).
    + intros Ht Hs.
      destruct h.(c_now_) as [ p1 [ p' [ hp [ hpp' [ hp' ho ] ] ] ]]; eauto.
      * intros p0 Hin. apply hXX' in Hin as (p' & Hin & Heqp').
        apply (terminate_preserved_by_eq2 (symmetry Heqp')). now apply Ht.
      * apply hXX' in hp as (p'' & Hin & Heqp'').
        apply eq_spec_wt with (p' := p'') in hpp' as (r & Hr & Heqr); trivial.
        exists p''; exists r; repeat split; trivial; now rewrite Heqr.
    + intros μ q' ps' hμ hqq' w.
      apply (wt_set_from_pset_spec_eq_rel_set (symmetry hXX')) in w
        as (ps'' & Heqps' & HXps''); [|trivial].
      apply CIH with ps''; [now symmetry|].
      eapply h.(c_step_); eauto.
      intros p Hp. apply hXX' in Hp as (p'' & Hin & Heqp'').
      rewrite Heqp''; auto with *.
    + intros Ht.
      apply h.(c_cnv_); intros p0 Hin.
      apply hXX' in Hin as (p'' & Hin & Heqp'').
      eapply terminate_preserved_by_eq2; [apply symmetry, Heqp''|auto with *].
Qed.
