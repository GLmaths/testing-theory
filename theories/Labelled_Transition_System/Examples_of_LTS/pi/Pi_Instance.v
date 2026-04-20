(*
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

From Stdlib.Program Require Import Equality.
From Stdlib Require Import Relations Morphisms.
From Must Require Import Renamings Congruence LTS LTS_Renamings.

Parameter (channel_eq_dec : base.EqDecision Value).
#[global] Instance channel_eqdecision : base.EqDecision Value. Proof. exact channel_eq_dec. Defined.
Parameter (channel_is_countable : countable.Countable Value).
#[global] Instance channel_countable : countable.Countable Value. Proof. exact channel_is_countable. Defined.
Parameter (value_eq_dec : base.EqDecision Value).
#[global] Instance value_eqdecision : base.EqDecision Value. Proof. exact value_eq_dec. Defined.
Parameter (value_is_countable : countable.Countable Value).
#[global] Instance value_countable : countable.Countable Value. Proof. exact value_is_countable. Defined.

Inductive sts : proc -> proc -> Prop :=
| sts_com : forall {c v p1 p2 g1 g2}, 
    sts ((c ! v • p1) + g1 ‖ ((c ? p2) + g2)) (p1 ‖ p2 [⋅; v..])

| sts_tau : forall {p g}, 
    sts ((t • p) + g) p

| sts_recursion : forall {p}, 
    sts (rec p) (p [(rec p).. ; ⋅])

| sts_ifOne : forall {p q E}, Eval_Eq E = Some true -> 
    sts (If E Then p Else q) p

| sts_ifZero : forall {p q E}, Eval_Eq E = Some false -> 
    sts (If E Then p Else q) q

| sts_par : forall {p1 p2 q}, 
    sts p1 p2 ->
    sts (p1 ‖ q) (p2 ‖ q)

| sts_cong : forall {p1 p2 q2 q1},
    p1 ≡* p2 -> sts p2 q2 -> q2 ≡* q1 -> sts p1 q1

| sts_res : forall {p q},
    sts p q -> sts (ν p) (ν q)
.

#[global] Hint Constructors sts:ccs.

#[global] Instance sts_Proper : Proper (cgr ==> cgr ==> iff) sts.
Proof.
  intros x1 x2 Hx y1 y2 Hy.
  split; intros Hst.
  - eapply sts_cong; eauto. now rewrite Hx.
  - eapply sts_cong; eauto with cgr.
Qed.

Hint Rewrite <- cgr_par_assoc : cgr.
Hint Rewrite <- n_extrusion : cgr.
Hint Rewrite cgr_scope : cgr.

(* Lemma 1.2.20 from Sangiorgi and Walker *)
Lemma ReductionShape : forall P Q, sts P Q ->
((exists c v P1 P2 G1 G2 s n, (P ≡* νs n (((c ! v • P1) + G1 ‖ ((c ? P2) + G2)) ‖ s)) /\ (Q ≡* νs n ((P1 ‖ (P2[⋅;v..])) ‖ s)))
\/ (exists P1 G1 s n, (P ≡* νs n (((t • P1) + G1) ‖ s)) /\ (Q ≡* νs n (P1 ‖ s)))
\/ (exists P1 s n, (P ≡* νs n ((rec P1) ‖ s)) /\ (Q ≡* νs n (P1 [(rec P1)..; ⋅] ‖ s)))
\/ (exists P1 P0 s E n, (P ≡* νs n ((If E Then P1 Else P0) ‖ s)) /\ (Q ≡* νs n (P1 ‖ s)) /\ (Eval_Eq E = Some true))
\/ (exists P1 P0 s E n, (P ≡* νs n ((If E Then P1 Else P0) ‖ s)) /\ (Q ≡* νs n (P0 ‖ s)) /\ (Eval_Eq E = Some false))
).
Proof with autorewrite with cgr; reflexivity.
intros P Q Transition.
induction Transition.
  - left. exists c, v, p1, p2, g1, g2, 𝟘, 0. split; apply cgr_par_nil_rev.
  - right. left. exists p, g0, 𝟘, 0. split; apply cgr_par_nil_rev.
  - right. right. left. exists p, 𝟘, 0. split; apply cgr_par_nil_rev.
  - right. right. right. left. exists p, q, 𝟘, E, 0.
    repeat split; [apply cgr_par_nil_rev | apply cgr_par_nil_rev | assumption].
  - right. right. right. right. exists p, q, 𝟘, E, 0.
    repeat split; [apply cgr_par_nil_rev | apply cgr_par_nil_rev | assumption].
  - destruct IHTransition as [IH|[IH|[IH|[IH |IH]]]].
    + destruct IH as (c & v & P1 & P2 & g1 & g2 & s & n & H1 & H2).
      left. destruct n.
      * exists c, v, P1, P2, g1,g2, (s ‖ q), 0. split; rewrite ?H1, ?H2...
      * exists c, v, P1, P2, g1,g2, (s ‖ nvars n (⇑ q)), (S n).
        split; simpl; rewrite ?H1, ?H2...
    + destruct IH as (P1 & P2 & s & n & H1 & H2). right. left. destruct n.
      * exists P1, P2, (s ‖ q), 0. split; rewrite ?H1, ?H2...
      * exists P1, P2, (s ‖ nvars n (⇑ q)), (S n).
        split; simpl; rewrite ?H1, ?H2...
    + destruct IH as (P1 & s & n & [H1 H2]). right. right. left. destruct n.
      * exists P1, (s ‖ q), 0. split; rewrite ?H1, ?H2...
      * exists P1, (s ‖ nvars n (⇑ q)), (S n).
        split; simpl; rewrite ?H1, ?H2...
    + destruct IH as (P1 & P0 & s & E & n & [H1 [H2 H3]]).
      right. right. right. left. destruct n.
      * exists P1, P0, (s ‖ q), E, 0.
        repeat split; [ rewrite H1 | rewrite H2 | assumption]...
      * exists P1, P0, (s ‖ nvars n (⇑ q)), E, (S n).
        repeat split; simpl; [ rewrite H1 | rewrite H2 | assumption ]...
    + destruct IH as (P1 & P0 & s & E & n & [H1 [H2 H3]]).
      right. right. right. right. destruct n; simpl in H1, H2.
      * exists P1, P0, (s ‖ q), E, 0.
        repeat split; [ rewrite H1 | rewrite H2 | assumption ]...
      * exists P1, P0, (s ‖ nvars n (⇑ q)), E, (S n).
        repeat split; simpl; [ rewrite H1 | rewrite H2 | assumption ]...
  - destruct IHTransition as [IH|[IH|[IH|[IH |IH]]]].
    + destruct IH as (c & v & P1 & P2 & g1 & g2 & s & n & H1 & H2).
      left. exists c, v, P1, P2, g1, g2, s, n.
      split; [ now rewrite <- H1 | now rewrite <- H2 ].
    + destruct IH as (P1 & P2 & s & n & [H1 H2]).
      right. left. exists P1, P2, s, n.
      split; [ now rewrite <- H1 | now rewrite <- H2 ].
    + destruct IH as (P1 & s & n & [H1 H2]).
      right. right. left. exists P1, s, n.
      split; [ now rewrite <- H1 | now rewrite <- H2 ].
    + destruct IH as (P1 & P0 & s & E & n & H1 & H2 & H3).
      right. right. right. left. exists P1, P0, s, E, n.
      repeat split; now rewrite <- ?H1, <- ?H2.
    + destruct IH as (P1 & P0 & s & E & n & H1 & H2 & H3).
      right. right. right. right. exists P1, P0, s, E, n.
      repeat split; now rewrite <- ?H1, <- ?H2.
  - destruct IHTransition as [IH|[IH|[IH|[IH |IH]]]].
    + destruct IH as (c & v & P1 & P2 & g1 & g2 & s & n & H1 & H2).
      left. exists c, v, P1, P2, g1, g2, s, (S n).
      split; [now rewrite H1 | now rewrite H2 ].
    + destruct IH as (P1 & P2 & s & n & H1 & H2).
      right. left. exists P1, P2, s, (S n).
      split; [ now rewrite H1 | now rewrite H2 ].
    + destruct IH as (P1 & s & n & H1 & H2).
      right. right. left. exists P1, s, (S n).
      split; [ now rewrite H1 | now rewrite H2 ].
    + destruct IH as (P1 & P0 & s & E & n & H1 & H2 & H3).
      right. right. right. left. exists P1, P0, s, E, (S n).
      repeat split; now rewrite ?H1, ?H2.
    + destruct IH as (P1 & P0 & s & E & n & H1 & H2 & H3).
      right. right. right. right. exists P1, P0, s, E, (S n).
      repeat split; now rewrite ?H1, ?H2.
Qed.


Ltac not_a_guard := intro hex; inversion hex as [L absurd_hyp]; inversion absurd_hyp.
Ltac finish_zero H := rewrite H, <- cgr_par_assoc.
Ltac finish_Sn H :=  rewrite H, <- cgr_par_assoc, <- n_extrusion, cgr_scope.

Lemma TransitionShapeForInput : forall P Q c v,
  lts P (ActIn (c ⋉ v)) Q -> exists P1 G R n,
  (P ≡* νs n (((nvars n c) ? P1 + G) ‖ R)) /\
  (Q ≡* νs n (P1[⋅; (nvars n v)..] ‖ R))   /\
  ((exists L, P = g L) -> R = 𝟘 /\ n = 0).
Proof.
intros P Q c v.
intro Transition. dependent induction Transition;
try destruct (IHTransition c v eq_refl) as (P1 & G & R & n & H0 & H1 & H3).
- exists P, 𝟘, 𝟘, 0. split; eauto with cgr.
- destruct (IHTransition (⇑ c) (⇑ v) eq_refl) as (P1 & G & R & n & H0 & H1 & H3).
  exists P1, G, R, (S n). simpl. do 2 (try split).
  + now rewrite shift_in_nvars, H0.
  + now rewrite shift_in_nvars, H1.
  + not_a_guard.
- destruct n.
  + exists P1, G, (R ‖ q), 0. simpl. do 2 (try split).
    * now rewrite H0, <- cgr_par_assoc.
    * now rewrite H1, <- cgr_par_assoc.
    * not_a_guard.
  + exists P1, G, (R ‖ nvars n (⇑ q)), (S n). simpl. do 2 (try split).
    * now finish_Sn H0.
    * now finish_Sn H1.
    * not_a_guard.
- destruct n; simpl in H0, H1.
  + exists P1, G, (R ‖ p), 0. simpl. do 2 (try split).
    * now rewrite H0, cgr_par_com, cgr_par_assoc.
    * now rewrite H1, cgr_par_com, cgr_par_assoc.
    * not_a_guard.
  + exists P1, G, (R ‖ nvars n (⇑ p)), (S n). simpl. do 2 (try split).
    * finish_Sn H0. now rewrite cgr_par_com.
    * finish_Sn H1. now rewrite cgr_par_com.
    * not_a_guard.
- destruct n.
  + exists P1, (G + p2), R, 0. simpl. do 2 (try split).
    * destruct H3. { now exists p1. } subst.
      rewrite cgr_par_nil, <- cgr_choice_assoc. apply cgr_choice.
      now rewrite H0, cgr_par_nil.
    * now rewrite H1.
    * intro. apply H3. now exists p1.
  + destruct H3 as [_ AbsHyp]. {now exists p1. } inversion AbsHyp.
- destruct n.
  + exists P1, (G + p1), R, 0. simpl. do 2 (try split).
    * destruct H3. { now exists p2. } subst.
      rewrite cgr_par_nil, <- cgr_choice_assoc, cgr_choice_com.
      apply cgr_choice.
      now rewrite H0, cgr_par_nil.
    * now rewrite H1.
    * intro. apply H3. now exists p2.
  + destruct H3 as [_ AbsHyp]. {now exists p2. } inversion AbsHyp.
Qed.

Lemma TransitionShapeForFreeOutput : forall P Q c v,
  lts P (FreeOut (c ⋉ v)) Q -> exists P1 G R n,
  P ≡* νs n ((nvars n c) ! (nvars n v) • P1 + G ‖ R) /\
  Q ≡* νs n (P1 ‖ R) /\
  ((exists L, P = g L) -> (R = 𝟘 /\ n = 0)).
Proof.
intros P Q c v Transition.
dependent induction Transition; try destruct (IHTransition c v eq_refl)
  as (P1 & G & R & n & H0 & H1 & H3).
- exists P, 𝟘, 𝟘, 0. repeat split; eauto with cgr.
- destruct (IHTransition (⇑ c) (⇑ v) eq_refl) as (P1 & G & R & n & H0 & H1 & H3).
    exists P1, G, R, (S n). do 2 (try split).
  + simpl. repeat rewrite shift_in_nvars. now rewrite H0.
  + simpl. now rewrite H1.
  + not_a_guard.
- destruct n.
  + exists P1, G, (R ‖ q), 0. do 2 (try split).
    * now finish_zero H0.
    * now finish_zero H1.
    * not_a_guard.
  + exists P1, G, (R ‖ nvars (S n) q), (S n). do 2 (try split).
    * now rewrite H0, n_extrusion, cgr_par_assoc.
    * now rewrite H1, n_extrusion, cgr_par_assoc.
    * not_a_guard.
- destruct n; simpl in H0, H1.
  + exists P1, G, (R ‖ p), 0. do 2 (try split).
    * now rewrite H0, cgr_par_com, cgr_par_assoc.
    * now rewrite H1, cgr_par_com, cgr_par_assoc.
    * not_a_guard.
  + exists P1, G, (R ‖ nvars n (⇑ p)), (S n). do 2 (try split).
    * simpl. now rewrite H0, <- cgr_par_com, <- cgr_par_assoc, <- n_extrusion, cgr_scope.
    * simpl. now rewrite H1, <- cgr_par_com, <- cgr_par_assoc, <- n_extrusion, cgr_scope.
    * not_a_guard.
- destruct n.
  + exists P1, (G + p2), R, 0. do 2 (try split).
    * destruct H3. { now exists p1. } subst.
      rewrite cgr_par_nil, <- cgr_choice_assoc. apply cgr_choice.
      now rewrite H0, cgr_par_nil.
    * now rewrite H1.
    * intro. apply H3. now exists p1.
  + destruct H3 as [_ AbsHyp]. {now exists p1. } inversion AbsHyp.
- destruct n.
  + exists P1, (G + p1), R, 0. do 2 (try split).
    * destruct H3. { now exists p2. } subst.
      rewrite cgr_choice_com.
      rewrite cgr_par_nil. rewrite <- cgr_choice_assoc. apply cgr_choice.
      now rewrite H0, cgr_par_nil.
    * now rewrite H1.
    * intro. apply H3. now exists p2.
  + destruct H3 as [_ AbsHyp]. {now exists p2. } inversion AbsHyp.
Qed.

Lemma GuardedDoesNoBoundOutput : forall p c q, not (lts (g p) (BoundOut c) q).
Proof. 
intros. intro Transition.
dependent induction Transition; eapply IHTransition; eauto.
Qed.

Lemma TransitionShapeForBoundOutput : forall P Q c,
  lts P (BoundOut c) Q ->
  exists n P' Q' G',
  (P ≡* νs (S n) (nvars (S n) c ! (nvars n (var_Data 0)) • P' + G' ‖ Q')
  /\ Q ≡* (νs n (P' ‖ Q'))).
Proof.
intros. dependent induction H.
- destruct (IHlts (⇑ c) eq_refl) as (n & P & Q & G' & HcongrP & HcongrQ).
  exists (S n), (P ⟨ upn n swap ⟩), (Q ⟨ upn n swap ⟩),
         (G' ⟨ upn n swap ⟩).
  split.
  + simpl.
    rewrite <- upnswap_neut.
    rewrite var0_shiftupn2.
    change
      ((ren1 (upn n swap) (⇑ (⇑ (nvars n c)))) !
        ren1 (upn n swap) (nvars n (var_Data 0))
        • P ⟨ upn n swap ⟩ + G' ⟨ upn n swap ⟩ ‖ Q ⟨ upn n swap ⟩)
    with
    ((⇑ (⇑ (nvars n c)) ! nvars n (var_Data 0) • P + G' ‖ Q) ⟨ upn n swap ⟩).
    rewrite <- upn_νs.
    rewrite shift_in_nvars.
    rewrite HcongrP.
    apply cgr_nu_nu.
  + simpl. rewrite HcongrQ. now rewrite upn_νs.
- destruct (TransitionShapeForFreeOutput _ _ _ _ H) as (p & g & r & n & H0 & H1 & ?).
  exists n. repeat eexists.
  + simpl. rewrite shift_in_nvars. now rewrite H0.
  + simpl. now rewrite H1.
- destruct (IHlts c eq_refl) as (n & P & Q & G & HcongrP & HcongrQ).
  exists n, P, (Q ‖ nvars n (⇑ q)). repeat eexists.
  + rewrite HcongrP. simpl.
    now rewrite <- cgr_par_assoc, <- n_extrusion, cgr_scope.
  + rewrite HcongrQ.
    now rewrite <- cgr_par_assoc, <- n_extrusion.
- destruct (IHlts c eq_refl) as (n & P & Q & G & HcongrP & HcongrQ).
  exists n, P, (Q ‖ nvars n (⇑ p)). repeat eexists.
  + rewrite HcongrP. simpl. rewrite <- cgr_par_assoc, <- n_extrusion.
    now rewrite cgr_scope, (cgr_par_com p), (cgr_par_com _ Q).
  + rewrite HcongrQ. now rewrite <- cgr_par_assoc, <- n_extrusion, cgr_par_com.
- apply GuardedDoesNoBoundOutput in H. contradiction.
- apply GuardedDoesNoBoundOutput in H. contradiction.
Qed.

Lemma TransitionShapeForTauAndGuard : forall P V, ((lts P τ V) /\ (exists L, P = (g L))) -> 
(exists Q M, ((P ≡* ((t • Q) + M))) /\ (V ≡* (Q))).
Proof.
intros P V (Transition & guard_witness). 
dependent induction Transition;
  try (inversion guard_witness as (g & A); inversion A).
  - exists P. exists 𝟘. split. 
    * apply cgr_choice_nil_rev.
    * apply cgr_refl.
  - destruct (IHTransition (reflexivity τ)).
    * now exists p1.
    * destruct H. destruct H. exists x. 
      exists (x0 + p2). split; eauto.
      rewrite <- cgr_choice_assoc.
      apply cgr_choice. assumption.
  - destruct (IHTransition (reflexivity τ)).
    * now exists p2.
    * destruct H. destruct H.
      exists x.
      eexists (x0 + p1). split; eauto.
      rewrite <- cgr_choice_assoc.
      rewrite cgr_choice_com.
      apply cgr_choice. assumption.
Qed.
  
Ltac case_shift :=
  match goal with
  |- context G [ ?a ⇑? _ ] => case is_bound_out
  end.
Hint Extern 1 (_ ≡* _) => case_shift:cgr.

(* p 'is equivalent some r 'and r performs α to q *)
Definition sc_then_lts p α q := exists r, r ≡* p /\ (lts r α q).

(* p 'is equivalent some r 'and r performs α to q *)
Definition sc_step_then_lts p α q := exists r, r ≡ p /\ (lts r α q).

(* p performs α to some r and this is equivalent to q*)
Definition lts_then_sc p α q := exists r, ((lts p α r) /\ r ≡* q).
Hint Unfold lts_then_sc:lts.

(* p 'is equivalent some r 'and r performs α to q , the congruence and the Transition can be reversed : *)
(* fact 1.4.16 in Sangiorgi&Walker *)
(* First we prove it just for one step, then for the full congruence *)
Lemma Congruence_Respects_Transition_Step : forall p q α,
  sc_step_then_lts p α q -> lts_then_sc p α q.
Proof with (eauto with lts cgr).
unfold sc_step_then_lts, lts_then_sc.
intros p' q α (p & hcgr & hlts).
revert p' hcgr.
dependent induction hlts; intros p'' hcgr.
- (* lts_input *)     inversion hcgr... eexists; rewrite H2...
- (* lts_output *)    inversion hcgr... subst. eexists. split; [apply lts_output | now rewrite H3].
- (* lts_tau *)       inversion hcgr... eexists; rewrite H0...
- (* lts_recursion *) inversion hcgr... eexists; rewrite H0...
- (* lts_ifOne *)
  inversion hcgr... repeat eexists.
  + eauto with lts.
  + now constructor.
- (* lts_ifZero *)
  inversion hcgr... repeat eexists.
  + eauto with lts.
  + now constructor.
- (* lts_comL *)
  inversion hcgr...
  + subst. inversion hlts2.
  + (* cgr_par_assoc *) subst. inversion hlts1...
  + (* cgr_par_assoc_rev *) subst. inversion hlts2...
  + (* cgr_par *) subst. destruct (IHhlts1 _ H2) as [r [Hlts Hcongr]]...
  + (* cgr_scope_rev *)
    subst p1. inversion hlts1.
    apply shift_transition, proj1 in hlts2.
    repeat eexists...
- (* lts_comR *)
  inversion hcgr...
  + subst p1. inversion hlts1.
  + (* cgr_par_assoc *) subst. inversion hlts2...
  + (* cgr_par_assoc_rev *) subst. inversion hlts1...
  + (* cgr_par *) subst. destruct (IHhlts2 _ H2) as [r [Hlts Hcongr]]...
  + (* cgr_scope_rev *)
    subst q1. inversion hlts2.
    apply shift_transition, proj1 in hlts1.
    repeat eexists...
- (* lts_close_l *)
  inversion hcgr...
  + subst q1. inversion hlts2.
  + (* cgr_par_assoc *) subst.
    inversion hlts1.
    * subst. repeat eexists.
      -- eapply lts_close_l. exact H1. eapply parR_not_bound...
      -- simpl...
    * subst. repeat eexists...
  + (* cgr_par_assoc_rev *) subst.
    inversion hlts2.
    * subst. repeat eexists...
    * subst. repeat eexists...
  + (* cgr_par *) subst. destruct (IHhlts1 _ H2) as [r [Hlts Hcongr]].
    repeat eexists...
  + (* cgr_scope_rev *)
    subst p1. inversion hlts1.
    * subst. apply shift_transition, proj1 in hlts2.
      specialize (hlts2 eq_refl).
      apply swap_transition, proj1 in hlts2.
      rewrite Shift_Shift_Swap_pr in hlts2. cbn in hlts2.
      replace (ren_Data swap (ren_Data shift (⇑ c)) ⋉ 0) with
              (ren_Data swap (⇑ (⇑ c)) ⋉ 0) in hlts2 by now cbn.
      rewrite Shift_Shift_Swap_Data in hlts2. specialize (hlts2 eq_refl).
      repeat eexists.
      ** eapply lts_res. eapply lts_close_l. exact H0. apply hlts2.
      ** simpl. rewrite <- (Swap_Proc_Involutive q) at 1.
         change (q ⟨swap⟩⟨swap⟩ ‖ (⇑ q2) ⟨ swap ⟩) with ((q ⟨ swap ⟩ ‖ (⇑ q2)) ⟨ swap ⟩).
         rewrite <- cgr_nu_nu. now rewrite cgr_scope_rev.
    * eauto with lts cgr.
- (* lts_close_r *)
  inversion hcgr...
  + subst q1. inversion hlts1.
  + (* cgr_par_assoc *) subst. inversion hlts2...
    * subst. repeat eexists...
    * subst. repeat eexists...
  + (* cgr_par_assoc_rev *) subst. inversion hlts1...
    * subst. repeat eexists...
    * subst. repeat eexists.
      -- eapply lts_close_r. exact H1. eapply lts_parL...
      -- simpl...
  + (* cgr_par *) subst.
    assert (Hshift : ⇑ p1 ≡ ⇑ q) by
    (apply RenProperStep; trivial; intro x; trivial).
    destruct (IHhlts2 _ Hshift) as [r [Hlts Hcongr]].
    repeat eexists...
  + (* cgr_scope_rev *)
    subst p1. inversion hlts2; subst.
    * apply shift_transition, proj2 in hlts1.
      specialize (hlts1 eq_refl).
      (* This is a clever example of using swap in a place
         where no actual swap rule is involved *)
      repeat eexists.
      -- eapply lts_res. eapply lts_close_r. exact hlts1.
         eapply swap_transition, proj1 in H0.
         specialize (H0 eq_refl).
         rewrite <- Shift_Swap in H0.
         rewrite Swap_Proc_Involutive in H0.
         change (ren1 swap (⇑ (ActIn (⇑ c ⋉ 0))))
           with (ActIn (ren1 swap (⇑ (⇑ c)) ⋉ 0)) in H0.
         rewrite Shift_Shift_Swap_Data in H0.
         apply H0.
      -- simpl. rewrite <- Shift_Swap.
         change ((q ⟨ swap ⟩ ‖ (⇑ q2) ⟨ swap ⟩))
           with ((q ‖ (⇑ q2)) ⟨ swap ⟩).
         now rewrite <- cgr_nu_nu, cgr_scope_rev.
- (* lts_res *)
  inversion hcgr.
  + (* cgr_refl *) eauto with lts cgr.
  + (* cgr_res_nil *) subst. repeat eexists... 
  + (* cgr_nu_nu *)
    subst. inversion hlts; subst.
    (* lts_res *)
    * destruct α; try destruct e.
      -- apply swap_transition, proj1 in H0. specialize (H0 eq_refl).
         rewrite Shift_Shift_Swap_Act in H0.
         repeat eexists.
         ++ eapply lts_res. eapply lts_res. exact H0.
         ++ simpl. now rewrite <-  cgr_nu_nu.
      -- apply swap_transition, proj1 in H0. specialize (H0 eq_refl).
         rewrite Shift_Shift_Swap_Act in H0.
         repeat eexists.
         ++ eapply lts_res. eapply lts_res. exact H0.
         ++ simpl. now rewrite <-  cgr_nu_nu.
      -- apply swap_transition, proj2 in H0. specialize (H0 eq_refl).
         rewrite Shift_Shift_Swap_Act in H0.
         repeat eexists.
         ++ eapply lts_res. eapply lts_res. exact H0.
         ++ etransitivity; [apply cgr_nu_nu|]. fold ren_proc. asimpl. simpl.
            apply cgr_res, cgr_res.
            eapply RenProper; try easy.
            intro n. do 4 (destruct n as [|n]; trivial).
      -- apply swap_transition, proj1 in H0. specialize (H0 eq_refl).
         rewrite Shift_Shift_Swap_Act in H0.
         repeat eexists.
         ++ eapply lts_res. eapply lts_res. exact H0.
         ++ simpl. now rewrite <-  cgr_nu_nu.
    (* lts_open *)
    * apply Invert_Bound_Out in H0. destruct H0 as [d [Hd Hbound]].
      rewrite Hbound. eexists. split.
      -- eapply swap_transition, proj1 in H1.
         specialize (H1 eq_refl).
         rewrite Hd in H1.
         change (ren1 swap (FreeOut ((⇑ (⇑ d)) ⋉ 0))) with
                (FreeOut (ren1 swap (⇑ (⇑ d)) ⋉ 1)) in H1.
         rewrite Shift_Shift_Swap_Data in H1.
         eapply lts_open.
         eapply lts_res. apply H1.
      -- reflexivity.
  + subst p. inversion hlts.
  + (* cgr_res *)
    subst. destruct (IHhlts _ H0) as [r [Hlts Hcongr]].
    repeat eexists.
    * eapply lts_res. exact Hlts.
    * case_eq (is_bound_out α); now rewrite Hcongr.
  + (* cgr_scope_rev *)
      (* res case: then νP ‖ Q did any action, and we have 6 possible cases *)
      subst. inversion hlts.
        (* lts_comL *)
        -- replace α with τ by (destruct α; try destruct e; now inversion H1).
           destruct (Invert_Lts_Input _ _ _ _ _ H4) as (c' & Hc'). subst.
           destruct v.
           (* communicate a channel *)
           ++ destruct n.
              (* the channel is 0. Then this "com" becomes "close" *)
              ** eexists. split; [|reflexivity].
                 eapply lts_close_l; [apply (lts_open H2) | apply H4].
              (* the channel is S n. So it is actually "com" *)
              ** replace (FreeOut (((ren1 shift c') ⋉ (S n)))) with 
                         (⇑ (FreeOut (c' ⋉ n))) in H2 by now asimpl.
                 replace (var_Data (S n)) with (ren1 shift (var_Data n)) in H4 by now asimpl.
                 destruct (Invert_Lts_Input_Full _ _ _ _ _ H4) as (d & q' & H & Heq1 & Heq2).
                 apply Injective_Ren_Data in H; [|apply Shift_Injective].
                 eexists. split.
                 --- eapply lts_comL; [eauto with lts|]. rewrite H. apply Heq2.
                 --- rewrite Heq1. eauto with cgr.
           (* communicate a constant value *)
           ++ replace (FreeOut (((ren1 shift c') ⋉ v))) with
                      (ren1 shift (FreeOut ((c' ⋉ v)))) in H2 by now asimpl.
              replace (cst v) with (ren1 shift (cst v)) in H4 by now asimpl.
              destruct (Invert_Lts_Input_Full _ _ _ _ _ H4) as (d & q' & H & Heq1 & Heq2).
              apply Injective_Ren_Data in H; [|apply Shift_Injective].
              eexists. split.
              ** eapply lts_comL. eapply lts_res, H2. rewrite H. apply Heq2.
              ** rewrite Heq1. eauto with cgr.
        (* lts_comR *)
        -- replace α with τ by (destruct α; try destruct e; now inversion H1).
            destruct (Invert_Lts_FreeOut _ _ _ _ _ H2) as (c' & v' & q' & Hc' & Hv' & Hq' & Htransition).
            subst.
            eexists. split.
            ++ eapply lts_comR; [exact Htransition|]. eapply lts_res. apply H4.
            ++ eauto with cgr.
        (* lts_close_l *)
        -- replace α with τ by (destruct α; try destruct e; now inversion H1).
           (* Pack the two shifts in a single renaming, to be used with Invert_Lts_Input *)
           (* (can't do it with replace because asimpl complains about evars) *)
           assert (Hrew: (⇑ (⇑ Q)) = (ren_proc ids (shift >> shift) Q)) by now asimpl.
           rewrite Hrew in H4.
           destruct (Invert_Lts_Input _ _ _ _ _ H4) as (c' & Hc').
           replace (ren1 (shift >> shift) c') with (⇑ (⇑ c')) in Hc' by now asimpl.
           apply Injective_Ren_Data in Hc'; [|apply Shift_Injective]. subst.
           rewrite <- Hrew in H4. clear Hrew.
           apply swap_transition, proj1 in H4. specialize (H4 eq_refl).
           rewrite Shift_Shift_Swap_pr in H4. cbn in H4.
           rewrite Shift_Shift_Swap_Data in H4.
           change (var_Data 1) with (⇑ (var_Data 0)) in H4.
           destruct (Invert_Lts_Input_Full _ _ _ _ _ H4) as (d & q' & H & Heq1 & Heq2).
           apply Injective_Ren_Data in H; [|apply Shift_Injective]. rewrite <- H in Heq2.
           change (q' ⟨shift⟩) with (⇑ q') in Heq1.
           eexists. split.
           ++ eapply lts_close_l. eapply lts_res, H2. apply Heq2.
           ++ simpl. rewrite cgr_scope_rev. rewrite <- Heq1.
              change (p2 ⟨swap⟩ ‖ q2 ⟨ swap ⟩) with ((p2 ‖ q2) ⟨ swap ⟩).
              symmetry. apply cgr_nu_nu.
        (* lts_close_r *)
        -- replace α with τ by (destruct α; try destruct e; now inversion H1).
           destruct (Invert_Lts_BoundOut _ _ _ _ H2) as (c' & v' & Hc' & Hv' & Htransition).
           eapply swap_transition, proj1 in H4. specialize (H4 eq_refl).
           rewrite Shift_Swap in H4. rewrite Hc' in H4. 
           replace (ren1 swap (ActIn (⇑ (ren1 shift c') ⋉ 0))) with
                   (ActIn (ren1 swap (⇑ (⇑ c')) ⋉ 1)) in H4 by trivial.
           rewrite Shift_Shift_Swap_Data in H4.
           eexists. split.
           ++ eapply lts_close_r; [apply Htransition | eapply lts_res, H4].
           ++ simpl. rewrite Hv'. rewrite <- Shift_Swap.
              rewrite cgr_scope_rev. rewrite cgr_nu_nu. cbn.
              now rewrite Swap_Proc_Involutive.
        (* parL *)
        -- subst q'. eexists. split.
           ++ eapply lts_parL...
           ++ case_eq (is_bound_out α);
              intro Hbound; rewrite is_bound_shift in Hbound; rewrite Hbound.
              ** rewrite cgr_scope_rev. now asimpl.
              ** eauto with cgr.
        (* parR *)
        -- case_eq (is_bound_out α); intro Hbound.
           ++ destruct (is_bound_exists α Hbound) as [c Hc]. subst α.
              destruct (Invert_Lts_BoundOut _ _ _ _ H1) as (d & v' & Hc' & Hv' & Htransition).
              replace c with d by now (apply Injective_Ren_Data in Hc'; [|apply Shift_Injective]).
              subst.
              eexists. split.
              ** eapply lts_parR. apply Htransition. reflexivity.
              ** simpl. rewrite <- Shift_Swap. cbn. rewrite Swap_Proc_Involutive.
                 rewrite Shift_Swap. apply cgr_scope_rev.
           ++ destruct (Invert_Lts_Alpha _ _ _ _ Hbound Shift_Injective H1) as (q' & Hq' & Htransition).
              subst q2.
              subst p'. eexists. split.
              ** eapply lts_parR. exact Htransition. reflexivity.
              ** rewrite Hbound. rewrite is_bound_shift in Hbound. rewrite Hbound.
                 apply cgr_scope_rev.
- (* lts_open *)
  inversion hcgr...
  + (* cgr_nu_nu *)
    subst. inversion hlts. eexists. split.
    -- eapply swap_transition, proj1 in H0.
       specialize (H0 eq_refl).
       replace (ren1 swap (⇑ (FreeOut (⇑ c ⋉ 0)))) with
               (FreeOut (ren1 swap (⇑ (⇑ c)) ⋉ 0)) in H0
       by now cbn.
       rewrite Shift_Shift_Swap_Data in H0.
       apply (@lts_res _ (q ⟨swap⟩)). apply lts_open. exact H0.
    -- now rewrite Swap_Proc_Involutive.
  + subst p1; inversion hlts.
  + (* cgr_res *)
    subst. destruct (IHhlts _ H0) as [r [Hlts Hcongr]].
    repeat eexists...
  + (* cgr_scope_rev *) subst p1. dependent destruction hlts.
    -- eexists. split.
       ++ eapply lts_parL...
       ++ reflexivity.
    -- (* this is not possible : ⇑ Q can't output on 0 *)
       destruct (Invert_Lts_FreeOut _ _ _ _ _ hlts) as (? & v' & ? & ? & Hv' & ?).
       destruct v'; try destruct n; inversion Hv'.
- (* lts_parL *)
  inversion hcgr...
  + subst...
  + subst. destruct (IHhlts p1) as [x [Hlts Hcongr]]. reflexivity.
     eexists. split.
    * eapply lts_parL. eapply lts_parL. apply Hlts. reflexivity. reflexivity.
    * replace (α ⇑? (g 𝟘)) with (g 𝟘) by (destruct α; try destruct e; reflexivity).
      rewrite cgr_par_nil_step. now rewrite Hcongr.
  + (* cgr_par_assoc *) subst. inversion hlts...
    * subst. eexists. split.
      -- eapply lts_close_l. exact H1. eapply lts_parL. exact H4. reflexivity.
      -- fold ren_proc. simpl. now rewrite <- cgr_par_assoc, cgr_scope_rev.
    * subst. eexists. split...
    * subst. eexists. split...
  + (* cgr_par_assoc_rev *) subst. eexists...
  + (* cgr_parL *) subst. destruct (IHhlts q0) as [x [Hlts Hcongr]]...
  + (* cgr_scope_rev *) subst. inversion hlts; subst.
    * eexists. split.
      -- eapply lts_res. eapply lts_parL. exact H0. reflexivity.
      -- case_eq (is_bound_out α); intro Hbound;
         rewrite is_bound_shift in Hbound; rewrite Hbound.
         ** rewrite cgr_scope_rev. cbn. now rewrite Shift_Shift_Swap_pr.
         ** eauto with cgr.
    * eauto with lts cgr.
- (* lts_parR *) inversion hcgr...
  + subst. inversion hlts.
  + subst. destruct (IHhlts q1) as [x [Hlts Hcongr]]. reflexivity.
    eexists. split.
    * eapply lts_parL. eapply lts_parR. apply Hlts. reflexivity. reflexivity.
    * replace (α ⇑? (g 𝟘)) with (g 𝟘) by
      (destruct α; try destruct e; reflexivity).
      rewrite cgr_par_nil_step. now rewrite Hcongr.
  + (* cgr_par_assoc *) subst. eexists...
  + (* cgr_par_assoc_rev *) subst. inversion hlts...
    * subst. eexists. split.
      -- eapply lts_close_l. eapply lts_parR. exact H1. reflexivity. exact H4.
      -- simpl. now rewrite cgr_par_assoc, cgr_par_com, cgr_scope, cgr_par_com.
    * subst. eexists. split.
      -- eapply lts_close_r. exact H1. eapply lts_parR. exact H4. reflexivity.
      -- fold ren_proc. simpl. change (ren_proc ids shift p) with (⇑ p).
         now rewrite cgr_par_assoc, cgr_par_com, cgr_scope, cgr_par_com.
    * subst. eexists. split...
  + (* cgr_parR *) subst. eexists. split.
    * eapply lts_parR. exact hlts. reflexivity.
    * assert (Hshift : ⇑ p ≡ ⇑ q) by
      (apply RenProperStep; trivial; intro x; trivial).
      case is_bound_out; now rewrite ?H3, ?Hshift.
  + (* cgr_scope_rev *) subst. case_eq (is_bound_out α); intro Hbound; eexists.
    * split.
       -- eapply lts_res. eapply lts_parR.
          ++ apply shift_transition. exact hlts. exact Hbound.
          ++ reflexivity.
       -- rewrite Hbound. rewrite is_bound_shift in Hbound.
          rewrite Hbound.
          cbn.
          rewrite cgr_scope_rev.
          eapply cgr_res, cgr_fullpar.
          ++ now rewrite Shift_Swap.
          ++ now rewrite <- Swap_Proc_Involutive, Shift_Swap.
    * split.
       -- eapply lts_res.
          apply shift_transition, proj1 in hlts. specialize (hlts Hbound).
          eapply lts_parR. exact hlts. reflexivity.
       -- rewrite Hbound. rewrite is_bound_shift in Hbound.
          rewrite Hbound.
          apply cgr_scope.
- (* lts_choiceL *) inversion hcgr...
  + subst. destruct (IHhlts p1) as [x [Hlts Hcongr]]. reflexivity.
    eexists. split.
    * eapply lts_parL. eapply lts_choiceL. apply Hlts. reflexivity.
    * rewrite Hcongr. replace (α ⇑? (g 𝟘)) with (g 𝟘) by
      (destruct α; try destruct e; reflexivity).
      now rewrite cgr_par_nil_step.
  + subst. inversion hlts; subst...
  + subst. destruct (IHhlts q1) as [x [Hlts Hcongr]]. exact H2.
    eexists. split.
    * eapply lts_choiceL. exact Hlts.
    * exact Hcongr.
- (* lts_choiceR *) inversion hcgr...
  + subst. destruct (IHhlts p2) as [x [Hlts Hcongr]]. reflexivity.
    eexists. split.
    * eapply lts_parL. eapply lts_choiceR. apply Hlts. reflexivity.
    * rewrite Hcongr. replace (α ⇑? (g 𝟘)) with (g 𝟘) by
      (destruct α; try destruct e; reflexivity).
      now rewrite cgr_par_nil_step.
  + subst. inversion hlts.
  + (* cgr_choice_assoc *) subst. inversion hlts; subst...
Qed.

Lemma Congruence_Respects_Transition : forall p q α,
  sc_then_lts p α q -> lts_then_sc p α q.
Proof.
intros p q α (r & Hcongr & Hlts).
revert q Hlts. induction Hcongr.
- intros. apply Congruence_Respects_Transition_Step. eexists; eauto.
- intros q Hlts. destruct (IHHcongr1 _ Hlts) as [p [Hplts Hpcongr]].
  destruct (IHHcongr2 _ Hplts) as [q' [Hlts' Hqcongr]].
  eexists. split.
  * apply Hlts'.
  * now rewrite Hqcongr, Hpcongr.
Qed.

Lemma TransitionUnderScope : forall P Q n α,
  is_bound_out α = false ->
  lts P (nvars n α) Q -> lts (νs n P) α (νs n Q).
Proof.
intros P Q n.
induction n; intros α Hact Transition.
- simpl. exact Transition.
- simpl. apply res_not_bound, IHn. apply Hact. now rewrite <- (is_bound_shift α).
  rewrite <- shift_in_nvars. exact Transition.
Qed.

Lemma tau_helper : forall n, τ = nvars n τ.
Proof.
induction n; simpl.
- reflexivity.
- rewrite <- IHn. reflexivity.
Qed.

(* One side of the Harmony Lemma *)
Lemma Reduction_Implies_TausAndCong : forall P Q, (sts P Q) -> (lts_then_sc P τ Q).
Proof. 
intros P Q Reduction.
destruct (ReductionShape P Q Reduction) as [IH|[IH|[IH|[IH |IH]]]].

(* First case τ by communication *)
- destruct IH as [c [v [P1 [P2 [G1 [G2 [s [n [H1 H2]]]]]]]]].
  destruct (Congruence_Respects_Transition P (νs n (P1 ‖ P2 [⋅;v..] ‖ s)) τ) as [? [H3 H4]].
  + eexists. split.
    * now rewrite H1.
    * apply TransitionUnderScope, lts_parL. reflexivity.
      erewrite <- tau_helper.
      eauto with lts. erewrite <- tau_helper. reflexivity.
  + eexists. split.
    * exact H3.
    * rewrite H4, H2. reflexivity.

(* Second case τ by Tau Action *)
- destruct IH as [P1 [G1 [s [n [H1 H2]]]]].
  destruct (Congruence_Respects_Transition P (νs n (P1 ‖ s)) τ) as [? [H3 H4]].
  + eexists. split.
    * now rewrite H1.
    * apply TransitionUnderScope, lts_parL. reflexivity.
      erewrite <- tau_helper.
      eauto with lts. erewrite <- tau_helper. reflexivity.
  + eexists. split.
    * exact H3.
    * rewrite H4, H2. reflexivity.

(* Third case τ by recursion *)
- destruct IH as [P1 [s [n [H1 H2]]]].
  destruct (Congruence_Respects_Transition P (νs n (P1 [(rec P1)..;⋅] ‖ s)) τ) as [? [H3 H4]].
  + eexists. split.
    * now rewrite H1.
    * apply TransitionUnderScope, lts_parL. reflexivity.
      erewrite <- tau_helper.
      eauto with lts. erewrite <- tau_helper. reflexivity.
  + eexists. split.
    * exact H3.
    * rewrite H4, H2. reflexivity.

(* Fourth case τ by If ONE*)
- destruct IH as [P1 [P0 [s [E [n [H1 [H2 H3]]]]]]].
  destruct (Congruence_Respects_Transition P (νs n (P1 ‖ s)) τ) as [? [H4 H5]].
  + eexists. split.
    * now rewrite H1.
    * apply TransitionUnderScope, lts_parL. reflexivity.
      erewrite <- tau_helper.
      eapply lts_ifOne. exact H3. erewrite <- tau_helper. reflexivity.
  + eexists. split.
    * exact H4.
    * etransitivity. exact H5. now rewrite H2.

(* Fifth case τ by If ZERO*)
- destruct IH as [P1 [P0 [s [E [n [H1 [H2 H3]]]]]]].
  destruct (Congruence_Respects_Transition P (νs n (P0 ‖ s)) τ) as [? [H4 H5]].
  + eexists. split.
    * now rewrite H1.
    * apply TransitionUnderScope, lts_parL. reflexivity.
      erewrite <- tau_helper.
      eapply lts_ifZero. exact H3. erewrite <- tau_helper. reflexivity.
  + eexists. split.
    * exact H4.
    * etransitivity. exact H5. now rewrite H2.
Qed.

(* Strengthened Harmony Lemma (in one side) *)
Lemma Congruence_Simplicity : forall α ,
  (forall P Q, lts P α Q -> sts P Q) -> (forall P Q, lts_then_sc P α Q -> sts P Q).
Proof.
intros ? Hyp ? ? transition_then_congruence_hyp.
destruct transition_then_congruence_hyp as (R & transition & cong).
eapply sts_cong. 
* apply cgr_refl. 
* apply Hyp. exact transition.
* exact cong.
Qed.

Lemma sts_nres: forall P Q, (sts P Q) -> (forall n, sts (νs n P) (νs n Q)).
Proof.
intros P Q H n.
induction n.
- exact H.
- apply sts_res. exact IHn.
Qed.

Lemma Communication_Under_News: forall n1 n2 m c v P1 P2 G1 G2 R1 R2,
(νs n1
  ((nvars n1 c) ! (nvars n2 v) • P1 + G1 ‖ R1)
  ‖
  νs m ((nvars m c) ? P2 + G2 ‖ R2))
  ≡*
  νs n1 (νs m
    ((nvars (m + n1) c ! nvars (m + n2) v • nvars m P1 + nvars m G1
      ‖ nvars (m + n1) c ?
          P2 ⟨ up_ren (upn m (Nat.iter n1 shift)) ⟩ +
          G2 ⟨ upn m (Nat.iter n1 shift) ⟩)
          ‖ (R2 ⟨ upn m (Nat.iter n1 shift) ⟩ ‖ nvars m R1))).
Proof.
  intros.
  rewrite n_extrusion.
  rewrite nvars_νs.
  rewrite cgr_par_com.
  rewrite n_extrusion.
  rewrite Shift_to_Ren_Data.
  cbn. fold ren_proc. fold ren_gproc.
  rewrite renRen_Data, Pointwise_Up_Shift_Sum.
  rewrite Push_nvars_par, Push_nvars_choice, Push_nvars_output.
  repeat rewrite nvars_sum.
  rewrite PeanoNat.Nat.add_comm.
  rewrite <- Shift_to_Ren_Data.
  rewrite cgr_par_com, cgr_par_assoc.
  rewrite (cgr_par_com (nvars m R1)), cgr_par_assoc.
  rewrite cgr_par_assoc.
  reflexivity.
Qed.

Lemma Communicated_Under_News : forall n m v P1 P2 R1 R2,
νs n (νs m
  ((nvars m P1 ‖ P2 ⟨ upRen_Data_Data (upn m (Nat.iter n shift)) ⟩ [⋅; (nvars (m + n) v)..])
    ‖
    (R2 ⟨ upn m (Nat.iter n shift) ⟩ ‖ nvars m R1)))
≡*
νs n (P1 ‖ R1) ‖ νs m (P2 [⋅; (nvars m v)..] ‖ R2).
Proof.
intros.
rewrite cgr_par_assoc, cgr_par_com, cgr_par_assoc_rev.
rewrite n_extrusion. rewrite nvars_νs.
rewrite (cgr_par_com (P1 ‖ R1)). rewrite n_extrusion.
apply (NewsProper _ _ eq_refl).
apply (NewsProper _ _ eq_refl).
rewrite Push_nvars_par. rewrite (cgr_par_assoc ).
change ((P2 [⋅; (nvars n v)..] ‖ R2) ⟨ upn m (Nat.iter n shift) ⟩)
  with ((P2 [⋅; (nvars n v)..] ⟨ upn m (Nat.iter n shift) ⟩ ‖
         R2 ⟨ upn m (Nat.iter n shift) ⟩)).
rewrite (cgr_par_com (nvars m R1)).
apply cgr_par.
apply cgr_par. fold ren_proc.
rewrite PeanoNat.Nat.add_comm.
rewrite Shift_to_Ren_Data.
rewrite <- Pointwise_Up_Shift_Sum.
asimpl. simpl.
rewrite Shift_to_Ren_Data.
apply SubstProper; try reflexivity.
now asimpl.
Qed.

Lemma Taus_Implies_Reduction : forall P Q, (lts P τ Q) -> (sts P Q).
Proof. 
intros P Q Transition.
dependent induction Transition.
- rewrite cgr_choice_nil_rev. apply sts_tau.
- apply sts_recursion.
- apply sts_ifOne. assumption.
- apply sts_ifZero. assumption.
(* lts_comL *)
- destruct (TransitionShapeForFreeOutput p1 p2 c v Transition1)
    as (P1 & G1 & R1 & n & Hcongr1 & Hcongr1' & _).
  destruct (TransitionShapeForInput q1 q2 c v  Transition2)
    as (P2 & G2 & R2 & m & Hcongr2 & Hcongr2' & _).
  rewrite Hcongr1, Hcongr2, Hcongr1', Hcongr2'.
  rewrite Communication_Under_News.
  rewrite <- Communicated_Under_News.
  repeat eapply sts_nres. eapply sts_par. eapply sts_com.
(* lts_comR *)
- destruct (TransitionShapeForFreeOutput p1 p2 c v Transition1)
    as (P1 & G1 & R1 & n & Hcongr1 & Hcongr1' & _).
  destruct (TransitionShapeForInput q1 q2 c v  Transition2)
    as (P2 & G2 & R2 & m & Hcongr2 & Hcongr2' & _).
  rewrite cgr_par_com, (cgr_par_com q2).
  rewrite Hcongr1, Hcongr2, Hcongr1', Hcongr2'.
  rewrite Communication_Under_News.
  rewrite <- Communicated_Under_News.
  repeat eapply sts_nres. eapply sts_par. eapply sts_com.
(* lts_close_l *)
- destruct (TransitionShapeForBoundOutput p1 p2 c Transition1)
    as (n & P1 & Q1 & G1 & Hcongr1 & Hcongr1').
  destruct (TransitionShapeForInput _ q2 _ 0 Transition2)
    as (P2 & G2 & R2 & m & Hcongr2 & Hcongr2' & _).
  rewrite Hcongr1. simpl. rewrite shift_in_nvars.
  rewrite cgr_scope_rev.
  rewrite Hcongr2.
  rewrite Communication_Under_News.
  rewrite Hcongr1', Hcongr2'. rewrite <- Communicated_Under_News.
  apply sts_res. repeat apply sts_nres. eapply sts_par, sts_com.
(* lts_close_r *)
- destruct (TransitionShapeForBoundOutput _ _ c Transition1)
    as (m & P1 & Q1 & G1 & Hcongr1 & Hcongr1').
  destruct (TransitionShapeForInput _ _ _ 0 Transition2)
    as (P2 & G2 & R2 & n & Hcongr2 & Hcongr2' & _).
  rewrite cgr_par_com.
  rewrite Hcongr1. simpl. rewrite shift_in_nvars.
  rewrite cgr_scope_rev.
  rewrite Hcongr2.
  rewrite Communication_Under_News.
  rewrite (cgr_par_com p2). rewrite Hcongr1', Hcongr2'.
  rewrite <- Communicated_Under_News.
  apply sts_res. repeat apply sts_nres. eapply sts_par, sts_com.
(* lts_res *)
- now apply sts_res, IHTransition.
(* lts_parL *)
- now apply sts_par, IHTransition.
(* lts_parR *)
- rewrite cgr_par_com. rewrite (cgr_par_com p).
  now eapply sts_par, IHTransition.
(* lts_choiceL *)
- destruct (TransitionShapeForTauAndGuard (g p1) q) as (P & G & H1 & H2).
  + split. assumption. now exists p1.
  + rewrite H2.
    (* This (and the same below) should just be a "rewrite H1" but my typeclasses
       are likely to blame *)
    eapply sts_Proper. eapply gpr_choice_proper. unfold gpr_cgr. exact H1.
    unfold gpr_cgr. reflexivity. reflexivity.
    rewrite cgr_choice_assoc. apply sts_tau.
(* lts_choiceR *)
- destruct (TransitionShapeForTauAndGuard (g p2) q) as (P & G & H1 & H2).
  + split. assumption. now exists p2.
  + rewrite H2. eapply sts_Proper. rewrite cgr_choice_com.
    eapply gpr_choice_proper. unfold gpr_cgr. exact H1.
    unfold gpr_cgr. reflexivity. reflexivity.
    rewrite cgr_choice_assoc. apply sts_tau.
Qed.

Lemma TausAndCong_Implies_Reduction: forall P Q, (lts_then_sc P τ Q) -> (sts P Q).
Proof.
intros P Q H.
apply Congruence_Simplicity with τ.
- exact Taus_Implies_Reduction.
- exact H.
Qed.

Theorem HarmonyLemma : forall P Q, (lts_then_sc P τ Q) <-> (sts P Q).
Proof.
intros. split.
* apply TausAndCong_Implies_Reduction.
* apply Reduction_Implies_TausAndCong.
Qed.
