(*
   Copyright (c) 2024 Nomadic Labs
   Copyright (c) 2024 Paul Laforgue <paul.laforgue@nomadic-labs.com>
   Copyright (c) 2024 Léo Stefanesco <leo.stefanesco@mpi-sws.org>
   Copyright (c) 2024 Gaëtan Lopez <gaetanlopez.maths@gmail.com>

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

Require Import Coq.Program.Equality Coq.Strings.String.
Require Import RelationClasses.
From stdpp Require base countable finite gmap list gmultiset strings.
Require Import Relations Morphisms.
Require Import Coq.Wellfounded.Inverse_Image.

From Must.pi Require Import Renamings Congruence LTS LTS_Renamings.

Parameter (channel_eq_dec : base.EqDecision Value). (* only here for the classes *)
#[global] Instance channel_eqdecision : base.EqDecision Value. Proof. exact channel_eq_dec. Defined.
Parameter (channel_is_countable : countable.Countable Value). (* only here for the classes *)
#[global] Instance channel_countable : countable.Countable Value. Proof. exact channel_is_countable. Defined.
Parameter (value_eq_dec : base.EqDecision Value). (* only here for the classes *)
#[global] Instance value_eqdecision : base.EqDecision Value. Proof. exact value_eq_dec. Defined.
Parameter (value_is_countable : countable.Countable Value). (* only here for the classes *)
#[global] Instance value_countable : countable.Countable Value. Proof. exact value_is_countable. Defined.

(* State Transition System (STS-reduction), reduction semantic *)
Inductive sts : proc -> proc -> Prop :=
(*The axiomes*)
(* Communication of channels output and input that have the same name *)
| sts_com : forall {c v p1 p2 g1 g2}, 
    sts ((c ! v • p1) + g1 ‖ ((c ? p2) + g2)) (p1 ‖ p2 [⋅; v..])
(* Nothing more , something less *)
| sts_tau : forall {p g}, 
    sts ((t • p) + g) p
(* Recursion *)
| sts_recursion : forall {p}, 
    sts (rec p) (p [(rec p).. ; ⋅])
(*If Yes*)
| sts_ifOne : forall {p q E}, Eval_Eq E = Some true -> 
    sts (If E Then p Else q) p
(*If No*)
| sts_ifZero : forall {p q E}, Eval_Eq E = Some false -> 
    sts (If E Then p Else q) q

(* The left parallele respect the Reduction *)
| sts_par : forall {p1 p2 q}, 
    sts p1 p2 ->
    sts (p1 ‖ q) (p2 ‖ q)

(*The Congruence respects the Reduction *)
| sts_cong : forall {p1 p2 q2 q1},
    p1 ≡* p2 -> sts p2 q2 -> q2 ≡* q1 -> sts p1 q1

| sts_res : forall {p q},
    sts p q -> sts (ν p) (ν q)
.

#[global] Hint Constructors sts:ccs.

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
    + destruct IH as [c [v [P1 [P2 [g1 [g2 [s [n [H1 H2]]]]]]]]].
      left. exists c, v, P1, P2, g1, g2, s, n.
      split; [ now rewrite <- H1 | now rewrite <- H2 ].
    + destruct IH as [P1 [P2 [s [n [H1 H2]]]]].
      right. left. exists P1, P2, s, n.
      split; [ now rewrite <- H1 | now rewrite <- H2 ].
    + destruct IH as [P1 [s [n [H1 H2]]]].
      right. right. left. exists P1, s, n.
      split; [ now rewrite <- H1 | now rewrite <- H2 ].
    + destruct IH as [P1 [P0 [s [E [n [H1 [H2 H3]]]]]]].
      right. right. right. left. exists P1, P0, s, E, n.
      repeat split; now rewrite <- ?H1, <- ?H2.
    + destruct IH as [P1 [P0 [s [E [n [H1 [H2 H3]]]]]]].
      right. right. right. right. exists P1, P0, s, E, n.
      repeat split; now rewrite <- ?H1, <- ?H2.
  - destruct IHTransition as [IH|[IH|[IH|[IH |IH]]]].
    + destruct IH as [c [v [P1 [P2 [g1 [g2 [s [n [H1 H2]]]]]]]]].
      left. exists c, v, P1, P2, g1, g2, s, (S n).
      split; [now rewrite H1 | now rewrite H2 ].
    + destruct IH as [P1 [P2 [s [n [H1 H2]]]]].
      right. left. exists P1, P2, s, (S n).
      split; [ now rewrite H1 | now rewrite H2 ].
    + destruct IH as [P1 [s [n [H1 H2]]]].
      right. right. left. exists P1, s, (S n).
      split; [ now rewrite H1 | now rewrite H2 ].
    + destruct IH as [P1 [P0 [s [E [n [H1 [H2 H3]]]]]]].
      right. right. right. left. exists P1, P0, s, E, (S n).
      repeat split; now rewrite ?H1, ?H2.
    + destruct IH as [P1 [P0 [s [E [n [H1 [H2 H3]]]]]]].
      right. right. right. right. exists P1, P0, s, E, (S n).
      repeat split; now rewrite ?H1, ?H2.
Qed.


Ltac not_a_guard := intro hex; inversion hex as [L absurd_hyp]; inversion absurd_hyp.
Ltac finish_zero H := rewrite H, <- cgr_par_assoc.
Ltac finish_Sn H :=  rewrite H, <- cgr_par_assoc, <- n_extrusion, cgr_scope.

Lemma TransitionShapeForInput : forall P Q c v,
  lts P (ActIn (c ⋉ v)) Q -> exists P1 G R n cn vn,
  (P ≡* νs n ((cn ? P1 + G) ‖ R)) /\
  (Q ≡* νs n (P1[⋅; vn..] ‖ R))   /\
  (ActIn (cn ⋉ vn)) = nvars n (ActIn (c ⋉ v)) /\
  ((exists L, P = g L) -> R = 𝟘 /\ n = 0).
Proof.
intros P Q c v.
intro Transition. dependent induction Transition;
try destruct (IHTransition c v eq_refl) as (P1 & G & R & n & cn & vn & H0 & H1 & H3 & H4).
- exists P, 𝟘, 𝟘, 0, c, v. split; eauto with cgr.
- destruct (IHTransition (⇑ c) (⇑ v) eq_refl) as (P1 & G & R & n & cn & vn & H0 & H1 & H3 & H4).
  exists P1, G, R, (S n), cn, vn. simpl. do 3 (try split).
  + now rewrite H0.
  + now rewrite H1.
  + rewrite shift_in_nvars. now rewrite H3.
  + not_a_guard.
- destruct n.
  + exists P1, G, (R ‖ q), 0, cn, vn. simpl. do 3 (try split).
    * now rewrite H0, <- cgr_par_assoc.
    * now rewrite H1, <- cgr_par_assoc.
    * now rewrite H3.
    * not_a_guard.
  + exists P1, G, (R ‖ nvars n (⇑ q)), (S n), cn, vn. simpl. do 3 (try split).
    * now finish_Sn H0.
    * now finish_Sn H1.
    * now rewrite H3.
    * not_a_guard.
- destruct n; simpl in H0, H1.
  + exists P1, G, (R ‖ p), 0, cn, vn. simpl. do 3 (try split).
    * now rewrite H0, cgr_par_com, cgr_par_assoc.
    * now rewrite H1, cgr_par_com, cgr_par_assoc.
    * now rewrite H3.
    * not_a_guard.
  + exists P1, G, (R ‖ nvars n (⇑ p)), (S n), cn, vn. simpl. do 3 (try split).
    * finish_Sn H0. now rewrite cgr_par_com.
    * finish_Sn H1. now rewrite cgr_par_com.
    * now rewrite H3.
    * not_a_guard.
- destruct n.
  + exists P1, (G + p2), R, 0, cn, vn. simpl. do 3 (try split).
    * destruct H4. { now exists p1. } subst.
      rewrite cgr_par_nil, <- cgr_choice_assoc. apply cgr_choice.
      now rewrite H0, cgr_par_nil.
    * now rewrite H1.
    * now rewrite H3.
    * intro. apply H4. now exists p1.
  + destruct H4 as [_ AbsHyp]. {now exists p1. } inversion AbsHyp.
- destruct n.
  + exists P1, (G + p1), R, 0, cn, vn. simpl. do 3 (try split).
    * destruct H4. { now exists p2. } subst.
      rewrite cgr_par_nil, <- cgr_choice_assoc, cgr_choice_com.
      apply cgr_choice.
      now rewrite H0, cgr_par_nil.
    * now rewrite H1.
    * now rewrite H3.
    * intro. apply H4. now exists p2.
  + destruct H4 as [_ AbsHyp]. {now exists p2. } inversion AbsHyp.
Qed.

Lemma TransitionShapeForFreeOutput : forall P Q c v,
  lts P (FreeOut (c ⋉ v)) Q -> exists P1 G R n cn vn,
  P ≡* νs n (cn ! vn • P1 + G ‖ R) /\
  Q ≡* νs n (P1 ‖ R) /\
  (FreeOut (cn ⋉ vn)) = nvars n (FreeOut (c ⋉ v)) /\
  ((exists L, P = g L) -> (R = 𝟘 /\ n = 0)).
Proof.
intros P Q c v Transition.
dependent induction Transition; try destruct (IHTransition c v eq_refl) as (P1 & G & R & n & cn & vn & H0 & H1 & H3 & H2).
- exists P, 𝟘, 𝟘, 0, c, v. repeat split; eauto with cgr.
- destruct (IHTransition (⇑ c) (⇑ v) eq_refl) as (P1 & G & R & n & cn & vn & H0 & H1 & H3 & H2).
    exists P1, G, R, (S n), cn, vn. do 3 (try split).
  + now rewrite H0.
  + simpl. now rewrite H1.
  + rewrite H3. simpl. now rewrite shift_in_nvars.
  + not_a_guard.
- destruct n.
  + exists P1, G, (R ‖ q), 0, cn, vn. do 3 (try split).
    * now finish_zero H0.
    * now finish_zero H1.
    * now rewrite H3.
    * not_a_guard.
  + exists P1, G, (R ‖ nvars (S n) q), (S n), cn, vn. do 3 (try split).
    * now rewrite H0, n_extrusion, cgr_par_assoc.
    * now rewrite H1, n_extrusion, cgr_par_assoc.
    * now rewrite H3.
    * not_a_guard.
- destruct n; simpl in H0, H1.
  + exists P1, G, (R ‖ p), 0, cn, vn. do 3 (try split).
    * now rewrite H0, cgr_par_com, cgr_par_assoc.
    * now rewrite H1, cgr_par_com, cgr_par_assoc.
    * now rewrite H3.
    * not_a_guard.
  + exists P1, G, (R ‖ nvars n (⇑ p)), (S n), cn, vn. do 3 (try split).
    * simpl. now rewrite H0, <- cgr_par_com, <- cgr_par_assoc, <- n_extrusion, cgr_scope.
    * simpl. now rewrite H1, <- cgr_par_com, <- cgr_par_assoc, <- n_extrusion, cgr_scope.
    * now rewrite H3.
    * not_a_guard.
- destruct n.
  + exists P1, (G + p2), R, 0, cn, vn. do 3 (try split).
    * destruct H2. { now exists p1. } subst.
      rewrite cgr_par_nil, <- cgr_choice_assoc. apply cgr_choice.
      now rewrite H0, cgr_par_nil.
    * now rewrite H1.
    * now rewrite H3.
    * intro. apply H2. now exists p1.
  + destruct H2 as [_ AbsHyp]. {now exists p1. } inversion AbsHyp.
- destruct n.
  + exists P1, (G + p1), R, 0, cn, vn. do 3 (try split).
    * destruct H2. { now exists p2. } subst.
      rewrite cgr_choice_com.
      rewrite cgr_par_nil. rewrite <- cgr_choice_assoc. apply cgr_choice.
      now rewrite H0, cgr_par_nil.
    * now rewrite H1.
    * now rewrite H3.
    * intro. apply H2. now exists p2.
  + destruct H2 as [_ AbsHyp]. {now exists p2. } inversion AbsHyp.
Qed.

Lemma GuardedDoesNoBoundOutput : forall p c q, not (lts (g p) (BoundOut c) q).
Proof. 
intros. intro Transition.
dependent induction Transition; eapply IHTransition; eauto.
Qed.

Lemma TransitionShapeForBoundOutput : forall P Q c,
  lts P (BoundOut c) Q ->
  exists n P' Q',
  (P ≡* νs n (P' ‖ Q')).
  (* /\ (⇑ v) = (var_Data n). *)
  (* I know that: ⇑ LHS = n 
     want to prove: LHS = S n *)
Proof.
intros. dependent induction H.
- destruct (IHlts (⇑ c) eq_refl) as [n (P & Q & Hind1)]. exists (S n), P, Q.
  (* split. *)
  * now rewrite Hind1.
- exists 1, p1, 𝟘.
  (* split. *)
  * now rewrite cgr_par_nil.
  (* * reflexivity. *)
- destruct (IHlts c eq_refl) as (n & P & Q & IH1).
  exists n, P, (Q ‖ nvars n q).
  (* split. *)
  * now rewrite IH1, <- cgr_par_assoc, <- n_extrusion.
  (* * exact IH2. *)
- destruct (IHlts c eq_refl) as (n & P & Q & IH1).
  exists n, (P ‖ nvars n p), Q.
  (* split. *)
  * rewrite IH1. rewrite (cgr_par_com (_‖_)), <- cgr_par_assoc, <- n_extrusion.
    now rewrite (cgr_par_com p), (cgr_par_com Q).
  (* * exact IH2. *)
- apply GuardedDoesNoBoundOutput in H. contradiction.
- apply GuardedDoesNoBoundOutput in H. contradiction.
Qed.

(* Lemma TransitionShapeForOutputSimplified : forall P Q c v, (lts P (FreeOut (c ⋉ v)) Q) 
                                        -> (P ≡* ((c ! v • 𝟘) ‖ Q)).
Proof.
intros. 
destruct (TransitionShapeForOutput P Q c v H) as [G [R [n [H0 H1]]]].

apply transitivity with (((c ! v • 𝟘) ‖ x) ‖ 𝟘). apply transitivity with ((c ! v • 𝟘) ‖ x); eauto.
auto with cgr. apply transitivity with ((c ! v • 𝟘) ‖ (x ‖ 𝟘)). auto with cgr. apply cgr_fullpar. auto with cgr.
eauto with cgr. 
Qed.  *)


(* For the (LTS-transition), the transitable Guards and transitted terms, that performs a Tau ,
are pretty all the same, up to ≡* *)
(* Lemma TransitionShapeForTauAndGuard : forall P V, lts P τ V -> 
exists M, P ≡* (t • V) + M.
Proof.
intros P V (Transition & guard_witness). 
dependent induction Transition.
  - exists P. exists 𝟘. split. 
    * apply cgr_choice_nil_rev.
    * apply cgr_refl.
  - inversion guard_witness as (g & impossible_hyp). inversion impossible_hyp.
  - inversion guard_witness as (g & impossible_hyp). inversion impossible_hyp.
  - inversion guard_witness as (g & impossible_hyp). inversion impossible_hyp.
  - inversion guard_witness as (g & impossible_hyp). inversion impossible_hyp.
  - inversion guard_witness as (g & impossible_hyp). inversion impossible_hyp.
  - inversion guard_witness as (g & impossible_hyp). inversion impossible_hyp.
  - inversion guard_witness as (g & impossible_hyp). inversion impossible_hyp.
  - destruct (IHTransition (reflexivity τ)).
    * exists p1. reflexivity.
    * destruct H. destruct H.  exists x. 
      exists (x0 + p2). split; eauto. apply cgr_trans with (((t • x) + x0) + p2).
      apply cgr_choice. assumption.
      apply cgr_choice_assoc. 
  - destruct (IHTransition (reflexivity τ)).
    * exists p2. reflexivity.
    * destruct H. destruct H.  exists x. 
      exists (x0 + p1). split; eauto. apply cgr_trans with (((t • x) + x0) + p1). apply cgr_trans with (p2 + p1). 
      apply cgr_choice_com. apply cgr_choice. assumption. apply cgr_choice_assoc.
Qed. *)

  
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
Proof with (info_eauto with lts cgr).
unfold sc_step_then_lts, lts_then_sc.
intros p' q α (p & hcgr & hlts).
revert p' hcgr.
dependent induction hlts; intros p'' hcgr.
- (* lts_input *)     inversion hcgr... eexists; rewrite H2...
- (* lts_output *)    inversion hcgr...
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
         replace (q ⟨swap⟩⟨swap⟩ ‖ (⇑ q2) ⟨ swap ⟩) with ((q ⟨ swap ⟩ ‖ (⇑ q2)) ⟨ swap ⟩) by trivial.
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
                 apply Shift_Op_Injective in H.
                 eexists. split.
                 --- eapply lts_comL; [eauto with lts|]. rewrite H. apply Heq2.
                 --- rewrite Heq1. eauto with cgr.
           (* communicate a constant value *)
           ++ replace (FreeOut (((ren1 shift c') ⋉ v))) with
                      (ren1 shift (FreeOut ((c' ⋉ v)))) in H2 by now asimpl.
              replace (cst v) with (ren1 shift (cst v)) in H4 by now asimpl.
              destruct (Invert_Lts_Input_Full _ _ _ _ _ H4) as (d & q' & H & Heq1 & Heq2).
              apply Shift_Op_Injective in H.
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
           apply Shift_Op_Injective in Hc'. subst.
           rewrite <- Hrew in H4. clear Hrew.
           apply swap_transition, proj1 in H4. specialize (H4 eq_refl).
           rewrite Shift_Shift_Swap_pr in H4. cbn in H4.
           rewrite Shift_Shift_Swap_Data in H4.
           change (var_Data 1) with (⇑ (var_Data 0)) in H4.
           destruct (Invert_Lts_Input_Full _ _ _ _ _ H4) as (d & q' & H & Heq1 & Heq2).
           apply Shift_Op_Injective in H. rewrite <- H in Heq2.
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
              replace c with d by now apply Shift_Op_Injective in Hc'.
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


(* Some lemmas for multiple parallele processes to simplify the statements of proof*)
Lemma InversionParallele : forall P Q R S, (P ‖ Q) ‖ (R ‖ S) ≡* (P ‖ R) ‖ (Q ‖ S) . 
Proof. 
intros.
apply transitivity with (((P ‖ Q) ‖ R) ‖ S). apply cgr_par_assoc_rev.
apply transitivity with ((P ‖ (Q ‖ R)) ‖ S). apply cgr_par. apply cgr_par_assoc.
apply transitivity with (((Q ‖ R) ‖ P) ‖ S). apply cgr_par. apply cgr_par_com.
apply transitivity with ((Q ‖ R) ‖ (P ‖ S)). apply cgr_par_assoc.
apply transitivity with ((R ‖ Q) ‖ (P ‖ S)). apply cgr_par. apply cgr_par_com.
apply transitivity with (((R ‖ Q) ‖ P) ‖ S). apply cgr_par_assoc_rev.
apply transitivity with ((P ‖ (R ‖ Q)) ‖ S). apply cgr_par. apply cgr_par_com.
apply transitivity with (((P ‖ R) ‖ Q) ‖ S). apply cgr_par. apply cgr_par_assoc_rev.
apply transitivity with ((P ‖ R) ‖ (Q ‖ S)). apply cgr_par_assoc.
reflexivity. 
Qed.
Lemma InversionParallele2 : forall P Q R S, (P ‖ Q) ‖ (R ‖ S) ≡* (R ‖ P) ‖ (S ‖ Q).
Proof.
intros. 
apply transitivity with ((P ‖ R) ‖ (Q ‖ S)). apply InversionParallele.
apply transitivity with ((R ‖ P) ‖ (Q ‖ S)). apply cgr_par. apply cgr_par_com.
apply transitivity with ((Q ‖ S) ‖ (R ‖ P)). apply cgr_par_com.
apply transitivity with ((S ‖ Q) ‖ (R ‖ P)). apply cgr_par. apply cgr_par_com.
apply cgr_par_com.
Qed.
Lemma InversionParallele3 : forall P Q R S, (P ‖ Q) ‖ (R ‖ S) ≡* (R ‖ Q) ‖ (P ‖ S).
Proof.
intros.
apply transitivity with ((Q ‖ P) ‖ (R ‖ S)). apply cgr_par. apply cgr_par_com.
apply transitivity with ((Q ‖ R) ‖ (P ‖ S)). apply InversionParallele. apply cgr_par. apply cgr_par_com.
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

Lemma Communication_Under_News: forall p1 q1 n m c v P1 P2 G1 G2 R1 R2,
p1 ≡* νs n ((nvars n c) ! (nvars n v) • P1 + G1 ‖ R1) ->
q1 ≡* νs m ((nvars m c) ? P2 + G2 ‖ R2) ->
(p1 ‖ q1) ≡*
νs n
  (νs m
  ((nvars (m + n) c ! nvars (m + n) v • nvars m P1 + nvars m G1
‖ nvars (m + n) c
? P2 ⟨ upRen_Data_Data (upn m (Nat.iter n shift)) ⟩ +
G2 ⟨ upn m (Nat.iter n shift) ⟩)
‖ (R2 ⟨ upn m (Nat.iter n shift) ⟩ ‖ nvars m R1))).
Proof.
intros.
rewrite H, H0.
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
rewrite cgr_par_assoc_rev.
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
with ((P2 [⋅; (nvars n v)..] ⟨ upn m (Nat.iter n shift) ⟩ ‖ R2 ⟨ upn m (Nat.iter n shift) ⟩)).
rewrite (cgr_par_com (nvars m R1)).
apply cgr_par.
apply cgr_par. fold ren_proc.
(* rewrite <- nvars_sum. *)
rewrite PeanoNat.Nat.add_comm.
rewrite Shift_to_Ren_Data.
rewrite <- Pointwise_Up_Shift_Sum.
asimpl. simpl.
apply SubstProper.
- reflexivity.
- intro k.
   rewrite Shift_to_Ren_Data. now asimpl.
- reflexivity.
Qed.
(* replace (P2 ⟨ upRen_Data_Data (upn m (Nat.iter n shift)) ⟩ [⋅; (nvars (m + n) v)..]
‖ R2 ⟨ upn m (Nat.iter n shift) ⟩) with
(P2 ⟨ upRen_Data_Data (upn m (Nat.iter n shift)) ⟩ [⋅; (nvars (m + n) v)..]
‖ R2 ⟨ upn m (Nat.iter n shift) ⟩). admit. *)


Lemma Taus_Implies_Reduction : forall P Q, (lts P τ Q) -> (sts P Q).
Proof. 
intros P Q Transition.
dependent induction Transition.
- eapply sts_cong. instantiate (1:=  ((t • P) + 𝟘)). apply cgr_choice_nil_rev. eapply sts_tau. reflexivity.
- apply sts_recursion.
- apply sts_ifOne. assumption.
- apply sts_ifZero. assumption.
- destruct (TransitionShapeForFreeOutput p1 p2 c v Transition1) as (P1 & G1 & R1 & n & c1' & v1' & Hcongr1 & Hcongr1' & Hact1 & Hguard1).
  destruct (TransitionShapeForInput q1 q2 c v  Transition2) as (P2 & G2 & R2 & m & c2' & v2' & Hcongr2 & Hcongr2' & Hact2 & Hguard2).
  rewrite Push_nvars_ActIn in Hact2.
  inversion Hact2.
  rewrite Push_nvars_FreeOut in Hact1.
  inversion Hact1.
  rewrite H0 in Hcongr2.
  rewrite H2, H3 in Hcongr1.
  rewrite H1 in Hcongr2'.
  eapply sts_cong.
  + apply Communication_Under_News. exact Hcongr1. exact Hcongr2.
  + repeat eapply sts_nres. eapply sts_par. eapply sts_com.
  + rewrite Hcongr1', Hcongr2'. apply Communicated_Under_News.
- destruct (TransitionShapeForFreeOutput p1 p2 c v Transition1) as (P1 & G1 & R1 & n & c1' & v1' & Hcongr1 & Hcongr1' & Hact1 & Hguard1).
  destruct (TransitionShapeForInput q1 q2 c v  Transition2) as (P2 & G2 & R2 & m & c2' & v2' & Hcongr2 & Hcongr2' & Hact2 & Hguard2).
  rewrite Push_nvars_ActIn in Hact2.
  inversion Hact2.
  rewrite Push_nvars_FreeOut in Hact1.
  inversion Hact1.
  rewrite H0 in Hcongr2.
  rewrite H2, H3 in Hcongr1.
  rewrite H1 in Hcongr2'.
  eapply sts_cong.
  + rewrite cgr_par_com.
    apply Communication_Under_News. exact Hcongr1. exact Hcongr2.
  + repeat eapply sts_nres. eapply sts_par. eapply sts_com.
  + rewrite (cgr_par_com q2). rewrite Hcongr1', Hcongr2'. apply Communicated_Under_News.
- destruct (TransitionShapeForBoundOutput p1 p2 c Transition1) as (n & P1 & Hguard1).
- destruct (TransitionShapeForBoundOutput p1 p2 c v Transition1) as [G [R [n [H1 H2]]]].
  destruct (TransitionShapeForInput q1 q2 c v  Transition2) as [P1 [G0 [S [m [H3 [H4 H5]]]]]].
  admit.
- now apply sts_res, IHTransition.
- now apply sts_par, IHTransition.
- eapply sts_cong.
  + apply cgr_par_com.
  + now eapply sts_par, IHTransition.
  + apply cgr_par_com.
- destruct (TransitionShapeForTauAndGuard (g p1) q). split. assumption. exists p1. reflexivity.
  decompose record H.
  eapply sts_cong. instantiate (1:= ((t • x) + (x0 + p2))).
  apply transitivity with (g (((t • x) + x0) + p2)). apply cgr_choice. assumption. apply cgr_choice_assoc.
  instantiate (1:= x). apply sts_tau. symmetry. assumption.
- destruct (TransitionShapeForTauAndGuard (g p2) q). split. assumption. exists p2. reflexivity.
  decompose record H. eapply sts_cong. instantiate (1:= ((t • x) + (x0 + p1))).
  apply transitivity with (g (((t • x) + x0 ) + p1)). apply transitivity with (g (p2 + p1)). apply cgr_choice_com.
  apply cgr_choice. assumption. apply cgr_choice_assoc. instantiate (1:= x). apply sts_tau.
  symmetry. assumption.
Qed.

(* One side of the Harmony Lemma*)
Lemma TausAndCong_Implies_Reduction: forall P Q, (lts_then_sc P τ Q) -> (sts P Q).
Proof.
intros P Q H.
apply Congruence_Simplicity with τ. exact Taus_Implies_Reduction. exact H.
Qed.

Theorem HarmonyLemmaForCCSWithValuePassing : forall P Q, (lts_then_sc P τ Q) <-> (sts P Q).
Proof.
intros. split.
* apply TausAndCong_Implies_Reduction.
* apply Reduction_Implies_TausAndCong.
Qed.




(*
(*The next work is for making 'bvar' always relates to an input*) 

(* Definition for Well Abstracted bvariable *)
Inductive Well_Defined_Data : nat -> Data -> Prop :=
| bvar_is_defined_up_to_k: forall k x, (x < k) -> Well_Defined_Data k (bvar x)
| cst_is_always_defined : forall k v, Well_Defined_Data k (cst v).

Inductive Well_Defined_Condition : nat -> Equation Data -> Prop :=
| tt_is_WD : forall k, Well_Defined_Condition k tt
| ff_is_WD : forall k, Well_Defined_Condition k ff
| Inequality_is_WD : forall k x y, Well_Defined_Data k x -> Well_Defined_Data k y -> Well_Defined_Condition k (x ⩽ y)
| Or_is_WD : forall k e e', Well_Defined_Condition k e -> Well_Defined_Condition k e' -> Well_Defined_Condition k (e ∨ e')
| Not_is_WD : forall k e, Well_Defined_Condition k e -> Well_Defined_Condition k (non e).

(* the 'bvar' always relates to a input *)
Inductive Well_Defined_Input_in : nat -> proc -> Prop :=
| WD_par : forall k p1 p2, Well_Defined_Input_in k p1 -> Well_Defined_Input_in k p2 
                -> Well_Defined_Input_in k (p1 ‖ p2)
| WD_var : forall k i, Well_Defined_Input_in k (pr_var i)
| WD_rec : forall k x p1, Well_Defined_Input_in k p1 -> Well_Defined_Input_in k (rec x • p1)
| WD_if_then_else : forall k p1 p2 C, Well_Defined_Condition k C -> Well_Defined_Input_in k p1 
                    -> Well_Defined_Input_in k p2 
                        -> Well_Defined_Input_in k (If C Then p1 Else p2)
| WD_success : forall k, Well_Defined_Input_in k (①)
| WD_nil : forall k, Well_Defined_Input_in k (𝟘)
| WD_input : forall k c p, Well_Defined_Input_in (S k) p
                  -> Well_Defined_Input_in k (c ? p)
| WD_output : forall k c v, Well_Defined_Data k v 
                  -> Well_Defined_Input_in k (c ! v • 𝟘)
| WD_tau : forall k p,  Well_Defined_Input_in k p -> Well_Defined_Input_in k (t • p)
| WD_choice : forall k p1 p2,  Well_Defined_Input_in k (g p1) ->  Well_Defined_Input_in k (g p2) 
              ->  Well_Defined_Input_in k (p1 + p2).

#[global] Hint Constructors Well_Defined_Input_in:ccs.

Lemma Inequation_k_data : forall k d, Well_Defined_Data k d -> Well_Defined_Data (S k) d.
Proof.
intros. dependent destruction d. constructor. dependent destruction H. constructor. auto with arith.
Qed.

Lemma Inequation_k_equation : forall k c, Well_Defined_Condition k c -> Well_Defined_Condition (S k) c.
Proof.
intros. dependent induction c.
* constructor.
* constructor.
* destruct a; destruct a0.
  - constructor; constructor.
  - dependent destruction H. constructor. constructor. apply Inequation_k_data. assumption.
  - dependent destruction H. constructor. apply Inequation_k_data. assumption. constructor. 
  - dependent destruction H. constructor; apply Inequation_k_data; assumption.
* dependent destruction H. constructor. apply IHc1. assumption. apply IHc2. assumption.
* dependent destruction H. constructor. apply IHc. assumption.
Qed.

Lemma Inequation_k_proc : forall k p, Well_Defined_Input_in k p -> Well_Defined_Input_in (S k) p.
Proof.
intros. revert H. revert k.
induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct p.
- intros. dependent destruction H. constructor; apply Hp; simpl; auto with arith; assumption.
- intros. constructor.
- intros. constructor. apply Hp. simpl; auto with arith. dependent destruction H. assumption.
- intros. dependent destruction H. constructor. 
  ** apply Inequation_k_equation. assumption.
  ** apply Hp. simpl; auto with arith. assumption.
  ** apply Hp. simpl; auto with arith. assumption.
- intros. constructor. dependent destruction H. apply Inequation_k_data. assumption.
- destruct g0.
  ** intros. constructor.
  ** intros. constructor.
  ** intros. constructor. apply Hp. simpl; auto with arith. dependent destruction H. assumption.
  ** intros. constructor. apply Hp. simpl; auto with arith. dependent destruction H. assumption.
  ** intros. dependent destruction H. constructor.
    -- apply Hp. simpl; auto with arith. assumption.
    -- apply Hp. simpl; auto with arith. assumption.
Qed.


Lemma Congruence_step_Respects_WD_k : forall p q k, Well_Defined_Input_in k p -> p ≡ q -> Well_Defined_Input_in k q. 
Proof.
intros. revert H. revert k. dependent induction H0 ; intros.
* auto.
* dependent destruction H; auto.
* constructor; auto. constructor.
* dependent destruction H;constructor; auto.
* dependent destruction H. dependent destruction H. constructor. auto. constructor;auto.
* dependent destruction H. dependent destruction H0. constructor;auto. constructor; auto.
* dependent destruction H; auto.
* constructor; auto. constructor.
* dependent destruction H. constructor; auto. 
* dependent destruction H. dependent destruction H. constructor; auto. constructor; auto.
* dependent destruction H. dependent destruction H0. constructor; auto. constructor; auto.
* dependent destruction H. constructor. apply IHcgr_step. auto.
* dependent destruction H. constructor. apply IHcgr_step. auto.
* constructor. dependent destruction H. apply IHcgr_step. auto.
* dependent destruction H. constructor; auto.
* dependent destruction H. constructor; auto.
* dependent destruction H. constructor; auto.
* dependent destruction H. constructor; auto.
Qed.

Lemma Congruence_Respects_WD_k : forall p q k, Well_Defined_Input_in k p -> p ≡* q -> Well_Defined_Input_in k q. 
Proof.
intros. dependent induction H0.
- apply Congruence_step_Respects_WD_k with x; auto.
- eauto.
Qed.

Lemma Congruence_Respects_WD : forall p q, Well_Defined_Input_in 0 p -> p ≡* q -> Well_Defined_Input_in 0 q.
Proof.
intros. eapply Congruence_Respects_WD_k; eauto.
Qed.

Lemma NotK : forall n k,  n < S k -> n ≠ k -> n < k.
Proof.
intros. assert (n ≤ k). auto with arith. destruct H1. exfalso. apply H0. reflexivity. auto with arith.
Qed.

Lemma ForData : forall k v d, Well_Defined_Data (S k) d -> Well_Defined_Data k (subst_Data k (cst v) d).
Proof.
intros. revert H. revert v. revert k. dependent induction d.
* intros. simpl. constructor.
* intros. simpl. destruct (decide (n = k )).
  - constructor. 
  - dependent destruction H. constructor. apply NotK; assumption.
Qed.

Lemma ForEquation : forall k v e, Well_Defined_Condition (S k) e 
                -> Well_Defined_Condition k (subst_in_Equation k (cst v) e).
Proof.
intros. revert H. revert v. revert k. 
- dependent induction e. 
-- intros. simpl. constructor.
-- intros. simpl. constructor.
-- dependent induction a; dependent induction a0.
  * intros. simpl. constructor; constructor.
  * intros. simpl. destruct (decide (n = k)).
    ** constructor; constructor.
    ** constructor. constructor. dependent destruction H. dependent destruction H0. constructor. apply NotK; assumption.
  * intros. simpl. constructor; try constructor. destruct (decide (n = k)). constructor. dependent destruction H.
    dependent destruction H. constructor. apply NotK; assumption.
  * intros. simpl. constructor.
    ** destruct (decide (n = k)); try constructor. dependent destruction H. dependent destruction H. 
    apply NotK; assumption.
    ** destruct (decide (n0 = k)); try constructor. dependent destruction H. dependent destruction H0. 
    apply NotK; assumption.
-- intros. dependent destruction H. simpl. constructor. apply IHe1. assumption. apply IHe2. assumption.
-- intros. dependent destruction H. simpl. constructor. apply IHe. assumption.
Qed.

Lemma WD_and_subst_rec : forall k p v, Well_Defined_Input_in (S k) p -> Well_Defined_Input_in k (subst_in_proc k (cst v) p).
Proof.
intros. revert v. revert H. revert k.
induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct p.
* intros. dependent destruction H. simpl. constructor. 
  - apply Hp. simpl. auto with arith. assumption.
  - apply Hp. simpl. auto with arith. assumption.
* intros. simpl. constructor.
* intros. simpl. dependent destruction H. constructor. apply Hp. simpl. auto with arith. assumption.
* intros. simpl. dependent destruction H. constructor.
  - apply ForEquation. assumption.
  - apply Hp. simpl. auto with arith. assumption.
  - apply Hp. simpl. auto with arith. assumption.
* intros. simpl. dependent destruction H. constructor. apply ForData. assumption.
* destruct g0.
  - intros. simpl. constructor.
  - intros. simpl. constructor.
  - intros. simpl. constructor. apply Hp. simpl. auto. dependent destruction H. assumption.
  - intros. simpl. constructor. apply Hp. simpl. auto. dependent destruction H. assumption.
  - intros. simpl. dependent destruction H. constructor.
    -- assert (Well_Defined_Input_in k (subst_in_proc k v (g0_1))). apply Hp.
      simpl.  auto with arith. assumption. assumption.
    -- assert (Well_Defined_Input_in k (subst_in_proc k v (g0_2))). apply Hp.
      simpl.  auto with arith. assumption. assumption.
Qed.

Lemma WD_data_and_NewVar : forall d k i, Well_Defined_Data (k + i) d 
                          -> Well_Defined_Data (S (k + i)) (NewVar_in_Data i d).
Proof.
dependent induction d; intros.
- simpl. constructor.
- simpl. destruct (decide (i < S n)).
  * constructor. simpl. dependent destruction H. auto with arith.
  * constructor. dependent destruction H. apply transitivity with i.
    apply Nat.nlt_succ_r. assumption.
    auto with arith. 
Qed.

Lemma WD_eq_and_NewVar : forall e k i, Well_Defined_Condition (k + i) e 
                          -> Well_Defined_Condition (S (k + i)) (NewVar_in_Equation i e).
Proof.
intro. dependent induction e; intros; simpl. 
* constructor.
* constructor.
* dependent destruction H.  constructor; apply WD_data_and_NewVar ; assumption.
* dependent destruction H. constructor. 
  - apply IHe1. assumption.
  - apply IHe2. assumption.
* dependent destruction H. constructor. apply IHe. assumption.
Qed.

Lemma WD_and_NewVar : forall k i p, Well_Defined_Input_in (k + i) p -> Well_Defined_Input_in ((S k) + i) (NewVar i p).
Proof.
intros. revert H. revert k i.
induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct p; intros; simpl.
* dependent destruction H. constructor.
   - apply Hp. simpl. auto with arith. assumption.
   - apply Hp. simpl. auto with arith. assumption.
* constructor.
* constructor. dependent destruction H. apply Hp. simpl. auto with arith. assumption.
* dependent destruction H. constructor. apply  WD_eq_and_NewVar. assumption.
   - apply Hp. simpl. auto with arith. assumption.
   - apply Hp. simpl. auto with arith. assumption.
* constructor. dependent destruction H. apply WD_data_and_NewVar. assumption.
* destruct g0; intros; simpl.
  - constructor.
  - constructor.
  - dependent destruction H. constructor. 
    assert (S (S (k + i)) = (S k + S i)%nat). simpl. auto with arith.
    rewrite H0. apply Hp. simpl. auto with arith. assert ((k + S i)%nat = S (k + i)).  auto with arith. rewrite H1. assumption.
  - constructor. apply Hp. simpl. auto. dependent destruction H. assumption.
  - dependent destruction H. constructor.
    -- assert (S (k + i) = (S k + i)%nat). auto with arith. rewrite H1.
       assert (Well_Defined_Input_in (S k + i) (NewVar i (g g0_1))).
       apply Hp. simpl. auto with arith. assumption. assumption.
    -- assert (S (k + i) = (S k + i)%nat). auto with arith. rewrite H1.
       assert (Well_Defined_Input_in (S k + i) (NewVar i (g g0_2))).
       apply Hp. simpl. auto with arith. assumption. assumption.
Qed.

Lemma ForRecursionSanity : forall p' p x k, Well_Defined_Input_in k p' -> Well_Defined_Input_in k p 
            -> Well_Defined_Input_in k (pr_subst x p' p).
Proof.
intros. revert H. revert H0. revert k. revert x. revert p.
induction p' as (p' & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct p'.
* intros. simpl. constructor. 
  ** apply Hp. simpl. auto with arith. assumption. dependent destruction H. assumption.
  ** apply Hp. simpl. auto with arith. assumption. dependent destruction H. assumption.
* intros. simpl. destruct (decide (x = n)). assumption. assumption.
* intros. simpl. destruct (decide (x=n)). 
  ** dependent destruction H. assumption.
  ** constructor. apply Hp. simpl; auto with arith. assumption. dependent destruction H. assumption.
* intros. simpl. dependent destruction H. constructor.
  ** assumption.
  ** apply Hp. simpl; auto with arith. assumption. assumption.
  ** apply Hp. simpl; auto with arith. assumption. assumption.
* intros. simpl. assumption.
* destruct g0. 
  ** intros. simpl. constructor.
  ** intros. simpl. constructor.
  ** intros. simpl. constructor. dependent destruction H. apply Hp. 
    - simpl;auto with arith.
    - assert ((S k) = ((S k) + 0)%nat). auto with arith. rewrite H1. apply (WD_and_NewVar k 0 p0).
      assert (k = (k + 0)%nat). auto with arith. rewrite <-H2. assumption. 
    - assumption.
  ** intros. simpl. constructor. apply Hp.
    - simpl; auto with arith.
    - assumption.
    - dependent destruction H. assumption.
  ** intros. simpl. dependent destruction H. constructor.
    - assert (Well_Defined_Input_in k (pr_subst x (g g0_1) p)). apply Hp. simpl; auto with arith. assumption.
      assumption. assumption.
    - assert (Well_Defined_Input_in k (pr_subst x (g g0_2) p)). apply Hp. simpl; auto with arith. assumption.
      assumption. assumption.
Qed.

Lemma RecursionOverReduction_is_WD : forall k x p, Well_Defined_Input_in k (rec x • p) 
          -> Well_Defined_Input_in k (pr_subst x p (rec x • p)).
Proof.
intros. apply ForRecursionSanity. dependent destruction H. assumption. assumption.
Qed.

Lemma Well_Def_Data_Is_a_value : forall d, Well_Defined_Data 0 d <-> exists v, d = cst v.
Proof.
intros. split. 
- intro. dependent destruction H. exfalso. dependent induction H. exists v. reflexivity.
- intros. destruct H. subst. constructor.
Qed.

Lemma STS_Respects_WD : forall p q, Well_Defined_Input_in 0 p -> sts p q -> Well_Defined_Input_in 0 q.
Proof.
intros. revert H. rename H0 into Reduction. dependent induction Reduction.
* intros. constructor.
  - constructor.
  - dependent destruction H. dependent destruction H0. dependent destruction H0_. 
    dependent destruction H. apply Well_Def_Data_Is_a_value in H. destruct H. subst.  apply WD_and_subst_rec. assumption. 
* intros. dependent destruction H. dependent destruction H. assumption.
* intros. dependent destruction H. apply RecursionOverReduction_is_WD. constructor. assumption.
* intros. dependent destruction H0. assumption.
* intros. dependent destruction H0. assumption.
* intros. dependent destruction H. constructor. apply IHReduction. assumption. assumption.
* intros. apply Congruence_Respects_WD with q2. apply IHReduction. apply Congruence_Respects_WD with p1. 
  assumption. assumption. assumption.
Qed.

Inductive Well_Defined_Action: (Act TypeOfActions) -> Prop :=
| ActionOuput_with_value_is_always_defined : forall c v, Well_Defined_Action (ActOut  (c ⋉ (cst v)))
| ActionInput_with_value_is_always_defined : forall c v, Well_Defined_Action (ActIn  (c ⋉ (cst v)))
| Tau_is_always_defined : Well_Defined_Action (τ).

Lemma Output_are_good : forall p1 p2 c d, Well_Defined_Input_in 0 p1 -> lts p1 (ActOut (c ⋉ d)) p2 
      -> exists v, d = cst v.
Proof.
intros. dependent induction H0. dependent destruction H. apply Well_Def_Data_Is_a_value in H. destruct H.
subst. exists x. reflexivity.
- dependent destruction H. eapply IHlts with c. assumption. reflexivity.
- dependent destruction H. eapply IHlts with c. assumption. reflexivity.
- dependent destruction H. eapply IHlts with c. assumption. reflexivity.
- dependent destruction H. eapply IHlts with c. assumption. reflexivity.
Qed.

Lemma LTS_Respects_WD : forall p q α, Well_Defined_Input_in 0 p -> Well_Defined_Action α -> lts p α q 
            ->  Well_Defined_Input_in 0 q.
Proof.
intros. revert H. revert H0. rename H1 into Transition. dependent induction Transition.
* intros. dependent destruction H0.  apply WD_and_subst_rec. dependent destruction H. assumption.
* intros. constructor.
* intros. dependent destruction H. assumption.
* intros. apply ForRecursionSanity. dependent destruction H. assumption. assumption.
* intros. dependent destruction H1. assumption.
* intros. dependent destruction H1. assumption.
* intros. dependent destruction H. constructor. 
  ** apply IHTransition1. assert (exists v', v = cst v'). eapply Output_are_good. exact H.
     exact Transition1. destruct H2. subst. constructor. assumption.
  ** apply IHTransition2. assert (exists v', v = cst v'). eapply Output_are_good. exact H.
     exact Transition1. destruct H2. subst. constructor. assumption.
* intros. dependent destruction H. constructor.
  ** apply IHTransition2. assert (exists v', v = cst v'). eapply Output_are_good. exact H1.
     exact Transition1. destruct H2. subst. constructor. assumption.
  ** apply IHTransition1. assert (exists v', v = cst v'). eapply Output_are_good. exact H1.
     exact Transition1. destruct H2. subst. constructor. assumption.
* intros. dependent destruction H. constructor. apply IHTransition. assumption. assumption. assumption.
* intros. dependent destruction H. constructor. assumption. apply IHTransition. assumption. assumption.
* intros. dependent destruction H. apply IHTransition. assumption. assumption.
* intros. dependent destruction H. apply IHTransition. assumption. assumption.
Qed.


(* Lemma to simplify the Data in Value for a transition *)
Lemma OutputWithValue : forall p q a, lts p (ActOut a) q -> exists c d, a = c ⋉ d.
Proof.
intros. dependent destruction a. dependent induction H.
- exists c. exists d. reflexivity.
- destruct (IHlts c d). reflexivity. destruct H0. dependent destruction H0. exists x. exists x0. reflexivity.
- destruct (IHlts c d). reflexivity. destruct H0. dependent destruction H0. exists x. exists x0. reflexivity.
- destruct (IHlts c d). reflexivity. destruct H0. dependent destruction H0. exists x. exists x0. reflexivity.
- destruct (IHlts c d). reflexivity. destruct H0. dependent destruction H0. exists x. exists x0. reflexivity.
Qed.

Lemma InputWithValue : forall p q a, lts p (ActIn a) q -> exists c v, a = c ⋉ v.
Proof.
intros. dependent destruction a. dependent induction H.
- exists c. exists d. reflexivity.
- destruct (IHlts c d). reflexivity. destruct H0. dependent destruction H0. exists x. exists x0. reflexivity.
- destruct (IHlts c d). reflexivity. destruct H0. dependent destruction H0. exists x. exists x0. reflexivity.
- destruct (IHlts c d). reflexivity. destruct H0. dependent destruction H0. exists x. exists x0. reflexivity.
- destruct (IHlts c d). reflexivity. destruct H0. dependent destruction H0. exists x. exists x0. reflexivity.
Qed.


(* Peter Selinger Axioms (OutBuffered Agent with FeedBack) up to structural equivalence*)

Lemma OBA_with_FB_First_Axiom : forall p q r a α,
  lts p (ActOut a) q -> lts q α r ->
  (exists r', lts p α r' /\ lts_then_sc r' (ActOut a) r). (* output-commutativity *)
Proof.
intros. assert (lts p (ActOut a) q). assumption. apply OutputWithValue in H1.
decompose record H1. subst. eapply TransitionShapeForOutputSimplified in H.
eapply lts_parR in H0. instantiate (1 := (x ! x0 • 𝟘)) in H0.
edestruct (Congruence_Respects_Transition p ((x ! x0 • 𝟘) ‖ r) α).
exists ((x ! x0 • 𝟘) ‖ q). split; assumption. destruct H2.
assert (lts ((x ! x0 • 𝟘) ‖ r) (ActOut (x ⋉ x0)) (𝟘 ‖ r)). constructor. constructor.
edestruct (Congruence_Respects_Transition x1 (𝟘 ‖ r) (ActOut (x ⋉ x0))).
exists ((x ! x0 • 𝟘) ‖ r). split ; assumption. destruct H5.
assert (x2 ≡* r). eauto with cgr.
exists x1. split. assumption. exists x2. split; assumption.
Qed.

Lemma OBA_with_FB_Second_Axiom : forall p q1 q2 a μ, 
  μ ≠ (ActOut a) ->
  lts p (ActOut a) q1 ->
  lts p (ActExt μ) q2 ->
  ∃ r : proc, lts q1 (ActExt μ) r ∧ lts_then_sc q2 (ActOut a) r. (* output-confluence  *)
Proof.
intros. assert (lts p (ActOut a) q1). assumption. apply OutputWithValue in H2.
decompose record H2. subst. rename x into c. rename x0 into v.
eapply TransitionShapeForOutputSimplified in H0.
edestruct (Congruence_Respects_Transition ((c ! v • 𝟘) ‖ q1) q2 μ).
exists p. split. symmetry. assumption. assumption.
destruct H3. inversion H3; subst.
inversion H9. subst. now destruct H. 
exists q3. split. assumption.
assert (lts ((c ! v • 𝟘) ‖ q3) (ActOut (c ⋉ v)) (𝟘 ‖ q3)). constructor. constructor.
edestruct (Congruence_Respects_Transition q2 (𝟘 ‖ q3) (ActOut (c ⋉ v))).
exists ((c ! v • 𝟘) ‖ q3). split. eauto with cgr. assumption. destruct H6. exists x. split. assumption.
eauto with cgr.
Qed.

Lemma OBA_with_FB_Third_Axiom : forall p1 p2 p3 a, 
            lts p1 (ActOut a) p2 → lts p1 (ActOut a) p3 -> p2 ≡* p3. (* output-determinacy *)
Proof.
intros. assert (lts p1 (ActOut a) p2). assumption. apply OutputWithValue in H1.
decompose record H1. subst. rename x into c. rename x0 into v.
revert H0. revert p3. dependent induction H.
- intros. inversion H0. subst. eauto with cgr.
- intros. inversion H0;subst. 
  * apply cgr_fullpar. eapply IHlts. eauto. eauto. assumption. eauto with cgr.
  * apply TransitionShapeForOutputSimplified in H.
    apply TransitionShapeForOutputSimplified in H6.
    apply transitivity with (p2 ‖ ((c ! v • 𝟘) ‖ q2)). eauto with cgr. 
    apply transitivity with ((p2 ‖ (c ! v • 𝟘)) ‖ q2). eauto with cgr. apply cgr_par.
    eauto with cgr.
- intros. inversion H0 ; subst.
  * apply TransitionShapeForOutputSimplified in H.
    apply TransitionShapeForOutputSimplified in H6.
    apply transitivity with (((c ! v • 𝟘) ‖ p2) ‖ q2). eauto with cgr.
    apply transitivity with (( p2 ‖ (c ! v • 𝟘)) ‖ q2). eauto with cgr.
    apply transitivity with ( p2 ‖ ((c ! v • 𝟘) ‖ q2)). eauto with cgr. apply cgr_fullpar. reflexivity.
    eauto with cgr.
  * apply cgr_fullpar. reflexivity. eapply IHlts. eauto. eauto. assumption.
- intros. exfalso. eapply guarded_does_no_output. eassumption.
- intros. exfalso. eapply guarded_does_no_output. eassumption.
Qed.

Lemma OBA_with_FB_Fourth_Axiom : forall p1 p2 p3 a, lts p1 (ActOut a) p2 -> lts p2 (ActIn a) p3 
                              -> lts_then_sc p1 τ p3. (* feedback *)
Proof.
intros. assert (lts p1 (ActOut a) p2). assumption. apply OutputWithValue in H1.
decompose record H1. subst. rename x into c. rename x0 into v.
eapply TransitionShapeForOutputSimplified in H.
assert (lts (c ! v • 𝟘) (ActOut (c ⋉ v)) 𝟘). constructor.
assert (lts ((c ! v • 𝟘) ‖ p2) τ  (𝟘 ‖ p3)). econstructor; eassumption.
edestruct (Congruence_Respects_Transition p1 (𝟘 ‖ p3) τ). exists ((c ! v • 𝟘) ‖ p2).
split; assumption. destruct H4. exists x. split. assumption. eauto with cgr.
Qed.

Lemma OBA_with_FB_Fifth_Axiom : forall p q1 q2 a,
  lts p (ActOut a) q1 -> lts p τ q2 ->
  (∃ q : proc, lts q1 τ q /\ lts_then_sc q2 (ActOut a) q) \/ lts_then_sc q1 (ActIn a) q2. (* output-tau  *)
Proof.
intros. assert (lts p (ActOut a) q1). assumption. apply OutputWithValue in H1.
decompose record H1. subst. rename x into c. rename x0 into v.
eapply TransitionShapeForOutputSimplified in H.
edestruct (Congruence_Respects_Transition ((c ! v • 𝟘) ‖ q1) q2 τ). exists p. split. eauto with cgr. assumption.
destruct H2. dependent induction H2.
- inversion H2_; subst. right. exists q0. split. assumption. eauto with cgr. 
- inversion H2_0.
- inversion H2.
- left. exists q0. split. assumption. 
  assert (lts ((c ! v • 𝟘) ‖ q0) (ActOut (c ⋉ v)) (𝟘 ‖ q0)). constructor. constructor.
  edestruct (Congruence_Respects_Transition q2 (𝟘 ‖ q0) (ActOut (c ⋉ v))). exists ((c ! v • 𝟘) ‖ q0).
  split. eauto with cgr. assumption. destruct H5. exists x. split. assumption. eauto with cgr.
Qed.


Lemma ExtraAxiom : forall p1 p2 q1 q2 a,
      lts p1 (ActOut a) q1 -> lts p2 (ActOut a) q2 -> q1 ≡* q2 -> p1 ≡* p2.
Proof.
intros. assert (lts p1 (ActOut a) q1). assumption. apply OutputWithValue in H2.
decompose record H2. subst. rename x into c. rename x0 into v.
eapply TransitionShapeForOutputSimplified in H0.
eapply TransitionShapeForOutputSimplified in H.
apply transitivity with ((c ! v • 𝟘) ‖ q1). assumption.
apply transitivity with ((c ! v • 𝟘) ‖ q2). eauto with cgr. eauto with cgr.
Qed. 

Lemma Data_dec : forall (x y : Data) , {x = y} + {x <> y}.
Proof.
decide equality. 
* destruct (decide(v = v0)). left. assumption. right. assumption.
* destruct (decide (n = n0)). left. assumption. right. assumption.
Qed.

#[global] Instance data_eqdecision : EqDecision Data. by exact Data_dec . Defined.

Definition encode_data (D : Data) : gen_tree (nat + Value) :=
match D with
  | cst v => GenLeaf (inr v)
  | bvar i => GenLeaf (inl i)
end.

Definition decode_data (tree : gen_tree (nat + Value)) : Data :=
match tree with
  | GenLeaf (inr v) => cst v
  | GenLeaf (inl i) => bvar i
  | _ => bvar 0
end.

Lemma encode_decide_datas d : decode_data (encode_data d) = d.
Proof. case d. 
* intros. simpl. reflexivity.
* intros. simpl. reflexivity.
Qed.

#[global] Instance data_countable : Countable Data.
Proof.
  refine (inj_countable' encode_data decode_data _).
  apply encode_decide_datas.
Qed.


Fixpoint encode_equation (E : Equation Data) : gen_tree (nat + Data) :=
match E with
  | tt => GenLeaf (inl 1)
  | ff => GenLeaf (inl 0)
  | D1 ⩽ D2 => GenNode 2 [GenLeaf (inr D1) ; GenLeaf (inr D2)]
  | e1 ∨ e2 => GenNode 3 [encode_equation e1 ; encode_equation e2]
  | non e => GenNode 4 [encode_equation e] 
end.

Fixpoint decode_equation (tree : gen_tree (nat + Data)) : Equation Data :=
match tree with
  | GenLeaf (inl 1) => tt
  | GenLeaf (inl 0) => ff
  | GenNode 2 [GenLeaf (inr d); GenLeaf (inr d')] => d ⩽ d'
  | GenNode 3 [p ; q] => (decode_equation p) ∨ (decode_equation q)
  | GenNode 4 [t'] => non (decode_equation t')
  | _ => ff
end. 

Lemma Equation_dec : forall (x y : Equation Data) , {x = y} + {x <> y}.
Proof.
decide equality. apply Data_dec. apply Data_dec.
Qed.

#[global] Instance equation_dec : EqDecision (Equation Data). exact Equation_dec. Defined.

Lemma encode_decide_equations p : decode_equation (encode_equation p) = p.
Proof. 
induction p.
* simpl. reflexivity.
* simpl. reflexivity.
* simpl. reflexivity.
* simpl. rewrite IHp1. rewrite IHp2. reflexivity.
* simpl. rewrite IHp. reflexivity.
Qed.

#[global] Instance equation_countable : Countable (Equation Data).
Proof.
  refine (inj_countable' encode_equation decode_equation _).
  apply encode_decide_equations.
Qed.

Lemma TypeOfActions_dec : forall (x y : TypeOfActions) , {x = y} + {x <> y}.
Proof.
decide equality. 
* destruct (decide(d = d0)). left. assumption. right. assumption.
* destruct (decide (c = c0)). left. assumption. right. assumption.
Qed.

#[global] Instance TypeOfActions_eqdecision : EqDecision TypeOfActions. by exact TypeOfActions_dec . Defined.

Fixpoint proc_dec (x y : proc) : { x = y } + { x <> y }
with gproc_dec (x y : gproc) : { x = y } + { x <> y }.
Proof.
decide equality. 
* destruct (decide(n = n0));eauto.
* destruct (decide(n = n0));eauto.
* destruct (decide(e = e0));eauto. 
* destruct (decide(d = d0));eauto.
* destruct (decide(c = c0));eauto.
* decide equality. destruct (decide(c = c0));eauto.
Qed.

#[global] Instance proc_eqdecision : EqDecision proc. by exact proc_dec. Defined.

Definition encode_TypeOfActions (a : TypeOfActions) : gen_tree (nat + (Channel + Data)) :=
match a with
  | act c v => GenNode 0 [GenLeaf (inr (inl c)) ; GenLeaf (inr (inr v))]
end.

Definition decode_TypeOfActions (tree :gen_tree (nat + (Channel + Data))) : option TypeOfActions :=
match tree with
  | GenNode 0 [GenLeaf (inr (inl c)); GenLeaf (inr (inr v))] => Some (act c v)
  | _ => None
end.

Lemma encode_decide_TypeOfActions p : decode_TypeOfActions (encode_TypeOfActions  p) = Some p.
Proof. 
induction p. 
* simpl. reflexivity.
Qed.

#[global] Instance TypeOfActions_countable : Countable TypeOfActions.
Proof.
  eapply inj_countable with encode_TypeOfActions decode_TypeOfActions. 
  intro. apply encode_decide_TypeOfActions.
Qed.

Fixpoint encode_proc (p: proc) : gen_tree (nat + (((Equation Data ) + TypeOfActions) + Channel)) :=
  match p with
  | p ‖ q  => GenNode 0 [encode_proc p; encode_proc q]
  | c ! v • 𝟘  => GenLeaf (inr $ inl $ inr $ (c ⋉ v))
  | pr_var i => GenNode 2 [GenLeaf $ inl i]
  | rec x • P => GenNode 3 [GenLeaf $ inl x; encode_proc P]
  | If C Then A Else B => GenNode 4 [GenLeaf (inr ( inl (inl C))) ; encode_proc A; encode_proc B]
  | g gp => GenNode 1 [encode_gproc gp]
  end
with
encode_gproc (gp: gproc) : gen_tree (nat + (((Equation Data ) + TypeOfActions) + Channel)) :=
  match gp with
  | ① => GenNode 1 []
  | 𝟘 => GenNode 0 []
  | c ? p => GenNode 2 [GenLeaf (inr $ inr c); encode_proc p]
  | t • p => GenNode 3 [encode_proc p]
  | gp + gq => GenNode 4 [encode_gproc gp; encode_gproc gq]
  end.
  
Definition Channel_of (a : TypeOfActions) : Channel := 
match a with 
| act c d => c
end.

Definition Data_of (a : TypeOfActions) : Data := 
match a with 
| act c d => d
end.

Fixpoint decode_proc (t': gen_tree (nat + (((Equation Data ) + TypeOfActions) + Channel))) : proc :=
  match t' with
  | GenNode 0 [ep; eq] => (decode_proc ep) ‖ (decode_proc eq)
  | GenLeaf (inr ( inl (inr a))) => (Channel_of a) ! (Data_of a) • 𝟘
  | GenNode 2 [GenLeaf (inl i)] => pr_var i
  | GenNode 3 [GenLeaf (inl i); egq] => rec i • (decode_proc egq)
  | GenNode 4 [GenLeaf (inr ( inl (inl C))); A; B] => If C Then (decode_proc A) Else (decode_proc B)
  | GenNode 1 [egp] => g (decode_gproc egp)
  | _ => ① 
  end
with
decode_gproc (t': gen_tree (nat + (((Equation Data ) + TypeOfActions) + Channel))): gproc :=
  match t' with
  | GenNode 1 [] => ①
  | GenNode 0 [] => 𝟘
  | GenNode 2 [GenLeaf (inr (inr c)); ep] => c ? (decode_proc ep)
  | GenNode 3 [eq] => t • (decode_proc eq)
  | GenNode 4 [egp; egq] => (decode_gproc egp) + (decode_gproc egq)
  | _ => ① 
  end.

Lemma encode_decide_procs p : decode_proc (encode_proc p) = p
with encode_decide_gprocs p : decode_gproc (encode_gproc p) = p.
Proof. all: case p. 
* intros. simpl. rewrite (encode_decide_procs p0). rewrite (encode_decide_procs p1). reflexivity.
* intros. simpl. reflexivity.
* intros. simpl. rewrite (encode_decide_procs p0). reflexivity.
* intros. simpl. rewrite (encode_decide_procs p0). rewrite (encode_decide_procs p1). reflexivity.
* intros. simpl. reflexivity.
* intros. simpl. rewrite (encode_decide_gprocs g0). reflexivity.
* intros. simpl. reflexivity. 
* intros. simpl. reflexivity. 
* intros. simpl. rewrite (encode_decide_procs p0). reflexivity.
* intros. simpl. rewrite (encode_decide_procs p0). reflexivity.
* intros. simpl. rewrite (encode_decide_gprocs g0). rewrite (encode_decide_gprocs g1). reflexivity.
Qed.

#[global] Instance proc_count : Countable proc.
refine (inj_countable' encode_proc decode_proc _).
  apply encode_decide_procs.
Qed.
#[global] Instance Singletons_of_TypeOfActions : SingletonMS TypeOfActions (gmultiset TypeOfActions) 
:=gmultiset_singleton.
#[global] Instance Singletons_of_proc : Singleton proc (gset proc) := gset_singleton.
#[global] Instance Empty_of_proc : Empty (gset proc) := gset_empty.
#[global] Instance Union_of_proc : Union (gset proc) := gset_union.
#[global] Instance SemiSet_of_proc : SemiSet proc (gset proc) := gset_semi_set.

(* Next Obligations *)
Fixpoint moutputs_of p : gmultiset TypeOfActions := 
match p with
  | P ‖ Q => (moutputs_of P) ⊎ (moutputs_of Q)
  | pr_var _ => ∅
  | rec _ • _ => ∅
  | If C Then P Else Q => ∅
  | c ! v • 𝟘 => {[+ c ⋉ v +]}
  | g _ => ∅
end.  
Definition outputs_of p := dom (moutputs_of p).

Lemma mo_equiv_spec_step : forall {p q}, p ≡ q -> moutputs_of p = moutputs_of q.
Proof. intros. dependent induction H; multiset_solver. Qed.

Lemma mo_equiv_spec : forall {p q}, p ≡* q -> moutputs_of p = moutputs_of q.
Proof.
  intros p q hcgr.
  induction hcgr. now eapply mo_equiv_spec_step.
  etrans; eauto.
Qed.

Lemma mo_spec p a q : lts p (ActOut a) q -> moutputs_of p = {[+ a +]} ⊎ moutputs_of q.
Proof.
  intros l. assert (lts p (ActOut a) q). assumption. apply OutputWithValue in H.
  decompose record H. subst. rename x into c. rename x0 into v.
  eapply TransitionShapeForOutputSimplified, mo_equiv_spec in l. simpl in l. eauto.
Qed.

Lemma mo_spec_l e a :
  a ∈ moutputs_of e -> {e' | lts e (ActExt $ ActOut a) e' /\ moutputs_of e' = moutputs_of e ∖ {[+ a +]}}.
Proof.
  intros mem.
  dependent induction e.
  + cbn in mem.
    destruct (decide (a ∈ moutputs_of e1)).
    destruct (IHe1 a e) as (e1' & lts__e1 & eq).
    exists (pr_par e1' e2). repeat split; eauto with ccs.
    multiset_solver.
    destruct (decide (a ∈ moutputs_of e2)).
    destruct (IHe2 a e) as (e2' & lts__e2 & eq).
    exists (pr_par e1 e2'). repeat split; eauto with ccs.
    multiset_solver.
    contradict mem. intro mem. multiset_solver.
    + exfalso. multiset_solver.
    + exfalso. multiset_solver.
    + exfalso. multiset_solver.
  + exists (g 𝟘).
    assert (a = c ⋉ d). multiset_solver. subst.
    repeat split; eauto with ccs. multiset_solver.
  + simpl in mem. exfalso. set_solver. 
Qed.

Lemma mo_spec_r e a :
  {e' | lts e (ActExt $ ActOut a) e' /\ moutputs_of e' = moutputs_of e ∖ {[+ a +]}} -> a ∈ moutputs_of e.
Proof.
  dependent induction e; intros (e' & l & mem).
  + cbn.
    inversion l; subst.
    eapply gmultiset_elem_of_disj_union. left.
    eapply IHe1. exists p2. split.
    eassumption. cbn in mem. multiset_solver.
    eapply gmultiset_elem_of_disj_union. right.
    eapply IHe2. exists q2. split.
    eassumption. cbn in mem. multiset_solver.
  + inversion l.
  + inversion l.
  + inversion l.    
  + inversion l; subst. set_solver.
  + destruct a. now eapply guarded_does_no_output in l.
Qed.


Lemma outputs_of_spec2 p a : a ∈ outputs_of p -> {q | lts p (ActExt (ActOut a)) q}.
Proof.
  intros mem.
  eapply gmultiset_elem_of_dom in mem.
  eapply mo_spec_l in mem.
  firstorder.
Qed.

Lemma outputs_of_spec1_zero (p : proc) (a : TypeOfActions) : {q | lts p (ActExt (ActOut a)) q} 
      -> a ∈ outputs_of p.
Proof.    
  intros (p' & lts__p).
  dependent induction p.
  + eapply gmultiset_elem_of_dom.
    cbn. inversion lts__p; subst. apply IHp1 in H3. eapply gmultiset_elem_of_dom in H3. multiset_solver.
     apply IHp2 in H3. eapply gmultiset_elem_of_dom in H3. multiset_solver.
  + inversion lts__p; subst.
  + inversion lts__p; subst.
  + inversion lts__p; subst.
  + inversion lts__p; subst. unfold outputs_of. multiset_solver.
  + assert (lts g0 (ActOut a) p'). assumption. apply OutputWithValue in H.
    decompose record H. subst. rename x into c. rename x0 into v.
    now eapply guarded_does_no_output in lts__p.
Qed.

Lemma outputs_of_spec1 (p : proc) (a : TypeOfActions) (q : proc) : lts p (ActExt (ActOut a)) q
      -> a ∈ outputs_of p.
Proof.
intros. eapply outputs_of_spec1_zero. exists q. assumption.
Qed.

Fixpoint lts_set_output (p : proc) (a : TypeOfActions) : gset proc:=
match p with
  | p1 ‖ p2 => 
      let ps1 := lts_set_output p1 a in
      let ps2 := lts_set_output p2 a in
      (* fixme: find a way to map over sets. *)
      list_to_set (map (fun p => p ‖ p2) (elements ps1)) ∪ list_to_set (map (fun p => p1 ‖ p) (elements ps2))
  | pr_var _ => ∅
  | rec _ • _ => ∅
  | If _ Then _ Else _ => ∅
  | c ! v • 𝟘 => if decide(a = (c ⋉ v)) then {[ (g 𝟘) ]} else ∅
  | g _  => ∅
end.

Fixpoint lts_set_input_g (g : gproc) (a : TypeOfActions) : gset proc :=
  match g with
  | c ? p => if decide(Channel_of a = c) then {[ p^(Data_of a) ]} else ∅
  | g1 + g2 => lts_set_input_g g1 a ∪ lts_set_input_g g2 a
  | ① => ∅
  | 𝟘 => ∅
  | t • p => ∅
  end.
  
Fixpoint lts_set_input (p : proc) (a : TypeOfActions) : gset proc :=
match p with
  | p1 ‖ p2 =>
      let ps1 := lts_set_input p1 a in
      let ps2 := lts_set_input p2 a in
      list_to_set (map (fun p => p ‖ p2) (elements ps1)) ∪ list_to_set (map (fun p => p1 ‖ p) (elements ps2))
  | pr_var _ => ∅
  | rec _ • _ => ∅ 
  | c ! v • 𝟘 => ∅
  | If _ Then _ Else _ => ∅
  | g gp => lts_set_input_g gp a  
  end.
  
Fixpoint lts_set_tau_g (gp : gproc) : gset proc :=
match gp with
  | c ? p => ∅
  | ① => ∅
  | 𝟘 => ∅
  | t • p => {[ p ]}
  | gp1 + gp2 => lts_set_tau_g gp1 ∪ lts_set_tau_g gp2
end.



Fixpoint lts_set_tau (p : proc) : gset proc :=
match p with
  | p1 ‖ p2 =>
      let ps1_tau : gset proc := list_to_set (map (fun p => p ‖ p2) (elements $ lts_set_tau p1)) in
      let ps2_tau : gset proc := list_to_set (map (fun p => p1 ‖ p) (elements $ lts_set_tau p2)) in
      let ps_tau := ps1_tau ∪ ps2_tau in
      let acts1 := outputs_of p1 in
      let acts2 := outputs_of p2 in
      let ps1 :=
        flat_map (fun a =>
                    map
                      (fun '(p1 , p2) => p1 ‖ p2)
                      (list_prod (elements $ lts_set_output p1 a) (elements $ lts_set_input p2 a)))
        (elements $ outputs_of p1) in
      let ps2 :=
        flat_map
          (fun a =>
             map
               (fun '(p1 , p2) => p1 ‖ p2)
               (list_prod (elements $ lts_set_input p1 a) (elements $ lts_set_output p2 a)))
          (elements $ outputs_of p2)
      in
      ps_tau ∪ list_to_set ps1 ∪ list_to_set ps2
  | c ! v • 𝟘 => ∅
  | pr_var _ => ∅
  | rec x • p => {[ pr_subst x p (rec x • p) ]}
  | If C Then A Else B => match (Eval_Eq C) with 
                          | Some true => {[ A ]}
                          | Some false => {[ B ]}
                          | None => ∅
                          end
  | g gp => lts_set_tau_g gp
end.

Lemma lts_set_output_spec0 p a q : q ∈ lts_set_output p a -> lts p (ActExt (ActOut a)) q.
Proof.
  intro mem.
  dependent induction p; simpl in mem; try now inversion mem.
  - eapply elem_of_union in mem as [mem | mem]. 
    * eapply elem_of_list_to_set, elem_of_list_fmap in mem as (q' & eq & mem). subst.
    apply lts_parL. apply IHp1. rewrite elem_of_elements in mem. set_solver.
    * eapply elem_of_list_to_set, elem_of_list_fmap in mem as (q' & eq & mem). subst.
    apply lts_parR. apply IHp2. rewrite elem_of_elements in mem. exact mem.
  -  case (TypeOfActions_dec a (c ⋉ d)) in mem.
    + rewrite e. rewrite e in mem.
      destruct (decide (c ⋉ d = c ⋉ d)). subst. assert (q = (g 𝟘)). set_solver.
      rewrite H. apply lts_output. exfalso. set_solver.
    + destruct (decide (a = c ⋉ d)). exfalso. apply n. assumption. set_solver.
Qed.

Lemma lts_set_output_spec1 p a q : lts p (ActExt $ ActOut a) q -> q ∈ lts_set_output p a.
Proof.
  intro l. dependent induction l; try set_solver.
  simpl. destruct (decide (c ⋉ v = c ⋉ v)). set_solver. exfalso. apply n. reflexivity.
Qed.

Lemma lts_set_input_spec0 p a q : q ∈ lts_set_input p a -> lts p (ActExt $ ActIn a) q.
Proof.
  intro mem.
  dependent induction p; simpl in mem; try set_solver.
  + eapply elem_of_union in mem. destruct mem.
    ++ eapply elem_of_list_to_set in H.
       eapply elem_of_list_fmap in H as (q' & eq & mem). subst.
       rewrite elem_of_elements in mem. eauto with ccs.
    ++ eapply elem_of_list_to_set in H.
       eapply elem_of_list_fmap in H as (q' & eq & mem). subst.
       rewrite elem_of_elements in mem. eauto with ccs.
  + dependent induction g0; simpl in mem; try set_solver.
      ++ destruct (decide (Channel_of a = c)).
         +++ subst. eapply elem_of_singleton_1 in mem. subst. destruct a. simpl. apply lts_input.
         +++ destruct a. simpl in *. inversion mem.
      ++ eapply elem_of_union in mem. destruct mem; eauto with ccs.
Qed.

Lemma lts_set_input_spec1 p a q : lts p (ActExt $ ActIn a) q -> q ∈ lts_set_input p a.
Proof.
  intro l. dependent induction l; try set_solver.
  simpl. destruct (decide (c = c)). set_solver. exfalso. apply n. reflexivity.
Qed.


Lemma lts_set_tau_spec0 p q : q ∈ lts_set_tau p -> lts p τ q.
Proof.
  - intro mem.
    dependent induction p; simpl in mem.
    + eapply elem_of_union in mem. destruct mem as [mem1 | mem2].
      ++ eapply elem_of_union in mem1.
         destruct mem1.
         eapply elem_of_union in H as [mem1 | mem2]. 
         eapply elem_of_list_to_set, elem_of_list_fmap in mem1 as (t' & eq & h); subst.
         rewrite elem_of_elements in h. eauto with ccs.
         eapply elem_of_list_to_set, elem_of_list_fmap in mem2 as (t' & eq & h); subst.
         rewrite elem_of_elements in h. eauto with ccs.
         eapply elem_of_list_to_set, elem_of_list_In, in_flat_map in H as (t' & eq & h); subst.
         eapply elem_of_list_In, elem_of_list_fmap in h as ((t1 & t2) & eq' & h'). subst.
         eapply elem_of_list_In, in_prod_iff in h' as (mem1 & mem2).
         eapply elem_of_list_In in mem1. rewrite elem_of_elements in mem1.
         eapply elem_of_list_In in mem2. rewrite elem_of_elements in mem2.
         eapply lts_set_output_spec0 in mem1.
         eapply lts_set_input_spec0 in mem2. destruct t'. eapply lts_comL. exact mem1. exact mem2.
      ++ eapply elem_of_list_to_set, elem_of_list_In, in_flat_map in mem2 as (t' & eq & h); subst.
         eapply elem_of_list_In, elem_of_list_fmap in h as ((t1 & t2) & eq' & h'). subst.
         eapply elem_of_list_In, in_prod_iff in h' as (mem1 & mem2).
         eapply elem_of_list_In in mem1. rewrite elem_of_elements in mem1.
         eapply elem_of_list_In in mem2. rewrite elem_of_elements in mem2.
         eapply lts_set_input_spec0 in mem1.
         eapply lts_set_output_spec0 in mem2. destruct t'. eapply lts_comR. exact mem2. exact mem1.
    + inversion mem.
    + eapply elem_of_singleton_1 in mem. subst; eauto with ccs.
    + destruct (decide (Eval_Eq e = Some true)).
      * rewrite e0 in mem. assert (q = p1). set_solver. rewrite H. constructor. assumption.
      * destruct (decide (Eval_Eq e = Some false)). rewrite e0 in mem. 
        assert (q = p2). set_solver. rewrite H. constructor. assumption.
        assert (Eval_Eq e = None). destruct (Eval_Eq e). destruct b. exfalso. apply n. reflexivity.
        exfalso. apply n0. reflexivity. reflexivity. rewrite H in mem. set_solver.
    + inversion mem.
    + dependent induction g0; simpl in mem; try set_solver;
        try eapply elem_of_singleton_1 in mem; subst; eauto with ccs.
      eapply elem_of_union in mem as [mem1 | mem2]; eauto with ccs.
Qed.

Lemma lts_set_tau_spec1 p q : lts p τ q -> q ∈ lts_set_tau p.
Proof. 
  intro l. dependent induction l; simpl; try set_solver.
  - rewrite H. set_solver. 
  - rewrite H. set_solver. 
  - eapply elem_of_union. left.
    eapply elem_of_union. right.
    eapply elem_of_list_to_set.
    rewrite elem_of_list_In. rewrite in_flat_map.
    exists (c ⋉ v). split.
    + eapply elem_of_list_In, elem_of_elements.
      eapply outputs_of_spec1_zero. eauto.
    + eapply elem_of_list_In, elem_of_list_fmap.
      exists (p2 , q2). split.
      ++ reflexivity.
      ++ eapply elem_of_list_In, in_prod_iff; split; eapply elem_of_list_In, elem_of_elements.
         eapply lts_set_output_spec1; eauto with ccs.
         eapply lts_set_input_spec1; eauto with ccs.
  - eapply elem_of_union. right.
    eapply elem_of_list_to_set.
    rewrite elem_of_list_In. rewrite in_flat_map.
    exists (c ⋉ v). split.
    + eapply elem_of_list_In, elem_of_elements.
      eapply outputs_of_spec1_zero. exists p2. exact l1.
    + eapply elem_of_list_In, elem_of_list_fmap.
      exists (q2 , p2). split.
      ++ reflexivity.
      ++ eapply elem_of_list_In, in_prod_iff; split; eapply elem_of_list_In, elem_of_elements.
         eapply lts_set_input_spec1; eauto with ccs.
         eapply lts_set_output_spec1; eauto with ccs.
Qed.


Definition lts_set (p : proc) (α : Act TypeOfActions): gset proc :=
  match α with
  | τ => lts_set_tau p
  | ActExt (ActIn a) => lts_set_input p a
  | ActExt (ActOut a) => lts_set_output p a
  end.

Lemma lts_set_spec0 p α q : q ∈ lts_set p α -> lts p α q.
Proof.
  destruct α as [[a|a]|].
  - now eapply lts_set_input_spec0.
  - now eapply lts_set_output_spec0.
  - now eapply lts_set_tau_spec0.
Qed.

Lemma lts_set_spec1 p α q : lts p α q -> q ∈ lts_set p α.
Proof.
  destruct α as [[a|a]|].
  - now eapply lts_set_input_spec1.
  - now eapply lts_set_output_spec1.
  - now eapply lts_set_tau_spec1.
Qed.

Definition proc_stable p α := lts_set p α = ∅.

Lemma lts_dec p α q : { lts p α q } + { ~ lts p α q }.
Proof.
  destruct (decide (q ∈ lts_set p α)).
  - eapply lts_set_spec0 in e. eauto.
  - right. intro l. now eapply lts_set_spec1 in l.
Qed.

Lemma proc_stable_dec p α : Decision (proc_stable p α).
Proof. destruct (decide (lts_set p α = ∅)); [ left | right ]; eauto. Qed.

Lemma gset_nempty_ex (g : gset proc) : g ≠ ∅ -> {p | p ∈ g}.
Proof.
  intro n. destruct (elements g) eqn:eq.
  + destruct n. eapply elements_empty_iff in eq. set_solver.
  + exists p. eapply elem_of_elements. rewrite eq. set_solver.
Qed.

(* Making VACCS Instance of each class *)

#[global] Program Instance VACCS_Label : Label TypeOfActions := 
  {| label_eqdec := TypeOfActions_dec ;
  label_countable := TypeOfActions_countable |}. (* useless, already said it, it is just a reminder *)

#[global] Program Instance VACCS_Lts : Lts proc TypeOfActions := 
  {| lts_step x ℓ y  := lts x ℓ y ;
     lts_state_eqdec := proc_dec ;
     lts_step_decidable p α q := lts_dec p α q ;
     lts_outputs := outputs_of ;
     lts_outputs_spec1 p1 x p2 := outputs_of_spec1 p1 x p2;
     lts_outputs_spec2 p1 x := outputs_of_spec2 p1 x;
     lts_stable p := proc_stable p;
     lts_stable_decidable p α := proc_stable_dec p α 
    |}.
    Next Obligation.
        intros p [[a|a]|]; intro hs;eapply gset_nempty_ex in hs as (r & l); eapply lts_set_spec0 in l; 
        exists r; assumption.
    Qed.
    Next Obligation.  
        intros p [[a|a]|]; intros (q & mem); intro eq; eapply lts_set_spec1 in mem; set_solver.
    Qed.

#[global] Program Instance VACCS_LtsEq : LtsEq proc TypeOfActions := 
  {| eq_rel x y  := cgr x y;
     eq_rel_refl p := cgr_refl p;
     eq_symm p q := cgr_symm p q;
     eq_trans x y z:= cgr_trans x y z;
     eq_spec p q α := Congruence_Respects_Transition p q α |}.

#[global] Program Instance VACCS_LtsOba : LtsOba proc TypeOfActions :=
  {| lts_oba_output_commutativity p q r a α := OBA_with_FB_First_Axiom p q r a α;
     lts_oba_output_confluence p q1 q2 a μ := OBA_with_FB_Second_Axiom p q1 q2 a μ;
     lts_oba_output_deter p1 p2 p3 a := OBA_with_FB_Third_Axiom p1 p2 p3 a;
     lts_oba_output_tau p q1 q2 a := OBA_with_FB_Fifth_Axiom p q1 q2 a;
     lts_oba_output_deter_inv p1 p2 q1 q2 a := ExtraAxiom p1 p2 q1 q2 a;
     lts_oba_mo p := moutputs_of p 
  |}.
  Next Obligation.
    intros. simpl. unfold outputs_of.
    now rewrite gmultiset_elem_of_dom.
  Qed.
  Next Obligation.
    intros. simpl. unfold outputs_of.
    now eapply mo_spec.
  Qed.
  

#[global] Program Instance VACCS_LtsObaFB : LtsObaFB proc TypeOfActions :=
  {| lts_oba_fb_feedback p1 p2 p3 a := OBA_with_FB_Fourth_Axiom p1 p2 p3 a |}.

*)

(* Definition test_term :=  (ν ν (1 ! 0 • (0 ? 𝟘) + 𝟘) ‖ 0 ? (0 ! 3 • 𝟘) + 𝟘).

Lemma test_term_sts: sts test_term (ν ν (0 ? 𝟘 ‖ 0 ! 3 • 𝟘)).
Proof.
unfold test_term.
eapply sts_res.
eapply sts_cong.
- apply cgr_scope_rev.
- eapply sts_res. eapply sts_com.
- simpl. asimpl. apply cgr_refl.
Qed.

Lemma check : 
  (@subst2 _ _ _ _ Subst_proc ids (@scons Data O ids)
  (gpr_output 0 (@subst1 _ _ _ Subst_Data ids 4) 𝟘))= 
0 ! 3 • 𝟘.
Proof.
reflexivity.
Qed.

Lemma test_term_lts: lts test_term τ
  (ν ν (0 ? 𝟘 ‖ 0 ! 3 • 𝟘)).
  (* (subst_proc ids (@scons Data (var_Data O) ids)
  (gpr_output 0
  (Subst_Data ids 4) (Subst_proc ids (@scons Data O ids) 𝟘)
  )))). *)
Proof.
unfold test_term.
unfold Subst_proc. Set Printing All.
(* eexists. *)
assert (τ = Shift_Action τ) by reflexivity. rewrite H.
eapply lts_res.
eapply (@lts_close_l 1).
- eapply (@lts_open 1).
  + intro F. inversion F.
  + eapply lts_choiceL. eapply lts_output.
- eapply lts_choiceL. rewrite <- check. apply lts_input.
Set Printing All.
Show Proof.
Qed.

 *)
