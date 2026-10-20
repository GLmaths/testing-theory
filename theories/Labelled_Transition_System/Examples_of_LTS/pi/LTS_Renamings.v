(* begin hide *)
From TestingTheory Require Import pi.LTS Renamings pi.Congruence.
From Stdlib.Program Require Import Equality.
From Stdlib Require Import Morphisms.

Section LTS_Renamings.

Context {PiV : Pi_Values} {PiE : @Pi_Equations PiV}.

Lemma is_bound_ren : forall 𝜆 σ,
  is_bound_out 𝜆 = is_bound_out (ren1 σ 𝜆).
Proof.
intros 𝜆 σ. destruct 𝜆; try destruct e; reflexivity.
Qed.

Lemma is_bound_shift : forall 𝜆,
  is_bound_out 𝜆 = is_bound_out (⇑ 𝜆).
Proof. intro 𝜆. eapply is_bound_ren. Qed.

Lemma is_bound_exists : forall 𝜆,
  is_bound_out 𝜆 = true ->
  exists c, 𝜆 = BoundOut c.
Proof.
intros 𝜆 H. destruct 𝜆; try destruct e; try discriminate; eauto.
Qed.

Lemma Invert_Lts_Input : forall p q c v σ,
  lts (p ⟨σ⟩) (ActIn (c ⋉ v)) q ->
  exists c', c = ren1 σ c'.
Proof.
intros p q c v σ transition.
remember (p ⟨σ⟩) as P0 eqn:x in transition. remember (ActIn (c ⋉ v)) as α eqn:hα in transition.
revert p c v σ x hα.
induction transition; intros pX cX vX σX x hα; try discriminate; try (injection hα; intros; subst); subst; try rename p into p0; try rename pX into p; try rename cX into c; try rename vX into v; try rename σX into σ.
- destruct p; inversion x. destruct g0; inversion x. now exists d.
- destruct p; inversion x.
  destruct (IHtransition p (⇑ c) (⇑ v) (up_ren σ) H0 eq_refl) as [c' Heq].
  destruct (Invert_Shift _ _ _ Heq) as (d & Hd).
  exists d.
  rewrite Hd in Heq. rewrite permute_ren1 in Heq.
  now apply (Injective_Ren_Data _ Shift_Injective) in Heq.
- destruct p; inversion x. asimpl in x.
  destruct (IHtransition p3 _ _ _ H0 eq_refl) as (d & ?). exists d. exact H.
- destruct p; inversion x. asimpl in x.
  destruct (IHtransition p2 _ _ _ H1 eq_refl) as (d & ?). exists d. exact H.
- destruct p; inversion x. destruct g0; inversion x.
  assert (Heq: (g p1) = (g g0_1) ⟨σ⟩) by (asimpl; simpl; f_equal; exact H1).
  destruct (IHtransition (g g0_1) _ _ _ Heq eq_refl) as (d & ?). exists d. exact H.
- destruct p; inversion x. destruct g0; inversion x.
  assert (Heq: (g p2) = (g g0_2) ⟨σ⟩) by (asimpl; simpl; f_equal; exact H2).
  destruct (IHtransition (g g0_2) _ _ _ Heq eq_refl) as (d & ?). exists d. exact H.
Qed.

Lemma Invert_Lts_Input_Full : forall p q c v σ,
  lts (p ⟨σ⟩) (ActIn (c ⋉ ren1 σ v)) q ->
  exists c' q',
  c = ren1 σ c' /\
  q = q' ⟨σ⟩    /\
  lts p (ActIn (c' ⋉ v)) q'.
Proof.
intros p q c v σ transition.
remember (p ⟨σ⟩) as P0 eqn:x in transition. remember (ActIn (c ⋉ ren1 σ v)) as α eqn:hα in transition.
revert p c v σ x hα.
induction transition; intros pX cX vX σX x hα; try discriminate; try (injection hα; intros; subst); subst; try rename p into p0; try rename pX into p; try rename cX into c; try rename vX into v; try rename σX into σ.
- destruct p; inversion x. destruct g0; inversion x.
  repeat eexists; [|eapply lts_input]. now asimpl.
- destruct p; inversion x.
  assert (HeqAct: ⇑ (ActIn (c ⋉ ren1 σ v)) = ActIn (⇑ c ⋉ ren1 (up_ren σ) (⇑ v)))
  by (unfold shift_op; now setoid_rewrite <- shift_permute_Data).
  destruct (IHtransition p (⇑ c) (⇑ v) (up_ren σ) H0 HeqAct) as (c' & q' & Heq1 & Heq2 & Heq3).
  destruct (Invert_Shift _ _ _ Heq1) as (d & Hd).
  exists d, (ν q'). repeat split.
  + rewrite Hd in Heq1. rewrite permute_ren1 in Heq1.
    now apply (Injective_Ren_Data _ Shift_Injective) in Heq1.
  + now rewrite Heq2.
  + rewrite Hd in Heq3. refine (eq_rect _ _ (lts_res _) _ _). apply Heq3. reflexivity.
- destruct p; inversion x. asimpl in x.
  destruct (IHtransition p3 _ _ _ H0 eq_refl) as (d & q' & Heq1 & Heq2 & Heq3).
  exists d, (q' ‖ p4). subst. repeat split; eauto with lts.
- destruct p; inversion x. asimpl in x.
  destruct (IHtransition p2 _ _ _ H1 eq_refl) as (d & q' & Heq1 & Heq2 & Heq3).
  subst. now repeat eexists; eauto with lts.
- destruct p; inversion x. destruct g0; inversion x.
  assert (Heq: (g p1) = (g g0_1) ⟨σ⟩) by (asimpl; simpl; f_equal; exact H1).
  destruct (IHtransition (g g0_1) _ _ _ Heq eq_refl) as (d & q' & Heq1 & Heq2 & Heq3).
  eexists. eexists. repeat split; eauto with lts.
- destruct p; inversion x. destruct g0; inversion x.
  assert (Heq: (g p2) = (g g0_2) ⟨σ⟩) by (asimpl; simpl; f_equal; exact H2).
  destruct (IHtransition (g g0_2) _ _ _ Heq eq_refl) as (d & q' & Heq1 & Heq2 & Heq3).
  eexists. eexists. repeat split; eauto with lts.
Qed.

Lemma Invert_Lts_FreeOut : forall p q c v σ,
lts (p ⟨σ⟩) (FreeOut (c ⋉ v)) q ->
  exists c' v' q',
  c = ren1 σ c' /\
  v = ren1 σ v' /\
  q = q' ⟨σ⟩    /\
  lts p (FreeOut (c' ⋉ v')) q'.
Proof.
intros p q c v σ transition.
remember (p ⟨σ⟩) as P0 eqn:x in transition. remember (FreeOut (c ⋉ v)) as α eqn:hα in transition.
revert p c v σ x hα.
induction transition; intros pX cX vX σX x hα; try discriminate; try (injection hα; intros; subst); subst; try rename p into p0; try rename pX into p; try rename cX into c; try rename vX into v; try rename σX into σ.
- destruct p; inversion x. destruct g0; inversion x.
  repeat eexists; eapply lts_output.
- destruct p; inversion x.
  assert (HeqAct: ⇑ (FreeOut (c ⋉ v)) = FreeOut (⇑ c ⋉ ⇑ v)) by trivial.
  destruct (IHtransition p (⇑ c) (⇑ v) (up_ren σ) H0 HeqAct) as (c' & v' & q' & Heq1 & Heq2 & Heq3 & Heq4).
  destruct (Invert_Shift _ _ _ Heq1) as (d & Hd).
  destruct (Invert_Shift _ _ _ Heq2) as (w & Hw).
  exists d, w, (ν q'). repeat split.
  + rewrite Hd in Heq1. rewrite permute_ren1 in Heq1.
    now apply (Injective_Ren_Data _ Shift_Injective) in Heq1.
  + rewrite Hw in Heq2. rewrite permute_ren1 in Heq2.
    now apply (Injective_Ren_Data _ Shift_Injective) in Heq2.
  + now rewrite Heq3.
  + rewrite Hd, Hw in Heq4. refine (eq_rect _ _ (lts_res _) _ _). apply Heq4. reflexivity.
- destruct p; inversion x. asimpl in x.
  destruct (IHtransition p3 _ _ _ H0 eq_refl) as (d & w & q' & Heq1 & Heq2 & Heq3 & Heq4).
  exists d, w, (q' ‖ p4). subst. repeat split; eauto with lts.
- destruct p; inversion x. asimpl in x.
  destruct (IHtransition p2 _ _ _ H1 eq_refl) as (d & w & q' & Heq1 & Heq2 & Heq3 & Heq4).
  subst. now repeat eexists; eauto with lts.
- destruct p; inversion x. destruct g0; inversion x.
  assert (Heq: (g p1) = (g g0_1) ⟨σ⟩) by (asimpl; simpl; f_equal; exact H1).
  destruct (IHtransition (g g0_1) _ _ _ Heq eq_refl) as (d & w & q' & Heq1 & Heq2 & Heq3 & Heq4).
  eexists. eexists. eexists. repeat split; eauto with lts.
- destruct p; inversion x. destruct g0; inversion x.
  assert (Heq: (g p2) = (g g0_2) ⟨σ⟩) by (asimpl; simpl; f_equal; exact H2).
  destruct (IHtransition (g g0_2) _ _ _ Heq eq_refl) as (d & w & q' & Heq1 & Heq2 & Heq3 & Heq4).
  eexists. eexists. eexists. repeat split; eauto with lts.
Qed.

Lemma Invert_Lts_BoundOut : forall p q c σ,
  lts (p ⟨σ⟩) (BoundOut c) q ->
  exists c' q',
  c = ren1 σ c' /\
  q = q' ⟨up_ren σ⟩    /\
  lts p (BoundOut c') q'.
Proof.
intros p q c σ transition.
remember (p ⟨σ⟩) as P0 eqn:x in transition. remember (BoundOut c) as α eqn:hα in transition.
revert p c σ x hα.
induction transition; intros pX cX σX x hα; try discriminate; try (injection hα; intros; subst); subst; try rename p into p0; try rename pX into p; try rename cX into c; try rename σX into σ.
- (* lts_res *)
  destruct p; inversion x.
  destruct (IHtransition _ (⇑ c) _ H0 eq_refl) as (c' & q' & Heq1 & Heq2 & Heq3).
  destruct (Invert_Shift _ _ _ Heq1) as (d & Hd). rewrite Hd, permute_ren1 in Heq1.
  apply (Injective_Ren_Data _ Shift_Injective) in Heq1. rewrite Heq2, <- Up_Up_Swap.
  eexists. exists (ν (q' ⟨swap⟩)). repeat split.
  + exact Heq1.
  + rewrite Hd in Heq3. eapply res_bound; trivial.
- (* lts_open *)
  destruct p; inversion x. subst.
  destruct (Invert_Lts_FreeOut _ _ _ _ _ transition) as (c' & v' & q' & Heq1 & Heq2 & Heq3 & Heq4).
  destruct (Invert_Shift _ _ _ Heq1) as (d & Hd). rewrite Hd, permute_ren1 in Heq1.
  apply (Injective_Ren_Data _ Shift_Injective) in Heq1. rewrite Heq3.
  assert (Hzero: v' = 0) by (destruct v'; try destruct n; now inversion Heq2).
  rewrite Hzero in Heq4.
  eexists. exists q'. repeat split.
  + exact Heq1.
  + eapply lts_open. rewrite <- Hd. exact Heq4.
- destruct p; inversion x.
  destruct (IHtransition _ _ _ H0 eq_refl) as (d & q' & Heq1 & Heq2 & Heq3).
  rewrite Heq2. simpl.
  repeat eexists.
  + exact Heq1.
  + replace (⇑ (ren_proc ids σ p4)) with ((⇑ p4) ⟨up_ren σ⟩) by now asimpl.
    replace (q' ⟨up_ren σ⟩ ‖ (⇑ p4) ⟨up_ren σ⟩) with ((q' ‖ ⇑ p4) ⟨up_ren σ⟩) by now asimpl.
    reflexivity.
  + eapply lts_parL; [exact Heq3 |  reflexivity].
- destruct p; inversion x.
  destruct (IHtransition _ _ _ H1 eq_refl) as (d & q' & Heq1 & Heq2 & Heq3).
  rewrite Heq2. simpl.
  repeat eexists.
  + exact Heq1.
  + replace (⇑ (ren_proc ids σ p1)) with ((⇑ p1) ⟨up_ren σ⟩) by now asimpl.
    replace ((⇑ p1) ⟨up_ren σ⟩ ‖ q' ⟨up_ren σ⟩) with ((⇑ p1 ‖ q') ⟨up_ren σ⟩) by now asimpl.
    reflexivity.
  + eapply lts_parR; [exact Heq3 |  reflexivity].
- destruct p; inversion x. destruct g0; inversion x.
  destruct (IHtransition (g g0_1) c σ) as (d & q' & Heq1 & Heq2 & Heq3);
    (* justifications for IH neets to be stated separately since we work with guards *)
    [now rewrite H1 | reflexivity|].
  repeat eexists; eauto with lts.
- destruct p; inversion x. destruct g0; inversion x.
  destruct (IHtransition (g g0_2) c σ) as (d & q' & Heq1 & Heq2 & Heq3);
    [now rewrite H2 | reflexivity|].
  repeat eexists; eauto with lts.
Qed.

Lemma Invert_Lts_Tau : forall p q σ,
  injective σ ->
  lts (p ⟨σ⟩) τ q ->
  exists q', q = q' ⟨σ⟩ /\ lts p τ q'.
Proof.
intros p q σ Hinj transition.
remember (p ⟨σ⟩) as P0 eqn:x in transition. remember τ as α eqn:hα in transition.
revert σ Hinj p x hα.
induction transition; intros σX HinjX pX x hα; try discriminate; try (injection hα; intros; subst); subst;
  try rename σX into σ; try rename HinjX into Hinj; try rename p into p0; try rename pX into p.
- destruct p; inversion x. destruct g0; inversion H0. exists p; eauto with lts.
- destruct p; inversion x. eexists. split; [|apply lts_recursion]. now asimpl.
- destruct p; inversion x. eexists. split; [reflexivity|].
  apply lts_ifOne.  rewrite H1 in H. setoid_rewrite Eval_Eq_Spec in H. exact H. apply Eq_Subst_Spec_inj, Hinj.
- destruct p; inversion x. eexists. split; [reflexivity|].
  apply lts_ifZero. rewrite H1 in H. setoid_rewrite Eval_Eq_Spec in H. exact H. apply Eq_Subst_Spec_inj, Hinj.
- destruct p; inversion x. rewrite H0 in transition1.
  destruct (Invert_Lts_FreeOut _ _ _ _ σ transition1) as (c' & v' & q' & Heq1 & Heq2 & Heq3 & Heq4).
  rewrite H1 in transition2. rewrite Heq2 in transition2.
  destruct (Invert_Lts_Input_Full _ _ _ _ σ transition2) as (c'' & q'' & Heq5 & Heq6 & Heq7).
  rewrite Heq1 in Heq5. apply Injective_Ren_Data in Heq5; [|apply Hinj].
  subst c''. rewrite Heq3, Heq6.
  eexists. split.
  + now replace (q' ⟨σ⟩ ‖ q'' ⟨σ⟩) with ((q' ‖ q'') ⟨σ⟩) by trivial.
  + eapply lts_comL. apply Heq4. apply Heq7.
- destruct p; inversion x. rewrite H1 in transition1.
  destruct (Invert_Lts_FreeOut _ _ _ _ σ transition1) as (c'' & v' & q'' & Heq4 & Heq5 & Heq6 & Heq7).
  rewrite H0 in transition2. rewrite Heq5 in transition2.
  destruct (Invert_Lts_Input_Full _ _ _ _ σ transition2) as (c' & q' & Heq1 & Heq2 & Heq3).
  rewrite Heq1 in Heq4. apply Injective_Ren_Data in Heq4; [|apply Hinj].
  subst c''. rewrite Heq2, Heq6.
  eexists. split.
  + now replace (q' ⟨σ⟩ ‖ q'' ⟨σ⟩) with ((q' ‖ q'') ⟨σ⟩) by trivial.
  + eapply lts_comR. apply Heq7. apply Heq3.
- destruct p; inversion x. rewrite H0 in transition1.
  destruct (Invert_Lts_BoundOut _ _ _ σ transition1) as (c' & q' & Heq1 & Heq2 & Heq3).
  rewrite H1 in transition2.
  replace (⇑ (ren_proc ids σ p4)) with ((⇑ p4) ⟨up_ren σ⟩) in transition2 by now asimpl.
  replace (var_Data 0) with (ren1 (up_ren σ) (var_Data 0)) in transition2 by trivial.
  destruct (Invert_Lts_Input_Full _ _ _ _ (up_ren σ) transition2) as (c'' & q'' & Heq4 & Heq5 & Heq6).
  rewrite Heq2. rewrite Heq1 in Heq4. rewrite <- permute_ren1 in Heq4.
  apply Injective_UpRen in Hinj.
  apply Injective_Ren_Data in Heq4. 2: { exact Hinj. }
  subst c''. subst q2. eexists. split.
  + replace (q' ⟨up_ren σ⟩ ‖ q'' ⟨up_ren σ⟩) with ((q' ‖ q'') ⟨up_ren σ⟩) by trivial.
    now replace (ν ((q' ‖ q'') ⟨up_ren σ⟩)) with ((ν (q' ‖ q'')) ⟨σ⟩) by trivial.
  + eapply lts_close_l. exact Heq3. exact Heq6.
- destruct p; inversion x. rewrite H1 in transition1.
  destruct (Invert_Lts_BoundOut _ _ _ σ transition1) as (c' & q' & Heq1 & Heq2 & Heq3).
  rewrite H0 in transition2.
  replace (⇑ (ren_proc ids σ p3)) with ((⇑ p3) ⟨up_ren σ⟩) in transition2 by now asimpl.
  replace (var_Data 0) with (ren1 (up_ren σ) (var_Data 0)) in transition2 by trivial.
  destruct (Invert_Lts_Input_Full _ _ _ _ (up_ren σ) transition2) as (c'' & q'' & Heq4 & Heq5 & Heq6).
  rewrite Heq2. rewrite Heq1 in Heq4. rewrite <- permute_ren1 in Heq4.
  apply Injective_UpRen in Hinj.
  apply Injective_Ren_Data in Heq4. 2: { exact Hinj. }
  subst c''. subst q2. subst p2.
  eexists. split.
  + replace (q'' ⟨up_ren σ⟩ ‖ q' ⟨up_ren σ⟩) with ((q'' ‖ q') ⟨up_ren σ⟩) by trivial.
    now replace (ν ((q'' ‖ q') ⟨up_ren σ⟩)) with ((ν (q'' ‖ q')) ⟨σ⟩) by trivial.
  + eapply lts_close_r. exact Heq3. exact Heq6.
- destruct p; inversion x.
  destruct (IHtransition _ (Injective_UpRen _ Hinj) p H0 eq_refl) as (q' & Heq1 & Heq2).
  rewrite Heq1. simpl. eexists. split.
  + simpl. now change (ν (q' ⟨up_ren σ⟩)) with ((ν q') ⟨σ⟩).
  + apply res_not_bound; eauto.
- destruct p; inversion x.
  destruct (IHtransition _ Hinj _ H0 eq_refl) as (q' & Heq1 & Heq2).
  rewrite Heq1. simpl. eexists. split.
  + now change (q' ⟨σ⟩  ‖ ren_proc ids σ p4 ) with ((q' ‖ p4) ⟨σ⟩).
  + apply lts_parL; auto.
- destruct p; inversion x.
  destruct (IHtransition _ Hinj _ H1 eq_refl) as (q' & Heq1 & Heq2).
  rewrite Heq1. simpl. eexists. split.
  + now change (ren_proc ids σ p1 ‖ q' ⟨σ⟩) with ((p1 ‖ q') ⟨σ⟩).
  + apply lts_parR; auto.
- destruct p; inversion x. destruct g0; inversion x.
  destruct (IHtransition _ Hinj (g g0_1)) as (q' & Heq1 & Heq2);
    [now rewrite H1 | reflexivity|].
  rewrite Heq1. repeat eexists; eauto with lts.
- destruct p; inversion x. destruct g0; inversion x.
  destruct (IHtransition _ Hinj (g g0_2)) as (q' & Heq1 & Heq2);
    [now rewrite H2 | reflexivity|].
  rewrite Heq1. repeat eexists; eauto with lts.
Qed.

Lemma Invert_Lts_Alpha : forall p q σ 𝜆,
  is_bound_out 𝜆 = false ->
  injective σ ->
  lts (p ⟨σ⟩) (ren1 σ 𝜆) q ->
  exists q', q = q' ⟨σ⟩ /\ lts p 𝜆 q'.
Proof.
intros p q σ 𝜆 Hbound Hinj transition.
destruct 𝜆; try destruct e.
- (* ActIn *)
  destruct (Invert_Lts_Input_Full _ _ _ _ σ transition) as (c' & q' & Heq1 & Heq2 & Heq3).
  apply Injective_Ren_Data in Heq1; [|apply Hinj].
  subst. exists q'. repeat split; eauto with lts.
- (* FreeOut *)
  destruct (Invert_Lts_FreeOut _ _ _ _ σ transition) as (c' & v' & q' & Heq1 & Heq2 & Heq3 & Heq4).
  apply Injective_Ren_Data in Heq1; [|apply Hinj].
  apply Injective_Ren_Data in Heq2; [|apply Hinj].
  subst. exists q'. repeat split; eauto with lts.
- (* BoundOut: contradiction *)
  simpl in Hbound. inversion Hbound.
- (* Tau *)
  replace (ren1 σ τ) with τ in transition by trivial.
  destruct (Invert_Lts_Tau _ _ σ Hinj transition) as (q' & Heq1 & Heq2).
  exists q'. split; eauto with lts. 
Qed.

End LTS_Renamings.

(* For some reason this makes asimple solve a goal??? *)
From stdpp Require strings.

Section LTS_Renamings.

Context {PiV : Pi_Values} {PiE : @Pi_Equations PiV}.

Lemma ren_lts : forall p 𝜆 q σ,
  Eq_Subst_Spec σ ->
  lts p 𝜆 q ->
  (is_bound_out 𝜆 = false ->
    lts (ren2 ids σ p) (ren1 σ 𝜆) (ren2 ids σ q)) /\
   (is_bound_out 𝜆 = true ->
    lts (ren2 ids σ p) (ren1 σ 𝜆) (ren2 ids (up_ren σ) q)).
  intros p 𝜆 q σ EqSpec Transition. revert σ EqSpec.
  induction Transition; intro σ; split; intro Hbound; inversion Hbound; subst.
  - asimpl. simpl. refine (eq_rect _ _ lts_input _ _). now asimpl.
  - apply lts_output.
  - apply lts_tau.
  - asimpl. simpl.
    assert (Heq: (pointwise_relation _ eq) (0 .: idsRen >> S) ids) by (intros [|n]; trivial).
    (* uses ren_proc_morphism to avoid functional extensionality *)
    rewrite Heq. clear Heq.
    replace (
    (subst_proc
      ((rec ren_proc ids σ P) .: (idsRen >> var_proc)) (σ >> var_Data) P))
    with (subst2 (rec (P⟨σ⟩) .: ids) ids (P ⟨σ⟩)) by now asimpl.
    apply lts_recursion.
  - apply lts_ifOne. apply (Eval_Eq_Spec E σ) in EqSpec. rewrite H in EqSpec. assumption.
  - apply lts_ifZero. apply (Eval_Eq_Spec E σ) in EqSpec. rewrite H in EqSpec. assumption.
  - destruct (IHTransition1 σ EqSpec) as [IHTransition1' _].
    destruct (IHTransition2 σ EqSpec) as [IHTransition2' _].
    eapply lts_comL.
    + apply IHTransition1'. reflexivity.
    + apply IHTransition2'. reflexivity.
  - destruct (IHTransition1 σ EqSpec) as [IHTransition1' _].
    destruct (IHTransition2 σ EqSpec) as [IHTransition2' _].
    eapply lts_comR.
    + apply IHTransition1'. reflexivity.
    + apply IHTransition2'. reflexivity.
  - destruct (IHTransition1 σ EqSpec) as [_ IHTransition1'].
    destruct (IHTransition2 (up_ren σ) (Eq_Subst_Spec_lift σ EqSpec)) as [IHTransition2' _].
    eapply (@lts_close_l (ren1 σ c)); fold ren_proc. (* giving the channel explicitly to avoid some unfolding *)
    + apply IHTransition1'. reflexivity.
    + unfold shift_op, Shift_proc; cbv beta.
      setoid_rewrite shift_permute.
      setoid_rewrite shift_permute_Data.
      apply IHTransition2'. reflexivity.
  - destruct (IHTransition1 σ EqSpec) as [_ IHTransition1'].
    destruct (IHTransition2 (up_ren σ) (Eq_Subst_Spec_lift σ EqSpec)) as [IHTransition2' _].
    eapply (@lts_close_r (ren1 σ c)); fold ren_proc. (* giving the channel explicitly to avoid some unfolding *)
    + apply IHTransition1'. reflexivity.
    + unfold shift_op, Shift_proc; cbv beta.
      setoid_rewrite shift_permute.
      setoid_rewrite shift_permute_Data.
      apply IHTransition2'. reflexivity.
  - destruct (IHTransition (up_ren σ) (Eq_Subst_Spec_lift σ EqSpec)) as [IHTransition' _].
    rewrite Hbound. asimpl.
    refine (eq_rect _ _ (lts_res _) _ _).
    * unfold shift_op. setoid_rewrite shift_permute_Action.
      apply IHTransition'.
      rewrite (is_bound_ren _ shift) in Hbound.
      apply Hbound.
    * setoid_rewrite <- (is_bound_ren _ σ). now rewrite Hbound.
  - destruct (IHTransition (up_ren σ) (Eq_Subst_Spec_lift σ EqSpec)) as [_ IHTransition'].
    rewrite Hbound. asimpl.
    refine (eq_rect _ _ (lts_res _) _ _).
    * unfold shift_op. setoid_rewrite shift_permute_Action.
      apply IHTransition'.
      rewrite (is_bound_ren _ shift) in Hbound.
      apply Hbound.
    * setoid_rewrite <- (is_bound_ren _ σ); rewrite Hbound. simpl. now asimpl.
  - destruct (IHTransition (up_ren σ) (Eq_Subst_Spec_lift σ EqSpec)) as [IHTransition' _].
    eapply lts_open; fold ren_proc.
    cbn in IHTransition'. asimpl in IHTransition'.
    now eapply IHTransition'.
  - destruct (IHTransition σ EqSpec) as [IHTransition' _].
    eapply lts_parL; fold ren_proc.
    + apply IHTransition'. exact Hbound.
    + rewrite Hbound. rewrite (is_bound_ren _ σ) in Hbound. now rewrite Hbound.
  - destruct (IHTransition σ EqSpec) as [_ IHTransition'].
    eapply lts_parL; fold ren_proc.
    + apply IHTransition'. exact Hbound.
    + rewrite Hbound. rewrite (is_bound_ren _ σ) in Hbound. rewrite Hbound.
      asimpl. simpl. reflexivity.
  - destruct (IHTransition σ EqSpec) as [IHTransition' _].
    eapply lts_parR; fold ren_proc.
    + apply IHTransition'. exact Hbound.
    + rewrite Hbound. rewrite (is_bound_ren _ σ) in Hbound. now rewrite Hbound.
  - destruct (IHTransition σ EqSpec) as [_ IHTransition'].
    eapply lts_parR; fold ren_proc.
    + apply IHTransition'. exact Hbound.
    + rewrite Hbound. rewrite (is_bound_ren _ σ) in Hbound. rewrite Hbound.
      asimpl. simpl. reflexivity.
  - destruct (IHTransition σ EqSpec) as [IHTransition' _].
    eapply lts_choiceL. apply IHTransition'. exact Hbound.
  - destruct (IHTransition σ EqSpec) as [_ IHTransition'].
    eapply lts_choiceL. apply IHTransition'. exact Hbound.
  - destruct (IHTransition σ EqSpec) as [IHTransition' _].
    eapply lts_choiceR. apply IHTransition'. exact Hbound.
  - destruct (IHTransition σ EqSpec) as [_ IHTransition'].
    eapply lts_choiceR. apply IHTransition'. exact Hbound.
Qed.

Lemma shift_transition p 𝜆 q :
  lts p 𝜆 q ->
  (is_bound_out 𝜆 = false ->
  lts (⇑ p) (⇑ 𝜆) (⇑ q))
  /\
  (is_bound_out 𝜆 = true ->
  lts (⇑ p) (⇑ 𝜆) (q ⟨up_ren shift⟩)).
Proof.
intro Transition.
apply (ren_lts p 𝜆 q shift (Eq_Subst_Spec_inj shift Shift_Injective)) in Transition.
assumption.
Qed.

Lemma swap_transition p 𝜆 q :
  lts p 𝜆 q ->
  (is_bound_out 𝜆 = false ->
  lts (p ⟨swap⟩) (ren1 swap 𝜆) (q ⟨swap⟩))
  /\
  (is_bound_out 𝜆 = true ->
  lts (p ⟨swap⟩) (ren1 swap 𝜆) (q ⟨up_ren swap⟩)).
Proof.
intro Transition.
apply (ren_lts p 𝜆 q swap (Eq_Subst_Spec_inj swap Swap_Injective)) in Transition.
assumption.
Qed.

End LTS_Renamings.
(* end hide *)
