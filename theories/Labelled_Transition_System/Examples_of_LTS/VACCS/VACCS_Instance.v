From stdpp Require Import gmap gmultiset.
From Stdlib.Program Require Import Equality.
From Stdlib.Wellfounded Require Import Inverse_Image.
From TestingTheory Require Import 
  ActTau InputOutputActions Clos_n InListPropHelper Subset_Act
  gLts Bisimulation Lts_OBA Lts_Finite_Output_Chain Lts_OBA_FB Lts_FW FiniteImageLTS
  Must InteractionBetweenLts MultisetLTSConstruction ParallelLTSConstruction ForwarderConstruction
  DefinitionAS Equivalence.
From TestingTheory Require Export VACCS.Congruence.


Module Type VACCS_lts.

Include VACCS_congruence.
(* State Transition System (STS-reduction) *)
Inductive sts : proc -> proc -> Prop :=
(*The axiomes*)
(* Communication of channels output and input that have the same name *)
| sts_com : forall {c v p2 g2}, 
    sts ((c ! v • 𝟘) ‖ ((c ? p2) + g2)) (𝟘 ‖ (p2 ^ v))
(* Nothing more , something less *)
| sts_tau : forall {p g}, 
    sts ((𝛕 • p) + g) p
(* Resursion *)
| sts_recursion : forall {x p}, 
    sts (rec x • p) (pr_subst x p (rec x • p))

(* The left parallele respect the Reduction *)
| sts_par : forall {p1 p2 q}, 
    sts p1 p2 ->
    sts (p1 ‖ q) (p2 ‖ q)

(* Restriction on Channel *)
| sts_res : forall {p1 p2}, 
    sts p1 p2 ->
    sts (ν p1) (ν p2)


(*The Congruence respects the Reduction *)
| sts_cong : forall {p1 p2 q2 q1},
    p1 ≡* p2 -> sts p2 q2 -> q2 ≡* q1 -> sts p1 q1
.

Hint Constructors sts:ccs.

Fixpoint Ѵ (n : nat) (P : proc) : proc :=
match n with 
| 0 => P
| S n => ν (Ѵ  n P)
end.

Fixpoint NewVarCn (k : nat) (n : nat) (P : proc) : proc :=
match n with 
| 0 => P
| S n => NewVarC k (NewVarCn k n P)
end.

Fixpoint gNewVarCn (k : nat) (n : nat) (P : gproc) : gproc :=
match n with 
| 0 => P
| S n => gNewVarC k (gNewVarCn k n P)
end.

Lemma cgr_res_n n P Q : P ≡* Q -> Ѵ  n P ≡* Ѵ  n Q.
Proof.
  revert P Q. induction n.
  - intros; eauto.
  - intros; simpl. eapply cgr_res. eauto.
Qed.

Lemma NewVarCn_revert_def n P k: NewVarCn k n (NewVarC k P) = NewVarC k (NewVarCn k n P).
Proof.
  revert P. induction n.
  - reflexivity.
  - intros; simpl in *. f_equal. eauto.
Qed.

Lemma VarC_add_zero c : VarC_add 0 c = c.
Proof.
  destruct c ; simpl ; eauto.
Qed.


Lemma VarC_add_revert_def k n c : VarC_add (k + n) c = (VarC_add k (VarC_add n c)).
Proof.
  revert n c. induction k; intros; simpl.
  + destruct c; simpl; eauto.
  + destruct c; simpl; eauto. f_equal. lia.
Qed.

Lemma cgr_res_scope_n n P Q : (Ѵ  n P) ‖ Q ≡* (Ѵ n (P ‖ NewVarCn 0 n Q)).
Proof.
  revert P Q.
  dependent induction n.
  - simpl. reflexivity.
  - intros. simpl. etrans. eapply cgr_res_scope_rev. eapply cgr_res.
    etrans. eapply IHn. eapply cgr_res_n. eapply cgr_fullpar. reflexivity.
    rewrite NewVarCn_revert_def. reflexivity.
Qed.

(* For the (STS-reduction), the reductible terms and reducted terms are pretty all the same, up to ≡* *)
Lemma ReductionShape : forall P Q, sts P Q ->
((exists c v P2 G2 S n , ((P ≡* Ѵ  n ((c ! v • 𝟘) ‖ ((c ? P2) + G2) ‖ S))) /\ (Q ≡* Ѵ  n ((𝟘 ‖ (P2^v)) ‖ S)))
\/ (exists P1 G1 S n, (P ≡* Ѵ  n (((𝛕 • P1) + G1) ‖ S)) /\ (Q ≡* Ѵ  n (P1 ‖ S)))
\/ (exists n P1 S n', (P ≡* Ѵ  n' ((rec n • P1) ‖ S)) /\ (Q ≡* Ѵ  n' (pr_subst n P1 (rec n • P1) ‖ S)))
).
Proof with auto with cgr.
  intros P Q Transition. induction Transition.
  - left. exists c. exists v. exists p2.
    exists g2. exists 𝟘. exists 0. split.
    * simpl. etrans. eapply cgr_par_nil_rev. eapply cgr_fullpar; reflexivity.
    * simpl. etrans. eapply cgr_par_nil_rev. eapply cgr_fullpar; reflexivity.
  - right. left. exists p. exists g0. exists 𝟘. exists 0. split.
    * simpl. eapply cgr_par_nil_rev.
    * simpl. eapply cgr_par_nil_rev.
  - right. right. exists x. exists p. exists 𝟘. exists 0. split.
    * simpl. eapply cgr_par_nil_rev.
    * simpl. eapply cgr_par_nil_rev.
  - destruct IHTransition as [IH|[IH|IH]];  decompose record IH. 
    * left. exists x. exists x0. exists x1. exists x2.
      exists (x3 ‖ NewVarCn 0 x4 q). exists x4. split; simpl.
      + etrans. apply cgr_par. eauto. etrans. eapply cgr_res_scope_n. eapply cgr_res_n. apply cgr_par_assoc.
      + etrans. apply cgr_par. eauto. etrans. eapply cgr_res_scope_n. eapply cgr_res_n. apply cgr_par_assoc.
    * right. left. exists x. exists x0. exists (x1 ‖ NewVarCn 0 x2 q). exists x2. split.
      + apply transitivity with (Ѵ x2 ((𝛕 • x + x0) ‖ x1) ‖ q). apply cgr_par. auto. etrans.
           eapply cgr_res_scope_n. eapply cgr_res_n. apply cgr_par_assoc.
      +  transitivity (Ѵ x2 (x ‖ x1) ‖ q). apply cgr_par. auto. etrans.
           eapply cgr_res_scope_n. eapply cgr_res_n. apply cgr_par_assoc.
    * right. right. exists x. exists x0. exists (x1 ‖ NewVarCn 0 x2 q). exists x2. split. 
      +  transitivity (Ѵ  x2 ((rec x • x0) ‖ x1) ‖ q). apply cgr_par. assumption.
           etrans. eapply cgr_res_scope_n. eapply cgr_res_n. apply cgr_par_assoc.
      +  transitivity (Ѵ  x2 (pr_subst x x0 (rec x • x0) ‖ x1) ‖ q). apply cgr_par. assumption. 
           etrans. eapply cgr_res_scope_n. eapply cgr_res_n. apply cgr_par_assoc.
  - destruct IHTransition as [IH|[IH|IH]]; decompose record IH. 
    * left. exists x. exists x0. exists x1. exists x2. exists x3. exists (S x4). split.
      + simpl. eapply cgr_res. eauto.
      + simpl. eapply cgr_res. eauto.
    * right. left. exists x. exists x0. exists x1. exists (S x2). split.
      + simpl. eapply cgr_res. eauto.
      + simpl. eapply cgr_res. eauto.
    * right. right. exists x. exists x0. exists x1. exists (S x2). split.
      + simpl. eapply cgr_res. eauto.
      + simpl. eapply cgr_res. eauto.
  - destruct IHTransition as [IH|[IH|IH]]; decompose record IH. 
    * left. exists x. exists x0. exists x1. exists x2. exists x3. exists x4. split.
      + apply cgr_trans with p2. exact H. exact H1.
      + apply cgr_trans with q2. apply cgr_symm. exact H0. exact H3.
    * right. left. exists x. exists x0. exists x1. exists x2. split.
      + apply cgr_trans with p2. exact H. exact H1.
      + apply cgr_trans with q2. apply cgr_symm. apply H0. apply H3.
    * right. right. exists x. exists x0. exists x1. exists x2. split.
      + apply cgr_trans with p2. exact H. exact H1.
      + apply cgr_trans with q2. apply cgr_symm. apply H0. apply H3.
Qed.

(* For the (LTS-transition), the transitable terms and transitted terms, that performs an INPUT,
are pretty all the same, up to ≡* *)
Lemma TransitionShapeForInput : forall P Q c v, (lts P ((c ⋉ v) ?) Q) -> 
(exists P1 G R n, ((P ≡* Ѵ  n (((VarC_add n c) ? P1 + G) ‖ R)) /\ (Q ≡* Ѵ  n (P1^v ‖ R))
  /\ ((exists L,P = (g L)) -> R = 𝟘 /\ n = 0))).
Proof.
intros P Q c v Transition.
 dependent induction Transition.
- exists P. exists 𝟘. exists 𝟘. exists 0. repeat split.
  * simpl. destruct c.
    + simpl. apply cgr_trans with ((c ? P) + 𝟘). apply cgr_trans with (c ? P).
      apply cgr_refl. apply cgr_choice_nil_rev. apply cgr_par_nil_rev.
    + simpl. apply cgr_trans with (((bvarC n) ? P) + 𝟘). apply cgr_trans with ((bvarC n) ? P).
      apply cgr_refl. apply cgr_choice_nil_rev. apply cgr_par_nil_rev.
  * apply cgr_par_nil_rev.
- destruct (IHTransition c v). reflexivity. decompose record H0.
  exists x. exists x0. exists x1. exists x2. split; try split.
  * apply cgr_trans with p. apply cgr_if_true. assumption. simpl. assumption.
  * assumption.
  * intros. inversion H3. inversion H5.
- destruct (IHTransition c v). reflexivity. decompose record H0.
  exists x. exists x0. exists x1. exists x2. split; try split.
  * apply cgr_trans with q. apply cgr_if_false. assumption. assumption.
  * assumption.
  * intros. inversion H3. inversion H5.
- destruct (IHTransition (VarC_add 1 c) v). reflexivity. decompose record H. exists x. exists x0.
  exists x1. exists (S x2). repeat split.
  * simpl. eapply cgr_res. rewrite<- VarC_add_revert_def in H1.
    replace (S x2)%nat with (x2 + 1)%nat by lia. exact H1.
  * simpl. eapply cgr_res. exact H0.
  * intros. inversion H2. inversion H4.
  * intros. inversion H2. inversion H4.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists x0.
  exists (x1 ‖ NewVarCn 0 x2 q). exists x2. repeat split.
  * apply cgr_trans with (Ѵ x2 ((((VarC_add x2 c) ? x) + x0) ‖ x1) ‖ q). apply cgr_par. assumption.
    etrans. eapply cgr_res_scope_n. eapply cgr_res_n. apply cgr_par_assoc.
  * apply cgr_trans with (Ѵ x2 (x^v ‖ x1) ‖ q). apply cgr_par. assumption. etrans.
    eapply cgr_res_scope_n. eapply cgr_res_n. apply cgr_par_assoc.
  * intros. inversion H2. inversion H4.
  * intros. inversion H2. inversion H4.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists x0. exists (x1 ‖ NewVarCn 0 x2 p). exists x2. repeat split.
  * apply cgr_trans with (Ѵ x2 ((((VarC_add x2 c) ? x) + x0) ‖ x1) ‖ p). apply cgr_trans with (q1 ‖ p).
    apply cgr_par_com. apply cgr_par. assumption. etrans. eapply cgr_res_scope_n. eapply cgr_res_n. apply cgr_par_assoc.
  * apply cgr_trans with (Ѵ x2 (x^v ‖ x1) ‖ p). apply cgr_trans with (q2 ‖ p). apply cgr_par_com. apply cgr_par. assumption.
    etrans. eapply cgr_res_scope_n. eapply cgr_res_n. apply cgr_par_assoc.
  * intros. inversion H2. inversion H4.
  * intros. inversion H2. inversion H4.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists (x0 + p2). exists 𝟘. exists 0. repeat split.
  * simpl. apply cgr_trans with ((c ? x) + (x0 + p2)). apply cgr_trans with (((c ? x) + x0) + p2).
    apply cgr_choice. assert (x1 = 𝟘 ∧ x2 = 0) as (eq1 & eq2). apply H3. exists p1. reflexivity. subst.
     transitivity (((c ? x) + x0) ‖ 𝟘). simpl in *. rewrite VarC_add_zero in H1. eauto.
    apply cgr_par_nil. apply cgr_choice_assoc. rewrite VarC_add_zero. apply cgr_par_nil_rev.
  * simpl. assert (x1 = 𝟘 ∧ x2 = 0) as (eq1 & eq2). apply H3. exists p1. reflexivity. subst. simpl in *. assumption.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists (x0 + p1). exists 𝟘. exists 0. repeat split.
  * simpl. apply cgr_trans with ((c ? x) + (x0 + p1)). apply cgr_trans with (((c ? x) + x0) + p1).
    etrans. eapply cgr_choice_com. apply cgr_choice. assert (x1 = 𝟘 ∧ x2 = 0) as (eq1 & eq2).
    apply H3. exists p2. reflexivity. subst.
     transitivity (((c ? x) + x0) ‖ 𝟘). simpl in *. rewrite VarC_add_zero in H1. eauto.
    apply cgr_par_nil. apply cgr_choice_assoc. rewrite VarC_add_zero. apply cgr_par_nil_rev.
  * simpl. assert (x1 = 𝟘 ∧ x2 = 0) as (eq1 & eq2). apply H3. exists p2. reflexivity. subst. simpl in *. assumption.
Qed.


Lemma guarded_does_no_output : forall p c v q, ¬ lts (g p) ((c ⋉ v) !) q.
Proof. intros. intro l. dependent induction l;eapply IHl; eauto. Defined.


(* For the (LTS-transition), the transitable terms and transitted terms, that performs an OUPUT,
are pretty all the same, up to ≡* *)
Lemma TransitionShapeForOutput : forall P Q c v, (lts P ((c ⋉ v) !) Q) -> 
(exists R n, (P ≡* (Ѵ  n (((VarC_add n c) ! v • 𝟘) ‖ R)) /\ (Q ≡* Ѵ  n (𝟘 ‖ R)))).
Proof.
intros P Q c v Transition.
 dependent induction Transition.
- exists 𝟘. exists 0. split; simpl; try rewrite VarC_add_zero.
  * apply cgr_par_nil_rev.
  * apply cgr_par_nil_rev.
- destruct (IHTransition c v). reflexivity. decompose record H0. exists x. exists x0. split; try split.
  * apply cgr_trans with p. apply cgr_if_true. assumption. assumption.
  * assumption.
- destruct (IHTransition c v). reflexivity. decompose record H0. exists x. exists x0. split; try split.
  * apply cgr_trans with q. apply cgr_if_false. assumption. assumption.
  * assumption.
- destruct (IHTransition (VarC_add 1 c) v). reflexivity. decompose record H. exists x.
  exists (S x0). repeat split.
  * simpl. eapply cgr_res. rewrite<- VarC_add_revert_def in H1.
    replace (S x0)%nat with (x0 + 1)%nat by lia. exact H1.
  * simpl. eapply cgr_res. exact H2.
- edestruct IHTransition;eauto. decompose record H. exists (x ‖ NewVarCn 0 x0 q). exists x0. split.
  * etrans. apply cgr_par. eassumption. etrans. eapply cgr_res_scope_n. eapply cgr_res_n. apply cgr_par_assoc.
  * etrans. apply cgr_par. eassumption. etrans. eapply cgr_res_scope_n. eapply cgr_res_n. apply cgr_par_assoc.
- edestruct IHTransition; eauto. decompose record H. exists (x ‖ NewVarCn 0 x0 p). exists x0. split.
  * etrans. eapply cgr_par_com. etrans. eapply cgr_par. eassumption. etrans. eapply cgr_res_scope_n.
    eapply cgr_res_n. apply cgr_par_assoc.
  * etrans. eapply cgr_par_com. etrans. eapply cgr_par. eassumption. etrans. eapply cgr_res_scope_n.
    eapply cgr_res_n. apply cgr_par_assoc.
- edestruct guarded_does_no_output. subst. eauto.
- edestruct guarded_does_no_output. subst. eauto.
Qed.

Lemma BigNew_reverse_def_one j p : (Ѵ j (ν p)) = ν (Ѵ j p).
Proof.
  revert p.
  induction j.
  - intros. simpl. eauto.
  - intros. simpl. rewrite IHj. eauto.
Qed.

Lemma BigNew_reverse_def k j p : Ѵ k (Ѵ j p) = Ѵ j (Ѵ k p).
Proof.
  revert j p.
  induction k.
  - intros; simpl; eauto.
  - intros; simpl in *. replace ((ν Ѵ k p)) with (Ѵ 1 (Ѵ k p)); eauto.
    rewrite<- (IHk 1) at 1. simpl. rewrite<- IHk. replace ((ν Ѵ k (Ѵ j p))) with (Ѵ 1 (Ѵ k (Ѵ j p))); eauto.
    rewrite<- (IHk 1). f_equal. simpl. rewrite BigNew_reverse_def_one. eauto.
Qed.

Lemma VarC_add_zero_ext μ : VarC_action_add 0 μ = μ.
Proof.
  destruct μ; destruct a; destruct c; simpl; eauto.
Qed.

Lemma NewVarCzero_and_add_Channel c : VarC_add 1 c = NewVar_in_ChannelData 0 c.
Proof.
  destruct c; simpl ;eauto.
Qed.

Definition NewVarC_in_ext (k : nat) (μ : ExtAct TypeOfActions) : ExtAct TypeOfActions :=
match μ with
| ActIn (c ⋉ v) => ActIn ((NewVar_in_ChannelData k c) ⋉ v)
| ActOut (c ⋉ v) => ActOut ((NewVar_in_ChannelData k c) ⋉ v)
end.

Lemma NewVarCzero_and_add μ : VarC_action_add 1 μ = NewVarC_in_ext 0 μ.
Proof.
  destruct μ; destruct a; simpl; rewrite NewVarCzero_and_add_Channel; eauto.
Qed.

Lemma NewVarC_and_NewVarC_in_ChannelData k j μ :
      NewVarC_in_ext j (NewVarC_in_ext (j + k) μ) = NewVarC_in_ext (j + (S k)) (NewVarC_in_ext j μ).
Proof.
  destruct μ; destruct a; simpl; rewrite NewVar_in_ChannelData_and_NewVar_in_ChannelData; eauto.
Qed.

Lemma inversion_res_n_lts k e1 μ e1' : lts (Ѵ k e1) (ActExt μ) e1' -> exists e'1, e1' = (Ѵ k e'1).
Proof.
  revert e1 μ e1'.
  induction k.
  + simpl; eauto.
  + intros; simpl in *. inversion H; subst. eapply IHk in H2 as (e'' & eq).
    subst. exists e''. eauto.
Qed.

Lemma inversion_res_ext k e1 μ e1' : lts (Ѵ k e1) (ActExt μ) (Ѵ k e1') -> lts e1 (ActExt (VarC_action_add k μ)) e1'.
Proof.
  revert e1 μ e1'.
  induction k.
  + simpl; eauto. intros. rewrite VarC_add_zero_ext. eauto.
  + intros; simpl in *. inversion H; subst. eapply IHk in H3.
    rewrite VarC_action_add_add in H3. replace (S k) with (k+1)%nat by lia.
    eauto.
Qed.

Lemma VarCadd_and_NewVarCn n c v : VarC_add n c ! v • 𝟘 = NewVarCn 0 n (c ! v • 𝟘).
Proof.
  revert c v.
  induction n.
  + destruct c; simpl;  eauto.
  + intros. replace (S n)%nat with (n + 1)%nat by lia.
    rewrite VarC_add_revert_def.
    rewrite (IHn (VarC_add 1 c) v). symmetry. etrans.
    replace (n + 1)%nat with (S n)%nat by lia. simpl in *.
    rewrite<- NewVarCn_revert_def. simpl. reflexivity.
    destruct c; eauto.
Qed.

Lemma simpl_NewVarC_nil n : NewVarCn 0 n 𝟘 = 𝟘.
Proof.
  induction n; simpl; subst; eauto. rewrite IHn. simpl. eauto.
Qed.

Lemma TransitionShapeForOutputSimplified : forall P Q c v, (lts P ((c ⋉ v) !) Q) 
                                        -> P ≡* ((c ! v • 𝟘) ‖ Q).
Proof.
  intros. assert (exists R n, (P ≡* Ѵ  n (((VarC_add n c) ! v • 𝟘) ‖ R)) /\ (Q ≡* Ѵ  n (𝟘 ‖ R))) as (R & n & eq1 & eq2).
  { apply TransitionShapeForOutput. assumption. }
  assert (Q ≡* Ѵ n R).
  { symmetry. etrans. eapply cgr_par_nil_rev. etrans. eapply cgr_res_scope_n.
    etrans. eapply cgr_res_n.  eapply cgr_par_com. symmetry. destruct n; simpl in *; eauto. rewrite simpl_NewVarC_nil. simpl. eauto. }
  assert ((VarC_add n c ! v • 𝟘) = NewVarCn 0 n (c ! v • 𝟘)) as eq.
  { eapply VarCadd_and_NewVarCn. }
  rewrite eq in eq1.
  assert (P ≡* (c ! v • 𝟘) ‖ Ѵ  n R).
  { symmetry. etrans. etrans. eapply cgr_par_com. eapply cgr_res_scope_n.
    etrans. eapply cgr_res_n. eapply cgr_par_com. symmetry. eauto. }
  symmetry. etrans. eapply cgr_par_com. etrans. eapply cgr_par. eauto.
  etrans. eapply cgr_par_com. symmetry. eauto.
Qed.

(* For the (LTS-transition), the transitable Guards and transitted terms, that performs a Tau ,
are pretty all the same, up to ≡* *)
Lemma TransitionShapeForTauAndGuard : forall P V, ((lts P τ V) /\ (exists L, P = (g L))) -> 
(exists Q M, ((P ≡* ((𝛕 • Q) + M))) /\ (V ≡* (Q))).
Proof.
intros P V Hyp. 
destruct Hyp. rename H into Transition. dependent induction Transition.
- exists P. exists 𝟘. split. 
  * apply cgr_choice_nil_rev.
  * apply cgr_refl.
- inversion H0. inversion H.
- inversion H0. inversion H1.
- inversion H0. inversion H1.
- inversion H0. inversion H.
- inversion H0. inversion H.
- inversion H0. inversion H.
- inversion H0. inversion H.
- inversion H0. inversion H.
- edestruct IHTransition. reflexivity. exists p1. reflexivity. destruct H. destruct H.  exists x. 
  exists (x0 + p2). split. apply cgr_trans with (((𝛕 • x) + x0) + p2).
  apply cgr_choice. assumption.
  apply cgr_choice_assoc. assumption.
- destruct IHTransition. reflexivity. exists p2. reflexivity. destruct H. destruct H.  exists x. 
  exists (x0 + p1). split. apply cgr_trans with (((𝛕 • x) + x0) + p1). apply cgr_trans with (p2 + p1). 
  apply cgr_choice_com. apply cgr_choice. assumption. apply cgr_choice_assoc. assumption.
Qed.

(* p 'is equivalent some r 'and r performs α to q *)
Definition sc_then_lts p α q := exists r, p ≡* r /\ (lts r α q).

(* p performs α to some r and this is equivalent to q*)
Definition lts_then_sc p α q := exists r, ((lts p α r) /\ r ≡* q).

Lemma Swap_Swap_Chan k c : VarSwap_in_ChannelData k (VarSwap_in_ChannelData k c) = c.
Proof.
  destruct c; simpl; eauto.
  destruct (decide (n = k)).
  + simpl. rewrite decide_False; try lia. subst.
    rewrite decide_True; try lia. eauto.
  + destruct (decide (n = S k)).
    * subst. simpl. rewrite decide_True; try lia. eauto.
    * simpl. rewrite decide_False; try lia.
      rewrite decide_False; try lia. eauto.
Qed.

Lemma Swap_Swap k p : VarSwap_in_proc k (VarSwap_in_proc k p) = p.
Proof.
  revert k.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros ; simpl in *.
  * assert (VarSwap_in_proc k (VarSwap_in_proc k p1) = p1) as eq1.
    { eapply Hp. simpl. lia. }
    assert (VarSwap_in_proc k (VarSwap_in_proc k p2) = p2) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto.
  * eauto.
  * assert (VarSwap_in_proc k (VarSwap_in_proc k p) = p) as eq.
    { eapply Hp. simpl. lia. }
    rewrite eq. eauto.
  * assert (VarSwap_in_proc k (VarSwap_in_proc k p1) = p1) as eq1.
    { eapply Hp. simpl. lia. }
    assert (VarSwap_in_proc k (VarSwap_in_proc k p2) = p2) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto.
  * rewrite Swap_Swap_Chan. eauto.
  * assert (VarSwap_in_proc (S k) (VarSwap_in_proc (S k) p) = p) as eq.
    { eapply Hp. simpl. lia. }
    rewrite eq. eauto.
  * destruct g0; simpl in *.
    + eauto.
    + eauto.
    + rewrite Swap_Swap_Chan.
      assert (VarSwap_in_proc k (VarSwap_in_proc k p) = p) as eq.
      { eapply Hp. simpl. lia. }
      rewrite eq. eauto.
    + assert (VarSwap_in_proc k (VarSwap_in_proc k p) = p) as eq.
      { eapply Hp. simpl. lia. }
      rewrite eq. eauto.
    + assert (VarSwap_in_proc k (VarSwap_in_proc k (g g0_1)) = (g g0_1)) as eq1.
      { eapply Hp. simpl. lia. }
      assert (VarSwap_in_proc k (VarSwap_in_proc k (g g0_2)) = (g g0_2)) as eq2.
      { eapply Hp. simpl. lia. }
      inversion eq1. inversion eq2. rewrite H0. rewrite H1. rewrite H0. rewrite H1. eauto.
Qed.

Lemma VarSwap_swap_proc p p' μ k : lts (VarSwap_in_proc k p) (ActExt (VarC_action_add (S (S k)) μ)) p' -> 
lts p (ActExt (VarC_action_add (S (S k)) μ)) (VarSwap_in_proc k p').
Proof.
  revert p' μ k.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *.
  + dependent destruction H.
    * simpl. rewrite Swap_Swap. eapply lts_parL. eapply Hp. simpl. lia. eauto.
    * simpl. rewrite Swap_Swap. eapply lts_parR. eapply Hp. simpl. lia. eauto.
  + inversion H.
  + inversion H.
  + dependent destruction H.
    * simpl. eapply lts_ifOne; eauto. eapply Hp. simpl. lia. eauto.
    * simpl. eapply lts_ifZero; eauto. eapply Hp. simpl. lia. eauto.
  + destruct c.
      - simpl in *. inversion H; subst. simpl. constructor.
      - simpl in *. destruct (decide (n = k)).
        ++ subst. inversion H; subst. destruct μ. 
           ++++ destruct a. simpl in *. inversion H3.
           ++++ destruct a. simpl in *. inversion H3. subst. destruct c.
                +++++ simpl in *. inversion H1.
                +++++ simpl in *. destruct n. 
                      ++++++ inversion H1. lia.
                      ++++++ inversion H1. lia.
        ++ destruct (decide (n = S k)).
           ++++ subst. inversion H; subst. destruct μ.
                +++++ destruct a. simpl in *. inversion H3.
                +++++ destruct a. simpl in *. inversion H3. subst. destruct c.
                      ++++++ inversion H1.
                      ++++++ inversion H1. lia.
           ++++ inversion H; subst. simpl. eapply lts_output.
  + dependent destruction H. rewrite VarC_action_add_add in H. simpl in H.
    eapply Hp in H; simpl ; try lia. replace (S (S (S k)))%nat with (1 + (S (S k)))%nat in H by lia.
    rewrite<- VarC_action_add_add in H. eapply lts_res_ext in H. eauto. 
  + destruct g0.
    * inversion H.
    * inversion H.
    * simpl in *. destruct c.
      - simpl in *. inversion H; subst. rewrite<- subst_and_VarSwap. rewrite Swap_Swap. eapply lts_input.
      - simpl in *. destruct (decide (n = k)).
        ++ subst. inversion H; subst. destruct μ. 
           ++++ destruct a. simpl in *. inversion H3. subst. destruct c.
                +++++ simpl in *. inversion H1.
                +++++ simpl in *. destruct n. 
                      ++++++ inversion H3. lia.
                      ++++++ inversion H1. lia.
           ++++ destruct a. simpl in *. inversion H3.
        ++ destruct (decide (n = S k)).
           ++++ subst. inversion H; subst. destruct μ. 
                +++++ destruct a. simpl in *. inversion H3. subst. destruct c.
                      ++++++ inversion H3.
                      ++++++ inversion H1. lia.
                +++++ destruct a. simpl in *. inversion H3.
           ++++ inversion H; subst. rewrite<- subst_and_VarSwap. rewrite Swap_Swap. eapply lts_input.
    * inversion H.
    * dependent destruction H.
      - simpl. eapply lts_choiceL. eapply Hp. simpl. lia. eauto.
      - simpl. eapply lts_choiceR. eapply Hp. simpl. lia. eauto.
Qed.

Lemma VarC_action_add_Swap k μ : 
      (VarC_action_add 1 (VarSwap_in_ext k μ) = VarSwap_in_ext (S k) (VarC_action_add 1 μ)).
Proof.
  destruct μ; destruct a; destruct c; simpl in *.
  + eauto.
  + destruct (decide (n = k)).
    - subst. rewrite decide_True; eauto.
    - destruct (decide (n = S k)); subst.
      ++ rewrite decide_False; eauto.
         rewrite decide_True; eauto.
      ++ rewrite decide_False; eauto.
         rewrite decide_False; eauto.
  + eauto.
  + destruct (decide (n = k)).
    - subst. rewrite decide_True; eauto.
    - destruct (decide (n = S k)); subst.
      ++ rewrite decide_False; eauto.
         rewrite decide_True; eauto.
      ++ rewrite decide_False; eauto.
         rewrite decide_False; eauto.
Qed.

Lemma VarSwap_swap2_proc p p' μ k : lts (VarSwap_in_proc k p) (ActExt μ) p' -> 
lts p (ActExt (VarSwap_in_ext k μ)) (VarSwap_in_proc k p').
Proof.
  revert p' μ k.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *.
  + dependent destruction H.
    * simpl. rewrite Swap_Swap. eapply lts_parL. eapply Hp. simpl. lia. eauto.
    * simpl. rewrite Swap_Swap. eapply lts_parR. eapply Hp. simpl. lia. eauto.
  + inversion H.
  + inversion H.
  + dependent destruction H.
    * simpl. eapply lts_ifOne; eauto. eapply Hp. simpl. lia. eauto.
    * simpl. eapply lts_ifZero; eauto. eapply Hp. simpl. lia. eauto.
  + destruct c.
      - simpl in *. inversion H; subst. eapply lts_output.
      - simpl in *. destruct (decide (n = k)).
        ++ subst. inversion H; subst. simpl. rewrite decide_False; try lia. rewrite decide_True; try lia.
           constructor.
        ++ destruct (decide (n = S k)).
           ++++ subst. inversion H; subst. simpl in *. rewrite decide_True; try lia.
                eapply lts_output.
           ++++ inversion H; subst. simpl in *.
                rewrite decide_False; try lia. rewrite decide_False; try lia. eapply lts_output.
  + dependent destruction H. simpl in *. eapply Hp in H; try lia.
    eapply lts_res_ext. rewrite VarC_action_add_Swap. eauto.
  + destruct g0.
    * inversion H.
    * inversion H.
    * simpl in *. destruct c.
      - simpl in *. inversion H; subst. rewrite<- subst_and_VarSwap. rewrite Swap_Swap. eapply lts_input.
      - simpl in *. destruct (decide (n = k)).
        ++ subst. inversion H; subst. rewrite<- subst_and_VarSwap. rewrite Swap_Swap.
           simpl in *. rewrite decide_False; try lia. rewrite decide_True; try lia. eapply lts_input.
        ++ destruct (decide (n = S k)).
           ++++ subst. inversion H; subst. simpl in *. rewrite decide_True; try lia.
                rewrite<- subst_and_VarSwap. rewrite Swap_Swap. eapply lts_input.
           ++++ inversion H; subst. rewrite<- subst_and_VarSwap. rewrite Swap_Swap. simpl in *.
                rewrite decide_False; try lia. rewrite decide_False; try lia. eapply lts_input.
    * inversion H.
    * dependent destruction H.
      - simpl. eapply lts_choiceL. eapply Hp. simpl. lia. eauto.
      - simpl. eapply lts_choiceR. eapply Hp. simpl. lia. eauto.
Qed.

Lemma NewVarC_preserves_transition k p μ q :
  lts p (ActExt μ) q -> lts (NewVarC k p) (ActExt (NewVarC_in_ext k μ)) (NewVarC k q).
Proof.
  revert k μ q. induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; simpl in *; intros.
  + inversion H; subst; simpl in *.
    - eapply lts_parL. eapply Hp; eauto. simpl. lia.
    - eapply lts_parR. eapply Hp; eauto. simpl. lia.
  + inversion H.
  + inversion H.
  + inversion H; subst; simpl in *.
    * eapply lts_ifOne; eauto. eapply Hp; eauto. simpl. lia.
    * eapply lts_ifZero; eauto. eapply Hp; eauto. simpl. lia.
  + inversion H; subst. simpl. eapply lts_output.
  + inversion H; subst; simpl in *.
    eapply lts_res_ext. rewrite NewVarCzero_and_add.
    assert (k = (0 + k))%nat as eq by lia. rewrite eq at 2.
    rewrite NewVarC_and_NewVarC_in_ChannelData. simpl. eapply Hp. lia. eauto.
  + destruct g0; simpl in *.
    * inversion H.
    * inversion H.
    * inversion H; subst. simpl. rewrite<- subst_and_NewVarC. eapply lts_input.
    * inversion H.
    * inversion H; subst; simpl in *.
      - eapply lts_choiceL. eapply Hp in H4; simpl; try lia. eauto.
      - eapply lts_choiceR. eapply Hp in H4; simpl; try lia. eauto.
Qed.

Lemma NewVarCn_preserves_transition k q μ q2 :
  lts q (ActExt μ) q2 -> lts (NewVarCn 0 k q) (ActExt (VarC_action_add k μ)) (NewVarCn 0 k q2).
Proof.
  revert μ q2 q. induction k.
  + intros. simpl; rewrite VarC_add_zero_ext. eauto.
  + intros; simpl in *. replace (S k)%nat with (1 + k)%nat; try lia.
    rewrite<- VarC_action_add_add. rewrite NewVarCzero_and_add. eapply NewVarC_preserves_transition.
    eapply IHk. eauto.
Qed.

Lemma NewVarC_preserves_reduction k p q :
  lts p τ q -> lts (NewVarC k p) τ (NewVarC k q).
Proof.
  revert k q. induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; simpl in *; intros.
  + inversion H; subst; simpl in *.
    - eapply NewVarC_preserves_transition in H2.
      eapply NewVarC_preserves_transition in H3.
      eapply lts_comL; eauto.
    - eapply NewVarC_preserves_transition in H2.
      eapply NewVarC_preserves_transition in H3.
      eapply lts_comR; eauto.
    - eapply lts_parL. eapply Hp; eauto. simpl. lia.
    - eapply lts_parR. eapply Hp; eauto. simpl. lia.
  + inversion H.
  + inversion H; subst. rewrite<- pr_subst_and_NewVarC. constructor.
  + inversion H; subst; simpl in *.
    * eapply lts_ifOne; eauto. eapply Hp; eauto. simpl. lia.
    * eapply lts_ifZero; eauto. eapply Hp; eauto. simpl. lia.
  + inversion H.
  + inversion H; subst; simpl in *.
    eapply lts_res_tau. eapply Hp. lia. eauto.
  + destruct g0; simpl in *.
    * inversion H.
    * inversion H.
    * inversion H.
    * inversion H; subst. constructor.
    * inversion H; subst; simpl in *.
      - eapply lts_choiceL. eapply Hp in H4; simpl; try lia. eauto.
      - eapply lts_choiceR. eapply Hp in H4; simpl; try lia. eauto.
Qed.

Lemma NewVarCn_preserves_reduction q q2 k :
  lts q τ q2 -> lts (NewVarCn 0 k q) τ (NewVarCn 0 k q2).
Proof.
  revert q q2. induction k.
  + intros. simpl;eauto.
  + intros; simpl in *. eapply NewVarC_preserves_reduction.
    eapply IHk. eauto.
Qed.

Lemma VarSwap_com_VarC_in_ChannelData k j c : (NewVar_in_ChannelData j (VarSwap_in_ChannelData (j + k) c) 
          = VarSwap_in_ChannelData (j + S k) (NewVar_in_ChannelData j c)).
Proof.
  destruct c; simpl.
  + eauto.
  + destruct (decide (n = (j + k)%nat)); subst.
    - rewrite decide_True; try lia. simpl.
      rewrite decide_True; try lia.
      rewrite decide_True; try lia. eauto.
    - destruct (decide (n = S (j + k))); subst.
      * simpl. rewrite decide_True; try lia.
        rewrite decide_True; try lia. simpl.
        rewrite decide_False; try lia.
        rewrite decide_True; try lia. eauto.
      * simpl. destruct (decide (j < S n)); subst.
        ++ simpl. rewrite decide_False; try lia.
           rewrite decide_False; try lia. eauto.
        ++ simpl. rewrite decide_False; try lia.
           rewrite decide_False; try lia. eauto.
Qed.

Lemma VarSwap_com_VarC k j p : (NewVarC j (VarSwap_in_proc (j + k) p) = VarSwap_in_proc (j + S k) (NewVarC j p)).
Proof.
  revert k j.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *.
  + assert (NewVarC j (VarSwap_in_proc (j + k) p1) = VarSwap_in_proc (j + S k) (NewVarC j p1)) as eq1.
    { eapply Hp. simpl. lia. }
    assert (NewVarC j (VarSwap_in_proc (j + k) p2) = VarSwap_in_proc (j + S k) (NewVarC j p2)) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto.
  + eauto.
  + f_equal. eapply Hp. lia.
  + assert (NewVarC j (VarSwap_in_proc (j + k) p1) = VarSwap_in_proc (j + S k) (NewVarC j p1)) as eq1.
    { eapply Hp. simpl. lia. }
    assert (NewVarC j (VarSwap_in_proc (j + k) p2) = VarSwap_in_proc (j + S k) (NewVarC j p2)) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto.
  + rewrite VarSwap_com_VarC_in_ChannelData. eauto.
  + f_equal. replace (S (j + k))%nat with ((S j) + k)%nat by lia.
    replace (S (j + S k))%nat with ((S j) + S k)%nat by lia.
    eapply Hp. lia.
  + destruct g0; simpl in *.
    - eauto.
    - eauto.
    - rewrite VarSwap_com_VarC_in_ChannelData.
      assert (NewVarC j (VarSwap_in_proc (j + k) p) = VarSwap_in_proc (j + S k) (NewVarC j p)) as eq.
      { eapply Hp. simpl. lia. }
      rewrite eq. eauto.
    - assert (NewVarC j (VarSwap_in_proc (j + k) p) = VarSwap_in_proc (j + S k) (NewVarC j p)) as eq.
      { eapply Hp. simpl. lia. }
      rewrite eq. eauto.
    - assert (NewVarC j (VarSwap_in_proc (j + k) (g g0_1)) = VarSwap_in_proc (j + S k) (NewVarC j (g g0_1))) as eq1.
      { eapply Hp. simpl. lia. }
      assert (NewVarC j (VarSwap_in_proc (j + k) (g g0_2)) = VarSwap_in_proc (j + S k) (NewVarC j (g g0_2))) as eq2.
      { eapply Hp. simpl. lia. } inversion eq1. inversion eq2. eauto.
Qed.

Lemma pr_subst_and_VarSwap2  (n : nat) (p : proc) (k : nat) (q : proc) : 
    pr_subst n (VarSwap_in_proc k p) (VarSwap_in_proc k q) =
    VarSwap_in_proc k (pr_subst n p q).
Proof.
  revert n k q.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *.
  + assert (pr_subst n (VarSwap_in_proc k p1) (VarSwap_in_proc k q) = VarSwap_in_proc k (pr_subst n p1 q)) as eq1.
    { eapply Hp. simpl. lia. }
    assert (pr_subst n (VarSwap_in_proc k p2) (VarSwap_in_proc k q) = VarSwap_in_proc k (pr_subst n p2 q)) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto.
  + destruct (decide (n0 = n)); simpl ; eauto.
  + destruct (decide (n0 = n)); simpl.
    - eauto.
    - assert (pr_subst n0 (VarSwap_in_proc k p) (VarSwap_in_proc k q) = VarSwap_in_proc k (pr_subst n0 p q)) as eq.
      { eapply Hp. simpl. lia. }
      rewrite eq. eauto.
  + assert (pr_subst n (VarSwap_in_proc k p1) (VarSwap_in_proc k q) = VarSwap_in_proc k (pr_subst n p1 q)) as eq1.
    { eapply Hp. simpl. lia. }
    assert (pr_subst n (VarSwap_in_proc k p2) (VarSwap_in_proc k q) = VarSwap_in_proc k (pr_subst n p2 q)) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto.
  + eauto.
  + f_equal. replace k with (0 + k)%nat by lia. rewrite VarSwap_com_VarC.
    simpl in *. eapply Hp. eauto.
  + destruct g0; simpl in *.
    * eauto.
    * eauto.
    * rewrite NewVar_and_VarSwap.
      assert (pr_subst n (VarSwap_in_proc k p) (VarSwap_in_proc k (NewVar 0 q))
          = VarSwap_in_proc k (pr_subst n p (NewVar 0 q))) as eq.
      { eapply Hp. simpl. lia. }
      rewrite eq. eauto.
    * assert (pr_subst n (VarSwap_in_proc k p) (VarSwap_in_proc k q)
          = VarSwap_in_proc k (pr_subst n p q)) as eq.
      { eapply Hp. simpl. lia. }
      rewrite eq. eauto.
    * assert (pr_subst n (VarSwap_in_proc k (g g0_1)) (VarSwap_in_proc k q) 
                  = VarSwap_in_proc k (pr_subst n (g g0_1) q)) as eq1.
      { eapply Hp. simpl. lia. }
      assert (pr_subst n (VarSwap_in_proc k (g g0_2)) (VarSwap_in_proc k q) 
                  = VarSwap_in_proc k (pr_subst n (g g0_2) q)) as eq2.
      { eapply Hp. simpl. lia. } inversion eq1. inversion eq2. eauto.
Qed.

Lemma VarSwap_swap_tau_proc p p' k : lts (VarSwap_in_proc k p) τ p' -> 
lts p τ (VarSwap_in_proc k p').
Proof.
  revert k p'.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *.
  * dependent destruction H; simpl in *.
    - eapply VarSwap_swap2_proc in H, H0. simpl in *. eapply lts_comL; eauto.
    - eapply VarSwap_swap2_proc in H, H0. simpl in *. eapply lts_comR; eauto.
    - rewrite Swap_Swap. eapply lts_parL. eapply Hp; simpl; eauto. lia.
    - rewrite Swap_Swap. eapply lts_parR. eapply Hp; simpl; eauto. lia.
  * inversion H.
  * dependent destruction H; simpl in *. rewrite<- pr_subst_and_VarSwap2.
    simpl in *. rewrite Swap_Swap. constructor.
  * dependent destruction H; simpl in *.
    - eapply lts_ifOne; eauto. eapply Hp; simpl; eauto. lia.
    - eapply lts_ifZero; eauto. eapply Hp; simpl; eauto. lia.
  * inversion H.
  * dependent destruction H; simpl in *.
    eapply lts_res_tau. eapply Hp; simpl; eauto.
  * destruct g0; simpl in *.
    - inversion H.
    - inversion H.
    - inversion H.
    - dependent destruction H; simpl in *. rewrite Swap_Swap. eapply lts_tau.
    - dependent destruction H; simpl in *.
      + eapply lts_choiceL. eapply Hp; simpl; eauto. lia.
      + eapply lts_choiceR. eapply Hp; simpl; eauto. lia.
Qed.

Lemma NewVarC_in_ChannelData_inv c c' k : NewVar_in_ChannelData k c = NewVar_in_ChannelData k c' -> c = c'.
Proof.
  destruct c; destruct c'; simpl; eauto; intro Hyp.
  + destruct (decide (k < S n)); inversion Hyp.
  + destruct (decide (k < S n)); inversion Hyp.
  + destruct (decide (k < S n)); destruct (decide (k < S n0)).
    - inversion Hyp. eauto.
    - inversion Hyp. lia.
    - inversion Hyp. lia.
    - eauto.
Qed.

Lemma NewVarC_in_ext_inv μ μ' k : NewVarC_in_ext k μ = NewVarC_in_ext k μ' -> μ = μ'.
Proof.
  destruct μ; destruct μ'; destruct a; destruct a0; simpl in *; intro Hyp; inversion Hyp; subst;
  eapply NewVarC_in_ChannelData_inv in H0 ; subst; eauto.
Qed.

Lemma NewVarC_in_ext_rev_Input c v μ' k : ActIn (c ⋉ v) = NewVarC_in_ext k μ' 
    -> exists c' v', μ' = ActIn (c' ⋉ v') /\ v = v' /\ NewVar_in_ChannelData k c' = c.
Proof.
  destruct μ'; destruct c; destruct a; simpl in * ; intro Hyp; try (inversion Hyp); subst.
  + exists c0. exists d. split ;eauto.
  + exists c. exists d. split ;eauto.
Qed.

Lemma NewVarC_in_ext_rev_Output c v μ' k : ActOut (c ⋉ v) = NewVarC_in_ext k μ' 
    -> exists c' v', μ' = ActOut (c' ⋉ v') /\ v = v' /\ NewVar_in_ChannelData k c' = c.
Proof.
  destruct μ'; destruct c; destruct a; simpl in * ; intro Hyp; try (inversion Hyp); subst.
  + exists c0. exists d. split ;eauto.
  + exists c. exists d. split ;eauto.
Qed.

Lemma NewVarC_inv p p' k : NewVarC k p = NewVarC k p' -> p = p'.
Proof.
  revert p' k.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)); destruct p; 
    destruct p'; simpl in *; eauto; intros k Hyp ; try (inversion Hyp).
  + eapply Hp in H0; subst; try lia.
    eapply Hp in H1; subst; try lia. eauto.
  + subst. f_equal. eauto.
  + subst. eapply Hp in H1; subst; try lia.
    eapply Hp in H2; subst; try lia. eauto.
  + eapply NewVarC_in_ChannelData_inv in H0. subst. reflexivity.
  + f_equal. eapply Hp in H0; eauto ; try lia.
  + destruct g0; destruct g1; simpl in *; eauto; try (inversion Hyp).
    - eapply Hp in H2; subst; eauto. eapply NewVarC_in_ChannelData_inv in H1. subst; eauto.
    - eapply Hp in H1; subst; eauto.
    - assert (NewVarC k (g g0_1) = NewVarC k (g g1_1)); simpl; eauto. inversion H1; eauto.
      assert (NewVarC k (g g0_2) = NewVarC k (g g1_2)); simpl; eauto. inversion H2; eauto.
      eapply Hp in H; simpl ; try lia. eapply Hp in H3; simpl ; try lia. inversion H. inversion H3. subst. eauto.
Qed.

Lemma inversion_k_NewVarC k μ μ' : NewVarC_in_ext 0 μ = NewVarC_in_ext (S k) μ' 
  -> NewVarC_in_ext 0 μ = μ' \/ (exists μ'0, μ = NewVarC_in_ext k μ'0).
Proof.
  intro Hyp.
  destruct μ; destruct a; destruct μ'; destruct a; destruct c; destruct c0; simpl in *; subst; try (inversion Hyp).
    + subst. right. exists (ActIn (c0 ⋉ d0)). simpl; eauto.
    + destruct (decide ((S k < S n))); inversion H0.
    + destruct (decide ((S k < S n0))).
      - subst. inversion H0. subst. right. inversion l.
        ++ subst. exists (ActIn (k ⋉ d0)). simpl; eauto. rewrite decide_True; try lia. eauto.
        ++ subst. assert (0 < n0); try lia. assert (0 < n0); try lia. eapply Nat.succ_pred_pos in H. exists (ActIn (Nat.pred n0 ⋉ d0)).
           simpl. rewrite decide_True; try lia. f_equal. f_equal. eapply Nat.succ_pred_pos in H2. eauto.
      - subst. inversion H0. subst. left; eauto.
    + subst. left. eauto.
    + destruct (decide ((S k < S n))); inversion H0.
    + destruct (decide ((S k < S n0))).
      - subst. inversion H0. subst. right. inversion l.
        ++ subst. exists (ActOut (k ⋉ d0)). simpl; eauto. rewrite decide_True; try lia. eauto.
        ++ subst. assert (0 < n0); try lia. assert (0 < n0); try lia. eapply Nat.succ_pred_pos in H. exists (ActOut (Nat.pred n0 ⋉ d0)).
           simpl. rewrite decide_True; try lia. f_equal. f_equal. eapply Nat.succ_pred_pos in H2. eauto.
      - subst. inversion H0. subst. left; eauto.
Qed.

Lemma NewVarC_ext_proc p μ p' k : lts (NewVarC k p) (ActExt μ)  p' -> 
exists μ' p'', μ = NewVarC_in_ext k μ' /\ p' = (NewVarC k p'').
Proof.
  revert μ p' k.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *.
  * dependent destruction H; simpl in *.
    - eapply Hp in H as (μ' & p'' & eq' & eq'') ; simpl; subst ; try lia.
      exists μ'. exists (p'' ‖  p2). split; eauto.
    - eapply Hp in H as (μ' & p'' & eq' & eq'') ; simpl; subst ; try lia.
      exists μ'. exists (p1 ‖  p''). split; eauto.
  * inversion H.
  * inversion H.
  * dependent destruction H; simpl in *.
    - eapply Hp in H0 as (μ' & p'' & eq' & eq'') ; simpl; subst ; try lia.
      exists μ'. exists p''. split; eauto.
    - eapply Hp in H0 as (μ' & p'' & eq' & eq'') ; simpl; subst ; try lia.
      exists μ'. exists p''. split; eauto.
  * inversion H; subst. exists (ActOut (c ⋉ d)). exists 𝟘.
    split; eauto.
  * dependent destruction H; simpl in *.
    eapply Hp in H as (μ' & p'' & eq' & eq'') ; simpl; subst ; try lia.
    rewrite NewVarCzero_and_add in eq'.
    assert (NewVarC_in_ext 0 μ = NewVarC_in_ext (S k) μ'); eauto.
    eapply inversion_k_NewVarC in eq'. destruct eq' as [case1 | (μ'0 & case2)]; subst.
    + replace (S k) with (0 + S k)%nat in H by lia.
      rewrite<- NewVarC_and_NewVarC_in_ChannelData in H. simpl in *.
      exists μ. exists (ν p''). split. eapply NewVarC_in_ext_inv in H. eauto.
      simpl. eauto.
    + exists μ'0. exists (ν p''). split; eauto.
  * destruct g0; simpl in *.
    - inversion H.
    - inversion H.
    - inversion H; subst. exists (ActIn (c ⋉ v)). exists (p ^ v).
      split ;eauto. rewrite subst_and_NewVarC. eauto.
    - inversion H.
    - dependent destruction H; simpl in *.
      + assert (lts (NewVarC k (g g0_1)) (ActExt μ) q) as Hyp; eauto.
        eapply Hp in Hyp as (μ' & p'' & eq' & eq'') ; simpl; subst ; try lia.
        exists μ'. exists p''. split; eauto.
      + assert (lts (NewVarC k (g g0_2)) (ActExt μ) q) as Hyp; eauto.
        eapply Hp in Hyp as (μ' & p'' & eq' & eq'') ; simpl; subst ; try lia.
        exists μ'. exists p''. split; eauto.
Qed.

Lemma NewVarC_tau_proc p p' k : lts (NewVarC k p) τ p' ->
 exists p'', p' = NewVarC k p''.
Proof.
  revert k p'.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *.
  * dependent destruction H; simpl in *.
    - assert (lts (NewVarC k p1) ((c ⋉ v) !) p3); eauto. assert (lts (NewVarC k p2) ((c ⋉ v) ?) q2); eauto.
      eapply NewVarC_ext_proc in H as (μ' & p'' & eq' & eq'') ; simpl; subst ; try lia.
      eapply NewVarC_ext_proc in H0 as (μ'' & p''' & eq'' & eq''') ; simpl; subst ; try lia.
      exists (p'' ‖  p'''). split; eauto.
    - assert (lts (NewVarC k p2) ((c ⋉ v) !) p3); eauto. assert (lts (NewVarC k p1) ((c ⋉ v) ?) q2); eauto.
      eapply NewVarC_ext_proc in H as (μ' & p'' & eq' & eq'') ; simpl; subst ; try lia.
      eapply NewVarC_ext_proc in H0 as (μ'' & p''' & eq'' & eq''') ; simpl; subst ; try lia.
      exists (p''' ‖  p''). split; eauto.
    - eapply Hp in H as (p'' & eq'') ; simpl; subst ; try lia.
      exists (p'' ‖  p2). split; eauto.
    - eapply Hp in H as (p'' & eq'') ; simpl; subst ; try lia.
      exists (p1 ‖  p''). split; eauto.
  * inversion H.
  * inversion H ; subst. exists (pr_subst n p (rec n • p)).
    rewrite<- pr_subst_and_NewVarC. simpl; eauto.
  * dependent destruction H; simpl in *.
    - eapply Hp in H0 as (p'' & eq'') ; simpl; subst ; try lia.
      exists p''. split; eauto.
    - eapply Hp in H0 as (p'' & eq'') ; simpl; subst ; try lia.
      exists p''. split; eauto.
  * inversion H.
  * dependent destruction H; simpl in *.
    eapply Hp in H as (p'' & eq'') ; simpl; subst ; try lia.
    exists (ν p''). simpl ; eauto.
  * destruct g0; simpl in *.
    - inversion H.
    - inversion H.
    - inversion H.
    - inversion H; subst. exists p. auto.
    - dependent destruction H; simpl in *.
      + assert (lts (NewVarC k (g g0_1)) τ q) as Hyp; eauto.
        eapply Hp in Hyp as (p'' & eq'') ; simpl; subst ; try lia.
        exists p''. split; eauto.
      + assert (lts (NewVarC k (g g0_2)) τ q) as Hyp; eauto.
        eapply Hp in Hyp as (p'' & eq'') ; simpl; subst ; try lia.
        exists p''. split; eauto.
Qed.

Lemma NewVarC_ext_proc_rev p μ' p' k : lts (NewVarC k p) (ActExt (NewVarC_in_ext k μ')) (NewVarC k p') -> 
lts p (ActExt μ') p'.
Proof.
  revert μ' k p'.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *.
  * dependent destruction H; simpl in *; subst.
    - assert (lts (NewVarC k p1) (ActExt (NewVarC_in_ext k μ')) p3) ; eauto.
      eapply NewVarC_ext_proc in H as (μ'' & p'' & eq' & eq''); subst.
      eapply Hp in H0; try lia. assert (NewVarC k (p'' ‖ p2) = NewVarC k p') as Hyp'; eauto.
      eapply NewVarC_inv in Hyp'. subst. eapply lts_parL. eauto.
    - assert (lts (NewVarC k p2) (ActExt (NewVarC_in_ext k μ')) q2) ; eauto.
      eapply NewVarC_ext_proc in H as (μ'' & p'' & eq' & eq''); subst. eapply Hp in H0; try lia.
      assert (NewVarC k (p1 ‖ p'') = NewVarC k p') as Hyp'; eauto.
      eapply NewVarC_inv in Hyp'. subst. eapply lts_parR. eauto.
  * inversion H.
  * inversion H.
  * dependent destruction H; simpl in *.
    - eapply lts_ifOne; eauto. eapply Hp; simpl; eauto. lia.
    - eapply lts_ifZero; eauto. eapply Hp; simpl; eauto. lia.
  * inversion H; subst. assert (NewVarC_in_ext k (ActOut (c ⋉ d)) = NewVarC_in_ext k μ') as Hyp; eauto.
    eapply NewVarC_in_ext_inv in Hyp. subst. replace (g 𝟘) with (NewVarC k (g 𝟘)) in H4 by eauto.
    eapply NewVarC_inv in H4. subst. eapply lts_output.
  * dependent destruction H; simpl in *. rewrite NewVarCzero_and_add in H. assert (0 + k = k)%nat as eq by lia.
    rewrite<- eq in H at 2. rewrite NewVarC_and_NewVarC_in_ChannelData in H. simpl in *.
    assert (lts (NewVarC (S k) p) (ActExt (NewVarC_in_ext (S k) (NewVarC_in_ext 0 μ'))) p'0) ;eauto.
    eapply NewVarC_ext_proc in H as (μ'' & p'' & eq1 & eq2). subst.
    eapply NewVarC_in_ext_inv in eq1. subst. assert (NewVarC k (ν p'') = NewVarC k p'); eauto.
    eapply NewVarC_inv in H. subst. eapply lts_res_ext. eapply Hp in H0; try lia. rewrite NewVarCzero_and_add. eauto.
  * destruct g0; simpl in *.
    - inversion H.
    - inversion H.
    - inversion H; subst. assert (NewVarC_in_ext k (ActIn (c ⋉ v)) = NewVarC_in_ext k μ') as Hyp; eauto.
      eapply NewVarC_in_ext_inv in Hyp. subst. rewrite subst_and_NewVarC in H4.
      eapply NewVarC_inv in H4. subst. eapply lts_input.
    - inversion H.
    - dependent destruction H; simpl in *.
      + assert (lts (NewVarC k (g g0_1)) (ActExt (NewVarC_in_ext k μ')) (NewVarC k p')); eauto.
        eapply Hp in H0; simpl; try lia. eapply lts_choiceL. eauto.
      + assert (lts (NewVarC k (g g0_2)) (ActExt (NewVarC_in_ext k μ')) (NewVarC k p')); eauto.
        eapply Hp in H0; simpl; try lia. eapply lts_choiceR. eauto.
Qed.

Lemma inversion_NewVarC_par p1 p2 p3 k : p1 ‖ NewVarC k p2 = NewVarC k p3 -> exists p', p1 = NewVarC k p'.
Proof.
  destruct p3; intro Hyp ; simpl in *; try (inversion Hyp).
  exists p3_1; eauto.
Qed.

Lemma inversion_NewVarC_par2 p1 p2 p3 k : NewVarC k p2 ‖ p1  = NewVarC k p3 -> exists p', p1 = NewVarC k p'.
Proof.
  destruct p3; intro Hyp ; simpl in *; try (inversion Hyp).
  exists p3_2; eauto.
Qed.

Lemma NewVarC_tau_proc_rev p p' k : lts (NewVarC k p) τ (NewVarC k p') -> 
lts p τ p'.
Proof.
  revert k p'.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *.
  * dependent destruction H; simpl in *; subst.
    - assert (lts (NewVarC k p1) ((c ⋉ v) !) p3); eauto. assert (lts (NewVarC k p2) ((c ⋉ v) ?) q2); eauto.
      eapply NewVarC_ext_proc in H as (μ' & p'' & eq1 & eq2); subst.
      eapply NewVarC_ext_proc in H0 as (μ'' & p''' & eq'1 & eq'2); subst.
      rewrite eq1 in H1. rewrite eq'1 in H2.
      eapply NewVarC_ext_proc_rev in H1.
      eapply NewVarC_ext_proc_rev in H2.
      assert (NewVarC k (p'' ‖ p''') = NewVarC k p'); eauto.
      eapply NewVarC_inv in H. subst. eapply NewVarC_in_ext_rev_Output in eq1 as (c' & v' & eq'' & eq''' & eq'''').
      subst. eapply NewVarC_in_ext_rev_Input in eq'1 as (c'' & v'' & eq'' & eq''' & eq'''').
      subst. eapply NewVarC_in_ChannelData_inv in eq''''. subst. eapply lts_comL; eauto.
    - assert (lts (NewVarC k p2) ((c ⋉ v) !) p3); eauto. assert (lts (NewVarC k p1) ((c ⋉ v) ?) q2); eauto.
      eapply NewVarC_ext_proc in H as (μ' & p'' & eq1 & eq2); subst.
      eapply NewVarC_ext_proc in H0 as (μ'' & p''' & eq'1 & eq'2); subst.
      rewrite eq1 in H1. rewrite eq'1 in H2.
      eapply NewVarC_ext_proc_rev in H1.
      eapply NewVarC_ext_proc_rev in H2.
      assert (NewVarC k (p''' ‖ p'') = NewVarC k p'); eauto.
      eapply NewVarC_inv in H. subst. eapply NewVarC_in_ext_rev_Output in eq1 as (c' & v' & eq'' & eq''' & eq'''').
      subst. eapply NewVarC_in_ext_rev_Input in eq'1 as (c'' & v'' & eq'' & eq''' & eq'''').
      subst. eapply NewVarC_in_ChannelData_inv in eq''''. subst. eapply lts_comR; eauto.
    - assert (lts (NewVarC k p1) τ p3); eauto. assert (exists p', p3 = NewVarC k p') as (p'1 & eq); subst.
      { eapply inversion_NewVarC_par. eauto. } assert (NewVarC k (p'1 ‖ p2) = NewVarC k p'); eauto.
      eapply NewVarC_inv in H1; subst. eapply lts_parL. eapply Hp; eauto. simpl; lia.
    - assert (lts (NewVarC k p2) τ q2); eauto. assert (exists p', q2 = NewVarC k p') as (p'1 & eq); subst.
      { eapply inversion_NewVarC_par2. eauto. } assert (NewVarC k (p1 ‖ p'1) = NewVarC k p'); eauto.
      eapply NewVarC_inv in H1; subst. eapply lts_parR. eapply Hp; eauto. simpl; lia.
  * inversion H.
  * dependent destruction H; simpl in *. replace (rec n • NewVarC k p) with (NewVarC k (rec n •  p)) in x; eauto.
    rewrite pr_subst_and_NewVarC in x. eapply NewVarC_inv in x. subst. constructor.
  * dependent destruction H; simpl in *.
    - eapply lts_ifOne; eauto. eapply Hp; simpl; eauto. lia.
    - eapply lts_ifZero; eauto. eapply Hp; simpl; eauto. lia.
  * inversion H.
  * dependent destruction H; simpl in *.
    assert (lts (NewVarC (S k) p) τ p'0); eauto.
    eapply NewVarC_tau_proc in H as (p'' & eq); subst.
    assert (NewVarC k (ν p'') = NewVarC k p') as Hyp; eauto.
    eapply NewVarC_inv in Hyp. subst. eapply lts_res_tau. eapply Hp; eauto.
  * destruct g0; simpl in *.
    - inversion H.
    - inversion H.
    - inversion H.
    - dependent destruction H; simpl in *. eapply NewVarC_inv in x. subst. constructor.
    - dependent destruction H; simpl in *.
      + assert (lts (NewVarC k (g g0_1)) τ (NewVarC k p')); eauto. eapply lts_choiceL. eapply Hp; simpl; eauto. lia.
      + assert (lts (NewVarC k (g g0_2)) τ (NewVarC k p')); eauto. eapply lts_choiceR. eapply Hp; simpl; eauto. lia.
Qed.


(* p 'is equivalent some r 'and r performs α to q , the congruence and the Transition 
  can be reversed : *)
Lemma Congruence_Respects_Transition  : forall p q α, sc_then_lts p α q -> lts_then_sc p α q.
Proof. 
(* by induction on the congruence and the step then...*)
  intros p q α (p' & hcgr & l).
  revert q α l.
  dependent induction hcgr.
  - dependent induction H. 
(* reasonning about all possible cases due to the structure of terms *)
    + intros. exists q.  split.  exact l. reflexivity.
    + intros. exists q0.  split. eapply lts_ifOne; eauto. reflexivity.
    + intros. dependent destruction l.
      -- exists p'. split; eauto. reflexivity.
      -- eauto. rewrite H in H0. inversion H0.
    + intros. exists q0.  split. eapply lts_ifZero; eauto. reflexivity.
    + intros. dependent destruction l.
      -- eauto. rewrite H in H0. inversion H0.
      -- exists q'. split; eauto. reflexivity.
    + intros. exists (q ‖ 𝟘). split. apply lts_parL. assumption. auto with cgr (*par contexte parallele*). 
    + intros. dependent destruction l. inversion l2. inversion l1. exists p2. split. exact l. auto with cgr. 
      inversion l.
    + intros. dependent destruction l.
      -- exists (q2 ‖ p2). split. eapply lts_comR. instantiate (1:= v). instantiate (1:= c). exact l1. exact l2. auto with cgr.
      -- exists (p2 ‖ q2). split. eapply lts_comL. instantiate (1:= v). instantiate (1:= c). exact l1. exact l2. auto with cgr.
      -- exists (p ‖ p2). split. apply lts_parR. assumption. auto with cgr.
      -- exists (q2 ‖ q). split. apply lts_parL. assumption. auto with cgr.
    + intros. dependent destruction l.
      -- dependent destruction l2. 
         * exists ((p2 ‖ p0) ‖ r). split.
           apply lts_parL. eapply lts_comL. instantiate (1:= v). instantiate (1:= c). assumption. assumption. auto with cgr.
         * exists ((p2 ‖ q) ‖ q2). split. eapply lts_comL. instantiate (1:= v). instantiate (1:= c). apply lts_parL. assumption. assumption.
           apply cgr_par_assoc.
      -- dependent destruction l1. 
         * exists ((q2 ‖ p2) ‖ r). split. apply lts_parL. eapply lts_comR. instantiate (1:= v). instantiate (1:= c). assumption.
           assumption. auto with cgr.
         * exists ((q2 ‖ q) ‖ q0). split. eapply lts_comR. instantiate (1:= v). instantiate (1:= c). assumption. apply lts_parL.
           assumption. auto with cgr.
      -- exists ((p2 ‖ q) ‖ r). split. apply lts_parL. apply lts_parL. assumption. auto with cgr.
      -- dependent destruction l.
         * exists ((p ‖ p2) ‖ q2). split. eapply lts_comL. instantiate (1:= v). instantiate (1:= c). apply lts_parR. assumption. assumption.
           auto with cgr.
         * exists ((p ‖ q2) ‖ p2). split. eapply lts_comR. instantiate (1:= v). instantiate (1:= c). assumption. apply lts_parR.
           assumption. auto with cgr.
         * exists ((p ‖ p2) ‖ r). split. apply lts_parL. apply lts_parR. assumption. auto with cgr.
         * exists ((p ‖ q) ‖ q2). split. apply lts_parR. assumption. auto with cgr.
    + intros. dependent destruction l.
      -- dependent destruction l1. 
         * exists (p2 ‖ (q ‖ q2)). split.
           eapply lts_comL. instantiate (1:= v). instantiate (1:= c). assumption. apply lts_parR. assumption. auto with cgr.
         * exists (p ‖ (q0 ‖ q2)). split. apply lts_parR. eapply lts_comL. instantiate (1:= v). instantiate (1:= c). assumption.
           assumption. auto with cgr.
      -- dependent destruction l2. 
         * exists (p0 ‖ (q ‖ p2)). split. eapply lts_comR. instantiate (1:= v). instantiate (1:= c). apply lts_parR. assumption.
           assumption. auto with cgr.
         * exists (p ‖ (q2 ‖ p2)). split. apply lts_parR.  eapply lts_comR. instantiate (1:= v). instantiate (1:= c). assumption.
           assumption. auto with cgr.
      -- dependent destruction l.
         * exists (p2 ‖ (q2 ‖ r)). split. eapply lts_comL. instantiate (1:= v). instantiate (1:= c).  assumption. apply lts_parL.
           assumption. auto with cgr.
         * exists (q2 ‖ (p2 ‖ r)). split. eapply lts_comR. instantiate (1:= v). instantiate (1:= c). apply lts_parL. assumption.
           assumption. auto with cgr.
         * exists (p2 ‖ ( q ‖ r)). split. apply lts_parL. assumption. auto with cgr.
         * exists (p ‖ (q2 ‖ r)). split. apply lts_parR. apply lts_parL. assumption. auto with cgr.
      -- exists (p ‖ (q ‖ q2)). split. apply lts_parR.  auto. apply lts_parR. assumption. auto with cgr.
    + intros. inversion l.
    + intros. inversion l; subst.
      -- inversion H0.
      -- inversion H0.
    + intros. dependent destruction l.
      -- dependent destruction l. exists ((ν (ν VarSwap_in_proc 0 p'))). split.
         eapply lts_res_ext. eapply lts_res_ext. rewrite VarC_action_add_add in l. simpl in *.
         eapply VarSwap_swap_proc in l. rewrite VarC_action_add_add. simpl in *. eauto. eapply cgr_res_swap_rev.
      -- dependent destruction l. exists ((ν (ν VarSwap_in_proc 0 p'))). split. eapply lts_res_tau.
         eapply lts_res_tau. eapply VarSwap_swap_tau_proc. eauto. eapply cgr_res_swap_rev.
    + intros. dependent destruction l.
      -- dependent destruction l. exists ((ν (ν VarSwap_in_proc 0 p'))). split.
         eapply lts_res_ext. eapply lts_res_ext. rewrite VarC_action_add_add. simpl.
         eapply VarSwap_swap_proc. rewrite Swap_Swap. rewrite VarC_action_add_add in l. simpl in *.
         eauto. eapply cgr_res_swap_rev.
      -- dependent destruction l. exists ((ν (ν VarSwap_in_proc 0 p'))). split. eapply lts_res_tau.
         eapply lts_res_tau. eapply VarSwap_swap_tau_proc. rewrite Swap_Swap. eauto. eapply cgr_res_swap_rev.
    + intros. dependent destruction l.
      -- inversion l1; subst. simpl in *. eapply (NewVarC_preserves_transition 0) in l2.
         rewrite NewVarCzero_and_add_Channel in H1. simpl in *.
         exists (ν (p' ‖ (NewVarC 0 q2))). split. eapply lts_res_tau.
         eapply lts_comL; eauto. eapply cgr_res_scope.
      -- inversion l2; subst. simpl in *. eapply (NewVarC_preserves_transition 0) in l1. simpl in *.
         exists (ν (p' ‖ (NewVarC 0 p2))). split. eapply lts_res_tau.
         eapply lts_comR; eauto. eapply cgr_res_scope.
      -- dependent destruction l.
         * exists (ν (p' ‖ NewVarC 0 q)). split. eapply lts_res_ext. eapply lts_parL. eauto.
           eapply cgr_res_scope.
         * exists (ν (p' ‖ NewVarC 0 q)). split. eapply lts_res_tau. eapply lts_parL. eauto.
           eapply cgr_res_scope.
      -- exists (ν (p ‖ NewVarC 0 q2)). destruct α.
         * split. eapply lts_res_ext. eapply lts_parR. replace (NewVarC 0 q) with (NewVarCn 0 1 q); eauto.
           replace (NewVarC 0 q2) with (NewVarCn 0 1 q2); eauto. eapply NewVarC_preserves_transition. eauto.
           eapply cgr_res_scope.
         * split. eapply lts_res_tau. eapply lts_parR. replace (NewVarC 0 q) with (NewVarCn 0 1 q); eauto.
           replace (NewVarC 0 q2) with (NewVarCn 0 1 q2); eauto. eapply NewVarC_preserves_reduction. eauto.
           eapply cgr_res_scope.
    + intros. dependent destruction l.
      -- dependent destruction l.
         * exists (ν p2 ‖ q). split. eapply lts_parL. eapply lts_res_ext. eauto. eapply cgr_res_scope_rev.
         * rewrite NewVarCzero_and_add in l. assert (exists q'2, q2 = NewVarC 0 q'2) as (q'2 & eq). 
           { eapply NewVarC_ext_proc in l as (μ' & p'' & eq1 & eq2).
             subst. exists p''. eauto. } subst.
           assert (lts q (ActExt μ) q'2). { eapply NewVarC_ext_proc_rev. eauto. }
           exists (ν p ‖ q'2). split. eapply lts_parR. eauto.
           eapply cgr_res_scope_rev.
      -- dependent destruction l.
         * assert (lts (NewVarC 0 q) ((c ⋉ v) ?) q2) ;eauto.
           eapply NewVarC_ext_proc in l2 as (μ' & p'' & eq1 & eq2); subst.
           rewrite eq1 in H. eapply NewVarC_in_ext_rev_Input in eq1 as (c' & v' & eq' & eq'' & eq'''); subst.
           simpl in *. exists ((ν p2) ‖ p''). split. eapply lts_comL. eapply lts_res_ext. rewrite NewVarCzero_and_add.
           eauto. eapply NewVarC_ext_proc_rev; eauto. eapply cgr_res_scope_rev.
         * assert (lts (NewVarC 0 q) ((c ⋉ v) !) p2) ;eauto.
           eapply NewVarC_ext_proc in l1 as (μ' & p'' & eq1 & eq2); subst.
           rewrite eq1 in H. eapply NewVarC_in_ext_rev_Output in eq1 as (c' & v' & eq' & eq'' & eq'''); subst.
           simpl in *. exists ((ν q2) ‖ p''). split. eapply lts_comR. eapply NewVarC_ext_proc_rev; eauto.
           eapply lts_res_ext. rewrite NewVarCzero_and_add.
           eauto. eapply cgr_res_scope_rev.
         * exists ((ν p2) ‖ q). split. eapply lts_parL. eapply lts_res_tau. eauto.
           eapply cgr_res_scope_rev.
         * assert (lts (NewVarC 0 q) τ q2); eauto. eapply NewVarC_tau_proc in l as (q'' & eq''); subst.
           eapply NewVarC_tau_proc_rev in H. exists ((ν p) ‖ q''). split.
           eapply lts_parR. eauto. eapply cgr_res_scope_rev.
    + intros. exists q.  split. apply lts_choiceL.  assumption. auto with cgr.
    + intros. dependent destruction l.
      -- exists q. split. assumption. auto with cgr.
      -- inversion l.
    + intros. dependent destruction l.
      -- exists q0. split. apply lts_choiceR. assumption. auto with cgr.
      -- exists q0. split. apply lts_choiceL. assumption. auto with cgr.
    + intros. dependent destruction l.
      -- exists q0. split. apply lts_choiceL. apply lts_choiceL. assumption. auto with cgr.
      -- dependent destruction l.
         * exists q0. split. apply lts_choiceL. apply lts_choiceR. assumption. auto with cgr.
         * exists q0. split. apply lts_choiceR. assumption. auto with cgr.
    + intros. dependent destruction l.
      -- dependent destruction l.
         * exists q0. split. apply lts_choiceL. assumption. auto with cgr.
         * exists q0. split. apply lts_choiceR. apply lts_choiceL. assumption. auto with cgr.
      -- exists q0. split. apply lts_choiceR. apply lts_choiceR. assumption. auto with cgr.
    + intros. dependent destruction l. exists (pr_subst x p (rec x • p)). split. apply lts_recursion. 
      apply cgr_subst. assumption.
    + intros. dependent destruction l. exists p.  split. apply lts_tau.
      constructor. assumption.
    + intros. dependent destruction l. exists (p^v). split. apply lts_input.
      apply Congruence_Respects_Substitution. constructor. apply H.
    + intros. dependent destruction l.
      -- destruct (IHcgr_step p2 ((c ⋉ v) ! )).  exact l1. destruct H0. exists (x ‖ q2).
          split. eapply lts_comL. exact H0. assumption.
          apply cgr_fullpar. assumption. reflexivity.
      -- destruct (IHcgr_step q2 ((c ⋉ v) ?)). assumption. destruct H0. exists (x ‖ p2).
          split.  eapply lts_comR. exact l1. assumption.
          apply cgr_fullpar. assumption. reflexivity.
      -- destruct (IHcgr_step p2 α). assumption. destruct H0. eexists.
          split. instantiate (1:= (x ‖ r)). apply lts_parL. assumption. apply cgr_fullpar.
          assumption. reflexivity.
      -- eexists. split. instantiate (1:= (p ‖ q2)). apply lts_parR.
          assumption. apply cgr_par.
          constructor. assumption.
    + intros. inversion l; subst.
      -- destruct (IHcgr_step p' (ActExt (VarC_action_add 1 μ))) as (q'1 & l' & equiv'). eauto.
         exists (ν q'1). split; eauto. eapply lts_res_ext. eauto. eapply cgr_res. eauto.
      -- destruct (IHcgr_step p' τ) as (q'1 & l' & equiv'). eauto. exists (ν q'1). split.
         eapply lts_res_tau. eauto. eapply cgr_res. eauto. 
    + intros. dependent destruction l.
      -- eexists. split. instantiate (1:= p'). apply lts_ifOne; eauto. reflexivity. 
      -- destruct (IHcgr_step q'0 α) as (q'1 & l' & equiv'). eauto.
         eexists. split. apply lts_ifZero; eauto. eauto.
    + intros. dependent destruction l.
      -- destruct (IHcgr_step p'0 α) as (p'1 & l' & equiv'). eauto.
         eexists. split. apply lts_ifOne; eauto. eauto.
      -- eexists. split. instantiate (1:= q'). apply lts_ifZero; eauto. reflexivity. 
    + intros. dependent destruction l. 
      -- destruct (IHcgr_step q α). assumption. destruct H0. exists x. split. apply lts_choiceL. assumption. assumption.
      -- eexists. instantiate (1:= q). split. apply lts_choiceR. assumption. reflexivity.
  - intros. destruct (IHhcgr2 q α). assumption. destruct (IHhcgr1 x0 α). destruct H. assumption. exists x1. split. destruct H0. assumption.
    destruct H. destruct H0. eauto with cgr.
Qed.

Lemma lts_res_ext_n n p p' μ : lts p (ActExt (VarC_action_add n μ)) p' -> lts (Ѵ  n p) (ActExt μ) (Ѵ  n p').
Proof.
  revert p p' μ.
  induction n.
  + simpl; eauto. intros. rewrite VarC_add_zero_ext in H. eauto.
  + intros. simpl in *. eapply lts_res_ext. eapply IHn. replace (S n) with (n + 1)%nat in H by lia.
    rewrite VarC_action_add_add; eauto.
Qed.

Lemma lts_res_tau_n n p p' : lts p τ p' -> lts (Ѵ  n p) τ (Ѵ  n p').
Proof.
  revert p p'.
  induction n.
  + simpl; eauto.
  + intros. simpl in *. eapply lts_res_tau. eapply IHn. eauto.
Qed.

(* One side of the Harmony Lemma *)
Lemma Reduction_Implies_TausAndCong : forall P Q, (sts P Q) -> (lts_then_sc P τ Q).
Proof. 
intros P Q Reduction. 
assert ((exists c v P2 G2 S n, ((P ≡* Ѵ  n (((c ! v • 𝟘) ‖ ((c ? P2) + G2)) ‖ S))) /\ (Q ≡* Ѵ  n ((𝟘 ‖ (P2^v)) ‖ S)))
\/ (exists P1 G1 S n, (P ≡* Ѵ  n (((𝛕 • P1) + G1) ‖ S)) /\ (Q ≡* Ѵ  n (P1 ‖ S)))
\/ (exists n P1 S n', (P ≡* Ѵ  n' ((rec n • P1) ‖ S)) /\ (Q ≡* Ѵ  n' (pr_subst n P1 (rec n • P1) ‖ S)))
). 
apply ReductionShape. exact Reduction.
destruct H as [IH|[IH|IH]];  decompose record IH. 

(*First case τ by communication *)

- assert (lts (Ѵ x4 ((x ! x0 • 𝟘) ‖ ((x ? x1) + x2) ‖ x3)) τ (Ѵ x4 (𝟘 ‖ (x1^x0) ‖ x3))).
  * eapply lts_res_tau_n.
    apply lts_parL.   
    eapply lts_comL. instantiate (2:= x). instantiate (1:= x0).
    apply lts_output. apply lts_choiceL. apply lts_input.
  * assert (sc_then_lts P τ (Ѵ x4 ((𝟘 ‖ x1^x0) ‖ x3))). exists ((Ѵ x4 ((x ! x0 • 𝟘 ‖ (gpr_input x x1 + x2)) ‖ x3))). split. assumption. assumption.
    assert (lts_then_sc P τ (Ѵ x4 ((𝟘 ‖ x1^x0) ‖ x3))). apply Congruence_Respects_Transition. assumption. destruct H3. destruct H3.
    exists x5. split. assumption.  transitivity (Ѵ x4 ((𝟘 ‖ x1^x0) ‖ x3)). assumption. symmetry. assumption.

(*Second case τ by Tau Action *)

- assert (lts (Ѵ x2 ((𝛕 • x + x0) ‖ x1)) τ (Ѵ x2 (x ‖ x1))). eapply lts_res_tau_n. constructor.
  apply lts_choiceL. apply lts_tau.
  assert (sc_then_lts P τ (Ѵ x2 (x ‖ x1))). exists (Ѵ x2 ((𝛕 • x + x0) ‖ x1)). split. assumption.
  eapply lts_res_tau_n. apply lts_parL. apply lts_choiceL. apply lts_tau.
  assert (lts_then_sc P τ (Ѵ x2 (x ‖ x1))). apply Congruence_Respects_Transition. assumption. destruct H3. destruct H3. 
  exists x3. split. assumption.  transitivity (Ѵ x2 (x ‖ x1)). assumption. symmetry. assumption.

(*Third case τ by recursion *)

- assert (lts (Ѵ x2 (rec x • x0 ‖ x1)) τ (Ѵ x2 (pr_subst x x0 (rec x • x0) ‖ x1))). eapply lts_res_tau_n.
  constructor. apply lts_recursion. assert (sc_then_lts P τ (Ѵ x2 ((pr_subst x x0 (rec x • x0) ‖ x1)))). 
  exists (Ѵ x2 (rec x • x0 ‖ x1)). split. assumption. assumption.
  assert (lts_then_sc P τ (Ѵ x2 (pr_subst x x0 (rec x • x0) ‖ x1))). 
  apply Congruence_Respects_Transition. assumption. destruct H3. destruct H3. 
  exists x3. split. assumption.  transitivity (Ѵ x2 (pr_subst x x0 (rec x • x0) ‖ x1)). assumption.
  symmetry. assumption.
Qed.


(* Some lemmas for multiple parallele processes to simplify the statements of proof*)
Lemma InversionParallele : forall P Q R S, (P ‖ Q) ‖ (R ‖ S) ≡* (P ‖ R) ‖ (Q ‖ S) . 
Proof. 
intros.
 transitivity (((P ‖ Q) ‖ R) ‖ S). apply cgr_par_assoc_rev.
 transitivity ((P ‖ (Q ‖ R)) ‖ S). apply cgr_par. apply cgr_par_assoc.
 transitivity (((Q ‖ R) ‖ P) ‖ S). apply cgr_par. apply cgr_par_com.
 transitivity ((Q ‖ R) ‖ (P ‖ S)). apply cgr_par_assoc.
 transitivity ((R ‖ Q) ‖ (P ‖ S)). apply cgr_par. apply cgr_par_com.
 transitivity (((R ‖ Q) ‖ P) ‖ S). apply cgr_par_assoc_rev.
 transitivity ((P ‖ (R ‖ Q)) ‖ S). apply cgr_par. apply cgr_par_com.
 transitivity (((P ‖ R) ‖ Q) ‖ S). apply cgr_par. apply cgr_par_assoc_rev.
 transitivity ((P ‖ R) ‖ (Q ‖ S)). apply cgr_par_assoc.
reflexivity. 
Qed.
Lemma InversionParallele2 : forall P Q R S, (P ‖ Q) ‖ (R ‖ S) ≡* (R ‖ P) ‖ (S ‖ Q).
Proof.
intros. 
 transitivity ((P ‖ R) ‖ (Q ‖ S)). apply InversionParallele.
 transitivity ((R ‖ P) ‖ (Q ‖ S)). apply cgr_par. apply cgr_par_com.
 transitivity ((Q ‖ S) ‖ (R ‖ P)). apply cgr_par_com.
 transitivity ((S ‖ Q) ‖ (R ‖ P)). apply cgr_par. apply cgr_par_com.
apply cgr_par_com.
Qed.
Lemma InversionParallele3 : forall P Q R S, (P ‖ Q) ‖ (R ‖ S) ≡* (R ‖ Q) ‖ (P ‖ S).
Proof.
intros.
 transitivity ((Q ‖ P) ‖ (R ‖ S)). apply cgr_par. apply cgr_par_com.
 transitivity ((Q ‖ R) ‖ (P ‖ S)). apply InversionParallele. apply cgr_par. apply cgr_par_com.
Qed.

(* The More Stronger Harmony Lemma (in one side) is more stronger *)
Lemma Congruence_Simplicity : (forall α , ((forall P Q, (((lts P α Q) -> (sts P Q)))) 
-> (forall P Q, ((lts_then_sc P α Q) -> (sts P Q))))).
Proof.
intros. destruct H0. destruct H0. eapply sts_cong. instantiate (1:=P). apply cgr_refl. instantiate (1:=x). apply H. exact H0. 
exact H1.
Qed.

Lemma simpl_NewVarC k k' p : NewVarC k (Ѵ k' p) = Ѵ k' (NewVarC (k + k') p).
Proof.
  revert p k. induction k'.
  + simpl. intros. replace (k + 0)%nat with k%nat by lia. eauto.
  + intros. simpl. f_equal. rewrite IHk'. f_equal. replace (S k + k')%nat with (k + S k')%nat by lia.
    eauto.
Qed.

Lemma simpl_NewVarCn j k k' p: NewVarCn j k (Ѵ  k' p) = Ѵ  k' (NewVarCn (j + k') k p).
Proof.
  intros. revert j k' p. induction k.
  + simpl. eauto.
  + intros. simpl in *. rewrite<- (NewVarCn_revert_def k p (j + k')).
    rewrite<- (IHk j k' (NewVarC (j + k') p)). rewrite<- NewVarCn_revert_def at 1. f_equal.
    eapply simpl_NewVarC.
Qed.

Lemma sts_res_n n P Q : sts P Q → sts (Ѵ n P) (Ѵ n Q).
Proof.
  revert P Q. induction n.
  + intros; simpl; eauto.
  + intros; simpl. eapply sts_res. eauto.
Qed.

Lemma NewVarC_res i k p : NewVarC i (Ѵ k p) = Ѵ k (NewVarC (i + k) p).
Proof.
  revert i p. induction k.
  + intros; simpl; eauto. replace (i + 0)%nat with i by lia. eauto.
  + intros; simpl. f_equal. rewrite IHk. f_equal. replace (S i + k)%nat with (i + S k)%nat by lia. eauto.
Qed.

Lemma NewVarCn_res i j k p : NewVarCn i j (Ѵ k p) = Ѵ k (NewVarCn (i + k) j p).
Proof.
  revert i k p. induction j.
  + intros; simpl; eauto.
  + intros; simpl. rewrite<- NewVarCn_revert_def. rewrite<- NewVarCn_revert_def.
    rewrite<- (IHj i k (NewVarC (i + k) p)). f_equal. rewrite NewVarC_res. eauto.
Qed.

Lemma NewVarCn_par i j p q: NewVarCn i j (p ‖ q) = (NewVarCn i j p) ‖ (NewVarCn i j q).
Proof.
  revert i p q. induction j.
  + intros; simpl; eauto.
  + intros; simpl. rewrite<- NewVarCn_revert_def. simpl. rewrite<- NewVarCn_revert_def.
    rewrite<- NewVarCn_revert_def. rewrite IHj. eauto. 
Qed.

Lemma NewVarCn_input k j c p : gNewVarCn 0 j ((VarC_add k c) ? p) = (VarC_add (j + k) c) ? (NewVarCn 0 j p).
Proof.
  revert k c p. induction j.
  + intros; simpl; eauto.
  + intros; simpl. rewrite<- NewVarCn_revert_def. rewrite IHj. simpl. rewrite<- NewVarCn_revert_def.
    rewrite<- NewVarCzero_and_add_Channel. rewrite<- VarC_add_revert_def. simpl. eauto.
Qed.

Lemma subst_and_NewVarCn k i j v q :
    subst_in_proc k v (NewVarCn i j q) = NewVarCn i j (subst_in_proc k v q).
Proof.
  revert v q k i. induction j.
  + intros; simpl; eauto.
  + intros; simpl. rewrite subst_and_NewVarC. f_equal.
    eapply IHj.
Qed.

Lemma simpl_NewVar_auto k j c : (NewVar_in_ChannelData k (VarC_add (k + j) c)) = (VarC_add (k + S j) c).
Proof.
  destruct c.
  + simpl. eauto.
  + simpl. rewrite decide_True; try lia. replace (k + S j)%nat with (S (k + j))%nat by lia.
    replace (S (k + j) + n)%nat with (S (k + j + n))%nat by lia. eauto.
Qed.

Lemma NewVarCn_output k j c d : (NewVarCn k j (VarC_add k c ! d • 𝟘) = (VarC_add (j + k) c) ! d • 𝟘).
Proof.
  revert k c d. induction j.
  + intros; simpl; eauto.
  + intros; simpl. rewrite IHj. simpl. 
    assert (j+k = k + j)%nat as eq by lia. rewrite eq at 1. rewrite simpl_NewVar_auto.
    replace (k + S j)%nat with (S (j + k))%nat by lia. f_equal.
Qed.

Lemma NewVarCn_choice i j g1 g2: NewVarCn i j (g (g1 + g2)) = (gNewVarCn i j g1) + (gNewVarCn i j g2).
Proof.
  revert i g1 g2. induction j.
  + intros; simpl; eauto.
  + intros; simpl. rewrite IHj. simpl. eauto.
Qed.

Lemma simpl_NewVarCn_plus_par k j c p g1 q : (NewVarCn k j ((gpr_input (VarC_add k c) p + g1) ‖ q)
        = ((gpr_input (VarC_add (k + j) c) (NewVarCn k j p)) + (gNewVarCn k j g1)) ‖ (NewVarCn k j q)).
Proof.
  revert k c p g1 q. induction j.
  + intros ; simpl; eauto. replace (k + 0)%nat with k by lia. eauto.
  + intros; simpl. rewrite IHj. simpl. f_equal. rewrite simpl_NewVar_auto. eauto.
Qed.

Lemma simpl_NewVarCn_par_plus k j c v q : NewVarCn 0 k ((VarC_add j c ! v • 𝟘) ‖ q)
        = ((VarC_add (k + j) c ! v • 𝟘 ) ‖ (NewVarCn 0 k q)).
Proof.
  revert j c v q. induction k.
  + intros ; simpl; eauto.
  + intros; simpl. rewrite IHk. simpl. f_equal.
    rewrite<- NewVarCzero_and_add_Channel. rewrite<- VarC_add_revert_def.
    simpl. eauto.
Qed.

Lemma simpl_NewVarCn_zero j k : NewVarCn j k 𝟘 = 𝟘.
Proof.
  revert j. induction k; simpl ; eauto. intros; rewrite IHk. simpl;eauto.
Qed.

Lemma Taus_Implies_Reduction : forall P Q, (lts P τ Q) -> (sts P Q).
Proof. 
intros.
dependent induction H.
  - eapply sts_cong.  instantiate (1:=  ((𝛕 • P) + 𝟘)). apply cgr_choice_nil_rev. instantiate (1:=P).
    apply sts_tau. constructor. constructor.
  - apply sts_recursion.
  - eapply sts_cong.
    + eapply cgr_if_true; eauto.
    + eauto.
    + reflexivity.
  - eapply sts_cong.
    + eapply cgr_if_false; eauto.
    + eauto.
    + reflexivity.
  - eapply sts_res. eauto.
  - destruct (TransitionShapeForOutput p1 p2 c v). assumption. decompose record H1.
    destruct (TransitionShapeForInput q1 q2 c v). assumption. decompose record H2.
    eapply sts_cong. etrans. instantiate (1:= Ѵ x0 ((VarC_add x0 c ! v • 𝟘) ‖ x) ‖ Ѵ x4 ((gpr_input (VarC_add x4 c) x1 + x2) ‖ x3)).
    eapply cgr_fullpar; eauto. etrans. eapply cgr_res_scope_n. rewrite simpl_NewVarCn. etrans.
    eapply cgr_res_n. eapply cgr_par_com. etrans. eapply cgr_res_n. eapply cgr_res_scope_n. etrans.
    eapply cgr_res_n. etrans. eapply cgr_res_n. simpl. rewrite simpl_NewVarCn_par_plus.
    rewrite simpl_NewVarCn_plus_par. etrans. 
    instantiate (1 := ((VarC_add (x4 + x0) c ! v • 𝟘) ‖ NewVarCn x4 x0 x3) ‖
           ((gpr_input (VarC_add (x4 + x0) c) (NewVarCn x4 x0 x1) + gNewVarCn x4 x0 x2) ‖ NewVarCn 0 x4 x)). etrans.
    apply InversionParallele. etrans. 
    instantiate (1:= ((VarC_add (x4 + x0) c ! v • 𝟘)
        ‖ (gpr_input (VarC_add (x4 + x0) c) (NewVarCn x4 x0 x1) + gNewVarCn x4 x0 x2))
        ‖ (NewVarCn x4 x0 x3 ‖ NewVarCn 0 x4 x)). apply cgr_fullpar; eauto. eapply cgr_par_com. reflexivity.
    apply InversionParallele. apply InversionParallele. reflexivity. reflexivity.
    eapply sts_res_n. eapply sts_res_n. eapply sts_par. eapply sts_com. symmetry. etrans.
    eapply cgr_fullpar; eauto. etrans. eapply cgr_res_scope_n. eapply cgr_res_n.
    etrans. rewrite NewVarCn_res. eapply cgr_par_com. etrans. eapply cgr_res_scope_n.
    eapply cgr_res_n. simpl. rewrite NewVarCn_par. rewrite NewVarCn_par. rewrite subst_and_NewVarCn.
    etrans. eapply InversionParallele. eapply cgr_fullpar. simpl. rewrite simpl_NewVarCn_zero. eapply cgr_par_com. reflexivity.
  - destruct (TransitionShapeForOutput p1 p2 c v). assumption. decompose record H1.
    destruct (TransitionShapeForInput q1 q2 c v). assumption. decompose record H2.
    eapply sts_cong. etrans. instantiate (1:= Ѵ x4 ((gpr_input (VarC_add x4 c) x1 + x2) ‖ x3) ‖ Ѵ x0 ((VarC_add x0 c ! v • 𝟘) ‖ x)).
    eapply cgr_fullpar; eauto. etrans. eapply cgr_res_scope_n. rewrite simpl_NewVarCn. etrans.
    eapply cgr_res_n. eapply cgr_par_com. etrans. eapply cgr_res_n. eapply cgr_res_scope_n. etrans.
    eapply cgr_res_n. etrans. eapply cgr_res_n. simpl. rewrite NewVarCn_par. rewrite NewVarCn_par.
    rewrite NewVarCn_choice. rewrite NewVarCn_input. rewrite NewVarCn_output.
    apply InversionParallele. eapply cgr_res_n. reflexivity. etrans. eapply cgr_res_n. eapply cgr_res_n.
    reflexivity. eapply cgr_res_n. eapply cgr_res_n. reflexivity. eapply sts_res_n. eapply sts_res_n.
    eapply sts_par. replace (x4 + x0)%nat with (x0 + x4)%nat by lia. eapply sts_com. symmetry.
    etrans. eapply cgr_fullpar; eauto. etrans. eapply cgr_res_scope_n. eapply cgr_res_n.
    rewrite NewVarCn_res. etrans. eapply cgr_par_com. etrans. eapply cgr_res_scope_n.
    eapply cgr_res_n. simpl. rewrite NewVarCn_par. rewrite NewVarCn_par.
    rewrite<- subst_and_NewVarCn. etrans. apply InversionParallele. rewrite simpl_NewVarCn_zero. reflexivity.
  - apply sts_par. apply IHlts. reflexivity.
  - eapply sts_cong. instantiate (1:= q1 ‖ p). apply cgr_par_com. instantiate (1:= q2 ‖ p).
    apply sts_par. apply IHlts. reflexivity. apply cgr_par_com.
  - destruct (TransitionShapeForTauAndGuard (g p1) q). split. assumption. exists p1. reflexivity.
    decompose record H0.
    eapply sts_cong. instantiate (1:= ((𝛕 • x) + (x0 + p2))).
    apply transitivity with (g (((𝛕 • x) + x0) + p2)). apply cgr_choice. assumption. apply cgr_choice_assoc.
    instantiate (1:= x). apply sts_tau. symmetry. assumption.
  - destruct (TransitionShapeForTauAndGuard (g p2) q). split. assumption. exists p2. reflexivity.
    decompose record H0. eapply sts_cong. instantiate (1:= ((𝛕 • x) + (x0 + p1))).
    apply transitivity with (g (((𝛕 • x) + x0 ) + p1)). apply transitivity with (g (p2 + p1)). apply cgr_choice_com.
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

(* The next work is for making 'bvar' always relates to an input *) 

(* Definition for Well Abstracted bvariable *)
Inductive Well_Defined_Data : nat -> Data -> Prop :=
| bvar_is_defined_up_to_k: forall k x, (x < k) -> Well_Defined_Data k (bvar x)
| cst_is_always_defined : forall k v, Well_Defined_Data k (cst v).

Inductive Well_Defined_Condition : nat -> Equation Data -> Prop :=
| equationOnValueXX : forall k x y, Well_Defined_Data k x -> Well_Defined_Data k y -> Well_Defined_Condition k (x == y).

Inductive Well_Defined_Input_in : nat -> proc -> Prop :=
| WD_par : forall k p1 p2, Well_Defined_Input_in k p1 -> Well_Defined_Input_in k p2 
                -> Well_Defined_Input_in k (p1 ‖ p2)
| WD_res : forall k p, Well_Defined_Input_in k p -> Well_Defined_Input_in k (ν p)
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
| WD_tau : forall k p,  Well_Defined_Input_in k p -> Well_Defined_Input_in k (𝛕 • p)
| WD_choice : forall k p1 p2,  Well_Defined_Input_in k (g p1) ->  Well_Defined_Input_in k (g p2) 
              ->  Well_Defined_Input_in k (p1 + p2).

Hint Constructors Well_Defined_Input_in:ccs.

Lemma Inequation_k_data : forall k d, Well_Defined_Data k d -> Well_Defined_Data (S k) d.
Proof.
intros. dependent destruction d. constructor. dependent destruction H. constructor. auto with arith.
Qed.

Lemma Inequation_k_equation : forall k c, Well_Defined_Condition k c -> Well_Defined_Condition (S k) c.
Proof.
intros. dependent destruction c. destruct d; destruct d0.
- constructor; constructor.
- dependent destruction H. constructor. constructor. apply Inequation_k_data. assumption.
- dependent destruction H. constructor. apply Inequation_k_data. assumption. constructor. 
- dependent destruction H. constructor; apply Inequation_k_data; assumption.
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
- intros. constructor. apply Hp. simpl; auto with arith. dependent destruction H. assumption.
- destruct g0.
  ** intros. constructor.
  ** intros. constructor.
  ** intros. constructor. apply Hp. simpl; auto with arith. dependent destruction H. assumption.
  ** intros. constructor. apply Hp. simpl; auto with arith. dependent destruction H. assumption.
  ** intros. dependent destruction H. constructor.
    -- apply Hp. simpl; auto with arith. assumption.
    -- apply Hp. simpl; auto with arith. assumption.
Qed.


(* Lemma Congruence_step_Respects_WD_k : forall p q k, Well_Defined_Input_in k p -> p ≡ q -> Well_Defined_Input_in k q. 
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
Qed. *)

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
  - dependent destruction H.
    destruct (decide (n < k)). 
    -- constructor. assumption.
    -- constructor. apply NotK.  transitivity n. lia. (* pas top *) assumption. lia.
Qed.

Lemma ForEquation : forall k v e, Well_Defined_Condition (S k) e 
                -> Well_Defined_Condition k (subst_in_Equation k (cst v) e).
Proof.
intros. revert H. revert v. revert k. 
- dependent destruction e. dependent induction d; dependent induction d0.
  * intros. simpl. constructor; constructor.
  * intros. simpl. destruct (decide (n = k)).
    ** constructor; constructor.
    ** constructor. constructor. dependent destruction H. dependent destruction H0.
       destruct (decide(n < k)).
       --- constructor. assumption.
       --- constructor. lia.
  * intros. simpl. constructor; try constructor. destruct (decide (n = k)). constructor. dependent destruction H.
    dependent destruction H.
    destruct (decide(n < k)).
       --- constructor. assumption.
       --- constructor. lia. 
  * intros. simpl. constructor.
    ** destruct (decide (n = k)); try constructor. dependent destruction H. dependent destruction H. 
       destruct (decide(n < k)).
       --- constructor. assumption.
       --- constructor. lia. 
    ** destruct (decide (n0 = k)); try constructor. dependent destruction H. dependent destruction H0. 
       destruct (decide(n0 < k)).
       --- constructor. assumption.
       --- constructor. lia. 
Qed.

Lemma ForSTS : forall k p v, Well_Defined_Input_in (S k) p -> Well_Defined_Input_in k (subst_in_proc k (cst v) p).
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
* intros. simpl. dependent destruction H. constructor. apply Hp. simpl. auto with arith. assumption.
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
  * constructor. dependent destruction H.  transitivity i.
    apply Nat.nlt_succ_r. assumption.
    auto with arith. 
Qed.


Lemma WD_eq_and_NewVar : forall e k i, Well_Defined_Condition (k + i) e 
                          -> Well_Defined_Condition (S (k + i)) (NewVar_in_Equation i e).
Proof.
intro. dependent induction e; intros; simpl. 
* dependent induction H. constructor. 
  - apply WD_data_and_NewVar. assumption.
  - apply WD_data_and_NewVar. assumption.
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
* constructor. dependent destruction H. apply Hp. simpl. auto with arith. assumption.
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

Lemma WD_and_NewVarC : forall k i p, Well_Defined_Input_in k p -> Well_Defined_Input_in k (NewVarC i p).
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
* dependent destruction H. constructor. eauto.
   - apply Hp. simpl. auto with arith. assumption.
   - apply Hp. simpl. auto with arith. assumption.
* constructor. dependent destruction H. eauto.
* constructor. dependent destruction H. apply Hp. simpl. auto with arith. assumption.
* destruct g0; intros; simpl.
  - constructor.
  - constructor.
  - dependent destruction H. constructor. 
    apply Hp. simpl. auto with arith. eauto.
  - constructor. apply Hp. simpl. auto. dependent destruction H. assumption.
  - dependent destruction H. constructor.
    -- assert (Well_Defined_Input_in k (NewVarC i (g g0_1))).
       apply Hp. simpl. auto with arith. assumption. assumption.
    -- assert (Well_Defined_Input_in k (NewVarC i (g g0_2))).
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
* intros. simpl. constructor. dependent destruction H. apply Hp.
    - simpl; auto with arith.
    - eapply WD_and_NewVarC. eauto.
    - eauto.
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

(* Lemma STS_Respects_WD : forall p q, Well_Defined_Input_in 0 p -> sts p q -> Well_Defined_Input_in 0 q.
Proof.
intros. revert H. rename H0 into Reduction. dependent induction Reduction.
* intros. constructor.
  - constructor.
  - dependent destruction H. dependent destruction H0. dependent destruction H0_. 
    dependent destruction H. apply Well_Def_Data_Is_a_value in H. destruct H. subst.  apply ForSTS. assumption. 
* intros. dependent destruction H. dependent destruction H. assumption.
* intros. dependent destruction H. apply RecursionOverReduction_is_WD. constructor. assumption.
* intros. dependent destruction H0. assumption.
* intros. dependent destruction H0. assumption.
* intros. dependent destruction H. constructor. apply IHReduction. assumption. assumption.
* intros. apply Congruence_Respects_WD with q2. apply IHReduction. apply Congruence_Respects_WD with p1. 
  assumption. assumption. assumption.
Qed. *)

Inductive Well_Defined_Action: (ActIO TypeOfActions) -> Prop :=
| ActionOuput_with_value_is_always_defined : forall c v, Well_Defined_Action ((c ⋉ (cst v))!)
| ActionInput_with_value_is_always_defined : forall c v, Well_Defined_Action ((c ⋉ (cst v))?)
| Tau_is_always_defined : Well_Defined_Action τ.

Inductive Well_Defined_ExtAction: (ExtAct TypeOfActions) -> Prop :=
| ExtActionOuput_with_value_is_always_defined : forall c v, Well_Defined_ExtAction (ActOut (c ⋉ (cst v)))
| ExtActionInput_with_value_is_always_defined : forall c v, Well_Defined_ExtAction (ActIn (c ⋉ (cst v))).

Lemma Output_are_good : forall p1 p2 c d, Well_Defined_Input_in 0 p1 -> lts p1 ((c ⋉ d) !) p2 
      -> exists v, d = cst v.
Proof.
intros. dependent induction H0. dependent destruction H. eapply Well_Def_Data_Is_a_value in H. destruct H.
subst. exists x. reflexivity.
- dependent destruction H. eapply IHlts with c. assumption. reflexivity.
- dependent destruction H. eapply IHlts with c. assumption. reflexivity.
- dependent destruction H. simpl in *. eapply IHlts with (VarC_add 1 c). assumption. simpl. reflexivity.
- dependent destruction H. eapply IHlts with c. assumption. reflexivity.
- dependent destruction H. eapply IHlts with c. assumption. reflexivity.
- dependent destruction H. eapply IHlts with c. assumption. reflexivity.
- dependent destruction H. eapply IHlts with c. assumption. reflexivity.
Qed.

Lemma LTS_Respects_WD : forall p q α, Well_Defined_Input_in 0 p -> Well_Defined_Action α -> lts p α q 
            ->  Well_Defined_Input_in 0 q.
Proof.
intros. revert H. revert H0. rename H1 into Transition. dependent induction Transition.
* intros. dependent destruction H0. apply ForSTS. dependent destruction H. assumption.
* intros. constructor.
* intros. dependent destruction H. assumption.
* intros. apply ForRecursionSanity. dependent destruction H. assumption. assumption.
* intros. inversion H1; subst. eapply IHTransition; eauto.
* intros. inversion H1; subst. eapply IHTransition; eauto.
* intros. inversion H; subst. constructor. eapply IHTransition; eauto. destruct μ; destruct a; destruct d; simpl in *.
  + simpl. constructor.
  + simpl. inversion H0.
  + simpl. constructor.
  + simpl. inversion H0.
* intros. inversion H; subst. constructor. eapply IHTransition; eauto.
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
Lemma OutputWithValue : forall p q a, lts p (a !) q -> exists c d, a = c ⋉ d.
Proof.
intros. dependent destruction a. dependent induction H.
- exists c. exists d. reflexivity.
- destruct (IHlts c d). reflexivity. destruct H1. dependent destruction H1. exists x. exists x0. reflexivity.
- destruct (IHlts c d). reflexivity. destruct H1. dependent destruction H1. exists x. exists x0. reflexivity.
- exists c. exists d. eauto.
- destruct (IHlts c d). reflexivity. destruct H0. dependent destruction H0. exists x. exists x0. reflexivity.
- destruct (IHlts c d). reflexivity. destruct H0. dependent destruction H0. exists x. exists x0. reflexivity.
- destruct (IHlts c d). reflexivity. destruct H0. dependent destruction H0. exists x. exists x0. reflexivity.
- destruct (IHlts c d). reflexivity. destruct H0. dependent destruction H0. exists x. exists x0. reflexivity.
Qed.

Lemma InputWithValue : forall p q a, lts p (a ?) q -> exists c v, a = c ⋉ v.
Proof.
intros. dependent destruction a. dependent induction H.
- exists c. exists d. reflexivity.
- destruct (IHlts c d). reflexivity. destruct H1. dependent destruction H1. exists x. exists x0.  reflexivity.
- destruct (IHlts c d). reflexivity. destruct H1. dependent destruction H1. exists x. exists x0. reflexivity.
- exists c. exists d. eauto.
- destruct (IHlts c d). reflexivity. destruct H0. dependent destruction H0. exists x. exists x0. reflexivity.
- destruct (IHlts c d). reflexivity. destruct H0. dependent destruction H0. exists x. exists x0. reflexivity.
- destruct (IHlts c d). reflexivity. destruct H0. dependent destruction H0. exists x. exists x0. reflexivity.
- destruct (IHlts c d). reflexivity. destruct H0. dependent destruction H0. exists x. exists x0. reflexivity.
Qed.

Lemma cgr_par_nil_n n r :  Ѵ n 𝟘 ‖ r ≡* r.
Proof.
  revert r. induction n.
  - simpl. intros. eauto with cgr.
  - simpl. intros. etrans. instantiate (1 := (𝟘 ‖ (ν Ѵ n 𝟘) ‖ r)).
    eapply cgr_par. symmetry. etrans. eapply cgr_par_com. eapply cgr_par_nil.
    etrans. eapply cgr_par. eapply cgr_par_com. etrans. eapply cgr_par.
    eapply cgr_res_scope_rev. simpl. etrans. eapply cgr_par. eapply cgr_res. eauto.
    etrans. eapply cgr_par. eapply cgr_res_nil. etrans. eapply cgr_par_com. eapply cgr_par_nil.
Qed.

(* Peter Selinger Axioms (OutBuffered Agent with FeedBack) up to structural equivalence*)

Lemma OBA_with_FB_First_Axiom : forall p q r a α,
  lts p (a !) q -> lts q α r ->
  (exists r', lts p α r' /\ lts_then_sc r' (a !) r). (* output-commutativity *)
Proof.
  intros. assert (lts p (a !) q). assumption. apply OutputWithValue in H1.
  decompose record H1. subst. eapply TransitionShapeForOutputSimplified in H as eq.
  eapply lts_parR in H0. instantiate (1 := x ! x0 • 𝟘) in H0.
  edestruct (Congruence_Respects_Transition p ((x ! x0 • 𝟘) ‖ r) α).
  exists ((x ! x0 • 𝟘) ‖ q). split; assumption. destruct H2.
  assert (lts ((x ! x0 • 𝟘) ‖ r) ((x ⋉ x0) !) (𝟘 ‖ r)). constructor.
  constructor.
  edestruct (Congruence_Respects_Transition x1 (𝟘 ‖ r) ((x ⋉ x0) !)).
  exists ((x ! x0 • 𝟘) ‖ r). split ; assumption. destruct H5.
  assert (x2 ≡* r). etrans. eauto. etrans. eapply cgr_par_com. eapply cgr_par_nil.
  exists x1. split. assumption. exists x2. split; assumption.
Qed.

Lemma simpl_output_res n c v p μ : lts (Ѵ n (VarC_add n c ! v • 𝟘)) (ActExt μ) p -> μ = ActOut (c ⋉ v) /\ p = Ѵ n 𝟘.
Proof.
  revert c v p μ.
  induction n.
  + simpl in * ; intros. rewrite VarC_add_zero in H. inversion H; eauto; split ;eauto.
  + intros. simpl in *. inversion H. subst. replace (S n)%nat with (n + 1)%nat in H2 by lia.
    rewrite VarC_add_revert_def in H2. simpl in *. eapply IHn in H2 as (eq1 & eq2).
    subst. rewrite NewVarCzero_and_add in eq1.
    replace (ActOut (VarC_add 1 c ⋉ v)) with (VarC_action_add 1 (ActOut (c ⋉ v))) in eq1 by eauto.
    rewrite NewVarCzero_and_add in eq1. eapply NewVarC_in_ext_inv in eq1. subst. split ;eauto.
Qed.

Lemma OBA_with_FB_Second_Axiom : forall p q1 q2 a μ, 
  μ ≠ (ActOut a) ->
  lts p (a !) q1 ->
  lts p (ActExt μ) q2 ->
  ∃ r : proc, lts q1 (ActExt μ) r ∧ lts_then_sc q2 (a !) r. (* output-confluence  *)
Proof.
  intros. assert (lts p (a !) q1). assumption. apply OutputWithValue in H2.
  decompose record H2. subst. rename x into c. rename x0 into v.
  eapply TransitionShapeForOutputSimplified in H0.
  edestruct (Congruence_Respects_Transition ((c ! v • 𝟘) ‖ q1) q2 (ActExt μ)).
  exists p. split. symmetry. assumption. assumption.
  destruct H3. inversion H3; subst.
  - inversion H9. subst. assert (ActOut (c ⋉ v) = ActOut (c ⋉ v)). eauto. exfalso. eapply H. eauto.
  - exists q3. split. assumption.
    assert (lts ((c ! v • 𝟘) ‖ q3) ((c ⋉ v) !) (𝟘 ‖ q3)). constructor. constructor.
    edestruct (Congruence_Respects_Transition q2 (𝟘 ‖ q3) ((c ⋉ v) !)).
    exists ((c ! v • 𝟘) ‖ q3). split. eauto with cgr. assumption. destruct H6. exists x. split. assumption.
    etrans. eauto. etrans. eapply cgr_par_com. eapply cgr_par_nil.
Qed.

Lemma OBA_with_FB_Third_Axiom : forall p1 p2 p3 a, 
            lts p1 (a !) p2 → lts p1 (a !) p3 -> p2 ≡* p3. (* output-determinacy *)
Proof.
  intros. assert (lts p1 (a !) p2). assumption. apply OutputWithValue in H1.
  decompose record H1. subst. rename x into c. rename x0 into v.
  revert H0. revert p3. dependent induction H.
  - intros. inversion H0. subst. eauto with cgr.
  - intros. inversion H2; subst.
    + eapply IHlts; eauto.
    + rewrite H in H8. inversion H8.
  - intros. inversion H2; subst.
    + rewrite H in H8. inversion H8.
    + eapply IHlts; eauto.
  - intros. inversion H0;subst. eapply cgr_res. eapply (IHlts v (VarC_add 1 c)); eauto.
  - intros. inversion H0;subst. 
    * apply cgr_fullpar. eapply IHlts. eauto. eauto. assumption. eauto with cgr.
    * apply TransitionShapeForOutputSimplified in H.
      apply TransitionShapeForOutputSimplified in H6.
       transitivity (p2 ‖ ((c ! v • 𝟘) ‖ q2)). eapply cgr_fullpar. 
      reflexivity. exact H6. etrans. symmetry. eapply cgr_par_assoc.
      eapply cgr_par. etrans. eapply cgr_par_com. symmetry. eauto.
  - intros. inversion H0 ; subst.
      apply TransitionShapeForOutputSimplified in H.
      apply TransitionShapeForOutputSimplified in H6.
       transitivity (((c ! v • 𝟘) ‖ p2) ‖ q2). eauto with cgr.
       transitivity (( p2 ‖ (c ! v • 𝟘)) ‖ q2). eauto with cgr.
       transitivity ( p2 ‖ ((c ! v • 𝟘) ‖ q2)). eauto with cgr. apply cgr_fullpar. reflexivity.
      eauto with cgr.
    * apply cgr_fullpar. reflexivity. eapply IHlts. eauto. eauto. assumption.
  - intros. exfalso. eapply guarded_does_no_output. eassumption.
  - intros. exfalso. eapply guarded_does_no_output. eassumption.
Qed.

Lemma OBA_with_FB_Fourth_Axiom : forall p1 p2 p3 a, lts p1 (a !) p2 -> lts p2 (a ?) p3 
                              -> lts_then_sc p1 τ p3. (* feedback *)
Proof.
  intros. assert (lts p1 (a !) p2). assumption. apply OutputWithValue in H1.
  decompose record H1. subst. rename x into c. rename x0 into v.
  eapply TransitionShapeForOutputSimplified in H.
  assert (lts ((c ! v • 𝟘)) ((c ⋉ v) !) 𝟘).
  constructor.
  assert (lts ((c ! v • 𝟘) ‖ p2) τ  (𝟘 ‖ p3)). econstructor; eassumption.
  edestruct (Congruence_Respects_Transition p1 ( 𝟘 ‖ p3) τ). exists (( c ! v • 𝟘) ‖ p2).
  split; assumption. destruct H4. exists x. split. assumption. etrans. eauto. etrans.
  eapply cgr_par_com. eapply cgr_par_nil. 
Qed.

Lemma OBA_with_FB_Fifth_Axiom : forall p q1 q2 a,
  lts p (a !) q1 -> lts p τ q2 ->
  (∃ q : proc, lts q1 τ q /\ lts_then_sc q2 (a !) q) \/ lts_then_sc q1 (a ?) q2. (* output-tau  *)
Proof.
  intros. assert (lts p (a !) q1). assumption. apply OutputWithValue in H1.
  decompose record H1. subst. rename x into c. rename x0 into v.
  eapply TransitionShapeForOutputSimplified in H.
  edestruct (Congruence_Respects_Transition ((c ! v • 𝟘) ‖ q1) q2 τ). exists p. split. eauto with cgr. assumption.
  destruct H2. dependent induction H2.
  - inversion H2_; subst. right. exists q0. split. assumption. eauto with cgr. 
  - inversion H2_0.
  - inversion H2.
  - left. exists q0. split. assumption. 
    assert (lts ((c ! v • 𝟘) ‖ q0) ((c ⋉ v) !) (𝟘 ‖ q0)). constructor. constructor.
    edestruct (Congruence_Respects_Transition q2 (𝟘 ‖ q0) ((c ⋉ v) !)). exists ((c ! v • 𝟘) ‖ q0).
    split. eauto with cgr. assumption. destruct H5. exists x. split. assumption. eauto with cgr.
Qed.

Lemma ExtraAxiom : forall p1 p2 q1 q2 a,
      lts p1 (a !) q1 -> lts p2 (a !) q2 -> q1 ≡* q2 -> p1 ≡* p2.
Proof.
  intros. assert (lts p1 (a !) q1). assumption. apply OutputWithValue in H2.
  decompose record H2. subst. rename x into c. rename x0 into v.
  eapply TransitionShapeForOutputSimplified in H0.
  eapply TransitionShapeForOutputSimplified in H.
   transitivity ((c ! v • 𝟘) ‖ q1). assumption.
   transitivity ((c ! v • 𝟘) ‖ q2). eauto with cgr. eauto with cgr.
Qed.

Definition encode_channeldata (C : ChannelData) : gen_tree (nat + Channel) :=
match C with
  | cstC c => GenLeaf (inr c)
  | bvarC i => GenLeaf (inl i)
end.

Definition decode_channeldata (tree : gen_tree (nat + Channel)) : ChannelData :=
match tree with
  | GenLeaf (inr c) => cstC c
  | GenLeaf (inl i) => bvarC i
  | _ => bvarC 0
end.

Lemma encode_decide_channeldatas c : decode_channeldata (encode_channeldata c) = c.
Proof. case c. 
* intros. simpl. reflexivity.
* intros. simpl. reflexivity.
Qed.

#[global] Instance channeldata_countable : Countable ChannelData.
Proof.
  refine (inj_countable' encode_channeldata decode_channeldata _).
  apply encode_decide_channeldatas.
Qed.

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

Lemma Equation_dec : forall (x y : Equation Data) , {x = y} + {x <> y}.
Proof.
decide equality. apply Data_dec. apply Data_dec.
Qed.

#[global] Instance equation_dec : EqDecision (Equation Data). exact Equation_dec. Defined.

Definition encode_equation (E : Equation Data) : gen_tree (nat + Data) :=
match E with
  | D1 == D2 => GenNode 0 [GenLeaf (inr D1) ; GenLeaf (inr D2)]
end.

Definition decode_equation (tree : gen_tree (nat + Data)) : option (Equation Data) :=
match tree with
  | GenNode 0 [GenLeaf (inr d); GenLeaf (inr d')] => Some (d == d')
  | _ => None
end. 


Lemma encode_decide_equations p : decode_equation (encode_equation p) = Some p.
Proof. 
induction p.
* simpl. reflexivity.
Qed.

#[global] Instance equation_countable : Countable (Equation Data).
Proof.
  refine (inj_countable encode_equation decode_equation _).
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

Definition encode_TypeOfActions (a : TypeOfActions) : gen_tree (nat + (ChannelData + Data)) :=
match a with
  | act c v => GenNode 0 [GenLeaf (inr (inl c)) ; GenLeaf (inr (inr v))]
end.

Definition decode_TypeOfActions (tree :gen_tree (nat + (ChannelData + Data))) : option TypeOfActions :=
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

Definition encode_ExtAct_TypeOfActions (a : ExtAct TypeOfActions) : 
    gen_tree (nat + (ChannelData + Data)) :=
match a with
  | ActIn a => GenNode 0 [encode_TypeOfActions a]
  | ActOut a => GenNode 1 [encode_TypeOfActions a]
end.

Definition decode_ExtAct_TypeOfActions_raw (tree :gen_tree (nat + (ChannelData + Data))) 
  : option (ExtAct (option TypeOfActions)) :=
match tree with
  | GenNode 0 [l] => Some (ActIn (decode_TypeOfActions l))
  | GenNode 1 [l] => Some (ActOut (decode_TypeOfActions l))
  | _ => None
end.

Definition simpl_option (a : option (ExtAct (option TypeOfActions)))
  : option (ExtAct TypeOfActions) :=
match a with
  | Some (ActIn None) => None
  | Some (ActIn (Some b)) => Some (ActIn b)
  | Some (ActOut None) => None
  | Some (ActOut (Some b)) => Some (ActOut b)
  | None => None
end.

Definition decode_ExtAct_TypeOfActions (tree :gen_tree (nat + (ChannelData + Data))) 
  : option (ExtAct TypeOfActions) := simpl_option (decode_ExtAct_TypeOfActions_raw tree).

Lemma encode_decide_ExtAct_TypeOfActions a : 
  decode_ExtAct_TypeOfActions (encode_ExtAct_TypeOfActions  a) = Some a.
Proof. 
induction a. 
* unfold decode_ExtAct_TypeOfActions. simpl.
  rewrite encode_decide_TypeOfActions. eauto.
* unfold decode_ExtAct_TypeOfActions. simpl.
  rewrite encode_decide_TypeOfActions. eauto.
Qed.

#[global] Instance ExtAct_TypeOfActions_countable : Countable (ExtAct TypeOfActions).
Proof.
  eapply inj_countable with encode_ExtAct_TypeOfActions decode_ExtAct_TypeOfActions. 
  intro. apply encode_decide_ExtAct_TypeOfActions.
Qed.

Fixpoint encode_proc (p: proc) : gen_tree (nat + (((Equation Data ) + TypeOfActions) + ChannelData)) :=
  match p with
  | p ‖ q  => GenNode 0 [encode_proc p; encode_proc q]
  | c ! v • 𝟘  => GenLeaf (inr $ inl $ inr $ (c ⋉ v))
  | pr_var i => GenNode 2 [GenLeaf $ inl i]
  | rec x • P => GenNode 3 [GenLeaf $ inl x; encode_proc P]
  | If C Then A Else B => GenNode 4 [GenLeaf (inr ( inl (inl C))) ; encode_proc A; encode_proc B]
  | ν p => GenNode 5 [encode_proc p]
  | g gp => GenNode 1 [encode_gproc gp]
  end
with
encode_gproc (gp: gproc) : gen_tree (nat + (((Equation Data ) + TypeOfActions) + ChannelData)) :=
  match gp with
  | ① => GenNode 1 []
  | 𝟘 => GenNode 0 []
  | c ? p => GenNode 2 [GenLeaf (inr $ inr c); encode_proc p]
  | 𝛕 • p => GenNode 3 [encode_proc p]
  | gp + gq => GenNode 4 [encode_gproc gp; encode_gproc gq]
  end.


Fixpoint decode_proc (t': gen_tree (nat + (((Equation Data ) + TypeOfActions) + ChannelData))) : proc :=
  match t' with
  | GenNode 0 [ep; eq] => (decode_proc ep) ‖ (decode_proc eq)
  | GenLeaf (inr ( inl (inr a))) => (ChannelData_of a) ! (Data_of a) • 𝟘
  | GenNode 2 [GenLeaf (inl i)] => pr_var i
  | GenNode 3 [GenLeaf (inl i); egq] => rec i • (decode_proc egq)
  | GenNode 4 [GenLeaf (inr ( inl (inl C))); A; B] => If C Then (decode_proc A) Else (decode_proc B)
  | GenNode 5 [eq] => ν (decode_proc eq)
  | GenNode 1 [egp] => g (decode_gproc egp)
  | _ => ① 
  end
with
decode_gproc (t': gen_tree (nat + (((Equation Data ) + TypeOfActions) + ChannelData))): gproc :=
  match t' with
  | GenNode 1 [] => ①
  | GenNode 0 [] => 𝟘
  | GenNode 2 [GenLeaf (inr (inr c)); ep] => c ? (decode_proc ep)
  | GenNode 3 [eq] => 𝛕 • (decode_proc eq)
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
* intros. simpl. rewrite (encode_decide_procs p0). eauto.
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

Fixpoint moutputs_of (k : nat) p : gmultiset TypeOfActions := 
match p with
  | P ‖ Q => (moutputs_of k P) ⊎ (moutputs_of k Q)
  | pr_var _ => ∅
  | rec _ • _ => ∅
  | If E Then P Else Q => match (Eval_Eq E) with 
                          | Some true => moutputs_of k P
                          | Some false => moutputs_of k Q
                          | None => ∅
                          end
  | (cstC c) ! v • 𝟘 => {[+ ((cstC c) ⋉ v) +]}
  | (bvarC i) ! v • 𝟘 => if decide(k < (S i)) then {[+ ((bvarC (i - k)) ⋉ v) +]}
                                            else ∅
  | ν p => moutputs_of (S k) p
  | g _ => ∅
end.

Definition outputs_of p := dom (moutputs_of 0 p).

Lemma VarSwap_and_moutputs j p k : moutputs_of (j + S (S k)) p =
moutputs_of (j + S (S k)) (VarSwap_in_proc j p).
Proof.
  revert j k.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *; try multiset_solver.
  + assert (moutputs_of (j + S (S k)) p1 
      = moutputs_of (j + S (S k)) (VarSwap_in_proc j p1)) as eq1. 
    { eapply Hp. simpl. lia. }
    assert (moutputs_of (j + S (S k)) p2 
      = moutputs_of (j + S (S k)) (VarSwap_in_proc j p2)) as eq2. 
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto. 
  + case_eq (Eval_Eq e); intros; try multiset_solver.
    destruct b.
    ++ eapply Hp. simpl. lia.
    ++ eapply Hp. simpl. lia.
  + destruct c.
      * simpl. eauto.
      * simpl. destruct (decide (j + S (S k) < S n)).
        ++ destruct (decide (n = j)); subst.
           +++ rewrite decide_True ; try lia.
           +++ destruct (decide (n = S j)); subst.
               ++++ destruct (decide (j + S (S k) < S j)).
                    +++++ lia.
                    +++++ lia.
               ++++ rewrite decide_True ; try lia. eauto.
        ++ destruct (decide (n = j)); subst.
           +++ rewrite decide_False ; try lia. eauto.
           +++ destruct (decide (n = S j)); subst.
               ++++ rewrite decide_False ; try lia. eauto.
               ++++ rewrite decide_False ; try lia. eauto.
  + replace (S (j + S (S k)))%nat with ((S j) + S (S k))%nat by lia. eauto. 
Qed.

Lemma NewVarC_and_moutputs p j : moutputs_of (S j) (NewVarC j p) = moutputs_of j p.
Proof.
  revert j.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *; try multiset_solver.
  + assert (moutputs_of (S j) (NewVarC j p1)
      = moutputs_of j p1 ) as eq1. 
    { eapply Hp. simpl. lia. }
    assert (moutputs_of (S j) (NewVarC j p2)
      = moutputs_of j p2) as eq2. 
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto. 
  + case_eq (Eval_Eq e); intros; try multiset_solver.
    destruct b.
    ++ eapply Hp. simpl. lia.
    ++ eapply Hp. simpl. lia.
  + destruct c.
      * simpl. eauto.
      * simpl. destruct (decide (j < S n)).
        ++ rewrite decide_True; try lia. eauto.
        ++ rewrite decide_False; try lia. eauto.
Qed.

Lemma simpl_bvar_in_NewVar_ChannelData j c : NewVar_in_ChannelData j (NewVar_in_ChannelData j c) 
        = NewVar_in_ChannelData (S j) (NewVar_in_ChannelData j c).
Proof.
  destruct c.
  + simpl. eauto.
  + simpl. destruct (decide (j < S n)).
    ++ simpl. rewrite decide_True; try lia.
       rewrite decide_True; try lia. eauto.
    ++ simpl. rewrite decide_False; try lia.
       rewrite decide_False; try lia. eauto.
Qed.

Lemma simpl_bvar_in_NewVarC j p : NewVarC j (NewVarC j p) = NewVarC (S j) (NewVarC j p).
Proof.
  revert j.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *.
  + assert ((NewVarC j (NewVarC j p1)) = (NewVarC (S j) (NewVarC j p1))) as eq1.
    { eapply Hp. simpl. lia. }
    assert ((NewVarC j (NewVarC j p2)) = (NewVarC (S j) (NewVarC j p2))) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto.
  + eauto.
  + f_equal. eapply Hp. simpl; eauto.
  + assert ((NewVarC j (NewVarC j p1)) = (NewVarC (S j) (NewVarC j p1))) as eq1.
    { eapply Hp. simpl. lia. }
    assert ((NewVarC j (NewVarC j p2)) = (NewVarC (S j) (NewVarC j p2))) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto.
  + rewrite simpl_bvar_in_NewVar_ChannelData. eauto.
  + f_equal. eapply Hp. simpl; eauto.
  + destruct g0; simpl in *.
    - eauto.
    - eauto.
    - rewrite simpl_bvar_in_NewVar_ChannelData.
      assert ((NewVarC j (NewVarC j p)) = (NewVarC (S j) (NewVarC j p))) as eq.
      { eapply Hp. simpl. eauto. }
      rewrite eq. eauto.
    - assert ((NewVarC j (NewVarC j p)) = (NewVarC (S j) (NewVarC j p))) as eq.
      { eapply Hp. simpl. eauto. }
      rewrite eq. eauto.
    - assert (NewVarC j (NewVarC j (g g0_1)) = NewVarC (S j) (NewVarC j (g g0_1))) as eq1.
      { eapply Hp. simpl. lia. }
      assert (NewVarC j (NewVarC j (g g0_2)) = NewVarC (S j) (NewVarC j (g g0_2))) as eq2.
      { eapply Hp. simpl. lia. }
      inversion eq1. inversion eq2. eauto.
Qed.

Lemma simpl_bvar_in_NewVarCn j k p :(NewVarCn j k (NewVarC j p) = NewVarCn (S j) k (NewVarC j p)).
Proof.
  revert p j.
  induction k.
  - simpl; eauto.
  - intros; simpl. rewrite<- (NewVarCn_revert_def k _ j). rewrite IHk.
    rewrite<- (NewVarCn_revert_def k _ (S j)). f_equal.
    replace (NewVarC j (NewVarCn j k (NewVarC j p))) with (NewVarCn j 1 (NewVarCn j k (NewVarC j p))).
    2 : { eauto. } rewrite simpl_bvar_in_NewVarC. eauto.
Qed.

Lemma NewVarCn_and_moutputs j p k : moutputs_of j p =
moutputs_of (k + j) (NewVarCn j k p).
Proof.
  revert p j.
  induction k.
  + simpl; eauto.
  + intros. simpl. rewrite<- NewVarCn_revert_def.
    replace (S (k + j))%nat with (k + (S j))%nat by lia.
    assert ((NewVarCn j k (NewVarC j p)) = (NewVarCn (S j) k (NewVarC j p))) as eq.
    { rewrite simpl_bvar_in_NewVarCn. eauto. } rewrite eq. rewrite<- (IHk  (NewVarC j p)).
    rewrite NewVarC_and_moutputs. eauto.
Qed.

Lemma moutputs_and_NewVar k p j : moutputs_of (k + j) p = moutputs_of (k + S j) (NewVarC j p).
Proof.
  revert j k.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *.
  + assert (moutputs_of (k + j) p1 = moutputs_of (k + S j) (NewVarC j p1)) as eq1.
    { eapply Hp. lia. }
    assert (moutputs_of (k + j) p2 = moutputs_of (k + S j) (NewVarC j p2)) as eq2.
    { eapply Hp. lia. }
    rewrite eq1, eq2. eauto.
  + eauto.
  + eauto.
  + assert (moutputs_of (k + j) p1 = moutputs_of (k + S j) (NewVarC j p1)) as eq1.
    { eapply Hp. lia. }
    assert (moutputs_of (k + j) p2 = moutputs_of (k + S j) (NewVarC j p2)) as eq2.
    { eapply Hp. lia. }
    rewrite eq1, eq2. eauto.
  + destruct c.
      * simpl. eauto.
      * destruct (decide (k + j < S n)).
        ++ simpl. rewrite decide_True; try lia.
           rewrite decide_True; try lia.
           replace ((S n - (k + S j)))%nat with (n - (k + j))%nat by lia.
           eauto.
        ++ simpl. destruct (decide (j < S n)).
           +++ rewrite decide_False; try lia. eauto.
           +++ rewrite decide_False; try lia. eauto.
  + replace ((S (k + j)))%nat with (k + S j)%nat by lia.
    replace (S (k + S j))%nat with (k + S (S j))%nat by lia.
    eapply Hp. simpl. eauto.
  + eauto.
Qed.

Lemma NewVarCn_and_moutputs2 j p k : moutputs_of k p =
moutputs_of (j + k) (NewVarCn 0 j p).
Proof.
  revert p k.
  induction j.
  + intros; simpl; eauto.
  + intros. simpl. rewrite<- NewVarCn_revert_def.
    replace (S (j+ k))%nat with (j + (S k))%nat by lia.
    rewrite<- (IHj (NewVarC 0 p)).
    assert ((NewVarCn j k (NewVarC j p)) = (NewVarCn (S j) k (NewVarC j p))) as eq.
    { rewrite simpl_bvar_in_NewVarCn. eauto. } replace k%nat with (k + 0)%nat by lia.
    rewrite moutputs_and_NewVar. replace (k + 1)%nat with (S k)%nat by lia.
    replace (S (k + 0))%nat with (S k)%nat by lia. eauto.
Qed.

Lemma mo_equiv_spec_step : forall {p q k}, p ≡ q -> moutputs_of k p = moutputs_of k q.
Proof. intros. revert k. dependent induction H ; try multiset_solver; simpl in *; try rewrite H; eauto.
+ intros. replace (S (S k))%nat with (0 + (S (S k)))%nat by lia. rewrite VarSwap_and_moutputs. eauto.
+ intros. replace (S (S k))%nat with (0 + (S (S k)))%nat by lia. symmetry. rewrite VarSwap_and_moutputs. eauto.
+ intros. f_equal. replace (NewVarC 0 q) with (NewVarCn 0 1 q); eauto.
  replace (S k)%nat with (1 + k)%nat; eauto. rewrite<- NewVarCn_and_moutputs2. eauto.
+ intros. f_equal. replace (NewVarC 0 q) with (NewVarCn 0 1 q); eauto.
  replace (S k)%nat with (1 + k)%nat; eauto. rewrite<- NewVarCn_and_moutputs2. eauto.
+ destruct (Eval_Eq C); eauto. destruct b; eauto.
+ destruct (Eval_Eq C); eauto. destruct b; eauto.
Qed.

Lemma mo_equiv_spec : forall {p q k}, p ≡* q -> moutputs_of k p = moutputs_of k q.
Proof.
  intros p q l hcgr.
  induction hcgr.
  - now eapply mo_equiv_spec_step.
  - etrans; eauto.
Qed.

Lemma simpl_new_output n k c v : moutputs_of k (c ! v • 𝟘) = moutputs_of k (Ѵ n (VarC_add n c ! v • 𝟘)).
Proof.
  revert k c v.
  induction n.
  - intros; simpl; eauto. destruct c; simpl; eauto.
  - intros; simpl. destruct c ; simpl.
    + replace (c ! v • 𝟘) with (VarC_add n c ! v • 𝟘) by eauto.
      rewrite<- IHn. simpl. eauto.
    + destruct (decide (k < S n0)).
      ++ replace (S (n + n0))%nat with (n + S n0)%nat by lia.
         replace ((n + S n0)%nat ! v • 𝟘) with (VarC_add n (S n0) ! v • 𝟘) by (simpl; eauto). rewrite<- IHn.
         simpl. rewrite decide_True; try lia. eauto.
      ++ replace (S (n + n0))%nat with (n + S n0)%nat by lia.
         replace ((n + S n0)%nat ! v • 𝟘) with (VarC_add n (S n0) ! v • 𝟘) by (simpl; eauto). rewrite<- IHn.
         simpl. rewrite decide_False; try lia. eauto.
Qed.

Lemma mo_spec p a q : lts p (a !) q -> moutputs_of 0 p = {[+ a +]} ⊎ moutputs_of 0 q.
Proof.
  intros l. assert (lts p (a !) q). assumption. apply OutputWithValue in H.
  decompose record H. subst. rename x into c. rename x0 into v.
  eapply TransitionShapeForOutputSimplified in l. eapply mo_equiv_spec in l. simpl in l.
  rewrite l. f_equal. simpl. destruct c; eauto.
  replace (n - 0)%nat with n%nat; try lia. eauto.
Qed.

Lemma mo_spec_l e a k :
  a ∈ moutputs_of k e -> {e' | lts (Ѵ  k e) (ActExt $ ActOut a) (Ѵ  k e') /\ moutputs_of k e' = moutputs_of k e ∖ {[+ a +]}}.
Proof.
  intros mem.
  dependent induction e.
  + cbn in mem.
    destruct (decide (a ∈ moutputs_of k e1)).
    destruct (IHe1 a k e) as (e1' & lts__e1 & eq).
    exists (pr_par e1' e2). repeat split; eauto with ccs.
    eapply inversion_res_ext in lts__e1. eapply lts_res_ext_n.
    eapply lts_parL. eauto.
    multiset_solver.
    destruct (decide (a ∈ moutputs_of k e2)).
    destruct (IHe2 a k e) as (e2' & lts__e2 & eq).
    exists (pr_par e1 e2'). repeat split; eauto with ccs.
    eapply inversion_res_ext in lts__e2. eapply lts_res_ext_n.
    eapply lts_parR. eauto.
    multiset_solver.
    contradict mem. intro mem. multiset_solver.
  + exfalso. multiset_solver.
  + exfalso. multiset_solver.
  + simpl in *. case_eq (Eval_Eq e1); intros.
    ++ rewrite H in mem. destruct b.
       +++ eapply IHe1 in mem as (e' & l & eq).
           exists e'. split ;eauto. eapply lts_res_ext_n. eapply lts_ifOne; eauto.
           eapply inversion_res_ext. eauto.
       +++ eapply IHe2 in mem as (e' & l & eq).
           exists e'. split ;eauto. eapply lts_res_ext_n. eapply lts_ifZero; eauto.
           eapply inversion_res_ext. eauto.
    ++ rewrite H in mem. exfalso. inversion mem.
  + exists (g 𝟘).
    destruct c.
    ++ simpl in *.
       assert (a = c ⋉ d). multiset_solver. subst.
       repeat split; eauto with ccs. eapply lts_res_ext_n. simpl. constructor. multiset_solver.
    ++ simpl in *. destruct (decide (k < S n)).
       +++ split. eapply lts_res_ext_n. simpl. destruct a. assert (c ⋉ d0 = (n - k) ⋉ d). multiset_solver.
           inversion H; subst. simpl in *. replace (k + (n - k))%nat with n%nat by lia. constructor.
           multiset_solver.
       +++ inversion mem.
  + simpl in *. eapply IHe in mem as (e' & eq1 & eq2).
    exists (ν e'). split. rewrite BigNew_reverse_def_one. rewrite BigNew_reverse_def_one.
    simpl in *; eauto. simpl. eauto.
  + simpl in mem. exfalso. set_solver. 
Qed.

Lemma mo_spec_r e a k:
  {e' | lts (Ѵ  k e) (ActExt $ ActOut a) (Ѵ  k e') /\ moutputs_of k e' = moutputs_of k e ∖ {[+ a +]}} -> a ∈ moutputs_of k e.
Proof.
  dependent induction e; intros (e' & l & mem).
  + cbn. eapply inversion_res_ext in l.
    inversion l; subst.
    eapply gmultiset_elem_of_disj_union. left.
    eapply IHe1. exists p2. split. eapply lts_res_ext_n; eauto. cbn in mem.
    multiset_solver.
    eapply gmultiset_elem_of_disj_union. right.
    eapply IHe2. exists q2. split. eapply lts_res_ext_n; eauto. cbn in mem.
    multiset_solver.
  + eapply inversion_res_ext in l. inversion l.
  + eapply inversion_res_ext in l. inversion l.
  + eapply inversion_res_ext in l. inversion l; subst; simpl in *; rewrite H4 in mem; rewrite H4.
    ++ destruct a. eapply IHe1 ; eauto. exists e'. split. eapply lts_res_ext_n. simpl; eauto. multiset_solver.
    ++ destruct a. eapply IHe2 ; eauto. exists e'. split. eapply lts_res_ext_n. simpl; eauto. multiset_solver.
  + eapply inversion_res_ext in l. inversion l; subst. destruct a.
    inversion H; subst. destruct c0.
    ++ simpl. subst. multiset_solver.
    ++ simpl. rewrite decide_True; try lia. replace (k + n - k)%nat with n%nat by lia. multiset_solver.
  + eapply inversion_res_ext in l. inversion l; subst. destruct a. simpl. eapply IHe. exists p'. split.
    eapply lts_res_ext_n. simpl in *. rewrite<- VarC_add_revert_def in H1. simpl in *. eauto. multiset_solver.
  + destruct a. simpl in *. eapply inversion_res_ext in l. now eapply guarded_does_no_output in l.
Qed.

Lemma outputs_of_spec2 p a : a ∈ outputs_of p -> {q | lts p (ActExt (ActOut a)) q}.
Proof.
  intros mem.
  eapply gmultiset_elem_of_dom in mem.
  eapply mo_spec_l in mem.
  firstorder.
Qed.

Lemma outputs_of_spec1_raw (e : proc) (a : TypeOfActions) k : {e' | lts (Ѵ  k e) (ActExt (ActOut a)) (Ѵ  k e')} 
      -> a ∈ moutputs_of k e.
Proof.
  dependent induction e; intros (e' & l).
  + cbn. eapply inversion_res_ext in l.
    inversion l; subst.
    eapply gmultiset_elem_of_disj_union. left.
    eapply IHe1. exists p2. eapply lts_res_ext_n; eauto.
    eapply gmultiset_elem_of_disj_union. right.
    eapply IHe2. exists q2. eapply lts_res_ext_n; eauto.
  + eapply inversion_res_ext in l. inversion l.
  + eapply inversion_res_ext in l. inversion l.
  + eapply inversion_res_ext in l. inversion l; subst; simpl in *; rewrite H4.
    ++ destruct a. eapply IHe1 ; eauto. exists e'. eapply lts_res_ext_n. simpl; eauto.
    ++ destruct a. eapply IHe2 ; eauto. exists e'. eapply lts_res_ext_n. simpl; eauto.
  + eapply inversion_res_ext in l. inversion l; subst. destruct a.
    inversion H; subst. destruct c0.
    ++ simpl. subst. multiset_solver.
    ++ simpl. rewrite decide_True; try lia. replace (k + n - k)%nat with n%nat by lia. multiset_solver.
  + eapply inversion_res_ext in l. inversion l; subst. destruct a. simpl. eapply IHe. exists p'.
    eapply lts_res_ext_n. simpl in *. rewrite<- VarC_add_revert_def in H1. simpl in *. eauto.
  + destruct a. simpl in *. eapply inversion_res_ext in l. now eapply guarded_does_no_output in l.
Qed.

Lemma outputs_of_spec1 (p : proc) (a : TypeOfActions) (q : proc) : lts p (ActExt (ActOut a)) q
      -> a ∈ outputs_of p.
Proof.
  intros mem.
  eapply gmultiset_elem_of_dom.
  eapply outputs_of_spec1_raw.
  firstorder.
Qed.

Fixpoint lts_set_output (p : proc) (a : TypeOfActions) : gset proc:=
match p with
  | p1 ‖ p2 => 
      let ps1 := lts_set_output p1 a in
      let ps2 := lts_set_output p2 a in
      (set_map (fun p => p ‖ p2) ps1) ∪ (set_map (fun p => p1 ‖ p) ps2)
  | pr_var _ => ∅
  | rec _ • _ => ∅
  | If E Then A Else B => match (Eval_Eq E) with 
                          | Some true => lts_set_output A a
                          | Some false => lts_set_output B a
                          | None => ∅
                          end
  | c ! v • 𝟘 => if decide(a = (c ⋉ v)) then {[ (g 𝟘) ]} else ∅
  | ν p => (set_map (fun q => ν q) (lts_set_output p (VarC_TypeOfActions_add 1 a))) 
  | g _  => ∅
end.

Fixpoint lts_set_input_g (g : gproc) (a : TypeOfActions) : gset proc :=
  match g with
  | c ? p => if decide(ChannelData_of a = c) then {[ p^(Data_of a) ]} else ∅
  | g1 + g2 => lts_set_input_g g1 a ∪ lts_set_input_g g2 a
  | ① => ∅
  | 𝟘 => ∅
  | 𝛕 • p => ∅
  end.

Fixpoint lts_set_input (p : proc) (a : TypeOfActions) : gset proc :=
match p with
  | p1 ‖ p2 =>
      let ps1 := lts_set_input p1 a in
      let ps2 := lts_set_input p2 a in
      (set_map (fun p => p ‖ p2) ps1) ∪ (set_map (fun p => p1 ‖ p) ps2)
  | pr_var _ => ∅
  | rec _ • _ => ∅ 
  | c ! v • 𝟘 => ∅
  | If E Then A Else B => match (Eval_Eq E) with 
                          | Some true => lts_set_input A a
                          | Some false => lts_set_input B a
                          | None => ∅
                          end
  | ν p => set_map (fun q => ν q) (lts_set_input p (VarC_TypeOfActions_add 1 a)) 
  | g gp => lts_set_input_g gp a  
  end.

Fixpoint lts_set_tau_g (gp : gproc) : gset proc :=
match gp with
  | c ? p => ∅
  | ① => ∅
  | 𝟘 => ∅
  | 𝛕 • p => {[ p ]}
  | gp1 + gp2 => lts_set_tau_g gp1 ∪ lts_set_tau_g gp2
end.


Fixpoint lts_set_tau (p : proc) : gset proc :=
match p with
  | p1 ‖ p2 =>
      let ps1_tau : gset proc := set_map (fun p => p ‖ p2) (lts_set_tau p1) in
      let ps2_tau : gset proc := set_map (fun p => p1 ‖ p) (lts_set_tau p2) in
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
                          | Some true => lts_set_tau A
                          | Some false => lts_set_tau B
                          | None => ∅
                          end
  | ν p => set_map (fun q => ν q) (lts_set_tau p)
  | g gp => lts_set_tau_g gp
end.

Lemma lts_set_output_spec0 p a q : q ∈ lts_set_output p a -> lts p (ActExt (ActOut a)) q.
Proof.
  intro mem.
  dependent induction p; simpl in mem; try now inversion mem.
  - eapply elem_of_union in mem as [mem | mem]. 
    * eapply elem_of_list_to_set, list_elem_of_fmap in mem as (q' & eq & mem). subst.
    apply lts_parL. apply IHp1. rewrite elem_of_elements in mem. set_solver.
    * eapply elem_of_list_to_set, list_elem_of_fmap in mem as (q' & eq & mem). subst.
    apply lts_parR. apply IHp2. rewrite elem_of_elements in mem. exact mem.
  - case_eq (Eval_Eq e).
    * intros. destruct b.
      ** rewrite H in mem. eapply lts_ifOne; eauto.
      ** rewrite H in mem. eapply lts_ifZero; eauto.
    * intros. rewrite H in mem. exfalso. inversion mem.
  -  case (TypeOfActions_dec a (c ⋉ d)) in mem.
    + rewrite e. rewrite e in mem.
      destruct (decide (c ⋉ d = c ⋉ d)). subst. assert (q = (g 𝟘)). set_solver.
      rewrite H. apply lts_output. exfalso. set_solver.
    + destruct (decide (a = c ⋉ d)). exfalso. apply n. assumption. set_solver.
  - eapply elem_of_list_to_set, list_elem_of_fmap in mem as (q' & eq & mem). subst.
    apply lts_res_ext. rewrite elem_of_elements in mem. eapply IHp in mem. simpl. destruct a. eauto.
Qed.

Lemma lts_set_output_spec1 p a q : lts p (ActExt $ ActOut a) q -> q ∈ lts_set_output p a.
Proof.
  intro l. dependent induction l; try set_solver.
  - simpl. destruct (decide (c ⋉ v = c ⋉ v)) as [eq | not_eq]. 
    + set_solver.
    + exfalso. apply not_eq. reflexivity.
  - simpl in *. rewrite H. eapply IHl; eauto ; simpl.
  - simpl in *. rewrite H. eapply IHl; eauto ; simpl.
  - simpl in *. destruct a. try set_solver.
Qed.

Lemma lts_set_input_spec0 p a q : q ∈ lts_set_input p a -> lts p (ActExt $ ActIn a) q.
Proof.
  intro mem.
  dependent induction p; simpl in mem; try set_solver.
  + eapply elem_of_union in mem. destruct mem.
    ++ eapply elem_of_list_to_set in H.
       eapply list_elem_of_fmap in H as (q' & eq & mem). subst.
       rewrite elem_of_elements in mem. eauto with cgr.
    ++ eapply elem_of_list_to_set in H.
       eapply list_elem_of_fmap in H as (q' & eq & mem). subst.
       rewrite elem_of_elements in mem. eauto with cgr.
  + case_eq (Eval_Eq e).
    - intros. rewrite H in mem. destruct b.
      ++ eapply lts_ifOne; eauto.
      ++ eapply lts_ifZero; eauto.
    - intros. rewrite H in mem. exfalso. inversion mem.
  + eapply elem_of_list_to_set, list_elem_of_fmap in mem as (q' & eq & mem). subst.
    apply lts_res_ext. rewrite elem_of_elements in mem. eapply IHp in mem. simpl. destruct a. eauto. 
  + dependent induction g0; simpl in mem; try set_solver.
      ++ destruct (decide (ChannelData_of a = c)).
         +++ subst. eapply elem_of_singleton_1 in mem. subst. destruct a. simpl. apply lts_input.
         +++ destruct a. simpl in *. inversion mem.
      ++ eapply elem_of_union in mem. destruct mem; eauto with cgr.
Qed.

Lemma lts_set_input_spec1 p a q : lts p (ActExt $ ActIn a) q -> q ∈ lts_set_input p a.
Proof.
  intro l. destruct a. destruct d.
  + dependent induction l; try set_solver.
    ++ simpl. rewrite decide_True; eauto. set_solver.
    ++ simpl in *. rewrite H. eauto.
    ++ simpl in *. rewrite H. eauto.
  + dependent induction l; try set_solver.
    ++ simpl. rewrite decide_True; eauto. set_solver.
    ++ simpl in *. rewrite H. eauto.
    ++ simpl in *. rewrite H. eauto.
Qed.


Lemma lts_set_tau_spec0 p q : q ∈ lts_set_tau p -> lts p τ q.
Proof.
  - intro mem.
    dependent induction p; simpl in mem.
    + eapply elem_of_union in mem. destruct mem as [mem1 | mem2].
      ++ eapply elem_of_union in mem1.
         destruct mem1.
         eapply elem_of_union in H as [mem1 | mem2]. 
         eapply elem_of_list_to_set, list_elem_of_fmap in mem1 as (t' & eq & h); subst.
         rewrite elem_of_elements in h. eauto with cgr.
         eapply elem_of_list_to_set, list_elem_of_fmap in mem2 as (t' & eq & h); subst.
         rewrite elem_of_elements in h. eauto with cgr.
         eapply elem_of_list_to_set, list_elem_of_In, in_flat_map in H as (t' & eq & h); subst.
         eapply list_elem_of_In, list_elem_of_fmap in h as ((t1 & t2) & eq' & h'). subst.
         eapply list_elem_of_In, in_prod_iff in h' as (mem1 & mem2).
         eapply list_elem_of_In in mem1. rewrite elem_of_elements in mem1.
         eapply list_elem_of_In in mem2. rewrite elem_of_elements in mem2.
         eapply lts_set_output_spec0 in mem1.
         eapply lts_set_input_spec0 in mem2. destruct t'. eapply lts_comL. exact mem1. exact mem2.
      ++ eapply elem_of_list_to_set, list_elem_of_In, in_flat_map in mem2 as (t' & eq & h); subst.
         eapply list_elem_of_In, list_elem_of_fmap in h as ((t1 & t2) & eq' & h'). subst.
         eapply list_elem_of_In, in_prod_iff in h' as (mem1 & mem2).
         eapply list_elem_of_In in mem1. rewrite elem_of_elements in mem1.
         eapply list_elem_of_In in mem2. rewrite elem_of_elements in mem2.
         eapply lts_set_input_spec0 in mem1.
         eapply lts_set_output_spec0 in mem2. destruct t'. eapply lts_comR. exact mem2. exact mem1.
    + inversion mem.
    + eapply elem_of_singleton_1 in mem. subst; eauto with cgr.
    + case_eq (Eval_Eq e); intros; rewrite H in mem.
      ++ destruct b.
         +++ eapply lts_ifOne; eauto.
         +++ eapply lts_ifZero; eauto.
      ++ exfalso. inversion mem.
    + inversion mem.
    + eapply elem_of_list_to_set, list_elem_of_fmap in mem as (t' & eq & h); subst.
      eapply lts_res_tau. eapply IHp. eapply elem_of_elements. eauto.
    + dependent induction g0; simpl in mem; try set_solver;
        try eapply elem_of_singleton_1 in mem; subst; eauto with cgr.
      eapply elem_of_union in mem as [mem1 | mem2]; eauto with cgr.
Qed.

Lemma lts_set_tau_spec1 p q : lts p τ q -> q ∈ lts_set_tau p.
Proof. 
  intro l. dependent induction l; simpl; try set_solver.
  - rewrite H. set_solver. 
  - rewrite H. set_solver. 
  - eapply elem_of_union. left.
    eapply elem_of_union. right.
    eapply elem_of_list_to_set.
    rewrite list_elem_of_In. rewrite in_flat_map.
    exists (c ⋉ v). split.
    + eapply list_elem_of_In, elem_of_elements.
      eapply outputs_of_spec1. eauto.
    + eapply list_elem_of_In, list_elem_of_fmap.
      exists (p2 , q2). split.
      ++ reflexivity.
      ++ eapply list_elem_of_In, in_prod_iff; split; eapply list_elem_of_In, elem_of_elements.
         eapply lts_set_output_spec1; eauto with ccs.
         eapply lts_set_input_spec1; eauto with ccs.
  - eapply elem_of_union. right.
    eapply elem_of_list_to_set.
    rewrite list_elem_of_In. rewrite in_flat_map.
    exists (c ⋉ v). split.
    + eapply list_elem_of_In, elem_of_elements.
      eapply outputs_of_spec1. exact l1.
    + eapply list_elem_of_In, list_elem_of_fmap.
      exists (q2 , p2). split.
      ++ reflexivity.
      ++ eapply list_elem_of_In, in_prod_iff; split; eapply list_elem_of_In, elem_of_elements.
         eapply lts_set_input_spec1; eauto with ccs.
         eapply lts_set_output_spec1; eauto with ccs.
Qed.


Definition lts_set (p : proc) (α : ActIO TypeOfActions): gset proc :=
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

Definition non_blocking_output (μ : ExtAct TypeOfActions) := (is_output μ).

(** ** VACCS satisfies the axioms for soundness and completeness *)

#[global] Program Instance VACCS_ExtAction : ExtAction (ExtAct TypeOfActions) :=
  {| non_blocking η := non_blocking_output η ;
      dual μ1 μ2 := ext_act_match μ1 μ2 |}.
Next Obligation.
 intros. simpl. destruct a.
 * right. intro Hyp. destruct Hyp as (a' & eq). inversion eq.
 * left. exists a. eauto.
Defined.
Next Obligation.
 intros ? ? ? dual nb; simpl in *.
 destruct nb as (a & eq). subst.
 eapply simplify_match_output in dual.
 subst. destruct H. inversion H.
Defined.
Next Obligation.
 intros μ; simpl in *.
 exists (InputOutputActions.co μ).
 symmetry. eapply dual_co.
Defined.
Next Obligation.
  intros μ1 μ2 dual; subst.
  simpl in *.
  destruct μ2 as [ (* Input *) a' | (* Output *) a' ].
  + apply simplify_match_input in dual; subst. eauto.
  + apply simplify_match_output in dual; subst. eauto.
Defined.

#[global] Program Instance VACCS_gLts : gLts proc VACCS_ExtAction := 
  {| lts_step x ℓ y  := lts x ℓ y ;
     lts_state_eqdec := proc_dec ;
     lts_step_decidable p α q := lts_dec p α q ;
     lts_refuses p := proc_stable p;
     lts_refuses_decidable p α := proc_stable_dec p α 
    |}.
Next Obligation.
  intros p [[a|a]|]; intro hs;eapply gset_nempty_ex in hs as (r & l); eapply lts_set_spec0 in l; 
  exists r; assumption.
Qed.
Next Obligation.  
  intros p [[a|a]|]; intros (q & mem); intro eq; eapply lts_set_spec1 in mem; set_solver.
Qed.

#[global] Program Instance VACCS_gLtsEq : gLtsEq proc VACCS_ExtAction := 
  {| eq_rel x y  := cgr x y;
     eq_spec p q α := Congruence_Respects_Transition p q α |}.

#[global] Program Instance VACCS_gLtsOBA : gLtsOba proc.
(*   {| lts_oba_output_commutativity p q r a α := OBA_with_FB_First_Axiom p q r a α;
     lts_oba_output_confluence p q1 q2 a μ := OBA_with_FB_Second_Axiom p q1 q2 a μ;
     lts_oba_output_deter p1 p2 p3 a := OBA_with_FB_Third_Axiom p1 p2 p3 a;
     lts_oba_output_tau p q1 q2 a := OBA_with_FB_Fifth_Axiom p q1 q2 a;
     lts_oba_output_deter_inv p1 p2 q1 q2 a := ExtraAxiom p1 p2 q1 q2 a;
     lts_oba_mo p := moutputs_of 0 p 
  |}. *)
Next Obligation. (* lts_oba_non_blocking_action_delay *)
  intros ? ? ? ? ? nb l1 l2 ;simpl in *.
  destruct nb as (a & eq); subst. 
  eapply OBA_with_FB_First_Axiom; eauto.
Qed.
Next Obligation. (* lts_oba_non_blocking_action_confluence *)
  intros ? ? ? ? ? nb eq l1 l2 ;simpl in *.
  destruct nb as (a & eq'); subst.
  eapply OBA_with_FB_Second_Axiom; eauto.
Qed.
Next Obligation. (* lts_oba_output_tau *)
  intros ? ? ? ? nb l1 l2 ;simpl in *.
  destruct nb as (a & eq); subst.
  eapply OBA_with_FB_Fifth_Axiom in l1 as cases; eauto.
  destruct cases as [computation_without_a | computation_with_a].
  + left. destruct computation_without_a. 
    eexists; eauto.
  + right. exists (ActIn a). split; eauto.
    unfold sc. simpl. eauto.
Qed.
Next Obligation. (* lts_oba_output_deter *)
  intros ? ? ? ? nb l1 l2 ;simpl in *.
  destruct nb as (a & eq); subst. 
  eapply OBA_with_FB_Third_Axiom; eauto.
Qed.
Next Obligation. (* lts_oba_non_blocking_action_deter_inv *)
  intros ? ? ? ? ? nb l1 l2 ;simpl in *.
  destruct nb as (a & eq); subst.
  eapply ExtraAxiom; eauto.
Qed.

#[global] Program Instance VACCS_gLtsOBAFB : gLtsObaFB proc (ExtAct TypeOfActions).
Next Obligation.
  intros ? ? ? ? ? nb dual l1 l2 ;simpl in *.
  destruct nb as (a & eq); subst. symmetry in dual.
  eapply simplify_match_output in dual; subst.
  eapply OBA_with_FB_Fourth_Axiom; eauto.
Qed.

Definition label_to_output (a : TypeOfActions) : ExtAct TypeOfActions := ActOut a.

Definition mo_label_to_mo_output (m : gmultiset TypeOfActions) : gmultiset (ExtAct TypeOfActions) :=
    gmultiset_map label_to_output m.

#[global] Program Instance VACCS_gFiniteOutputChain_LtsOba
 : FiniteOutputChain_LtsOba proc :=
  {| lts_oba_mo p := mo_label_to_mo_output (moutputs_of 0 p) ; |}.
Next Obligation.
  intros ? ? ? nb l.
  destruct η as [a | a].
  + exfalso. inversion nb. inversion H.
  + simpl. eapply elem_of_gmultiset_map.
    exists a. split.
      ++ unfold label_to_output. eauto.
      ++ eapply mo_spec_r. 
         exists p2. split ;simpl ; eauto. 
         eapply mo_spec in l. multiset_solver.
Defined.
Next Obligation.
  intros ? ? Hyp. 
  eapply elem_of_gmultiset_map in Hyp.
  assert ({ x : TypeOfActions | η = label_to_output x ∧ x ∈ moutputs_of 0 p1}) as (a & eq & mem).
  eapply choice; eauto. intros.
  destruct (decide (η = label_to_output x)) as [eq | not_eq].
  + destruct (decide (x ∈ moutputs_of 0 p1)).
    ++ left. split; eauto.
    ++ right. intro Hyp'. destruct Hyp' as (eq' & imp). contradiction.
  + right. intro Hyp'. destruct Hyp' as (eq' & imp). contradiction.
  + eapply mo_spec_l in mem as (q & l & eq'). simpl; subst; eauto.
    exists q. split.
    ++ exists a. subst. eauto.
    ++ unfold label_to_output. exact l.
Defined.
Next Obligation.
  intros ? ? ? nb Hyp;simpl in *.
  destruct nb as (a & eq). subst.
  assert (moutputs_of 0 p = {[+ a +]} ⊎ moutputs_of 0 q) as mem.
  eapply mo_spec. exact Hyp.
  rewrite mem. simpl in *. unfold mo_label_to_mo_output at 1.
  rewrite gmultiset_map_disj_union. rewrite gmultiset_map_singleton.
  unfold label_to_output at 1. reflexivity.
Qed.

#[global] Program Instance VACCS_gLtsFiniteImage : FiniteImagegLts proc (ExtAct TypeOfActions).
Next Obligation.
  intros p ℓ. unfold dsig.
  destruct ℓ as [[a|a]|].
  - eapply (in_list_finite (elements (lts_set_input p a))).
    intros q Htrans%bool_decide_unpack.
    now eapply elem_of_elements, lts_set_input_spec1.
  - eapply (in_list_finite (elements (lts_set_output p a))).
    intros q Htrans%bool_decide_unpack.
    now eapply elem_of_elements, lts_set_output_spec1.
  - eapply (in_list_finite (elements (lts_set_tau p))).
    intros q Htrans%bool_decide_unpack.
    now eapply elem_of_elements, lts_set_tau_spec1.
Defined.

#[global] Program Instance Interaction_between_parallel_VACCS :
  Prop_of_Inter proc proc (ExtAct TypeOfActions) dual :=
  {| lts_essential_actions_left p := set_map ActOut (outputs_of p) ;
       lts_essential_actions_right q := set_map ActOut (outputs_of q)|}.
Next Obligation.
  intros ? ? Hyp ;simpl in *.
  unfold set_map in Hyp. simpl in *.
  eapply elem_of_list_to_set in Hyp.
  eapply list_elem_of_fmap in Hyp.
  destruct ξ.
  + exfalso. destruct Hyp as (a' & eq & mem). inversion eq.
  + eapply outputs_of_spec2. destruct Hyp as (a' & eq & mem).
    inversion eq. subst. eapply elem_of_elements. eauto.
Defined.
Next Obligation.
  intros q ? Hyp ;simpl in *.
  unfold set_map in Hyp. simpl in *.
  eapply elem_of_list_to_set in Hyp.
  eapply list_elem_of_fmap in Hyp.
  destruct ξ.
  + exfalso. destruct Hyp as (a' & eq & mem). inversion eq.
  + eapply outputs_of_spec2. destruct Hyp as (a' & eq & mem).
    inversion eq. subst. eapply elem_of_elements. eauto.
Defined.
Next Obligation.
  intros ? ? ? q ? q' ? ? inter;simpl in *.
  destruct μ1 as [ (*Input*) a | (*Output*) a].
  + right. eapply simplify_match_input in inter. subst.
    eapply elem_of_list_to_set.
    eapply list_elem_of_fmap. exists a. split; eauto. 
    eapply elem_of_elements. eapply outputs_of_spec1; eauto.
  + left. eapply simplify_match_output in inter. subst.
    eapply elem_of_list_to_set.
    eapply list_elem_of_fmap. exists a. split; eauto. 
    eapply elem_of_elements. eapply outputs_of_spec1; eauto.
Defined.
Next Obligation.
  intros ξ p;simpl in *.
  destruct ξ as [ (*Input*) a | (*Output*) a ].
  + exact empty. 
  + exact {[ ActIn a ]}.
Defined.
Next Obligation.
  unfold Interaction_between_parallel_VACCS_obligation_4.
  intros ? ? ? ? q mem l inter;simpl in *. 
  eapply elem_of_list_to_set in mem.
  eapply list_elem_of_fmap in mem.
  destruct mem as ( a & eq & mem ); subst.
  symmetry in inter. eapply simplify_match_output in inter. subst. set_solver.
Defined.
Next Obligation.
  intros ξ q;simpl in *.
  destruct ξ as [ (*Input*) a | (*Output*) a ].
  + exact empty. 
  + exact {[ ActIn a ]}.
Defined.
Next Obligation.
  unfold Interaction_between_parallel_VACCS_obligation_6.
  intros ? ? ? ? q mem l inter;simpl in *. 
  eapply elem_of_list_to_set in mem.
  eapply list_elem_of_fmap in mem.
  destruct mem as ( a & eq & mem ); subst. symmetry in inter.
  symmetry in inter. eapply simplify_match_output in inter. subst. set_solver.
Defined.

#[global] Program Instance Interaction_between_VACCS_and_MB: Prop_of_Inter proc (mb (ExtAct TypeOfActions)) (ExtAct TypeOfActions) fw_inter :=
    {| lts_essential_actions_left p := empty ;
       lts_essential_actions_right m := dom (mb_without_not_nb m) ; 
       lts_co_inter_action_right m := fun x => empty |}.
Next Obligation. 
  intros ? ? Hyp ;simpl in *.
  inversion Hyp.
Qed.
Next Obligation.
  intros m ? Hyp ;simpl in *.
  eapply gmultiset_elem_of_dom in Hyp. 
  assert (ξ ∈ mb_without_not_nb m) as mem. eauto.
  eapply lts_mb_nb_with_nb_spec1 in mem as (nb & eq).
  eapply gmultiset_disj_union_difference' in eq.
  exists (m ∖ {[+ ξ +]}). rewrite eq at 1.
  eapply lts_multiset_minus; eauto.
Defined.
Next Obligation.
  intros ? ? ? m ? m' ? ? inter;simpl in *.
  right. destruct inter as (duo & nb).
  eapply non_blocking_action_in_ms in nb as eq'; eauto. 
  rewrite<- eq'.
  assert (mb_without_not_nb ({[+ μ2 +]} ⊎ m') 
  = {[+ μ2 +]} ⊎ (mb_without_not_nb m')) as eq.
  eapply lts_mb_nb_spec1; eauto. rewrite eq.
  eapply gmultiset_elem_of_dom.
  multiset_solver.
Defined.
Next Obligation.
  intros ξ p;simpl in *.
  destruct (decide (non_blocking ξ)) as [ nb (* Input_case *) | not_nb (* Ouput_case *)].
  + exact {[ co ξ ]}.
  + exact empty.
Defined.
Next Obligation.
  intros ? ? ? ? m mem l inter;simpl in *.
  unfold Interaction_between_VACCS_and_MB_obligation_4.
  destruct inter as (duo & nb). rewrite decide_True; eauto.
  assert (μ = co ξ). { eapply unique_nb. symmetry. exact duo. }
  subst; set_solver.
Defined.
Next Obligation.
  intros ? ? ? ? m mem l inter;simpl in *.
  inversion mem.
Qed.

#[global] Program Instance Interaction_between_FW_VACCS_and_VACCS :
  Prop_of_Inter (proc * mb (ExtAct TypeOfActions)) proc (ExtAct TypeOfActions) dual :=
    {| lts_essential_actions_left p := set_map ActOut (outputs_of p.1) ∪ (dom (mb_without_not_nb p.2)); 
       lts_essential_actions_right q := set_map ActOut (outputs_of q)|}.
Next Obligation.
  intros (p , m) ? ?. simpl in *.
  eapply elem_of_union in H. destruct (decide (ξ ∈ dom (mb_without_not_nb m))).
  + eapply gmultiset_elem_of_dom in e.
    eapply lts_mb_nb_with_nb_spec1 in e as (nb & mem).
    assert ({ m'| m = {[+ ξ +]} ⊎ m'}) as (m' & eq).
    { exists (m ∖ {[+ ξ +]}). multiset_solver. }
    subst. exists (p , m'). eapply ParRight. eapply lts_multiset_minus; eauto.
  + assert (ξ ∈ @set_map TypeOfActions (gset TypeOfActions) _ (ExtAct TypeOfActions) (gset (ExtAct TypeOfActions)) _ _ _  ActOut (outputs_of p)) as Hyp.
    { destruct H as [case1 | case2]. exact case1. contradiction. }
    unfold set_map in Hyp. simpl in *.
    eapply elem_of_list_to_set in Hyp.
    eapply list_elem_of_fmap in Hyp.
    destruct ξ.
    ++ exfalso. destruct Hyp as (a' & eq & mem). inversion eq.
    ++ assert (a ∈ elements (outputs_of p)) as mem.
       { destruct Hyp as (y & Hyp'); destruct Hyp' as (eq' & mem). 
         inversion eq'; subst. eauto. }
       apply elem_of_elements in mem. eapply outputs_of_spec2 in mem.
       destruct mem as (p' & l). exists (p' , m). eapply ParLeft. eauto.
Defined.
Next Obligation.
  intros e ? Hyp ;simpl in *.
  unfold set_map in Hyp. simpl in *.
  eapply elem_of_list_to_set in Hyp.
  eapply list_elem_of_fmap in Hyp.
  destruct ξ as [ (*Input*) a | (*Output*) a].
  + exfalso. destruct Hyp. destruct H. inversion H.
  + assert (a ∈ elements (outputs_of e)) as mem.
    { destruct Hyp as (y & Hyp'); destruct Hyp' as (eq' & mem). 
      inversion eq'; subst. eauto. }
    apply elem_of_elements in mem. eapply outputs_of_spec2 in mem. eauto.
Defined.
Next Obligation.
  intros (p1 , m1) ? (p'1, m'1) ? ? ? Tr ? inter;simpl in *.
 destruct μ2 as [ (*Input*) a | (*Output*) a].
  - symmetry in inter. eapply simplify_match_input in inter. subst. left.
    inversion Tr; subst.
    + eapply elem_of_union. left. eapply elem_of_list_to_set.
      eapply list_elem_of_fmap. exists a. split; eauto.
      eapply elem_of_elements. eapply outputs_of_spec1. eauto.
    + eapply elem_of_union. right. eapply gmultiset_elem_of_dom.
      destruct (decide (non_blocking (ActOut a))) as [nb | b].
      * eapply non_blocking_action_in_ms in l; eauto.
        rewrite<- l. 
        eapply lts_mb_nb_spec1 in nb. rewrite nb. multiset_solver.
      * eapply blocking_action_in_ms in l as (eq & duo & nb);eauto.
        eapply simplify_match_output in duo. subst.
        rewrite duo in Tr, nb. destruct nb. inversion H0.
  - symmetry in inter. eapply simplify_match_output in inter. subst. right.
    eapply elem_of_list_to_set.
    eapply list_elem_of_fmap. exists a. split; eauto.
    eapply elem_of_elements. eapply outputs_of_spec1. eauto.
Qed.
Next Obligation.
  intros ξ p ;simpl in *. destruct ξ as [ (*Input*) a | (*Output*) a].
  + exact empty. 
  + exact {[ ActIn a ]}.
Defined.
Next Obligation.
  intros p q ? μ ? mem ? inter;simpl in *.
  unfold Interaction_between_FW_VACCS_and_VACCS_obligation_4. destruct ξ as [ (*Input*) a | (*Output*) a].
  - eapply elem_of_list_to_set in mem.
    eapply list_elem_of_fmap in mem. destruct mem as (? & eq & ?).
    inversion eq.
  - symmetry in inter. eapply simplify_match_output in inter. subst. set_solver.
Defined.
Next Obligation.
  intros ξ e;simpl in *.
  destruct ξ as [ a (* Input_case *) | a (* Ouput_case *)].
  + exact {[ ActOut a ]}.
  + exact {[ ActIn a ]}.
Defined.
Next Obligation.
  intros p q ? μ (p1 , m1) mem ? inter;simpl in *.
  unfold Interaction_between_FW_VACCS_and_VACCS_obligation_6. symmetry in inter.
  destruct ξ as [ (*Input*) a | (*Output*) a].
  - symmetry in inter. eapply simplify_match_input in inter. subst.
    eapply elem_of_union in mem. destruct mem as [case1 | case2].
    + set_solver.
    + set_solver.
  - symmetry in inter. eapply simplify_match_output in inter. subst. set_solver.
Defined.


Inductive FinA :=
| Inputs (c : ChannelData)
.

Definition Φᴠᴀᴄᴄꜱ (μ : ExtAct TypeOfActions) : FinA :=
match μ with
| ActIn (c ⋉ v) => (Inputs c)
| ActOut (c ⋉ v) => (Inputs c)
end.

Definition PreAct := FinA.

Definition 𝝳ᴠᴀᴄᴄꜱ (pre_μ : FinA) : PreAct := pre_μ.

#[global] Program Instance EqPreAct : EqDecision PreAct.
Next Obligation.
  intros. destruct x , y.
  + destruct (decide( c = c0)).
    - left. f_equal. subst. eauto.
    - right. intro. inversion H. contradiction.
Qed.

Definition encode_PreAct (c : PreAct) : gen_tree ChannelData :=
match c with
  | Inputs c => GenLeaf c
end.

Definition decode_PreAct (tree : gen_tree ChannelData) : option PreAct :=
match tree with
  | GenLeaf c => Some (Inputs c)
  | _ => None
end.

Lemma encode_decide_PreAct c : decode_PreAct (encode_PreAct c) = Some c.
Proof. case c. 
* intros. simpl. reflexivity.
Qed.


#[global] Instance CountPreAct : Countable PreAct.
Proof.
  refine (inj_countable encode_PreAct decode_PreAct _).
  apply encode_decide_PreAct.
Qed.

Fixpoint  mPreCoAct_of (k : nat) p : gmultiset PreAct := 
match p with
  | P ‖ Q => (mPreCoAct_of k P) ⊎ (mPreCoAct_of k Q)
  | (cstC c) ! v • 𝟘 => {[+ Inputs (cstC c) +]}
  | (bvarC i) ! v • 𝟘 => if decide(k < (S i)) then {[+ Inputs (bvarC (i - k)) +]}
                                              else ∅
  | pr_var _ => ∅
  | rec _ • _ => ∅
  | If E Then P Else Q => match (Eval_Eq E) with 
                          | Some true => mPreCoAct_of k P
                          | Some false => mPreCoAct_of k Q
                          | None => ∅
                          end
  | ν p => mPreCoAct_of (S k) p
  | g p => ∅
end.

Definition PreCoAct_of p := dom (mPreCoAct_of 0 p).

Lemma mPreCoAct_of_res_n_g j n g1 : mPreCoAct_of j (Ѵ n (g g1)) = mPreCoAct_of (n + j) (g g1).
Proof.
  revert g1 j.
  induction n.
  + simpl; eauto.
  + intros; simpl in *. replace (S (n + j))%nat with (n + (S j))%nat by lia.
    eapply IHn.
Qed.

Lemma mPreCoAct_of_res_n j n p1 : mPreCoAct_of j (Ѵ n p1) = mPreCoAct_of (n + j) p1.
Proof.
  revert p1 j.
  induction n.
  + simpl; eauto.
  + intros; simpl in *. replace (S (n + j))%nat with (n + (S j))%nat by lia.
    eapply IHn.
Qed.

Lemma PreCoAct_NewVarC k j p : mPreCoAct_of (k + S j) (NewVarC j p) = mPreCoAct_of (k + j) p.
Proof.
  revert k j.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0));
  destruct p; intros k j; simpl in *; eauto.
  + assert (mPreCoAct_of (k + S j) (NewVarC j p1) = mPreCoAct_of (k + j) p1) as eq1.
    { eapply Hp. simpl. lia. }
    assert (mPreCoAct_of (k + S j) (NewVarC j p2) = mPreCoAct_of (k + j) p2) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto.
  + case_eq (Eval_Eq e).
    ++ intros. destruct b.
       +++ eauto with lia.
       +++ eauto with lia.
    ++ eauto with lia.
  + destruct c; simpl.
      ++ eauto.
      ++ destruct (decide (j < S n)).
         +++ destruct (decide (k + j < S n)).
             ++++ rewrite decide_True; try lia.
                  replace (S n - (k + S j))%nat with (n - (k + j))%nat by lia. eauto.
             ++++ rewrite decide_False; try lia. eauto.
         +++ rewrite decide_False; try lia.
             rewrite decide_False; try lia. eauto.
  + replace (S (k + S j))%nat with (k + S (S j))%nat by lia.
    replace (S (k + j))%nat with (k + S j)%nat by lia.
    eapply Hp. simpl; eauto.
Qed.

Lemma PreCoAct_VarSwap k j p : mPreCoAct_of (j + S (S k)) p = mPreCoAct_of (j + S (S k)) (VarSwap_in_proc j p).
Proof.
  revert k j.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0));
  destruct p; intros k j; simpl in *; eauto.
  + assert (mPreCoAct_of (j + S (S k)) p1 = mPreCoAct_of (j + S (S k)) (VarSwap_in_proc j p1)) as eq1.
    { eapply Hp; simpl; eauto. lia. }
    assert (mPreCoAct_of (j + S (S k)) p2 = mPreCoAct_of (j + S (S k)) (VarSwap_in_proc j p2)) as eq2.
    { eapply Hp; simpl; eauto. lia. } rewrite eq1, eq2. eauto.
  + case_eq (Eval_Eq e).
    ++ intros. destruct b.
       +++ eauto with lia.
       +++ eauto with lia.
    ++ eauto with lia.
  + destruct c.
      ++ simpl. eauto.
      ++ simpl. destruct (decide (j + S (S k) < S n)).
         ++++ destruct (decide (n = j)).
              +++++ subst. destruct (decide (j + S (S k) < S (S j))).
                    ++++++ lia.
                    ++++++ lia.
              +++++ destruct (decide (n = S j)).
                    ++++++ subst. lia.
                    ++++++ rewrite decide_True; try lia. eauto.
         ++++ destruct (decide (n = j)).
              +++++ subst. rewrite decide_False; try lia. eauto.
              +++++ destruct (decide (n = S j)).
                    ++++++ subst. rewrite decide_False; try lia. eauto.
                    ++++++ rewrite decide_False; try lia. eauto.
  + replace (S (j + S (S k)))%nat with ((S j) + S (S k))%nat by lia.
    eapply Hp. simpl; eauto.
Qed.

Lemma PreCoEquiv (k : nat) (p : proc) (q : proc) (c : PreAct) : p ≡* q -> c ∈ mPreCoAct_of k p -> c ∈ mPreCoAct_of k q.
Proof.
  intros eq mem. revert k c mem. dependent induction eq.
  + dependent induction H; intros; simpl in *; subst; eauto; try multiset_solver.
    * rewrite H in mem; eauto.
    * rewrite H; eauto.
    * rewrite H in mem; eauto.
    * rewrite H; eauto.
    * replace (S (S k))%nat with (0 + (S (S k)))%nat by lia. rewrite<- PreCoAct_VarSwap. simpl; eauto.
    * replace (S (S k))%nat with (0 + (S (S k)))%nat in mem by lia. rewrite<- PreCoAct_VarSwap in mem. simpl; eauto.
    * eapply gmultiset_elem_of_disj_union in mem. destruct mem.
      - eapply gmultiset_elem_of_disj_union. left. eauto.
      - eapply gmultiset_elem_of_disj_union. right.
        replace (S k)%nat with (k + S 0)%nat in H by lia. rewrite PreCoAct_NewVarC in H.
        replace (k + 0)%nat with k%nat in H by lia. eauto.
    * eapply gmultiset_elem_of_disj_union in mem. destruct mem.
      - eapply gmultiset_elem_of_disj_union. left. eauto.
      - eapply gmultiset_elem_of_disj_union. right.
        replace (S k)%nat with (k + S 0)%nat by lia. rewrite PreCoAct_NewVarC.
        replace (k + 0)%nat with k%nat by lia. eauto.
    * case_eq (Eval_Eq C).
      ++ intros. destruct b.
         +++ rewrite H0 in mem; eauto.
         +++ rewrite H0 in mem; eauto.
      ++ intros. rewrite H0 in mem; eauto.
    * case_eq (Eval_Eq C).
      ++ intros. destruct b.
         +++ rewrite H0 in mem; eauto.
         +++ rewrite H0 in mem; eauto.
      ++ intros. rewrite H0 in mem; eauto.
  + eauto.
Qed.

Definition VarC_preaction_add (k : nat) (pre_μ : PreAct) : PreAct :=
match pre_μ with
| Inputs c => Inputs (VarC_add k c)
end.

Lemma VarC_preaction_add_zero pre_μ : VarC_preaction_add 0 pre_μ = pre_μ.
Proof.
  destruct pre_μ; simpl. destruct c; simpl; eauto.
Qed.

(* Lemma VarC_preaction_add_rev j k pre_μ μ' : 
      VarC_preaction_add (j + k) pre_μ = Φᴠᴀᴄᴄꜱ  (VarC_action_add (j + k) μ') 
      -> VarC_preaction_add k pre_μ = Φᴠᴀᴄᴄꜱ  (VarC_action_add k μ').
Proof.
  revert k pre_μ μ'.
  induction j.
  + simpl; eauto.
  + intros; simpl. destruct pre_μ; destruct μ'.
    ++ destruct f; destruct a.
       +++ simpl in *. destruct c0.
           ++++ inversion H; subst. f_equal. destruct c. simpl; eauto.
           ++++ simpl in *. inversion H.
       +++ simpl in *. destruct c.
           ++++ simpl in *. inversion H.
           ++++ simpl in *. inversion H. f_equal. assert (n = n0)%nat by lia. subst; eauto.
    ++ destruct c; destruct a.
       +++ simpl in *. destruct c0.
           ++++ simpl; eauto.
           ++++ simpl in *. inversion H.
       +++ simpl in *. destruct c.
           ++++ simpl in *. inversion H.
           ++++ simpl in *. inversion H.
Qed. *)

Lemma simpl_dual_VarC_add μ'' μ' k : dual μ'' (VarC_action_add k μ') -> μ'' = VarC_action_add k (co μ').
Proof.
  revert μ'' μ'.
  intros; eauto. destruct μ'; destruct a; destruct c; symmetry in H;
    destruct μ''; simpl in * ; try inversion H; subst; eauto.
Qed.

Lemma simpl_dual_VarC j k μ': dual (VarC_action_add (j + k) (co μ')) (VarC_action_add (j + k) μ') 
              -> dual (VarC_action_add k (co μ')) (VarC_action_add k μ').
Proof.
  intros. destruct μ'; destruct a; destruct c; simpl; eauto.
Qed.

Lemma simpl_blocking_Varc j k μ' : ¬ non_blocking (VarC_action_add (j + k) μ')
  -> ¬ non_blocking (VarC_action_add k μ').
Proof.
  intros. destruct μ'; destruct a; destruct c; simpl; eauto.
  + intro imp; inversion imp; inversion H0.
  + intro. simpl in *. inversion H0. inversion H1. subst.
    assert (non_blocking_output (ActOut ((j + k + n)%nat ⋉ d))).
    exists ((j + k + n)%nat ⋉ d). eauto. contradiction.
Qed.

Lemma VarC_action_add_co_rev j k μ' p : VarC_action_add (j + k) μ' ∈ coR p
                        -> VarC_action_add k μ' ∈ coR (Ѵ  j p).
Proof.
  revert k μ' p.
  induction j.
  + simpl ;eauto.
  + intros; simpl in *. rewrite<- BigNew_reverse_def_one.
    eapply IHj. exists (VarC_action_add (j + k) (co μ')).
    destruct H as (μ'' & eq1 & eq2 & eq3).
    eapply lts_refuses_spec1 in eq1 as (p' & tr). 
    assert (dual μ'' (VarC_action_add (S (j + k)) μ')); eauto.
    eapply simpl_dual_VarC_add in eq2. subst.
    repeat split.
    ++ eapply lts_refuses_spec2. exists (ν p'). eapply lts_res_ext.
       rewrite VarC_action_add_add; simpl; eauto.
    ++ eapply (simpl_dual_VarC 1). simpl; eauto.
    ++ eapply (simpl_blocking_Varc 1). simpl ; eauto.
Qed.

Lemma VarC_action_add_co_rev_map j k μ' p : VarC_preaction_add (j + k) μ' ∈ ⌈ 𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ ⌉ (coR p)
                        -> VarC_preaction_add k μ' ∈ ⌈ 𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ ⌉ (coR (Ѵ  j p)).
Proof.
  revert k μ' p.
  induction j.
  + simpl ;eauto.
  + intros; simpl in *. rewrite<- BigNew_reverse_def_one.
    eapply IHj. destruct H as (μ'' & eq1 & eq2).
    destruct eq1 as (μ''' & eq'1 & duo & b).
    eapply lts_refuses_spec1 in eq'1 as (p' & tr).
    
    admit.
    
(*     exists (VarC_preaction_add (j + k) (co μ')).
    assert (S (j + k) = 1 + (j+k))%nat by lia.
    rewrite H in eq2.
    rewrite<- (VarC_preaction_add_rev 1 (j + k)) in eq2.
        assert (dual μ'' (VarC_action_add (S (j + k)) μ')); eauto.
    eapply simpl_dual_VarC_add in eq2. subst.
    repeat split.
    ++ eapply lts_refuses_spec2. exists (ν p'). eapply lts_res_ext.
       rewrite VarC_action_add_add; simpl; eauto.
    ++ eapply (simpl_dual_VarC 1). simpl; eauto.
    ++ eapply (simpl_blocking_Varc 1). simpl ; eauto. *)
Admitted.

Lemma specPreAct1 k : ∀ (pre_μ : PreAct) (p : proc),
   pre_μ ∈ (λ p0 : proc, mPreCoAct_of k p0) p -> (VarC_preaction_add k pre_μ) ∈ ⌈ (𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ) ⌉ (coR p).
(*     → (VarC_preaction_add k pre_μ)
      ∈ (λ (p0 : proc) (pre_μ0 : FinA),
           ∃ μ' : ExtAct TypeOfActions, pre_μ0 = Φᴠᴄᴄꜱ (VarC_action_add k μ') ∧ (VarC_action_add k μ') ∈ coR p0) p. *)
Proof.
  intros. simpl in *. revert k pre_μ H.
  induction p as (p & Hp) using
        (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros.
  * simpl in *. eapply gmultiset_elem_of_disj_union in H. destruct H.
    -- eapply (Hp p1) in H. destruct H as (μ' & eq & mem).
       destruct eq as (μ'' & Tr & duo & b). exists μ'. split; eauto. 
       exists μ''. repeat split; eauto. eapply lts_refuses_spec1 in Tr as (p'1 & Tr).
       eapply lts_refuses_spec2. exists (p'1 ‖ p2). constructor. eauto. simpl. lia.
    -- eapply (Hp p2) in H. destruct H as (μ' & eq & mem).
       exists μ'. split; eauto. destruct eq as (μ'' & Tr & duo & b).
       exists μ''. repeat split; eauto. eapply lts_refuses_spec1 in Tr as (p'2 & Tr).
       eapply lts_refuses_spec2. exists (p1 ‖ p'2). constructor. eauto. simpl. lia.
  * simpl in *. inversion H.
  * simpl in *. inversion H.
  * case_eq (Eval_Eq e); intros; simpl in *. rewrite H0 in H. destruct b.
    -- eapply (Hp p1) in H. destruct H as (μ' & eq & mem).
       exists μ'. split; eauto. destruct eq as (μ'' & Tr & duo & b).
       exists μ''. repeat split; eauto. eapply lts_refuses_spec1 in Tr as (p'1 & Tr).
       eapply lts_refuses_spec2. exists p'1. constructor; eauto. lia.
    -- eapply (Hp p2) in H. destruct H as (μ' & eq & mem).
       exists μ'. split; eauto. destruct eq as (μ'' & Tr & duo & b).
       exists μ''. repeat split; eauto. eapply lts_refuses_spec1 in Tr as (p'2 & Tr).
       eapply lts_refuses_spec2. exists p'2. eapply lts_ifZero; eauto. lia.
    -- eapply gmultiset_elem_of_dom in H. simpl in *. rewrite H0 in H. inversion H.
  * simpl in *. destruct c.
    ** assert (pre_μ = Inputs c) by multiset_solver.
       rewrite H0. simpl. assert ((𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ) (ActIn (c ⋉ d)) = Inputs c). simpl; eauto.
       rewrite<- H1. eapply map_gamma_of_action. exists (ActOut (c ⋉ d)). repeat split.
       eapply lts_refuses_spec2. exists (g 𝟘). constructor. intro. inversion H2. inversion H3.
    ** destruct (decide ((k < S n))).
       - assert (pre_μ = Inputs (n - k)) by multiset_solver.
         rewrite H0. simpl. assert ((k + (n - k) = n)%nat) by lia. subst. rewrite H1.
         assert ((𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ) (ActIn (bvarC n ⋉ d)) = Inputs (bvarC n)). simpl; eauto.
         rewrite<- H0. eapply map_gamma_of_action. exists (ActOut (bvarC n ⋉ d)). repeat split.
         eapply lts_refuses_spec2. exists (g 𝟘). constructor. intro. inversion H2. inversion H3.
       - inversion H.
  * simpl in *. assert (S k = 1 + k)%nat as eq'' by lia.
    rewrite eq'' in H.
    eapply (VarC_action_add_co_rev_map 1 k).
    eapply Hp; try lia. eauto.
  * simpl in *. inversion H.
Qed.


#[global] Program Instance AbsVACCS : AbsAction (ExtAct TypeOfActions) VACCS_ExtAction Φᴠᴀᴄᴄꜱ 𝝳ᴠᴀᴄᴄꜱ.
Next Obligation.
  intros. destruct β; destruct β'; destruct a; destruct a0.
  - inversion H1; subst.
    eapply lts_refuses_spec1 in H2 as (e' & Tr).
    eapply TransitionShapeForInput in Tr as (P1 & G & R & n & eq & eq' & Hyp).
    assert (¬ (Ѵ n ((gpr_input (VarC_add n c0) P1 + G) ‖ R) ↛{ (c0 ⋉ d0) ? })) as accepts.
    { eapply lts_refuses_spec2. exists (Ѵ n (P1 ^ d0 ‖ R)). eapply lts_res_ext_n. eapply lts_parL. eapply lts_choiceL. constructor. }
    eapply (@accepts_preserved_by_eq proc (ExtAct TypeOfActions) VACCS_ExtAction VACCS_gLtsEq) in accepts.
    exact accepts. symmetry. eauto.
  - exfalso. eapply H0. exists (c0 ⋉ d0). eauto.
  - exfalso. eapply H. exists (c ⋉ d). eauto.
  - exfalso. eapply H. exists (c ⋉ d). eauto.
Qed.
Next Obligation.
  - intros. destruct H2 as (μ'' & eq & mem). destruct β.
    + destruct a. simpl in *. destruct μ''.
      * simpl in *. destruct a. inversion mem. subst. destruct β'.
        -- destruct a. simpl in *. inversion H1; subst.
           destruct eq as (μ'' & tr & duo & b).
           symmetry in duo. eapply simplify_match_input in duo. subst.
           exists (ActIn(c ⋉ d0)). split ;eauto. exists (ActOut (c ⋉ d0)).
           repeat split ;eauto.
        -- exfalso. eapply H0. exists a. eauto.
      * destruct eq as (a' & Tr' & duo' & b).
        exfalso. eapply b. exists a; eauto.
    + destruct a. simpl in *. exfalso. eapply H. exists (c ⋉ d);eauto.
Qed.

#[global] Program Instance FinitaryAbsVACCS  : FinitaryAbsAction proc proc (ExtAct TypeOfActions) VACCS_ExtAction Φᴠᴀᴄᴄꜱ 𝝳ᴠᴀᴄᴄꜱ :=
  {| coR_abs p := PreCoAct_of p ; |}.
Next Obligation.
  intros; subst. eapply gmultiset_elem_of_dom in H.
  eapply (specPreAct1 0) in H. rewrite VarC_preaction_add_zero in H. eauto.
Qed.
Next Obligation.
  intros. simpl in *. destruct H as (μ & eq & mem).
  destruct μ.
  + destruct eq as (μ' & Tr & duo & b). symmetry in duo.
    destruct a. eapply simplify_match_input in duo. subst.
    eapply lts_refuses_spec1 in Tr as (p' & Tr).
    eapply TransitionShapeForOutput in Tr as (R & n & eq & eq').
    assert ((𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ) (ActIn (c ⋉ d)) ∈ PreCoAct_of (Ѵ n ((VarC_add n c ! d • 𝟘) ‖ R))).
    { eapply gmultiset_elem_of_dom. simpl. rewrite mPreCoAct_of_res_n.
      simpl. destruct c; simpl.
      + multiset_solver.
      + rewrite decide_True; try lia. replace (n + n0 - (n + 0))%nat with n0%nat by lia.
        multiset_solver. }
    eapply gmultiset_elem_of_dom. eapply PreCoEquiv. symmetry. eauto.
    eapply gmultiset_elem_of_dom. eauto.
  + destruct eq as (μ' & Tr & duo & b).
    destruct b. exists a; eauto.
Qed.

End VACCS_lts.


