From stdpp Require Import gmap gmultiset.
From Stdlib.Program Require Import Equality.
From Stdlib.Wellfounded Require Import Inverse_Image.
From TestingTheory Require Import InputOutputActions OldTransitionSystems ActTau .
From TestingTheory Require Export VACCS.

(** ** VACCS satisfies the axioms for soundness and completeness *)

#[global] Program Instance VACCS_Label : Label TypeOfActions := 
  {| label_eqdec := TypeOfActions_dec ;
  label_countable := TypeOfActions_countable |}.

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
     lts_oba_mo p := moutputs_of 0 p 
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

From TestingTheory Require Import gLts Bisimulation Lts_OBA Lts_FW Lts_OBA_FB GeneralizeLtsOutputs ForwarderConstruction.

#[global] Program Instance VACCS_ggLts : @gLts proc (ExtAct TypeOfActions) gLabel_nb := ggLts gLabel_nb.

#[global] Program Instance VACCS_ggLtsEq : @gLtsEq proc (ExtAct TypeOfActions) gLabel_nb := 
  ggLtsEq gLabel_nb.

#[global] Program Instance VACCS_gLtsOBA : 
  @gLtsOba proc (ExtAct TypeOfActions) gLabel_nb VACCS_ggLtsEq := ggLtsOba_nb.

#[global] Program Instance VACCS_gLtsOBAFB :
  @gLtsObaFB proc (ExtAct TypeOfActions) gLabel_nb VACCS_ggLtsEq VACCS_gLtsOBA := ggLtsObaFB_nb.

From TestingTheory Require Import InteractionBetweenLts ParallelLTSConstruction.

#[global] Program Instance Interaction_between_parallel_VACCS :
  @Prop_of_Inter proc proc (ExtAct TypeOfActions) dual gLabel_nb
  VACCS_ggLts VACCS_ggLts :=  Inter_parallel_IO gLabel_nb.
Next Obligation.
  intros μ1 μ2 inter. unfold dual in inter.
  unfold dual in inter. simpl in *. eauto.
Defined.

From TestingTheory Require Import Must.

Inductive FinA :=
| Inputs (c : ChannelData)
.

Definition Φ (μ : ExtAct TypeOfActions) : FinA :=
match μ with
| ActIn (c ⋉ v) => Inputs c
| ActOut (c ⋉ v) => Inputs c
end.


From TestingTheory Require Import DefinitionAS.

#[global] Program Instance gAbsAction {A : Type} 
  : @AbsAction (ExtAct TypeOfActions) gLabel_nb proc FinA VACCS_ggLts Φ.
Next Obligation.
  intros. destruct μ; destruct μ'; destruct a; destruct a0.
  - inversion H1; subst. eapply lts_refuses_spec1 in H2 as (e' & Tr). simpl in *.
    eapply TransitionShapeForInput in Tr as (P1 & G & R & n & eq & eq' & Hyp).
    assert (¬ (Ѵ n ((gpr_input (VarC_add n c0) P1 + G) ‖ R) ↛{ (c0 ⋉ d0) ? })) as accepts.
    { eapply lts_refuses_spec2. exists (Ѵ n (P1 ^ d0 ‖ R)). eapply lts_res_ext_n. eapply lts_parL. eapply lts_choiceL. constructor. }
    eapply accepts_preserved_by_eq in accepts. exact accepts. symmetry. eauto.
  - exfalso. eapply H0. exists (c0 ⋉ d0). eauto.
  - exfalso. eapply H. exists (c ⋉ d). eauto.
  - exfalso. eapply H. exists (c ⋉ d). eauto.
Qed.

Definition PreAct := FinA.

Definition 𝝳 (pre_μ : FinA) : PreAct := pre_μ.

#[global] Program Instance EqPreAct : EqDecision PreAct.
Next Obligation.
  intros. destruct x , y.
  + destruct (decide( c = c0)).
    - left. f_equal. eauto.
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

From TestingTheory Require Import Subset_Act.

Definition VarC_preaction_add (k : nat) (pre_μ : FinA) : FinA :=
match pre_μ with
| Inputs c => Inputs (VarC_add k c)
end.

Lemma VarC_preaction_add_zero pre_μ : VarC_preaction_add 0 pre_μ = pre_μ.
Proof.
  destruct pre_μ; simpl; destruct c; eauto.
Qed.

Lemma VarC_preaction_add_rev j k pre_μ μ' : 
      VarC_preaction_add (j + k) pre_μ = Φ (VarC_action_add (j + k) μ') 
      -> VarC_preaction_add k pre_μ = Φ (VarC_action_add k μ').
Proof.
  revert k pre_μ μ'.
  induction j.
  + simpl; eauto.
  + intros; simpl. destruct pre_μ; destruct μ'.
    ++ destruct c; destruct a.
       +++ simpl in *. destruct c0.
           ++++ simpl; eauto.
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
           ++++ simpl in *. inversion H. f_equal. assert (n = n0)%nat by lia. subst; eauto.
Qed.

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

Lemma simpl_blocking_Varc j k μ' : ¬ (@non_blocking _ (@gLabel_nb TypeOfActions VACCS_Label) (VarC_action_add (j + k) μ'))
  -> ¬ (@non_blocking _ (@gLabel_nb TypeOfActions VACCS_Label)(VarC_action_add k μ')).
Proof.
  intros. destruct μ'; destruct a; destruct c; simpl; eauto.
  + intro imp; inversion imp; inversion H0.
  + intro. simpl in *. inversion H0. inversion H1. subst.
    assert (non_blocking_output (ActOut ((j + k + n)%nat ⋉ d))).
    exists ((j + k + n)%nat ⋉ d). eauto. contradiction.
Qed.

Lemma VarC_action_add_co_rev j k μ' p : VarC_action_add (j + k) μ' ∈ @co_actions_of _ _ (@gLabel_nb TypeOfActions VACCS_Label) _ p
                        -> VarC_action_add k μ' ∈ @co_actions_of _ _ (@gLabel_nb TypeOfActions VACCS_Label) _ (Ѵ  j p).
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

Lemma specPreAct1 k : ∀ (pre_μ : FinA) (p : proc),
  𝝳 (pre_μ) ∈ (λ p0 : proc, mPreCoAct_of k p0) p
    → (VarC_preaction_add k pre_μ)
      ∈ (λ (p0 : proc) (pre_μ0 : FinA),
           ∃ μ' : ExtAct TypeOfActions, pre_μ0 = Φ (VarC_action_add k μ') 
     ∧ (VarC_action_add k μ') ∈ @co_actions_of proc (ExtAct TypeOfActions)
      (@gLabel_nb TypeOfActions VACCS_Label)
      (@ggLts TypeOfActions (@gLabel_nb TypeOfActions VACCS_Label) proc
         VACCS_Label VACCS_Lts) p0) p.
Proof.
  intros. simpl in *. revert k pre_μ H.
  induction p as (p & Hp) using
        (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *.
  * eapply gmultiset_elem_of_disj_union in H. destruct H.
    -- eapply (Hp p1) in H. destruct H as (μ' & eq & mem).
       destruct mem as (μ'' & Tr & duo & b). exists μ'. split; eauto. 
       exists μ''. repeat split; eauto. eapply lts_refuses_spec1 in Tr as (p'1 & Tr).
       eapply lts_refuses_spec2. exists (p'1 ‖ p2). constructor. eauto. simpl. lia.
    -- eapply (Hp p2) in H. destruct H as (μ' & eq & mem).
       exists μ'. split; eauto. destruct mem as (μ'' & Tr & duo & b).
       exists μ''. repeat split; eauto. eapply lts_refuses_spec1 in Tr as (p'2 & Tr).
       eapply lts_refuses_spec2. exists (p1 ‖ p'2). constructor. eauto. simpl. lia.
  * simpl in *. inversion H.
  * simpl in *. inversion H.
  * case_eq (Eval_Eq e); intros; simpl in *. rewrite H0 in H. destruct b.
    -- eapply (Hp p1) in H. destruct H as (μ' & eq & mem).
       exists μ'. split; eauto. destruct mem as (μ'' & Tr & duo & b).
       exists μ''. repeat split; eauto. eapply lts_refuses_spec1 in Tr as (p'1 & Tr).
       eapply lts_refuses_spec2. exists p'1. constructor; eauto. lia.
    -- eapply (Hp p2) in H. destruct H as (μ' & eq & mem).
       exists μ'. split; eauto. destruct mem as (μ'' & Tr & duo & b).
       exists μ''. repeat split; eauto. eapply lts_refuses_spec1 in Tr as (p'2 & Tr).
       eapply lts_refuses_spec2. exists p'2. eapply lts_ifZero; eauto. lia.
    -- eapply gmultiset_elem_of_dom in H. simpl in *. rewrite H0 in H. inversion H.
  * simpl in *.
       destruct pre_μ.
       + simpl in *. subst. destruct c.
         ++ assert (Inputs c0 = Inputs c) by multiset_solver. inversion H0. subst.
            exists (ActIn (c ⋉ d)). split.
            -- simpl in *. reflexivity.
            -- exists (ActOut (c ⋉ d)). repeat split ;eauto.
               eapply lts_refuses_spec2. exists 𝟘. constructor.
               intro imp. unfold non_blocking in imp. simpl in *.
               inversion imp. inversion H1.
         ++ destruct (decide (k < S n)).
            +++ assert (Inputs c0 = Inputs (bvarC (n - k))) by multiset_solver. inversion H0. subst.
                exists (ActIn (bvarC (n - k) ⋉ d)). split.
                -- simpl in *. reflexivity.
                -- exists (ActOut (bvarC n ⋉ d)). repeat split ;eauto.
                   eapply lts_refuses_spec2. exists 𝟘. constructor. simpl. eauto with lia.
                   replace  (k + (n - k))%nat with n%nat by lia. eauto.
                   intro imp. unfold non_blocking in imp. simpl in *.
                   inversion imp. inversion H1.
            +++ inversion H.
  * unfold PreCoAct_of in H.
    eapply Hp in H as ( μ' & eq1 & eq2); simpl ; eauto. exists μ'.
    split. eapply VarC_preaction_add_rev. instantiate (1:= 1). simpl; eauto.
    eapply (VarC_action_add_co_rev 1). simpl ;eauto.
  * inversion H.
Qed.

#[global] Program Instance gPreExtAction : 
  @PreExtAction proc (ExtAct TypeOfActions) gLabel_nb FinA PreAct EqPreAct CountPreAct 𝝳 Φ (ggLts gLabel_nb) :=
  {| pre_co_actions_of_fin p := fun pre_μ => (exists μ', pre_μ = Φ μ' /\ 
      μ' ∈ @co_actions_of proc (ExtAct TypeOfActions) (@gLabel_nb TypeOfActions VACCS_Label)
      (@ggLts TypeOfActions (@gLabel_nb TypeOfActions VACCS_Label) proc VACCS_Label VACCS_Lts) p) ;
     pre_co_actions_of p := PreCoAct_of p ; |}.
Next Obligation.
  intros; simpl in *.
  exists μ.  split ;eauto.
Qed.
Next Obligation.
  intros; simpl in *.
  destruct H as (μ' & eq & mem). subst. destruct μ'.
  + destruct a. simpl. exists (ActIn (c ⋉ d)). split; eauto.
  + destruct a. simpl. exists (ActOut (c ⋉ d)). split; eauto.
Qed.
Next Obligation.
  intros. split.
  - intros. destruct H as (μ & eq & mem).
    destruct μ.
    + destruct mem as (μ' & Tr & duo & b). symmetry in duo.
      destruct a. eapply simplify_match_input in duo. subst.
      eapply lts_refuses_spec1 in Tr as (p' & Tr).
      eapply TransitionShapeForOutput in Tr as (R & n & eq & eq').
      assert (𝝳 (Φ (ActIn (c ⋉ d))) ∈ PreCoAct_of (Ѵ n ((VarC_add n c ! d • 𝟘) ‖ R))).
      { eapply gmultiset_elem_of_dom. simpl. rewrite mPreCoAct_of_res_n.
        simpl. destruct c; simpl.
        + multiset_solver.
        + rewrite decide_True; try lia. replace (n + n0 - (n + 0))%nat with n0%nat by lia.
          multiset_solver. }
      eapply gmultiset_elem_of_dom. eapply PreCoEquiv. symmetry. eauto.
      eapply gmultiset_elem_of_dom. eauto.
    + destruct mem as (μ' & Tr & duo & b).
      destruct b. exists a; eauto.
  - intros; subst. eapply gmultiset_elem_of_dom in H.
    eapply (specPreAct1 0) in H. rewrite VarC_preaction_add_zero in H.
    destruct H. rewrite VarC_add_zero_ext in H. exists x. destruct H. split ;eauto.
Qed.



