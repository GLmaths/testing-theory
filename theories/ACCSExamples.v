From Must Require Import ACCSInstance TransitionSystems Coin.
From stdpp Require Import strings sets gmap base.
From Coq Require Import Relations.

(* Proof of hoisting *)

Lemma q_terminate : forall M, (!"a" & (gpr_tau (!"b") ⊕ gpr_tau (!"c")) ▷ M) ⤓.
Proof.
  intro M. constructor.
  intros (p1, M1) l. inversion l; subst.
  inversion H2; subst.
  inversion H1; subst.
  inversion H3; subst; inversion H6. inversion H4.
  inversion H4; subst. inversion H5; subst.
  constructor. intros (p2, M2) l2. inversion l2; subst.
  inversion H3; subst. inversion H1; subst. inversion H6. inversion H7. inversion H7.
  inversion H3; subst; inversion H7.
  inversion H5; subst.
  constructor. intros (p2, M2) l2. inversion l2; subst.
  inversion H3; subst. inversion H1; subst. inversion H6. inversion H7. inversion H7.
  inversion H3; subst; inversion H7.
  inversion H2; subst. inversion H4. inversion H4; subst; inversion H5.
Qed.

Lemma ineq01 : forall (M : mb name) X,
    {[ gpr_tau (!"a" & !"b") ⊕ gpr_tau (!"a" & !"c") ▷ M ]} ∪ X
      ⩽ !"a" & !"b" ▷ M.
Proof.
  cofix hco.
  intros.
  split.
  - intros (q', M') l.
    inversion l; subst. inversion H2; subst.
    inversion H1; subst. inversion H3; subst. inversion H4. inversion H4.
    inversion H2; subst; inversion H4.
  - intros.
    exists (gpr_tau (!"a" & !"b") ⊕ gpr_tau (!"a" & !"c") ▷ M), (! "a" & ! "b" ▷ M).
    split.
    + eapply elem_of_union. left. now eapply elem_of_singleton_2.
    + split. eapply wt_tau.
      eapply lts_fw_p, lts_choiceL, lts_tau.
      eapply wt_nil.
      split. eassumption. set_solver.
  - intros.
    inversion H0; subst.
    + inversion H6; subst.
      ++ inversion H7; subst.
         assert (pr_nil & ! "b" ▷ M ∈ ps').
         eapply H1.
         eapply elem_of_union. left.
         eapply elem_of_singleton. reflexivity.
         eapply wt_tau. eapply lts_fw_p, lts_choiceL, lts_tau.
         eapply wt_act. eapply lts_fw_p, lts_parL, lts_output.
         eapply wt_nil.
         eapply union_difference_singleton_L in H2.
         rewrite H2. eapply h_cup. eapply coin_refl.
      ++ inversion H7; subst.
         assert (! "a" & pr_nil ▷ M ∈ ps').
         eapply H1.
         eapply elem_of_union. left.
         eapply elem_of_singleton. reflexivity.
         eapply wt_tau. eapply lts_fw_p, lts_choiceL, lts_tau.
         eapply wt_act. eapply lts_fw_p, lts_parR, lts_output.
         eapply wt_nil.
         eapply union_difference_singleton_L in H2.
         rewrite H2. eapply h_cup. eapply coin_refl.
    + assert (gpr_tau (! "a" & ! "b") ⊕ gpr_tau (! "a" & ! "c") ▷ m ∈ ps').
      eapply H1.
      eapply elem_of_union. left.
      eapply elem_of_singleton. reflexivity.
      eapply wt_act. eapply (lts_fw_out_mb m). eapply wt_nil.
      eapply union_difference_singleton_L in H2.
      rewrite H2. eapply hco.
    + assert (gpr_tau (! "a" & ! "b") ⊕ gpr_tau (! "a" & ! "c") ▷ {[+ a +]} ⊎ M ∈ ps').
      eapply H1.
      eapply elem_of_union. left.
      eapply elem_of_singleton. reflexivity.
      eapply wt_act. eapply (lts_fw_inp_mb M). eapply wt_nil.
      eapply union_difference_singleton_L in H2.
      rewrite H2. eapply hco.
  - intros. constructor.
    intros (q', M') l.
    inversion l; subst. inversion H3; subst.
    inversion H2; subst. inversion H4. inversion H5. inversion H5.
    inversion H3; subst. inversion H5. inversion H5.
Qed.

Example ineq02 : forall (M : mb name) X,
    {[ gpr_tau (! "a" & ! "b") ⊕ gpr_tau (! "a" & ! "c") ▷ M ]} ∪ X
      ⩽ ! "a" & ! "c" ▷ M.
Proof.
  cofix hco.
  intros.
  split.
  - intros (q', M') l.
    inversion l; subst. inversion H2; subst.
    inversion H1; subst. inversion H3; subst. inversion H4. inversion H4.
    inversion H2; subst; inversion H4.
  - intros.
    exists (gpr_tau (!"a" & !"b") ⊕ gpr_tau (!"a" & !"c") ▷ M), (! "a" & ! "c" ▷ M).
    split.
    + eapply elem_of_union. left. now eapply elem_of_singleton_2.
    + split. eapply wt_tau.
      eapply lts_fw_p, lts_choiceR, lts_tau.
      eapply wt_nil.
      split. eassumption. set_solver.
  - intros.
    inversion H0; subst.
    + inversion H6; subst.
      ++ inversion H7; subst.
         assert (pr_nil & ! "c" ▷ M ∈ ps').
         eapply H1.
         eapply elem_of_union. left.
         eapply elem_of_singleton. reflexivity.
         eapply wt_tau. eapply lts_fw_p, lts_choiceR, lts_tau.
         eapply wt_act. eapply lts_fw_p, lts_parL, lts_output.
         eapply wt_nil.
         eapply union_difference_singleton_L in H2.
         rewrite H2. eapply h_cup. eapply coin_refl.
      ++ inversion H7; subst.
         assert (! "a" & pr_nil ▷ M ∈ ps').
         eapply H1.
         eapply elem_of_union. left.
         eapply elem_of_singleton. reflexivity.
         eapply wt_tau. eapply lts_fw_p, lts_choiceR, lts_tau.
         eapply wt_act. eapply lts_fw_p, lts_parR, lts_output.
         eapply wt_nil.
         eapply union_difference_singleton_L in H2.
         rewrite H2. eapply h_cup. eapply coin_refl.
    + assert (gpr_tau (! "a" & ! "b") ⊕ gpr_tau (! "a" & ! "c") ▷ m ∈ ps').
      eapply H1.
      eapply elem_of_union. left.
      eapply elem_of_singleton. reflexivity.
      eapply wt_act. eapply (lts_fw_out_mb m). eapply wt_nil.
      eapply union_difference_singleton_L in H2.
      rewrite H2. eapply hco.
    + assert (gpr_tau (! "a" & ! "b") ⊕ gpr_tau (! "a" & ! "c") ▷ {[+ a +]} ⊎ M ∈ ps').
      eapply H1.
      eapply elem_of_union. left.
      eapply elem_of_singleton. reflexivity.
      eapply wt_act. eapply (lts_fw_inp_mb M). eapply wt_nil.
      eapply union_difference_singleton_L in H2.
      rewrite H2. eapply hco.
  - intros. constructor.
    intros (q', M') l.
    inversion l; subst. inversion H3; subst.
    inversion H2; subst. inversion H4. inversion H5. inversion H5.
    inversion H3; subst. inversion H5. inversion H5.
Qed.

Example ineq03 : forall (M : mb name) X,
    {[ (! "b" ▷ M); (! "c" ▷ M) ]} ∪ X
      ⩽ gpr_tau (! "b") ⊕ gpr_tau (! "c") ▷ M.
Proof.
  cofix hco.
  intros.
  split.
  - intros (q', M') l.
    inversion l; subst. inversion H2; subst.
    + inversion H4; subst.
      eapply h_cup. eapply h_cup. eapply coin_refl.
    + inversion H4; subst.
      eapply h_cup.
      replace ({[! "b" ▷ M'; ! "c" ▷ M']})
        with ({[! "c" ▷ M'; ! "b" ▷ M']} : gset (proc * mb name)).
      eapply h_cup. eapply coin_refl.
      eapply leibniz_equiv.
      intros q.
      split; intros h%elem_of_union; destruct h as [hl | hr]; eapply elem_of_union; eauto.
    + inversion H2; subst; inversion H4.
  - intros.
    exfalso. eapply (lts_stable_spec2 (gpr_tau (! "b") ⊕ gpr_tau (! "c") ▷ M)).
    eexists. eapply lts_fw_p, lts_choiceL, lts_tau. assumption.
  - intros. inversion H0; subst.
    + inversion H6; subst; inversion H7.
    + assert ({[! "b" ▷ m; ! "c" ▷ m ]} ⊆ ps').
      intros p mem%elem_of_union.
      destruct mem as [hl%elem_of_singleton | hr%elem_of_singleton]; subst.
      eapply H1.
      eapply elem_of_union. left.
      eapply elem_of_union. left.
      eapply elem_of_singleton. reflexivity.
      eapply wt_act. eapply (lts_fw_out_mb m). eapply wt_nil.
      eapply H1.
      eapply elem_of_union. left.
      eapply elem_of_union. right.
      eapply elem_of_singleton. reflexivity.
      eapply wt_act. eapply (lts_fw_out_mb m). eapply wt_nil.
      eapply union_difference_L in H2.
      rewrite H2. eapply hco.
    + assert ({[! "b" ▷ {[+ a +]} ⊎ M; ! "c" ▷ {[+ a +]} ⊎ M]} ⊆ ps').
      intros p mem%elem_of_union.
      destruct mem as [hl%elem_of_singleton | hr%elem_of_singleton]; subst.
      eapply H1.
      eapply elem_of_union. left.
      eapply elem_of_union. left.
      eapply elem_of_singleton. reflexivity.
      eapply wt_act. eapply (lts_fw_inp_mb M). eapply wt_nil.
      eapply H1.
      eapply elem_of_union. left.
      eapply elem_of_union. right.
      eapply elem_of_singleton. reflexivity.
      eapply wt_act. eapply (lts_fw_inp_mb M). eapply wt_nil.
      eapply union_difference_L in H2.
      rewrite H2. eapply hco.
  - intros. constructor.
    intros (q', M') l.
    inversion l; subst. inversion H3; subst.
    inversion H5; subst. constructor. intros.
    inversion H0; subst. inversion H7. inversion H2.
    inversion H5; subst. constructor. intros.
    inversion H0; subst. inversion H7. inversion H2.
    inversion H3; subst; inversion H5.
Qed.

Example ineq03' : forall (M : mb name) X,
    {[ (pr_nil & ! "b" ▷ M); (pr_nil & ! "c" ▷ M) ]} ∪ X
      ⩽ gpr_tau (pr_nil & ! "b") ⊕ gpr_tau (pr_nil & ! "c") ▷ M.
Proof.
  cofix hco.
  intros.
  split.
  - intros (q', M') l.
    inversion l; subst. inversion H2; subst.
    + inversion H4; subst.
      eapply h_cup. eapply h_cup. eapply coin_refl.
    + inversion H4; subst.
      eapply h_cup.
      replace ({[pr_nil & ! "b" ▷ M'; pr_nil & ! "c" ▷ M']})
        with ({[pr_nil & ! "c" ▷ M'; pr_nil &  ! "b" ▷ M']} : gset (proc * mb name)).
      eapply h_cup. eapply coin_refl.
      eapply leibniz_equiv.
      intros q.
      split; intros h%elem_of_union; destruct h as [hl | hr]; eapply elem_of_union; eauto.
    + inversion H2; subst; inversion H4.
  - intros.
    exfalso. eapply (lts_stable_spec2 (gpr_tau (pr_nil & ! "b") ⊕ gpr_tau (pr_nil & ! "c") ▷ M)).
    eexists. eapply lts_fw_p, lts_choiceL, lts_tau. assumption.
  - intros. inversion H0; subst.
    + inversion H6; subst; inversion H7.
    + assert ({[pr_nil & ! "b" ▷ m; pr_nil & ! "c" ▷ m ]} ⊆ ps').
      intros p mem%elem_of_union.
      destruct mem as [hl%elem_of_singleton | hr%elem_of_singleton]; subst.
      eapply H1.
      eapply elem_of_union. left.
      eapply elem_of_union. left.
      eapply elem_of_singleton. reflexivity.
      eapply wt_act. eapply (lts_fw_out_mb m). eapply wt_nil.
      eapply H1.
      eapply elem_of_union. left.
      eapply elem_of_union. right.
      eapply elem_of_singleton. reflexivity.
      eapply wt_act. eapply (lts_fw_out_mb m). eapply wt_nil.
      eapply union_difference_L in H2.
      rewrite H2. eapply hco.
    + assert ({[pr_nil & ! "b" ▷ {[+ a +]} ⊎ M; pr_nil & ! "c" ▷ {[+ a +]} ⊎ M]} ⊆ ps').
      intros p mem%elem_of_union.
      destruct mem as [hl%elem_of_singleton | hr%elem_of_singleton]; subst.
      eapply H1.
      eapply elem_of_union. left.
      eapply elem_of_union. left.
      eapply elem_of_singleton. reflexivity.
      eapply wt_act. eapply (lts_fw_inp_mb M). eapply wt_nil.
      eapply H1.
      eapply elem_of_union. left.
      eapply elem_of_union. right.
      eapply elem_of_singleton. reflexivity.
      eapply wt_act. eapply (lts_fw_inp_mb M). eapply wt_nil.
      eapply union_difference_L in H2.
      rewrite H2. eapply hco.
  - intros. constructor.
    intros (q', M') l.
    inversion l; subst. inversion H3; subst.
    inversion H5; subst. constructor. intros.
    inversion H0; subst. inversion H7; subst. inversion H4. inversion H8. inversion H8.
    inversion H2; subst; inversion H8.
    inversion H5; subst. constructor. intros.
    inversion H0; subst. inversion H7; subst. inversion H4. inversion H8. inversion H8.
    inversion H2; subst; inversion H8.
    inversion H3; subst; inversion H5.
Qed.

Example ineq4 : forall (M : mb name) X,
    {[ gpr_tau (!"a" & !"b") ⊕ gpr_tau (!"a" & !"c") ▷ M ]} ∪ X
      ⩽ !"a" & (gpr_tau (!"b") ⊕ gpr_tau (!"c")) ▷ M.
Proof.
  cofix hco.
  intros.
  split.
  - intros q l.
    inversion l; subst. inversion H3; subst. inversion H1; subst. simpl in H2.
    inversion H2; subst.
    inversion H6; subst. inversion H6; subst.
    inversion H4; subst.
    + inversion H4; subst.
      ++ inversion H5; subst. eapply ineq01.
      ++ inversion H5; subst. eapply ineq02.
    + inversion H0; subst. inversion H4.
      inversion H4; subst; inversion H5.
  - intros. exfalso.
    eapply (lts_stable_spec2 (! "a" & (gpr_tau (! "b") ⊕ gpr_tau (! "c")) ▷ M)); eauto.
    exists (! "a" & !"b" ▷ M). eapply lts_fw_p, lts_parR, lts_choiceL, lts_tau.
  - intros. inversion H0; subst.
    + inversion H6; subst. inversion H7; subst.
      ++ eapply h2.
      
         etrans. eapply t_step. eapply cgr_par_nil_rev.
         etrans. eapply t_step. eapply cgr_par_com.
         reflexivity.
         eapply (h2 (gpr_tau (pr_nil & ! "b") ⊕ gpr_tau (pr_nil & ! "c"))).
         symmetry.
         etrans. eapply t_step. eapply cgr_choice.
         eapply cgr_tau. eapply cgr_par_nil_rev.
         eapply cgr_tau. eapply cgr_par_nil_rev.
         etrans. eapply t_step. eapply cgr_choice.
         eapply cgr_tau. eapply cgr_par_com.
         eapply cgr_tau. eapply cgr_par_com. reflexivity.
         assert ({[ (pr_nil & ! "b" ▷ M); (pr_nil & ! "c" ▷ M) ]} ⊆ ps').
         intros x mem%elem_of_union.
         destruct mem as [hl%elem_of_singleton | hr%elem_of_singleton]; subst.
         eapply H1. eapply elem_of_union. left. now eapply elem_of_singleton.
         eapply wt_tau. eapply lts_fw_p. eapply lts_choiceL, lts_tau.
         eapply wt_act. eapply lts_fw_p. eapply lts_parL, lts_output. eapply wt_nil.
         eapply H1. eapply elem_of_union. left. now eapply elem_of_singleton.
         eapply wt_tau. eapply lts_fw_p. eapply lts_choiceR, lts_tau.
         eapply wt_act. eapply lts_fw_p. eapply lts_parL, lts_output. eapply wt_nil.
         eapply union_difference_L in H2.
         rewrite H2. eapply ineq03'.
      ++ inversion H7; subst; inversion H8.
    + assert (gpr_tau (!"a" & !"b") ⊕ gpr_tau (!"a" & !"c") ▷ m ∈ ps').
      eapply H1.
      eapply elem_of_union. left.
      eapply elem_of_singleton. reflexivity.
      eapply wt_act. eapply (lts_fw_out_mb m). eapply wt_nil.
      eapply union_difference_singleton_L in H2.
      rewrite H2. eapply hco.
    + assert (gpr_tau (!"a" & !"b") ⊕ gpr_tau (!"a" & !"c") ▷ {[+ a +]} ⊎ M ∈ ps').
      eapply H1.
      eapply elem_of_union. left.
      eapply elem_of_singleton. reflexivity.
      eapply wt_act. eapply (lts_fw_inp_mb M). eapply wt_nil.
      eapply union_difference_singleton_L in H2.
      rewrite H2. eapply hco.
  - intros. eapply q_terminate.
Qed.
