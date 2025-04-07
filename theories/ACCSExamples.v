From Must Require Import ACCSInstance TransitionSystems Coin.
From stdpp Require Import strings sets gmap base.
From Coq Require Import Relations.


(* Executable step through lts ; i.e. inversion lemma for lts_fw_p *)
Lemma lts_fw_p_step p m α q n :
  lts_fw_step (p ▷ m) α (q ▷ n) ->
  if decide (m = n) then p ⟶{α} q
  else match α with
       | ActExt (ActOut a) => p = q /\ m = {[+ a +]} ⊎ n
       | ActExt (ActIn a) => p = q /\ n = {[+ a +]} ⊎ m
       | τ => exists a, p ⟶[ActIn a] q /\ m = {[+ a +]} ⊎ n
       end.
Proof.
intro H. inversion H; subst.
- rewrite decide_True; trivial.
- rewrite decide_False. split; trivial. symmetry. apply gmultiset_neq_s.
- rewrite decide_False. split; trivial. apply gmultiset_neq_s.
- rewrite decide_False. eexists. split; eauto. symmetry. apply gmultiset_neq_s.
Qed.

(* inversion lemma for lts *)
Lemma lts_inv p α q : lts p α q ->
  match p with
  | pr_input a t => α = ActExt (ActIn a)  /\ q = t
  | !a => exists a, α = ActExt (ActOut a) /\ q = pr_nil
  | g (τ⋅ t) => q = t /\ α = τ
  | p1 ∥ p2 =>
     (exists q1, exists q2, q = q1 ∥ q2 /\ α = τ /\ exists μ, lts p1 (ActExt μ) q1 /\ lts p2 (ActExt (co μ)) q2) \/
     (exists q1, q = q1 ∥ p2 /\ lts p1 α q1) \/
     (exists q2, q = p1 ∥ q2 /\ lts p2 α q2)
  | p1 ⊕ p2 => lts (g p1) α q \/ lts (g p2) α q
  | pr_rec x p => α = τ /\ q = pr_subst x p (pr_rec x p)
  | pr_var _ | pr_success | pr_nil => False
  end.
Proof.
intro Hl. inversion Hl; subst; intuition; eauto. left.
eexists; eexists. split. reflexivity. intuition.
eexists. split; eassumption.
Qed.

(* Proof of hoisting *)


Ltac contradict_by_stability :=
match goal with H : lts_step ?p ?a ?q |- _  =>
  let Hs := fresh "Hf" in 
  assert(Hs : lts_stable p a) by reflexivity; contradict Hs; apply lts_stable_spec2;
  exists q; exact H end.

Lemma parallel_output_terminate M a b : (!a ∥ !b ▷ M) ⤓.
Proof.
constructor. intros (p, M') Hl. simpl in Hl.
apply lts_fw_p_step in Hl. case decide in Hl; subst.
- inversion Hl; subst.
  + inversion H1; subst. inversion H2; subst.
  + inversion H3.
  + inversion H3.
- destruct Hl as (a' & Hl & Heq). subst.
  inversion Hl; subst; inversion H3.
  (* we rely on the fact that we can contradict impossible inputs *)
Qed.


Lemma q_terminate : forall M, (!"a" ∥ (τ⋅ !"b" ⊕  τ⋅ !"c") ▷ M) ⤓.
Proof.
intro M. constructor. intros (p1, M1) l.
apply lts_fw_p_step in l. case decide in l.
(* τ *)
- subst. apply lts_inv in l.
  destruct l as [(q1 & q2 & Heq & _ & μ & _ & Hl)| [(q1 & Heq & Hl) | (q2 & Heq & Hl)]];
  subst.
  + apply lts_inv in Hl. destruct Hl as [Hl | Hl];
    apply lts_inv in Hl; destruct Hl as [Heq Hf]; subst; discriminate Hf.
  + subst. apply lts_inv in Hl. destruct Hl as (a & Hf & _). discriminate Hf.
  + subst. apply lts_inv in Hl. destruct Hl as [Hl | Hl].
    * apply lts_inv in Hl; destruct Hl as [Heq _]; subst.
      apply parallel_output_terminate.
    * apply lts_inv in Hl; destruct Hl as [Heq _]; subst.
      apply parallel_output_terminate.
- destruct l as (a & Hl & Heq). subst.
  (* if a parallel makes an input, one of them does *)
  apply lts_inv in Hl.
  destruct Hl as [(q1 & q2 & _ & Hf & μ & _ & Hl)| [(q1 & Heq & Hl) | (q2 & Heq & Hl)]];
  subst.
  + discriminate.
  + subst. apply lts_inv in Hl. destruct Hl as (b & Hf & _). discriminate.
  + subst. apply lts_inv in Hl. destruct Hl as [Hl | Hl];
    apply lts_inv in Hl; destruct Hl as [Heq _]; subst.
    * apply parallel_output_terminate.
    * apply parallel_output_terminate.
Qed.

Lemma ineq01 : forall (M : mb name) X,
    {[ τ⋅ (!"a" ∥ !"b") ⊕ τ⋅ (!"a" ∥ !"c") ▷ M ]} ∪ X
      ⩽ !"a" ∥ !"b" ▷ M.
Proof.
  cofix hco.
  intros.
  split.
  - intros (q', M') l. inversion l; subst; contradict_by_stability.
  - intros pM' Hs.
    exists (τ⋅ (!"a" ∥ !"b") ⊕ τ⋅ (!"a" ∥ !"c") ▷ M), (!"a" ∥ !"b" ▷ M).
    split.
    + eapply elem_of_union; left; now eapply elem_of_singleton_2.
    + split. eapply wt_tau.
      eapply lts_fw_p, lts_choiceL, lts_tau.
      eapply wt_nil. split. eassumption. set_solver.
  - intros.
    inversion H0; subst.
    + inversion H6; subst.
      ++ inversion H7; subst.
         assert (pr_nil ∥ !"b" ▷ M ∈ ps').
         eapply H1.
         eapply elem_of_union. left.
         eapply elem_of_singleton. reflexivity.
         eapply wt_tau. eapply lts_fw_p, lts_choiceL, lts_tau.
         eapply wt_act. eapply lts_fw_p, lts_parL, lts_output.
         eapply wt_nil.
         eapply union_difference_singleton_L in H2.
         rewrite H2. eapply h_cup. eapply coin_refl.
      ++ inversion H7; subst.
         assert (!"a" ∥ pr_nil ▷ M ∈ ps').
         eapply H1.
         eapply elem_of_union. left.
         eapply elem_of_singleton. reflexivity.
         eapply wt_tau. eapply lts_fw_p, lts_choiceL, lts_tau.
         eapply wt_act. eapply lts_fw_p, lts_parR, lts_output.
         eapply wt_nil.
         eapply union_difference_singleton_L in H2.
         rewrite H2. eapply h_cup. eapply coin_refl.
    + assert (τ⋅ (!"a" ∥ !"b") ⊕ τ⋅ (!"a" ∥ !"c") ▷ m ∈ ps').
      eapply H1.
      eapply elem_of_union. left.
      eapply elem_of_singleton. reflexivity.
      eapply wt_act. eapply (lts_fw_out_mb m). eapply wt_nil.
      eapply union_difference_singleton_L in H2.
      rewrite H2. eapply hco.
    + assert (τ⋅ (!"a" ∥ !"b") ⊕ τ⋅ (!"a" ∥ !"c") ▷ {[+ a +]} ⊎ M ∈ ps').
      eapply H1.
      eapply elem_of_union. left.
      eapply elem_of_singleton. reflexivity.
      eapply wt_act. eapply (lts_fw_inp_mb M). eapply wt_nil.
      eapply union_difference_singleton_L in H2.
      rewrite H2. eapply hco.
  - intros. constructor.
    intros (q', M') l. inversion l; subst; contradict_by_stability.
Qed.

Example ineq02 : forall (M : mb name) X,
    {[ τ⋅ (!"a" ∥ !"b") ⊕ τ⋅ (!"a" ∥ !"c") ▷ M ]} ∪ X
      ⩽ !"a" ∥ !"c" ▷ M.
Proof.
  cofix hco.
  intros.
  split.
  - intros (q', M') l.
    inversion l; subst; contradict_by_stability.
  - intros.
    exists (τ⋅ (!"a" ∥ !"b") ⊕ τ⋅ (!"a" ∥ !"c") ▷ M), (!"a" ∥ !"c" ▷ M).
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
         assert (pr_nil ∥ !"c" ▷ M ∈ ps').
         eapply H1.
         eapply elem_of_union. left.
         eapply elem_of_singleton. reflexivity.
         eapply wt_tau. eapply lts_fw_p, lts_choiceR, lts_tau.
         eapply wt_act. eapply lts_fw_p, lts_parL, lts_output.
         eapply wt_nil.
         eapply union_difference_singleton_L in H2.
         rewrite H2. eapply h_cup. eapply coin_refl.
      ++ inversion H7; subst.
         assert (!"a" ∥ pr_nil ▷ M ∈ ps').
         eapply H1.
         eapply elem_of_union. left.
         eapply elem_of_singleton. reflexivity.
         eapply wt_tau. eapply lts_fw_p, lts_choiceR, lts_tau.
         eapply wt_act. eapply lts_fw_p, lts_parR, lts_output.
         eapply wt_nil.
         eapply union_difference_singleton_L in H2.
         rewrite H2. eapply h_cup. eapply coin_refl.
    + assert (τ⋅ (!"a" ∥ !"b") ⊕ τ⋅ (!"a" ∥ !"c") ▷ m ∈ ps').
      eapply H1.
      eapply elem_of_union. left.
      eapply elem_of_singleton. reflexivity.
      eapply wt_act. eapply (lts_fw_out_mb m). eapply wt_nil.
      eapply union_difference_singleton_L in H2.
      rewrite H2. eapply hco.
    + assert (τ⋅ (!"a" ∥ !"b") ⊕ τ⋅ (!"a" ∥ !"c") ▷ {[+ a +]} ⊎ M ∈ ps').
      eapply H1.
      eapply elem_of_union. left.
      eapply elem_of_singleton. reflexivity.
      eapply wt_act. eapply (lts_fw_inp_mb M). eapply wt_nil.
      eapply union_difference_singleton_L in H2.
      rewrite H2. eapply hco.
  - intros. constructor.
    intros (q', M') l. inversion l; subst; contradict_by_stability.
Qed.

Example ineq03 : forall (M : mb name) X,
    {[ (!"b" ▷ M); (!"c" ▷ M) ]} ∪ X
      ⩽ τ⋅ !"b" ⊕ τ⋅ !"c" ▷ M.
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
      replace ({[!"b" ▷ M'; !"c" ▷ M']})
        with ({[!"c" ▷ M'; !"b" ▷ M']} : gset (proc * mb name)).
      eapply h_cup. eapply coin_refl.
      eapply leibniz_equiv.
      intros q.
      split; intros h%elem_of_union; destruct h as [hl | hr]; eapply elem_of_union; eauto.
    + inversion H2; subst; inversion H4.
  - intros.
    exfalso. eapply (lts_stable_spec2 (τ⋅ !"b" ⊕ τ⋅ !"c" ▷ M)).
    eexists. eapply lts_fw_p, lts_choiceL, lts_tau. assumption.
  - intros. inversion H0; subst.
    + inversion H6; subst; inversion H7.
    + assert ({[!"b" ▷ m; !"c" ▷ m ]} ⊆ ps').
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
    + assert ({[!"b" ▷ {[+ a +]} ⊎ M; !"c" ▷ {[+ a +]} ⊎ M]} ⊆ ps').
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
    inversion l; subst; try contradict_by_stability. inversion H3; subst.
    + inversion H5; subst. constructor. intros.
      inversion H0; subst; contradict_by_stability.
    + inversion H5; subst. constructor. intros.
      inversion H0; subst; contradict_by_stability.
Qed.

Example ineq03' : forall (M : mb name) X,
    {[ (pr_nil ∥ !"b" ▷ M); (pr_nil ∥ !"c" ▷ M) ]} ∪ X
      ⩽ τ⋅ (pr_nil ∥ !"b") ⊕ τ⋅ (pr_nil ∥ !"c") ▷ M.
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
      replace ({[pr_nil ∥ !"b" ▷ M'; pr_nil ∥ !"c" ▷ M']})
        with ({[pr_nil ∥ !"c" ▷ M'; pr_nil ∥  !"b" ▷ M']} : gset (proc * mb name)).
      eapply h_cup. eapply coin_refl.
      eapply leibniz_equiv.
      intros q.
      split; intros h%elem_of_union; destruct h as [hl | hr]; eapply elem_of_union; eauto.
    + inversion H2; subst; inversion H4.
  - intros.
    exfalso. eapply (lts_stable_spec2 (τ⋅ (pr_nil ∥ !"b") ⊕ τ⋅ (pr_nil ∥ !"c") ▷ M)).
    eexists. eapply lts_fw_p, lts_choiceL, lts_tau. assumption.
  - intros. inversion H0; subst.
    + inversion H6; subst; inversion H7.
    + assert ({[pr_nil ∥ !"b" ▷ m; pr_nil ∥ !"c" ▷ m ]} ⊆ ps').
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
    + assert ({[pr_nil ∥ !"b" ▷ {[+ a +]} ⊎ M; pr_nil ∥ !"c" ▷ {[+ a +]} ⊎ M]} ⊆ ps').
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
    inversion l; subst; try contradict_by_stability. inversion H3; subst.
    + inversion H5; subst. constructor. intros.
      inversion H0; subst; contradict_by_stability.
    + inversion H5; subst. constructor. intros.
      inversion H0; subst; contradict_by_stability.
Qed.

Example ineq4 : forall (M : mb name) X,
    {[ τ⋅ (!"a" ∥ !"b") ⊕ τ⋅ (!"a" ∥ !"c") ▷ M ]} ∪ X
      ⩽ !"a" ∥ (τ⋅ !"b" ⊕ τ⋅ !"c") ▷ M.
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
    + contradict_by_stability.
  - intros. exfalso.
    eapply (lts_stable_spec2 (!"a" ∥ (τ⋅ !"b" ⊕ τ⋅ !"c") ▷ M)); eauto.
    exists (!"a" ∥ !"b" ▷ M). eapply lts_fw_p, lts_parR, lts_choiceL, lts_tau.
  - intros. inversion H0; subst. 
    + inversion H6; subst. inversion H7; subst.
      ++ eapply h2.
        ** etrans. eapply t_step. eapply cgr_par_nil_rev.
           etrans. eapply t_step. eapply cgr_par_com. reflexivity.
        ** eapply (h2 (τ⋅ (pr_nil ∥ !"b") ⊕ τ⋅ (pr_nil ∥ !"c"))).
           symmetry.
           etrans. eapply t_step. eapply cgr_choice.
           eapply cgr_tau. eapply cgr_par_nil_rev.
           eapply cgr_tau. eapply cgr_par_nil_rev.
           etrans. eapply t_step. eapply cgr_choice.
           eapply cgr_tau. eapply cgr_par_com.
           eapply cgr_tau. eapply cgr_par_com. reflexivity.
           assert ({[ (pr_nil ∥ !"b" ▷ M); (pr_nil ∥ !"c" ▷ M) ]} ⊆ ps').
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
    + assert (τ⋅ (!"a" ∥ !"b") ⊕ τ⋅ (!"a" ∥ !"c") ▷ m ∈ ps').
      eapply H1.
      eapply elem_of_union. left.
      eapply elem_of_singleton. reflexivity.
      eapply wt_act. eapply (lts_fw_out_mb m). eapply wt_nil.
      eapply union_difference_singleton_L in H2.
      rewrite H2. eapply hco.
    + assert (τ⋅ (!"a" ∥ !"b") ⊕ τ⋅ (!"a" ∥ !"c") ▷ {[+ a +]} ⊎ M ∈ ps').
      eapply H1.
      eapply elem_of_union. left.
      eapply elem_of_singleton. reflexivity.
      eapply wt_act. eapply (lts_fw_inp_mb M). eapply wt_nil.
      eapply union_difference_singleton_L in H2.
      rewrite H2. eapply hco.
  - intros. eapply q_terminate.
Qed.
