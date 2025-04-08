From Must Require Import ACCSInstance TransitionSystems Coin.
From stdpp Require Import strings sets gmap base.
From Coq Require Import Relations.

Ltac lts_inversion q :=
match goal with
| H : lts_step ?p ?a q |- _ => inversion H; subst; clear H
| H : lts ?p ?a q |- _ => inversion H; subst; clear H end.

(* TODO: still needed? *)
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

(* Given an assumption that a tau transition reaches q, 
  make a case distinction on the possible values of q *)
Ltac step_tac H0 :=
  let H := fresh H0 in
  assert(H := H0);
  (apply lts_tau_set_spec in H || apply lts_set_input_spec1 in H);
  vm_compute in H; simpl in H; discriminate ||
  apply elem_of_list_In in H; simpl in H;
  repeat destruct H as [H | H]; subst.

(* A tactic to try and prove termination *)
Ltac term_tac l :=
  constructor;
  let p := fresh "p" in let M := fresh "M" in
  intros (p, M) l; apply lts_fw_p_step in l; case decide in l; subst;
  [ step_tac l
  | let a := fresh "a" in let Ha := fresh "Ha" in let HM := fresh "HM" in
    destruct l as (a & Ha & HM); subst; step_tac Ha
  ]; tauto || let H := fresh l in try term_tac H.

Example q_terminate : forall M, (!"a" ∥ (τ⋅ !"b" ⊕  τ⋅ !"c") ▷ M) ⤓.
Proof. intro M. term_tac H. Qed.


Lemma choice_copre_l p q: forall (M : mb name) X,
  {[τ⋅ p ⊕ τ⋅ q ▷ M]} ∪ X ⩽ p ▷ M.
Proof.
intros M X. eapply c_tau.
- apply h_cup, coin_refl.
- constructor. apply lts_choiceL. constructor.
Qed.

Lemma choice_copre_r p q: forall (M : mb name) X,
  {[τ⋅ p ⊕ τ⋅ q ▷ M]} ∪ X ⩽ q ▷ M.
Proof.
intros M X. eapply c_tau.
- apply h_cup, coin_refl.
- constructor. apply lts_choiceR. constructor.
Qed.

(* TODO: generalise and move *)
Lemma choice_elem_of (p : (proc * mb name)) X: p ∈ X -> X ⩽ p.
Proof.
intro Hin. setoid_rewrite (union_difference_singleton_L p X Hin).
apply h_cup, coin_refl.
Qed.


(* /!\ set_solver may use coinduction hypothesis! *)
Lemma choice_copre_rev p q: forall M X,
  {[ (p ▷ M); (q ▷ M) ]} ∪ X ⩽ τ⋅ p ⊕ τ⋅ q ▷ M.
Proof.
cofix hco.
intros. split.
- clear hco. intros (q', M') l. apply lts_fw_p_step in l. case decide in l.
  + subst. apply lts_inv in l. destruct l as [Hp | Hq].
    * inversion Hp; subst. apply choice_elem_of. set_solver.
    * inversion Hq; subst. apply choice_elem_of. set_solver.
  + destruct l as (a & Ha & Heq); subst.
    apply lts_inv in Ha. destruct Ha as [Ha | Ha]; inversion Ha.
- intros Ht Hs.
  exfalso. eapply (lts_stable_spec2 (τ⋅ p ⊕ τ⋅ q ▷ M)).
  eexists. eapply lts_fw_p, lts_choiceL, lts_tau. assumption.
- intros μ q' ps' H0 Hμ Hw. inversion Hμ; subst.
  + repeat lts_inversion q0.
  + rewrite (union_difference_L {[p ▷ m; q ▷ m ]} ps'). apply hco.
    clear hco.
    intros p' mem%elem_of_union.
    destruct mem as [hl%elem_of_singleton | hr%elem_of_singleton]; subst.
    * apply Hw with (p ▷ {[+ a +]} ⊎ m). set_solver.
      eapply wt_act. eapply (lts_fw_out_mb m). eapply wt_nil.
    * apply Hw with (q ▷ {[+ a +]} ⊎ m). set_solver.
      eapply wt_act. eapply (lts_fw_out_mb m). eapply wt_nil.
  + rewrite (union_difference_L {[p ▷ {[+ a +]} ⊎ M; q ▷ {[+ a +]} ⊎ M]} ps'). apply hco.
    clear hco.
    intros p' mem%elem_of_union.
    destruct mem as [hl%elem_of_singleton | hr%elem_of_singleton]; subst.
    * apply Hw with (p ▷ M). set_solver.
      eapply wt_act. apply lts_fw_inp_mb. apply wt_nil.
    * eapply Hw with (q ▷ M). set_solver.
      eapply wt_act. eapply lts_fw_inp_mb. eapply wt_nil.
- clear hco. intros Ht. constructor. intros (q', M') l.
  inversion l; subst; try contradict_by_stability.
  repeat lts_inversion q'.
  + apply Ht. set_solver.
  + apply Ht. set_solver.
Qed.

Example code_hoisting : forall (M : mb name) X,
    {[ τ⋅ (!"a" ∥ !"b") ⊕ τ⋅ (!"a" ∥ !"c") ▷ M ]} ∪ X
      ⩽ !"a" ∥ (τ⋅ !"b" ⊕ τ⋅ !"c") ▷ M.
Proof.
cofix hco.
intros M X. split.
- intros q l. lts_inversion q.
  + lts_inversion q0.
   * repeat lts_inversion q2.
   * lts_inversion p2.
   * repeat lts_inversion q2.
    -- apply choice_copre_l.
    -- apply choice_copre_r.
  + contradict_by_stability.
- intros. exfalso.
  eapply (lts_stable_spec2 (!"a" ∥ (τ⋅ !"b" ⊕ τ⋅ !"c") ▷ M)); eauto.
  exists (!"a" ∥ !"b" ▷ M). eapply lts_fw_p, lts_parR, lts_choiceL, lts_tau.
- intros μ q' ps' H0 Hμ Hw. inversion Hμ; subst.
  + lts_inversion q; subst. lts_inversion p2; subst.
  (* h2 : pas beau ! adhoc ; ACCS *)
    * eapply h2.
      -- etrans. eapply t_step. eapply cgr_par_nil_rev.
         etrans. eapply t_step. eapply cgr_par_com. reflexivity.
      -- eapply (h2 (τ⋅ (pr_nil ∥ !"b") ⊕ τ⋅ (pr_nil ∥ !"c"))).
        ++ symmetry.
           etrans. eapply t_step. eapply cgr_choice.
           eapply cgr_tau. eapply cgr_par_nil_rev.
           eapply cgr_tau. eapply cgr_par_nil_rev.
           etrans. eapply t_step. eapply cgr_choice.
           eapply cgr_tau. eapply cgr_par_com.
           eapply cgr_tau. eapply cgr_par_com. reflexivity.
        ++ assert (Hi : {[ (pr_nil ∥ !"b" ▷ M); (pr_nil ∥ !"c" ▷ M) ]} ⊆ ps'). {
            intros x mem%elem_of_union.
             destruct mem as [hl%elem_of_singleton | hr%elem_of_singleton]; subst.
             eapply Hw. eapply elem_of_union. left. now eapply elem_of_singleton.
             eapply wt_tau. eapply lts_fw_p. eapply lts_choiceL, lts_tau.
             eapply wt_act. eapply lts_fw_p. eapply lts_parL, lts_output. eapply wt_nil.
             eapply Hw. eapply elem_of_union. left. now eapply elem_of_singleton.
             eapply wt_tau. eapply lts_fw_p. eapply lts_choiceR, lts_tau.
             eapply wt_act. eapply lts_fw_p. eapply lts_parL, lts_output. eapply wt_nil.
           }
           eapply union_difference_L in Hi.
           rewrite Hi. eapply choice_copre_rev.
    * repeat lts_inversion q2.
  + assert (Hin : τ⋅ (!"a" ∥ !"b") ⊕ τ⋅ (!"a" ∥ !"c") ▷ m ∈ ps').
    * eapply Hw.
      eapply elem_of_union. left.
      eapply elem_of_singleton. reflexivity.
      eapply wt_act. eapply (lts_fw_out_mb m). eapply wt_nil.
    * eapply union_difference_singleton_L in Hin.
      rewrite Hin. eapply hco.
  + assert (Hin : τ⋅ (!"a" ∥ !"b") ⊕ τ⋅ (!"a" ∥ !"c") ▷ {[+ a +]} ⊎ M ∈ ps').
    * eapply Hw.
      eapply elem_of_union. left.
      eapply elem_of_singleton. reflexivity.
      eapply wt_act. eapply (lts_fw_inp_mb M). eapply wt_nil.
    * eapply union_difference_singleton_L in Hin.
      rewrite Hin. eapply hco.
- intros. eapply q_terminate.
Qed.

(* TODO: generalise, and avoid using h2 *)
Example code_hoisting_gen a b c: forall (M : mb name) X,
    {[ τ⋅ (a ∥ b) ⊕ τ⋅ (a ∥ c) ▷ M ]} ∪ X
      ⩽ a ∥ (τ⋅ b ⊕ τ⋅ c) ▷ M.
Proof.
cofix hco.
intros M X. split.
- intros q l. lts_inversion q.
  + lts_inversion q0.
   * repeat lts_inversion q2.
   * admit.
   * repeat lts_inversion q2.
    -- apply choice_copre_l.
    -- apply choice_copre_r.
  + admit.
- intros. exfalso.
  eapply (lts_stable_spec2 (a ∥ (τ⋅ b ⊕ τ⋅ c) ▷ M)); eauto.
  exists (a ∥ b ▷ M). eapply lts_fw_p, lts_parR, lts_choiceL, lts_tau.
- intros μ q' ps' H0 Hμ Hw. inversion Hμ; subst.
  + lts_inversion q.
  (* h2 : pas beau ! adhoc ; ACCS *)
    * admit.
    * repeat lts_inversion q2.
  + assert (Hin : τ⋅ (a ∥ b) ⊕ τ⋅ (a ∥ c) ▷ m ∈ ps').
    * eapply Hw.
      eapply elem_of_union. left.
      eapply elem_of_singleton. reflexivity.
      eapply wt_act. eapply (lts_fw_out_mb m). eapply wt_nil.
    * eapply union_difference_singleton_L in Hin.
      rewrite Hin. eapply hco.
  + assert (Hin : τ⋅ (a ∥ b) ⊕ τ⋅ (a ∥ c) ▷ {[+ a0 +]} ⊎ M ∈ ps').
    * eapply Hw.
      eapply elem_of_union. left.
      eapply elem_of_singleton. reflexivity.
      eapply wt_act. eapply (lts_fw_inp_mb M). eapply wt_nil.
    * eapply union_difference_singleton_L in Hin.
      rewrite Hin. eapply hco.
- intros Ht. constructor. intros q Hq. lts_inversion q.
  + lts_inversion q0.
    * repeat lts_inversion q2.
    * apply terminate_preserved_by_lts_tau with (a ∥ (τ⋅ b ⊕ τ⋅ c) ▷ M).
      -- eapply hco. exact Ht. (* cheating? *)
      -- now do 2 constructor.
    * repeat lts_inversion q2.
      -- admit.
      -- admit.
  + admit.
Admitted.