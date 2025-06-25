From Must Require Import ACCSInstance TransitionSystems Coin Termination
                         Must Completeness Soundness Equivalence.
From stdpp Require Import strings sets gmap base gmultiset.
From Coq Require Import Relations.
From Coq Require Import Program.Equality.
From Must Require Import Must.


Ltac lts_inversion := Termination.lts_inversion lts; try discriminate.
Ltac step_tac := Termination.step_tac lts; simpl.
Ltac term_tac := repeat step_tac.

(*
(* Parallel composition in ACCS is similar to the parallel composition of LTSs *)
Lemma accs_parallel_sim (p q : proc) :
  (p ∥ q) ≲ (p, q).
Proof.
revert p q. cofix hco. intros p q. constructor.
intros α r Hstep. inversion Hstep; subst.
- eexists (p2, q2); split.
  + econstructor; simpl; eauto. now destruct μ.
  + apply hco.
- eexists; split.
  + econstructor; simpl; eauto.
  + apply hco.
- eexists; split.
  + econstructor; simpl; eassumption.
  + apply hco.
Qed.

(* Parallel composition in ACCS with forwarders is similar to
  the parallel composition of LTSs (with forwarder on one side) *)
Lemma accs_fw_parallel_sim (p q : proc) (M : mb name):
  ((p ∥ q) ▷ M) ≲ (p, (q ▷ M)).
Proof.
revert M p q. cofix hco. intros M p q. constructor.
intros α r Hstep. inversion Hstep; subst.
- inversion H3; subst.
  + exists (p2, (q2, M)); split.
    * eapply ParSync with (α1 := ActExt μ) (α2 := ActExt (co μ)); trivial.
      -- destruct μ; simpl; trivial.
      -- now constructor.
    * apply hco.
  + eexists; split.
    * econstructor; simpl; eauto.
    * apply hco.
  + eexists; split.
    * econstructor 2; simpl. constructor. eassumption.
    * apply hco.
- eexists; split.
  + econstructor 2; simpl; constructor 2.
  + apply hco.
- eexists; split.
  + econstructor 2; simpl; constructor 3.
  + apply hco.
- inversion H3; subst.
  + exists (p2, (q, m)); split.
    * apply ParSync with (α1 := ActExt (ActIn a))
                          (α2 := ActExt (ActOut a)); simpl; eauto.
      constructor.
    * apply hco.
  + exists (p, (q2, m)); split.
    * econstructor 2; simpl. constructor. eassumption.
    * apply hco.
Qed.
*)

Derive Inversion_clear lts_inv with (forall p a q, lts p a q) Sort Prop.
Derive Inversion_clear lts_step_inv with (forall p a q, lts_fw_step p a q)
  Sort Prop.
(*
Lemma pr_nil_similar p : (pr_nil ∥ p) ≲ p.
Proof.
revert p. cofix hco. intro p.
constructor. intros α q Hq. lts_inversion.
- inversion H1.
- inversion H3.
- eexists; split; eauto.
Qed.
*)

Hint Constructors lts_fw_step : lts.
Hint Constructors lts : lts.
Hint Unfold lts_step : lts.
Hint Extern 0 => simpl : lts.

(*
Lemma pr_nil_fw_similar p M : (pr_nil ∥ p ▷ M) ≲ (p ▷ M).
Proof.
revert p M. cofix hco. intros p M.
constructor. intros α q Hq. lts_inversion.
- lts_inversion.
  + inversion H1.
  + inversion H4.
  + eexists; split; eauto with lts.
- eexists; split; eauto with lts.
- eexists; split; eauto with lts.
- lts_inversion.
  + inversion H4.
  + eexists; split; eauto with lts.
Qed.

Lemma parallel_output_mb_similar μ (q : proc) (M : mb name):
  (!μ ∥ q  ▷ M) ≲ (q ▷ {[+ μ +]} ⊎ M).
Proof.
revert q M. cofix hco. intros q M.
constructor. intros α r Hstep.
inversion Hstep; subst; clear Hstep.
- lts_inversion.
  + inversion H1; subst. eexists; split; eauto.
    * apply lts_fw_com. eauto.
    * apply pr_nil_fw_similar.
  + lts_inversion. eexists; split; eauto.
    * apply lts_fw_out_mb.
    * apply pr_nil_fw_similar.
  + eexists; split; eauto.
    now apply lts_fw_p.
- eexists; split; eauto.
  replace ({[+ μ +]} ⊎ ({[+ a +]} ⊎ m)) with ({[+ a +]} ⊎ ({[+ μ +]} ⊎ m));
  [constructor| clear hco; multiset_solver].
- eexists; split; eauto.
  replace ({[+ μ +]} ⊎ ({[+ a +]} ⊎ M)) with ({[+ a +]} ⊎ ({[+ μ +]} ⊎ M));
  [constructor| clear hco; multiset_solver].
- lts_inversion.
  + lts_inversion.
  + exists (q2 ▷ {[+ μ +]} ⊎ m); split.
    * replace ({[+ μ +]} ⊎ ({[+ a +]} ⊎ m)) with ({[+ a +]} ⊎ ({[+ μ +]} ⊎ m));
      [now constructor| clear hco; multiset_solver].
    * apply hco.
Qed.


Lemma parallel_output_terminate M a b : (!a ∥ !b ▷ M) ⤓.
Proof.
constructor. intros (p, M') Hl. inversion Hl; subst.
- repeat lts_inversion.
- decompose record Hl. repeat lts_inversion.
Qed.
*)

Example q_terminate : forall M, (!"a" ∥ (τ⋅ !"b" ⊕  τ⋅ !"c") ▷ M) ⤓.
Proof. intro M. term_tac. Qed.

Lemma choice_copre_l p q: forall (M : mb name) X,
  {[τ⋅ p ⊕ τ⋅ q ▷ M]} ∪ X ⩽ p ▷ M.
Proof.
intros M X. eapply c_tau.
- apply coin_union_l, coin_refl.
- constructor. apply lts_choiceL. constructor.
Qed.

Lemma choice_copre_r p q: forall (M : mb name) X,
  {[τ⋅ p ⊕ τ⋅ q ▷ M]} ∪ X ⩽ q ▷ M.
Proof.
intros M X. eapply c_tau.
- apply coin_union_l, coin_refl.
- constructor. apply lts_choiceR. constructor.
Qed.

Lemma choice_copre_rev p q: forall M X,
  {[ (p ▷ M); (q ▷ M) ]} ∪ X ⩽ τ⋅ p ⊕ τ⋅ q ▷ M.
Proof.
cofix hco.
intros. split.
- clear hco. intros (q', M') l.
  inversion_clear l.
  + repeat lts_inversion; apply coin_elem_of; set_tac.
  + repeat lts_inversion.
- intros Ht Hs.
  exfalso. eapply (lts_stable_spec2 (τ⋅ p ⊕ τ⋅ q ▷ M)).
  eexists. eapply lts_fw_p, lts_choiceL, lts_tau. assumption.
- intros μ q' ps' H0 Hμ Hw. inversion Hμ; subst.
  + repeat lts_inversion.
  + rewrite (union_difference_L {[p ▷ m; q ▷ m ]} ps').
    * apply hco.
    * clear hco.
      intros p' mem%elem_of_union.
      destruct mem as [hl%elem_of_singleton | hr%elem_of_singleton]; subst.
      -- apply Hw with (p ▷ {[+ a +]} ⊎ m). set_tac.
         eapply wt_act. eapply (lts_fw_out_mb m). eapply wt_nil.
      -- apply Hw with (q ▷ {[+ a +]} ⊎ m). set_tac.
         eapply wt_act. eapply (lts_fw_out_mb m). eapply wt_nil.
  + rewrite (union_difference_L {[p ▷ {[+ a +]} ⊎ M; q ▷ {[+ a +]} ⊎ M]} ps').
    apply hco. clear hco.
    intros p' mem%elem_of_union.
    destruct mem as [hl%elem_of_singleton | hr%elem_of_singleton]; subst.
    * apply Hw with (p ▷ M). set_tac.
      eapply wt_act. apply lts_fw_inp_mb. apply wt_nil.
    * eapply Hw with (q ▷ M). set_tac.
      eapply wt_act. eapply lts_fw_inp_mb. eapply wt_nil.
- clear hco. intros Ht. constructor. intros (q', M') l.
  inversion l; subst; repeat lts_inversion; apply Ht; set_tac.
Qed.

Hint Resolve coin_elem_of : coin.

(* Recursively delete nil from term *)

Fixpoint proc_absorb_nil (p : proc) := match p with
| (p ∥ q) => let p' := proc_absorb_nil p in
             let q' := proc_absorb_nil q in
             if decide (p' = pr_nil) then q'
             else if decide (q' = pr_nil) then p'
             else p' ∥ q'
| pr_rec n p => pr_rec n (proc_absorb_nil p)
| g gp => g (gproc_absorb_nil gp)
| p => p
end
with gproc_absorb_nil (gp : gproc) : gproc := match gp with
| gpr_input a p => gpr_input a (proc_absorb_nil p)
| gpr_tau p => gpr_tau (proc_absorb_nil p)
| gpr_choice g1 g2 => let g1' := gproc_absorb_nil g1 in
                      let g2' := gproc_absorb_nil g2 in
                      if decide (g g1' = pr_nil) then g2'
                      else if decide (g g2' = pr_nil) then g1'
                      else gpr_choice g1' g2'
| gp => gp
end.

(* Defining mutual induction principle for processes and guards *)
Scheme proc_gproc_ind := Induction for proc Sort Prop
  with gproc_proc_ind := Induction for gproc Sort Prop.

(* TODO : also missing in VACCS *)
Lemma cgr_choice_trans : forall p1 q1 p2 q2, g p1 ≡* g q1 -> g p2 ≡* g q2 -> 
  pr_choice p1 p2 ≡* pr_choice q1 q2.
Proof.
intros. dependent induction H. 
constructor.
Admitted.



Lemma proc_absorb_nil_cgr p : p ≡* proc_absorb_nil p.
Proof.
induction p using proc_gproc_ind with
  (P0 := fun gp => g gp ≡* g (gproc_absorb_nil gp)); simpl; auto with *.
- case decide; intro Heq; subst. {
  transitivity (𝟘 ∥ p2).
    + apply cgr_par_left. etrans; [eassumption|].
      rewrite Heq. reflexivity.
    + etrans; [|eassumption].
      etrans; constructor.
      * apply cgr_par_com.
      * constructor.
  }
  case decide; intro Heq'. {
  transitivity (p1 ∥ 𝟘).
    + apply cgr_par_right. etrans; [eassumption|].
      rewrite Heq'. reflexivity.
    + etrans; [|eassumption]. constructor. constructor.
  }
  etrans; [apply cgr_par_left; eassumption|].
  etrans; [apply cgr_par_right; eassumption|].
  reflexivity.
- induction IHp; [now repeat constructor| etrans; eassumption].
- induction IHp; [now repeat constructor| etrans; eassumption].
- induction IHp; [now repeat constructor| etrans; eassumption].
- case decide; intro Heq; subst. {
  transitivity (gpr_nil ⊕ g0).
    + eapply cgr_choice_trans; [|reflexivity]. etrans; [eassumption|].
      rewrite Heq. reflexivity.
    + etrans; [constructor; apply cgr_choice_com|].
      etrans; [constructor; apply cgr_choice_nil|]. assumption.
  }
  case decide; intro Heq'. {
  transitivity (g ⊕ gpr_nil).
    + apply cgr_choice_trans; [reflexivity|]. etrans; [eassumption|].
      rewrite Heq'. reflexivity.
    + etrans; [constructor; apply cgr_choice_nil|]. assumption.
  }
  apply cgr_choice_trans; assumption.
Qed.


Example code_hoisting_outputs : forall (M : mb name) X,
    {[ τ⋅ (!"a" ∥ !"b") ⊕ τ⋅ (!"a" ∥ !"c") ▷ M ]} ∪ X
      ⩽ !"a" ∥ (τ⋅ !"b" ⊕ τ⋅ !"c") ▷ M.
Proof.
cofix hco.
intros M X. split.
- intros q l. repeat lts_inversion.
  + apply choice_copre_l.
  + apply choice_copre_r.
- intros. exfalso.
  eapply (lts_stable_spec2 (!"a" ∥ (τ⋅ !"b" ⊕ τ⋅ !"c") ▷ M)); eauto.
  exists (!"a" ∥ !"b" ▷ M). eapply lts_fw_p, lts_parR, lts_choiceL, lts_tau.
- intros μ q' ps' H0 Hμ Hw. inversion Hμ; subst.
  + repeat lts_inversion.
    eapply h2.
    -- etrans. eapply t_step. eapply cgr_par_nil_rev.
       etrans. eapply t_step. eapply cgr_par_com. reflexivity.
    -- eapply (h2 (τ⋅ (pr_nil ∥ !"b") ⊕ τ⋅ (pr_nil ∥ !"c"))).
      ++ apply proc_absorb_nil_cgr.
      ++ assert (Hi : {[ (pr_nil ∥ !"b" ▷ M); (pr_nil ∥ !"c" ▷ M) ]} ⊆ ps'). {
          intros x mem%elem_of_union.
           destruct mem as [hl%elem_of_singleton | hr%elem_of_singleton]; subst.
           - eapply Hw.
            + eapply elem_of_union. left. now eapply elem_of_singleton.
            + eapply wt_tau. apply lts_fw_p. apply lts_choiceL, lts_tau.
              eapply wt_act. eapply lts_fw_p. eapply lts_parL, lts_output.
              eapply wt_nil.
           - eapply Hw.
            + eapply elem_of_union. left. now eapply elem_of_singleton.
            + eapply wt_tau. eapply lts_fw_p. eapply lts_choiceR, lts_tau.
              eapply wt_act.
              * eapply lts_fw_p. eapply lts_parL, lts_output. 
              * eapply wt_nil.
         }
         eapply union_difference_L in Hi.
         rewrite Hi. eapply choice_copre_rev.
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

Section Omega.

Definition omega := pr_rec 0 (pr_var 0). (* rec X. X *)

Lemma omega_diverges : ¬ terminate omega.
Proof.
intro Ht. dependent induction Ht.
apply (H0 omega).
- term_tac.
- trivial.
Qed.

Lemma omega_is_bottom p : {[omega]} ⩽ p.
Proof.
revert p.
cofix hco. intros p.
constructor.
- intros q Hq. apply hco.
- clear hco. intros Ht _. exfalso. apply omega_diverges, (Ht omega).
  auto with *.
- clear hco. intros a b c Ht _. exfalso.
  eapply omega_diverges, cnv_terminate, (Ht omega).
  auto with *.
- clear hco. intros Ht. exfalso. apply omega_diverges, (Ht omega).
  auto with *.
Qed.

End Omega.

(*
(* In ACCS, recursion unfolding steps are "invertible" τ steps *)
Lemma rec_inv n p : forall μ p',
  (pr_rec n p) ⟶{μ} p' <-> (p' = pr_subst n p (pr_rec n p) /\ μ = τ).
Proof.
intros μ p'. split; intro Hs.
- now lts_inversion.
- destruct Hs; subst. term_tac.
Qed.


(* Remark : proofs using the definition of must are not always difficult *)
Lemma musts_choice (p q : gproc) (e : proc) : 
  must (g p) e -> must (g q) e -> must (p ⊕ q) e.
Proof.
intros Hp Hq.
dependent induction Hp; [now constructor|]. destruct Hq; [now constructor|].
constructor 2.
- trivial.
- destruct ex as [[t1 t1'] H1']. dependent destruction H1'.
  + exists (t1, t1'). apply ParLeft. constructor. assumption.
  + exists (p ⊕ q ▷ t1'). apply ParRight. assumption.
  + exists (t1, t1'). eapply ParSync; eauto.
    constructor. assumption.
- intros p' Hp'. inversion Hp'; subst.
  + apply pt. assumption.
  + apply pt0. assumption.
- intros e' He'. eapply H0; trivial. now apply et0.
- intros p' e' μ Hμ Hμ'. inversion Hμ'; subst.
  + eapply com; eassumption.
  + eapply com0; eassumption.
Qed.
*)


Section Example_2_1.

Definition unreliableW :=
  pr_rec 0 ( τ⋅ ! "end" ⊕ ("data" ? (τ⋅ (! "work" ∥ pr_var 0) ⊕ τ⋅ ! "bye"))).

Definition reliableW :=
  pr_rec 0 (τ⋅ ! "end" ⊕ ("data" ? (! "work" ∥ pr_var 0))).


Lemma reliableW_terminate M : (reliableW ▷ M) ⤓.
Proof.
(* By induction on the number of "data" in the mailbox. *)
remember (multiplicity "data" M) as n. revert M Heqn.
induction n; intros M Hs.
- do 3 step_tac.
  contradict Hs.
  rewrite (multiplicity_disj_union {[+ "data" +]} m "data").
  rewrite multiplicity_singleton. lia.
- step_tac; step_tac; [step_tac|]. fold reliableW.
  eapply terminate_preserved_by_eq.
  + apply (IHn ( {[+"work" +]} ⊎ m)).
    setoid_rewrite multiplicity_disj_union.
    setoid_rewrite multiplicity_singleton_ne; [| by auto].
    setoid_rewrite multiplicity_disj_union in Hs.
    setoid_rewrite multiplicity_singleton in Hs. lia.
  + (* This proof of equivalence can certainly be automated *)
    eapply lts_oba_output_deter_inv.
    * apply (lts_fw_out_mb m reliableW "work").
    * term_tac.
    * apply fw_eq_id_mb. etransitivity.
      -- constructor. apply cgr_par_nil_rev.
      -- constructor. apply cgr_par_com.
Qed.

Fixpoint add_work n p := match n with
| O => p
| S n => add_work n (!"work" ∥ p)
end.

Fixpoint add_data n m : mb name := 
match n with
| O => m
| S n => add_data n ({[+ "data" +]} ⊎ m)
end.

Lemma add_work_comm n p :
  add_work (S n) p = ! "work" ∥ (add_work n p).
Proof.
revert p; induction n; intro p; [trivial|].
once unfold add_work at 2. fold add_work.
rewrite <- IHn. trivial.
Qed.


Lemma add_work_inversion n :
  (forall p q, p ↛[ActIn "work"] -> add_work n p ⟶ q ->
    exists q', p ⟶ q' /\
    q = add_work n q') /\
  (forall p q μ, p ↛[ActIn "work"] -> lts (add_work n p) μ q ->
    ((exists n1 n2, S (n1 + n2) = n /\ q = add_work n2 (𝟘 ∥ add_work n1 p) /\ μ = ActExt (ActOut "work")) \/
    (exists q0, lts p μ q0 /\ q = add_work n q0 ))) /\
  (forall p q μ, lts p μ q -> lts (add_work n p) μ (add_work n q)).
Proof.
induction n; (split; [|split]); intros p q.
- intros Hs Hpq. eexists; split; eauto.
- intros μ Hpq. right. eexists; split; eauto.
- trivial.
- intros Hs Hpq. rewrite add_work_comm in Hpq. lts_inversion.
  + inversion H1. subst. clear H1. apply (proj1 (proj2 IHn)) in H2; trivial.
    destruct H2 as [[n1 [n2 [Heq [Heq' HF]]]]|[q'[Hq' Heq]]];
    subst; [discriminate|].
    unfold lts_stable in Hs. simpl in Hs.
    apply lts_set_spec1 in Hq'. multiset_solver.
  + lts_inversion.
  + apply (proj1 (proj2 IHn)) in H3; trivial.
    destruct H3 as [[n1 [n2 [Heq [Heq' HF]]]]|[q'[Hq' Heq]]];
    subst; [discriminate|].
    exists q'; split; trivial. now rewrite add_work_comm.
- simpl. intros μ Hs Hμ.
  setoid_rewrite (add_work_comm n) in Hμ.
  lts_inversion.
  + inversion H1; subst. clear H1.
    apply (proj1 (proj2 IHn)) in H4; trivial.
    destruct H4 as [[n1 [n2 [Heq [Heq' HF]]]]|[q'[Hq' Heq]]]; subst;
    [discriminate|].
    apply lts_set_spec1 in Hq'. multiset_solver.
  + lts_inversion. left. exists n; exists 0; repeat split; trivial. lia.
  + apply (proj1 (proj2 IHn)) in H3; trivial. clear IHn.
    destruct H3 as [[n1 [n2 [Heq [Heq' HF]]]]|[q'[Hq' Heq]]]; subst.
    * left. exists n1; exists (S n2). repeat split; trivial; [lia|].
      now rewrite add_work_comm.
    * right; exists q'; split; trivial.
      now setoid_rewrite (add_work_comm n).
- intros μ Hμ. repeat rewrite (add_work_comm n).
  apply lts_parR, IHn, Hμ.
Qed.

(* unused 
Lemma parallel_output_preserve_termination a p M :
 (forall q l, wt p l q -> ¬ In (ActIn a) l) -> (p  ▷ M) ⤓ -> (! a ∥ p ▷ M) ⤓.
Proof.
intros Hs Ht. dependent induction Ht generalizing M p Hs.
constructor. intros q Hq.
lts_inversion.
- lts_inversion.
  + inversion H3; subst. clear H3.
    exfalso; apply (Hs q2 [ActIn a]); [|auto with *].
    eapply wt_act; [|apply wt_nil]. assumption.
  + lts_inversion.
  + apply H0 with (q2 ▷ M).
    * constructor; trivial.
    * intros q l Hq. apply (Hs q l).
      apply wt_tau with q2; assumption.
    * trivial.
- lts_inversion.
  + lts_inversion.
  + eapply H0 with (q2 ▷ m); trivial.
    * now constructor.
    * intros q l Hq Ha. apply (Hs q (ActIn a0 :: l)); [|auto with *].
      eapply wt_act; eassumption.
Qed.
*)

(* unused for now
Lemma harmony_wt: ∀ (p q : proc) s,
  (∃ r : proc, p ≡* r ∧ wt r s q) → ∃ r : proc, wt p s r ∧ r ≡* q.
Proof.
intros p q s [r [Heq Hr]]. dependent induction Hr generalizing p Heq.
- eexists; split; eauto using wt_nil.
- destruct (harmony_cgr p q τ) as [r [Hs Heqr]].
  + exists p0. split; trivial.
  + destruct (IHHr r Heqr) as [r' [Hr' Heqr']].
    exists r'; split; trivial.
    apply wt_tau with r; trivial.
- destruct (harmony_cgr p q (ActExt μ)) as [r [Hs Heqr]].
  + exists p0. split; trivial.
  + destruct (IHHr r Heqr) as [r' [Hr' Heqr']].
    exists r'; split; trivial.
    apply wt_act with r; trivial.
Qed.

*)


Lemma cgr_par_nil_l p : 𝟘 ∥ p ≡* p.
Proof.
eapply t_trans.
- eapply t_step, cgr_par_com.
- eapply t_step, cgr_par_nil.
Qed.

(* unused 

Lemma output_no_ActIn p a:
  (forall q l, wt p l q -> ¬ In (ActIn a) l) ->
    (forall q l, wt (! a ∥ p) l q -> ¬ In (ActIn a) l).
Proof.
intros Hp q l Hwt.
dependent induction Hwt; simpl.
- tauto.
- lts_inversion.
  + inversion H1; subst. clear H1.
    intro.
    eapply (Hp q2 [ActIn a]); [|auto with *].
    eapply wt_act; [|apply wt_nil]. eassumption.
  + lts_inversion.
  + eapply IHHwt; [|reflexivity].
    intros q l Hl. eapply (Hp q l).
    eapply wt_tau; [eassumption|]; assumption.
- intros [Heq|HF].
  + subst. lts_inversion; [lts_inversion|].
    apply (Hp q2 [ActIn a]); [|auto with *].
    eapply wt_act; [eassumption| apply wt_nil].
  + lts_inversion.
    * lts_inversion. destruct (harmony_wt p t s) as [r [Hr Heqr]].
      -- exists (𝟘 ∥ p). split; trivial. symmetry; apply cgr_par_nil_l.
      -- apply (Hp r s Hr HF).
    * apply (IHHwt a q2); trivial.
      intros q l Hl. intro Hal. apply (Hp q (μ :: l)); [|auto with *].
      eapply wt_act; [eassumption|]; assumption.
Qed.

Lemma add_work_no_ActIn p n:
  (forall q l, wt p l q -> ¬ In (ActIn "work") l) ->
    (forall q l, wt (add_work n p) l q -> ¬ In (ActIn "work") l).
Proof.
intro Hp. induction n; trivial.
rewrite add_work_comm.
intros. eapply output_no_ActIn; eauto.
Qed.

Lemma add_work_terminate n : ∀ p M,
 (forall q l, wt p l q -> ¬ In (ActIn "work") l) -> (p  ▷ M) ⤓ ->
   (add_work n p ▷ M) ⤓.
Proof.
intros p M Hp Ht.
induction n; trivial.
rewrite add_work_comm.
apply parallel_output_preserve_termination; [|apply IHn].
apply add_work_no_ActIn, Hp.
Qed.

*)

Ltac wt_inversion:=
match goal with
| H : wt ?p ?a ?q |- _ =>
  inversion H; subst; clear H; repeat lts_inversion; simpl in *
end;
try match goal with
| H : ?a ⊎ ?b = ∅ |- _ => contradict H; apply Lift.neq_multi_nil
end;
try discriminate; try tauto; auto with *.

(* Tactic to handle assumptions about add_work *)
Ltac add_tac := match goal with
| H : (lts_step (add_work ?n _) ?μ ?q0) |- _ =>
  apply add_work_inversion in H; try tauto;
  decompose [and or ex] H; subst; clear H; try discriminate
| H : (lts (add_work ?n _) ?μ ?q0) |- _ => 
  apply add_work_inversion in H; try tauto;
  decompose [and or ex] H; subst; clear H; try discriminate
end;
repeat match goal with
| H : ActExt ?A = ActExt ?B |- _ => inversion H; subst end.

Lemma add_work_end_terminate M w : (add_work w (!"end") ▷ M) ⤓.
Proof.
constructor. intros q Hq. inversion Hq; subst;
(add_tac; [lts_inversion|term_tac]).
Qed.

(* Strengthening *)
Lemma add_work_reliableW_terminate M w : (add_work w reliableW ▷ M) ⤓.
Proof.
(* By induction on the number of "data" in the mailbox. *)
remember (multiplicity "data" M) as n. revert M w Heqn.
induction n; intros M w Hs.
- constructor. intros q Hq; lts_inversion;
  (add_tac; [lts_inversion |term_tac]).
  constructor. intros q Hq. lts_inversion;
  (add_tac; [repeat lts_inversion |term_tac]).
  + apply add_work_end_terminate. (* end *)
  + contradict Hs.
    rewrite (multiplicity_disj_union {[+ "data" +]} m "data").
    rewrite multiplicity_singleton. lia.
- constructor. intros q Hq; lts_inversion; (add_tac; [lts_inversion |term_tac]).
  constructor. intros q Hq; lts_inversion;
    (add_tac; [repeat lts_inversion |term_tac]).
  + apply add_work_end_terminate. (* end *)
  + fold reliableW. apply (IHn m (S w)).
    rewrite (multiplicity_disj_union {["data"]} m), multiplicity_singleton in Hs.
    now inversion Hs.
Qed.

(* can be deduced from add_work_reliableW_terminate? *)

Lemma add_data_comm a n m :
 {[+ a +]} ⊎ add_data n m = add_data n ({[+ a +]} ⊎ m).
Proof.
revert m. induction n; intros m; simpl; [|rewrite IHn; f_equal]; multiset_solver.
Qed.


(* TODO: ⟹ should have lower priority than ∥ *)
Lemma wt_par_l p q r s : p ⟹[s] q -> (r ∥ p) ⟹[s] (r ∥ q).
Proof.
intro Ht. induction Ht.
- apply wt_nil.
- apply wt_tau with (r ∥ q); trivial.
  apply lts_parR; trivial.
- apply wt_act with (r ∥ q); trivial.
  apply lts_parR; trivial.
Qed.


Lemma lts_fw_par_l p q α M M' r:
  lts_step (p ▷ M) α (q ▷ M')->
    lts_step (r ∥ p ▷ M) α (r ∥ q ▷ M').
Proof.
intro Hs. inversion Hs; subst.
- now apply lts_fw_p, lts_parR.
- apply (lts_fw_out_mb M' (r ∥ q) a).
- apply (lts_fw_inp_mb M (r ∥ q) a).
- apply (lts_fw_com M' (r ∥ p) a (r ∥ q)), lts_parR. trivial.
Qed.

Lemma wt_par_fw_l p q M M' r s:
  (p ▷ M) ⟹[s] (q ▷ M')->
    (r ∥ p ▷ M) ⟹[s] (r ∥ q ▷ M').
Proof.
intro Ht. dependent induction Ht.
- apply wt_nil.
- destruct q0 as [q0 M0].
  apply wt_tau with (r ∥ q0 ▷ M0).
  + now apply lts_fw_par_l.
  + now apply IHHt.
- destruct q0 as [q0 M0].
  apply wt_act with (r ∥ q0 ▷ M0).
  + now apply lts_fw_par_l.
  + now apply IHHt.
Qed.

Fixpoint add_zeros n p := match n with
| O => p
| S n => add_zeros n (𝟘 ∥ p)
end.

Lemma add_zeroes_comm n p :
  add_zeros (S n) p = 𝟘 ∥ (add_zeros n p).
Proof.
revert p; induction n; intro p; [trivial|].
once unfold add_zeros at 2. fold add_zeros.
rewrite <- IHn. trivial.
Qed.

Lemma add_zeros_lts : forall n p q α,
  lts p α q <-> lts (add_zeros n p) α (add_zeros n q).
Proof.
induction n; intros p q α; trivial.
do 2 rewrite add_zeroes_comm. rewrite IHn. split; intro Hpq.
- apply lts_parR, Hpq.
- lts_inversion.
  + inversion H3.
  + inversion H2.
  + trivial.
Qed.

Lemma add_work_plus x x0 p :
  add_work (x + x0) p = add_work x (add_work x0 p).
Proof.
revert x0 p. induction x as [|x]; intros x0 p; trivial.
simpl. now rewrite IHx, <- add_work_comm.
Qed.

Local Instance Proper_par : Proper (cgr ==> cgr ==> cgr) (fun x y => x ∥ y).
Proof.
intros p p' Hp q q' Hq. 
eapply t_trans.
- apply cgr_par_right, Hq.
- apply cgr_par_left, Hp.
Defined.


Lemma add_zeros_cgr p z : add_zeros z p ≡* p.
Proof.
revert p; induction z; intro p; simpl.
- reflexivity.
- rewrite IHz. apply cgr_par_nil_l.
Qed.


Global Instance Reflexive_cgr : Reflexive cgr.
Proof. intro x. apply t_step, cgr_refl. Defined.

Local Instance Proper_add_work : Proper (eq ==> cgr ==> cgr) add_work.
Proof.
intros n n' Hn. subst n'. induction n; intros p p' Hp; trivial.
do 2 rewrite add_work_comm. apply Proper_par; auto with *.
Defined.

Lemma add_work_par_comm x p1 p2 :
  add_work x (p1 ∥ p2) ≡* p1 ∥ add_work x p2.
Proof.
revert p1 p2. induction x as [|x]; intros p1 p2; simpl; trivial.
- reflexivity.
- repeat rewrite IHx.
  eapply t_trans; [ apply t_step; symmetry; apply cgr_par_ass|].
  eapply t_trans; [|apply t_step, cgr_par_ass].
  apply t_step. apply cgr_par.
  + apply cgr_par_com.
  + reflexivity.
Qed.

Lemma add_zeros_par_comm z p1 p2 :
  add_zeros z (p1 ∥ p2) ≡* p1 ∥ add_zeros z p2.
Proof.
revert p1 p2. induction z as [|x]; intros p1 p2; simpl; trivial.
- reflexivity.
- repeat rewrite IHx.
  eapply t_trans; [ apply t_step; symmetry; apply cgr_par_ass|].
  eapply t_trans; [|apply t_step, cgr_par_ass].
  apply t_step. apply cgr_par.
  + apply cgr_par_com.
  + reflexivity.
Qed.

(* After n unfolding and n "data" received, n "work" have been produced *)
Lemma unreliable_add_work_add_data_terminate z n M :
  (add_zeros z unreliableW ▷ add_data n M) ⟹ (add_zeros z (add_work n (! "end")) ▷ M).
Proof.
revert z M. induction n as [|n]; intros z M; simpl.
- eapply wt_tau; [constructor; apply add_zeros_lts; term_tac|].
  eapply wt_tau; [constructor; apply add_zeros_lts; term_tac|]. apply wt_nil.
- eapply wt_tau; [constructor; apply add_zeros_lts; term_tac|]. simpl.
  fold unreliableW. eapply wt_tau.
  + setoid_rewrite <- (add_data_comm "data" n M).
    apply lts_fw_com, add_zeros_lts, lts_choiceR. constructor.
  + apply wt_tau with (add_zeros z (! "work" ∥ unreliableW) ▷ add_data n M).
    * apply lts_fw_p, add_zeros_lts, lts_choiceL. constructor.
    * setoid_rewrite add_work_comm.
      induction z.
      -- apply wt_par_fw_l. apply (IHn 0).
      -- do 2 rewrite add_zeroes_comm. apply wt_par_fw_l, IHz.
Qed.

Lemma reliableW_consume_data n M :
  (add_work n reliableW ▷ ({[+ "data"+]} ⊎ M))
    ⟹ (add_work n (! "work" ∥ reliableW) ▷ M).
Proof.
  eapply wt_tau.
  - constructor. apply add_work_inversion. constructor.
  - simpl. fold reliableW. eapply wt_tau; [|apply wt_nil].
    simpl. apply (lts_fw_com M).
    apply add_work_inversion. apply lts_choiceR. constructor.
Qed.

Lemma reliableW_stable_work : reliableW ↛[ActIn "work"].
Proof. now vm_compute. Qed.


Lemma add_work_zero x x0 p :
  add_work (x + x0) p ≡* add_work x0 (𝟘 ∥ add_work x p).
Proof.
replace (x + x0) with (x0 + x) by lia.
rewrite add_work_plus. apply Proper_add_work. trivial.
symmetry. eapply t_trans.
- eapply t_step, cgr_par_com.
- eapply t_step, cgr_par_nil.
Qed.

Require Import Must.

Axiom FF : False.
Ltac cheat := exfalso; apply FF.

Example unreliable_reliable :
 unreliableW ⊑ reliableW.
Proof. 
apply soundness, alt_set_singleton_iff, eqx.
(* generalisation *)
enough (Ht : forall n z (M :  mb name) X,
  {[add_zeros z unreliableW ▷ add_data n M]} ∪ X ⩽ add_work n reliableW ▷ M). {
  replace ({[unreliableW ▷ (∅ : mb name)]}) with
          ({[unreliableW ▷ add_data 0 ∅ ]} ∪ ∅ : gset (proc * mb name))
          by (simpl; set_solver).
  apply (Ht 0 0 ∅ ∅).
  }
cofix hco. intros n z M X.
assert(Hrs := reliableW_stable_work).
constructor.
(* A. stable by τ *)
- intros q Hq. lts_inversion; add_tac; lts_inversion.
  simpl. fold reliableW. constructor.
  (* A' : stable by τ *)
  + intros q Hq. lts_inversion; add_tac; repeat lts_inversion.
    * (* → add_work n (! "end") ▷ M *)
      apply h2 with (add_zeros z (add_work n (! "end")));
      [by apply add_zeros_cgr|].
      apply co_preserved_by_wt_nil with (add_zeros z unreliableW ▷ add_data n M);
      [|refine (coin_union_l _ _ _ (coin_refl))].
      apply unreliable_add_work_add_data_terminate.
    * (* Loop back on coinduction hypothesis, with one more !"work" *)
      apply (hco (S n)).
  + (* B' : weak transitions outputs *)
    clear hco. intros Ht Hs.
    contradict Hs. apply lts_stable_spec2.
    exists (add_work n (!"end") ▷ M). constructor. apply add_work_inversion.
    term_tac.
  + (* C' : Weak termination sets *)
    intros μ q' ps' Hμ1 Hμ2 Hwt. lts_inversion.
    * add_tac.
      -- (* output "work" *)
        eapply h2 with
          (𝟘 ∥ add_work (x + x0)
                        (τ⋅ ! "end" ⊕ ("data" ? (! "work" ∥ reliableW)))).
       { replace (x + x0) with (x0 + x) by lia. 
         rewrite add_work_par_comm, add_work_plus. reflexivity. }
        apply co_preserved_by_wt_nil with (𝟘 ∥ add_work (x + x0) reliableW ▷ M).
        ++ eapply wt_tau; [|apply wt_nil].
           constructor. constructor. apply add_work_inversion; term_tac.
        ++ assert(Hin : (add_zeros (S z) unreliableW ▷ add_data (x + x0) M) ∈ ps').
          {
            clear hco. (* needed to avoid set_tac to use hco *)
            eapply Hwt with (p := add_zeros z unreliableW ▷ add_data (S (x + x0)) M)
            ; [ set_tac|].
            simpl. rewrite <- add_data_comm.
            eapply wt_tau with
              (add_zeros z (τ⋅ ! "end" ⊕
                           ("data" ? (τ⋅ (! "work" ∥ unreliableW) ⊕
                                      τ⋅ ! "bye")))
               ▷ {[+ "data" +]} ⊎ add_data (x + x0) M);
              [apply lts_fw_p; apply add_zeros_lts; constructor|].
            eapply wt_tau with (add_zeros z (τ⋅ (! "work" ∥ unreliableW) ⊕ τ⋅ ! "bye")
                                ▷ add_data (x + x0) M);
            [apply lts_fw_com, add_zeros_lts, lts_choiceR, lts_input|].
            eapply wt_tau with (add_zeros z (! "work" ∥ unreliableW), add_data (x + x0) M);
            [eapply lts_fw_p; apply add_zeros_lts; do 2 constructor|].
            eapply wt_act; [|apply wt_nil].
            apply lts_fw_p, add_zeros_lts. do 2 constructor.
          }
          apply union_difference_singleton_L in Hin. rewrite Hin.
          apply h2 with (add_work (x + x0) reliableW); [|apply hco].
          symmetry. apply cgr_par_nil_l.
      -- lts_inversion; lts_inversion.
         (* input "data" *)
         eapply co_preserved_by_wt_nil with (add_work n reliableW ▷ ({["data"]} ⊎ M)).
         2 : { eapply hco; eauto. constructor. }
         apply reliableW_consume_data.
    * apply co_preserved_by_wt_nil with (add_work n reliableW ▷ m).
     -- eapply wt_tau; [|apply wt_nil].
        constructor. eapply add_work_inversion. constructor.
     -- assert(Hin : (add_zeros z  unreliableW ▷ add_data n m) ∈ ps'). {
        clear hco. (* needed to avoid set_tac to use hco *)
        eapply Hwt with (p := add_zeros z unreliableW
                         ▷ add_data n ({[+ a +]} ⊎ m)); [ set_tac|].
        rewrite <- add_data_comm. eapply wt_act;
        [apply lts_fw_out_mb| apply wt_nil].
        }
        apply union_difference_singleton_L in Hin. rewrite Hin.
        apply hco.
    * apply co_preserved_by_wt_nil with (add_work n reliableW ▷ {[+ a +]} ⊎ M).
     -- eapply wt_tau; [|apply wt_nil].
        constructor. eapply add_work_inversion. constructor.
     -- assert(Hin : (add_zeros z unreliableW ▷ add_data n ({[+ a +]} ⊎ M)) ∈ ps'). {
        clear hco. (* needed to avoid set_tac to use hco *)
        eapply Hwt with (p := add_zeros z unreliableW ▷ add_data n M); [ set_tac|].
        rewrite <- add_data_comm. eapply wt_act;
        [apply lts_fw_inp_mb|apply wt_nil].
        }
        apply union_difference_singleton_L in Hin. rewrite Hin.
        apply hco.
  + clear hco. intros _. clear X.
    apply terminate_preserved_by_lts_tau with (add_work n reliableW ▷ M).
    * apply add_work_reliableW_terminate.
    * constructor. apply add_work_inversion. term_tac.
(* B. Weak transitions to stable states preserve output inclusion *)
- clear hco. intros Ht Hs.
  destruct Hs as [Hs _]. simpl in Hs.
  (* Easy, the right-hand side is stable. *)
  assert (Htau : (add_work n reliableW) ⟶
          (add_work n (τ⋅ ! "end" ⊕ ("data" ? (! "work" ∥ reliableW))))).
  { apply add_work_inversion. constructor. }
  contradict Hs. unfold proc_stable. apply lts_set_spec1 in Htau.
  intro Heq; rewrite Heq in Htau. now apply elem_of_empty in Htau.
(* C. Weak termination sets *)
- intros μ q' ps' Hμ1 Hμ2 Hwt. inversion Hμ2; subst.
  + destruct n as [|n]; [clear hco; lts_inversion|].
    add_tac; [| clear hco; lts_inversion]. clear Hμ2.
    assert(Hin : (add_zeros (S z) unreliableW ▷ add_data (x0 + x) M) ∈ ps'). {
      clear hco. (* needed to avoid set_tac to use hco *)
      apply Hwt with (p := add_zeros z unreliableW ▷ add_data (S (x + x0)) M);
      [ simpl; set_solver|].
      apply wt_tau with
        (add_zeros z (τ⋅ ! "end" ⊕
        ("data" ? (τ⋅ (! "work" ∥ unreliableW) ⊕ τ⋅ ! "bye")))
         ▷ add_data (S (x + x0)) M); [apply lts_fw_p, add_zeros_lts; term_tac|].
      setoid_rewrite <- add_data_comm.
      apply wt_tau with (add_zeros z (τ⋅(! "work" ∥ unreliableW) ⊕ τ⋅! "bye")
                         ▷ add_data (x + x0) M);
      [apply lts_fw_com, add_zeros_lts, lts_choiceR; constructor|].
      eapply wt_tau with (add_zeros z (! "work" ∥ unreliableW) ▷ add_data (x + x0) M);
      [apply lts_fw_p, add_zeros_lts, lts_choiceL; constructor
      |eapply wt_act; [|apply wt_nil]].
      simpl. rewrite Nat.add_comm. apply lts_fw_p, add_zeros_lts. term_tac.
    }
    apply union_difference_singleton_L in Hin. rewrite Hin.
    apply h2 with (add_work (x0 + x) reliableW); [|apply (hco (x0 + x) (S z))].
    clear hco. (* ici? *)
    rewrite add_work_par_comm, add_work_plus.
    symmetry. apply cgr_par_nil_l.
  + assert(Hin : (add_zeros z unreliableW ▷ add_data n m) ∈ ps'). {
      clear hco. (* needed to avoid set_tac to use hco *)
      eapply Hwt with (p := add_zeros z unreliableW ▷ add_data n ({[+ a +]} ⊎ m))
      ; [ set_tac|].
      eapply wt_act; [| apply wt_nil].
      replace (add_data n ({[+ a +]} ⊎ m)) with ({[+ a +]} ⊎ (add_data n m));
      [term_tac|]. apply add_data_comm.
    }
    apply union_difference_singleton_L in Hin. rewrite Hin.
    apply hco.
  + assert(Hin : (add_zeros z unreliableW ▷ add_data n ({[+a+]} ⊎ M)) ∈ ps'). {
      clear hco.
      eapply Hwt with (p := add_zeros z unreliableW ▷ add_data n M); [ set_tac|].
      eapply wt_act.
      apply lts_fw_inp_mb.
      replace  ({[+ a +]} ⊎ (add_data n M)) with (add_data n ({[+ a +]} ⊎ M));
      [term_tac|]. now rewrite add_data_comm.
    }
    apply union_difference_singleton_L in Hin. rewrite Hin.
    apply hco.
(* D. Termination on the left implies termination on the right *)
- intros. apply add_work_reliableW_terminate.
Qed.

End Example_2_1.
