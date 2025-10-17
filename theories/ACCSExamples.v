From Must Require Import ACCSInstance TransitionSystems Coin_tower Termination
                         Must Completeness Soundness Equivalence.
From stdpp Require Import strings sets gmap base gmultiset.
From Coq Require Import Relations.
From Coq Require Import Program.Equality.
From Must Require Import Must.
From Coinduction Require Import all.



Ltac lts_inversion := Termination.lts_inversion lts; try discriminate.
Ltac step_tac := Termination.step_tac lts; simpl.
Ltac term_tac := repeat step_tac.


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


Derive Inversion_clear lts_inv with (forall p a q, lts p a q) Sort Prop.
Derive Inversion_clear lts_step_inv with (forall p a q, lts_fw_step p a q)
  Sort Prop.

Hint Constructors lts_fw_step : lts.
Hint Constructors lts : lts.
Hint Unfold lts_step : lts.
Hint Extern 0 => simpl : lts.


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


Example q_terminate : forall M, (!"a" ∥ (τ⋅ !"b" ⊕  τ⋅ !"c") ▷ M) ⤓.
Proof. intro M. term_tac. Qed.

Lemma choice_copre_l (p q : proc) :
  forall (PRE : Chain (copre_m (LtsP := MbLts))) (M : mb name),
    elem PRE {[τ⋅ p ⊕ τ⋅ q ▷ M]} (p ▷ M).
Proof.
intros PRE M. eapply c_tau_.
- change (copre_ ?a ?b ?c) with (copre_m a b c); apply coin_refl.
- constructor. apply lts_choiceL. constructor.
Qed.

Lemma choice_copre_r p q:
  forall (PRE : Chain (copre_m (LtsP := MbLts))) (M : mb name),
    elem PRE {[τ⋅ p ⊕ τ⋅ q ▷ M]} (q ▷ M).
Proof.
intros PRE M. eapply c_tau_.
- change (copre_ ?a ?b ?c) with (copre_m a b c). apply coin_refl.
- constructor. apply lts_choiceR. constructor.
Qed.

Lemma choice_copre_rev (p q : proc) :
  forall (PRE : Chain (copre_m (LtsP := MbLts))) M,
    elem PRE ({[ (p ▷ M); (q ▷ M) ]}) (τ⋅ p ⊕ τ⋅ q ▷ M).
Proof.
  intro PRE; apply tower; clear PRE; [ intros P HP ???; eapply HP; eauto | ].
  intros PRE CIH M; split.
- intros (q', M') l.
  inversion_clear l.
  + repeat lts_inversion; apply coin_elem_of; set_tac.
  + repeat lts_inversion.
- intros Ht Hs.
  exfalso. eapply (lts_stable_spec2 (τ⋅ p ⊕ τ⋅ q ▷ M)).
  eexists. eapply lts_fw_p, lts_choiceL, lts_tau. assumption.
- intros μ q' ps' H0 Hμ Hw. inversion Hμ; subst.
  + repeat lts_inversion.
  + rewrite (union_difference_L {[p ▷ m; q ▷ m ]} ps');
    [apply coin_union_l, CIH|].
    intros p' mem%elem_of_union.
    destruct mem as [hl%elem_of_singleton | hr%elem_of_singleton]; subst.
    * apply Hw with (p ▷ {[+ a +]} ⊎ m). set_tac.
      apply lts_to_wt. term_tac.
    * apply Hw with (q ▷ {[+ a +]} ⊎ m). set_tac.
      apply lts_to_wt. term_tac.
  + rewrite (union_difference_L {[p ▷ {[+ a +]} ⊎ M; q ▷ {[+ a +]} ⊎ M]} ps');
    [apply coin_union_l, CIH|].
    intros p' mem%elem_of_union.
    destruct mem as [hl%elem_of_singleton | hr%elem_of_singleton]; subst.
    * apply Hw with (p ▷ M). set_tac. apply lts_to_wt. term_tac.
    * eapply Hw with (q ▷ M). set_tac. apply lts_to_wt. term_tac.
- intros Ht. constructor. intros (q', M') l.
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
| gpr_choice g1 g2 => gpr_choice g1 g2
  (* We can't can't simplify under + yet *)
| gp => gp
end.

(* Defining mutual induction principle for processes and guards *)
Scheme proc_gproc_ind := Induction for proc Sort Prop
  with gproc_proc_ind := Induction for gproc Sort Prop.

Lemma proc_absorb_nil_cgr p : eq_rel p (proc_absorb_nil p).
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
Qed.

Lemma cgr_par_nil_l p : (𝟘 ∥ p) ⋍ p.
Proof.
eapply t_trans.
- eapply t_step, cgr_par_com.
- eapply t_step, cgr_par_nil.
Qed.

(* TODO : should be in ACCS *)
Local Instance Proper_par : Proper ((eq_rel) ==> (eq_rel) ==> (eq_rel)) (fun x y => x ∥ y).
Proof.
intros p p' Hp q q' Hq. 
eapply t_trans.
- apply cgr_par_right, Hq.
- apply cgr_par_left, Hp.
Defined.

Global Instance Reflexive_cgr : Reflexive cgr.
Proof. intro x. apply t_step, cgr_refl. Defined.

Example code_hoisting_outputs : forall (M : mb name),
 {[ τ⋅ (!"a" ∥ !"b") ⊕ τ⋅ (!"a" ∥ !"c") ▷ M ]} ⩽ !"a" ∥ (τ⋅ !"b" ⊕ τ⋅ !"c") ▷ M.
Proof.
unfold copre. coinduction PRE CIH.
intros M. split.
- intros q l. repeat lts_inversion.
  + apply choice_copre_l.
  + apply choice_copre_r.
- intros. exfalso.
  eapply (lts_stable_spec2 (!"a" ∥ (τ⋅ !"b" ⊕ τ⋅ !"c") ▷ M)); eauto.
  exists (!"a" ∥ !"b" ▷ M). eapply lts_fw_p, lts_parR, lts_choiceL, lts_tau.
- intros μ q' ps' H0 Hμ Hw. inversion Hμ; subst.
  + repeat lts_inversion.
    (* Here we can simplify modulo congruence. Replaces the infamous h2 *)
    setoid_rewrite cgr_par_nil_l; simpl.
    (* TODO: handling + should make this work in 1 step *)
    setoid_replace ((τ⋅ ! "b" ⊕ τ⋅ ! "c")▷ M)
              with ((τ⋅ (!"b" ∥ pr_nil) ⊕ τ⋅ (!"c" ∥ pr_nil))▷ M).
    2 : { apply fw_eq_id_mb; trivial. econstructor 2; repeat constructor. }
    setoid_replace ((τ⋅ (!"b" ∥ pr_nil) ⊕ τ⋅ (!"c" ∥ pr_nil))▷ M)
              with ((τ⋅ (pr_nil ∥ !"b") ⊕ τ⋅ (pr_nil ∥ !"c"))▷ M).
    2 : { apply fw_eq_id_mb; trivial. constructor.
          constructor; constructor; apply cgr_par_com. }
    assert (Hi : {[ (pr_nil ∥ !"b" ▷ M); (pr_nil ∥ !"c" ▷ M) ]} ⊆ ps'). {
      intros x mem%elem_of_union.
       destruct mem as [hl%elem_of_singleton | hr%elem_of_singleton]; subst.
       - eapply Hw.
        + now eapply elem_of_singleton.
        + eapply wt_tau. apply lts_fw_p. apply lts_choiceL, lts_tau.
          apply lts_to_wt. term_tac.
       - eapply Hw.
        + now eapply elem_of_singleton.
        + eapply wt_tau. eapply lts_fw_p. eapply lts_choiceR, lts_tau.
          apply lts_to_wt. term_tac.
     }
     eapply union_difference_L in Hi.
     rewrite Hi. refine (coin_union_l _ _ _ _). (* TODO: why apply doesn't work here? *)
     apply choice_copre_rev.
  + assert (Hin : τ⋅ (!"a" ∥ !"b") ⊕ τ⋅ (!"a" ∥ !"c") ▷ m ∈ ps').
    * eapply Hw; [now eapply elem_of_singleton|]. apply lts_to_wt. term_tac.
    * eapply union_difference_singleton_L in Hin.
      rewrite Hin. eapply coin_union_l, CIH.
  + assert (Hin : τ⋅ (!"a" ∥ !"b") ⊕ τ⋅ (!"a" ∥ !"c") ▷ {[+ a +]} ⊎ M ∈ ps').
    * eapply Hw.
      -- now eapply elem_of_singleton.
      -- apply lts_to_wt. term_tac.
    * eapply union_difference_singleton_L in Hin.
      rewrite Hin. eapply coin_union_l, CIH.
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
unfold copre. coinduction PRE hco. intros p.
constructor.
- intros q Hq. apply hco.
- intros Ht _. exfalso. apply omega_diverges, (Ht omega). set_tac.
- intros a b c Ht _. exfalso.
  eapply omega_diverges, cnv_terminate, (Ht omega). set_tac.
- intros Ht. exfalso. apply omega_diverges, (Ht omega). set_tac.
Qed.

End Omega.


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


Section Example_2_1.
(** A nontrivial example with recursion *)

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
    * apply fw_eq_id_mb; trivial. etransitivity.
      -- constructor. apply cgr_par_nil_rev.
      -- constructor. apply cgr_par_com.
Qed.

Section AddWork.

(* Adds n outputs "work" in parallel *)
Fixpoint add_work n p := match n with
| O => p
| S n => add_work n (!"work" ∥ p)
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
    ((exists n1 n2, S (n1 + n2) = n /\
        q = add_work n2 (𝟘 ∥ add_work n1 p) /\ μ = ActExt (ActOut "work")) \/
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

Lemma add_work_plus x x0 p :
  add_work (x + x0) p = add_work x (add_work x0 p).
Proof.
revert x0 p. induction x as [|x]; intros x0 p; trivial.
simpl. now rewrite IHx, <- add_work_comm.
Qed.

Local Instance Proper_add_work : Proper (eq ==> cgr ==> cgr) add_work.
Proof.
intros n n' Hn. subst n'. induction n; intros p p' Hp; trivial.
do 2 rewrite add_work_comm. apply Proper_par; auto with *.
Defined.

End AddWork.

(* Adds n "data" in the mailbox *)
Fixpoint add_data n m : mb name := 
match n with
| O => m
| S n => add_data n ({[+ "data" +]} ⊎ m)
end.

Lemma add_data_comm a n m :
 {[+ a +]} ⊎ add_data n m = add_data n ({[+ a +]} ⊎ m).
Proof.
revert m. induction n; intros m; simpl; [|rewrite IHn; f_equal]; multiset_solver.
Qed.


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

(*
Lemma wt_par_l p q r s : p ⟹[s] q -> (r ∥ p) ⟹[s] (r ∥ q).
Proof.
intro Ht. induction Ht.
- apply wt_nil.
- apply wt_tau with (r ∥ q); trivial.
  apply lts_parR; trivial.
- apply wt_act with (r ∥ q); trivial.
  apply lts_parR; trivial.
Qed.
*)


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


Lemma add_work_par_comm x p1 p2 :
  add_work x (p1 ∥ p2) ≡* p1 ∥ add_work x p2.
Proof.
revert p1 p2. induction x as [|x]; intros p1 p2; simpl; trivial.
repeat rewrite IHx.
eapply t_trans; [ apply t_step; symmetry; apply cgr_par_ass|].
eapply t_trans; [|apply t_step, cgr_par_ass].
apply t_step. apply cgr_par.
- apply cgr_par_com.
- reflexivity.
Qed.

(* After n unfolding and n "data" received, n "work" have been produced *)
Lemma unreliable_add_work_add_data_end n M :
  (unreliableW ▷ add_data n M) ⟹ (add_work n (! "end") ▷ M).
Proof.
revert M. induction n as [|n]; intros M; simpl.
- eapply wt_tau; [constructor; term_tac|].
  eapply wt_tau; [constructor; term_tac|]. apply wt_nil.
- eapply wt_tau; [constructor; term_tac|]. simpl.
  fold unreliableW. eapply wt_tau.
  + setoid_rewrite <- (add_data_comm "data" n M).
    apply lts_fw_com, lts_choiceR. constructor.
  + apply wt_tau with (! "work" ∥ unreliableW ▷ add_data n M).
    * apply lts_fw_p, lts_choiceL. constructor.
    * setoid_rewrite add_work_comm. apply wt_par_fw_l, IHn.
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
  add_work (x + x0) p ⋍ add_work x0 (𝟘 ∥ add_work x p).
Proof.
replace (x + x0) with (x0 + x) by lia.
rewrite add_work_plus. apply Proper_add_work. trivial.
symmetry. eapply t_trans.
- eapply t_step, cgr_par_com.
- eapply t_step, cgr_par_nil.
Qed.

Lemma cnv_pr_nil M s: 𝟘 ▷ M ⇓ s.
Proof.
apply nil_cnv. intros. destruct α as [[ | ]| ]; now compute.
Qed.


Ltac wt_inversion:=
match goal with
| H : wt ?p ?a ?q |- _ =>
  inversion H; subst; clear H; repeat lts_inversion; simpl in *
end;
try match goal with
| H : ?a ⊎ ?b = ∅ |- _ => contradict H; apply Lift.neq_multi_nil
end;
try discriminate; try tauto; auto with *.

Lemma cnv_output a M s : (! a) ▷ M ⇓ s.
Proof.
revert M.
induction s; intro M; constructor.
- constructor. intros. repeat lts_inversion.
- constructor. intros. repeat lts_inversion.
- intros. repeat wt_inversion. apply cnv_pr_nil.
Qed.

(* Termination is preserved by congruence *)
Lemma cgr_terminate (p q : proc) : p ⤓ -> p ≡* q -> q ⤓.
Proof.
intro Ht. revert q; induction Ht; intros q Heq.
constructor. intros q' Hq'.
destruct (harmony_cgr p q' τ) as (r & Heq' & Hr).
- exists q; split; trivial.
- eapply H0; eauto.
Qed.

Lemma cnv_fw_inp p a M s : cnv (p ▷ M) (ActIn a :: s) -> cnv (p ▷ {[+ a +]} ⊎ M) s.
Proof.
intro Hc. dependent destruction Hc.
apply H0. eapply wt_act; [|apply wt_nil]. constructor.
Qed.

(* Transitions are preserved when extending the mailbox *)
Lemma lts_fw_frame_rule p q M M' M'' α : lts_step (p ▷ M) α (q ▷ M') ->
  lts_step (p ▷ M'' ⊎ M) α (q ▷ M'' ⊎ M').
Proof.
intro Hl. lts_inversion.
- now constructor.
- replace (M'' ⊎ ({[+ a +]} ⊎ M')) with ({[+ a +]} ⊎ (M'' ⊎ M')) by multiset_solver.
  constructor.
- replace (M'' ⊎ ({[+ a +]} ⊎ M)) with ({[+ a +]} ⊎ (M'' ⊎ M)) by multiset_solver.
  constructor.
- replace (M'' ⊎ ({[+ a +]} ⊎ M')) with ({[+ a +]} ⊎ (M'' ⊎ M')) by multiset_solver.
  now constructor.
Qed.

(* weak transitions are preserved when extending the mailbox *)
Lemma wt_mb_frame_rule p q M M' M'' s : wt (p ▷ M) s (q ▷ M') ->
  wt (p ▷ M'' ⊎ M) s (q ▷ M'' ⊎ M').
Proof.
intro Hwt. dependent induction Hwt generalizing p q M M'.
- apply wt_nil.
- destruct q0 as (q0 & M0).
  apply wt_tau with (q0 ▷ M'' ⊎ M0).
  + now apply lts_fw_frame_rule.
  + apply IHHwt; trivial.
- destruct q0 as (q0 & M0).
  apply wt_act with (q0 ▷ M'' ⊎ M0).
  + now apply lts_fw_frame_rule.
  + apply IHHwt; trivial.
Qed.


(* Convergence on all traces is preserved by transitions *)
Lemma cnv_all_preserved_by_lts p {α q} : lts p α q ->
  (forall s, cnv p s) -> (forall s, cnv q s).
Proof.
intros Hpq Hs s. destruct α as [μ|].
- specialize (Hs (μ :: s)).
  dependent destruction Hs. apply H0. now apply lts_to_wt.
- apply cnv_preserved_by_wt_nil with p; trivial.
  eapply wt_tau; [exact Hpq| apply wt_nil].
Qed.

(* convergence on all trace lifts to forwarders *)
Lemma cnv_mb p M : (forall s, cnv p s) -> (forall s, cnv (p ▷ M) s).
Proof.
intros Hp s. revert M. induction s; intro M.
- constructor.
  assert(Ht : terminate p) by now destruct (Hp []).
  revert p Hp Ht. remember (size M) as n. symmetry in Heqn; revert M Heqn.
  (* double induction on the size of M and the termination of p *)
  induction n; intros M Heqn p Hp Ht.
  + apply gmultiset_size_empty_inv in Heqn. subst.
    apply Lift.conv. now destruct (Hp []).
  + revert M Heqn IHn; induction Ht as [p Ht Hstep]; intros X IHM.
    constructor. intros q Hq. lts_inversion.
    * apply Hstep; trivial.
      apply cnv_all_preserved_by_lts with (p := p) (α := τ); trivial.
    * assert (Hq0 := cnv_all_preserved_by_lts p H0 Hp).
      apply IHn.
      -- setoid_rewrite gmultiset_size_disj_union in IHM.
         setoid_rewrite gmultiset_size_singleton in IHM. now inversion IHM.
      -- exact Hq0.
      -- apply cnv_terminate with []; trivial.
- constructor.
  + induction M as [|b M] using gmultiset_ind.
    * apply Lift.conv. now destruct (Hp []).
    * constructor. intros q Hq. lts_inversion.
      -- eapply terminate_preserved_by_lts_tau with (p ▷ {[+ b +]} ⊎ M).
        ++ eapply cnv_terminate, IHs.
        ++ now constructor.
      -- apply cnv_terminate with (s := s).
         eapply cnv_preserved_by_lts_tau with (p ▷ {[+ b +]} ⊎ M).
        ++ apply IHs.
        ++ setoid_rewrite <- H1. now constructor.
  + intros q Hq. destruct a as [i | o].
    * destruct (wt_decomp_one Hq) as (p' & q' & Hp' & Hlt & Hq').
      lts_inversion.
      -- eapply cnv_preserved_by_wt_nil; [|exact Hq'].
         eapply cnv_preserved_by_wt_nil with (p0 ▷ {[+ i +]} ⊎ m).
        ++ eapply cnv_preserved_by_wt_nil with (p ▷ {[+ i +]} ⊎ M).
          ** apply IHs.
          ** now apply wt_mb_frame_rule.
        ++ eapply wt_tau; [| apply wt_nil]. now constructor.
      -- eapply cnv_preserved_by_wt_nil; [|exact Hq'].
         eapply cnv_preserved_by_wt_nil with (p ▷ {[+ i +]} ⊎ M).
        ++ apply IHs.
        ++ now apply wt_mb_frame_rule.
    * eapply cnv_preserved_by_wt_output; eauto.
Qed.


Example unreliable_reliable :
 unreliableW ⊑ reliableW.
Proof.
apply soundness, alt_set_singleton_iff, eqx.
(* The trick is to generalise to all terms that are weakly reachable from the
  right-hand-side AND followed by a recursive call *)
enough (Ht : forall n (M :  mb name) q0,
  q0 ∈ [add_work n reliableW; add_work n (τ⋅ ! "end" ⊕ ("data" ? (! "work" ∥ reliableW)))] ->
  {[unreliableW ▷ add_data n M]} ⩽ q0 ▷ M). {
  replace ({[unreliableW ▷ (∅ : mb name)]}) with
          ({[unreliableW ▷ add_data 0 ∅ ]} : gset (proc * mb name))
          by (simpl; set_solver).
  apply (Ht 0 ∅). constructor.
  }
unfold copre. coinduction PRE hco. intros n M q0 Hq0.
assert(Hrs := reliableW_stable_work).
constructor.
(* A. stable by τ *)
- intros q Hq.
  apply elem_of_cons in Hq0 as [Hq0 | Hq0%elem_of_list_singleton]; subst.
  (* for free, since we generalised the induction hypothesis with the next step *)
  { lts_inversion; add_tac; lts_inversion. simpl. apply hco. right. left. }
  lts_inversion; add_tac; repeat lts_inversion; simpl;
  (* for free, since we generalised the induction hypothesis with the next step *)
  [| apply (hco (S n)); left].
  (* → add_work n (! "end") ▷ M *)
  (* no need to put this one in the induction hypothesis as it is not followed
      by a recursive call *)
   eapply (gfp_chain PRE), co_preserved_by_wt_nil; [|refine coin_refl].
   apply unreliable_add_work_add_data_end.
(* B. Weak transitions to stable states preserve output inclusion *)
- intros Ht Hs.
  destruct Hs as [Hs _]. simpl in Hs.
  (* Easy, the right-hand side is stable. *)
  contradict Hs. unfold proc_stable.
  apply elem_of_cons in Hq0 as [Hq0 | Hq0%elem_of_list_singleton]; subst.
  + apply non_empty_inhabited_L with
      (add_work n (τ⋅ ! "end" ⊕ ("data" ? (! "work" ∥ reliableW)))).
    apply lts_set_spec1. apply add_work_inversion. constructor.
  + apply non_empty_inhabited_L with (add_work n (! "end")).
    apply lts_set_spec1. apply add_work_inversion. do 2 constructor.
(* C. Weak termination sets *)
- intros μ q' ps' Hμ1 Hμ2 Hwt.
  apply elem_of_cons in Hq0 as [Hq0 | Hq0%elem_of_list_singleton]; subst.
  + inversion Hμ2; subst.
    * (* ! "work" *)
      add_tac; [| lts_inversion]. clear Hμ2.
      rewrite <- add_work_zero.
      assert(Hin : (pr_nil ∥ unreliableW ▷ add_data (x + x0) M) ∈ ps'). {
        apply Hwt with (p := unreliableW ▷ add_data (S (x + x0)) M);
        [ simpl; set_solver|].
        apply wt_tau with
          ((τ⋅ ! "end" ⊕
          ("data" ? (τ⋅ (! "work" ∥ unreliableW) ⊕ τ⋅ ! "bye")))
           ▷ add_data (S (x + x0)) M); [apply lts_fw_p; term_tac|].
        setoid_rewrite <- add_data_comm.
        apply wt_tau with ((τ⋅(! "work" ∥ unreliableW) ⊕ τ⋅! "bye")
                           ▷ add_data (x + x0) M);
        [apply lts_fw_com, lts_choiceR; constructor|].
        eapply wt_tau with ((! "work" ∥ unreliableW) ▷ add_data (x + x0) M);
        [apply lts_fw_p, lts_choiceL; constructor
        |apply lts_to_wt].
        apply lts_fw_p. term_tac.
      }
      apply (coin_choose Hin).
      rewrite cgr_par_nil_l.
      apply hco. left.
    * (* output from the mailbox *)
      assert(Hin : (unreliableW ▷ add_data n m) ∈ ps'). {
        eapply Hwt with (p := unreliableW ▷ add_data n ({[+ a +]} ⊎ m));[set_tac|].
        apply lts_to_wt. rewrite <- add_data_comm. term_tac.
      }
      apply (coin_choose Hin). apply hco. left.
    * (* input in the mailbox *)
      assert(Hin : (unreliableW ▷ add_data n ({[+a+]} ⊎ M)) ∈ ps'). {
        eapply Hwt with (p := unreliableW ▷ add_data n M); [ set_tac|].
        apply lts_to_wt. rewrite <- add_data_comm. term_tac.
      }
      apply (coin_choose Hin).
      apply hco. left.
  (* TODO: there seeems to be some redundancy with the previous bullet. *)
  + inversion Hμ2; subst; [add_tac| |].
    * (* ! "work" *)
      rewrite <- add_work_zero.
      assert(Hin : (pr_nil ∥ unreliableW ▷ add_data (x + x0) M) ∈ ps'). {
        apply Hwt with (p := unreliableW ▷ add_data (S (x + x0)) M);
        [ simpl; set_solver|].
        apply wt_tau with
          ((τ⋅ ! "end" ⊕
          ("data" ? (τ⋅ (! "work" ∥ unreliableW) ⊕ τ⋅ ! "bye")))
           ▷ add_data (S (x + x0)) M); [apply lts_fw_p; term_tac|].
        setoid_rewrite <- add_data_comm.
        apply wt_tau with ((τ⋅(! "work" ∥ unreliableW) ⊕ τ⋅! "bye")
                           ▷ add_data (x + x0) M);
        [apply lts_fw_com, lts_choiceR; constructor|].
        eapply wt_tau with ((! "work" ∥ unreliableW) ▷ add_data (x + x0) M);
        [apply lts_fw_p, lts_choiceL; constructor
        |apply lts_to_wt]. rewrite Nat.add_comm. apply lts_fw_p, lts_parL. term_tac.
      }
      apply (coin_choose Hin). rewrite cgr_par_nil_l.
      apply (hco (x + x0) M). right. left.
    * (* ? "data" *)
      clear Hμ2. lts_inversion; lts_inversion.
      assert(Hin : (unreliableW ▷ add_data n ({[+"data"+]} ⊎ M)) ∈ ps'). {
        eapply Hwt with (p := unreliableW ▷ add_data n M); [ set_tac|].
        rewrite <- add_data_comm. apply lts_to_wt. term_tac.
      }
      apply (coin_choose Hin). apply (hco (S n)). left.
    * (* output from the mailbox *)
      assert(Hin : (unreliableW ▷ add_data n m) ∈ ps'). {
        eapply Hwt with (p := unreliableW ▷ add_data n ({[+ a +]} ⊎ m));[set_tac|].
        apply lts_to_wt. rewrite <- add_data_comm. term_tac.
      }
      apply (coin_choose Hin). apply hco. right. left.
    * (* input in the mailbox *)
      assert(Hin : (unreliableW ▷ add_data n ({[+a+]} ⊎ M)) ∈ ps'). {
        eapply Hwt with (p := unreliableW ▷ add_data n M); [ set_tac|].
        rewrite <- add_data_comm. apply lts_to_wt. term_tac.
      }
      apply (coin_choose Hin). apply hco. right. left.
(* D. Termination on the left implies termination on the right *)
- intros.
  apply elem_of_cons in Hq0 as [Hq0 | Hq0%elem_of_list_singleton]; subst.
  + apply add_work_reliableW_terminate.
  + constructor. intros q Hq. lts_inversion.
    * add_tac. repeat lts_inversion. apply add_work_end_terminate.
    * add_tac. repeat lts_inversion. apply (add_work_reliableW_terminate m (S n)).
Qed.


End Example_2_1.
