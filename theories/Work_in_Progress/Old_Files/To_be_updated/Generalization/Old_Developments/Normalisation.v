(*
   Copyright (c) 2024 Nomadic Labs
   Copyright (c) 2024 Paul Laforgue <paul.laforgue@nomadic-labs.com>
   Copyright (c) 2024 Léo Stefanesco <leo.stefanesco@mpi-sws.org>

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

From Stdlib.Program Require Import Wf Equality.
From Stdlib.Wellfounded Require Import Inverse_Image.

From stdpp Require Import base countable finite gmap list decidable gmultiset hlist.

From TestingTheory Require Import ActTau FiniteImageLTS 
    gLts Bisimulation Lts_FW Convergence Termination WeakTransitions Lts_OBA Subset_Act DefinitionAS Must.

Definition ntrace A `{ExtAction A} : Type := (gmultiset A) * list A * (gmultiset A).
(* Definition ntrace A `{ExtAction A} : Type := list (gmultiset A * gmultiset A * list A). *)
(* mi = m_co_nb, mo = m_nb , m_other (* NEW *)*)
(* Definition ntrace L `{Label L} : Type := list (gmultiset L * gmultiset L). *)

Fixpoint normalize_loop `{ExtAction A} (s : list A) (count_co_nb : gmultiset A) (l_bb : list A) (count_nb : gmultiset A) : ntrace A := 
match s with
  | [] => (count_co_nb , l_bb , count_nb)
  | μ :: s => if (decide(non_blocking μ)) then normalize_loop s count_co_nb l_bb ({[+ μ +]} ⊎ count_nb)
                                          else if (decide(exist_co_nba μ)) then normalize_loop s ({[+ μ +]} ⊎ count_co_nb) l_bb count_nb
                                                                           else normalize_loop s count_co_nb (l_bb++[μ]) count_nb
end.

Definition normalize `{ExtAction A} (s : trace A) : ntrace A := normalize_loop s ∅ [] ∅.

Definition linearize `{ExtAction A} (nt : ntrace A) : trace A :=
  match nt with
  | (M_co_nb , l , M_nb) => (elements M_co_nb) ++ l ++ (elements M_nb)
  end.

Definition linorm `{ExtAction A} s := linearize (normalize s).
(* Definition linorm `{Label L}  s := linearize (normalize s). *)

Notation "⟪ s ⟫" := (linearize (normalize s)).

(* Notation "⌈ nt ⌉" := (linearize nt). *)

(* Lemma norm_nil `{ExtAction A} s M boo : normalize s = [] -> s = [].
Proof.
  revert M boo.
  induction s
    as (s & Hlength) using
         (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
  destruct s.
  - eauto.
  - intros M boo eq. simpl in eq.
    destruct (decide(non_blocking a)) as [nb | b].
    + case_eq boo.
      * intros bb eq'; simpl. subst.
        destruct bb.
        --  inversion H2. rewrite decide_True in eq; eauto. now eapply norm_loop_nil in eq.
Qed. unfold normalize.  *)


(* Lemma norm_loop_nil `{ExtAction A} s M b_nb : M <> ∅ -> normalize_loop s M b_nb ≠ [].
Proof.
  revert M b_nb.
  induction s; eauto.
  + intros. simpl. simpl. rewrite decide_False; eauto.
  + intros. simpl. destruct (decide(non_blocking a)) as [nb | b].
    - destruct b_nb; [destruct b|].
      * eapply IHs. multiset_solver.
      * set_solver.
      * eapply IHs. multiset_solver. 
    - destruct (decide (exist_co_nba a)) as [co_nb | cob].
      * destruct b_nb; [destruct b0|].
        ++ multiset_solver.
        ++ eapply IHs. multiset_solver. 
        ++ eapply IHs. multiset_solver.
      * rewrite decide_False; eauto.
Qed. *)

Lemma norm_nil `{ExtAction A} : ⟪ [] ⟫ = [].
Proof.
  subst.
  simpl. eauto.
Qed.

Lemma norm_nil_rev `{ExtAction A} s : ⟪ s ⟫ = [] <-> s = [].
Proof.
  split.
  - dependent induction s.
    + simpl. eauto.
    + intro Hyp. exfalso.
      unfold normalize in Hyp. simpl in *.
      destruct (decide (non_blocking a)) as [nb | b].
      * simpl in *. admit.
      * destruct (decide (exist_co_nba a)).
        -- admit.
        -- admit.
  - intros; subst. simpl. eauto.
Admitted.

Lemma norm_singleton `{ExtAction A} μ : ⟪ [μ] ⟫ = [μ].
Proof.
  simpl. unfold normalize. simpl. destruct (decide (non_blocking μ)) as [nb | b].
  + simpl. admit.
  + destruct (decide (exist_co_nba μ)) as [co_nb | co_b].
    - simpl. admit.
    - simpl. eauto.
Admitted.

(* Lemma norm_non_blocking_blocking_step `{ExtAction A} η β s :
  non_blocking η -> blocking β -> normalize (η :: β :: s) = {[+ η +]} :: normalize (β :: s).
Proof.
  intros. unfold normalize. simpl. rewrite decide_True; eauto.
  rewrite decide_False; eauto.
  destruct (decide (exist_co_nba β)) as [co_nb | co_b].
  + rewrite decide_False; eauto. (* simpl. now rewrite gmultiset_disj_union_right_id. *)
  + rewrite decide_False; eauto. rewrite decide_False; eauto.
Qed. *)

(* Lemma norm_co_non_blocking_co_blocking_step `{ExtAction A} β β' s :
  exist_co_nba β ->  ¬ exist_co_nba β' -> normalize (β :: β' :: s) = {[+ β +]} :: normalize (β' :: s).
Proof.
  intros co_nb co_b. unfold normalize. simpl.
  assert (blocking β) as b.
  { destruct co_nb as (η & nb & duo). eapply dual_blocks in duo; eauto. }
  rewrite decide_False; eauto.
  rewrite decide_True; eauto.
  destruct (decide (non_blocking β')) as [nb' | b'].
  + eauto.
  + rewrite decide_False; eauto. rewrite decide_False; eauto.
    rewrite decide_False; eauto.
Qed. *)

(* Lemma norm_blocking_non_blocking_step `{ExtAction A} η β s :
  blocking β -> non_blocking η -> normalize (β :: η :: s) = {[+ β +]} :: normalize (η :: s).
Proof.
  intros. unfold normalize. simpl. rewrite decide_False; eauto.
  destruct (decide (exist_co_nba β)) as [co_nb | co_b].
  + rewrite decide_True; eauto.
    rewrite decide_True; eauto. (* simpl. now rewrite gmultiset_disj_union_right_id. *)
  + rewrite decide_True; eauto.
Qed. *)

(* Lemma norm_loop_blocking_co_non_blocking_step `{ExtAction A} β s : blocking β -> exist_co_nba β -> normalize_loop s {[+ β +]} (Some false) = normalize (β :: s).
Proof.
  revert β.
  dependent induction s; intros.
  + unfold normalize. simpl. rewrite decide_False;eauto.
    rewrite decide_False;eauto.
    rewrite decide_True;eauto.
  + unfold normalize. simpl. destruct (decide (non_blocking a)) as [nb | b].
    - rewrite decide_False;eauto.
      rewrite decide_True; eauto.
    - destruct (decide (exist_co_nba a)) as [co_nb | co_b].
      * rewrite decide_False;eauto.
        rewrite decide_True; eauto.
      * rewrite decide_False;eauto.
        rewrite decide_False;eauto.
        rewrite decide_True; eauto.
Qed. *)

Definition b_and_co_b `{ExtAction A} (β : A) : Prop := blocking β /\ ¬ exist_co_nba β.

(* Lemma norm_blocking_co_blocking_step_eq `{ExtAction A} β s : blocking β -> ¬ exist_co_nba β -> normalize (β :: s) = {[+ β +]} :: normalize s.
Proof.
  revert β. intros.
  dependent induction s; intros; unfold normalize; simpl.
  + rewrite decide_False;eauto.
    rewrite decide_False;eauto.
  + rewrite decide_False; eauto.
    rewrite decide_False; eauto.
Qed. *)

(* Lemma norm_loop_blocking_step' `{ExtAction A} s β :
  blocking β -> ¬ (exist_co_nba β) -> normalize (β :: s) = {[+ β +]} :: normalize s.
Proof.
  intros b co_b.
  unfold normalize. simpl. rewrite decide_False;eauto. rewrite decide_False;eauto.
Qed. *)

Lemma norm_non_blocking_step `{ExtAction A} η s :
  non_blocking η
  -> exists s'3 s1 s2 s3,
      ⟪ η :: s ⟫ = s1 ++ s2 ++ s3
      /\ Forall exist_co_nba s1
      /\ Forall b_and_co_b s2
      /\ Forall non_blocking s'3
      /\ s ≡ₚ s1 ++ s2 ++ s'3
      /\ η :: s'3 ≡ₚ s3
      /\ η ∈ s3.
Proof.
  revert η. induction s
    as (s & Hlength) using
         (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
  destruct s; intros η nb.
  + exists [], [], [], [η]. repeat split.
    * rewrite norm_singleton. simpl. eauto.
    * constructor;eauto.
    * eauto.
    * eauto.
    * eauto.
    * eauto.
    * set_solver.
  + destruct (decide (non_blocking a)) as [nb' | b'].
    * admit.
      (* exists (elements ({[+ a +]} ⊎ (list_to_set_disj s1))).
      exists ({[+ a +]} ⊎  M_nb). exists (a :: s1), s2. repeat split.
      - subst. admit. 
      - subst. eauto.
      - constructor;eauto.
      - subst. rewrite gmultiset_elements_disj_union. rewrite gmultiset_elements_singleton.
        simpl. eapply Permutation_skip. eauto.
      - simpl. lia. *)
    * destruct (decide (exist_co_nba a)) as [co_nb | co_b].
      (* - exists ∅, [], (a :: s). repeat split.
        ++ assert ({[+ η +]} ⊎ (∅ : gmultiset A) = {[+ η +]}) as eq by multiset_solver.
           rewrite eq. rewrite norm_non_blocking_blocking_step; eauto.
        ++ constructor.
        ++ rewrite gmultiset_elements_empty. reflexivity.
        ++ eauto.
      - exists ∅, [], (a :: s). repeat split.
        ++ assert ({[+ η +]} ⊎ (∅ : gmultiset A) = {[+ η +]}) as eq by multiset_solver.
           rewrite eq. f_equal. fold normalize. rewrite norm_non_blocking_blocking_step; eauto.
        ++ constructor.
        ++ rewrite gmultiset_elements_empty. reflexivity.
        ++ eauto. *)
Admitted.

Lemma norm_co_nba_step `{ExtAction A} μ s :
  exist_co_nba μ
  -> exists s'1 s1 s2 s3,
      ⟪ μ :: s ⟫ = s1 ++ s2 ++ s3
      /\ Forall exist_co_nba s'1
      /\ Forall b_and_co_b s2
      /\ Forall non_blocking s3
      /\ s ≡ₚ s'1 ++ s2 ++ s3
      /\ μ :: s'1 ≡ₚ s1
      /\ μ ∈ s1.
Proof.
  revert μ. induction s
    as (s & Hlength) using
         (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
  destruct s; intros μ co_nb.
  + exists [], [μ], [], []. repeat split.
    * rewrite norm_singleton. simpl. reflexivity.
    * eauto.
    * constructor.
    * eauto.
    * eauto.
    * eauto.
    * set_solver.
  + admit.
  (* destruct (decide (non_blocking a)) as [nb' | b'].
    * exists ∅, [], (a :: s). repeat split.
      - assert ({[+ β +]} ⊎ (∅ : gmultiset A) = {[+ β +]}) as eq by multiset_solver.
        rewrite eq. assert (blocking β) as b.
        { destruct co_nb as (β' & nb & duo). eapply dual_blocks in duo;eauto. }
        rewrite norm_blocking_non_blocking_step; eauto.
      - constructor.
      - rewrite gmultiset_elements_empty. reflexivity.
      - eauto.
    * destruct (decide (exist_co_nba a)) as [co_nb' | co_b'].
      - assert (∃ (M_co_nb : gmultiset A) (s1 : list A) (s2 : trace A),
            normalize (β :: s) = {[+ β +]} ⊎ M_co_nb :: normalize s2
            ∧ s = s1 ++ s2
              ∧ Forall exist_co_nba s1
                ∧ elements M_co_nb ≡ₚ s1 ∧ length s2 ≤ length s) as (M_co_nb & s1 & s2 & eq & eq_trace & all_co_nb & permut & subeq_length).
        { eapply Hlength; eauto. }
        exists ({[+ a +]} ⊎  M_co_nb). exists (a :: s1), s2. repeat split; subst.
        ++ admit.
        ++ eauto.
        ++ constructor; eauto.
        ++ rewrite gmultiset_elements_disj_union. rewrite gmultiset_elements_singleton.
           simpl. eapply Permutation_skip. eauto.
        ++ simpl. lia.
      - exists ∅, [], (a :: s). repeat split.
        ++ assert ({[+ β +]} ⊎ (∅ : gmultiset A) = {[+ β +]}) as eq by multiset_solver.
           rewrite eq. rewrite norm_co_non_blocking_co_blocking_step; eauto.
        ++ constructor.
        ++ rewrite gmultiset_elements_empty. reflexivity.
        ++ eauto. *)
Admitted.

Lemma norm_b_and_co_b_step `{ExtAction A} β s :
  b_and_co_b β
  -> exists s'2 s1 s2 s3,
      ⟪ β :: s ⟫ = s1 ++ s2 ++ s3
      /\ Forall exist_co_nba s1
      /\ Forall b_and_co_b s'2
      /\ Forall non_blocking s3
      /\ s ≡ₚ s1 ++ s'2 ++ s3
      /\ β :: s'2 = s2
      /\ β ∈ s2.
Proof.
  revert β. induction s
    as (s & Hlength) using
         (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
  destruct s; intros β bcb.
  + exists [], [], [β], []. repeat split.
    * rewrite norm_singleton. simpl. reflexivity.
    * constructor.
    * eauto.
    * constructor.
    * eauto.
    * set_solver.
  + admit.
  (* destruct (decide (non_blocking a)) as [nb' | b'].
    * exists ∅, [], (a :: s). repeat split.
      - assert ({[+ β +]} ⊎ (∅ : gmultiset A) = {[+ β +]}) as eq by multiset_solver.
        rewrite eq. assert (blocking β) as b.
        { destruct co_nb as (β' & nb & duo). eapply dual_blocks in duo;eauto. }
        rewrite norm_blocking_non_blocking_step; eauto.
      - constructor.
      - rewrite gmultiset_elements_empty. reflexivity.
      - eauto.
    * destruct (decide (exist_co_nba a)) as [co_nb' | co_b'].
      - assert (∃ (M_co_nb : gmultiset A) (s1 : list A) (s2 : trace A),
            normalize (β :: s) = {[+ β +]} ⊎ M_co_nb :: normalize s2
            ∧ s = s1 ++ s2
              ∧ Forall exist_co_nba s1
                ∧ elements M_co_nb ≡ₚ s1 ∧ length s2 ≤ length s) as (M_co_nb & s1 & s2 & eq & eq_trace & all_co_nb & permut & subeq_length).
        { eapply Hlength; eauto. }
        exists ({[+ a +]} ⊎  M_co_nb). exists (a :: s1), s2. repeat split; subst.
        ++ admit.
        ++ eauto.
        ++ constructor; eauto.
        ++ rewrite gmultiset_elements_disj_union. rewrite gmultiset_elements_singleton.
           simpl. eapply Permutation_skip. eauto.
        ++ simpl. lia.
      - exists ∅, [], (a :: s). repeat split.
        ++ assert ({[+ β +]} ⊎ (∅ : gmultiset A) = {[+ β +]}) as eq by multiset_solver.
           rewrite eq. rewrite norm_co_non_blocking_co_blocking_step; eauto.
        ++ constructor.
        ++ rewrite gmultiset_elements_empty. reflexivity.
        ++ eauto. *)
Admitted.

Lemma norm_shape `{ExtAction A} s :
      exists s1 s2 s3,
      ⟪ s ⟫ = s1 ++ s2 ++ s3
      /\ Forall exist_co_nba s1
      /\ Forall b_and_co_b s2
      /\ Forall non_blocking s3
      /\ s ≡ₚ s1 ++ s2 ++ s3.
Proof.
  induction s
    as (s & Hlength) using
         (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
  destruct s.
  + exists [], [], []. repeat split.
    * constructor. (* rewrite norm_singleton. *)
    * constructor.
    * eauto.
    * constructor.
  + admit.
  (* destruct (decide (non_blocking a)) as [nb' | b'].
    * exists ∅, [], (a :: s). repeat split.
      - assert ({[+ β +]} ⊎ (∅ : gmultiset A) = {[+ β +]}) as eq by multiset_solver.
        rewrite eq. assert (blocking β) as b.
        { destruct co_nb as (β' & nb & duo). eapply dual_blocks in duo;eauto. }
        rewrite norm_blocking_non_blocking_step; eauto.
      - constructor.
      - rewrite gmultiset_elements_empty. reflexivity.
      - eauto.
    * destruct (decide (exist_co_nba a)) as [co_nb' | co_b'].
      - assert (∃ (M_co_nb : gmultiset A) (s1 : list A) (s2 : trace A),
            normalize (β :: s) = {[+ β +]} ⊎ M_co_nb :: normalize s2
            ∧ s = s1 ++ s2
              ∧ Forall exist_co_nba s1
                ∧ elements M_co_nb ≡ₚ s1 ∧ length s2 ≤ length s) as (M_co_nb & s1 & s2 & eq & eq_trace & all_co_nb & permut & subeq_length).
        { eapply Hlength; eauto. }
        exists ({[+ a +]} ⊎  M_co_nb). exists (a :: s1), s2. repeat split; subst.
        ++ admit.
        ++ eauto.
        ++ constructor; eauto.
        ++ rewrite gmultiset_elements_disj_union. rewrite gmultiset_elements_singleton.
           simpl. eapply Permutation_skip. eauto.
        ++ simpl. lia.
      - exists ∅, [], (a :: s). repeat split.
        ++ assert ({[+ β +]} ⊎ (∅ : gmultiset A) = {[+ β +]}) as eq by multiset_solver.
           rewrite eq. rewrite norm_co_non_blocking_co_blocking_step; eauto.
        ++ constructor.
        ++ rewrite gmultiset_elements_empty. reflexivity.
        ++ eauto. *)
Admitted.


(*Lemma norm_length `{ExtAction A} :
  forall s I O s' M l,
    normalize s = M :: l -> length  *)


(* Lemma norm_loop_non_blocking_non_blocking_step `{ExtAction A} η η' s M boo :
  non_blocking η -> non_blocking η' -> normalize_loop (η :: η' :: s) (Some false) 
    = :: normalize_loop s ∅ ({[+ η' +]} ⊎ {[+ η +]} ⊎ m_nb).
Proof.
  intros nb nb'. simpl. rewrite decide_True; eauto.
  assert (¬ (exist_co_nba η')) as co_b.
  { intro Hyp_imp. destruct Hyp_imp as (μ'' & nb'' & duo). eapply dual_blocks in nb''; auto. eapply nb''. exact nb'. eauto. }
  rewrite decide_False; eauto. rewrite decide_True; eauto.
Qed. *)

(* Lemma norm_non_blocking_blocking_step `{ExtAction A} η β s M boo :
  non_blocking η -> blocking β -> normalize_loop (η :: β :: s) M boo = m_co_nb :: ({[+ η +]} ⊎ m_nb) :: normalize (β :: s).
Proof.
  intros nb nb'. etrans. simpl. rewrite decide_True; eauto. destruct (decide (exist_co_nba β)) as [co_nb | co_b].
  + admit.
  + rewrite decide_False; eauto.
  + eauto.
  assert (¬ (exist_co_nba η')) as co_b.
  { intro Hyp_imp. destruct Hyp_imp as (μ'' & nb'' & duo). eapply dual_blocks in nb''; auto. eapply nb''. exact nb'. eauto. }
  rewrite decide_False; eauto. rewrite decide_True; eauto.
Qed.
 *)

(*
Lemma norm_not_nil `{ExtAction A} s : s ≠ [] -> exists μ M l, normalize s = ({[+ μ +]} ⊎  M) :: normalise.
Proof.
 induction s
    as (s & Hlength) using
         (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
 destruct s.
 + intro Hyp. exfalso. eauto.
 + intros. exists a. destruct s.
   - exists ∅. exists []. assert ({[+ a +]} ⊎ ∅ = ({[+ a +]} :gmultiset A)) as eq by multiset_solver.
     rewrite eq. simpl. destruct (decide((non_blocking a))) as [nb | b].
     * rewrite eq. eauto.
     * destruct (decide (exist_co_nba a)) as [co_nb | co_b].
       ++ rewrite eq. eauto.
       ++ eauto.
   - 
  dependent induction s.
  - eauto.
  - unfold normalize. intro eq. now eapply norm_loop_nil in eq.
Qed. *)


(* Lemma norm_loop_non_blocking_non_blocking_step `{ExtAction A} η η' s m_co_nb m_nb :
  non_blocking η -> non_blocking η' -> normalize_loop (η :: η' :: s) m_co_nb m_nb = normalize_loop s m_co_nb ({[+ η' +]} ⊎ {[+ η +]} ⊎ m_nb).
Proof.
  intros nb nb'. simpl. rewrite decide_True; eauto.
  assert (¬ (exist_co_nba η')) as co_b.
  { intro Hyp_imp. destruct Hyp_imp as (μ'' & nb'' & duo). eapply dual_blocks in nb''; auto. eapply nb''. exact nb'. eauto. }
  rewrite decide_False; eauto. rewrite decide_True; eauto.
Qed. *)
(* Lemma norm_loop_output_output_step `{Label L} a b s mi mo :(*  ⊎ *)
  normalize_loop (ActOut a :: ActOut b :: s) mi mo = normalize_loop (ActOut b :: s) mi ({[+ a +]} ⊎ mo).
Proof. eauto. Qed. *)



(*
Lemma norm_loop_output_input_step `{ExtAction A} a b s mi mo :
  non_blocking normalize (ActOut a :: ActIn b :: s) mi mo = (mi, {[+ a +]} ⊎ mo) :: normalize (ActIn b :: s).
Proof.
  intros. simpl. now rewrite gmultiset_disj_union_right_id.
Qed. *) 




(* Lemma norm_sub `{ExtAction A} s mi mo I O nt :
  normalize_loop s mi mo = (I, O) :: nt -> mi ⊆ I /\ mo ⊆ O.
Proof.
  revert mi mo I O nt.
  induction s.
  - intros. simpl in H0. inversion H0; subst. eauto.
  - intros. destruct a.
    + rewrite norm_loop_input_step in H0.
      eapply IHs in H0. multiset_solver.
    + destruct s.
      ++ multiset_solver.
      ++ destruct e.
         +++ rewrite norm_loop_output_input_step in H0.
             inversion H; subst. multiset_solver.
         +++ rewrite norm_loop_output_output_step in H0.
             eapply IHs in H0. multiset_solver.
Qed. *)

(* Lemma norm_mem `{ExtAction A} μ s M nt :
    normalize (μ :: s) = M :: nt ->
    μ ∈ M.
Proof.
  revert μ M nt.
  dependent induction s; intros μ M nt Hyp.
  + rewrite norm_singleton in Hyp. set_solver.
  + destruct (decide (non_blocking μ)) as [ nb | b].
    * simpl in *. destruct b_nb; [ destruct b |].
      - rewrite decide_False in Hyp; eauto.
        inversion Hyp; subst. multiset_solver. multiset_solver.
      -   mse admit.
    *
  rewrite norm_loop_input_step in H0.
  eapply norm_sub in H0. multiset_solver. 
Admitted.*)

(* Lemma norm_output_mem `{HL : Label L} s a mi mo I O nt :
    normalize_loop (ActOut a :: s) mi mo = (I, O) :: nt ->
    a ∈ O.
Proof.
  intros.
  destruct s.
  - multiset_solver.
  - destruct e.
    + rewrite norm_loop_output_input_step in H. multiset_solver.
    + rewrite norm_loop_output_output_step in H.
      eapply norm_sub in H. multiset_solver.
Qed.
 *)
(* Lemma norm_extend_mi `{HL : Label L} :
  forall s a I O mi mo s',
    normalize_loop s I O = (mi, mo) :: normalize s' ->
    normalize_loop s ({[+ a +]} ⊎ I) O = ({[+ a +]} ⊎ mi, mo) :: normalize s'.
Proof.
  dependent induction s.
  - intros. simpl in *. inversion H; subst. eauto.
  - intros.
    destruct a.
    + rewrite norm_loop_input_step in H.
      eapply (IHs a0) in H.
      rewrite norm_loop_input_step.
      now replace
        ({[+ a +]} ⊎ ({[+ a0 +]} ⊎ I)) with
        ({[+ a0 +]} ⊎ ({[+ a +]} ⊎ I)) by multiset_solver.
    + destruct s.
      ++ simpl. simpl in H. inversion H. now subst.
      ++ destruct e.
         +++ rewrite norm_loop_output_input_step in *.
             inversion H. subst. eauto.
         +++ rewrite norm_loop_output_output_step in *.
             inversion H. subst. eauto.
Qed. *)

(* Lemma norm_extend_mo `{HL : Label L} :
  forall s a I O mi mo s',
    normalize_loop s I O = (mi, mo) :: normalize s' ->
    normalize_loop s I ({[+ a +]} ⊎ O) = (mi, {[+ a +]} ⊎ mo) :: normalize s'.
Proof.
  dependent induction s.
  - intros. simpl in *. inversion H; subst. eauto.
  - intros.
    destruct a.
    + rewrite norm_loop_input_step in H.
      eapply (IHs a0) in H.
      rewrite norm_loop_input_step.
      now replace
        ({[+ a +]} ⊎ ({[+ a0 +]} ⊎ I)) with
        ({[+ a0 +]} ⊎ ({[+ a +]} ⊎ I)) by multiset_solver.
    + destruct s.
      ++ simpl. simpl in H. inversion H. subst.
         now replace
           ({[+ a +]} ⊎ ({[+ a0 +]} ⊎ O)) with
           ({[+ a0 +]} ⊎ ({[+ a +]} ⊎ O)) by multiset_solver.
      ++ destruct e.
         +++ rewrite norm_loop_output_input_step in *.
             inversion H. subst.
             now replace
               ({[+ a +]} ⊎ ({[+ a0 +]} ⊎ O)) with
               ({[+ a0 +]} ⊎ ({[+ a +]} ⊎ O)) by multiset_solver.
         +++ rewrite norm_loop_output_output_step in *.
             eapply (IHs a0) in H.
             now replace
               ({[+ a +]} ⊎ ({[+ a0 +]} ⊎ O)) with
               ({[+ a0 +]} ⊎ ({[+ a +]} ⊎ O)) by multiset_solver.
Qed. *)

(* Lemma normalize_loop_mi `{HL : Label L} :
  forall s a mi mo I O nt, normalize_loop (ActOut a :: s) mi mo = (I, O) :: nt -> mi = I.
Proof.
  dependent induction s.
  - simpl. intros. now inversion H.
  - intros.
    destruct a.
    + rewrite norm_loop_output_input_step in H.
      now inversion H.
    + eauto.
Qed. *)

(* Lemma norm_shape_elements `{ExtAction A} s nt M:
    normalize s = nt -> M ∈ nt -> M <> ∅.
Proof.
  revert nt M.
  dependent induction s.
  + intros nt M Hyp1 mem. rewrite norm_nil in Hyp1. subst. inversion mem.
  + intros nt M Hyp1 mem. admit.
Admitted. *)

(* Lemma norm_same_shape_non_blocking `{ExtAction A} s : s <> [] -> Forall non_blocking s -> normalize s = [list_to_set_disj s].
Proof.
  dependent induction s.
  + intro forall_nb. simpl. set_solver.
  + intros neq forall_nb. simpl. admit.
Admitted.
 *)
(* Lemma norm_same_shape_co_nb `{ExtAction A} s : s <> [] -> Forall exist_co_nba s -> normalize s = [list_to_set_disj s].
Proof.
  dependent induction s.
  + intro forall_nb. simpl. set_solver.
  + intros neq forall_nb. simpl. admit.
Admitted. *)

(* Lemma norm_same_shape_b_and_co_b `{ExtAction A} s : s <> [] -> Forall b_and_co_b s -> normalize s = [list_to_set_disj s].
Proof.
  dependent induction s.
  + intro forall_nb. simpl. set_solver.
  + intros neq forall_nb. simpl. admit.
Admitted. *)

(* Lemma norm_shape `{ExtAction A} : forall s,
    normalize s = []
    \/ exists M s1 s2, normalize s = M :: normalize s2
                      /\ normalize s1 = [M]
                      /\ s = s1 ++ s2
                      /\ (Forall exist_co_nba s1 \/ Forall non_blocking s1 \/ Forall b_and_co_b s1)
                      /\ (elements M) ≡ₚ s1.
Proof.
  induction s as [|μ s].
  - eauto.
  - right. assert (normalize s = []
  ∨ ∃ (M : gmultiset A) (s1 : list A) (s2 : trace A),
      normalize s = M :: normalize s2
      ∧ normalize s1 = [M]
      ∧ s = s1 ++ s2
        ∧ (Forall exist_co_nba s1
           ∨ Forall non_blocking s1 ∨ Forall b_and_co_b s1)
          ∧ elements M ≡ₚ s1) as [eq_nil |(M & s1 & s2 & eq & eq_norm & eq_trace & type_of_mset & all_elem)].
    { eapply IHs. }
    + eapply norm_nil_rev in eq_nil. subst. exists {[+ μ +]}, [μ], []. repeat split.
      * rewrite norm_nil. rewrite norm_singleton. reflexivity.
      * eapply norm_singleton.
      * destruct (decide(non_blocking μ)) as [nb | b].
        -- right. left. constructor; eauto.
        -- destruct (decide(exist_co_nba μ)) as [co_nb | co_b].
           ++ left. constructor; eauto.
           ++ right. right. constructor. split; eauto. constructor.
      * rewrite gmultiset_elements_singleton. reflexivity.
    + destruct type_of_mset as [forall_co_nba | [forall_nb | forall_b_co_b]].
      * destruct (decide(exist_co_nba μ)) as [co_nb | co_b].
        -- exists ({[+ μ +]} ⊎ M), (μ :: s1), s2. subst. repeat split.
           ++ admit.
           ++ rewrite norm_same_shape_co_nb; eauto. simpl.
              rewrite<- all_elem. assert (list_to_set_disj (elements M) = M) as eq'.
              { admit. } rewrite eq'. eauto.
           ++ left. constructor; eauto.
           ++ simpl. rewrite gmultiset_elements_disj_union. rewrite gmultiset_elements_singleton.
              simpl. set_solver. 
        -- exists ({[+ μ +]}), [μ], (s1 ++ s2). subst. repeat split.
           ++ admit.
           ++ eapply norm_singleton.
           ++ destruct (decide(non_blocking μ)) as [nb | b].
              ** right. left. constructor; eauto.
              ** right. right. constructor; eauto. split; eauto.
           ++ rewrite gmultiset_elements_singleton. reflexivity.
      * admit.
      * admit.
Admitted. *)
        
      
(*               assert (list_to_set_disj s1
    
    
         destructdestruct (decide(non_blocking μ)) as [nb | b]; simpl in *.
    + right.
      destruct IHs.
      ++ eapply norm_nil in H. subst.
         exists {[+ a +]}, ∅, [ActIn a], [], [].
         simpl. repeat split; eauto with mdb; try now eapply Forall_nil.
         +++ now replace
               ({[+ a +]} ⊎ ∅) with
               ({[+ a +]} : gmultiset L) by multiset_solver.
         +++ eapply Forall_cons.
             eexists. reflexivity. now eapply Forall_nil.
         +++ rewrite gmultiset_elements_singleton. simpl.
             eauto.
      ++ destruct H
           as (mi & mo & s1 & s2 & s' & e0 & e1 & e3 & e4 & e5 & e6).
         exists ({[+ a +]} ⊎ mi), mo, (ActIn a :: s1), s2, s'.
         unfold normalize at 1.
         rewrite norm_loop_input_step.
         repeat split; eauto with mdb.
         +++ eapply norm_extend_mi.
             destruct s. inversion e0. eauto.
         +++ rewrite e1. eauto.
         +++ eapply Forall_cons.
             eexists. reflexivity. eassumption.
         +++ rewrite gmultiset_elements_disj_union.
             rewrite gmultiset_elements_singleton.
             simpl. eauto.
    + right.
      destruct IHs.
      ++ eapply norm_nil in H. subst.
         exists  ∅, {[+ a +]}, [], [ActOut a], [].
         simpl. repeat split; eauto with mdb; try now eapply Forall_nil.
         +++ now replace
               ({[+ a +]} ⊎ ∅) with
               ({[+ a +]} : gmultiset L) by multiset_solver.
         +++ eapply Forall_cons.
             eexists. reflexivity. now eapply Forall_nil.
         +++ rewrite gmultiset_elements_singleton. simpl.
             eauto.
      ++ destruct H
           as (mi & mo & s1 & s2 & s' & e0 & e1 & e3 & e4 & e5 & e6).
         destruct s.
         +++ inversion e0.
         +++ destruct e.
             ++++ exists ∅, {[+ a +]}, [], [ActOut a], (ActIn a0 :: s).
                  repeat split; eauto.
                  unfold normalize at 1 in e0.
                  eapply (norm_extend_mo _ a0) in e0.
                  unfold normalize at 1.
                  rewrite norm_loop_output_input_step.
                  now replace
                    ({[+ a +]} ⊎ ∅) with
                    ({[+ a +]} : gmultiset L) by multiset_solver.
                  now eapply Forall_nil.
                  eapply Forall_cons.
                  eexists. reflexivity. now eapply Forall_nil.
                  rewrite gmultiset_elements_singleton. eauto.
             ++++ exists mi, ({[+ a +]} ⊎ mo), s1, (ActOut a :: s2), s'.
                  repeat split; eauto.
                  unfold normalize at 1 in e0.
                  unfold normalize at 1.
                  rewrite norm_loop_output_output_step.
                  eapply norm_extend_mo.
                  eassumption.
                  eapply normalize_loop_mi in e0. subst.
                  rewrite gmultiset_elements_empty in e5.
                  simpl in e5.
                  eapply Permutation_nil in e5. subst.
                  cbn. rewrite e1. eauto.
                  eapply Forall_cons.
                  eexists. reflexivity. eassumption.
                  rewrite gmultiset_elements_disj_union.
                  rewrite gmultiset_elements_singleton.
                  simpl. eauto. 
Qed.*)

(* Lemma norm_perm `{ExtAction A} : forall nt s1 s2,
    normalize s1 = nt -> normalize s2 = nt -> s1 ≡ₚ s2.
Proof.
  intros nt.
  induction nt.
  - intros s1 s2 H1 H2.
    eapply norm_nil_rev in H1, H2. now subst.
  - intros s1 s2 H1 H2. admit.
(*     destruct (norm_shape s1).
    rewrite H in H1. inversion H1.
    destruct (norm_shape s2).
    rewrite H0 in H2. inversion H2.
    destruct H as
      (mi0 & mo0 & s01 & s02 & s03 & e01 & e02 & e03 & e04 & e05 & e06).
    destruct H0 as
      (mi1 & mo1 & s11 & s12 & s13 & e11 & e12 & e13 & e14 & e15 & e16).
    rewrite e01 in H1. rewrite e11 in H2.
    inversion H2. inversion H1.  subst.
    etransitivity.
    eapply Permutation_app_tail.
    trans (map ActIn (elements mi)). now symmetry in e15. eassumption.
    etransitivity.
    eapply Permutation_app_head.
    eapply Permutation_app_tail.
    trans (map ActOut (elements mo)). now symmetry in e06. eassumption.
    eapply Permutation_app_head.
    eapply Permutation_app_head.
    eapply (IHnt s03 s13 H7 eq_refl). *)
Admitted. *)

(* Lemma norm_length `{ExtAction A} :
  forall s M s',
    normalize s = M :: normalize s' ->
    length s' < length s.
Proof.
  intros s.
  dependent induction s.
  - intros M s' Hyp_eq. rewrite norm_nil in Hyp_eq. inversion Hyp_eq.
  - intros.
    destruct (norm_shape (a :: s)) as [|].
    (* + now eapply norm_loop_nil in H0.
    destruct H0 as (mi' & mo' & s1 & s2 & s'' & e0 & e1 & e3 & e4 & e5 & e6).
    assert (exists a, a ∈ s1 ++ s2) as (b & mem).
    destruct a.
    exists (ActIn a). eapply elem_of_app. left.
    eapply elem_of_Permutation_proper. symmetry. eassumption.
    eapply list_elem_of_fmap. exists a. split; eauto.
    eapply gmultiset_elem_of_elements.
    now eapply norm_input_mem in e0.
    exists (ActOut a). eapply elem_of_app. right.
    eapply elem_of_Permutation_proper. symmetry. eassumption.
    eapply list_elem_of_fmap. exists a. split; eauto.
    eapply gmultiset_elem_of_elements.
    now eapply norm_output_mem in e0.
    rewrite e1, app_assoc, length_app.
    eapply elem_of_Permutation in mem as (s0 & eqp) .
    replace (length (s1 ++ s2)) with (length (b :: s0)).
    replace (length s') with (length s'').
    eapply PeanoNat.Nat.lt_add_pos_l, Nat.lt_0_succ.
    eapply Permutation_length.
    rewrite e0 in H. inversion H.
    now eapply norm_perm.
    eapply Permutation_length. now symmetry. *)
Admitted. *)

From Stdlib Require Import Wellfounded.


(* TODO : delted those lemma , already in weak_transition file *)
Lemma get_back_wt_co_non_blocking_action `{gLtsObaFW P A} (p : P) q s μ : 
  (exists η, non_blocking η /\ dual μ η) -> p ⟹[s ++ [μ]] q
    -> p ⟹⋍[[μ] ++ s] q.
Proof.
  revert p q μ. dependent induction s.
  + intros; simpl in *; eauto. exists q. split; eauto. reflexivity.
  + intros p q μ co_nb wk_tr. assert ((a :: s) ++ [μ] = a :: (s ++ [μ])) as eq.
    { simpl. eauto. } rewrite eq in wk_tr.
    eapply wt_pop in wk_tr as (p'' & wk_tr1 & wk_tr2).
    eapply IHs in wk_tr2 as (p''' & wk_tr2 & eq''');eauto.
    eapply wt_split in wk_tr2 as (p'''' & wk_tr2 & wk_tr'2).
    assert (p ⟹⋍[[μ ; a]] p'''').
    { eapply wt_input_swap;eauto. assert ([a; μ] = [a] ++ [μ]) as eq'''' by (simpl; eauto).
    rewrite eq''''. eapply wt_concat;eauto. }
    assert ([μ] ++ a :: s = [μ; a] ++ s) as eq1. { simpl. eauto. }
    rewrite eq1. eapply wt_join_eq.
    * exact H2.
    * exists p'''; split;eauto.
Qed.

Lemma get_back_wt_co_non_blocking_trace `{gLtsObaFW P A} (p : P) q s s' :
  Forall exist_co_nba s' -> p ⟹[s ++ s'] q
    -> p ⟹⋍[s' ++ s] q.
Proof.
  revert p q s. dependent induction s'.
  + intros p q s Hyp wk_tr; simpl in *; eauto. exists q. split.
    * rewrite app_nil_r in wk_tr. eauto.
    * reflexivity.
  + intros p q s co_nb wk_tr. inversion co_nb; subst.
    assert (s ++ a :: s' = ((s ++ [a]) ++ s')) as eq.
    { rewrite<- app_assoc. simpl. eauto. }
    rewrite eq in wk_tr. eapply wt_split in wk_tr as (p' & wk_tr1 & wk_tr2).
    eapply get_back_wt_co_non_blocking_action in wk_tr1;eauto.
    destruct wk_tr1 as (p'' & wk_tr' & equiv').
    eapply wt_split in wk_tr' as (p1 & wk_tr1 & wk_tr'1).
    symmetry in equiv'. eapply eq_spec_wt in equiv'; eauto.
    eapply wt_join_eq_r in wk_tr'1 as (q' & wk_tr_q' & equiv'');eauto.
    eapply IHs' in wk_tr_q';eauto.
    assert ((a :: s') ++ s = [a] ++ (s' ++ s)) as eq' by (simpl;eauto).
    rewrite eq'. eapply wt_join_eq_r;eauto.
    destruct wk_tr_q' as (p'1 & wk_tr'1 & equiv1).
    exists p'1. split; eauto.
    etrans;eauto.
Qed.


Theorem normalize_wta_r `{gLtsObaFW P A} : forall s (p : P) q, p ⟹[s] q -> p ⟹⋍[⟪s⟫] q.
Proof.
  induction s
    as (s & Hlength)
         using
         (well_founded_induction (wf_inverse_image _ nat _ List.length PeanoNat.Nat.lt_wf_0)).
  destruct s.
  - intros p q w. simpl. exists q. split. eauto with mdb. reflexivity.
  - intros p q wt_tr. assert (a :: s = [a] ++ s) as eq_trace.
    { simpl; eauto. } rewrite eq_trace in wt_tr.
    eapply wt_split in wt_tr as (p' & wt_tr1 & wt_tr2).
    destruct (decide (non_blocking a)) as [nb | b].
    + assert (non_blocking a);eauto.
      eapply (norm_non_blocking_step a s) in nb as (s'3 & s1 & s2 & s3 & eq & cnb & bcb & nb & perm1 & perm2 & mem).
      rewrite eq.
      eapply Hlength in wt_tr2; try (simpl; lia).
      assert (⟪ s ⟫ = s1 ++ s2 ++ s'3) as eq'.
      { admit. }
      destruct wt_tr2 as (p'' & wt_tr2 & equiv). rewrite eq' in wt_tr2.
      eapply wt_split in wt_tr2 as (p''' & wt_tr2 & wt_tr2').
      eapply wt_split in wt_tr2' as (p'''' & wt_tr2' & wt_tr2'').
      assert (p ⟹⋍[(s1 ++ s2) ++ [a]] p'''') as wk_tr3.
      { eapply push_wt_non_blocking_action;eauto. eapply wt_push_left;eauto.
        eapply wt_concat; eauto. }
      destruct wk_tr3 as (p4 & wk_tr3 & equiv'').
      eapply wt_split in wk_tr3 as (p5 & wk_tr1 & wk_tr2). symmetry in equiv''.
      eapply eq_spec_wt in equiv''; eauto.
      eapply wt_join_eq_r in wk_tr2 as (p'5 & wk_tr2 & equiv5) ;eauto.
      eapply wt_non_blocking_action_perm in wk_tr2 as (p''5 & wk_tr2 & equiv'5);eauto.
      exists p''5. split.
      ++ eapply wt_split in wk_tr1 as (p7 & wk_tr1' & wk_tr1'').
         eapply wt_concat;eauto. eapply wt_concat;eauto.
      ++ etrans; eauto. etrans; eauto.
      ++ simpl. constructor; eauto.
    + destruct (decide (exist_co_nba a)) as [co_nb | co_b].
      * assert (exist_co_nba a);eauto.
        eapply (norm_co_nba_step a s) in co_nb as (s'1 & s1 & s2 & s3 & eq & cnb & bcb & nb & perm1 & perm2 & mem).
        rewrite eq.
        eapply Hlength in wt_tr2; try (simpl; lia).
        assert (⟪ s ⟫ = s'1 ++ s2 ++ s3) as eq'.
        { admit. }
        destruct wt_tr2 as (p'' & wt_tr2 & equiv). rewrite eq' in wt_tr2.
        eapply wt_split in wt_tr2 as (p''' & wt_tr2 & wt_tr2').
        eapply wt_join_eq.
        ++ eapply (wt_input_perm (a :: s'1));eauto.
           assert (a :: s'1 = [a] ++ s'1) as eq'';eauto. rewrite eq''.
           eapply wt_concat.
           ** exact wt_tr1.
           ** exact wt_tr2.
        ++ exists p''; eauto.
      * assert (b_and_co_b a) as bcb.
        { split; eauto. }
        eapply (norm_b_and_co_b_step a s) in bcb as (s'2 & s1 & s2 & s3 & eq & cnb & bcb & nb & perm1 & perm2 & mem).
        rewrite eq.
        eapply Hlength in wt_tr2; try (simpl; lia).
        assert (⟪ s ⟫ = s1 ++ s'2 ++ s3) as eq'.
        { admit. }
        destruct wt_tr2 as (p'' & wt_tr2 & equiv). rewrite eq' in wt_tr2.
        eapply wt_split in wt_tr2 as (p''' & wt_tr2 & wt_tr2').
        eapply wt_split in wt_tr2' as (p'''' & wt_tr2' & wt_tr2'').
        assert (p ⟹⋍[s1 ++ [a]] p''') as (p3 & wk_tr3 & equiv3).
        { eapply get_back_wt_co_non_blocking_trace;eauto.
          simpl. eapply wt_push_left;eauto. }
        eapply wt_split in wk_tr3 as (p'2 & wk_tr2' & wk_tr2'').
        eapply wt_join_eq_r;eauto. subst.
        assert (p''' ⟹[s'2 ++ s3] p'').
        { eapply wt_concat;eauto. }
        symmetry in equiv3. eapply eq_spec_wt in equiv3 as (p9 & wk_tr & equiv3); eauto.
        assert ((a :: s'2) ++ s3 = [a] ++ (s'2 ++ s3)) as eq5.
        { simpl. eauto. } rewrite eq5.
        eapply wt_join_eq_r;eauto. exists p9. split ;eauto. etrans;eauto.
Admitted.

(* Lemma normalize_wta_l `{gLtsObaFW P A} : forall s (p : P) q, p ⟹[⟪s⟫] q -> p ⟹⋍[s] q.
Proof.
   induction s
    as (s & Hlength)
         using
         (well_founded_induction (wf_inverse_image _ nat _ List.length PeanoNat.Nat.lt_wf_0)).
  destruct s.
  - intros p q w. simpl in w. exists q. split. eauto with mdb. reflexivity.
  - intros p q wt_tr. destruct (decide (non_blocking a)) as [nb | b].
    + eapply (norm_non_blocking_step a s) in nb as (s1 & s2 & s3 & eq & cnb & bcb & nb & perm & mem).
      rewrite eq in wt_tr.
      
      Check wt_non_blocking_action_perm.
      wt_non_blocking_action_perm (* qu'importe l'ordre des nb *)
      push_wt_non_blocking_action (* mettre les nb à la fin *)
      
      wt_input_perm (* qu'importe l'ordre des co_nb *)
      wt_input_swap (* mettre les co_nb au début *)
      
      
      rewrite eq.
    (* destruct (norm_shape (e :: s)).
    now eapply norm_loop_nil in H3.
    destruct H3
      as (mi & mo & s1 & s2 & s' & e0 & e1 & e3 & e4 & e5 & e6).
    rewrite e0 in w.
    simpl in w.
    rewrite e1.
    eapply wt_split in w as (t & w1 & w2).
    eapply wt_split in w2 as (r & w2 & w3).
    assert (hl : length s' < length (e :: s)).
    eapply norm_length in e0. eassumption.
    set (h := Hlength s' hl r q w3).
    eapply wt_join_eq.
    eapply (wt_input_perm (map ActIn (elements mi))).
    admit. (* eapply are_inputs_map_ActIn. *)
    now symmetry. eassumption.
    eapply wt_join_eq.
    eapply (wt_non_blocking_action_perm (map ActOut (elements mo))).
    admit. (* eapply are_outputs_map_ActOut. *)
    now symmetry. eassumption. eauto. *) admit.
Admitted. *)

(*Lemma normalize_wta `{gLtsObaFW P A} s (p : P) q : p ⟹⋍[⟪s⟫] q <-> p ⟹⋍[s] q.
Proof.
  split.
  intros (q' & w & sc).
  eapply normalize_wta_l in w as (q'' & w & sc').
  exists q''. split. eauto with mdb. transitivity q'; now symmetry.
  intros (q' & w & sc).
  eapply normalize_wta_r in w as (q'' & w & sc').
  exists q''. split. eauto with mdb. transitivity q'; now symmetry.
Qed. *)

Lemma pre_act_of_eq `{gLtsEq P A} `{Γ : A -> PreAct}
  p q : p ⋍ q -> ⌈ Γ ⌉ (coR p) ≡ ⌈ Γ ⌉ (coR q).
Proof.
  intro equiv. split.
  (* apply leibniz_equiv. intros Hyp. split. *)
  - intro Hyp. destruct Hyp as (μ & mem_coR & eq);subst.
    destruct mem_coR as (μ' & accepts & duo & b).
    eapply accepts_preserved_by_eq in accepts;eauto.
    assert (μ ∈ coR q) as mem.
    { exists μ'. repeat split; eauto. }
    eapply map_gamma_of_action;eauto.
  - intro Hyp. destruct Hyp as (μ & mem_coR & eq);subst.
    destruct mem_coR as (μ' & accepts & duo & b). symmetry in equiv.
    eapply accepts_preserved_by_eq in accepts;eauto.
    assert (μ ∈ coR p) as mem.
    { exists μ'. repeat split; eauto. }
    eapply map_gamma_of_action;eauto.
Qed.

(* Lemma normalize_accs `{gLtsObaFW P A, !FiniteImageLts P A}
  `{!@PreExtAction P A _ FinA PreA PreA_eq PreA_countable 𝝳 Φ _}
  (p : P) (s : trace A) h1 h2 :
  (set_map pre_co_actions_of (wt_refuses_set p s h1) : gset (gset PreA))
  ≡ (set_map pre_co_actions_of (wt_refuses_set p (linorm s) h2) : gset (gset PreA)).
Proof.
  intros.
  split.
  - intro.
    eapply elem_of_map.
    eapply elem_of_map in H3 as (q & eq & mem).
    eapply wt_refuses_set_spec1 in mem as (w & st).
    eapply normalize_wta_r in w as (q' & w' & st').
    exists q'. split.
    transitivity (lts_outputs q). assumption. symmetry.
    eapply leibniz_equiv. now eapply outputs_of_eq in st'.
    eapply wt_refuses_set_spec2; split.
    eassumption.
    symmetry in st'. eapply stable_preserved_by_eq; eauto.
  - intro.
    eapply elem_of_map.
    eapply elem_of_map in H3 as (q & eq & mem).
    eapply wt_refuses_set_spec1 in mem as (w & st).
    eapply normalize_wta_l in w as (q' & w' & st').
    exists q'. split.
    transitivity (lts_outputs q). eassumption.
    eapply leibniz_equiv.
    eapply outputs_of_eq. symmetry. eassumption.
    eapply wt_refuses_set_spec2; split.
    eassumption.
    symmetry in st'. eapply stable_preserved_by_eq; eauto.
Qed. *)

Definition bhv_lin_pre_cond1 `{gLts P H, gLts Q H} (p : P) (q : Q) := forall norm_s, p ⇓ linearize norm_s -> q ⇓ linearize norm_s.

Notation "p ₁≼ₙₒᵣₘ₋ₐₛ q" := (bhv_lin_pre_cond1 p q) (at level 70).

Definition bhv_lin_pre_cond2 `{
  gLtsP : @gLts P A H, AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳P gLtsP gLtsT,
  gLtsQ : @gLts Q A H, AbsQT : @AbsAction Q T FinA PreAct A H Φ 𝝳Q gLtsQ gLtsT}
  (p : P) (q : Q) :=
  forall norm_s q',
    p ⇓ linearize norm_s -> q ⟹[linearize norm_s] q' -> q' ↛ ->
    ∃ p', p ⟹[linearize norm_s] p' /\ p' ↛ /\ (⌈ (𝝳P ∘ Φ) ⌉ (coR p') ⊆ ⌈ (𝝳Q ∘ Φ) ⌉ (coR q')).

Notation "p ₂≼ₙₒᵣₘ₋ₐₛ q" := (bhv_lin_pre_cond2 p q) (at level 70).

Definition bhv_lin_pre `{
  gLtsP : @gLts P A H, AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳P gLtsP gLtsT,
  gLtsQ : @gLts Q A H, AbsQT : @AbsAction Q T FinA PreAct A H Φ 𝝳Q gLtsQ gLtsT}
  (p : P) (q : Q) := p ₁≼ₙₒᵣₘ₋ₐₛ q /\ p ₂≼ₙₒᵣₘ₋ₐₛ q.

Notation "p ≼ₙₒᵣₘ₋ₐₛ q" := (bhv_lin_pre p q) (at level 70).

(* TODO : delte it : *)
Lemma cnv_drop_input_trace `{gLtsObaFW P A} (p : P) s' s :
  Forall exist_co_nba s' -> p ⇓ (s' ++ s)
    -> p ⇓ s.
Proof.
  revert s' p. induction s'.
  + intros; simpl ;eauto.
  + intros. eapply IHs'.
    * inversion H2; subst ;eauto.
    * simpl in *. eapply cnv_drop_input_hd in H3;eauto.
      inversion H2; eauto.
Qed.

(* faux : ( c ? x . c ! 0 || rec X.X, empty_set) et s = c ! 0 :: [ c ? 1] *)
(* Lemma normalize_acnv_l `{gLtsObaFW P A} (p : P) s : p ⇓ s -> p ⇓ ⟪ s ⟫.
Proof.
  revert p.
  induction s
    as (s & Hlength)
         using (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
  destruct s; intros p Hyp_conv.
  - rewrite norm_nil. exact Hyp_conv.
  - destruct (decide (non_blocking a)) as [nb | b]; [| destruct (decide (exist_co_nba a)) as [co_nb | co_b] ].
    * assert (non_blocking a);eauto.
      eapply (norm_non_blocking_step a s) in nb as (s'3 & s1 & s2 & s3 & eq & cnb & bcb & nb & perm1 & perm2 & mem).
      admit.
    * assert (exist_co_nba a);eauto.
      eapply (norm_co_nba_step a s) in co_nb as (s'1 & s1 & s2 & s3 & eq & cnb & bcb & nb & perm1 & perm2 & mem).
      rewrite eq. 
      assert (⟪ s ⟫ = s'1 ++ s2 ++ s3) as eq'.
      { admit. }
      assert (p ⇓ s) as Hyp_conv'.
      { eapply cnv_drop_input_hd;eauto. }
      eapply Hlength in Hyp_conv'; try (simpl; lia).
      rewrite eq' in Hyp_conv'.
      
      
      
      destruct s1.
      + inversion mem.
      + simpl. constructor.
        -- inversion Hyp_conv; eauto.
        -- intros. assert (⟪ s ⟫ = s'1 ++ s2 ++ s3) as eq'.
           { admit. }
           assert (p ⇓ s).
           { eapply cnv_drop_input_hd;eauto. }
           
             assert (Forall exist_co_nba [s]) ;eauto.
        eapply Hlength.
           eapply (cnv_input_perm q s1);eauto.
      
      { admit. }
      eapply Hlength; try (simpl;lia).
      rewrite eq'.
      eapply cnv_prefix in Hyp_conv as Hyp_prefix.
      symmetry in perm2. eapply cnv_input_perm in perm2 ; eauto.
      assert (q ⇓ s'1).
      { admit. }
      rewrite eq in H2. admit. 
    * assert (b_and_co_b a) as bcb.
      { split; eauto. }
      eapply (norm_b_and_co_b_step a s) in bcb as (s'2 & s1 & s2 & s3 & eq & cnb & bcb & nb & perm1 & perm2 & mem).
      admit.
  (* destruct (norm_shape s).
  - eapply norm_nil in H3. subst. now simpl.
  - destruct H3
      as (mi & mo & s1 & s2 & s' & e0 & e1 & e3 & e4 & e5 & e6).
    intros p hacnv.
    rewrite e0. simpl. rewrite e1 in hacnv.
    set (h0 := cnv_prefix hacnv).
    set (h2 := cnv_wt_prefix _ _ _ hacnv).
    rewrite app_assoc.
    eapply cnv_jump.
    + eapply cnv_jump.
      eapply (cnv_input_perm p s1);eauto.
      admit. (* eassumption *)
      now symmetry. (* intros.
      eapply cnv_prefix. eassumption. *)
      intros q hw.
      eapply (wt_input_perm _ s1) in hw as (q0 & hw0 & heq0).
      eapply h2, cnv_prefix in hw0.
      eapply cnv_preserved_by_eq. eassumption.
      eapply (cnv_non_blocking_action_perm q0 s2 (map ActOut (elements mo))); eauto.
      admit. (* assumption. *)
      now symmetry.
      admit. (* eapply are_inputs_map_ActIn. *) now symmetry.
    + intros q hw.
      eapply Hlength. eapply norm_length. eassumption.
      eapply wt_split in hw as (t & hw1 & hw2).
      eapply (wt_input_perm _ s1) in hw1 as (p0 & hwp0 & heqp0).
      eapply (wt_non_blocking_action_perm _ s2) in hw2 as (q0 & hwq0 & heqq0).
      eapply cnv_preserved_by_eq. eassumption.
      assert (t ⇓ s2 ++ s').
      eapply cnv_preserved_by_eq. eassumption.
      eapply cnv_wt_prefix; eassumption.
      eapply cnv_wt_prefix; eassumption.
      admit. (* eapply are_outputs_map_ActOut. *) now symmetry.
      admit. (* eapply are_inputs_map_ActIn. *) now symmetry. *)
Admitted. *)

(* Lemma normalize_acnv_r `{gLtsObaFW P A} (p : P) s : p ⇓ ⟪ s ⟫ -> p ⇓ s.
Proof.
  revert p.
  induction s
    as (s & Hlength)
         using (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
  destruct s. intros p Hyp.
  - rewrite norm_nil in Hyp. eauto.
  - intros p Hyp_conv. constructor;intros.
    + inversion Hyp_conv; subst;eauto.
    + destruct (decide (non_blocking a)) as [nb | b]; [| destruct (decide (exist_co_nba a)) as [co_nb | co_b] ].
      * assert (non_blocking a);eauto.
        eapply (norm_non_blocking_step a s) in nb as (s'3 & s1 & s2 & s3 & eq & cnb & bcb & nb & perm1 & perm2 & mem).
        admit.
      * assert (exist_co_nba a);eauto.
        eapply (norm_co_nba_step a s) in co_nb as (s'1 & s1 & s2 & s3 & eq & cnb & bcb & nb & perm1 & perm2 & mem).
        rewrite eq in Hyp_conv.
        assert (⟪ s ⟫ = s'1 ++ s2 ++ s3) as eq'.
        { admit. }
        eapply Hlength; try (simpl;lia).
        rewrite eq'.
        eapply cnv_prefix in Hyp_conv as Hyp_prefix.
        symmetry in perm2. eapply cnv_input_perm in perm2 ; eauto.
        assert (q ⇓ s'1).
        { admit. }
        rewrite eq in H2. admit. 
      * assert (b_and_co_b a) as bcb.
        { split; eauto. }
        eapply (norm_b_and_co_b_step a s) in bcb as (s'2 & s1 & s2 & s3 & eq & cnb & bcb & nb & perm1 & perm2 & mem).
        admit.
    
    (* 
  destruct H3
      as (mi & mo & s1 & s2 & s' & e0 & e1 & e3 & e4 & e5 & e6).
    intros p hacnv.
    rewrite e0 in hacnv.
    simpl. rewrite e1.
    simpl in hacnv.
    set (h0 := cnv_prefix hacnv).
    set (h1 := cnv_wt_prefix _ _ _ hacnv).
    rewrite app_assoc.
    eapply cnv_jump.
    + eapply cnv_jump.
      eapply cnv_input_perm.
      admit. (* eapply are_inputs_map_ActIn. *) eassumption. eassumption.
      intros q hw.
      eapply (wt_input_perm s1 (map ActIn (elements mi))) in hw as (q0 & hw0 & heq0).
      eapply h1, cnv_prefix in hw0.
      eapply cnv_preserved_by_eq. eassumption.
      eapply cnv_non_blocking_action_perm.
      admit. (* eapply are_outputs_map_ActOut. *) eassumption.
      eassumption.
      admit. (* eassumption. *) now symmetry.
    + intros q hw.
      eapply Hlength. eapply norm_length. eassumption.
      eapply wt_split in hw as (t & hw1 & hw2).
      eapply (wt_input_perm s1 (map ActIn (elements mi))) in hw1 as (p0 & hwp0 & heqp0).
      eapply (wt_non_blocking_action_perm s2 (map ActOut (elements mo))) in hw2 as (q0 & hwq0 & heqq0).
      eapply cnv_preserved_by_eq. eassumption.
      assert (t ⇓ map ActOut (elements mo) ++ ⟪ s' ⟫).
      eapply cnv_preserved_by_eq. eassumption.
      eapply cnv_wt_prefix; eassumption.
      eapply cnv_wt_prefix; eassumption.
      admit. (* eassumption. *) now symmetry.
      admit. (* eassumption. *) now symmetry. *)
Admitted. *)

(* Lemma normalize_acnv `{gLtsObaFW P A} (p : P) s : p ⇓ s <-> p ⇓ ⟪ s ⟫.
Proof. split; [eapply normalize_acnv_l | eapply normalize_acnv_r]. Qed. *)

Lemma asyn_iff_bhv `{
  @gLtsObaFW P A H gLtsEqP gLtsObaP, !FiniteImagegLts P A, AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳P _ gLtsT,
  @gLtsObaFW Q A H gLtsEqQ gLtsObaQ, !FiniteImagegLts Q A, AbsQT : @AbsAction Q T FinA PreAct A H Φ 𝝳Q _ gLtsT}
  : forall (p : P) (q : Q), p ≼ₙₒᵣₘ₋ₐₛ q <-> p ≼ₐₛ q.
Proof.
  intros p q. split.
  - intros (hl1 & hl2). split.
    + clear hl2. intros s hacnv. revert p q hl1 hacnv. induction s.
      * intros; simpl ;eauto. rewrite<- norm_nil.
        eapply hl1. rewrite norm_nil. exact hacnv.
      * intros. constructor.
        -- assert (p ⇓ []) as Hyp.
           { constructor. inversion hacnv; subst ;eauto. }
           rewrite<- norm_nil in Hyp. eapply hl1 in Hyp.
           rewrite norm_nil in Hyp. inversion Hyp; subst; eauto.
        -- intros.
           assert (exists p', p ⟹{a} p') as (p' & wk_tr).
           { admit. }
           eapply IHs; eauto.
           ++ intro. intros. eapply cnv_preserved_by_wt_act;eauto. 
           ++ assert (p' ⇓ s) as Hyp_conv'.
              { eapply cnv_preserved_by_wt_act ; eauto. }
              exact Hyp_conv'.
      eapply hl1 in hacnv.
      eapply normalize_acnv_r in hacnv.
      eauto.
    + intros s q' hacnv hw st.
      eapply normalize_acnv_l in hacnv as hacnv'.
      eapply normalize_wta_r in hw as hw'.
      destruct hw' as (q0 & w0 & sc).
      set (h0 := stable_preserved_by_eq q' q0  st (symmetry sc)).
      destruct (hl2 (normalize s) q0 hacnv' ltac:(eauto with mdb))
        as (p' & w' & sc' & sub). eassumption.
      
      (* eapply normalize_wta_l in w' as (p0 & wp0 & scp). *)
      
      exists p'. repeat split.
      * admit. (* eassumption. *)
      * eapply stable_preserved_by_eq;eauto. reflexivity.
      * rewrite pre_act_of_eq; eauto. assert (q0 ⋍ q') as eq; eauto.
        eapply pre_act_of_eq in eq. rewrite<- eq. exact sub.
        reflexivity.
  - intros (hl1 & hl2). split.
    + intros s hacnv. eauto.
    + intros nt q' hacnv w st. eauto.
Qed.

      
      exists p0. repeat split. eassumption.
      eapply stable_preserved_by_eq;eauto. symmetry. eassumption.
      rewrite pre_act_of_eq; eauto. assert (q0 ⋍ q') as eq; eauto.
      eapply pre_act_of_eq in eq. rewrite<- eq. exact sub.
  - intros (hl1 & hl2). split.
    + intros s hacnv. eauto.
    + intros nt q' hacnv w st. eauto.
Qed.
