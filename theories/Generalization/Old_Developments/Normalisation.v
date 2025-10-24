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

From Coq.Program Require Import Equality.

From stdpp Require Import base countable finite gmap list decidable gmultiset.

From Must Require Import ActTau InputOutputActions OldTransitionSystems FiniteImageLTS 
    gLts Bisimulation Lts_FW Convergence Termination WeakTransitions Must GeneralizeLtsOutputs DefinitionAS.

Definition ntrace L `{Label L} : Type := list (gmultiset L * gmultiset L).

Fixpoint normalize_loop `{Label L} (s : list (ExtAct L)) (mi : gmultiset L) (mo : gmultiset L)
  : ntrace L :=
  match s with
  | [] => [(mi, mo)]
  | ActIn a :: s' =>
      normalize_loop s' ({[+ a +]} ⊎ mi) mo
  | ActOut a :: ActIn b :: s' =>
      (mi , {[+ a +]} ⊎ mo) :: normalize_loop s' {[+ b +]} ∅
  | ActOut a :: s' =>
      normalize_loop s' mi ({[+ a +]} ⊎ mo)
  end.

Definition normalize `{Label L} (s : trace (ExtAct L)) : ntrace L :=
  match s with
  | [] => []
  | _ => normalize_loop s ∅ ∅
  end.

Fixpoint linearize `{Label L} (nt : ntrace L) : trace (ExtAct L) :=
  match nt with
  | [] => []
  | (mi, mo) :: nt' =>
      let inputs := map ActIn (elements mi) in
      let outputs := map ActOut (elements mo) in
      inputs ++ outputs ++ linearize nt'
  end.

Definition linorm `{Label L}  s := linearize (normalize s).

Notation "⟪ s ⟫" := (linearize (normalize s)).

Notation "⌈ mi , mo ⌉₁" := (map ActIn (elements mi) ++ map ActOut (elements mo)).

Notation "⌈ nt ⌉" := (linearize nt).

Lemma norm_loop_nil `{Label L} s mi mo : normalize_loop s mi mo <> [].
Proof.
  revert mi mo.
  induction s; eauto. destruct a; eauto.
  destruct s; eauto. destruct e; eauto.
Qed.

Lemma norm_nil `{Label L} s : normalize s = [] -> s = [].
Proof.
  dependent induction s.
  - eauto.
  - unfold normalize. intro eq. now eapply norm_loop_nil in eq.
Qed.

Lemma norm_loop_output_output_step `{Label L} a b s mi mo :
  normalize_loop (ActOut a :: ActOut b :: s) mi mo = normalize_loop (ActOut b :: s) mi ({[+ a +]} ⊎ mo).
Proof. eauto. Qed.

Lemma norm_loop_output_input_step `{Label L} a b s mi mo :
  normalize_loop (ActOut a :: ActIn b :: s) mi mo = (mi, {[+ a +]} ⊎ mo) :: normalize (ActIn b :: s).
Proof.
  intros. simpl. now rewrite gmultiset_disj_union_right_id.
Qed.

Lemma norm_loop_input_step `{Label L} s a mi mo :
  normalize_loop (ActIn a :: s) mi mo = normalize_loop s ({[+ a +]} ⊎ mi) mo.
Proof. eauto. Qed.

Lemma norm_sub `{Label L} s mi mo I O nt :
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
Qed.

Lemma norm_input_mem `{Label L} :
  forall s a mi mo I O nt,
    normalize_loop (ActIn a :: s) mi mo = (I, O) :: nt ->
    a ∈ I.
Proof.
  intros.
  rewrite norm_loop_input_step in H0.
  eapply norm_sub in H0. multiset_solver.
Qed.

Lemma norm_output_mem `{HL : Label L} s a mi mo I O nt :
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

Lemma norm_extend_mi `{HL : Label L} :
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
Qed.

Lemma norm_extend_mo `{HL : Label L} :
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
Qed.

Lemma normalize_loop_mi `{HL : Label L} :
  forall s a mi mo I O nt, normalize_loop (ActOut a :: s) mi mo = (I, O) :: nt -> mi = I.
Proof.
  dependent induction s.
  - simpl. intros. now inversion H.
  - intros.
    destruct a.
    + rewrite norm_loop_output_input_step in H.
      now inversion H.
    + eauto.
Qed.

Lemma norm_shape `{HL : Label L} : forall s,
    normalize s = []
    \/ exists I O s1 s2 s', normalize s = (I,O) :: normalize s'
                      /\ s = s1 ++ s2 ++ s'
                      /\ are_inputs s1
                      /\ are_outputs s2
                      /\ map ActIn (elements I) ≡ₚ s1
                      /\ map ActOut (elements O) ≡ₚ s2.
Proof.
  induction s as [|μ s].
  - eauto.
  - destruct μ.
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
Qed.

Lemma norm_perm `{HL : Label L} : forall nt s1 s2,
    normalize s1 = nt -> normalize s2 = nt -> s1 ≡ₚ s2.
Proof.
  intros nt.
  induction nt.
  - intros s1 s2 H1 H2.
    eapply norm_nil in H1, H2. now subst.
  - intros s1 s2 H1 H2.
    destruct a as (mi & mo).
    destruct (norm_shape s1).
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
    eapply (IHnt s03 s13 H7 eq_refl).
Qed.

Lemma norm_length `{HL : Label L} :
  forall s I O s',
    normalize s = (I, O) :: normalize s' ->
    length s' < length s.
Proof.
  intro s.
  dependent induction s.
  - intros. inversion H.
  - intros.
    destruct (norm_shape (a :: s)).
    now eapply norm_loop_nil in H0.
    destruct H0 as (mi' & mo' & s1 & s2 & s'' & e0 & e1 & e3 & e4 & e5 & e6).
    assert (exists a, a ∈ s1 ++ s2) as (b & mem).
    destruct a.
    exists (ActIn a). eapply elem_of_app. left.
    eapply elem_of_Permutation_proper. symmetry. eassumption.
    eapply elem_of_list_fmap. exists a. split; eauto.
    eapply gmultiset_elem_of_elements.
    now eapply norm_input_mem in e0.
    exists (ActOut a). eapply elem_of_app. right.
    eapply elem_of_Permutation_proper. symmetry. eassumption.
    eapply elem_of_list_fmap. exists a. split; eauto.
    eapply gmultiset_elem_of_elements.
    now eapply norm_output_mem in e0.
    rewrite e1, app_assoc, app_length.
    eapply elem_of_Permutation in mem as (s0 & eqp) .
    replace (length (s1 ++ s2)) with (length (b :: s0)).
    replace (length s') with (length s'').
    eapply PeanoNat.Nat.lt_add_pos_l, Nat.lt_0_succ.
    eapply Permutation_length.
    rewrite e0 in H. inversion H.
    now eapply norm_perm.
    eapply Permutation_length. now symmetry.
Qed.

Require Import Wellfounded.

Theorem normalize_wta_r `{LtsObaFW A L} : forall s (p : A) q, p ⟹[s] q -> p ⟹⋍[ ⟪s⟫] q.
Proof.
  induction s
    as (s & Hlength)
         using
         (well_founded_induction (wf_inverse_image _ nat _ List.length PeanoNat.Nat.lt_wf_0)).
  destruct s.
  - intros p q w. simpl. exists q. split. eauto with mdb. reflexivity.
  - intros p q w.
    destruct (norm_shape (e :: s)).
    now eapply norm_loop_nil in H3.
    destruct H3
      as (mi & mo & s1 & s2 & s' & e0 & e1 & e3 & e4 & e5 & e6).
    subst.
    rewrite e0.
    simpl.
    rewrite e1 in w.
    eapply wt_split in w as (t & w1 & w2).
    eapply wt_split in w2 as (r & w2 & w3).
    assert (hl : length s' < length (e :: s)).
    eapply norm_length in e0. eassumption.
    set (h := Hlength s' hl r q w3).
    eapply wt_join_eq.
    eapply (wt_input_perm s1);eauto.
    admit. (* eassumption. *)
    now symmetry. eapply wt_join_eq.
    eapply (wt_non_blocking_action_perm s2); eauto.
    admit. (* eassumption. *)
    now symmetry.  eassumption.
Admitted.

Lemma are_inputs_map_ActIn `{Label L} (s : list L) : are_inputs (map ActIn s).
Proof.
  induction s; simpl.
  eapply Forall_nil. eapply Forall_cons. now exists a. eassumption.
Qed.

Lemma are_outputs_map_ActOut `{Label L} (s : list L) : are_outputs (map ActOut s).
Proof.
  induction s; simpl.
  eapply Forall_nil. eapply Forall_cons. now exists a. eassumption.
Qed.

Lemma normalize_wta_l `{LtsObaFW A L} : forall s (p : A) q, p ⟹[⟪s⟫] q -> p ⟹⋍[s] q.
Proof.
   induction s
    as (s & Hlength)
         using
         (well_founded_induction (wf_inverse_image _ nat _ List.length PeanoNat.Nat.lt_wf_0)).
  destruct s.
  - intros p q w. simpl in w. exists q. split. eauto with mdb. reflexivity.
  - intros p q w.
    destruct (norm_shape (e :: s)).
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
    now symmetry. eassumption. eauto.
Admitted.

Lemma normalize_wta `{LtsObaFW A L} s (p : A) q : p ⟹⋍[⟪s⟫] q <-> p ⟹⋍[s] q.
Proof.
  split.
  intros (q' & w & sc).
  eapply normalize_wta_l in w as (q'' & w & sc').
  exists q''. split. eauto with mdb. transitivity q'; now symmetry.
  intros (q' & w & sc).
  eapply normalize_wta_r in w as (q'' & w & sc').
  exists q''. split. eauto with mdb. transitivity q'; now symmetry.
Qed.

Lemma outputs_of_eq `{LtsEq A L} p q : p ⋍ q -> lts_outputs p ≡ lts_outputs q.
Proof.
  intro heq.
  intros a. split.
  intro lh. symmetry in heq.
  eapply lts_outputs_spec2 in lh as (p' & hl).
  edestruct (eq_spec q p') as (q' & hl' & heq'). eauto.
  eapply lts_outputs_spec1. eassumption.
  intro lh.
  eapply lts_outputs_spec2 in lh as (q' & hl).
  edestruct (eq_spec p q') as (p' & hl' & heq'). eauto.
  eapply lts_outputs_spec1. eassumption.
Qed.

Lemma normalize_accs `{LtsObaFW A L, !FiniteLts A L} (p : A) (s : trace (ExtAct L)) h1 h2 :
  (set_map lts_outputs (wt_refuses_set p s h1) : gset (gset L))
  ≡ (set_map lts_outputs (wt_refuses_set p (linorm s) h2) : gset (gset L)).
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
Qed.

Definition bhv_lin_pre_cond1 `{Lts P L, Lts Q L} (p : P) (q : Q) := forall s, p ⇓ linearize s -> q ⇓ linearize s.

Notation "p ⪷₁ q" := (bhv_lin_pre_cond1 p q) (at level 70).

Definition bhv_lin_pre_cond2 `{@Lts P L HL, @Lts Q L HL} (p : P) (q : Q) :=
  forall nt q',
    p ⇓ linearize nt -> q ⟹[linearize nt] q' -> q' ↛ ->
    ∃ p', p ⟹[linearize nt] p' /\ p' ↛ /\ lts_outputs p' ⊆ lts_outputs q'.

Notation "p ⪷₂ q" := (bhv_lin_pre_cond2 p q) (at level 70).

Definition bhv_lin_pre `{@Lts P L HL, @Lts Q L HL} (p : P) (q : Q) := p ⪷₁ q /\ p ⪷₂ q.

Notation "p ⪷ q" := (bhv_lin_pre p q) (at level 70).

Lemma normalize_acnv_l `{LtsObaFW A L} (p : A) s : p ⇓ s -> p ⇓ ⟪ s ⟫.
Proof.
  revert p.
  induction s
    as (s & Hlength)
         using (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
  destruct (norm_shape s).
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
      admit. (* eapply are_inputs_map_ActIn. *) now symmetry.
Admitted.

Lemma normalize_acnv_r `{LtsObaFW A L} (p : A) s : p ⇓ ⟪ s ⟫ -> p ⇓ s.
Proof.
  revert p.
  induction s
    as (s & Hlength)
         using (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
  destruct (norm_shape s).
  - eapply norm_nil in H3. subst. now simpl.
  - destruct H3
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
      admit. (* eassumption. *) now symmetry.
Admitted.

Lemma normalize_acnv `{LtsObaFW A L} (p : A) s : p ⇓ s <-> p ⇓ ⟪ s ⟫.
Proof. split; [eapply normalize_acnv_l | eapply normalize_acnv_r]. Qed.

(* Lemma asyn_iff_bhv
  `{@LtsObaFW P L IL LA LOA V, PreAP : @PreExtAction A H P FinA PreA PreA_eq PreA_countable 𝝳 Φ LtsP,
    @LtsObaFW Q L IL LB LOB W, PreAQ : @PreExtAction A H Q FinA PreA PreA_eq PreA_countable 𝝳 Φ LtsQ
    !FiniteLts Q L, !FiniteLts Q L} : forall (p : P) (q : Q), p ⪷ q <-> p ≼ q.
Proof.
  intros p q. split.
  - intros (hl1 & hl2). split.
    + intros s hacnv.
      eapply normalize_acnv in hacnv. eapply hl1 in hacnv.
      now eapply normalize_acnv in hacnv.
    + intros s q' hacnv hw st.
      eapply normalize_acnv in hacnv.
      eapply normalize_wta_r in hw.
      destruct hw as (q0 & w0 & sc).
      set (h0 := stable_preserved_by_eq q' q0 (symmetry sc) st).
      destruct (hl2 (normalize s) q0 hacnv ltac:(eauto with mdb))
        as (p' & w' & sc' & sub). eassumption.
      eapply normalize_wta_l in w' as (p0 & wp0 & scp).
      exists p0. repeat split. eassumption.
      eapply stable_preserved_by_eq. symmetry. eassumption. eassumption.
      
      eapply retrieve_a_better_pre_order; eauto.
      intros. admit. (* eapply fw_does_all_input. *)
      
      rewrite (outputs_of_eq p0 p'), (outputs_of_eq q' q0); eauto with mdb.
      now symmetry.
  - intros (hl1 & hl2). split.
    + intros s hacnv. eauto.
    + intros nt q' hacnv w st. eauto.
Admitted. *)
