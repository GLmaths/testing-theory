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

Require ssreflect.
Require Import Coq.Unicode.Utf8.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Program.Equality.
Require Import Coq.Wellfounded.Inverse_Image.
Require Import Coq.Logic.JMeq.
Require Import Coq.Program.Wf Setoid.
Require Import Coq.Program.Equality.
From Coq.Logic Require Import ProofIrrelevance.
From stdpp Require Import base countable finite gmap list finite base decidable finite gmap.
From Must Require Import TransitionSystems Must.
From Must Require Import Lift.

(** Test generators specification. *)

Class gen_spec {P A : Type} `{Lts P A, !LtsEq P A, !Good P A good}
  (co_of : A -> A) (gen : list A -> P) := {
            co_inter μ : parallel_inter μ (co_of μ);
                (* co_of μ interragît avec μ *)
            co_inter_spec1 μ μ': 
                parallel_inter μ' (co_of μ)
                          -> μ = μ';
                (* co_of μ n'interragît qu'avec μ *)
    (* 1 *) gen_spec_ungood : 
              forall s, ¬ good (gen s) ;
    (* 2 *) gen_spec_mu_lts_co μ1 (* μ2 *) s :
              gen (μ1 :: s) ⟶⋍[co_of μ1] gen s;
    (* 3 *) gen_spec_out_lts_tau_ex μ s : 
              (* non_blocking μ ->  *) 
              ∃ e', gen (μ :: s) ⟶ e';
    (* 4 *) gen_spec_out_lts_tau_good η s e : 
              (* non_blocking η -> *) 
              gen (η :: s) ⟶ e -> good e;
    (* 5 *) gen_spec_out_lts_mu_uniq {e η μ s} : (* unique ???? *)
              (* non_blocking η ->  *)
              ¬ non_blocking μ ->
              gen (η :: s) ⟶[μ] e -> e ⋍ gen s /\ μ = co_of η;
  }.
  
Lemma gen_spec_determinacy `{
  M1 : LtsOba E A, !Good E A good, !gen_spec co_of f} 
  μ1 s e:
  f (μ1 :: s) ⟶[co_of μ1] e -> e ⋍ f s.
Proof.
  intro HypTr.
  destruct (decide (non_blocking (co_of μ1))) as [nb | not_nb].
  + assert (f (μ1 :: s) ⟶⋍[co_of μ1] f s) as (e' & Tr & Eq). eapply gen_spec_mu_lts_co.
    assert (e' ⋍ e) as equiv. eapply lts_oba_non_blocking_action_deter; eauto.
    etransitivity; eauto. symmetry; eauto.
  + eapply gen_spec_out_lts_mu_uniq in not_nb as (equi & Tr); eauto.
Qed.



Class gen_spec_conv {P A : Type} `{Lts P A, ! LtsEq P A, !Good P A good}
  (co_of : A -> A) (gen_conv : list A -> P) := {
    gen_conv_spec_gen_spec : gen_spec co_of gen_conv ;
    (* c1 *) gen_spec_conv_nil_stable_mu μ : gen_conv [] ↛[μ] ;
    (* c2 *) gen_spec_conv_nil_lts_tau_ex : ∃ e', gen_conv [] ⟶ e';
    (* c2 *) gen_spec_conv_nil_lts_tau_good e : gen_conv [] ⟶ e -> good e;
  }. 

#[global] Existing Instance gen_conv_spec_gen_spec.

Class gen_spec_acc {P : Type} `{Lts P A, ! LtsEq P A, !Good P A good}
  (co_of : A -> A) (gen_acc : (* gset A *)(A -> Prop) -> list A -> P) := {
    gen_acc_spec_gen_spec O : gen_spec co_of (gen_acc O) ;
    (* t1 *) gen_spec_acc_nil_stable_tau O : 
                gen_acc O [] ↛ ;
    (* t2 *) gen_spec_acc_nil_stable_out O η : 
                non_blocking η -> gen_acc O [] ↛[η] ;
  (* t3-> *) gen_spec_acc_nil_mu_inv O μ e : 
                ¬ non_blocking μ -> gen_acc O [] ⟶[μ] e
                    -> (exists η, μ = co_of η /\ O η) ;
  (* t3<- *) gen_spec_acc_nil_mem_lts_inp O η : 
                O η (* η ∈ O *) -> ∃ r μ, gen_acc O [] ⟶[μ] r /\ μ = co_of η;
    (* t4 *) gen_spec_acc_nil_lts_inp_good μ e' O : 
                gen_acc O [] ⟶[μ] e' -> good e' ;
  }.

#[global] Existing Instance gen_acc_spec_gen_spec.

(** Facts about Must *)

Lemma must_preserved_by_weak_nil_srv `{
  LtsP : Lts P A, 
  LtsE : ! Lts E A, ! LtsEq E A, !Good E A good}

  `{@Prop_of_Inter P E A parallel_inter H LtsP LtsE}

  (p q : P) (e : E) : 
  must p e -> p ⟹ q 
    -> must q e.
Proof.
  intros hm w.
  dependent induction w; eauto with mdb.
  eapply IHw; eauto.
  eapply must_preserved_by_lts_tau_srv; eauto.
Qed.

Lemma must_preserved_by_synch_if_notgood `{
  LtsP : Lts P A, 
  LtsE : ! Lts E A, ! LtsEq E A, !Good E A good}

  `{@Prop_of_Inter P E A parallel_inter H LtsP LtsE}

  (p p' : P) (r r' : E) μ μ':
  must p r -> ¬ good r -> parallel_inter μ μ' -> p ⟶[μ] p' -> r ⟶[μ'] r' 
    -> must p' r'.
Proof.
  intros hm u inter l__p l__r.
  inversion hm; subst.
  - contradiction.
  - eapply com; eauto with mdb.
Qed.

(* Facts about test generators. *)

Lemma gen_conv_always_reduces `{
  LtsOba E A, !Good E A good, !gen_spec_conv co_of gen_conv} s :
  ∃ e, gen_conv s ⟶ e.
Proof.
  induction s as [|μ s'].
  - eapply gen_spec_conv_nil_lts_tau_ex.
  - eapply gen_spec_out_lts_tau_ex.
Qed.

Lemma terminate_must_test_conv_nil `{
  LtsP : Lts P A, 
  LtsE : !Lts E A, !LtsEq E A, !Good E A good, !gen_spec_conv co_of gen_conv}

  `{@Prop_of_Inter P E A parallel_inter H LtsP LtsE}

  (p : P) : 
  p ⤓ -> must p (gen_conv []).
Proof.
  intros ht.
  induction ht.
  eapply m_step; eauto with mdb.
  - eapply gen_spec_ungood.
  - destruct gen_spec_conv_nil_lts_tau_ex as (e' & l); eauto with mdb.
  - intros e' l. eapply gen_spec_conv_nil_lts_tau_good in l. eauto with mdb.
  - intros p0 e0 μ μ' inter l1 l2.
    exfalso. eapply lts_stable_spec2.
    exists e0. eassumption. eapply gen_spec_conv_nil_stable_mu.
Qed.

Lemma must_gen_conv_wta_mu `{
  LtsP : Lts P A, 
  LtsE : ! Lts E A, ! LtsEq E A, !Good E A good, ! gen_spec_conv co_of gen_conv}

  `{@Prop_of_Inter P E A parallel_inter H LtsP LtsE}

  μ s (p q : P): 
  must p (gen_conv (μ :: s)) -> 
    p ⟹{μ} q -> must q (gen_conv s).
Proof.
  intros hm w.
  dependent induction w.
  + eapply IHw; eauto with mdb.
    eapply must_preserved_by_lts_tau_srv; eauto.
  + edestruct gen_spec_mu_lts_co as (t' & hlt' & heqt').
    (* edestruct gen_spec_mu_lts_co as (t' & hlt' & heqt'). *)
    eapply (must_eq_client _ _ _ heqt').
    eapply (must_preserved_by_weak_nil_srv q t); eauto.
    eapply must_preserved_by_synch_if_notgood; eauto with mdb.
    eapply gen_spec_ungood. eapply co_inter.
Qed.

(** First implication of the first requirement. *)

Lemma cnv_if_must `{
  LtsP : Lts P A, 
  LtsE : !Lts E A, !LtsEq E A, !Good E A good, !gen_spec_conv co_of gen_conv}

  `{@Prop_of_Inter P E A parallel_inter H LtsP LtsE}

  s (p : P) : 
  must p (gen_conv s) -> p ⇓ s.
Proof.
  revert p.
  induction s as [|μ s']; intros p hm.
  - eapply cnv_nil.
    eapply (must_terminate_ungood _ _ hm), gen_spec_ungood.
  - eapply cnv_act.
    + eapply (must_terminate_ungood _ _ hm), gen_spec_ungood.
    + intros q w. eapply IHs', must_gen_conv_wta_mu; eauto.
Qed.

Lemma f_gen_lts_mu_in_the_middle `{
  LtsOba P A, !Good P A good, !gen_spec co_of f} 
  s1 s2 μ:
  Forall exist_co_nba s1
    -> f (s1 ++ μ :: s2) ⟶⋍[co_of μ] f (s1 ++ s2).
Proof.
  revert s2 μ.
  induction s1 as [|ν s']; intros s2 μ his ; simpl in *.
  - eapply (gen_spec_mu_lts_co μ).
  - inversion his as [| ? ? (b & nb & duo) his']. subst.
    destruct (IHs' s2 μ his') as (r & hlr & heqr).
    edestruct (gen_spec_mu_lts_co ν (s' ++ μ :: s2))
      as (t & hlt & heqt).
    assert (non_blocking (co_of ν)) as nb'. eapply nb_not_nb; eauto.
    assert (b = co ν). eapply unique_nb; eauto. subst.
    eapply co_inter.
    edestruct (eq_spec t r) as (u & hlu & hequ). eauto with mdb.
    destruct (lts_oba_non_blocking_action_delay nb' hlt hlu)
      as (v & l1 & (t' & l2 & heq')).
    exists v. split. eassumption.
    destruct (gen_spec_mu_lts_co ν (s' ++ s2)) as (w & hlw & heqw).
    eapply lts_oba_non_blocking_action_deter_inv; try eassumption.
    etrans. eauto. etrans. eauto. etrans. eauto. now symmetry.
Qed.

Lemma f_gen_lts_mu_in_the_middle' `{
  LtsOba P A, !Good P A good, !gen_spec co_of f} 
  s1 s2 μ p:
  Forall exist_co_nba s1
    -> f (s1 ++ μ :: s2) ⟶⋍[co_of μ] p -> p ⋍ f (s1 ++ s2).
Proof.
  revert s2 μ p.
  induction s1 as [|ν s']; intros s2 μ p his HypTr; simpl in *.
  - destruct (decide (non_blocking (co_of μ))) as [nb | not_nb].
    + assert (f ([] ++ μ :: s2) ⟶⋍[co_of μ] f ([] ++ s2)) as HypTr'.
      eapply f_gen_lts_mu_in_the_middle. eauto.
      destruct HypTr as (e & HypTr & equiv).
      destruct HypTr' as (e' & HypTr' & equiv').
      simpl in *. assert (e ⋍ e').
      eapply lts_oba_non_blocking_action_deter; eauto. 
      etransitivity. symmetry. exact equiv. etransitivity; eauto.
    + destruct HypTr as (e & HypTr & equiv).
      assert (e ⋍ f s2 /\ co_of μ = co_of μ) as (equiv' & eq'). 
      eapply gen_spec_out_lts_mu_uniq; eauto.
      etransitivity. symmetry. exact equiv. eauto.
  - inversion his; subst.
    destruct (decide (non_blocking (co_of μ))) as [nb | not_nb].
    + assert (f ((ν :: s') ++ μ :: s2) ⟶⋍[co_of μ] f ((ν :: s') ++ s2)) as HypTr'.
      eapply f_gen_lts_mu_in_the_middle. eauto.
      destruct HypTr as (e & HypTr & equiv).
      destruct HypTr' as (e' & HypTr' & equiv').
      simpl in *. assert (e ⋍ e').
      eapply lts_oba_non_blocking_action_deter; eauto. 
      etransitivity. symmetry. exact equiv. etransitivity; eauto.
    + destruct HypTr as (e & HypTr & equiv).
      assert (e ⋍ f (s' ++ μ :: s2) /\ co_of μ = co_of ν) as (equiv' & eq'). 
      eapply gen_spec_out_lts_mu_uniq; eauto. 
      
      assert (μ = ν). eapply co_inter_spec1. rewrite eq'. eapply co_inter.
      subst.
      
      
      destruct H3 as (ν' & nb & duo).
      
      assert (non_blocking (co_of ν)). eapply nb_not_nb; eauto. eapply co_inter.
      contradiction.
Qed.

Lemma inversion_gen_mu_not_nb `{
  M1 : LtsOba E A, !Good E A good, !gen_spec co_of f} 
  s μ' p :
  (forall μ, f [] ↛[μ] \/ (forall e, f [] ⟶[μ] e -> good e)) ->
  f s ⟶[μ'] p ->
  ¬ non_blocking μ' -> 
  ¬ good p ->
  ∃ s1 s2 μ, s = s1 ++ μ :: s2 /\ p ⋍ f (s1 ++ s2) /\ μ' = co_of μ /\ Forall exist_co_nba s1.
Proof.
  revert μ' p.
  induction s
    as (s & Hlength) using
         (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
  destruct s as [|ν s']; intros μ p h l not_nb not_happy.
  - edestruct (h μ) as [stable_f | f_to_good].
    + now eapply lts_stable_spec2 in stable_f; eauto.
    + assert (good p). eapply f_to_good. eauto. contradiction.
  - destruct (gen_spec_out_lts_mu_uniq not_nb l); subst.
    exists [], s', ν. simpl. repeat split; simpl; eauto with mdb.
Qed.


Lemma inversion_gen_mu_nb `{
  M1 : LtsOba E A, !Good E A good, !gen_spec co_of f} 
  s μ p :
  (forall μ, f [] ↛[μ] \/ (forall e, f [] ⟶[μ] e -> good e)) ->
  f s ⟶[μ] p ->
  non_blocking μ -> 
  ¬ good p ->
  ∃ s1 s2 μ', s = s1 ++ μ' :: s2 /\ p ⋍ f (s1 ++ s2) /\ μ = co_of μ' /\ Forall exist_co_nba s1.
Proof.
  revert μ p.
  induction s
    as (s & Hlength) using
         (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
  destruct s as [|ν s']; intros μ p h l nb not_happy.
  - edestruct (h μ); eauto.
    + now eapply lts_stable_spec2 in H0; eauto.
    + eapply H0 in l; eauto. contradiction.
  - (* destruct (decide (non_blocking ν)) as [nb'| not_nb']. *)
    + edestruct (gen_spec_mu_lts_co ν s') as (r & hlr & heqr).
      destruct (decide (co_of ν = μ)) as [eq | not_eq].
      ++ subst. exists [], s', ν. repeat split; simpl; eauto with mdb.
         transitivity r; eauto. eapply (lts_oba_non_blocking_action_deter nb l hlr); eauto.
      ++ destruct (lts_oba_non_blocking_action_confluence nb not_eq l hlr )
           as (t' & l2 & (t & l1 & heq)).
         destruct (eq_spec (f s') t (ActExt $ μ)) as (v & hlv & heqv).
         exists r. split; eauto with mdb. now symmetry.
         destruct (decide (good v)) as [happy' | not_happy'].
         +++ exfalso. assert (good (f s')). 
             eapply good_preserved_by_lts_non_blocking_action_converse; eauto.
             assert (¬ good (f s')). eapply gen_spec_ungood. contradiction.
         +++ edestruct (Hlength s' ltac:(eauto) μ v h hlv nb not_happy')
             as (s1' & s2' & μ' & eq0 & eq1 & eq2 & eq3); eauto. subst.
             destruct (decide (non_blocking (co_of ν))) as [nb' | not_nb'].
             ++++ assert (¬ non_blocking ν) as not_nb''.
                  eapply lts_oba_fw_non_blocking_duo_spec; eauto. eapply co_inter.
                  
                  assert (Forall exist_co_nba (ν :: s1')) as Hyp.
                  constructor. esplit; eauto. split ;eauto. eapply co_inter. eauto.
                  
                  exists (ν :: s1'), s2', μ'. repeat split; eauto.
                  
                  edestruct (f_gen_lts_mu_in_the_middle (ν :: s1') s2' ν)
               as (r' & hlr' & heqr').
                  eauto.
                  edestruct (gen_spec_mu_lts_co ν (s1' ++ s2'))
               as (w & hlw & heqw).
                  eapply lts_oba_non_blocking_action_deter_inv; try eassumption.
                  transitivity t. symmetry. eassumption.
                  transitivity v. now symmetry.
                  transitivity (f (s1' ++ s2')). eassumption. now symmetry.
            ++++ assert (¬ non_blocking μ') as not_nb''.
                 eapply lts_oba_fw_non_blocking_duo_spec; eauto. eapply co_inter.
                 
                 assert (r ⋍ f (s1' ++ μ' :: s2')) as equiv. eapply gen_spec_determinacy; eauto.
                 
                 assert (¬ good r) as not_happy''. assert (¬ good (f (s1' ++ μ' :: s2'))) as not_happy'''.
                 eapply gen_spec_ungood. eapply ungood_preserved_by_eq; eauto. 
                 
                 assert (f (ν :: s1' ++ μ' :: s2') ⟶[co_of ν] r) as HypTr; eauto.
                 eapply (inversion_gen_mu_not_nb (ν :: s1' ++ μ' :: s2') (co_of ν) r) in HypTr ; eauto.
                 
                 destruct HypTr.

Admitted.


(* Lemma inversion_gen_mu `{
  M1 : LtsOba E A, !Good E A good, !gen_spec co_of f} 
  s μ' p :
  (forall μ, f [] ↛[μ] \/ (forall e, f [] ⟶[μ] e -> good e)) ->
  f s ⟶[μ'] p ->
  non_blocking μ' -> 
  ¬ good p ->
  ∃ s1 s2 μ, s = s1 ++ μ :: s2 /\ p ⋍ f (s1 ++ s2) /\ μ' = co_of μ /\ Forall exist_co_nba s1.
Proof.
  revert μ' p.
  induction s
    as (s & Hlength) using
         (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
  destruct s as [|ν s']; intros μ p h l nb not_happy.
  - edestruct (h μ) as [stable_f | f_to_good].
    + now eapply lts_stable_spec2 in stable_f; eauto.
    + exfalso. eapply not_happy. eapply f_to_good; eauto.
  - edestruct (gen_spec_mu_lts_co ν s') as (r & hlr & heqr).
      destruct (decide (co_of ν = μ)) as [eq | neq].
      ++ subst.
         exists [], s', ν. repeat split; simpl; eauto with mdb.
         transitivity r; eauto. 
         eapply (lts_oba_non_blocking_action_deter nb l hlr); eauto.
      ++ destruct (lts_oba_non_blocking_action_confluence nb neq l hlr )
           as (p' & l2 & r' & l1 & heq).
         destruct (eq_spec (f s') r' (ActExt $ μ)) as (v & hlv & heqv).
         exists r. split; eauto with mdb. now symmetry.
         destruct (decide (good v)) as [happy' | not_happy'].
         +++ exfalso. assert (good (f s')). 
             eapply good_preserved_by_lts_non_blocking_action_converse; eauto.
             assert (¬ good (f s')). eapply gen_spec_ungood. contradiction.
         +++ edestruct (Hlength s' ltac:(eauto) μ v h hlv nb not_happy')
             as (s1' & s2' & μ' & eq0 & eq1 & eq2 & eq3); eauto.
             
             
              
             assert (r ⋍ f(s')) as equiv'. eapply gen_spec_determinacy; eauto.
             symmetry in equiv'. edestruct (eq_spec (f s') r') as (r'' & HypTr'' & equiv''). 
             exists r; eauto. subst.
             assert (¬ non_blocking μ') as not_nb. 
             eapply lts_oba_fw_non_blocking_duo_spec; eauto. eapply co_inter.
             assert (Forall exist_co_nba (μ' :: s1')).
             constructor. exists (co_of μ'). split; eauto. eapply co_inter. eauto.
             exists (ν :: s1'). exists s2'. exists μ'.
             split. eauto. 
             split. 
             destruct (decide (non_blocking ν)) as [nb' | not_nb'].
             + admit.
             + eapply inversion_gen_mu_nb in hlr.
             
              
             
             
         right.
         exists [], s', ν.
         repeat split; eauto. simpl.
                  
         +++ (*right. exists (ActIn b :: s1'), s2'. repeat split; eauto.
             destruct μ; subst; eauto.
             edestruct (f_gen_lts_mu_in_the_middle (ActIn b :: s1') s2' (ActIn b))
               as (r' & hlr' & heqr').
             eapply Forall_cons. split; eauto. eexists. reflexivity.
             edestruct (gen_spec_mu_lts_co (ActIn b) (s1' ++ s2'))
               as (w & hlw & heqw).
             eapply lts_oba_output_deter_inv; try eassumption.
             transitivity t. eassumption.
             transitivity v. now symmetry.
             transitivity (f (s1' ++ s2')). eassumption. now symmetry.
             eapply Forall_cons. split; eauto. eexists. reflexivity. *) admit.
Qed.

  
  
  
  
  destruct (decide (non_blocking μ)) as [nb | not_nb].
    + edestruct (gen_spec_mu_lts_co ν s') as (r & hlr & heqr).
      destruct (decide (non_blocking (co_of ν))) as [nb' | not_nb'].
      ++ subst.
         right. exists [], s', ν. repeat split; simpl; eauto with mdb.
         transitivity r; eauto. admit. 
         (* eapply (lts_oba_non_blocking_action_deter nb l hlr); eauto. *)
         (* +++ destruct (decide (non_blocking (co_of ν))) as [nb' | not_nb'].
             ++++ left.
                  eapply good_preserved_by_lts_non_blocking_action_converse. exact nb'.
                  exact l2. eapply good_preserved_by_eq; eauto.
                  transitivity r' ; now symmetry. *)
      ++ assert (co_of ν ≠ μ) as neq. eapply BlockingAction_are_not_non_blocking; eauto.
         destruct (lts_oba_non_blocking_action_confluence nb neq l hlr )
           as (p' & l2 & r' & l1 & heq).
         destruct (eq_spec (f s') r' (ActExt $ μ)) as (v & hlv & heqv).
         exists r. split; eauto with mdb. now symmetry.
         edestruct (Hlength s' ltac:(eauto) μ v h hlv)
           as [hg | (s1' & s2' & eq0 & eq1 & eq2)]; eauto.
         right.
                  exists [], s', ν.
                  repeat split; eauto. simpl.
                  
         +++ (*right. exists (ActIn b :: s1'), s2'. repeat split; eauto.
             destruct μ; subst; eauto.
             edestruct (f_gen_lts_mu_in_the_middle (ActIn b :: s1') s2' (ActIn b))
               as (r' & hlr' & heqr').
             eapply Forall_cons. split; eauto. eexists. reflexivity.
             edestruct (gen_spec_mu_lts_co (ActIn b) (s1' ++ s2'))
               as (w & hlw & heqw).
             eapply lts_oba_output_deter_inv; try eassumption.
             transitivity t. eassumption.
             transitivity v. now symmetry.
             transitivity (f (s1' ++ s2')). eassumption. now symmetry.
             eapply Forall_cons. split; eauto. eexists. reflexivity. *) admit.
    + right.
      destruct (gen_spec_out_lts_mu_uniq not_nb l); subst.
      exists [], s', ν. simpl. repeat split; simpl; eauto with mdb.













  revert μ' p.
  induction s
    as (s & Hlength) using
         (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
  destruct s as [|ν s']; intros μ p h l.
  - edestruct (h μ) as [stable_f | f_to_good].
    + now eapply lts_stable_spec2 in stable_f; eauto.
    + eauto.
  - destruct (decide (non_blocking μ)) as [nb | not_nb].
    + edestruct (gen_spec_mu_lts_co ν s') as (r & hlr & heqr).
      destruct (decide (non_blocking (co_of ν))) as [nb' | not_nb'].
      ++ subst.
         right. exists [], s', ν. repeat split; simpl; eauto with mdb.
         transitivity r; eauto. admit. 
         (* eapply (lts_oba_non_blocking_action_deter nb l hlr); eauto. *)
         (* +++ destruct (decide (non_blocking (co_of ν))) as [nb' | not_nb'].
             ++++ left.
                  eapply good_preserved_by_lts_non_blocking_action_converse. exact nb'.
                  exact l2. eapply good_preserved_by_eq; eauto.
                  transitivity r' ; now symmetry. *)
      ++ assert (co_of ν ≠ μ) as neq. eapply BlockingAction_are_not_non_blocking; eauto.
         destruct (lts_oba_non_blocking_action_confluence nb neq l hlr )
           as (p' & l2 & r' & l1 & heq).
         destruct (eq_spec (f s') r' (ActExt $ μ)) as (v & hlv & heqv).
         exists r. split; eauto with mdb. now symmetry.
         edestruct (Hlength s' ltac:(eauto) μ v h hlv)
           as [hg | (s1' & s2' & eq0 & eq1 & eq2)]; eauto.
         right.
                  exists [], s', ν.
                  repeat split; eauto. simpl.
                  
         +++ (*right. exists (ActIn b :: s1'), s2'. repeat split; eauto.
             destruct μ; subst; eauto.
             edestruct (f_gen_lts_mu_in_the_middle (ActIn b :: s1') s2' (ActIn b))
               as (r' & hlr' & heqr').
             eapply Forall_cons. split; eauto. eexists. reflexivity.
             edestruct (gen_spec_mu_lts_co (ActIn b) (s1' ++ s2'))
               as (w & hlw & heqw).
             eapply lts_oba_output_deter_inv; try eassumption.
             transitivity t. eassumption.
             transitivity v. now symmetry.
             transitivity (f (s1' ++ s2')). eassumption. now symmetry.
             eapply Forall_cons. split; eauto. eexists. reflexivity. *) admit.
    + right.
      destruct (gen_spec_out_lts_mu_uniq not_nb l); subst.
      exists [], s', ν. simpl. repeat split; simpl; eauto with mdb.


  - right. destruct (decide (non_blocking μ)) as [nb | not_nb].
    + (* exists ν, s'. repeat split; simpl; eauto with mdb.*) admit.
    + destruct (gen_spec_out_lts_mu_uniq not_nb l) as (equiv & eq); subst.
      exists ν, s'. repeat split; simpl; eauto with mdb.
      eapply co_inter.
Qed.
 *)
Lemma inversion_gen_mu_gen_conv `{
  M1 : LtsOba E A, !Good E A good, !gen_spec_conv co_of f}
  s μ p :
  f s ⟶[μ] p ->
  good p \/ 
  ∃ s1 s2 μ', s = s1 ++ μ' :: s2 /\ p ⋍ f (s1 ++ s2) /\ μ = co_of μ' /\ Forall exist_co_nba s1.
Proof.
  intros. 
  destruct (decide (good p)) as [happy | not_happy].
  + left; eauto.
  + right. 
    destruct (decide (non_blocking μ)) as [nb | not_nb]. 
    ++ eapply inversion_gen_mu_nb; eauto.
       intros. left. eapply gen_spec_conv_nil_stable_mu; eauto.
    ++ eapply inversion_gen_mu_not_nb; eauto.
       intros. left. eapply gen_spec_conv_nil_stable_mu; eauto.
Qed.

Lemma inversion_gen_mu_gen`{
  M1 : LtsOba E A, !Good E A good, !gen_spec_acc co_of f} 
  s μ p O :
  f O s ⟶[μ] p ->
  good p \/ 
  ∃ s1 s2 μ', s = s1 ++ μ' :: s2 /\ p ⋍ f O (s1 ++ s2) /\ μ = co_of μ' /\ Forall exist_co_nba s1.
Proof.
  intros. 
  destruct (decide (good p)) as [happy | not_happy].
  + left; eauto.
  + right. 
    destruct (decide (non_blocking μ)) as [nb | not_nb]. 
    ++ eapply inversion_gen_mu_nb; eauto.
       intros. left. eapply gen_spec_conv_nil_stable_mu; eauto.
    ++ eapply inversion_gen_mu_not_nb; eauto.
       intros. left. eapply gen_spec_conv_nil_stable_mu.
       
    Unshelve. eauto.
     eauto.  eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.


Definition not_non_blocking `{ExtAction A} μ := ¬ non_blocking μ.

Lemma inversion_gen_tau `{
  M1 : LtsOba E A, !Good E A good, !gen_spec co_of f}
  s q :
  (f [] ↛ \/ (forall e, f [] ⟶ e -> good e)) ->
  (forall μ, f [] ↛[μ] \/ (forall e, f [] ⟶[μ] e -> good e)) ->
  f s ⟶ q ->
  good q. (* \/ (∃ μ μ' (s1 : list A) s2 s3, s = s1 ++ [μ] ++ s2 ++ [μ'] ++ s3
                          /\ parallel_inter μ μ'
                          /\ q ⋍ f (s1 ++ s2 ++ s3)
                          /\ ¬ non_blocking μ
                          /\ Forall (not_non_blocking) s1 
                          /\ Forall (not_non_blocking) s2). *)
Proof.
  revert q. induction s as [|μ s']; intros q h1 h2 l.
  - destruct h1 as [stable_f | f_to_good].
    + eauto. now eapply lts_stable_spec2 in stable_f ; eauto.
    + eauto. 
  - eapply gen_spec_out_lts_tau_good; eauto.
Qed.

Lemma inversion_gen_tau_gen_conv `{
  M1 : LtsOba E A, !Good E A good, !gen_spec_conv co_of f} 
  s q :
  f s ⟶ q ->
  good q (* \/ (∃ μ s1 s2 s3, s = s1 ++ [μ] ++ s2 ++ [co μ] ++ s3
                          /\ q ⋍ f (s1 ++ s2 ++ s3)
                          /\ is_input μ /\ are_inputs s1 /\ are_inputs s2) *).
Proof.
  intros.
  eapply inversion_gen_tau; eauto.
  right. eapply gen_spec_conv_nil_lts_tau_good.
  intro μ. left. eapply gen_spec_conv_nil_stable_mu.
Qed.

(* Lemma inversion_gen_tau_gen_acc
  `{M1 : LtsOba A L, !Good A L good, !gen_spec_acc f} s O q :
  f O s ⟶ q ->
  good q \/ (∃ μ s1 s2 s3, s = s1 ++ [μ] ++ s2 ++ [co μ] ++ s3
                          /\ q ⋍ f O (s1 ++ s2 ++ s3)
                          /\ is_input μ /\ are_inputs s1 /\ are_inputs s2).
Proof.
  intros.
  eapply inversion_gen_tau; eauto.
  left. eapply gen_spec_acc_nil_stable_tau.
  intro μ. right.
  intros.  eapply gen_spec_acc_nil_lts_inp_good; eauto.
Qed. *)

(** Converse implication of the first requirement. *)

Lemma must_if_cnv `{
  @LtsObaFW P A H LtsP LtsEqP V,
  @LtsObaFB E A H LtsE LtsEqE W, !Good E A good,
  !gen_spec_conv co_of gen_conv} 

  `{@Prop_of_Inter P E A parallel_inter H LtsP LtsE}

  s (p : P) :
  p ⇓ s -> must p (gen_conv s).
Proof.
  revert p.
  induction s
    as (s & Hlength) using
         (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
  intros p hcnv.
  induction (cnv_terminate p s hcnv) as [p hp IHtp].
  (* destruct (decide (good (gen_conv s))).
  - eapply m_now; eauto.
  -  *) apply m_step.
  + eapply gen_spec_ungood.
  + edestruct gen_conv_always_reduces. eauto with mdb.
  + intros p' l. eapply IHtp; [|eapply cnv_preserved_by_lts_tau]; eauto.
  + intros e' l.
    assert (good e') as happy.
    eapply inversion_gen_tau_gen_conv; eauto.
    eapply m_now; eauto.
  + intros p' e' ν ν' inter hlp hle.
    destruct (inversion_gen_mu_gen_conv s ν' e' hle)
      as [hg | (s1 & s2 & ν'' & heq & sc & eq & his)]; eauto with mdb. subst.
    assert (ν'' = ν). eapply co_inter_spec1; eauto. subst.
    eapply (cnv_drop_in_the_middle p s1 s2) in hlp; subst; eauto with mdb.
    eapply must_eq_client. symmetry. eassumption.
    eapply Hlength; subst; eauto with mdb.
    rewrite 2 app_length. simpl. lia.
(*     destruct s.
    ++ exfalso. 
       assert (gen_conv [] ↛[ν']) as stable.
       eapply gen_spec_conv_nil_stable_mu.
       assert (¬ gen_conv [] ↛[ν']) as not_stable.
       eapply lts_stable_spec2; eauto. 
       contradiction.
    ++ assert (gen_conv (a :: s) ⟶[ν'] e') as hle'; eauto.
       eapply gen_spec_out_lts_mu_uniq in hle' as (equiv' & eq'). subst.
       eapply must_eq_client. symmetry. eassumption.
       eapply Hlength; subst; eauto with mdb.
       eapply co_inter_spec1 in inter. subst.
       assert (p ⟹{ν} p') as weak_tr. eapply lts_to_wt; eauto.
       eapply cnv_preserved_by_wt_act in hcnv; eauto. *)
Qed.

Lemma must_iff_cnv `{
  @LtsObaFW P A H LtsP LtsEqP V,
  @LtsObaFB E A H LtsE LtsEqE W, !Good E A good, 
  !gen_spec_conv co_of gen_conv}

  `{@Prop_of_Inter P E A parallel_inter H LtsP LtsE}

  (p : P) s : must p (gen_conv s) <-> p ⇓ s.
Proof. split; [eapply cnv_if_must | eapply must_if_cnv]; eauto. Qed.

Lemma completeness1 `{
    @LtsObaFW P A H LtsP LtsEqP V,
    @LtsObaFW Q A H LtsQ LtsEqQ T,
    @LtsObaFB E A H LtsE LtsEqE W, !Good E A good,
    ! gen_spec_conv co_of gen_conv}
    
    `{@Prop_of_Inter P E A parallel_inter H LtsP LtsE}
    `{@Prop_of_Inter Q E A parallel_inter H LtsQ LtsE}
    
  (p : P) (q : Q) : p ⊑ q -> p ≼₁ q.
Proof. intros hleq s hcnv. now eapply must_iff_cnv, hleq, must_iff_cnv. Qed.

(** Second requirement for completeness *)

Definition pre_acc_set_of `{Lts P A} (p : P) (μ : A) : Prop := ¬ lts_stable p (ActExt μ).

Definition acc_set_of `{Lts P A} (p : P) : A -> Prop := pre_acc_set_of p.

Definition oas `{FiniteImageLts P A} (p : P) (s : list A) (hcnv : p ⇓ s) : list (A -> Prop) :=
  let ps : list P := elements (wt_stable_set p s hcnv) in
  (* ⋃  *) map acc_set_of ps.

Lemma exists_forall_in {B} (ps : list B) (P : B -> Prop) (Q : B -> Prop)
  (h : forall p, p ∈ ps -> P p \/ Q p) : Exists P ps \/ Forall Q ps.
Proof.
  induction ps as [|p ?]. eauto.
  destruct IHps; destruct (h p); eauto; set_solver.
Qed.

Lemma exists_forall_in_gset `{Countable B} (ps : gset B) (P : B -> Prop) (Q : B -> Prop)
  (h : forall p, p ∈ ps -> P p \/ Q p) : (exists p, p ∈ ps /\ P p)\/ (forall p, p ∈ ps -> Q p).
Proof.
  induction ps using set_ind_L. set_solver.
  destruct IHps; destruct (h x); eauto; set_solver.
Qed.

Lemma wt_acceptance_set_subseteq
  `{FiniteImageLts P A} μ s p q hacnv1 hacnv2 :
  p ⟹{μ} q ->
  map acc_set_of (elements (wt_stable_set q s hacnv1)) ⊆
    map acc_set_of (elements (wt_stable_set p (μ :: s) hacnv2)).
Proof.
  intros.
  intros a in__a.
  assert (wt_stable_set q s hacnv1 ⊆ wt_stable_set p (μ :: s) hacnv2).
  intros t in__t.
  eapply wt_stable_set_spec2.
  eapply wt_stable_set_spec1 in in__t.
  destruct in__t. split; eauto with mdb.
  eapply wt_push_left; eauto.
  set_solver.
Qed.

Lemma lts_tau_acceptance_set_subseteq `{FiniteImageLts P A} s p q hacnv1 hacnv2 :
  p ⟶ q ->
  map acc_set_of (elements $ wt_stable_set q s hacnv1) ⊆
    map acc_set_of (elements $ wt_stable_set p s hacnv2).
Proof.
  intros.
  intros a in__a.
  assert (wt_stable_set q s hacnv1 ⊆ wt_stable_set p s hacnv2).
  intros t in__t.
  eapply wt_stable_set_spec2.
  eapply wt_stable_set_spec1 in in__t.
  destruct in__t. split; eauto with mdb.
  set_solver.
Qed.

(* Definition `{ExtAction A} (Acc1 : list (A -> Prop)) (Acc1 : list (A -> Prop)) 
          := forall X , X ∈ Acc1  gset P.  *)

Lemma union_wt_acceptance_set_subseteq `{FiniteImageLts P A} μ s p q h1 h2 :
    p ⟹{μ} q -> oas q s h1 ⊆ oas p (μ :: s) h2.
Proof.
  intros hw a Hyp. 
  eapply wt_acceptance_set_subseteq; eauto.
(*   (O & mem1 & mem2)%elem_of_union_list.
  eapply elem_of_union_list.
  exists O. split; eauto. eapply wt_outputs_subseteq; eauto. *)
Qed.

Lemma union_acceptance_set_lts_tau_subseteq `{FiniteImageLts P A} s p q h1 h2 :
  p ⟶ q -> oas q s h1 ⊆ oas p s h2.
Proof.
  intros hw a Hyp. 
  eapply lts_tau_acceptance_set_subseteq; eauto.
Qed.

Lemma aft_output_must_gen_acc `{
  @LtsOba P A H LtsP LtsEqP, 
  @LtsOba E A H LtsE LtsEqE, !Good E A good, !gen_spec_acc co_of gen_acc}

  `{@Prop_of_Inter P E A parallel_inter H LtsP LtsE}

  (p : P) μ s O :
  p ⤓ -> (forall q, p ⟹{μ} q -> must q (gen_acc O s)) 
              -> must p (gen_acc O (μ :: s) : E).
Proof.
  intros tp hmq. induction tp.
  eapply m_step.
  - eapply gen_spec_ungood.
  - edestruct (@gen_spec_out_lts_tau_ex E A); eauto with mdb.
    now destruct gen_spec_acc0.
  - intros. eapply H4. eassumption. intros.
    eauto with mdb.
  - intros e' l. eapply m_now.
    apply (gen_spec_out_lts_tau_good μ s e'). eassumption.
  - intros p' e' μ' μ'' inter l0 l1.
    eapply gen_spec_out_lts_mu_uniq in l1 as (h1 & h2). subst.
    eapply must_eq_client. symmetry; eauto.
    eapply hmq. eapply co_inter_spec1 in inter. subst. eauto with mdb.
    
    Unshelve. exact O.
Qed.

(* Lemma gen_acc_tau_ex
  `{M1 : LtsObaFB A L, !Good A L good, !gen_spec_acc f} s1 s2 s3 μ O :
  is_input μ -> are_inputs s1 -> are_inputs s2 ->
  f O (s1 ++ [μ] ++ s2 ++ [co μ] ++ s3) ⟶⋍ f O (s1 ++ s2 ++ s3).
Proof.
  intros.
  assert (f O (s1 ++ [μ] ++ s2 ++ [co μ] ++ s3) ⟶⋍[co μ]
            f O (s1 ++ s2 ++ [co μ] ++ s3)) as (e1 & l1 & heq1).
  eapply (@f_gen_lts_mu_in_the_middle A L _ _ _ _ _ _ (f O) _
            s1 (s2 ++ [co μ] ++ s3) μ); simpl in *; eauto.
  assert (f O (s1 ++ s2 ++ [co μ] ++ s3) ⟶⋍[co (co μ)]
            f O ((s1 ++ s2) ++ s3)) as (e2 & l2 & heq2).
  replace (s1 ++ s2 ++ [co μ] ++ s3) with ((s1 ++ s2) ++ [co μ] ++ s3).
  eapply (@f_gen_lts_mu_in_the_middle A L _ _ _ _ _ _ (f O) _
            (s1 ++ s2) s3 (co μ)); simpl in *; eauto.
  unfold are_inputs. eapply Forall_app; eauto.
  now rewrite <- app_assoc.
  rewrite co_involution in l2.
  destruct H2 as (a & eq). subst. simpl in *.
  edestruct (eq_spec e1 e2) as (e' & l' & heq'). eauto.
  destruct (lts_oba_fb_feedback l1 l') as (t & lt & heqt); eauto.
  exists t. split; eauto.
  rewrite <- app_assoc in heq2.
  transitivity e'. eauto.
  transitivity e2; eauto.
Qed. *)

(* Lemma must_f_gen_a_subseteq_non_blocking `{
  @LtsObaFB E A H LtsE LtsEqE W, !Good E A good, !gen_spec_acc gen_acc} 
  s e η O1 :
  non_blocking η -> gen_acc O1 s ⟶[η] e -> forall O2, (forall μ, O1 μ -> O2 μ) 
    -> exists t, gen_acc O2 s ⟶[η] t.
Proof.
  revert e O1.
  induction s as [|μ s']; intros e O1 nb l O2 hsub.
  + exfalso. eapply lts_stable_spec2, gen_spec_acc_nil_stable_out. eauto. eauto.
  + destruct (decide (non_blocking μ)) as [nb' | not_nb'].
    ++ edestruct
         (@gen_spec_mu_lts_co E A _ _ _ _ _ (gen_acc O2) _ μ s')
         as (r' & hl' & heqr').
       edestruct (gen_spec_out_lts_mu_uniq l). subst. 
       (* assert (parallel_inter μ (co_of μ)) as inter. eapply co_inter.
       exfalso. *) admit.
    ++ edestruct
        (@gen_spec_mu_lts_co E A _ _ _ _ _ (gen_acc O1) _ μ s')
        as (e1 & hle1 & heqe1). (* simpl in hle1. *)
       edestruct
         (@gen_spec_mu_lts_co E A _ _ _ _ _ (gen_acc O2) _ μ s')
         as (e2 & hle2 & heqe2). (* simpl in hle2. *)
       destruct (decide (a = b)); subst; eauto.
       assert (neq : ActOut a ≠ ActOut b) by now inversion 1.
       destruct (lts_oba_output_confluence neq hle1 l) as
         (r1 & l1 & r2 & l2 & heq).
       edestruct (eq_spec (gen_acc O1 s') r1) as (e' & hle' & heqe').
       symmetry in heqe1. eauto.
       eapply IHs' in hle' as (t & hlt).
       edestruct (eq_spec e2 t) as (e2' & hle2' & heqe2'). eauto.
       edestruct (lts_oba_output_commutativity hle2 hle2') as (v & l3 & l4).
       eauto with mdb. eassumption.
Qed. *)

Lemma must_f_gen_a_subseteq `{
  @LtsObaFB E A H LtsE LtsEqE W, !Good E A good, !gen_spec_acc co_of gen_acc} 
  s e μ O1 :
  gen_acc O1 s ⟶[μ] e -> forall O2, (forall μ, O1 μ -> O2 μ) -> exists t, gen_acc O2 s ⟶[μ] t.
Proof.
  revert e O1.
  induction s as [|μ' s']; intros e O1 l O2 hsub.
  + destruct (decide (non_blocking μ)) as [nb | not_nb].
    ++ rename μ into η. exfalso.
       eapply lts_stable_spec2, gen_spec_acc_nil_stable_out. eauto. eauto.
    ++ eapply gen_spec_acc_nil_mu_inv in not_nb as (μ' & inter & mem); eauto.
       eapply hsub in mem. 
       eapply gen_spec_acc_nil_mem_lts_inp in mem as (t & μ'' & HypTr & eq).
       subst. exists t. eauto.
  + edestruct
        (@gen_spec_mu_lts_co E A _ _ _ _ _ co_of (gen_acc O1) _ μ' s')
        as (e1 & hle1 & heqe1).
    edestruct
         (@gen_spec_mu_lts_co E A _ _ _ _ _ co_of (gen_acc O2) _ μ' s')
         as (e2 & hle2 & heqe2).
    eapply 
  
  
  eapply gen_spec_out_lts_mu_uniq in l as (equiv & eq). subst.
    exists (gen_acc O2 s').
    apply gen_spec_mu_lts_co.
    
  
  assert (exists e,  gen_acc O2 (μ' :: s') ⟶[μ] e -> e ⋍ gen_acc O2 s' /\ μ = co_of μ') as sol.
    eexists. eapply gen_spec_out_lts_mu_uniq.
    destruct sol as (e' & Hyp).
    exists e'. eauto.
    
    
  
    destruct μ as [b|b].
    ++ edestruct
        (@gen_spec_mu_lts_co B L _ _ _ _ _ (gen_acc O1) _ (ActIn b) s')
        as (r & hl & heqr). simpl in hl.
       assert (neq : ActIn a ≠ ActOut b) by now inversion 1.
       destruct (lts_oba_output_confluence neq hl l) as
         (r1 & l1 & r2 & l2 & heq).
       edestruct (eq_spec (gen_acc O1 s') r1) as (e' & hle' & heqe').
       symmetry in heqr. eauto.
       eapply IHs' in hle' as (t & hlt).
       edestruct
         (@gen_spec_mu_lts_co B L _ _ _ _ _ (gen_acc O2) _ (ActIn b) s')
         as (r' & hl' & heqr'). simpl in hl'.
       edestruct (eq_spec r' t) as (e2 & hle2 & heqe2). eauto.
       edestruct (lts_oba_output_commutativity hl' hle2) as (v & l3 & l4).
       eauto with mdb. eassumption.
    ++ edestruct
         (@gen_spec_mu_lts_co B L _ _ _ _ _ (gen_acc O2) _ (ActOut b) s')
         as (r' & hl' & heqr').
       edestruct (gen_spec_out_lts_mu_uniq l); eauto. subst.
       assert (a = b) by now inversion H1. subst. eauto.
Qed.

Lemma must_f_gen_a_subseteq_tau
  `{@LtsObaFB B L IL LB LOB W, !Good B L good, !gen_spec_acc gen_acc}
  s e O1 : gen_acc O1 s ⟶ e -> forall O2, O1 ⊆ O2 -> exists t, gen_acc O2 s ⟶ t.
Proof.
  revert e O1.
  induction s as [|μ s']; intros e O1 l O2 hsub.
  + exfalso. eapply lts_stable_spec2, gen_spec_acc_nil_stable_tau; eauto.
  + destruct μ as [a|a].
    ++ edestruct
        (@gen_spec_mu_lts_co B L _ _ _ _ _ (gen_acc O1) _ (ActIn a) s')
        as (r & hl & heqr). simpl in hl.
       destruct (lts_oba_output_tau hl l) as [(r1 & l1 & (r2 & l2 & heq))|].
       +++ edestruct (eq_spec (gen_acc O1 s') r1) as (e' & hle' & heqe').
           symmetry in heqr. eauto.
           eapply IHs' in hle' as (t & hlt).
           edestruct
             (@gen_spec_mu_lts_co B L _ _ _ _ _ (gen_acc O2) _ (ActIn a) s')
             as (r' & hl' & heqr'). simpl in hl'.
           edestruct (eq_spec r' t) as (e2 & hle2 & heqe2). eauto.
           edestruct (lts_oba_output_commutativity hl' hle2) as (v & l3 & l4).
           eauto with mdb. eassumption.
       +++ edestruct H0 as (r' & hl' & heq').
           edestruct (eq_spec (gen_acc O1 s') r') as (t & hlt & heqt).
           symmetry in heqr. eauto.
           edestruct (must_f_gen_a_subseteq_input s' t a O1 hlt O2 hsub).
           edestruct
             (@gen_spec_mu_lts_co B L _ _ _ _ _ (gen_acc O2) _ (ActIn a) s')
             as (u & hlu & hequ).
           edestruct (eq_spec u x) as (t' & hlt' & heqt'). eauto.
           edestruct (lts_oba_fb_feedback hlu hlt'); eauto.
           firstorder.
    ++ eapply gen_spec_out_lts_tau_ex.
Qed.

Lemma must_f_gen_a_subseteq_nil
  `{@Lts A L IL, @LtsObaFB B L IL LB LOB W, !Good B L good, !gen_spec_acc gen_acc}
  (p : A) O1 : must p (gen_acc O1 []) -> forall O2, O1 ⊆ O2 -> must p (gen_acc O2 []).
Proof.
  intros hm.
  assert (hpt : p ⤓)
    by now (eapply must_terminate_ungood, gen_spec_ungood; eauto).
  induction hpt. dependent induction hm; intros O2 hsub.
  - now eapply gen_spec_ungood in H1.
  - eapply m_step; eauto with mdb.
    + eapply gen_spec_ungood.
    + destruct ex as ((p' & e') & l').
      inversion l'; subst.
      +++ eauto with mdb.
      +++ exfalso. eapply lts_stable_spec2, gen_spec_acc_nil_stable_tau; eauto.
      +++ destruct α1 as [[b|b]|]; destruct α2 as [[a|a]|]; inversion eq; subst.
          exfalso. eapply lts_stable_spec2, gen_spec_acc_nil_stable_out; eauto.
          eapply gen_spec_acc_nil_mu_inv, hsub, gen_spec_acc_nil_mem_lts_inp
            in l2 as (e & l).
          eauto with mdb.
    + intros e l.
      exfalso. eapply lts_stable_spec2, gen_spec_acc_nil_stable_tau; eauto.
    + intros p' e' μ l1 l2.
      eapply gen_spec_acc_nil_lts_inp_good in l1. eauto with mdb.
Qed.

Lemma must_f_gen_a_subseteq
  `{@Lts A L IL,
    @LtsObaFB B L IL LB LOB W, !Good B L good,
    !gen_spec_acc gen_acc} s (p : A) O1 :
  must p (gen_acc O1 s) -> forall O2, O1 ⊆ O2 -> must p (gen_acc O2 s).
Proof.
  revert p O1.
  induction s
    as (s & Hlength) using
         (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
  destruct s as [|ν s']; intros p O1 hm O2 hsub; subst.
  - eapply must_f_gen_a_subseteq_nil; eauto.
  - assert (htp : p ⤓) by (eapply must_terminate_ungood, gen_spec_ungood; eauto).
    induction htp.
    inversion hm. now eapply gen_spec_ungood in H3.
    eapply m_step; eauto with mdb.
    + eapply gen_spec_ungood.
    + destruct ex as (t & l). inversion l; subst; eauto with mdb.
      ++ eapply must_f_gen_a_subseteq_tau in l0 as (e & hle); eauto with mdb.
      ++ destruct α1 as [[b|b]|]; destruct α2 as [[a|a]|]; inversion eq; subst.
         eapply must_f_gen_a_subseteq_output in l2 as (t & hl); eauto with mdb.
         eapply must_f_gen_a_subseteq_input in l2 as (t & hl); eauto with mdb.
    + intros e' l.
      edestruct inversion_gen_tau_gen_acc as [|H3]; eauto with mdb.
      destruct H3 as (μ & s1 & s2 & s3 & heqs & sc & himu & his1 & his2).
      eapply (must_eq_client p (gen_acc O2 (s1 ++ s2 ++ s3))). now symmetry.
      edestruct (gen_acc_tau_ex s1 s2 s3 μ O1) as (t & hlt & heqt); eauto.
      eapply Hlength; eauto.
      ++ rewrite heqs, 6 app_length. simpl. lia.
      ++ eapply must_eq_client. eapply heqt. eapply et. now rewrite heqs.
    + intros p' e' μ l1 l2.
      edestruct inversion_gen_mu_gen_acc as [|H3]; eauto with mdb.
      destruct H3 as (s1 & s2 & heqs & heq & his1).
      eapply must_eq_client. symmetry. eassumption.
      edestruct @f_gen_lts_mu_in_the_middle as (t & l & heq'); eauto.
      now destruct gen_spec_acc0.
      eapply Hlength. rewrite heqs.
      rewrite 2 app_length. simpl. lia.
      eapply must_eq_client. eapply heq'.
      eapply com. rewrite heqs. eassumption.
      now rewrite co_involution. eassumption.
Qed.

Lemma must_gen_acc_stable
  `{@LtsOba A L IL LA LOA, @LtsOba B L IL LB LOB, !Good B L good, !gen_spec_acc gen_acc}
  (p : A) O : p ↛ -> must p (gen_acc (lts_outputs p ∖ O) []) \/ lts_outputs p ⊆ O.
Proof.
  intros.
  remember (lts_outputs p ∖ O) as D.
  destruct D as [|a D'] using set_ind_L.
  + right. set_solver.
  + left.
    eapply m_step.
    ++ now eapply gen_spec_ungood.
    ++ edestruct (gen_spec_acc_nil_mem_lts_inp ({[a]} ∪ D') a)
         as (t & l0). set_solver.
       assert (mem : a ∈ lts_outputs p). set_solver.
       eapply lts_outputs_spec2 in mem as (r & l).
       exists (r, t).
       eapply (ParSync (ActExt $ ActOut a) (ActExt $ ActIn a)); simpl; eauto.
    ++ intros p' l'. exfalso. eapply (@lts_stable_spec2 A); eauto with mdb.
    ++ intros e' l'. exfalso.
       eapply (@lts_stable_spec2 B L _ _ (gen_acc ({[a]} ∪ D') []) τ); eauto with mdb.
       eapply gen_spec_acc_nil_stable_tau.
    ++ intros p' e' μ l0 l1.
       destruct μ.
       eapply gen_spec_acc_nil_lts_inp_good in l0. eauto with mdb.
       exfalso.
       eapply (@lts_stable_spec2 B); eauto with mdb.
       eapply gen_spec_acc_nil_stable_out.
Qed.

Lemma must_gen_a_with_nil
  `{@LtsObaFW A L IL LA LOA V, @LtsObaFB B L IL LB LOB W,
    !FiniteLts A L, !Good B L good,
    !gen_spec_acc gen_acc} (p : A) (hcnv : p ⇓ []) O :
  (exists p', p ⟹ p' /\ lts_stable p' τ /\ lts_outputs p' ⊆ O)
  \/ must p (gen_acc (oas p [] hcnv ∖ O) []).
Proof.
  induction (cnv_terminate p [] hcnv) as (p, hpt, ihhp).
  destruct (decide (lts_stable p τ)) as [st | (p' & l)%lts_stable_spec1].
  - destruct (must_gen_acc_stable p O st).
    + right. unfold oas.
      rewrite wt_stable_set_stable_singleton, elements_singleton; eauto.
      simpl. rewrite union_empty_r_L. set_solver.
    + left. eauto with mdb.
  - assert
      (h : ∀ q,
          q ∈ lts_tau_set p ->
          (exists p', q ⟹ p' ∧ lts_stable p' τ ∧ lts_outputs p' ⊆ O) ∨
            (exists h, must q (gen_acc (oas q [] h ∖ O) []))).
    intros q l'%lts_tau_set_spec.
    destruct (hpt q l') as (hq).
    edestruct (ihhp q l') as [hl | hr].
    now left. right. exists (cnv_nil _ (tstep q hq)). eauto.
    destruct (@exists_forall_in A (lts_tau_set p) _ _ h).
    + eapply Exists_exists in H1 as (t & l'%lts_tau_set_spec & t' & w & st & sub).
      left. exists t'. eauto with mdb.
    + right. eapply m_step.
      ++ eapply gen_spec_ungood.
      ++ eauto with mdb.
      ++ intros p0 l0%lts_tau_set_spec.
         eapply Forall_forall in H1 as (h0 & hm).
         eapply must_f_gen_a_subseteq; eauto.
         eapply difference_mono_r, union_outputs_lts_tau_subseteq; eauto.
         now eapply lts_tau_set_spec. eassumption.
      ++ intros e' l'. exfalso.
         eapply (@lts_stable_spec2 B). eauto. eapply gen_spec_acc_nil_stable_tau.
      ++ intros p0 e0 μ le%gen_spec_acc_nil_lts_inp_good lp; eauto with mdb.
Qed.

Lemma must_gen_a_with_s
  `{@LtsObaFW A L IL LA LOA V, @LtsObaFB B L IL LB LOB W,
    !FiniteLts A L, !Good B L good, !gen_spec_acc gen_acc} s (p : A) (hcnv : p ⇓ s) O :
  (exists p', p ⟹[s] p' /\ lts_stable p' τ /\ lts_outputs p' ⊆ O) \/ must p (gen_acc (oas p s hcnv ∖ O) s).
Proof.
  revert p hcnv O.
  induction s as [|μ s'].
  - eapply must_gen_a_with_nil.
  - intros p hcnv O.
    set (ps := wt_set_mu p μ s' hcnv).
    inversion hcnv; subst.
    assert (hcnv0 : forall p', p' ∈ ps -> p' ⇓ s') by (intros ? mem%wt_set_mu_spec1; eauto).
    assert (he : ∀ p', p' ∈ ps ->
                      (exists pr p0, p0 ∈ wt_stable_set p' s' pr ∧ lts_outputs p0 ⊆ O)
                      ∨ (exists h, must p' (gen_acc (oas p' s' h ∖ O) s'))).
    intros p' mem.
    destruct (IHs' p' (hcnv0 _ mem) O) as [(r & w & st & sub)| hm].
    left. eapply wt_set_mu_spec1 in mem.
    exists (H5 _ mem), r. split; [eapply wt_stable_set_spec2 |]; eauto.
    right. eauto.
    destruct (exists_forall_in_gset ps _ _ he).
    + left. destruct H1
        as (p1 & ?%wt_set_mu_spec1 & ? & r & (? & ?)%wt_stable_set_spec1 & ?).
      exists r. repeat split; eauto. eapply wt_push_left; eauto.
    + right. destruct μ. inversion hcnv; subst.
      ++ destruct (lts_oba_fw_forward p a) as (p' & l0 & l1).
         assert (gen_acc (oas p (ActIn a :: s') hcnv ∖ O) (ActIn a :: s')
                   ⟶⋍[co $ ActIn a] gen_acc (oas p (ActIn a :: s') hcnv ∖ O) s')
           as (e' & hle' & heqe') by eapply gen_spec_mu_lts_co.
         eapply must_output_swap_l_fw. eauto. eauto.
         eapply (must_eq_client _ _ _ (symmetry heqe')).
         edestruct (H1 p') as (? & hm).
         eapply wt_set_mu_spec2; eauto with mdb.
         eapply must_f_gen_a_subseteq, difference_mono_r, union_wt_outputs_subseteq; eauto with mdb.
      ++ eapply aft_output_must_gen_acc; eauto.
         intros p' hw. edestruct (H1 p') as (? & hm).
         eapply wt_set_mu_spec2; eauto.
         eapply must_f_gen_a_subseteq, difference_mono_r, union_wt_outputs_subseteq; eauto with mdb.
Qed.

Lemma not_must_gen_a_without_required_output
  `{@LtsObaFW A L IL LA LOA V, @LtsObaFB B L IL LB LOB W,
    !Good B L good, !gen_spec_acc gen_acc} (q q' : A) s O :
  q ⟹[s] q' -> q' ↛ -> ¬ must q (gen_acc (O ∖ lts_outputs q') s).
Proof.
  intros wt hst.
  dependent induction wt; intros hm.
  - inversion hm; subst.
    ++ contradict H1. eapply gen_spec_ungood.
    ++ destruct ex as (t & l). inversion l; subst.
       +++ eapply (lts_stable_spec2 p τ); eauto with mdb.
       +++ exfalso. eapply lts_stable_spec2, gen_spec_acc_nil_stable_tau; eauto.
       +++ destruct α1 as [[b|b]|]; destruct α2 as [[a|a]|]; inversion eq; subst.
           eapply lts_stable_spec2, gen_spec_acc_nil_stable_out; eauto.
           eapply gen_spec_acc_nil_mu_inv in l2.
           eapply lts_outputs_spec1 in l1. set_solver.
  - eapply (IHwt hst), (must_preserved_by_lts_tau_srv p q _ hm l).
  - eapply (IHwt hst).
    assert (gen_acc (O ∖ lts_outputs t) (μ :: s) ⟶⋍[co μ]
              gen_acc (O ∖ lts_outputs t) s) as (e' & hle' & heqe').
    by eapply gen_spec_mu_lts_co.
    eapply must_eq_client; eauto.
    inversion hm; subst. now eapply gen_spec_ungood in H1. destruct μ; eauto.
Qed.

Lemma completeness2
  `{@LtsObaFW A L IL LA LOA V, @LtsObaFB B L IL LB LOB W,
    @LtsObaFW C L IL LC LOC VC,
    !FiniteLts A L, !FiniteLts C L, !Good B L good, !gen_spec_acc gen_acc}
  (p : A) (q : C) : p ⊑ q -> p ≼₂ q.
Proof.
  intros hpre s q' hacnv w st.
  destruct (must_gen_a_with_s s p hacnv (lts_outputs q')) as [|hm] ; eauto.
  eapply hpre in hm. contradict hm.
  eapply not_must_gen_a_without_required_output; set_solver.
Qed.

Lemma completeness_fw
  `{@LtsObaFW A L IL LA LOA V, @LtsObaFW B L IL LB LOB W, @LtsObaFB C L IL LC LOC VC,
    !FiniteLts A L, !FiniteLts B L, !FiniteLts C L, !Good C L good,
    !gen_spec_conv gen_conv, !gen_spec_acc gen_acc}
  (p : A) (q : B) : p ⊑ q -> p ≼ q.
Proof. intros. split. now apply completeness1. now apply completeness2. Qed.

Lemma completeness
  `{@LtsObaFB A L IL LA LOA V, @LtsObaFB B L IL LB LOB W, @LtsObaFB C L IL LC LOC VC,
    !FiniteLts A L, !FiniteLts B L, !FiniteLts C L, !Good C L good,
    !gen_spec_conv gen_conv, !gen_spec_acc gen_acc}
  (p : A) (q : B) : p ⊑ q -> p ▷ ∅ ≼ q ▷ ∅.
Proof.
  intros hctx.
  eapply completeness_fw.
  now rewrite <- Lift.lift_fw_ctx_pre.
Qed.
