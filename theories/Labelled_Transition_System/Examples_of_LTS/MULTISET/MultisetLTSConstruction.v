(*
   Copyright (c) 2024 Nomadic Labs
   Copyright (c) 2024 Paul Laforgue <paul.laforgue@nomadic-labs.com>
   Copyright (c) 2024 Léo Stefanesco <leo.stefanesco@mpi-sws.org>
   Copyright (c) 2025 Gaëtan Lopez <glopez@irif.fr>

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

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Program Require Import Equality.
From stdpp Require Import finite gmap gmultiset.
From TestingTheory Require Import ActTau gLts InteractionBetweenLts Bisimulation Lts_OBA Lts_OBA_FB Lts_FW.

(** ** Mailbox LTS *)

(** A mailbox is a multiset of actions *)

Definition MO (A : Type) `{ExtAction A} := gmultiset A.

Lemma Prop_for_nb `{ExtAction A} (η : A) (m : MO A) :
    non_blocking η -> (forall η', η' ∈ m -> non_blocking η')
      -> (forall η'', η'' ∈ ({[+ η +]} ⊎ m) -> non_blocking η'').
Proof.
  intros nb nb_for_MO.
  intros η'' mem.
  destruct (decide (η'' ∈ m)) as [mem' | not_mem'].
  + exact (nb_for_MO η'' mem').
  + assert (η'' = η). multiset_solver. subst.
    eauto.
Qed.

Inductive lts_multiset_step `{ExtAction A} : MO A -> Act A -> MO A -> Prop :=
| lts_multiset_add m η μ (duo : dual μ η) (nb : non_blocking η) :
   lts_multiset_step m (ActExt μ) ({[+ η +]} ⊎ m) 
| lts_multiset_minus m η (nb : non_blocking η):  
   lts_multiset_step ({[+ η +]} ⊎ m) (ActExt η) m.

Global Hint Constructors lts_multiset_step:mdb.

Lemma non_blocking_action_in_ms `{ExtAction A}  mb1 η mb2 :  
  non_blocking η -> lts_multiset_step mb1 (ActExt η) mb2 
    ->  {[+ η +]} ⊎ mb2 = mb1.
Proof.
  intros nb Hstep.
  inversion Hstep as [ ? μ ? duo nb'|]; subst.
  + simpl in *. 
    assert (nb'' : non_blocking μ); eauto.
    apply dual_blocks in duo; eauto. contradiction.
  + eauto.
Qed.

Lemma blocking_action_in_ms `{ExtAction A}  mb1 β mb2 :  
  blocking β -> lts_multiset_step mb1 (ActExt β) mb2 
    ->  ({[+ co β +]} ⊎ mb1 = mb2 /\ (dual β (co β) /\ non_blocking (co β))).
Proof.
  intros nb Hstep.
  inversion Hstep as [ ? η ? duo nb'|]; subst.
  + assert (η =  co β) as eq. eapply unique_nb;eauto. subst. eauto.
  + contradiction.
Qed.

Definition lts_multiset_step_decidable `{ExtAction A} m α m' : Decision (lts_multiset_step m α m').
Proof.
  destruct α as [μ |].
  + destruct (decide (non_blocking μ)) as [nb | not_nb].
    - rename μ into η. destruct (decide ((m =  {[+ η +]} ⊎ m'))); subst.
      ++ left. eapply lts_multiset_minus; eauto.
      ++ right. intro. eapply non_blocking_action_in_ms in nb; eauto.
    - destruct (decide (∃ η', non_blocking η' /\ dual μ η')) as [exists_dual | not_exists_dual].
      ++ destruct (decide (({[+ (co μ) +]} ⊎ m = m') )) as [eq | not_eq].
         +++ left. destruct exists_dual as (η' & nb & duo).
             assert (η' = co μ) as eq'.
             { eapply unique_nb; eauto. } subst. eauto with mdb. 
         +++ right. intro. eapply blocking_action_in_ms in not_nb as (eq'' & Hyp) ; eauto.
      ++ right. intro HypTr. 
         eapply blocking_action_in_ms in not_nb as (eq & duo & nb); eauto; subst.
  + right. inversion 1.
Qed.

Definition lts_multiset_refuses `{ExtAction A} (m : MO A) (α : Act A): Prop := 
match α with
    | ActExt η => if (decide (non_blocking η)) then if (decide (η ∈ m)) then False
                                                                        else True
                                               else forall η', dual η η' -> blocking η'
    | τ => True
end.

Definition lts_multiset_refuses_decidable `{ExtAction A} m α : Decision (lts_multiset_refuses m α).
Proof.
  destruct α as [μ |].
  + simpl in *. destruct (decide (non_blocking μ)) as [nb | not_nb].
    - rename μ into η. destruct (decide (η ∈ m)) as [in_mem | not_in_mem].
      ++ right. intro. eauto.
      ++ left. eauto. 
    - destruct (decide (∃ η', non_blocking η' /\ dual μ η' )) as [exists_dual | not_exists_dual].
      ++ right. intro imp. destruct exists_dual as (η & nb & duo). destruct (imp η); eauto.
      ++ left. eauto.
  + left. simpl. eauto.
Qed.

#[global] Program Instance MbgLts `{H : ExtAction A} : gLts (MO A) H :=
{|
    lts_step m α m' := lts_multiset_step m α m' ;
    lts_refuses p := lts_multiset_refuses p;
    lts_step_decidable m α m' := lts_multiset_step_decidable m α m';
    lts_refuses_decidable m α := lts_multiset_refuses_decidable m α;
  |}.
Next Obligation.
  intros ? ? m α not_refuses; simpl in *.
  destruct α.
  - simpl in *. destruct (decide (non_blocking μ)) as [nb | not_nb].
    + rename μ into η. destruct (decide (η ∈ m)).
      ++ assert (m = {[+ η +]} ⊎ (m ∖ {[+ η +]})) as eq. multiset_solver.
         exists (m ∖ {[+ η +]}). rewrite eq at 1. eapply lts_multiset_minus; eauto.
      ++ exfalso. eauto.
    + destruct (decide (∃ η' : A, non_blocking η' ∧ dual μ η')) as [exist | not_exists ].
      ++ exists ({[+ co μ +]} ⊎ m). destruct exist as (η & nb & duo).
         eapply unique_nb in duo as eq; eauto;subst.
         constructor; eauto.  
      ++ exfalso. eapply not_refuses. eauto.
  - simpl in *. exfalso. eauto.
Qed.
Next Obligation.
  intros ? ? m α not_refuses; simpl in *.
  destruct α.
  + intro refuses. simpl in *. destruct (decide (non_blocking μ)) as [nb | not_nb].
    ++ destruct (decide (μ ∈ m)) as [in_mem | not_in_mem]. 
      +++ eauto. 
      +++ destruct not_refuses as (q & HypTr). 
          eapply non_blocking_action_in_ms in nb;eauto; subst. 
          multiset_solver.
    ++ destruct not_refuses as (q & HypTr).
       eapply blocking_action_in_ms in not_nb as Hyp;eauto; subst.
       destruct Hyp as (eq & duo & nb). subst.
       eapply refuses in duo as not_nb'. eauto.
  + intro impossible. destruct not_refuses as (q & HypTr). inversion HypTr.
Qed.

(*************************** Mailbox purification of blocking actions *********************************)

Fixpoint MO_without_not_nb_on_list `{ExtAction A} (l : list A) : MO A:=
match l with
| [] => empty : MO A
| η :: l' => if (decide (non_blocking η)) then {[+ η +]} ⊎ (MO_without_not_nb_on_list l')
                                          else MO_without_not_nb_on_list l'
end.

Lemma lts_MO_nb_on_list_spec1 `{H : ExtAction A} η l: 
  non_blocking η ->  
    MO_without_not_nb_on_list (η :: l) = {[+ η +]} ⊎ MO_without_not_nb_on_list l.
Proof.
  intro nb.
  unfold MO_without_not_nb_on_list at 1.
  erewrite decide_True. fold MO_without_not_nb_on_list. reflexivity. eauto.
Qed.

Lemma lts_MO_nb_on_list_spec2 `{H : ExtAction A} β l: 
  blocking β ->  
    MO_without_not_nb_on_list (β :: l) = MO_without_not_nb_on_list l.
Proof.
  intro nb.
  unfold MO_without_not_nb_on_list at 1.
  erewrite decide_False. fold MO_without_not_nb_on_list. reflexivity. eauto.
Qed.

Lemma lts_MO_nb_on_list_perm `{H : ExtAction A} (l1 : list A) (l2 : list A) :
  l1 ≡ₚ l2 -> MO_without_not_nb_on_list l1 = MO_without_not_nb_on_list l2.
Proof.
  intro equiv.
  revert l1 l2 equiv.
  dependent induction l1.
  + intros. eapply Permutation_nil in equiv. rewrite equiv. simpl. reflexivity.
  + intro l2. intros. revert l1 IHl1 equiv. dependent induction l2.
    ++ intros. symmetry in equiv. eapply Permutation_nil in equiv. 
       rewrite equiv. simpl. reflexivity.
    ++ intros. destruct (decide (a = a0)) as [eq | not_eq].
       +++ subst. eapply Permutation_cons_inv in equiv.
           destruct (decide (non_blocking a0)) as [nb | not_nb].
           ++++ erewrite lts_MO_nb_on_list_spec1; eauto.
                erewrite lts_MO_nb_on_list_spec1; eauto.
                f_equal. eauto.
           ++++ erewrite lts_MO_nb_on_list_spec2; eauto.
                erewrite lts_MO_nb_on_list_spec2; eauto.
       +++ assert (a0 ∈ a :: l1). eapply list_elem_of_In.
           symmetry in equiv.
           eapply Permutation_in ;eauto. set_solver.
           assert (a0 ∈ l1) as mem. set_solver.
           eapply elem_of_Permutation in mem as (l'1 & Hyp1).
           assert (a ∈ a0 :: l2). eapply list_elem_of_In.
           eapply Permutation_in ;eauto. set_solver.
           assert (a ∈ l2) as mem. set_solver.
           eapply elem_of_Permutation in mem as (l'2 & Hyp2). 
           assert (a :: a0 :: l'1 ≡ₚ a0 :: a :: l'1) as Hyp'. eapply perm_swap.
           assert (a0 :: a :: l'2 ≡ₚ a0 :: l2). eapply perm_skip. 
           symmetry ;eauto. assert (a :: l1 ≡ₚ a :: a0 :: l'1). eapply perm_skip. eauto.
           assert (a0 :: a :: l'2 ≡ₚ a0 :: a :: l'1) as eq'.
           etransitivity; eauto. symmetry in equiv. etransitivity; eauto.
           symmetry in Hyp'. etransitivity; eauto. symmetry ;eauto.
           eapply Permutation_cons_inv in eq'. eapply Permutation_cons_inv in eq'.
           assert (MO_without_not_nb_on_list (a :: l'2) = MO_without_not_nb_on_list l2) as eq1.
           symmetry in Hyp2. eapply IHl2; eauto. intros.
           assert (l1 ≡ₚ a0 :: l'2) as hyp1. etransitivity; eauto.
           eapply Permutation_cons; eauto. symmetry; eauto.
           assert (l1 ≡ₚ a0 :: l0) as hyp2. etransitivity; eauto.
           eapply IHl1 in hyp1. eapply IHl1 in hyp2.
           unfold MO_without_not_nb_on_list in hyp1 at 2.
           unfold MO_without_not_nb_on_list in hyp2 at 2.
           destruct (decide (non_blocking a0)) as [nb' | not_nb'].
           ++++ fold MO_without_not_nb_on_list in hyp1.
                fold MO_without_not_nb_on_list in hyp2.
                assert ({[+ a0 +]} ⊎ MO_without_not_nb_on_list l'2 
                    = {[+ a0 +]} ⊎ MO_without_not_nb_on_list l0) as eq''.
                rewrite<- hyp1. rewrite<- hyp2. eauto.
                eapply gmultiset_disj_union_inj_1; eauto.
           ++++ fold MO_without_not_nb_on_list in hyp1.
                fold MO_without_not_nb_on_list in hyp2.
                rewrite<- hyp1. rewrite<- hyp2. eauto.
           ++++ assert (MO_without_not_nb_on_list l1 = MO_without_not_nb_on_list (a0 :: l'1)) as eq2.
                eapply IHl1. eauto.
                destruct (decide (non_blocking a)) as [nb | not_nb]; 
                destruct (decide (non_blocking a0)) as [nb' | not_nb'].
                +++++ rewrite (lts_MO_nb_on_list_spec1 a l1 nb).
                      rewrite (lts_MO_nb_on_list_spec1 a0 l2 nb').
                      rewrite<- eq1. 
                      assert (MO_without_not_nb_on_list l1
                        = MO_without_not_nb_on_list (a0 :: l'2)) as eq'''.
                      eapply IHl1. etransitivity; eauto. eapply Permutation_cons;eauto.
                      symmetry; eauto. rewrite eq'''.
                      rewrite (lts_MO_nb_on_list_spec1 a0 l'2 nb').
                      rewrite (lts_MO_nb_on_list_spec1 a l'2 nb).
                      multiset_solver.
                +++++ rewrite (lts_MO_nb_on_list_spec2 a0 l2 not_nb').
                      rewrite<- eq1.
                      rewrite (lts_MO_nb_on_list_spec1 a l1 nb).
                      rewrite (lts_MO_nb_on_list_spec1 a l'2 nb).
                      f_equal.
                      rewrite<- (lts_MO_nb_on_list_spec2 a0 l'2 not_nb').
                      eapply IHl1. etransitivity; eauto. eapply Permutation_cons;eauto.
                      symmetry; eauto.
                +++++ rewrite (lts_MO_nb_on_list_spec1 a0 l2 nb').
                      rewrite<- eq1.
                      rewrite (lts_MO_nb_on_list_spec2 a l1 not_nb).
                      rewrite (lts_MO_nb_on_list_spec2 a l'2 not_nb).
                      rewrite<- (lts_MO_nb_on_list_spec1 a0 l'2 nb').
                      eapply IHl1.
                      etransitivity; eauto. eapply Permutation_cons;eauto.
                      symmetry; eauto.
                +++++ rewrite (lts_MO_nb_on_list_spec2 a l1 not_nb).
                      rewrite (lts_MO_nb_on_list_spec2 a0 l2 not_nb').
                      rewrite<- eq1.
                      rewrite (lts_MO_nb_on_list_spec2 a l'2 not_nb).
                      rewrite<- (lts_MO_nb_on_list_spec2 a0 l'2 not_nb').
                      eapply IHl1. etransitivity; eauto.
                      eapply Permutation_cons;eauto. symmetry; eauto.
Qed.

Definition MO_without_not_nb `{ExtAction A} (m : MO A) : MO A :=
  MO_without_not_nb_on_list ((elements (m : MO A) : list A)).

Lemma MO_list_union `{ExtAction A} l1 l2 :
  MO_without_not_nb_on_list (l1 ++ l2) = (MO_without_not_nb_on_list l1) ⊎ (MO_without_not_nb_on_list l2).
Proof.
  induction l1.
  + simpl. multiset_solver.
  + simpl. destruct (decide(non_blocking a)).
    - rewrite IHl1. multiset_solver.
    - eauto.
Qed.

Lemma MO_union `{ExtAction A} (m1 m2 : MO A) :
  MO_without_not_nb (m1 ⊎ m2) = MO_without_not_nb m1 ⊎  MO_without_not_nb m2.
Proof.
  assert (elements (m1 ⊎ m2) ≡ₚ elements m1 ++ elements m2) as eq by (eapply gmultiset_elements_disj_union).
  eapply lts_MO_nb_on_list_perm in eq. unfold MO_without_not_nb. rewrite eq.
  eapply MO_list_union.
Qed.

Lemma lts_MO_nb_spec0 `{H : ExtAction A}: 
      ((MO_without_not_nb (∅ : MO A)) : MO A) = (∅  : MO A).
Proof.
  unfold MO_without_not_nb. 
  assert (eq : elements (∅ : MO A) = []).
  multiset_solver. rewrite eq. simpl. reflexivity.
Qed.

Lemma lts_MO_nb_spec1 `{H : ExtAction A} η m : 
  non_blocking η -> 
      (MO_without_not_nb (({[+ η +]} : gmultiset A) ⊎ m) : gmultiset A) 
          = (({[+ η +]} : gmultiset A) ⊎ ((MO_without_not_nb m)  : gmultiset A)  : gmultiset A).
Proof.
  revert η.
  induction m using gmultiset_ind.
  + intros η nb.
    assert (eq : ({[+ η +]} ⊎ ∅ : gmultiset A) = ({[+ η +]} : gmultiset A)).
    eapply gmultiset_disj_union_right_id. unfold MO in eq.
    unfold MO.
    rewrite eq. 
    unfold MO_without_not_nb. 
    assert (eq' : elements (∅ : gmultiset A) = []).
    multiset_solver. unfold MO in eq'. unfold MO. rewrite eq'. simpl.
    rewrite gmultiset_disj_union_right_id. rewrite gmultiset_elements_singleton.
    unfold MO_without_not_nb_on_list.
    erewrite decide_True. unfold MO. rewrite gmultiset_disj_union_right_id. reflexivity. eauto.
  + intros η nb.
    unfold MO_without_not_nb.
    assert (elements ({[+ η +]} ⊎ ({[+ x +]} ⊎ m)) ≡ₚ 
          elements ({[+ η +]} : gmultiset A) ++ elements ({[+ x +]} ⊎ m)) as eq.
    eapply gmultiset_elements_disj_union.
    erewrite lts_MO_nb_on_list_perm; eauto.
    rewrite gmultiset_elements_singleton. simpl.
    rewrite decide_True. reflexivity. eauto.
Qed.

Lemma lts_MO_nb_spec2 `{H : ExtAction A} β m : 
      blocking β ->  
        MO_without_not_nb (({[+ β +]} : gmultiset A) ⊎ m : gmultiset A) = (MO_without_not_nb m : gmultiset A).
Proof.
  revert β.
  induction m using gmultiset_ind.
  + intros μ nb.
    assert (eq : (({[+ μ +]} : gmultiset A) ⊎ ∅ : gmultiset A) = ({[+ μ +]} : gmultiset A)).
    eapply gmultiset_disj_union_right_id. unfold MO in eq.
    unfold MO.
    rewrite eq.
    unfold MO_without_not_nb. unfold MO.
    erewrite gmultiset_elements_singleton. simpl.
    rewrite decide_False. reflexivity. eauto.
  + intros μ nb.
    unfold MO_without_not_nb.
    assert (elements ({[+ μ +]} ⊎ ({[+ x +]} ⊎ m)) ≡ₚ 
          elements ({[+ μ +]} : gmultiset A) ++ elements ({[+ x +]} ⊎ m)) as eq.
    eapply gmultiset_elements_disj_union.
    rewrite (lts_MO_nb_on_list_perm (elements ({[+ μ +]} ⊎ ({[+ x +]} ⊎ m))) 
    (elements ({[+ μ +]} : gmultiset A) ++ elements ({[+ x +]} ⊎ m))); eauto.
    rewrite  gmultiset_elements_singleton. simpl.
    rewrite decide_False. reflexivity. eauto.
Qed.

Lemma lts_MO_nb_with_nb_spec1 `{H : ExtAction A} η m :
  η ∈ (MO_without_not_nb (m  : MO A) : MO A)
    -> non_blocking η /\ η ∈ m.
Proof.
    induction m as [|μ m] using gmultiset_ind.
    + intro mem.
      exfalso.
      assert (η ∈ (MO_without_not_nb ∅ : MO A)) as eq. eauto.
      erewrite lts_MO_nb_spec0 in eq.
      multiset_solver.
    + intro mem.
      destruct (decide (non_blocking μ)) as [nb | not_nb].
      ++ assert ((MO_without_not_nb (({[+ μ +]}  : MO A) ⊎ m) : MO A) = 
          ((({[+ μ +]} : MO A) ⊎ MO_without_not_nb m) : MO A))
               as eq'.
         eapply (lts_MO_nb_spec1 μ m nb); eauto.
         assert (η ∈ ({[+ μ +]} ⊎ MO_without_not_nb m : MO A)) as eq''.
         rewrite<- eq'. eauto.
         eapply gmultiset_elem_of_disj_union in eq''.
         destruct eq'' as [eq | mem'].
         +++ eapply gmultiset_elem_of_singleton in eq. subst.
             split; eauto; try multiset_solver.
         +++ eapply IHm in mem' as (nb'' & mem'').
             split; eauto; try multiset_solver.
      ++ assert (η ∈ (MO_without_not_nb m : MO A)) as mem'.
         rewrite<- (lts_MO_nb_spec2 μ m not_nb); eauto.
         eapply IHm in mem' as (nb & mem').
         split; eauto; try multiset_solver.
Qed.

Lemma lts_MO_nb_with_nb_spec2 `{H : ExtAction A} η m :
    non_blocking η -> η ∈ m -> η ∈ MO_without_not_nb m.
Proof.
    intros nb mem.
    assert (m = {[+ η +]} ⊎ m ∖ {[+ η +]}) as eq. multiset_solver.
    rewrite eq.
    unfold MO.
    erewrite lts_MO_nb_spec1; eauto.
    multiset_solver.
Qed.

Lemma lts_MO_nb_with_nb_diff `{H : ExtAction A} η m :
    non_blocking η -> η ∈ m -> 
        (MO_without_not_nb (m ∖ {[+ η +]}) : MO A) = ((MO_without_not_nb m) ∖ {[+ η +]} : MO A).
Proof.
    induction m as [|μ m] using gmultiset_ind.
    + intros nb mem.
      inversion mem.
    + intros nb mem.
      eapply gmultiset_elem_of_disj_union in mem.
      destruct mem as [eq | mem'].
      ++ eapply gmultiset_elem_of_singleton in eq. subst.
         assert (MO_without_not_nb ({[+ μ +]} ⊎ m) = {[+ μ +]} ⊎ MO_without_not_nb m) as eq'.
         eapply lts_MO_nb_spec1; eauto.
         rewrite eq'. 
         assert (({[+ μ +]} ⊎ MO_without_not_nb m) ∖ {[+ μ +]} = MO_without_not_nb m) 
          as eq'' by multiset_solver.
         rewrite eq''. f_equal. multiset_solver.
      ++ eapply IHm in nb as Hyp; eauto.
         eapply lts_MO_nb_with_nb_spec2 in nb as mem'' ; eauto.
         assert ((({[+ μ +]} ⊎ m) ∖ {[+ η +]} : MO A) = (({[+ μ +]} ⊎ (m ∖ {[+ η +]})) : MO A))
           as eq.
         multiset_solver. 
         erewrite (gmultiset_disj_union_difference' η m) at 1; eauto.
         assert (({[+ μ +]} ⊎ ({[+ η +]} ⊎ m ∖ {[+ η +]})) =
            {[+ η +]} ⊎ ({[+ μ +]} ⊎ m ∖ {[+ η +]})) as eq' by multiset_solver.
         rewrite eq'. 
         assert (η ∈ {[+ μ +]} ⊎ m) as eq'''. multiset_solver.
         assert (({[+ η +]} ⊎ ({[+ μ +]} ⊎ m ∖ {[+ η +]})) = 
              {[+ μ +]} ⊎ m) as eq'' by multiset_solver.
         rewrite eq''. rewrite<- eq'' at 2.
         assert (MO_without_not_nb ({[+ η +]} ⊎ ({[+ μ +]} ⊎ m ∖ {[+ η +]})) = 
         {[+ η +]} ⊎ MO_without_not_nb (({[+ μ +]} ⊎ m ∖ {[+ η +]}))) as eq''''. 
         eapply lts_MO_nb_spec1; eauto.
         rewrite eq''''. 
         assert (({[+ η +]} ⊎ MO_without_not_nb ({[+ μ +]} ⊎ m ∖ {[+ η +]})) ∖ {[+ η +]} =
          MO_without_not_nb ({[+ μ +]} ⊎ m ∖ {[+ η +]})) as eq''''' by multiset_solver.
         rewrite eq'''''. f_equal. multiset_solver.
Qed.

Definition MO_eq `{H : ExtAction A} (M1 : MO A) (M2 : MO A) := M1 = M2.

Lemma MO_eq_equiv `{H : ExtAction A} : Equivalence MO_eq.
Proof.
  unfold MO_eq. constructor.
  + intro M. now reflexivity.
  + intros M1 M2. now symmetry.
  + intros M1 M2 M3. now (etrans; eauto).
Qed.

Global Hint Resolve MO_eq_equiv:mdb.

#[global] Program Instance MbgLtsEq `{H : ExtAction A} : gLtsEq (MO A) H :=
 {| eq_rel := MO_eq |}.
Next Obligation.
  unfold MO_eq.
  intros ? ? M1 M2 ? (r & eq & tr).
  subst. exists M2. split; eauto.
Qed.

Lemma delay_in_ms `{H : ExtAction A} η α M1 M2 M3 : non_blocking η -> M1 ⟶[ η ] M2 -> M2 ⟶{ α } M3 
        → (∃ M'2, M1 ⟶{α} M'2 /\ M'2 ⟶⋍[ η ] M3).
Proof.
  destruct α.
  + destruct (decide (non_blocking μ)) as [nb' | b'];intros nb tr_nb tr.
    - eapply non_blocking_action_in_ms in tr_nb; eauto ; subst.
      eapply non_blocking_action_in_ms in tr; eauto ; subst.
      exists ({[+ η +]} ⊎ M3). split.
      * assert ({[+ μ +]} ⊎ ({[+ η +]} ⊎ M3) = {[+ η +]} ⊎ ({[+ μ +]} ⊎ M3)) as eq by multiset_solver.
        rewrite<- eq. eapply lts_multiset_minus;eauto.
      * exists M3. split.
        ++ eapply lts_multiset_minus;eauto.
        ++ reflexivity.
    - eapply non_blocking_action_in_ms in tr_nb; eauto ; subst.
      eapply blocking_action_in_ms in tr as (eq & duo & nb'); eauto ; subst.
      exists ({[+ co μ +]} ⊎ ({[+ η +]} ⊎ M2)). split.
      * eapply lts_multiset_add;eauto.
      * assert ({[+ co μ +]} ⊎ ({[+ η +]} ⊎ M2) = {[+ η +]} ⊎ ({[+ co μ +]} ⊎ M2)) as eq by multiset_solver.
        rewrite eq. exists ({[+ co μ +]} ⊎ M2). split.
        ++ eapply lts_multiset_minus;eauto.
        ++ reflexivity.
  + intros nb tr_nb tr. inversion tr.
Qed.

Lemma confluence_in_ms `{H : ExtAction A} M M1 M2 η μ : μ ≠ η -> M ⟶[ η ] M1 → M ⟶[ μ ] M2 
        → ∃ M', M1 ⟶[ μ ] M' /\ M2 ⟶⋍[ η ] M'.
Proof.
  intros neq tr_nb tr.
  destruct (decide (non_blocking μ)) as [nb' | b']; destruct (decide (non_blocking η)) as [nb | b].
  + eapply non_blocking_action_in_ms in tr_nb; eauto ; subst.
    eapply non_blocking_action_in_ms in tr; eauto ; subst.
    assert (η ∈ M2) by multiset_solver.
    assert (μ ∈ M1) by multiset_solver.
    assert (exists M'2, M2 = {[+ η +]} ⊎ M'2) as (M'2 & eq2).
    { exists (M2 ∖ {[+ η +]}). multiset_solver. }
    assert (exists M'1, M1 = {[+ μ +]} ⊎ M'1) as (M'1 & eq1).
    { exists (M1 ∖ {[+ μ +]}). multiset_solver. }
    subst. assert (M'1 = M'2) by multiset_solver. subst.
    exists M'2. split.
    * eapply lts_multiset_minus; eauto.
    * exists M'2. split.
      - eapply lts_multiset_minus; eauto.
      - reflexivity.
  + eapply blocking_action_in_ms in tr_nb as (eq & duo & nb''); eauto ; subst.
    eapply non_blocking_action_in_ms in tr; eauto ; subst.
    exists ({[+ co η +]} ⊎ M2). split.
    * assert ({[+ co η +]} ⊎ ({[+ μ +]} ⊎ M2) = {[+ μ +]} ⊎ ({[+ co η +]} ⊎ M2)) as eq by multiset_solver.
      rewrite eq. eapply lts_multiset_minus; eauto.
    * exists ({[+ co η +]} ⊎ M2). split.
      - eapply lts_multiset_add; eauto.
      - reflexivity. 
  + eapply non_blocking_action_in_ms in tr_nb; eauto ; subst.
    eapply blocking_action_in_ms in tr as (eq & duo & nb''); eauto ; subst.
    exists ({[+ co μ +]} ⊎ M1). split.
    * eapply lts_multiset_add; eauto.
    * exists ({[+ co μ +]} ⊎ M1). split.
      - assert ({[+ co μ +]} ⊎ ({[+ η +]} ⊎ M1) = {[+ η +]} ⊎ ({[+ co μ +]} ⊎ M1)) as eq by multiset_solver.
        rewrite eq. eapply lts_multiset_minus; eauto.
      - reflexivity.
  + eapply blocking_action_in_ms in tr_nb as (eq' & duo' & nb''); eauto ; subst.
    eapply blocking_action_in_ms in tr as (eq & duo & nb'''); eauto ; subst.
    * exists ({[+ co μ +]} ⊎ ({[+ co η +]} ⊎ M)). split.
      - eapply lts_multiset_add; eauto.
      - exists ({[+ co μ +]} ⊎ ({[+ co η +]} ⊎ M)). split.
        ++ assert ({[+ co μ +]} ⊎ ({[+ co η +]} ⊎ M) = {[+ co η +]} ⊎ ({[+ co μ +]} ⊎ M)) as eq by multiset_solver.
           rewrite eq. eapply lts_multiset_add; eauto.
        ++ reflexivity.
Qed.

Lemma nb_tau_in_ms `{H : ExtAction A} M M1 M2 η :
      M ⟶[ η ] M1 -> M ⟶ M2 
        → (∃ M', M1 ⟶ M' /\ M2 ⟶⋍[ η ] M') \/ (∃ β, (dual β η) /\ M1 ⟶⋍[ β ] M2).
Proof.
  intros ? tr_tau.
  inversion tr_tau.
Qed.

Lemma deter_in_ms `{H : ExtAction A} M1 M2 M3 η :
      M1 ⟶[ η ] M2 → M1 ⟶[ η ] M3 
        → M2 ⋍ M3.
Proof.
  intros tr1 tr2.
  destruct (decide (non_blocking η)) as [nb | b].
  + eapply non_blocking_action_in_ms in tr1; eauto ; subst.
    eapply non_blocking_action_in_ms in tr2; eauto ; subst.
    assert (M3 = M2) as eq by multiset_solver. subst.
    reflexivity.
  + eapply blocking_action_in_ms in tr1 as (eq' & duo' & nb'); eauto ; subst.
    eapply blocking_action_in_ms in tr2 as (eq'' & duo'' & nb''); eauto ; subst.
Qed.

Lemma inv_deter_in_ms `{H : ExtAction A} M1 M'1 M2 M3 η :
      M1 ⟶[ η ] M2 -> M'1 ⟶[ η ] M3 
        -> M2 ⋍ M3 -> M1 ⋍ M'1.
Proof.
  intros tr1 tr2 equiv. inversion equiv. subst.
  destruct (decide (non_blocking η)) as [nb | b].
  + eapply non_blocking_action_in_ms in tr1; eauto ; subst.
    eapply non_blocking_action_in_ms in tr2; eauto ; subst.
  + eapply blocking_action_in_ms in tr1 as (eq' & duo' & nb'); eauto ; subst.
    eapply blocking_action_in_ms in tr2 as (eq'' & duo'' & nb''); eauto ; subst.
    assert (M1 = M'1) by multiset_solver. subst.
    reflexivity.
Qed.

#[global] Program Instance MbgLts_Oba`{H : ExtAction A} : gLtsOba (MO A). 
Next Obligation.
  intros. eapply delay_in_ms;eauto.
Qed.
Next Obligation.
  intros. eapply confluence_in_ms;eauto.
Qed.
Next Obligation.
  intros. eapply nb_tau_in_ms; eauto.
Qed.
Next Obligation.
  intros. eapply deter_in_ms; eauto.
Qed.
Next Obligation.
  intros. eapply inv_deter_in_ms; eauto.
Qed.

Lemma forward_in_ms `{H : ExtAction A} M1 η β :
      ∃ M2, non_blocking η -> dual β η
        -> M1 ⟶[ β ] M2 /\ M2 ⟶[ η ] M1.
Proof.
  exists ({[+ η +]} ⊎ M1).
  intros nb duo. split.
  + eapply lts_multiset_add;eauto.
  + eapply lts_multiset_minus;eauto.
Qed.

Lemma forward_feedback_in_ms `{H : ExtAction A} M1 M2 M3 η β :
      non_blocking η -> dual β η -> M1 ⟶[ η ] M2 -> M2 ⟶[ β ] M3 
        -> M1 ⟶⋍ M3 \/ M1 ⋍ M3.
Proof.
  intros nb duo tr_nb tr. right.
  eapply non_blocking_action_in_ms in tr_nb;eauto; subst.
  eapply blocking_action_in_ms in tr as (eq'' & duo'' & nb''); eauto ; subst.
  + assert (η = co β).
    { eapply unique_nb; eauto. }
    subst; eauto. reflexivity.
  + eapply dual_blocks;eauto.
Qed.

#[global] Program Instance MbgLts_Oba_FW `{H : ExtAction A} : gLtsObaFW (MO A) A. 
Next Obligation.
  intros. eapply forward_in_ms; eauto.
Qed.
Next Obligation.
  intros. eapply forward_feedback_in_ms;eauto.
Qed.