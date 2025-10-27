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

From Coq.Unicode Require Import Utf8.
From Coq.Program Require Import Equality.
From stdpp Require Import finite gmap gmultiset.
From Must Require Import ActTau gLts InteractionBetweenLts.

(************************************************ Mailbox LTS ********************************************)

(** A mailbox is a multiset of actions *)

Definition mb (A : Type) `{ExtAction A} := gmultiset A.

Lemma Prop_for_nb `{ExtAction A} (η : A) (m : mb A) :
    non_blocking η -> (forall η', η' ∈ m -> non_blocking η')
      -> (forall η'', η'' ∈ ({[+ η +]} ⊎ m) -> non_blocking η'').
Proof.
  intros nb nb_for_mb.
  intros η'' mem.
  destruct (decide (η'' ∈ m)) as [mem' | not_mem'].
  + exact (nb_for_mb η'' mem').
  + assert (η'' = η). multiset_solver. subst.
    eauto.
Qed.

Inductive lts_multiset_step `{ExtAction A} : mb A -> Act A -> mb A -> Prop :=
| lts_multiset_add m η μ (duo : dual η μ) (nb : non_blocking η) :
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
    apply (dual_blocks μ η ) in nb''; eauto. contradiction.
  + eauto.
Qed.

Lemma blocking_action_in_ms `{ExtAction A}  mb1 μ mb2 :  
  blocking μ -> lts_multiset_step mb1 (ActExt μ) mb2 
    ->  ({[+ co μ +]} ⊎ mb1 = mb2 /\ (dual (co μ) μ /\ non_blocking (co μ))).
Proof.
  intros nb Hstep.
  inversion Hstep as [ ? η ? duo nb'|]; subst.
  + assert (η =  co μ) as eq. eapply unique_nb;eauto. subst. eauto.
  + contradiction.
Qed.

Definition lts_exists_duo_decidable : 
forall (A : Type) (H : ExtAction A) μ, Decision (∃ η' : A, non_blocking η' ∧ dual η' μ).
Proof.
intros. destruct (decide (non_blocking μ)) as [nb | not_nb].
  + right. intro Hyp. destruct Hyp as (μ' & nb' & duo').
    assert (blocking μ).
    eapply dual_blocks; eauto. contradiction.
  + destruct (decide (non_blocking (co μ))) as [nb' | not_nb'].
    ++ assert { μ' | dual μ μ'} as (μ' & duo).
       exact (choice (fun μ0 => dual μ μ0) (exists_duo_nb μ) ).
       symmetry in duo.
       destruct (decide (non_blocking μ')) as [nb'' | not_nb''].
       +++ left. exists μ'; eauto.
       +++ right. intro Hyp. destruct Hyp as (μ'' & nb'' & duo'').
           assert (non_blocking μ'). eapply nb_not_nb; eauto. contradiction.
    ++ right. intro imp. destruct imp as (η'' & nb'' & duo).
       assert (η'' = (co μ)). eapply unique_nb; eauto. subst.
       contradiction.
Qed.

#[global] Instance lts_exists_duo_decidable_inst `{ExtAction A} μ 
  : Decision (∃ η', non_blocking η' /\ dual η' μ).
Proof. exact (lts_exists_duo_decidable A H μ). Qed.

Definition lts_multiset_step_decidable `{ExtAction A} m α m' : Decision (lts_multiset_step m α m').
Proof.
  destruct α as [μ |].
  + destruct (decide (non_blocking μ)) as [nb | not_nb].
    - rename μ into η. destruct (decide ((m =  {[+ η +]} ⊎ m'))); subst.
      ++ left. eapply lts_multiset_minus; eauto.
      ++ right. intro. eapply non_blocking_action_in_ms in nb; eauto.
    - destruct (decide (∃ η', non_blocking η' /\ dual η' μ)) as [exists_dual | not_exists_dual].
      assert ({ η' | non_blocking η' ∧ dual η' μ}) as Hyp'.
      exact (choice (fun η' => non_blocking η' ∧ dual η' μ) exists_dual).
      destruct Hyp' as (η' & nb & duo).
      ++ assert (η' = co μ) as eq. eapply unique_nb; eauto. subst.
         destruct (decide (({[+ (co μ) +]} ⊎ m = m') )) as [eq | not_eq].
         +++ subst. left. eauto with mdb. 
         +++ right. intro. eapply blocking_action_in_ms in not_nb as (eq'' & Hyp) ; eauto.
      ++ right. intro HypTr. 
         eapply blocking_action_in_ms in not_nb as (eq & duo & nb); eauto; subst.
  + right. inversion 1.
Qed.

Definition lts_multiset_refuses `{ExtAction A} (m : mb A) (α : Act A): Prop := 
match α with
    | ActExt η => if (decide (non_blocking η)) then if (decide (η ∈ m)) then False
                                                                        else True
                                               else forall η', dual η' η -> blocking η'
    | τ => True
end.

Definition lts_multiset_refuses_decidable `{ExtAction A} m α : Decision (lts_multiset_refuses m α).
Proof.
  destruct α as [μ |].
  + simpl in *. destruct (decide (non_blocking μ)) as [nb | not_nb].
    - rename μ into η. destruct (decide (η ∈ m)) as [in_mem | not_in_mem].
      ++ right. intro. eauto.
      ++ left. eauto. 
    - destruct (decide (∃ η', non_blocking η' /\ dual η' μ)) as [exists_dual | not_exists_dual].
      ++ right. intro imp. destruct exists_dual as (η & nb & duo). destruct (imp η); eauto.
      ++ left. unfold blocking. eauto.
  + left. simpl. eauto.
Qed.

#[global] Program Instance MbgLts `{H : ExtAction A} : gLts (mb A) A :=
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
    + destruct (decide (∃ η' : A, non_blocking η' ∧ dual η' μ)) as [exist | not_exists ].
      ++ exists ({[+ co μ +]} ⊎ m). destruct exist as (η & nb & duo).
         eapply unique_nb in nb as eq; eauto;subst.
         constructor; eauto.  
      ++ exfalso. eapply not_refuses. unfold blocking. eauto.
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

Fixpoint mb_without_not_nb_on_list `{ExtAction A} (l : list A) : mb A:=
match l with
| [] => empty : mb A
| η :: l' => if (decide (non_blocking η)) then {[+ η +]} ⊎ (mb_without_not_nb_on_list l')
                                          else mb_without_not_nb_on_list l'
end.

Lemma lts_mb_nb_on_list_spec1 `{H : ExtAction A} η l: 
  non_blocking η ->  
    mb_without_not_nb_on_list (η :: l) = {[+ η +]} ⊎ mb_without_not_nb_on_list l.
Proof.
  intro nb.
  unfold mb_without_not_nb_on_list at 1.
  erewrite decide_True. fold mb_without_not_nb_on_list. reflexivity. eauto.
Qed.

Lemma lts_mb_nb_on_list_spec2 `{H : ExtAction A} μ l: 
  blocking μ ->  
    mb_without_not_nb_on_list (μ :: l) = mb_without_not_nb_on_list l.
Proof.
  intro nb.
  unfold mb_without_not_nb_on_list at 1.
  erewrite decide_False. fold mb_without_not_nb_on_list. reflexivity. eauto.
Qed.

Lemma lts_mb_nb_on_list_perm `{H : ExtAction A} (l1 : list A) (l2 : list A) :
  l1 ≡ₚ l2 -> mb_without_not_nb_on_list l1 = mb_without_not_nb_on_list l2.
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
           ++++ erewrite lts_mb_nb_on_list_spec1; eauto.
                erewrite lts_mb_nb_on_list_spec1; eauto.
                f_equal. eauto.
           ++++ erewrite lts_mb_nb_on_list_spec2; eauto.
                erewrite lts_mb_nb_on_list_spec2; eauto.
       +++ assert (a0 ∈ a :: l1). eapply elem_of_list_In.
           symmetry in equiv.
           eapply Permutation_in ;eauto. set_solver.
           assert (a0 ∈ l1) as mem. set_solver.
           eapply elem_of_Permutation in mem as (l'1 & Hyp1).
           assert (a ∈ a0 :: l2). eapply elem_of_list_In.
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
           assert (mb_without_not_nb_on_list (a :: l'2) = mb_without_not_nb_on_list l2) as eq1.
           symmetry in Hyp2. eapply IHl2; eauto. intros.
           assert (l1 ≡ₚ a0 :: l'2) as hyp1. etransitivity; eauto.
           eapply Permutation_cons; eauto. symmetry; eauto.
           assert (l1 ≡ₚ a0 :: l0) as hyp2. etransitivity; eauto.
           eapply IHl1 in hyp1. eapply IHl1 in hyp2.
           unfold mb_without_not_nb_on_list in hyp1 at 2.
           unfold mb_without_not_nb_on_list in hyp2 at 2.
           destruct (decide (non_blocking a0)) as [nb' | not_nb'].
           ++++ fold mb_without_not_nb_on_list in hyp1.
                fold mb_without_not_nb_on_list in hyp2.
                assert ({[+ a0 +]} ⊎ mb_without_not_nb_on_list l'2 
                    = {[+ a0 +]} ⊎ mb_without_not_nb_on_list l0) as eq''.
                rewrite<- hyp1. rewrite<- hyp2. eauto.
                eapply gmultiset_disj_union_inj_1; eauto.
           ++++ fold mb_without_not_nb_on_list in hyp1.
                fold mb_without_not_nb_on_list in hyp2.
                rewrite<- hyp1. rewrite<- hyp2. eauto.
           ++++ assert (mb_without_not_nb_on_list l1 = mb_without_not_nb_on_list (a0 :: l'1)) as eq2.
                eapply IHl1. eauto.
                destruct (decide (non_blocking a)) as [nb | not_nb]; 
                destruct (decide (non_blocking a0)) as [nb' | not_nb'].
                +++++ rewrite (lts_mb_nb_on_list_spec1 a l1 nb).
                      rewrite (lts_mb_nb_on_list_spec1 a0 l2 nb').
                      rewrite<- eq1. 
                      assert (mb_without_not_nb_on_list l1
                        = mb_without_not_nb_on_list (a0 :: l'2)) as eq'''.
                      eapply IHl1. etransitivity; eauto. eapply Permutation_cons;eauto.
                      symmetry; eauto. rewrite eq'''.
                      rewrite (lts_mb_nb_on_list_spec1 a0 l'2 nb').
                      rewrite (lts_mb_nb_on_list_spec1 a l'2 nb).
                      multiset_solver.
                +++++ rewrite (lts_mb_nb_on_list_spec2 a0 l2 not_nb').
                      rewrite<- eq1.
                      rewrite (lts_mb_nb_on_list_spec1 a l1 nb).
                      rewrite (lts_mb_nb_on_list_spec1 a l'2 nb).
                      f_equal.
                      rewrite<- (lts_mb_nb_on_list_spec2 a0 l'2 not_nb').
                      eapply IHl1. etransitivity; eauto. eapply Permutation_cons;eauto.
                      symmetry; eauto.
                +++++ rewrite (lts_mb_nb_on_list_spec1 a0 l2 nb').
                      rewrite<- eq1.
                      rewrite (lts_mb_nb_on_list_spec2 a l1 not_nb).
                      rewrite (lts_mb_nb_on_list_spec2 a l'2 not_nb).
                      rewrite<- (lts_mb_nb_on_list_spec1 a0 l'2 nb').
                      eapply IHl1.
                      etransitivity; eauto. eapply Permutation_cons;eauto.
                      symmetry; eauto.
                +++++ rewrite (lts_mb_nb_on_list_spec2 a l1 not_nb).
                      rewrite (lts_mb_nb_on_list_spec2 a0 l2 not_nb').
                      rewrite<- eq1.
                      rewrite (lts_mb_nb_on_list_spec2 a l'2 not_nb).
                      rewrite<- (lts_mb_nb_on_list_spec2 a0 l'2 not_nb').
                      eapply IHl1. etransitivity; eauto.
                      eapply Permutation_cons;eauto. symmetry; eauto.
Qed.

Definition mb_without_not_nb `{ExtAction A} (m : mb A) : mb A :=
  mb_without_not_nb_on_list ((elements (m : mb A) : list A)).

Lemma lts_mb_nb_spec0 `{H : ExtAction A}: 
      ((mb_without_not_nb (∅ : mb A)) : mb A) = (∅  : mb A).
Proof.
  unfold mb_without_not_nb. 
  assert (eq : elements (∅ : mb A) = []).
  multiset_solver. rewrite eq. simpl. reflexivity.
Qed.

Lemma lts_mb_nb_spec1 `{H : ExtAction A} η m : 
  non_blocking η -> 
      (mb_without_not_nb (({[+ η +]} : gmultiset A) ⊎ m) : gmultiset A) 
          = (({[+ η +]} : gmultiset A) ⊎ ((mb_without_not_nb m)  : gmultiset A)  : gmultiset A).
Proof.
  revert η.
  induction m using gmultiset_ind.
  + intros η nb.
    assert (eq : ({[+ η +]} ⊎ ∅ : gmultiset A) = ({[+ η +]} : gmultiset A)).
    eapply gmultiset_disj_union_right_id. unfold mb in eq.
    unfold mb.
    rewrite eq. 
    unfold mb_without_not_nb. 
    assert (eq' : elements (∅ : gmultiset A) = []).
    multiset_solver. unfold mb in eq'. unfold mb. rewrite eq'. simpl.
    rewrite gmultiset_disj_union_right_id. rewrite gmultiset_elements_singleton.
    unfold mb_without_not_nb_on_list.
    erewrite decide_True. unfold mb. rewrite gmultiset_disj_union_right_id. reflexivity. eauto.
  + intros η nb.
    unfold mb_without_not_nb.
    assert (elements ({[+ η +]} ⊎ ({[+ x +]} ⊎ m)) ≡ₚ 
          elements ({[+ η +]} : gmultiset A) ++ elements ({[+ x +]} ⊎ m)) as eq.
    eapply gmultiset_elements_disj_union.
    erewrite lts_mb_nb_on_list_perm; eauto.
    rewrite gmultiset_elements_singleton. simpl.
    rewrite decide_True. reflexivity. eauto.
Qed.

Lemma lts_mb_nb_spec2 `{H : ExtAction A} μ m : 
      blocking μ ->  
        mb_without_not_nb (({[+ μ +]} : gmultiset A) ⊎ m : gmultiset A) = (mb_without_not_nb m : gmultiset A).
Proof.
  revert μ.
  induction m using gmultiset_ind.
  + intros μ nb.
    assert (eq : (({[+ μ +]} : gmultiset A) ⊎ ∅ : gmultiset A) = ({[+ μ +]} : gmultiset A)).
    eapply gmultiset_disj_union_right_id. unfold mb in eq.
    unfold mb.
    rewrite eq.
    unfold mb_without_not_nb. unfold mb.
    erewrite gmultiset_elements_singleton. simpl.
    rewrite decide_False. reflexivity. eauto.
  + intros μ nb.
    unfold mb_without_not_nb.
    assert (elements ({[+ μ +]} ⊎ ({[+ x +]} ⊎ m)) ≡ₚ 
          elements ({[+ μ +]} : gmultiset A) ++ elements ({[+ x +]} ⊎ m)) as eq.
    eapply gmultiset_elements_disj_union.
    rewrite (lts_mb_nb_on_list_perm (elements ({[+ μ +]} ⊎ ({[+ x +]} ⊎ m))) 
    (elements ({[+ μ +]} : gmultiset A) ++ elements ({[+ x +]} ⊎ m))); eauto.
    rewrite  gmultiset_elements_singleton. simpl.
    rewrite decide_False. reflexivity. eauto.
Qed.

Lemma lts_mb_nb_with_nb_spec1 `{H : ExtAction A} η m :
  η ∈ (mb_without_not_nb (m  : mb A) : mb A)
    -> non_blocking η /\ η ∈ m.
Proof.
    induction m as [|μ m] using gmultiset_ind.
    + intro mem.
      exfalso.
      assert (η ∈ (mb_without_not_nb ∅ : mb A)) as eq. eauto.
      erewrite lts_mb_nb_spec0 in eq.
      multiset_solver.
    + intro mem.
      destruct (decide (non_blocking μ)) as [nb | not_nb].
      ++ assert ((mb_without_not_nb (({[+ μ +]}  : mb A) ⊎ m) : mb A) = 
          ((({[+ μ +]} : mb A) ⊎ mb_without_not_nb m) : mb A))
               as eq'.
         eapply (lts_mb_nb_spec1 μ m nb); eauto.
         assert (η ∈ ({[+ μ +]} ⊎ mb_without_not_nb m : mb A)) as eq''.
         rewrite<- eq'. eauto.
         eapply gmultiset_elem_of_disj_union in eq''.
         destruct eq'' as [eq | mem'].
         +++ eapply gmultiset_elem_of_singleton in eq. subst.
             split; eauto; try multiset_solver.
         +++ eapply IHm in mem' as (nb'' & mem'').
             split; eauto; try multiset_solver.
      ++ assert (η ∈ (mb_without_not_nb m : mb A)) as mem'.
         rewrite<- (lts_mb_nb_spec2 μ m not_nb); eauto.
         eapply IHm in mem' as (nb & mem').
         split; eauto; try multiset_solver.
Qed.

Lemma lts_mb_nb_with_nb_spec2 `{H : ExtAction A} η m :
    non_blocking η -> η ∈ m -> η ∈ mb_without_not_nb m.
Proof.
    intros nb mem.
    assert (m = {[+ η +]} ⊎ m ∖ {[+ η +]}) as eq. multiset_solver.
    rewrite eq.
    unfold mb.
    erewrite lts_mb_nb_spec1; eauto.
    multiset_solver.
Qed.

Lemma lts_mb_nb_with_nb_diff `{H : ExtAction A} η m :
    non_blocking η -> η ∈ m -> 
        (mb_without_not_nb (m ∖ {[+ η +]}) : mb A) = ((mb_without_not_nb m) ∖ {[+ η +]} : mb A).
Proof.
    induction m as [|μ m] using gmultiset_ind.
    + intros nb mem.
      inversion mem.
    + intros nb mem.
      eapply gmultiset_elem_of_disj_union in mem.
      destruct mem as [eq | mem'].
      ++ eapply gmultiset_elem_of_singleton in eq. subst.
         assert (mb_without_not_nb ({[+ μ +]} ⊎ m) = {[+ μ +]} ⊎ mb_without_not_nb m) as eq'.
         eapply lts_mb_nb_spec1; eauto.
         rewrite eq'. 
         assert (({[+ μ +]} ⊎ mb_without_not_nb m) ∖ {[+ μ +]} = mb_without_not_nb m) 
          as eq'' by multiset_solver.
         rewrite eq''. f_equal. multiset_solver.
      ++ eapply IHm in nb as Hyp; eauto.
         eapply lts_mb_nb_with_nb_spec2 in nb as mem'' ; eauto.
         assert ((({[+ μ +]} ⊎ m) ∖ {[+ η +]} : mb A) = (({[+ μ +]} ⊎ (m ∖ {[+ η +]})) : mb A))
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
         assert (mb_without_not_nb ({[+ η +]} ⊎ ({[+ μ +]} ⊎ m ∖ {[+ η +]})) = 
         {[+ η +]} ⊎ mb_without_not_nb (({[+ μ +]} ⊎ m ∖ {[+ η +]}))) as eq''''. 
         eapply lts_mb_nb_spec1; eauto.
         rewrite eq''''. 
         assert (({[+ η +]} ⊎ mb_without_not_nb ({[+ μ +]} ⊎ m ∖ {[+ η +]})) ∖ {[+ η +]} =
          mb_without_not_nb ({[+ μ +]} ⊎ m ∖ {[+ η +]})) as eq''''' by multiset_solver.
         rewrite eq'''''. f_equal. multiset_solver.
Qed.