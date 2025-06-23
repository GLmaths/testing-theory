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
From Must Require Import TransitionSystems.


Definition subset_of (A : Type) := A -> Prop.

Definition lts_pre_acc_set_of `{Lts P A} (p : P) (μ : A) : Prop := 
      ¬ lts_stable p (ActExt μ).

Definition lts_acc_set_of `{Lts P A} (p : P) : subset_of A := lts_pre_acc_set_of p.

(* Definition Included {A : Type} (B C: A -> Prop) : Prop := 
    forall μ : A, B μ -> C μ.
Notation "B ⫅ C" := (Included B C) (at level 20, format "B ⫅ C").

Definition Setminus {A : Type} (B C: A -> Prop) : A -> Prop :=
    fun μ : A => B μ /\ ~ C μ.
Notation "B \ C" := (Setminus B C) (at level 20, format "B \ C"). *)


Definition Union_of_Act {A :Type} (S : subset_of A) (S' : subset_of A) (a : A)  : Prop := 
        S a \/ S' a.
Definition Intersection_of_Act {A :Type} (S : subset_of A) (S' : subset_of A) (a : A)  : Prop := 
        S a /\ S' a.
Definition Empty_of_Act {A : Type} (x : A) : Prop := False.
Definition Difference_of_act {A :Type} (S : subset_of A) (S' : subset_of A) (a : A)  : Prop := 
        S a /\ (~ (S' a)).
(* Definition Singleton_of_Act {A : Type} (x : A) : Prop := forall y : A , x = y. *)

(** Instances to use sets notation/properties from stdpp lib *)
#[global] Instance Union_of_Actions {A : Type} : Union (@subset_of A).
exact Union_of_Act. Defined.
#[global] Instance Empty_Actions {A : Type} : Empty (@subset_of A).
exact Empty_of_Act. Defined.
#[global] Instance Singleton_of_Actions {A : Type} : Singleton A (@subset_of A).
intro single_element. exact (fun x : A => single_element = x). Defined.
#[global] Instance Elements_of {A : Type} : ElemOf A (@subset_of A).
intro x. intro P. exact (P x). Defined.
#[global] Instance Intersection_of_Actions {A : Type} : Intersection (@subset_of A).
exact Intersection_of_Act. Defined.
#[global] Instance Difference_of_Actions {A : Type} : Difference (@subset_of A).
exact Difference_of_act. Defined.
#[global] Instance Top_Actions {A : Type} : Top (@subset_of A).
intro. exact True. Defined.
(* #[global] Instance SubsetEq_of_Actions {A : Type} : SubsetEq (@subset_of A).
intro P. intro Q. exact (forall x : A, P x -> Q x). Defined. *)


#[global] Instance SemiSet_of_Actions {A : Type} : SemiSet A (@subset_of A).
repeat split.
+ intros. intro. exact H.
+ intro. inversion H. reflexivity.
+ intro eq. subst. (* unfold elem_of. unfold singleton. unfold Singleton_of_Actions. 
    unfold Elements_of. *) reflexivity.
+ intro Hyp. destruct Hyp.
  ++ left; eauto.
  ++ right; eauto.
+ intro. destruct H.
  ++ left; eauto.
  ++ right; eauto.
Defined.

#[global] Instance Set_of_Actions {A : Type} : Set_ A (@subset_of A).
repeat split; try set_solver.
+ destruct H. eauto.
+ destruct H. eauto.
+ destruct H. eauto.
+ destruct H. eauto. Defined.

#[global] Instance TopSet_of_Actions {A : Type} : TopSet A (@subset_of A).
repeat split ; try set_solver. Defined.

(* Axiom Extensionality_Subset_of: 
  forall A : Type, forall S S': subset_of A, (S ⊆ S' /\ S' ⊆ S) -> S = S'.

#[global] Instance LeibnizEquiv_Actions {A : Type} : LeibnizEquiv (@subset_of A).
  intro. intros.
  eapply Extensionality_Subset_of. set_solver.
Qed. *)