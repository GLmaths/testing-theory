(*
   Copyright (c) 2024 Gaëtan Lopez <glopez@irif.fr>

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

(* From Coq Require ssreflect Setoid. *)
(* From Coq.Unicode Require Import Utf8. *)
(* From Coq.Lists Require Import List.
Import ListNotations. *)
(* From Coq.Program Require Import Wf Equality. *)
(* From Coq.Wellfounded Require Import Inverse_Image. *)
(* From Coq.Logic Require Import JMeq ProofIrrelevance. *)

From stdpp Require Import gmap.
From Must Require Import gLts.

Definition subset_of (A : Type) := A -> Prop.

Definition lts_pre_acc_set_of `{gLts P A} (p : P) (μ : A) : Prop := 
      ¬ p ↛[μ].

Definition lts_acc_set_of `{gLts P A} (p : P) : subset_of A := lts_pre_acc_set_of p.

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
#[global] Instance SemiSet_of_Actions {A : Type} : SemiSet A (@subset_of A).
repeat split.
+ intros. intro. exact H.
+ intro. inversion H. reflexivity.
+ intro eq. subst. reflexivity.
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