(*
   Copyright (c) 2024 Gaëtan Lopez <gaetanlopez.maths@gmail.com>

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


From Stdlib.Program Require Import Equality.
From Stdlib.Strings Require Import String.
From Stdlib.Wellfounded Require Import Inverse_Image.
From stdpp Require Import base countable finite gmap list gmultiset strings.
From TestingTheory Require Import Clos_n InputOutputActions ActTau .

(** * VACCS *)

Module Type VACCS_proc.

(** ** Definitions and properties of VACCS *)

(* ChannelType is the type of channels *)
(* ValueType is the type of data that can be transmitted over channels *)


(*************************************** Channels ******************************************)
Parameter (Channel : Type).
(* Exemple : Definition Channel := string. *)

Parameter (channel_eq_dec : EqDecision Channel).
#[global] Instance channel_eqdecision : EqDecision Channel.
  by exact channel_eq_dec. Defined.

Parameter (channel_is_countable : Countable Channel).
#[global] Instance channel_countable : Countable Channel.
  by exact channel_is_countable. Defined.

(* Values and their bound variables *)
Inductive ChannelData :=
| cstC : Channel -> ChannelData
| bvarC : nat -> ChannelData. (* variable as De Bruijn indices *) 

Coercion cstC : Channel >-> ChannelData.
Coercion bvarC : nat >-> ChannelData.

Lemma ChannelData_dec : forall (x y : ChannelData) , {x = y} + {x <> y}.
Proof.
decide equality. 
* destruct (decide(c = c0)). left. assumption. right. assumption.
* destruct (decide (n = n0)). left. assumption. right. assumption.
Qed.

#[global] Instance channeldata_eqdecision : EqDecision ChannelData.
  by exact ChannelData_dec . Defined.


(*************************************** Values ******************************************)
Parameter (Value : Type).
(* Exemple : Definition Value := nat. *)

Parameter (value_eq_dec : EqDecision Value).
#[global] Instance value_eqdecision : EqDecision Value.
  by exact value_eq_dec. Defined.

Parameter (value_is_countable : Countable Value).
#[global] Instance value_countable : Countable Value.
  by exact value_is_countable. Defined.

(* Values and their bound variables *)
Inductive Data :=
| cst : Value -> Data
| bvar : nat -> Data. (* variable as De Bruijn indices *) 

Coercion cst : Value >-> Data.
Coercion bvar : nat >-> Data.

Lemma Data_dec : forall (x y : Data) , {x = y} + {x <> y}.
Proof.
decide equality. 
* destruct (decide(v = v0)). left. assumption. right. assumption.
* destruct (decide (n = n0)). left. assumption. right. assumption.
Qed.

#[global] Instance data_eqdecision : EqDecision Data. by exact Data_dec . Defined.

(********************* Labels **********************)
(* Label of action (other than tau), here it is a channel's name with data *)
Inductive TypeOfActions := 
| act : ChannelData -> Data -> TypeOfActions.

Notation "c ⋉ v" := (act c v) (at level 50).

Definition ChannelData_of (a : TypeOfActions) : ChannelData := 
match a with 
| c ⋉ v => c
end.

Definition Data_of (a : TypeOfActions) : Data := 
match a with 
| c ⋉ d => d
end.

(* Definition ChannelData_of_ext (μ : ExtAct TypeOfActions) : ChannelData := 
match μ with 
| ActIn (c ⋉ v) => c
| ActOut (c ⋉ v) => c
end.

Definition Data_of_ext (μ : ExtAct TypeOfActions) : Data := 
match μ with 
| ActIn (c ⋉ v) => v
| ActOut (c ⋉ v) => v
end. *)

Inductive Equation (A : Type) : Type :=
| Equality : A -> A -> Equation A.

Arguments  Equality {_} _ _.

Notation "x == y" := (Equality x y) (at level 50).

Definition Eval_Eq (E : Equation Data) : option bool :=
match E with
| cst t == cst t' => if (decide (t = t')) then (Some true)
                                          else (Some false)
| bvar i == cst t => None
| cst t == bvar i => None
| bvar i == bvar i' => if (decide (i = i')) then (Some true)
                                          else None
end.

(* Definition of processes *)
Inductive proc : Type :=
(* To parallele two processes *)
| pr_par : proc -> proc -> proc
(* Variable in a process, for recursion and substitution *)
| pr_var : nat -> proc
(* recursion for process *)
| pr_rec : nat -> proc -> proc
(* If test *NEW term in comparison of CCS* *)
| pr_if_then_else : Equation Data -> proc -> proc -> proc
(* The Guards *)
(* An output is a name of a channel, an ouput value, followed by a process *)
| pr_output : ChannelData -> Data -> proc
(* Restriction of a channel *)
| pr_restrict : proc -> proc
| g : gproc -> proc

with gproc : Type :=
(* The Success operation *)
| gpr_success : gproc
(* The Process that does nothing *)
| gpr_nil : gproc
(* An input is a name of a channel, an input variable, followed by a process *)
| gpr_input : ChannelData ->  proc -> gproc
(* A tau action : does nothing *)
| gpr_tau : proc -> gproc
(* To choose between two processes *)
| gpr_choice : gproc -> gproc -> gproc
.

Coercion pr_var : nat >-> proc.
Coercion g : gproc >-> proc.


(*Some notation to simplify the view of the code*)

Notation "①" := (gpr_success).
Notation "𝟘" := (gpr_nil).
Notation "'rec' x '•' p" := (pr_rec x p) (at level 50).
Notation "P + Q" := (gpr_choice P Q).
Notation "P ‖ Q" := (pr_par P Q) (at level 50).
Notation "c ! v • 𝟘" := (pr_output c v) (at level 50).
Notation "c ? P" := (gpr_input c P) (at level 50).
Notation "'𝛕' • P" := (gpr_tau P) (at level 50).
Notation "'ν' P" := (pr_restrict P) (at level 50).
Notation "'If' C 'Then' P 'Else' Q" := (pr_if_then_else C P Q)
(at level 200, right associativity, format
"'[v   ' 'If'  C '/' '[' 'Then'  P  ']' '/' '[' 'Else'  Q ']' ']'").

(*Definition of the Substitution *)
Definition subst_Data (k : nat) (X : Data) (Y : Data) : Data := 
match Y with
| cst v => cst v
| bvar i => if (decide(i = k)) then X (* else bvar i *) else if (decide(i < k)) then bvar i
                                                              else bvar (Nat.pred i)
end.

Definition subst_in_Equation (k : nat) (X : Data) (E : Equation Data) : Equation Data :=
match E with 
| D1 == D2 => (subst_Data k X D1) == (subst_Data k X D2)
end.

Definition Succ_bvar (X : Data) : Data :=
match X with
| cst v => cst v
| bvar i => bvar (S i)
end.

Fixpoint subst_in_proc (k : nat) (X : Data) (p : proc) {struct p} : proc :=
match p with
| P ‖ Q => (subst_in_proc k X P) ‖ (subst_in_proc k X Q)
| pr_var i => pr_var i
| rec x • P =>  rec x • (subst_in_proc k X P)
| If C Then P Else Q => If (subst_in_Equation k X C) Then (subst_in_proc k X P) Else (subst_in_proc k X Q)
| c ! v • 𝟘 => c ! (subst_Data k X v) • 𝟘
| ν P => ν (subst_in_proc k X P)
| g M => subst_in_gproc k X M
end

with subst_in_gproc k X M {struct M} : gproc :=
match M with 
| ① => ①
| 𝟘 => 𝟘
| c ? p => c ? (subst_in_proc (S k) (Succ_bvar X) p)  (* Succ_bvar X = NewVar_in_Data 0 v *)
| 𝛕 • p => 𝛕 • (subst_in_proc k X p)
| p1 + p2 => (subst_in_gproc k X p1) + (subst_in_gproc k X p2)
end.


Notation "t1 ^ x1" := (subst_in_proc 0 x1 t1).


Definition NewVar_in_Data (k : nat) (Y : Data) : Data := 
match Y with
| cst v => cst v
| bvar i => if (decide(k < S i)) then bvar (S i) else bvar i
end.

Definition NewVar_in_Equation (k : nat) (E : Equation Data) : Equation Data :=
match E with
| D1 == D2 => (NewVar_in_Data k D1) == (NewVar_in_Data k D2)
end.

(* Definition NewVar_in_ext (k : nat) (μ : ExtAct TypeOfActions) : ExtAct TypeOfActions :=
match μ with
| ActIn (c ⋉ v) => ActIn (c ⋉ (NewVar_in_Data k v))
| ActOut (c ⋉ v) => ActOut (c ⋉ (NewVar_in_Data k v))
end. *)

Fixpoint NewVar (k : nat) (p : proc) {struct p} : proc :=
match p with
| P ‖ Q => (NewVar k P) ‖ (NewVar k Q)
| pr_var i => pr_var i
| rec x • P =>  rec x • (NewVar k P)
| If C Then P Else Q => If (NewVar_in_Equation k C)
                          Then (NewVar k P)
                          Else (NewVar k Q)
| c ! v • 𝟘 => c ! (NewVar_in_Data k v) • 𝟘
| ν P => ν (NewVar k P)
| g M => gNewVar k M
end

with gNewVar k M {struct M} : gproc :=
match M with 
| ① => ①
| 𝟘 => 𝟘
| c ? p => c ? (NewVar (S k) p)
| 𝛕 • p => 𝛕 • (NewVar k p)
| p1 + p2 => (gNewVar k p1) + (gNewVar k p2)
end.

Definition NewVar_in_ChannelData (k : nat) (Y : ChannelData) : ChannelData := 
match Y with
| cstC v => cstC v
| bvarC i => if (decide(k < (S i))) then bvarC (S i) else bvarC i
end.

Fixpoint NewVarC (k : nat) (p : proc) {struct p} : proc :=
match p with
| P ‖ Q => (NewVarC k P) ‖ (NewVarC k Q)
| pr_var i => pr_var i
| rec x • P =>  rec x • (NewVarC k P)
| If C Then P Else Q => If C
                          Then (NewVarC k P)
                          Else (NewVarC k Q)
| c ! v • 𝟘 => (NewVar_in_ChannelData k c) ! v • 𝟘
| ν P => ν (NewVarC (S k) P)
| g M => gNewVarC k M
end

with gNewVarC k M {struct M} : gproc :=
match M with 
| ① => ①
| 𝟘 => 𝟘
| c ? p => (NewVar_in_ChannelData k c) ? (NewVarC k p)
| 𝛕 • p => 𝛕 • (NewVarC k p)
| p1 + p2 => (gNewVarC k p1) + (gNewVarC k p2)
end.

Definition VarC_add (k : nat) (c : ChannelData) : ChannelData :=
match c with
| cstC c => cstC c
| bvarC i => bvarC (k + i)
end.

Definition VarC_TypeOfActions_add (k : nat) (a : TypeOfActions) : TypeOfActions :=
match a with
| (c ⋉ v) => (VarC_add k c) ⋉ v
end.

Lemma VarC_TypeOfActions_add_add (k : nat) (i : nat) (a : TypeOfActions) :
        VarC_TypeOfActions_add k (VarC_TypeOfActions_add i a) = VarC_TypeOfActions_add (k + i) a.
Proof.
  revert i a.
  induction k; destruct a;destruct c; simpl ;eauto.
  f_equal. replace (k + (i + n))%nat with (k + i + n)%nat by lia. eauto.
Qed.

Definition VarC_action_add (k : nat) (μ : ExtAct TypeOfActions) : ExtAct TypeOfActions :=
match μ with
| ActIn (c ⋉ v) => ActIn ((VarC_add k c) ⋉ v)
| ActOut (c ⋉ v) => ActOut ((VarC_add k c) ⋉ v)
end.

Lemma VarC_action_add_add (k : nat) (i : nat) (μ : ExtAct TypeOfActions) :
        VarC_action_add k (VarC_action_add i μ) = VarC_action_add (k + i) μ.
Proof.
  revert k μ.
  induction k; destruct μ ; destruct a; destruct c; intros; simpl; eauto.
  + f_equal. f_equal. f_equal. lia.
  + f_equal. f_equal. f_equal. lia.
Qed.

(* Substitution for the Recursive Variable *)
Fixpoint pr_subst (id : nat) (p : proc) (q : proc) : proc :=
  match p with 
  | p1 ‖ p2 => (pr_subst id p1 q) ‖ (pr_subst id p2 q) 
  | pr_var id' => if decide (id = id') then q else p
  | rec id' • p => if decide (id = id') then p else rec id' • (pr_subst id p q)
  | If C Then P Else Q => If C Then (pr_subst id P q) Else (pr_subst id Q q)
  | c ! v • 𝟘 => c ! v • 𝟘
  | ν P => ν (pr_subst id P (NewVarC 0 q))
  | g gp => g (gpr_subst id gp q)
end

with gpr_subst id p q {struct p} := match p with
| ① => ①
| 𝟘 => 𝟘
| c ? p => c ? (pr_subst id p (NewVar 0 q))
| 𝛕 • p => 𝛕 • (pr_subst id p q)
| p1 + p2 => (gpr_subst id p1 q) + (gpr_subst id p2 q)
end.


(* The Labelled Transition System (LTS-transition) *)
Inductive lts : proc-> (ActIO TypeOfActions) -> proc -> Prop :=
(* The Input and the Output *)
| lts_input : forall {c v P},
    lts (c ? P) ((c ⋉ v) ?) (P^v)
| lts_output : forall {c v},
    lts (c ! v • 𝟘) ((c ⋉ v) !) 𝟘

(* The actions Tau *)
| lts_tau : forall {P},
    lts (𝛕 • P) τ P
| lts_recursion : forall {x P},
    lts (rec x • P) τ (pr_subst x P (rec x • P))
| lts_ifOne : forall {p p' q α E}, Eval_Eq E = Some true -> lts p α p' ->  
    lts (If E Then p Else q) α p'
| lts_ifZero : forall {p q q' α E}, Eval_Eq E = Some false -> lts q α q' -> 
    lts (If E Then p Else q) α q'

(* The actions for process restriction *)
| lts_res_ext : forall {p p' μ}, lts p (ActExt (VarC_action_add 1 μ)) p'
                    -> lts (ν p) (ActExt μ) (ν p')
| lts_res_tau : forall {p p'}, lts p τ p' -> lts (ν p) τ (ν p')


(* Communication of a channel output and input that have the same name *)
| lts_comL : forall {c v p1 p2 q1 q2},
    lts p1 ((c ⋉ v) !) p2 ->
    lts q1 ((c ⋉ v) ?) q2 ->
    lts (p1 ‖ q1) τ (p2 ‖ q2) 
| lts_comR : forall {c v p1 p2 q1 q2},
    lts p1 ((c ⋉ v) !) p2 ->
    lts q1 ((c ⋉ v) ?) q2 ->
    lts (q1 ‖ p1) τ (q2 ‖ p2)

(* The decoration for the transition system...*)
(* ...for the parallele *)   
| lts_parL : forall {α p1 p2 q},
    lts p1 α p2 ->
    lts (p1 ‖ q) α (p2 ‖ q)
| lts_parR : forall {α p q1 q2}, 
    lts q1 α q2 ->
    lts (p ‖ q1) α (p ‖ q2)
(* ...for the sum *)
| lts_choiceL : forall {p1 p2 q α},
    lts (g p1) α q -> 
    lts (p1 + p2) α q
| lts_choiceR : forall {p1 p2 q α},
    lts (g p2) α q -> 
    lts (p1 + p2) α q
.

Global Hint Constructors lts : cgr.

Fixpoint size (p : proc) := 
  match p with
  | p ‖ q  => S (size p + size q)
  | pr_var _ => 1
  | If C Then p Else q => S (size p + size q)
  | rec x • p => S (size p)
  | c ! v • 𝟘 => 1
  | ν P => S (size P)
  | g p => gsize p
  end

with gsize p :=
  match p with
  | ① => 1
  | 𝟘 => 0
  | c ? p => S (size p)
  | 𝛕 • p => S (size p)
  | p + q => S (gsize p + gsize q)
end.

Definition VarSwap_in_ChannelData (k0 : nat) (c : ChannelData) : ChannelData := 
match c with
| cstC v => cstC v
| bvarC k => if (decide (k = k0)) then bvarC (S k0)
                                  else if (decide (k = S k0)) then bvarC k0
                                                              else bvarC k
end.

Definition VarSwap_in_ext (k : nat) (μ : ExtAct TypeOfActions) : ExtAct TypeOfActions := 
match μ with
| ActIn (c ⋉ v) => ActIn ((VarSwap_in_ChannelData k c) ⋉ v)
| ActOut (c ⋉ v) => ActOut ((VarSwap_in_ChannelData k c) ⋉ v)
end.

Fixpoint VarSwap_in_proc (k0 : nat) (p : proc) {struct p} : proc :=
match p with
| P ‖ Q => (VarSwap_in_proc k0 P) ‖ (VarSwap_in_proc k0 Q)
| pr_var i => pr_var i
| rec x • P =>  rec x • (VarSwap_in_proc k0 P)
| If C Then P Else Q => If C
                          Then (VarSwap_in_proc k0 P)
                          Else (VarSwap_in_proc k0 Q)
| c ! v • 𝟘 => (VarSwap_in_ChannelData k0 c) ! v • 𝟘
| ν P => ν (VarSwap_in_proc (S k0) P)
| g M => gVarSwap_in_proc k0 M
end

with gVarSwap_in_proc k0 M {struct M} : gproc :=
match M with 
| ① => ①
| 𝟘 => 𝟘
| c ? p => (VarSwap_in_ChannelData k0 c) ? (VarSwap_in_proc k0 p)
| 𝛕 • p => 𝛕 • (VarSwap_in_proc k0 p)
| p1 + p2 => (gVarSwap_in_proc k0 p1) + (gVarSwap_in_proc k0 p2)
end.

Lemma subst_equation E k v x: Eval_Eq E = Some x -> Eval_Eq (subst_in_Equation k v E) = Some x.
Proof.
  intros. destruct E. destruct d; destruct d0; simpl in *; eauto ; try inversion H.
  destruct (decide (n = n0)).
  - inversion H; subst.
    destruct (decide (n0 = k)).
    + subst. destruct v. 
      rewrite decide_True; eauto.
      rewrite decide_True; eauto.
    + destruct (decide (n0 < k)).
      * rewrite decide_True; eauto.
      * rewrite decide_True; eauto.
  - inversion H; subst.
Qed.

Lemma NewVar_equation E k x : Eval_Eq E = Some x -> Eval_Eq (NewVar_in_Equation k E) = Some x.
Proof.
  intros. destruct E. destruct d; destruct d0; simpl in *; eauto; try inversion H.
  destruct (decide (n = n0)).
  - inversion H; subst.
    destruct (decide ((k < S n0))).
    + rewrite decide_True; eauto.
    + rewrite decide_True; eauto.
  - inversion H; subst.
Qed.

Lemma subst_and_VarSwap k k0 v p : subst_in_proc k v (VarSwap_in_proc k0 p) = (VarSwap_in_proc k0 (subst_in_proc k v p)).
Proof. 
  revert k k0 v.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *.
  + assert (subst_in_proc k v (VarSwap_in_proc k0 p1) = VarSwap_in_proc k0 (subst_in_proc k v p1)) as eq1.
    { eapply Hp. simpl. lia. }
    assert (subst_in_proc k v (VarSwap_in_proc k0 p2) = VarSwap_in_proc k0 (subst_in_proc k v p2)) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto.
  + reflexivity.
  + assert (subst_in_proc k v (VarSwap_in_proc k0 p) = VarSwap_in_proc k0 (subst_in_proc k v p)) as eq.
    { eapply Hp. simpl. lia. }
    rewrite eq. eauto.
  + assert (subst_in_proc k v (VarSwap_in_proc k0 p1) = VarSwap_in_proc k0 (subst_in_proc k v p1)) as eq1.
    { eapply Hp. simpl. lia. }
    assert (subst_in_proc k v (VarSwap_in_proc k0 p2) = VarSwap_in_proc k0 (subst_in_proc k v p2)) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto.
  + eauto.
  + assert (subst_in_proc k v (VarSwap_in_proc (S k0) p) = VarSwap_in_proc (S k0) (subst_in_proc k v p)) as eq.
    { eapply Hp. simpl. lia. }
    rewrite eq. eauto.
  + destruct g0; simpl in *.
    * reflexivity.
    * reflexivity.
    * assert ((subst_in_proc (S k) (Succ_bvar v) (VarSwap_in_proc k0 p)) 
          = (VarSwap_in_proc k0 (subst_in_proc (S k) (Succ_bvar v) p))) as eq.
      { eapply Hp. simpl. lia. }
      rewrite eq. eauto.
   * assert (subst_in_proc k v (VarSwap_in_proc k0 p) = VarSwap_in_proc k0 (subst_in_proc k v p)) as eq.
     { eapply Hp. simpl. lia. }
     rewrite eq. eauto.
   * assert (subst_in_proc k v (VarSwap_in_proc k0 (g g0_1)) = VarSwap_in_proc k0 (subst_in_proc k v (g g0_1))) as eq1.
     { eapply Hp. simpl. lia. }
     assert (subst_in_proc k v (VarSwap_in_proc k0 (g g0_2)) = VarSwap_in_proc k0 (subst_in_proc k v (g g0_2))) as eq2.
     { eapply Hp. simpl. lia. } simpl in *. inversion eq1. inversion eq2.
     rewrite H0 , H1. eauto.
Qed.

Lemma subst_and_NewVarC k j v q : subst_in_proc k v (NewVarC j q) = NewVarC j (subst_in_proc k v q).
Proof.
  revert k j v.
  induction q as (q & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct q; intros; simpl in *.
  + assert (subst_in_proc k v (NewVarC j q1) = NewVarC j (subst_in_proc k v q1)) as eq1.
    { eapply Hp. simpl. lia. }
    assert (subst_in_proc k v (NewVarC j q2) = NewVarC j (subst_in_proc k v q2)) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1 , eq2. eauto.
  + eauto.
  + assert (subst_in_proc k v (NewVarC j q) = NewVarC j (subst_in_proc k v q)) as eq.
    { eapply Hp. simpl. lia. }
    rewrite eq. eauto.
  + assert (subst_in_proc k v (NewVarC j q1) = NewVarC j (subst_in_proc k v q1)) as eq1.
    { eapply Hp. simpl. lia. }
    assert (subst_in_proc k v (NewVarC j q2) = NewVarC j (subst_in_proc k v q2)) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1 , eq2. eauto.
  + eauto.
  + assert (subst_in_proc k v (NewVarC (S j) q) = NewVarC (S j) (subst_in_proc k v q)) as eq1.
    { eapply Hp. simpl. eauto. }
    rewrite eq1. eauto.
  + destruct g0; simpl in *.
    * eauto.
    * eauto.
    * assert ((subst_in_proc (S k) (Succ_bvar v) (NewVarC j p))
        = (NewVarC j (subst_in_proc (S k) (Succ_bvar v) p))) as eq.
      { eapply Hp. simpl. lia. }
      rewrite eq. eauto.
    * assert (subst_in_proc k v (NewVarC j p) = NewVarC j (subst_in_proc k v p)) as eq.
      { eapply Hp. simpl. lia. }
      rewrite eq. eauto.
    * assert (subst_in_proc k v (NewVarC j (g g0_1)) = NewVarC j (subst_in_proc k v (g g0_1))) as eq1.
      { eapply Hp. simpl. lia. }
      assert (subst_in_proc k v (NewVarC j (g g0_2)) = NewVarC j (subst_in_proc k v (g g0_2))) as eq2.
      { eapply Hp. simpl. lia. } inversion eq1. inversion eq2. eauto.
Qed.

Lemma NewVar_and_VarSwap j k0 p : (NewVar j (VarSwap_in_proc k0 p) = VarSwap_in_proc k0 (NewVar j p)).
Proof.
  revert j k0.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *.
  + assert (NewVar j (VarSwap_in_proc k0 p1) = VarSwap_in_proc k0 (NewVar j p1)) as eq1.
    { eapply Hp. simpl. lia. }
    assert (NewVar j (VarSwap_in_proc k0 p2) = VarSwap_in_proc k0 (NewVar j p2)) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto.
  + reflexivity.
  + assert (NewVar j (VarSwap_in_proc k0 p) = VarSwap_in_proc k0 (NewVar j p)) as eq.
    { eapply Hp. simpl. lia. }
    rewrite eq. eauto.
  + assert (NewVar j (VarSwap_in_proc k0 p1) = VarSwap_in_proc k0 (NewVar j p1)) as eq1.
    { eapply Hp. simpl. lia. }
    assert (NewVar j (VarSwap_in_proc k0 p2) = VarSwap_in_proc k0 (NewVar j p2)) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto.
  + eauto.
  + assert (NewVar j (VarSwap_in_proc (S k0) p) = VarSwap_in_proc (S k0) (NewVar j p)) as eq.
    { eapply Hp. simpl. lia. }
    rewrite eq. eauto.
  + destruct g0; simpl in *.
    * reflexivity.
    * reflexivity.
    * assert (NewVar (S j) (VarSwap_in_proc k0 p) = VarSwap_in_proc k0 (NewVar (S j) p)) as eq.
      { eapply Hp. simpl. lia. }
      rewrite eq. eauto.
   * assert (NewVar j (VarSwap_in_proc k0 p) = VarSwap_in_proc k0 (NewVar j p)) as eq.
     { eapply Hp. simpl. lia. }
     rewrite eq. eauto.
   * assert (NewVar j (VarSwap_in_proc k0 (g g0_1)) = VarSwap_in_proc k0 (NewVar j (g g0_1))) as eq1.
     { eapply Hp. simpl. lia. }
     assert (NewVar j (VarSwap_in_proc k0 (g g0_2)) = VarSwap_in_proc k0 (NewVar j (g g0_2))) as eq2.
     { eapply Hp. simpl. lia. } simpl in *. inversion eq1. inversion eq2.
     rewrite H0 , H1. eauto.
Qed.

Lemma NewVar_and_NewVarC j k p : (NewVar k (NewVarC j p) = (NewVarC j (NewVar k p))).
Proof.
  revert j k.
  (* Induction on the size of p*)
  induction p as (p & Hp) using
      (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros; destruct p ; simpl in *.
  + assert (NewVar k (NewVarC j p1) = NewVarC j (NewVar k p1)) as eq1.
    { eapply Hp; simpl ; lia. }
    assert (NewVar k (NewVarC j p2) = NewVarC j (NewVar k p2)) as eq2.
    { eapply Hp; simpl ; lia. }
    rewrite eq1, eq2. eauto.
  + eauto.
  + assert (NewVar k (NewVarC j p) = NewVarC j (NewVar k p)) as eq.
    { eapply Hp; simpl ; lia. }
    rewrite eq. eauto.
  + assert (NewVar k (NewVarC j p1) = NewVarC j (NewVar k p1)) as eq1.
    { eapply Hp; simpl ; lia. }
    assert (NewVar k (NewVarC j p2) = NewVarC j (NewVar k p2)) as eq2.
    { eapply Hp; simpl ; lia. }
    rewrite eq1, eq2. eauto.
  + eauto.
  + assert (NewVar k (NewVarC (S j) p) = NewVarC (S j) (NewVar k p)) as eq.
    { eapply Hp; simpl ; lia. }
    rewrite eq. eauto.
  + destruct g0; simpl in *.
    * eauto.
    * eauto.
    * assert (NewVar (S k) (NewVarC j p) = NewVarC j (NewVar (S k) p)) as eq.
      { eapply Hp; simpl ; lia. }
      rewrite eq. eauto.
    * assert (NewVar k (NewVarC j p) = NewVarC j (NewVar k p)) as eq.
      { eapply Hp; simpl ; lia. }
      rewrite eq. eauto.
    * assert (NewVar k (NewVarC j (g g0_1)) = NewVarC j (NewVar k (g g0_1))) as eq1.
      { eapply Hp; simpl ; lia. }
      assert (NewVar k (NewVarC j (g g0_2)) = NewVarC j (NewVar k (g g0_2))) as eq2.
      { eapply Hp; simpl ; lia. } inversion eq1. inversion eq2.
      rewrite H0, H1. eauto.
Qed.

Lemma NewVar_in_ChannelData_and_VarSwap_in_ChannelData j k0 c :
(NewVar_in_ChannelData (S (S (j + k0))) (VarSwap_in_ChannelData k0 c)
        = VarSwap_in_ChannelData k0 (NewVar_in_ChannelData (S (S (j + k0))) c)).
Proof.
  destruct c.
  + simpl. reflexivity.
  + simpl. destruct (decide (n = k0)).
    - subst. simpl. destruct (decide (j + k0 < k0)).
      * rewrite decide_True; try lia.
      * rewrite decide_False; try lia.
        rewrite decide_False; try lia. simpl.
        rewrite decide_True; try lia. eauto.
    - simpl. destruct (decide ((n = S k0)%nat)); subst. 
      * simpl. destruct (decide ((S (S (j + k0)) < S k0)%nat)); subst.
        ++ rewrite decide_False; try lia.
        ++ rewrite decide_False; try lia. simpl.
           rewrite decide_False; try lia.
           rewrite decide_True; try lia. eauto.
      * destruct (decide (S (S (j + k0)) < S n)).
        ++ simpl. rewrite decide_True; try lia.
           destruct (decide ((S n = k0))).
           ** subst. lia.
           ** rewrite decide_False; try lia. eauto.
        ++ simpl. rewrite decide_False; try lia.
           rewrite decide_False; eauto.
           rewrite decide_False; try lia. eauto.
Qed.

Lemma NewVarC_and_VarSwap j k0 p : (NewVarC (S (S (j + k0))) (VarSwap_in_proc k0 p) = VarSwap_in_proc k0 (NewVarC (S (S (j + k0))) p)).
Proof.
  revert j k0.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *.
  + assert (NewVarC (S (S (j + k0))) (VarSwap_in_proc k0 p1) = VarSwap_in_proc k0 (NewVarC (S (S (j + k0))) p1)) as eq1.
    { eapply Hp. simpl. lia. }
    assert (NewVarC (S (S (j + k0))) (VarSwap_in_proc k0 p2) = VarSwap_in_proc k0 (NewVarC (S (S (j + k0))) p2)) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto.
  + reflexivity.
  + assert (NewVarC (S (S (j + k0))) (VarSwap_in_proc k0 p) = VarSwap_in_proc k0 (NewVarC (S (S (j + k0))) p)) as eq.
    { eapply Hp. simpl. lia. }
    rewrite eq. eauto.
  + assert (NewVarC (S (S (j + k0))) (VarSwap_in_proc k0 p1) = VarSwap_in_proc k0 (NewVarC (S (S (j + k0))) p1)) as eq1.
    { eapply Hp. simpl. lia. }
    assert (NewVarC (S (S (j + k0))) (VarSwap_in_proc k0 p2) = VarSwap_in_proc k0 (NewVarC (S (S (j + k0))) p2)) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto.
  + rewrite NewVar_in_ChannelData_and_VarSwap_in_ChannelData. eauto.
  + assert (S (S (S (j + k0))) = S (S (j + (S k0)))) as eq' by lia. rewrite eq'.
    assert (NewVarC (S (S (j + (S k0)))) (VarSwap_in_proc (S k0) p)
        = VarSwap_in_proc (S k0) (NewVarC (S (S (j + (S k0)))) p)) as eq.
    { eapply Hp. simpl. lia. }
    rewrite eq. eauto.
  + destruct g0; simpl in *.
    * reflexivity.
    * reflexivity.
    * assert (NewVarC (S (S (j + k0))) (VarSwap_in_proc k0 p) = VarSwap_in_proc k0 (NewVarC (S (S (j + k0))) p)) as eq1.
      { eapply Hp. simpl. lia. } rewrite eq1.
      rewrite NewVar_in_ChannelData_and_VarSwap_in_ChannelData. eauto.
   * assert (NewVarC (S (S (j + k0))) (VarSwap_in_proc k0 p) = VarSwap_in_proc k0 (NewVarC (S (S (j + k0))) p)) as eq.
     { eapply Hp. simpl. lia. }
     rewrite eq. eauto.
   * assert (NewVarC (S (S (j + k0))) (VarSwap_in_proc k0 (g g0_1)) = VarSwap_in_proc k0 (NewVarC (S (S (j + k0))) (g g0_1))) as eq1.
     { eapply Hp. simpl. lia. }
     assert (NewVarC (S (S (j + k0))) (VarSwap_in_proc k0 (g g0_2)) = VarSwap_in_proc k0 (NewVarC (S (S (j + k0))) (g g0_2))) as eq2.
     { eapply Hp. simpl. lia. } simpl in *. inversion eq1. inversion eq2.
     rewrite H0 , H1. eauto.
Qed.

Lemma NewVar_in_ChannelData_and_NewVar_in_ChannelData i j c :
    NewVar_in_ChannelData (i + (S j)) (NewVar_in_ChannelData i c) 
      = NewVar_in_ChannelData i (NewVar_in_ChannelData ( i + j ) c).
Proof.
  destruct c. simpl.
  + eauto.
  + simpl. destruct (decide ((i < S n))).
    - simpl. destruct (decide (i + j < S n)).
      * rewrite decide_True; try lia. simpl.
        rewrite decide_True; try lia. eauto.
      * rewrite decide_False; try lia. simpl.
        rewrite decide_True; try lia. eauto.
    - simpl. rewrite decide_False; try lia.
      rewrite decide_False; try lia. simpl.
      rewrite decide_False; try lia. eauto.
Qed.

Lemma NewVarC_and_NewVarC i j p : NewVarC (i + (S j)) (NewVarC i p) = NewVarC i (NewVarC ( i + j ) p).
Proof.
  revert i j.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *.
  + assert ((NewVarC (i + S j) (NewVarC i p1)) = (NewVarC i (NewVarC (i + j) p1))) as eq1.
    { eapply Hp. simpl. lia. } rewrite eq1.
    assert ((NewVarC (i + S j) (NewVarC i p2)) = (NewVarC i (NewVarC (i + j) p2))) as eq2.
    { eapply Hp. simpl. lia. } rewrite eq2. eauto.
  + eauto.
  + assert ((NewVarC (i + S j) (NewVarC i p)) = (NewVarC i (NewVarC (i + j) p))) as eq.
      { eapply Hp. simpl. eauto. } rewrite eq. eauto.
  + assert ((NewVarC (i + S j) (NewVarC i p1)) = (NewVarC i (NewVarC (i + j) p1))) as eq1.
    { eapply Hp. simpl. lia. } rewrite eq1.
    assert ((NewVarC (i + S j) (NewVarC i p2)) = (NewVarC i (NewVarC (i + j) p2))) as eq2.
    { eapply Hp. simpl. lia. } rewrite eq2. eauto.
  + rewrite NewVar_in_ChannelData_and_NewVar_in_ChannelData. eauto.
  + assert (NewVarC (S (i + S j)) (NewVarC (S i) p) = NewVarC (S i) (NewVarC (S (i + j)) p)) as eq.
    { replace ((S (i + S j))) with ((S i) + S j)%nat; try lia.
      replace (S (i + j)) with ((S i) + j)%nat; try lia. eapply Hp.
      simpl. lia. } rewrite eq. eauto.
  + destruct g0; simpl.
    * eauto.
    * eauto.
    * rewrite NewVar_in_ChannelData_and_NewVar_in_ChannelData.
      assert ((NewVarC (i + S j) (NewVarC i p)) = (NewVarC i (NewVarC (i + j) p))) as eq.
      { eapply Hp. simpl. eauto. } rewrite eq. eauto.
    * assert ((NewVarC (i + S j) (NewVarC i p)) = (NewVarC i (NewVarC (i + j) p))) as eq.
      { eapply Hp. simpl. eauto. } rewrite eq. eauto.
    * assert ((NewVarC (i + S j) (NewVarC i (g g0_1))) = (NewVarC i (NewVarC (i + j) (g g0_1)))) as eq1.
      { eapply Hp. simpl. lia. } inversion eq1.
      assert ((NewVarC (i + S j) (NewVarC i (g g0_2))) = (NewVarC i (NewVarC (i + j) (g g0_2)))) as eq2.
      { eapply Hp. simpl. lia. } inversion eq2. eauto.
Qed.

Lemma VarSwap_NewVarC_in_ChannelData k c : NewVar_in_ChannelData k (NewVar_in_ChannelData k c) 
  = VarSwap_in_ChannelData k (NewVar_in_ChannelData k (NewVar_in_ChannelData k c)).
Proof.
  destruct c; simpl.
  + eauto.
  + destruct (decide (k < S n)).
    * simpl. rewrite decide_True; try lia.
      simpl. rewrite decide_False; try lia.
      rewrite decide_False; try lia. eauto.
    * simpl. rewrite decide_False; try lia.
      simpl. rewrite decide_False; try lia.
      rewrite decide_False; try lia. eauto.
Qed.

Lemma VarSwap_NewVarC k q : NewVarC k (NewVarC k q) = VarSwap_in_proc k (NewVarC k (NewVarC k q)).
Proof.
  revert k.
  induction q as (q & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct q ; intros; simpl in *.
  + assert (NewVarC k (NewVarC k q1) = VarSwap_in_proc k (NewVarC k (NewVarC k q1))) as eq1.
    { eapply Hp. simpl. lia. }
    assert (NewVarC k (NewVarC k q2) = VarSwap_in_proc k (NewVarC k (NewVarC k q2))) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1 at 1. rewrite eq2 at 1. eauto.
  + eauto.
  + assert (NewVarC k (NewVarC k q) = VarSwap_in_proc k (NewVarC k (NewVarC k q))) as eq.
    { eapply Hp. simpl. lia. }
    rewrite eq at 1. eauto.
  + assert (NewVarC k (NewVarC k q1) = VarSwap_in_proc k (NewVarC k (NewVarC k q1))) as eq1.
    { eapply Hp. simpl. lia. }
    assert (NewVarC k (NewVarC k q2) = VarSwap_in_proc k (NewVarC k (NewVarC k q2))) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1 at 1. rewrite eq2 at 1. eauto.
  + rewrite VarSwap_NewVarC_in_ChannelData at 1. eauto.
  + assert (NewVarC (S k) (NewVarC (S k) q) = VarSwap_in_proc (S k) (NewVarC (S k) (NewVarC (S k) q))) as eq.
    { eapply Hp. simpl. lia. }
    rewrite eq at 1. eauto.
  + destruct g0; simpl in *.
    * eauto.
    * eauto.
    * assert (NewVarC k (NewVarC k p) = VarSwap_in_proc k (NewVarC k (NewVarC k p))) as eq.
      { eapply Hp. simpl. lia. }
      rewrite eq at 1. eauto. rewrite VarSwap_NewVarC_in_ChannelData at 1.
      eauto.
    * assert (NewVarC k (NewVarC k p) = VarSwap_in_proc k (NewVarC k (NewVarC k p))) as eq.
      { eapply Hp. simpl. lia. }
      rewrite eq at 1. eauto.
    * assert (NewVarC k (NewVarC k (g g0_1)) = VarSwap_in_proc k (NewVarC k (NewVarC k (g g0_1)))) as eq1.
      { eapply Hp. simpl. lia. }
      assert (NewVarC k (NewVarC k (g g0_2)) = VarSwap_in_proc k (NewVarC k (NewVarC k (g g0_2)))) as eq2.
      { eapply Hp. simpl. lia. } inversion eq1. inversion eq2. eauto.
Qed.

Lemma pr_subst_and_VarSwap n p0 k q : pr_subst n (VarSwap_in_proc k p0) (NewVarC k (NewVarC k q)) 
      = VarSwap_in_proc k (pr_subst n p0 (NewVarC k (NewVarC k q))).
Proof.
  revert n k q.
  induction p0 as (p0 & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros; destruct p0; simpl in *.
  + assert (pr_subst n (VarSwap_in_proc k p0_1) (NewVarC k (NewVarC k q))
       = VarSwap_in_proc k (pr_subst n p0_1 (NewVarC k (NewVarC k q)))) as eq1.
    { eapply Hp. simpl. lia. }
    assert (pr_subst n (VarSwap_in_proc k p0_2) (NewVarC k (NewVarC k q))
       = VarSwap_in_proc k (pr_subst n p0_2 (NewVarC k (NewVarC k q)))) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto.
  + destruct (decide (n = n0)); subst.
    ++ simpl. rewrite VarSwap_NewVarC at 1. eauto.
    ++ simpl. eauto.
  + destruct (decide (n = n0)); subst.
    ++ eauto.
    ++ simpl. assert (pr_subst n (VarSwap_in_proc k p0) (NewVarC k (NewVarC k q)) 
          = VarSwap_in_proc k (pr_subst n p0 (NewVarC k (NewVarC k q)))) as eq.
       { eapply Hp. simpl. lia. }
       rewrite eq. eauto.
  + assert (pr_subst n (VarSwap_in_proc k p0_1) (NewVarC k (NewVarC k q))
      = VarSwap_in_proc k (pr_subst n p0_1 (NewVarC k (NewVarC k q)))) as eq1.
    { eapply Hp. simpl. lia. }
    assert (pr_subst n (VarSwap_in_proc k p0_2) (NewVarC k (NewVarC k q))
      = VarSwap_in_proc k (pr_subst n p0_2 (NewVarC k (NewVarC k q)))) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto.
  + eauto.
  + assert (NewVarC (0 + (S k)) (NewVarC 0 q) = NewVarC 0 (NewVarC ( 0 + k ) q)) as eq.
    { rewrite NewVarC_and_NewVarC. eauto. }
    assert (NewVarC (0 + (S k)) (NewVarC 0 (NewVarC k q)) = NewVarC 0 (NewVarC ( 0 + k ) (NewVarC k q))) as eq2.
    { rewrite NewVarC_and_NewVarC. eauto. } simpl in *. rewrite<- eq2. rewrite<- eq.
    assert (pr_subst n (VarSwap_in_proc (S k) p0) (NewVarC (S k) (NewVarC (S k) (NewVarC 0 q)))
      = VarSwap_in_proc (S k) (pr_subst n p0 (NewVarC (S k) (NewVarC (S k) (NewVarC 0 q))))) as eq1.
    { eapply Hp. simpl. lia. } rewrite eq1. eauto.
  + destruct g0; simpl.
    * eauto.
    * eauto.
    * rewrite NewVar_and_NewVarC. rewrite NewVar_and_NewVarC.
      assert ((pr_subst n (VarSwap_in_proc k p) (NewVarC k (NewVarC k (NewVar 0 q))))
        = (VarSwap_in_proc k (pr_subst n p (NewVarC k (NewVarC k (NewVar 0 q)))))) as eq1.
      { eapply Hp. simpl. lia. } rewrite eq1. eauto.
    * assert (pr_subst n (VarSwap_in_proc k p) (NewVarC k (NewVarC k q))
        = VarSwap_in_proc k (pr_subst n p (NewVarC k (NewVarC k q)))) as eq1.
      { eapply Hp. simpl. lia. } rewrite eq1. eauto.
    * assert (pr_subst n (VarSwap_in_proc k (g g0_1)) (NewVarC k (NewVarC k q))
        = VarSwap_in_proc k (pr_subst n (g g0_1) (NewVarC k (NewVarC k q)))) as eq1.
      { eapply Hp. simpl. lia. }
      assert (pr_subst n (VarSwap_in_proc k (g g0_2)) (NewVarC k (NewVarC k q))
        = VarSwap_in_proc k (pr_subst n (g g0_2) (NewVarC k (NewVarC k q)))) as eq2.
      { eapply Hp. simpl. lia. } inversion eq1. inversion eq2. eauto.
Qed.

Lemma pr_subst_and_NewVarC q0 q n k : (pr_subst n (NewVarC k q0) (NewVarC k q) = NewVarC k (pr_subst n q0 q)).
Proof.
  revert n k q.
  induction q0 as (q0 & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct q0; intros; simpl in *.
  + assert (pr_subst n (NewVarC k q0_1) (NewVarC k q) = NewVarC k (pr_subst n q0_1 q)) as eq1.
    { eapply Hp. simpl. lia. }
    assert (pr_subst n (NewVarC k q0_2) (NewVarC k q) = NewVarC k (pr_subst n q0_2 q)) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1 , eq2. eauto.
  + destruct (decide(n0 = n)).
    - eauto.
    - simpl. eauto.
  + destruct (decide(n0 = n)).
    - eauto.
    - simpl. assert (pr_subst n0 (NewVarC k q0) (NewVarC k q) = NewVarC k (pr_subst n0 q0 q)) as eq.
    { eapply Hp. simpl. lia. }
    rewrite eq. eauto.
  + assert (pr_subst n (NewVarC k q0_1) (NewVarC k q) = NewVarC k (pr_subst n q0_1 q)) as eq1.
    { eapply Hp. simpl. lia. }
    assert (pr_subst n (NewVarC k q0_2) (NewVarC k q) = NewVarC k (pr_subst n q0_2 q)) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1 , eq2. eauto.
  + eauto.
  + assert (NewVarC (0 + (S k)) (NewVarC 0 q) = NewVarC 0 (NewVarC ( 0 + k ) q)) as eq1.
    { rewrite NewVarC_and_NewVarC. eauto. }
    simpl in *. rewrite<- eq1.
    assert (pr_subst n (NewVarC (S k) q0) (NewVarC (S k) (NewVarC 0 q))
      = NewVarC (S k) (pr_subst n q0 (NewVarC 0 q))) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq2. eauto.
  + destruct g0; simpl in *.
    * eauto.
    * eauto.
    * simpl. rewrite NewVar_and_NewVarC.
      assert ((pr_subst n (NewVarC k p) (NewVarC k (NewVar 0 q))) = (NewVarC k (pr_subst n p (NewVar 0 q)))) as eq.
      { eapply Hp. simpl. lia. }
      rewrite eq. eauto.
    * assert (pr_subst n (NewVarC k p) (NewVarC k q) = NewVarC k (pr_subst n p q)) as eq.
      { eapply Hp. simpl. lia. }
      rewrite eq. eauto.
    * assert (pr_subst n (NewVarC k (g g0_1)) (NewVarC k q) = NewVarC k (pr_subst n (g g0_1) q)) as eq1.
      { eapply Hp. simpl. lia. }
      assert (pr_subst n (NewVarC k (g g0_2)) (NewVarC k q) = NewVarC k (pr_subst n (g g0_2) q)) as eq2.
      { eapply Hp. simpl. lia. } inversion eq1. inversion eq2. eauto.
Qed.

End VACCS_proc.

