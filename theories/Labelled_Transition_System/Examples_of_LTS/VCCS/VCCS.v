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
From TestingTheory Require Import Clos_n InputOutputActions ActTau.

(* Values and their bound variables *)
Inductive Data (MyType : Type) :=
| cst : MyType -> Data MyType
| bvar : nat -> Data MyType. (* variable as De Bruijn indices *)

Arguments bvar {_} _.
Arguments cst {_} _.

Local Coercion bvar : nat >-> Data.

Lemma Data_dec `{Countable MyType} : forall (x y : Data MyType) , {x = y} + {x <> y}.
Proof.
decide equality. 
* destruct (decide(m = m0)). left. assumption. right. assumption.
* destruct (decide (n = n0)). left. assumption. right. assumption.
Qed.

#[global] Instance data_eqdecision `{Countable MyType} : EqDecision (Data MyType).
  by exact Data_dec . Defined.

Definition encode_data `{Countable MyType} (C : Data MyType) : gen_tree (nat + MyType) :=
match C with
  | cst c => GenLeaf (inr c)
  | bvar i => GenLeaf (inl i)
end.

Definition decode_data `{Countable MyType} (tree : gen_tree (nat + MyType)) : Data MyType :=
match tree with
  | GenLeaf (inr c) => cst c
  | GenLeaf (inl i) => i
  | _ => 0
end.

Lemma encode_decide_datas `{Countable MyType} (c : Data MyType) : decode_data (encode_data c) = c.
Proof. case c. 
* intros. simpl. reflexivity.
* intros. simpl. reflexivity.
Qed.

#[global] Instance data_countable `{Countable MyType} : Countable (Data MyType).
Proof.
  refine (inj_countable' encode_data decode_data _).
  apply encode_decide_datas.
Qed.

(** * VCCS *)
(****************************** Channels  and Values *************************)
(** VCCS is parameterized over two countable sets. *)
(** Channel is the type of channels *)
(** Value is the type of data that can be transmitted over channels *)

Class VCCS_Parameters :=
  { Channel : Type;
    Value : Type;
    O : Value;
    Channel_eq_dec :: EqDecision Channel;
    ValueData_eq_dec :: EqDecision Value;
    VACCS_Channels :: Countable Channel;
    VACCS_Value :: Countable Value }.

Section VCCS_proc.

(** ** Definitions and properties of VACCS *)

Context `{VP : VCCS_Parameters}.

(********************************* Channels with free variables ************************************)
Definition ChannelData := Data (VP.(Channel)).

(********************************* Values with free variables ************************************)
Definition ValueData := Data (VP.(Value)).

Definition cst_channel (c : Channel) : ChannelData := cst c.
Definition cst_value (v : Value) : ValueData := cst v.

(********************************* Labels **********************************)
(* Label of action (other than tau), here it is a channel's name with data *)
Definition TypeOfActions := (ChannelData * ValueData)%type.

Definition ChannelData_of (a : TypeOfActions) : ChannelData := fst a.

Definition ValueData_of (a : TypeOfActions) : ValueData := snd a.

Definition ChannelData_of_ext (μ : ExtAct TypeOfActions) : ChannelData := 
match μ with 
| ActIn (c , v) => c
| ActOut (c , v) => c
end.

Definition ValueData_of_ext (μ : ExtAct TypeOfActions) : ValueData := 
match μ with 
| ActIn (c , v) => v
| ActOut (c , v) => v
end.

Inductive Equation (A : Type) : Type :=
| Equality : A -> A -> Equation A.

Arguments  Equality {_} _ _.

Notation "x == y" := (Equality x y) (at level 70).

Definition Eval_Eq (E : Equation ValueData) : option bool :=
match E with
| cst t == cst t' => if (decide (t = t')) then (Some true)
                                          else (Some false)
| bvar i == cst t => None
| cst t == bvar i => None
| bvar i == bvar i' => if (decide (i = i')) then (Some true)
                                          else None
end.

(* Definition of processes*)
Inductive proc : Type :=
(* To parallele two processes*)
| pr_par : proc -> proc -> proc
(* Variable in a process, for recursion and substitution*)
| pr_var : nat -> proc
(* recursion for process*)
| pr_rec : nat -> proc -> proc
(* If test *NEW term in comparison of CCS* *)
| pr_if_then_else : Equation ValueData -> proc -> proc -> proc
(* Restriction of a channel*)
| pr_restrict : proc -> proc
(*The Guards*)
| g : gproc -> proc

with gproc : Type :=
(* The Success operation*)
| gpr_success : gproc
(* The Process that does nothing*)
| gpr_nil : gproc
(*An input is a name of a channel, an input variable, followed by a process*)
| gpr_input : ChannelData -> proc -> gproc
(*An output is a name of a channel, an ouput value, followed by a process*)
| gpr_output : ChannelData -> ValueData -> proc -> gproc
(*A tau action : does nothing *)
| gpr_tau : proc -> gproc
(* To choose between two processes*)
| gpr_choice : gproc -> gproc -> gproc
.

Coercion pr_var : nat >-> proc.
Coercion g : gproc >-> proc.

(* Induction schemes *)
Scheme proc_ind0 := Induction for proc Sort Prop
with gproc_ind0 := Induction for gproc Sort Prop.

Combined Scheme proc_ind' from proc_ind0, gproc_ind0.

Local Definition proc_Prop (P : proc -> Prop) :=
  (forall p, P p) /\ (forall q, P (g q)).

(*Some notation to simplify the view of the code*)

Notation "①" := (gpr_success).
Notation "𝟘" := (gpr_nil).
Notation "'rec' x '•' p" := (pr_rec x p) (at level 50).
Notation "P + Q" := (gpr_choice P Q).
Notation "P ‖ Q" := (pr_par P Q) (at level 50).
Notation "c ! v • P" := (gpr_output c v P) (at level 50).
Notation "c ? P" := (gpr_input c P) (at level 50).
Notation "'𝛕' • P" := (gpr_tau P) (at level 50).
Notation "'ν' P" := (pr_restrict P) (at level 50).
Notation "'If' C 'Then' P 'Else' Q" := (pr_if_then_else C P Q)
(at level 200, right associativity, format
"'[v   ' 'If'  C '/' '[' 'Then'  P  ']' '/' '[' 'Else'  Q ']' ']'").

(*Definition of the Substitution *)
Definition subst_Data (k : nat) (X : ValueData) (Y : ValueData) : ValueData := 
match Y with
| cst v => cst v
| bvar i => if (decide(i = k)) then X (* else bvar i *) else if (decide(i < k)) then i
                                                              else Nat.pred i
end.

Definition subst_in_Equation (k : nat) (X : ValueData) (E : Equation ValueData) : Equation ValueData :=
match E with 
| D1 == D2 => (subst_Data k X D1) == (subst_Data k X D2)
end.

Definition Succ_bvar (X : ValueData) : ValueData :=
match X with
| cst v => cst v
| bvar i => S i
end.

Fixpoint subst_in_proc (k : nat) (X : ValueData) (p : proc) {struct p} : proc :=
match p with
| P ‖ Q => (subst_in_proc k X P) ‖ (subst_in_proc k X Q)
| pr_var i => pr_var i
| rec x • P => rec x • (subst_in_proc k X P)
| If C Then P Else Q => If (subst_in_Equation k X C)
                           Then (subst_in_proc k X P)
                           Else (subst_in_proc k X Q)
| ν P => ν (subst_in_proc k X P)
| g M => subst_in_gproc k X M
end

with subst_in_gproc k X M {struct M} : gproc :=
match M with 
| ① => ①
| 𝟘 => 𝟘
| c ? p => c ? (subst_in_proc (S k) (Succ_bvar X) p)
| c ! v • p => c ! (subst_Data k X v) • (subst_in_proc k X p)
| 𝛕 • p => 𝛕 • (subst_in_proc k X p)
| p1 + p2 => (subst_in_gproc k X p1) + (subst_in_gproc k X p2)
end.

Notation "t1 ^ x1" := (subst_in_proc 0 x1 t1).

Definition NewVar_in_Data (k : nat) (Y : ValueData) : ValueData := 
match Y with
| cst v => cst v
| bvar i => if (decide(k < S i)) then S i else i
end.

Definition NewVar_in_Equation (k : nat) (E : Equation ValueData) : Equation ValueData :=
match E with
| D1 == D2 => (NewVar_in_Data k D1) == (NewVar_in_Data k D2)
end.

Definition NewVar_in_ext (k : nat) (μ : ExtAct TypeOfActions) : ExtAct TypeOfActions :=
match μ with
| ActIn (c , v) => ActIn (c , NewVar_in_Data k v)
| ActOut (c , v) => ActOut (c , NewVar_in_Data k v)
end.

Fixpoint NewVar (k : nat) (p : proc) {struct p} : proc :=
match p with
| P ‖ Q => (NewVar k P) ‖ (NewVar k Q)
| pr_var i => pr_var i
| rec x • P =>  rec x • (NewVar k P)
| If C Then P Else Q => If (NewVar_in_Equation k C)
                          Then (NewVar k P)
                          Else (NewVar k Q)
| ν P => ν (NewVar k P)
| g M => gNewVar k M
end

with gNewVar k M {struct M} : gproc :=
match M with 
| ① => ①
| 𝟘 => 𝟘
| c ? p => c ? (NewVar (S k) p)
| c ! v • p => c ! (NewVar_in_Data k v) • (NewVar k p)
| 𝛕 • p => 𝛕 • (NewVar k p)
| p1 + p2 => (gNewVar k p1) + (gNewVar k p2)
end.

Definition NewVar_in_ChannelData (k : nat) (Y : ChannelData) : ChannelData := 
match Y with
| cst v => cst v
| bvar i => if (decide(k < (S i))) then S i else i
end.

Definition NewVarC_in_ext (k : nat) (μ : ExtAct TypeOfActions) : ExtAct TypeOfActions :=
match μ with
| ActIn (c , v) => ActIn (NewVar_in_ChannelData k c , v)
| ActOut (c , v) => ActOut (NewVar_in_ChannelData k c , v)
end.

Fixpoint NewVarC (k : nat) (p : proc) {struct p} : proc :=
match p with
| P ‖ Q => (NewVarC k P) ‖ (NewVarC k Q)
| pr_var i => pr_var i
| rec x • P =>  rec x • (NewVarC k P)
| If C Then P Else Q => If C
                          Then (NewVarC k P)
                          Else (NewVarC k Q)
| ν P => ν (NewVarC (S k) P)
| g M => gNewVarC k M
end

with gNewVarC k M {struct M} : gproc :=
match M with 
| ① => ①
| 𝟘 => 𝟘
| c ? p => (NewVar_in_ChannelData k c) ? (NewVarC k p)
| c ! v • p => (NewVar_in_ChannelData k c) ! v • (NewVarC k p)
| 𝛕 • p => 𝛕 • (NewVarC k p)
| p1 + p2 => (gNewVarC k p1) + (gNewVarC k p2)
end.

Definition VarC_add (k : nat) (c : ChannelData) : ChannelData :=
match c with
| cst c => cst c
| bvar i => bvar (k + i)
end.

Definition VarC_TypeOfActions_add (k : nat) (a : TypeOfActions) : TypeOfActions :=
match a with
| (c , v) => (VarC_add k c , v)
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
| ActIn ((c , v)) => ActIn ((VarC_add k c) , v)
| ActOut ((c , v)) => ActOut ((VarC_add k c) , v)
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
  | ν P => ν (pr_subst id P (NewVarC 0 q))
  | g gp => g (gpr_subst id gp q)
end

with gpr_subst id p q {struct p} := match p with
| ① => ①
| 𝟘 => 𝟘
| c ? p => c ? (pr_subst id p (NewVar 0 q))
| c ! v • p => c ! v • (pr_subst id p q)
| 𝛕 • p => 𝛕 • (pr_subst id p q)
| p1 + p2 => (gpr_subst id p1 q) + (gpr_subst id p2 q)
end.

(* The Labelled Transition System (LTS-transition) *)
Inductive lts : proc-> (ActIO TypeOfActions) -> proc -> Prop :=
(*The Input and the Output*)
| lts_input : forall {c v P},
    lts (c ? P) ((c , v) ?) (P^v)
| lts_output : forall {c v P},
    lts (c ! v • P) ((c , v) !) P

(*The actions Tau*)
| lts_tau : forall {P},
    lts (𝛕 • P) τ P 
| lts_recursion : forall {x P},
    lts (rec x • P) τ (pr_subst x P (rec x • P))

(*The actions for IF contructor*)
| lts_ifOne : forall {p p' q α E}, Eval_Eq E = Some true -> lts p α p' ->  
    lts (If E Then p Else q) α p'
| lts_ifZero : forall {p q q' α E}, Eval_Eq E = Some false -> lts q α q' -> 
    lts (If E Then p Else q) α q'

(*The actions for process restriction*)
| lts_res_ext : forall {p p' μ}, lts p (ActExt (VarC_action_add 1 μ)) p'
                    -> lts (ν p) (ActExt μ) (ν p')
| lts_res_tau : forall {p p'}, lts p τ p' -> lts (ν p) τ (ν p')

(* Communication of a channel output and input that have the same name*)
| lts_comL : forall {c v p1 p2 q1 q2},
    lts p1 ((c , v) !) p2 ->
    lts q1 ((c , v) ?) q2 ->
    lts (p1 ‖ q1) τ (p2 ‖ q2) 
| lts_comR : forall {c v p1 p2 q1 q2},
    lts p1 ((c ,  v) !) p2 ->
    lts q1 ((c , v) ?) q2 ->
    lts (q1 ‖ p1) τ (q2 ‖ p2)

(*The decoration for the transition system...*)
(*...for the parallele*)   
| lts_parL : forall {α p1 p2 q},
    lts p1 α p2 ->
    lts (p1 ‖ q) α (p2 ‖ q)
| lts_parR : forall {α p q1 q2}, 
    lts q1 α q2 ->
    lts (p ‖ q1) α (p ‖ q2)
(*...for the sum*)
| lts_choiceL : forall {p1 p2 q α},
    lts (g p1) α q -> 
    lts (p1 + p2) α q
| lts_choiceR : forall {p1 p2 q α},
    lts (g p2) α q -> 
    lts (p1 + p2) α q
.

Fixpoint size (p : proc) := 
  match p with
  | p ‖ q  => S (size p + size q)
  | pr_var _ => 1
  | If C Then p Else q => S (size p + size q)
  | rec x • p => S (size p)
  | ν P => S (size P)
  | g p => gsize p
  end

with gsize p :=
  match p with
  | ① => 1
  | 𝟘 => 0
  | c ? p => S (size p)
  | c ! v • p => S (size p)
  | 𝛕 • p => S (size p)
  | p + q => S (gsize p + gsize q)
end.

Hint Constructors lts:ccs.

Reserved Notation "p ≡ q" (at level 70).

Definition VarSwap_in_ChannelData (k0 : nat) (c : ChannelData) : ChannelData := 
match c with
| cst v => cst v
| bvar k => if (decide (k = k0)) then S k0
                                  else if (decide (k = S k0)) then k0
                                                              else k
end.

Definition VarSwap_in_ext (k : nat) (μ : ExtAct TypeOfActions) : ExtAct TypeOfActions := 
match μ with
| ActIn (c , v) => ActIn (VarSwap_in_ChannelData k c , v)
| ActOut (c , v) => ActOut (VarSwap_in_ChannelData k c , v)
end.

Fixpoint VarSwap_in_proc (k0 : nat) (p : proc) {struct p} : proc :=
match p with
| P ‖ Q => (VarSwap_in_proc k0 P) ‖ (VarSwap_in_proc k0 Q)
| pr_var i => pr_var i
| rec x • P =>  rec x • (VarSwap_in_proc k0 P)
| If C Then P Else Q => If C
                          Then (VarSwap_in_proc k0 P)
                          Else (VarSwap_in_proc k0 Q)
| ν P => ν (VarSwap_in_proc (S k0) P)
| g M => gVarSwap_in_proc k0 M
end

with gVarSwap_in_proc k0 M {struct M} : gproc :=
match M with 
| ① => ①
| 𝟘 => 𝟘
| c ? p => (VarSwap_in_ChannelData k0 c) ? (VarSwap_in_proc k0 p)
| c ! v • p => (VarSwap_in_ChannelData k0 c) ! v • (VarSwap_in_proc k0 p)
| 𝛕 • p => 𝛕 • (VarSwap_in_proc k0 p)
| p1 + p2 => (gVarSwap_in_proc k0 p1) + (gVarSwap_in_proc k0 p2)
end.

End VCCS_proc.

Local Coercion cst_channel : Channel >-> ChannelData.
Local Coercion cst_value : Value >-> ValueData.

Global Arguments  Equality {_} _ _.
Global Hint Constructors lts : cgr.
Global Notation "x == y" := (Equality x y) (at level 70).
Global Notation "①" := (gpr_success).
Global Notation "𝟘" := (gpr_nil).
Global Notation "'rec' x '•' p" := (pr_rec x p) (at level 50).
Global Notation "P + Q" := (gpr_choice P Q).
Global Notation "P ‖ Q" := (pr_par P Q) (at level 50).
Global Notation "c ! v • P" := (gpr_output c v P) (at level 50).
Global Notation "c ? P" := (gpr_input c P) (at level 50).
Global Notation "'𝛕' • P" := (gpr_tau P) (at level 50).
Global Notation "'ν' P" := (pr_restrict P) (at level 50).
Global Notation "'If' C 'Then' P 'Else' Q" := (pr_if_then_else C P Q)
(at level 200, right associativity, format
"'[v   ' 'If'  C '/' '[' 'Then'  P  ']' '/' '[' 'Else'  Q ']' ']'").
Global Notation "t1 ^ x1" := (subst_in_proc 0 x1 t1).

