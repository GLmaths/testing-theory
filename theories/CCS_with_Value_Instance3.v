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


Require Import Coq.Program.Equality Coq.Strings.String.
From stdpp Require Import base countable finite gmap list gmultiset strings.
Require Import Relations.
Require Import Coq.Wellfounded.Inverse_Image.


(* ChannelType est le type des canaux, par exemple des chaînes de caractères*)
(* ValueType est le type des données transmises, par exemple des entiers, des chaînes de caractères, des programmes (?) *)
Inductive ExtAct (ChannelType TransmittedDataType : Type) :=
| ActIn : ChannelType -> TransmittedDataType -> ExtAct ChannelType TransmittedDataType
| ActOut : ChannelType -> TransmittedDataType -> ExtAct ChannelType TransmittedDataType
.

(* Table des vérités *) 
(*Inductive Qbit :=
| one
| zero
| one_OR_zero
.*)


Arguments ActIn {_} {_} _ _.
Arguments ActOut {_} {_} _ _.

Inductive Act (ChannelType TransmittedDataType : Type) :=
| ActExt (μ: ExtAct ChannelType TransmittedDataType)
| τ
.
Arguments ActExt {_} {_} _.
Arguments τ {_} {_}.


Coercion ActExt : ExtAct >-> Act.

Parameter ChannelType : Type.
(*Exemple : Definition ChannelType := string.*)
(*(* All of this for multi-set ?*)
Hypothesis ChannelType_eq_dec : EqDecision ChannelType.
#[global] Instance ChannelType_eq_decision : EqDecision ChannelType.
Proof. exact ChannelType_eq_dec.
Qed.
Hypothesis ChannelType_countable : Countable ChannelType.
#[global] Instance ChannelType_is_countable : Countable ChannelType.
Proof. exact ChannelType_countable.
Qed.
#[global] Instance Singletons_of_ChannelType : SingletonMS (gmultiset ChannelType) (gmultiset ChannelType).
Proof. intro. exact H.
Qed.*)


Parameter ValueType : Type.
(*Exemple : Definition ValueType := nat.*)
(*(* All of this for multi-set ?*)
Hypothesis ValueType_eq_dec : EqDecision ValueType.
#[global] Instance ValueType_eq_decision : EqDecision ValueType.
Proof. exact ValueType_eq_dec.
Qed.
Hypothesis ValueType_countable : Countable ValueType.
#[global] Instance ValueType_is_countable : Countable ValueType.
Proof. exact ValueType_countable.
Qed.
#[global] Instance Singletons_of_ValueType : SingletonMS (gmultiset ValueType) (gmultiset ValueType).
Proof. intro. exact H.
Qed.*)

Definition names_of_fvar := string.

(*Inductive ChannelsVar :=
| fvarC : names_of_fvar -> ChannelsVar.
Coercion fvarC : names_of_fvar >-> ChannelsVar.

Inductive Channels :=
| channel : ChannelType -> Channels
| fvarCC : ChannelsVar -> Channels
| bvarC : nat -> Channels.
Coercion channel : ChannelType >-> Channels.
Coercion fvarCC : ChannelsVar >-> Channels.
Coercion bvarC : nat >-> Channels.*)

Inductive Channels :=
| channel : ChannelType -> Channels
| fvarC : names_of_fvar -> Channels
| bvarC : nat -> Channels.

Coercion channel : ChannelType >-> Channels.
Coercion fvarC : names_of_fvar >-> Channels.
Coercion bvarC : nat >-> Channels.

(*Inductive ValuesVar :=
| fvarV : names_of_fvar -> ValuesVar.
Coercion fvarV : names_of_fvar >-> ValuesVar.

Inductive Values :=
| value : ValueType -> Values
| fvarVV : ValuesVar -> Values
| bvarV : nat -> Values.

Coercion value : ValueType >-> Values.
Coercion fvarVV : ValuesVar >-> Values.
Coercion bvarV : nat >-> Values.*)



Inductive Values :=
| value : ValueType -> Values
| fvarV : names_of_fvar -> Values
| bvarV : nat -> Values.

Coercion value : ValueType >-> Values.
Coercion fvarV : names_of_fvar >-> Values.
Coercion bvarV : nat >-> Values.

Inductive ChannelsOrValuesWithoutVariables :=
| Chan : ChannelType -> ChannelsOrValuesWithoutVariables
| Val : ValueType -> ChannelsOrValuesWithoutVariables.
Coercion Chan : ChannelType >->  ChannelsOrValuesWithoutVariables.
Coercion Val : ValueType >->  ChannelsOrValuesWithoutVariables.
(*
#[global] Instance ChannelsOrValuesWithoutVariables_eq_decision : EqDecision ChannelsOrValuesWithoutVariables.
Proof. 
Admitted.
#[global] Instance ChannelsOrValuesWithoutVariables_is_countable : Countable ChannelsOrValuesWithoutVariables.
Proof.
Admitted.
#[global] Instance Singletons_of_ChannelsOrValuesWithoutVariables : SingletonMS ChannelsOrValuesWithoutVariables (gset ChannelsOrValuesWithoutVariables).
Proof.
Admitted.*)


Inductive ChannelsOrValues :=
| chan : Channels -> ChannelsOrValues
| val : Values -> ChannelsOrValues.
Coercion chan : Channels >->  ChannelsOrValues.
Coercion val : Values >->  ChannelsOrValues.

Inductive Equation (A : Type) : Type :=
| Equality : A -> A -> Equation A.

Arguments  Equality {_} _ _.

Notation "x == y" := (Equality x y) (at level 50).

Definition EquationOnChannels := Equation Channels.

Definition EquationOnValues := Equation Values.

Inductive EquationOnValueOrChannel :=
| EqChannel : EquationOnChannels -> EquationOnValueOrChannel
| EqValue : EquationOnValues -> EquationOnValueOrChannel.

Coercion EqChannel : EquationOnChannels >->  EquationOnValueOrChannel.
Coercion EqValue : EquationOnValues >->  EquationOnValueOrChannel.




(*
(*Names in a Equation of Channels, ignore variables *)
Definition RealNames_of_Channels (c : Channels) : gset ChannelsOrValuesWithoutVariables := 
match c with
| channel x => {[+ Chan x +]}
| fvarC i => ∅ 
| bvarC i => ∅
end.
Definition All_Names_of_EqChannel (E : EquationOnChannels) : gset ChannelsOrValuesWithoutVariables :=
match E with 
| a == b => (RealNames_of_Channels a) ∪ (RealNames_of_Channels b)
end.



(*Names in a Equation of Values, ignore variables *)
Definition RealNames_of_Values (v : Values) : gset ChannelsOrValuesWithoutVariables := 
match v with
| value x => {[+ Val x +]}
| fvarV i => ∅ 
| bvarV i => ∅
end.
Definition All_Names_of_EqValue (E : EquationOnValues) : gset ChannelsOrValuesWithoutVariables :=
match E with 
| a == b => (RealNames_of_Values a) ∪ (RealNames_of_Values b)
end.

Definition RealNames_of_ChannelsOrValues (C_or_V : ChannelsOrValues) : gset ChannelsOrValuesWithoutVariables := 
match C_or_V with
| chan c => RealNames_of_Channels c
| val v => RealNames_of_Values v
end.


(*Names in a Equation, ignore variables *)
Definition All_Names_of_Eq (E : EquationOnValueOrChannel) : gset ChannelsOrValuesWithoutVariables :=
match E with 
| EqChannel A => All_Names_of_EqChannel A
| EqValue B => All_Names_of_EqValue B
end.
*)

Inductive ChanOrVal :=
| IndicChan : ChanOrVal
| IndicVal : ChanOrVal.

(* Definition of processes*)
Inductive proc' : Type :=
(* To parallele two processes*)
| pr_par' : proc' -> proc' -> proc'
(* Variable in a process, for recursion and substitution*)
| pr_var' : nat -> proc'
(* recursion for process*)
| pr_rec' : nat -> proc' -> proc'
(* If test *NEW term in comparison of CCS* *)
| pr_if_then_else' : EquationOnValueOrChannel -> proc' -> proc' -> proc' 
(*The Guards*)
| g' : gproc' -> proc'

with gproc' : Type :=
(* The Success operation*)
| gpr_success' : gproc'
(* The Process that does nothing*)
| gpr_nil' : gproc'
(*An input is a name of a channel, an input variable, followed by a process*)
| gpr_input' : Channels -> ChanOrVal ->  proc' -> gproc'
(*An output is a name of a channel, an ouput value, followed by a process*)
| gpr_output' : Channels -> ChannelsOrValues -> proc' -> gproc'
(*A tau action : does nothing *)
| gpr_tau' : proc' -> gproc'
(* To choose between two processes*)
| gpr_choice' : gproc' -> gproc' -> gproc'
.

Coercion pr_var' : nat >-> proc'.
Coercion g' : gproc' >-> proc'.


(*Some notation to simplify the view of the code*)

Notation "①" := (gpr_success').
Notation "⓪" := (gpr_nil').
Notation "'rec' x '•' p" := (pr_rec' x p) (at level 50).
Notation "P + Q" := (gpr_choice' P Q).
Notation "P ‖ Q" := (pr_par' P Q) (at level 50).
Notation "c ! v • P" := (gpr_output' c v P) (at level 50).
Notation "c ? I • P" := (gpr_input' c I P) (at level 50).
Notation "'t' • P" := (gpr_tau' P) (at level 50).
Notation "'If' C 'Then' P 'Else' Q" := (pr_if_then_else' C P Q)
(at level 200, right associativity, format
"'[v   ' 'If'  C '/' '[' 'Then'  P  ']' '/' '[' 'Else'  Q ']' ']'").



(*
Fixpoint All_Names_of_proc' (p : proc') : gset ChannelsOrValuesWithoutVariables :=
match p with 
| P ‖ Q => (All_Names_of_proc' P) ∪ (All_Names_of_proc' Q)
| pr_var' i => ∅
| rec x • P =>  (All_Names_of_proc' P)
| If C Then P Else Q => (All_Names_of_Eq C) ∪ (All_Names_of_proc' P) ∪ (All_Names_of_proc' Q)
| g' x => All_Names_of_gproc' x
end

with All_Names_of_gproc' x :=
match x with 
| ① => ∅
| ⓪ => ∅
| c ? x • p' => (RealNames_of_Channels c) ∪ (All_Names_of_proc' p')
| c ! v • p' => (RealNames_of_Channels c) ∪ (RealNames_of_ChannelsOrValues v) ∪ All_Names_of_proc' p'
| t • p' => All_Names_of_proc' p'
| p1 + p2 => (All_Names_of_gproc' p1) ∪ (All_Names_of_gproc' p2)
end.
*)



Definition subst_Channels (k : nat) (X : Channels) (Y : Channels) : Channels := 
match Y with
| channel c => channel c
| fvarC i => fvarC i
| bvarC i => if (decide(i = k)) then X else bvarC i
end.
Definition subst_ChannelsUnTyped (k : nat) (X : ChannelsOrValues) (Y : Channels) : Channels :=
match X with
| chan C => (subst_Channels k C Y)
| val V => Y
end.
Definition subst_in_EqChannels (k : nat) (X : Channels) (E : EquationOnChannels) : EquationOnChannels :=
match E with 
| Chan1 == Chan2 => (subst_Channels k X Chan1) == (subst_Channels k X Chan2)
end.
Definition subst_in_EqChannelsUnTyped (k : nat) (X : ChannelsOrValues) (E : EquationOnChannels) : EquationOnValueOrChannel :=
match X with 
| chan c => EqChannel (subst_in_EqChannels k c E)
| val v => E
end.



Definition subst_Values (k : nat) (X : Values) (Y : Values) : Values := 
match Y with
| value v => value v
| fvarV i => fvarV i
| bvarV i => if (decide(i = k)) then X else bvarV i
end.
Definition subst_ValuesUnTyped (k : nat) (X : ChannelsOrValues) (Y : Values) : Values :=
match X with
| chan C => Y
| val V => (subst_Values k V Y)
end.
Definition subst_in_EqValues (k : nat) (X : Values) (E : EquationOnValues) : EquationOnValues :=
match E with 
| Val1 == Val2 => (subst_Values k X Val1) == (subst_Values k X Val2)
end.
Definition subst_in_EqValuesUnTyped (k : nat) (X : ChannelsOrValues) (E : EquationOnValues) : EquationOnValueOrChannel :=
match X with 
| chan c => E
| val v => EqValue (subst_in_EqValues k v E)
end.


(* Substitution for ChannelOrValues *)
Definition subst_in_ChannelsOrValues (k : nat) (X : ChannelsOrValues) (Y : ChannelsOrValues) : ChannelsOrValues :=
match Y with
| chan c => chan (subst_ChannelsUnTyped k X c)
| val v => val (subst_ValuesUnTyped k X v)
end.
Definition subst_in_Eq (k : nat) (X : ChannelsOrValues) (E : EquationOnValueOrChannel) : EquationOnValueOrChannel :=
match E with 
| EqChannel A => (subst_in_EqChannelsUnTyped k X A)
| EqValue B => (subst_in_EqValuesUnTyped k X B)
end.

Fixpoint subst_in_proc (k : nat) (X : ChannelsOrValues) (p : proc') {struct p} : proc' :=
match p with
| P ‖ Q => (subst_in_proc k X P) ‖ (subst_in_proc k X Q)
| pr_var' i => pr_var' i
| rec x • P =>  rec x • (subst_in_proc k X P)
| If C Then P Else Q => If (subst_in_Eq k X C) Then (subst_in_proc k X P) Else (subst_in_proc k X Q)
| g' M => subst_in_gproc k X M
end

with subst_in_gproc k X M {struct M} : gproc' :=
match M with 
| ① => ①
| ⓪ => ⓪
| c ? x • p' => (subst_ChannelsUnTyped k X c) ? x • (subst_in_proc (S k) X p')
| c ! v • p' => (subst_ChannelsUnTyped  k X c) ! (subst_in_ChannelsOrValues k X v) • (subst_in_proc k X p')
| t • p' => t • (subst_in_proc k X p')
| p1 + p2 => (subst_in_gproc k X p1) + (subst_in_gproc k X p2)
end.

Notation "t1 ^ x1" := (subst_in_proc 0 x1 t1).
Check ((bvarC 0) ! bvarV 1  • ⓪).
Compute (((bvarC 0) ! bvarC 0  • ⓪) ^ (fvarC "c")).
Check ((bvarC 0) ! (fvarC "x") • ⓪).
Check (fvarC "x" ? IndicChan • ((bvarC 0) ! (fvarV "x") • ⓪)).

Definition closing_Channels (k : nat) (i : names_of_fvar) (Y : Channels) : Channels := 
match Y with
| channel v => channel v
| fvarC j => if (decide(i = j)) then bvarC k else fvarC j
| bvarC j => bvarC j
end.
Definition closing_Values (k : nat) (i : names_of_fvar) (Y : Values) : Values := 
match Y with
| value v => value v
| fvarV j => if (decide(i = j)) then bvarV k else fvarV j
| bvarV j => bvarV j
end.
Definition closing_ChannelsUnTyped (k : nat) (i : names_of_fvar) (X : ChannelsOrValues) : ChannelsOrValues :=
match X with
| chan c =>  chan (closing_Channels k i c)
| val v => val v
end.
Definition Type_of (X : ChannelsOrValues) : Type :=
match X with
| chan c => Channels
| val v => Values
end.
Definition closing_ValuesUnTyped (k : nat) (i : names_of_fvar) (X : ChannelsOrValues) : ChannelsOrValues :=
match X with
| chan c =>  chan c
| val v => val (closing_Values k i v)
end.
Definition closing_ChannelsOrValues (Indic : ChanOrVal) (k : nat) (i : names_of_fvar) (X : ChannelsOrValues) : ChannelsOrValues :=
match Indic with
| IndicChan => (closing_ChannelsUnTyped k i X)
| IndicVal => (closing_ValuesUnTyped k i X)
end.
Definition closing_in_EqChannels (k : nat) (i : names_of_fvar) (E : EquationOnChannels) : EquationOnChannels :=
match E with 
| Val1 == Val2 => (closing_Channels k i Val1) == (closing_Channels k i Val2)
end.
Definition closing_in_EqValues (k : nat) (i : names_of_fvar) (E : EquationOnValues) : EquationOnValues :=
match E with 
| Val1 == Val2 => (closing_Values k i Val1) == (closing_Values k i Val2)
end.
Definition closing_in_EqForChannels (k : nat) (i : names_of_fvar) (E : EquationOnValueOrChannel) : EquationOnValueOrChannel :=
match E with
| EqChannel A => EqChannel (closing_in_EqChannels k i A)
| EqValue B => EqValue B
end.
Definition closing_in_EqForValues (k : nat) (i : names_of_fvar) (E : EquationOnValueOrChannel) : EquationOnValueOrChannel :=
match E with
| EqChannel A => EqChannel A
| EqValue B => EqValue (closing_in_EqValues k i B)
end.
Definition closing_in_Eq (Indic : ChanOrVal) (k : nat) (i : names_of_fvar) (E : EquationOnValueOrChannel) : EquationOnValueOrChannel :=
match Indic with 
| IndicChan => (closing_in_EqForChannels k i E)
| IndicVal => (closing_in_EqForValues k i E)
end.

Definition closing_ChannelsOrValues_on_Channels (I : ChanOrVal) (k : nat) (i : names_of_fvar) (c : Channels) : Channels :=
match I with
| IndicChan => closing_Channels k i c
| IndicVal => c
end.

Fixpoint closing_in_proc (I : ChanOrVal) (k : nat) (i : names_of_fvar) (p : proc') : proc' :=
match p with
| P ‖ Q => (closing_in_proc I k i P) ‖ (closing_in_proc I k i Q)
| pr_var' i => pr_var' i
| rec x • P =>  rec x • (closing_in_proc I k i P)
| If C Then P Else Q => If (closing_in_Eq I k i C) Then (closing_in_proc I k i P) Else (closing_in_proc I k i Q)
| g' M => closing_in_gproc I k i M
end

with closing_in_gproc I k i M {struct M} : gproc' :=
match M with 
| ① => ①
| ⓪ => ⓪
| c ? x • p' => (closing_ChannelsOrValues_on_Channels I k i c) ? x • (closing_in_proc I (S k) i p')
| c ! v • p' => (closing_ChannelsOrValues_on_Channels I k i c) ! (closing_ChannelsOrValues I k i v) • (closing_in_proc I k i p')
| t • p' => t • (closing_in_proc I k i p')
| p1 + p2 => (closing_in_gproc I k i p1) + (closing_in_gproc I k i p2)
end.

Definition Input_on_Channel c i p := c ? IndicChan • (closing_in_proc IndicChan 0 i p).
Definition Input_on_Value c i p := c ? IndicVal • (closing_in_proc IndicVal 0 i p).
Definition Input I c i p := 
match I with
|IndicChan => Input_on_Channel c i p
|IndicVal => Input_on_Value c i p
end.

Check ((bvarC 0) ! fvarV "y"  • ⓪).
Check (Input_on_Channel (fvarC "MyChannel") "y" ((bvarC 0) ! fvarV "y"  • ⓪)).
Compute (Input_on_Channel (fvarC "MyChannel") "y" ((fvarC "MyChannel") ! fvarV "y"  • ⓪)).
Check (Input_on_Value (fvarC "MyChannel") "y" ((bvarC 0) ! fvarC "y"  • ⓪)).
Compute (Input_on_Channel (fvarC "MyChannel") "y" ((fvarC "MyChannel") ! fvarC "y"  • ⓪)).


Definition subst_fvarC (old : names_of_fvar) (new : names_of_fvar) (C : Channels) : Channels :=
match C with
  | bvarC i    => C
  | fvarC i    => if decide(i = old) then (fvarC new) else (fvarC i)
  | channel c  => C
end.

Definition subst_EqChan (old : names_of_fvar) (new : names_of_fvar) (E : EquationOnChannels) : EquationOnChannels :=
match E with
| a == b => (subst_fvarC old new a) == (subst_fvarC old new b)
end.

Definition subst_EqChan_on_EqChanOrVal (old : names_of_fvar) (new : names_of_fvar) (E : EquationOnValueOrChannel) : EquationOnValueOrChannel :=
match E with
| EqChannel A => EqChannel (subst_EqChan old new A)
| EqValue B => EqValue B
end.

Definition subst_fvarV (old : names_of_fvar) (new : names_of_fvar) (V : Values) : Values :=
match V with
  | bvarV i    => V
  | fvarV i    => if decide(i = old) then (fvarV new) else (fvarV i)
  | value v  => V
end.

Definition subst_EqVal (old : names_of_fvar) (new : names_of_fvar) (E : EquationOnValues) : EquationOnValues :=
match E with
| a == b => (subst_fvarV old new a) == (subst_fvarV old new b)
end.

Definition subst_EqVal_on_EqChanOrVal (old : names_of_fvar) (new : names_of_fvar) (E : EquationOnValueOrChannel) : EquationOnValueOrChannel :=
match E with
| EqChannel A => EqChannel A
| EqValue B => EqValue (subst_EqVal old new B)
end.
(* IndicChan pour remplacer les fvarC, et IndicVal pour remplacer les fvarV*)
Definition subst_fvar_C_or_V_in_Eq (Indic : ChanOrVal) (old : names_of_fvar) (new : names_of_fvar) (E : EquationOnValueOrChannel) : EquationOnValueOrChannel :=
match Indic with 
| IndicChan => (subst_EqChan_on_EqChanOrVal old new E)
| IndicVal => (subst_EqVal_on_EqChanOrVal old new E)
end.

Definition subst_fvar_C_or_V_on_Channels (I : ChanOrVal) (old : names_of_fvar) (new : names_of_fvar) (c : Channels) : Channels :=
match I with
| IndicChan => subst_fvarC old new c
| IndicVal => c
end.


Definition subst_fvarC_UnTyped (old : names_of_fvar) (new : names_of_fvar) (X : ChannelsOrValues) : ChannelsOrValues :=
match X with
| chan c =>  chan (subst_fvarC old new c)
| val v => val v
end.
Definition subst_fvarV_UnTyped (old : names_of_fvar) (new : names_of_fvar) (X : ChannelsOrValues) : ChannelsOrValues :=
match X with
| chan c =>  chan c
| val v => val (subst_fvarV old new v)
end.
Definition subst_fvar_C_or_V_ChannelsOrValues (Indic : ChanOrVal) (old : names_of_fvar) (new : names_of_fvar) (X : ChannelsOrValues) : ChannelsOrValues :=
match Indic with
| IndicChan => (subst_fvarC_UnTyped old new X)
| IndicVal => (subst_fvarV_UnTyped old new X)
end.


Check (fvarV "y" == fvarV "z").
Compute (subst_fvar_C_or_V_in_Eq IndicChan "y" "z" (EqChannel ((fvarC "y") == fvarC "ChannelDeBob"))).

Fixpoint subst_fvar_C_or_V_in_proc (I : ChanOrVal) (old : names_of_fvar) (new : names_of_fvar) (p : proc') : proc' :=
match p with
| P ‖ Q => (subst_fvar_C_or_V_in_proc I old new P) ‖ (subst_fvar_C_or_V_in_proc I old new Q)
| pr_var' i => pr_var' i
| rec x • P =>  rec x • (subst_fvar_C_or_V_in_proc I old new P)
| If C Then P Else Q => If (subst_fvar_C_or_V_in_Eq I old new C) Then (subst_fvar_C_or_V_in_proc I old new P) Else (subst_fvar_C_or_V_in_proc I old new Q)
| g' M => subst_fvar_C_or_V_in_gproc I old new M
end

with subst_fvar_C_or_V_in_gproc I old new M {struct M} : gproc' :=
match M with 
| ① => ①
| ⓪ => ⓪
| c ? x • p' => (subst_fvar_C_or_V_on_Channels I old new c) ? x • (subst_fvar_C_or_V_in_proc I old new p')
| c ! v • p' => (subst_fvar_C_or_V_on_Channels I old new c) ! (subst_fvar_C_or_V_ChannelsOrValues I old new v) • (subst_fvar_C_or_V_in_proc I old new p')
| t • p' => t • (subst_fvar_C_or_V_in_proc I old new p')
| p1 + p2 => (subst_fvar_C_or_V_in_gproc I old new p1) + (subst_fvar_C_or_V_in_gproc I old new p2)
end.

Check (If (EqValue (fvarV "x" == fvarV "y")) Then ① Else ⓪).
Compute (subst_fvar_C_or_V_in_proc IndicVal "x" "z" (If (EqValue (fvarV "x" == fvarV "y")) 
Then ((fvarC "x") ! fvarV "x" •  ①)
Else ⓪)).


(* l'abstractraction correspond à l'abstraction *)


Lemma GoodAbstraction1 : forall i j c p p', 
                      c ? IndicChan • (closing_in_proc IndicChan 0 i p) = c ? IndicChan • (closing_in_proc IndicChan 0 j p')
                      -> p' = subst_fvar_C_or_V_in_proc IndicChan i j p.
Proof.
intros.
Admitted.
Lemma GoodAbstraction2 : forall i j c p p', Input_on_Channel c i p = Input_on_Channel c j p' 
                                            -> p' = subst_fvar_C_or_V_in_proc IndicChan i j p.
Proof.
apply GoodAbstraction1.
Qed.

Lemma ClosIsClos : forall i p, (closing_in_proc IndicChan 0 i p) 
                  = (closing_in_proc IndicChan 0 i (closing_in_proc IndicChan 0 i p)).
Proof.
intros. revert i. dependent induction p.
* intros. simpl. rewrite IHp1 at 1. rewrite IHp2 at 1. reflexivity.
* intros. simpl. reflexivity.
* intros. simpl. rewrite IHp at 1. reflexivity.
* intros. simpl. admit.
* dependent induction g.
  - intros. simpl. reflexivity.
  - intros. simpl. reflexivity.
  - admit.
  - admit.
  - admit.
  - intros. simpl. admit.
Admitted. 
(*There Is No More fvarC*)
Lemma TINMfC : forall i j k e,
      subst_EqChan i j (closing_in_EqChannels 0 i e) = subst_EqChan i k (closing_in_EqChannels 0 i e).
Proof.
Admitted.

Lemma There_Is_No_More_fvar_i_in_EqChan : forall i j k e, 
                        subst_EqChan_on_EqChanOrVal i j (closing_in_EqForChannels 0 i e)
                        = subst_EqChan_on_EqChanOrVal i k (closing_in_EqForChannels 0 i e).
Proof.
Admitted.
Lemma There_Is_No_More_fvar_i_in_proc : forall i j k p, 
                        subst_fvar_C_or_V_in_proc IndicChan i j ((closing_in_proc IndicChan 0 i p))
                        = subst_fvar_C_or_V_in_proc IndicChan i k ((closing_in_proc IndicChan 0 i p)).
Proof.
intros. dependent induction p.
* simpl. rewrite IHp1. rewrite IHp2. reflexivity.
* simpl. reflexivity.
* simpl. rewrite IHp. reflexivity.
* simpl. rewrite IHp1. rewrite IHp2. admit.
* admit.
Admitted.

Inductive GoodCondition : EquationOnValueOrChannel -> Prop :=
| equationOnChannelXX : forall x y, GoodCondition (EqChannel (fvarC x == fvarC y))
| equationOnChannelXC : forall x y, GoodCondition (EqChannel (fvarC x == channel y))
| equationOnChannelCX : forall x y, GoodCondition (EqChannel (channel x == fvarC y))
| equationOnChannelCC : forall x y, GoodCondition (EqChannel (channel x == channel y))
| equationOnValueXX : forall x y, GoodCondition (EqValue (fvarV x == fvarV y))
| equationOnValueXV : forall x y, GoodCondition (EqValue (fvarV x == value y))
| equationOnValueVX : forall x y, GoodCondition (EqValue (value x == fvarV y))
| equationOnValueVV : forall x y, GoodCondition (EqValue (value x == value y)).

Inductive Well_Defined_Channel : Channels -> Prop :=
| fvarC_is_defined : forall x, Well_Defined_Channel (fvarC x)
| channel_is_defined : forall x, Well_Defined_Channel (channel x).

Inductive Well_Defined_Value : Values -> Prop :=
| fvarV_is_defined : forall x, Well_Defined_Value (fvarV x)
| value_is_defined : forall x, Well_Defined_Value (value x).


Inductive Well_Defined_ChannelsOrValues : ChannelsOrValues -> Prop :=
| Well_Defined_for_Channel : forall c, Well_Defined_Channel c -> Well_Defined_ChannelsOrValues (chan c)
| Well_Defined_for_Value : forall v, Well_Defined_Value v -> Well_Defined_ChannelsOrValues (val v).

(*Inductive IsNotFree : Variables -> Prop :=
| bvar_is_not_free : forall i, IsNotFree (bvar i).

Lemma FirstProp : forall x, IsNotFree x <-> ~(IsFree x).
Proof. intros. split. intros. destruct H. intro. inversion H. 
admit.
Admitted.

Lemma SecondProp : forall x, IsFree x <-> ~(IsNotFree x).
Proof. intros. split. intros. intro. destruct x. inversion H0. inversion H.
intros. exfalso. apply H. destruct x. admit. apply bvar_is_not_free.
Admitted.

#[global] Instance names_and_multisetnames : ElemOf names (gmultiset names).
Proof. intro. intros. exact (H ∈ H0).
Qed.*)


Inductive process : proc' -> Prop :=
| process_par' : forall p1 p2, process p1 -> process p2 -> process (p1 ‖ p2)
| process_var' : forall i, process (pr_var' i)
| process_rec' : forall x p1, process p1 -> process (rec x • p1)
| process_if_then_else' : forall p1 p2 C, GoodCondition C -> process p1 -> process p2 
                        -> process (If C Then p1 Else p2)
| process_success' : process (①)
| process_nil' : process (⓪)
| process_input' : forall c I i p, (Well_Defined_Channel c) -> process p 
                  -> process (c ? I • (closing_in_proc I 0 i p))
| process_output' : forall c v p', Well_Defined_Channel c -> Well_Defined_ChannelsOrValues v 
                    -> process p' -> process (c ! v • p')
| process_tau' : forall p', process p' -> process (t • p')
| process_choice' : forall p1 p2 : gproc', process (g' p1) -> process (g' p2) -> process (p1 + p2).

#[global] Hint Constructors process:ccs.
Check ((fvarC "x") ! (fvarV "x") • ⓪).
Compute (Input IndicChan (fvarC "x") "x" (g' ((fvarC "x") ! (fvarV "x") • (fvarC "y" ? IndicChan • ((g' ((fvarC "x") ! (fvarV "x") • ⓪))))))).

Lemma ProcessPar : forall p q, process (p ‖ q) <-> process p /\ process q.
Proof.
intros. split. intros. dependent destruction H. split; auto. intros. destruct H. constructor; auto.
Qed.

Lemma ProcessChoice : forall p q, process (p + q) <-> process p /\ process q.
Proof.
intros. split. intros. dependent destruction H. split; auto. intros. destruct H. constructor; auto.
Qed.

Lemma ProcessRecursion : forall p x, process (rec x • p) <-> process p.
Proof.
intros. split.  intros. dependent destruction H. auto. intro. constructor. auto.
Qed.

Lemma ProcessTau : forall p, process (t • p) <-> process p.
Proof.
intros. split.  intros. dependent destruction H. auto. intro. constructor. auto.
Qed.

Lemma ProcessOutput : forall c v p, process (c ! v • p ) <-> 
process p /\ (Well_Defined_Channel c) /\ (Well_Defined_ChannelsOrValues v ).
Proof.
intros. split.
* intro. dependent destruction H; auto.
* intro. destruct H. destruct H0. constructor; auto.
Qed.



Lemma ProcessInputForChan : forall c p, process (g' (c ? IndicChan • p) ) <-> 
                  (Well_Defined_Channel c) /\ (exists (i : names_of_fvar) (p' : proc'), process(p') /\ p = (closing_in_proc IndicChan 0 i p')).
Proof.
intros. split.
* intro. dependent destruction H. split. auto. exists i. 
 exists p0. split. auto. reflexivity.
* intro. destruct H. destruct H0. destruct H0. destruct H0. rewrite H1. apply process_input'. auto. auto.
Qed.


Lemma ProcessInputForVal : forall c p, process (g' (c ? IndicVal • p) ) <-> 
                  (Well_Defined_Channel c) /\ (exists (i : names_of_fvar) (p' : proc'), process(p') /\ p = (closing_in_proc IndicVal 0 i p')).
Proof.
intros. split.
* intro. dependent destruction H. split. auto. exists i. 
 exists p0. split. auto. reflexivity.
* intro. destruct H. destruct H0. destruct H0. destruct H0. rewrite H1. apply process_input'. auto. auto.
Qed.

Lemma ProcessInput2 : forall c i p I, process (c ? I • closing_in_proc I 0 i p) -> (Well_Defined_Channel c) /\ process p.
Proof.
intros. dependent destruction H. split.
* auto.
* 
Admitted.
Lemma GoodProcess : forall p' i j p, p' = subst_fvar_C_or_V_in_proc IndicChan i j p -> process p -> process p'.
Proof.
intros. dependent induction p.
* simpl in *.
Admitted.


Lemma ProcessIf : forall C p q, process (If C Then p Else q) <-> GoodCondition C /\ process p /\ process q.
Proof.
intros. split.
* intro. dependent destruction H. split; auto.
* intro. decompose record H. constructor; auto.
Qed.


Lemma Exemple2 : ~process(bvarC 0 ! fvarC "x" • ⓪).
Proof.
intro. dependent destruction H. inversion H.
Qed.

(*
Fixpoint proc_to_proc' :=
.

Lemma AspectOf_proc : forall p : proc, process (proc_to_proc' p).

*)

(* Substitution for the Recursive Variable *)
Fixpoint pr_subst id p q :=
  match p with 
  | p1 ‖ p2 => (pr_subst id p1 q) ‖ (pr_subst id p2 q) 
  | pr_var' id' => if decide (id = id') then q else p 
  | rec id' • p' => if decide (id = id') then p else rec id' • (pr_subst id p' q)
  | If C Then p' Else q' => If C Then (pr_subst id p' q) Else (pr_subst id q' q)
  | g' gp => g' (gpr_subst id gp q)
end

with gpr_subst id p q {struct p} := match p with
| ① => ①
| ⓪ => ⓪
| c ? x • p => 
    c ? x • (pr_subst id p q)

| c ! v • p =>
    c ! v • (pr_subst id p q)

| t • p =>
    t • (pr_subst id p q)
| p1 + p2 =>
    (gpr_subst id p1 q) + (gpr_subst id p2 q)
end.

Lemma SubstAndClosing : forall n I i p q, pr_subst n (closing_in_proc I 0 i p) q = (closing_in_proc I 0 i (pr_subst n p q)).
Proof.
intros.
Admitted.
(*
Fixpoint ChannelName_for_Input_of_proc' (p : proc') : gmultiset names_of_fvar :=
match p with 
| P ‖ Q => (ChannelName_for_Input_of_proc' P) ⊎ (ChannelName_for_Input_of_proc' Q)
| pr_var' i => ∅
| rec x • P =>  ∅
| If C Then P Else Q => ∅
| g' x => ChannelName_for_Input_of_gproc' x
end

with ChannelName_for_Input_of_gproc' x :=
match x with 
| ① => ∅
| ⓪ => ∅
| c ? x • p' => match c with 
                | fvarC x => {[+ x +]}
                | bvarC i => ∅
               end
| c ! v • p' => ∅
| t • p' => ∅
| p1 + p2 => ∅
end.

Fixpoint ChannelName_for_Output_of_proc' (p : proc') : gmultiset names :=
match p with 
| P ‖ Q => (ChannelName_for_Output_of_proc' P) ⊎ (ChannelName_for_Output_of_proc' Q)
| pr_var' i => ∅
| rec x • P =>  ∅
| If C Then P Else Q => ∅
| g' x => ChannelName_for_Output_of_gproc' x
end

with ChannelName_for_Output_of_gproc' x :=
match x with 
| ① => ∅
| ⓪ => ∅
| c ? x • p' => ∅
| c ! v • p' => match c with 
                | fvar x => {[+ x +]}
                | bvar i => ∅
               end
| t • p' => ∅
| p1 + p2 => ∅
end.
*)


(* The Labelled Transition System (LTS-transition) *)
Inductive lts : proc'-> (Act Channels ChannelsOrValues) -> proc' -> Prop :=
(*The Input and the Output*)
| lts_input_channel : forall {c inputedChan P}, process (c ? IndicChan • P) -> (Well_Defined_Channel inputedChan) ->
    lts (c ? IndicChan • P) (ActIn c (chan inputedChan)) (subst_in_proc 0 inputedChan P)
| lts_input_value : forall {c inputedVal P}, process (c ? IndicVal • P) -> (Well_Defined_Value inputedVal) ->
    lts (c ? IndicVal • P) (ActIn c (val inputedVal)) (subst_in_proc 0 inputedVal P)
| lts_output : forall {c v P}, process (c ! v • P) -> (Well_Defined_ChannelsOrValues v) ->
    lts (c ! v • P) (ActOut c v) P

(*The actions Tau*)
| lts_tau : forall {P}, process (t • P) ->
    lts (t • P) τ P 
| lts_recursion : forall {x p}, process (rec x • p) ->
    lts (rec x • p) τ (pr_subst x p (rec x • p))
| lts_ifOneChan : forall p q (x : Channels) (y : Channels), x = y -> process (If (EqChannel(x == y)) Then p Else q) ->
    lts (If (EqChannel(x == y)) Then p Else q) τ p
| lts_ifOneVal : forall p q (x : Values) (y : Values), x = y -> process (If (EqValue(x == y)) Then p Else q) ->
    lts (If (EqValue(x == y)) Then p Else q) τ p
| lts_ifZeroChan : forall {p q x y}, ~(x = y) -> process (If (EqChannel(x == y)) Then p Else q) ->
    lts (If (EqChannel (x == y)) Then p Else q) τ q
| lts_ifZeroVal : forall {p q x y}, ~(x = y) -> process (If (EqValue(x == y)) Then p Else q) ->
    lts (If (EqValue(x == y)) Then p Else q) τ q

(* Communication of a channel output and input that have the same name*)
| lts_comL : forall {c v p1 p2 q1 q2},
    lts p1 (ActOut c v) p2 ->
    lts q1 (ActIn c v) q2 ->
    lts (p1 ‖ q1) τ (p2 ‖ q2) 
| lts_comR : forall {c v p1 p2 q1 q2},
    lts p1 (ActOut c v) p2 ->
    lts q1 (ActIn c v) q2 ->
    lts (q1 ‖ p1) τ (q2 ‖ p2)

(*The decoration for the transition system...*)
(*...for the parallele*)   
| lts_parL : forall {α p1 p2 q}, process q ->
    lts p1 α p2 ->
    lts (p1 ‖ q) α (p2 ‖ q)
| lts_parR : forall {α p q1 q2}, process p ->
    lts q1 α q2 ->
    lts (p ‖ q1) α (p ‖ q2)
(*...for the sum*)
| lts_choiceL : forall {p1 p2 q α},
    lts (g' p1) α q -> process (g' p2) ->
    lts (p1 + p2) α q
| lts_choiceR : forall {p1 p2 q α},
    lts (g' p2) α q -> process (g' p1) ->
    lts (p1 + p2) α q
.


#[global] Hint Constructors lts:ccs.

Lemma SanityCheck : forall p q α, lts p α q -> (process p /\ process q).
Proof.
intros. dependent induction H; split; auto.
* dependent destruction H0. simpl. dependent destruction H.
Admitted.



Fixpoint size (p : proc') := 
  match p with
  | p ‖ q  => S (size p + size q)
  | pr_var' _ => 1
  | If C Then p Else q => S (size p + size q)
  | rec x • p => S (size p)
  | g' p => gsize p
  end

with gsize p :=
  match p with
  | ① => 1
  | ⓪ => 0
  | c ? x • p => S (size p)
  | c ! v • p => S (size p)
  | t • p => S (size p)
  | p + q => S (gsize p + gsize q)
end.

Lemma SizeAndClosing : forall I i p, size (closing_in_proc I 0 i p) = size p.
Proof.
intros.
Admitted.


Reserved Notation "p ≡ q" (at level 70).

(*Naïve definition of a relation ≡ that will become a congruence ≡* by transitivity*)
Inductive cgr_step : proc' -> proc' -> Prop :=
(*  Reflexivity of the Relation ≡  *)
| cgr_refl_step : forall p, p ≡ p

(* Rules for the Parallèle *)
| cgr_par_nil_step : forall p, 
    p ‖ ⓪ ≡ p
| cgr_par_nil_rev_step : forall p,
    p ≡ p ‖ ⓪
| cgr_par_com_step : forall p q,
    p ‖ q ≡ q ‖ p
| cgr_par_assoc_step : forall p q r,
    (p ‖ q) ‖ r ≡ p ‖ (q ‖ r)
| cgr_par_assoc_rev_step : forall p q r,
    p ‖ (q  ‖ r) ≡ (p ‖ q) ‖ r

(* Rules for the Summation *)
| cgr_choice_nil_step : forall p,
    cgr_step (p + ⓪) p
| cgr_choice_nil_rev_step : forall p,
    cgr_step (g' p) (p + ⓪)
| cgr_choice_com_step : forall p q,
    cgr_step (p + q) (q + p)
| cgr_choice_assoc_step : forall p q r,
    cgr_step ((p + q) + r) (p + (q + r))
| cgr_choice_assoc_rev_step : forall p q r,
    cgr_step (p + (q + r)) ((p + q) + r)

(*The reduction is given to certain terms...*)
| cgr_recursion_step : forall x p q,
    cgr_step p q -> (rec x • p) ≡ (rec x • q)
| cgr_tau_step : forall p q,
    cgr_step p q ->
    cgr_step (t • p) (t • q)
| cgr_input_step : forall c I i p q,
    cgr_step p q ->
    cgr_step (c ? I • (closing_in_proc I 0 i p)) (c ? I • (closing_in_proc I 0 i q))
| cgr_output_step : forall c v p q,
    cgr_step p q ->
    cgr_step (c ! v • p) (c ! v • q)
| cgr_par_step : forall p q r,
    cgr_step p q ->
    p ‖ r ≡ q ‖ r
| cgr_if_left_step : forall C p q q',
    cgr_step q q' ->
    (If C Then p Else q) ≡ (If C Then p Else q')
| cgr_if_right_step : forall C p p' q,
    cgr_step p p' ->
    (If C Then p Else q) ≡ (If C Then p' Else q)

(*...and sums (only for guards (by sanity))*)
| cgr_choice_step : forall p1 q1 p2,
    cgr_step (g' p1) (g' q1) -> 
    cgr_step (p1 + p2) (q1 + p2)
.


#[global] Hint Constructors cgr_step:cgr_step_structure.

Infix "≡" := cgr_step (at level 70).



Lemma Obvious0 : forall p q, process p -> p ≡ q -> process q. 
Proof.
intros. dependent induction H0.
* auto.
* assert (process p /\ process ⓪). apply ProcessPar. auto. destruct H0. auto.
* apply ProcessPar. split; auto; try constructor.
* dependent destruction H;constructor; auto.
* dependent destruction H. dependent destruction H. constructor. auto. constructor. auto. auto.
* dependent destruction H. dependent destruction H0. constructor;auto. constructor; auto.
* dependent destruction H; auto.
* constructor; auto. constructor.
* dependent destruction H. constructor. auto. auto.
* dependent destruction H. dependent destruction H. constructor. auto. constructor; auto.
* dependent destruction H. dependent destruction H0. constructor. constructor; auto. auto.
* dependent destruction H. constructor. apply IHcgr_step. auto.
* dependent destruction H. constructor. apply IHcgr_step. auto.
* dependent destruction I. dependent destruction H. (*dzzdzdzdzdz eapply process_input'. auto. apply  IHcgr_step. auto.
* dependent destruction H. constructor; auto.
* dependent destruction H. constructor; auto.
* dependent destruction H. constructor; auto.
* dependent destruction H. constructor; auto.
* dependent destruction H. constructor; auto.*)
Admitted.



(* The relation ≡ is an reflexive*)
#[global] Instance cgr_refl_step_is_refl : Reflexive cgr_step.
Proof. intro. apply cgr_refl_step. Qed.
(* The relation ≡ is symmetric*)
#[global] Instance cgr_symm_step : Symmetric cgr_step.
Proof. intros p q hcgr. induction hcgr; econstructor ; eauto.
Qed.

(* Defining the transitive closure of ≡ *)
Infix "≡" := cgr_step (at level 70).
(* Defining the transitive closure of ≡ *)
Definition cgr := (clos_trans proc' cgr_step).

Infix "≡*" := cgr (at level 70).


(* The relation ≡* is reflexive*)
#[global] Instance cgr_refl : Reflexive cgr.
Proof. intros. constructor. apply cgr_refl_step. Qed.
(* The relation ≡* is symmetric*)
#[global] Instance cgr_symm : Symmetric cgr.
Proof. intros p q hcgr. induction hcgr. constructor. apply cgr_symm_step. exact H. eapply t_trans; eauto. Qed.
(* The relation ≡* is transitive*)
#[global] Instance cgr_trans : Transitive cgr.
Proof. intros p q r hcgr1 hcgr2. eapply t_trans; eauto. Qed.

#[global] Hint Resolve cgr_refl cgr_symm cgr_trans:cgr_eq.

(* The relation ≡* is an equivence relation*)
#[global] Instance cgr_is_eq_rel  : Equivalence cgr.
Proof. repeat split.
       + apply cgr_refl.
       + apply cgr_symm.
       + apply cgr_trans.
Qed.


(*the relation ≡* respects all the rules that ≡ respected*)
Lemma cgr_par_nil : forall p, p ‖ ⓪ ≡* p.
Proof.
constructor.
apply cgr_par_nil_step.
Qed.
Lemma cgr_par_nil_rev : forall p, p ≡* p ‖ ⓪.
Proof.
constructor.
apply cgr_par_nil_rev_step.
Qed.
Lemma cgr_par_com : forall p q, p ‖ q ≡* q ‖ p.
Proof.
constructor.
apply cgr_par_com_step.
Qed.
Lemma cgr_par_assoc : forall p q r, (p ‖ q) ‖ r ≡* p ‖ (q ‖r).
Proof.
constructor.
apply cgr_par_assoc_step.
Qed.
Lemma cgr_par_assoc_rev : forall p q r, p ‖(q ‖ r) ≡* (p ‖ q) ‖ r.
Proof.
constructor.
apply cgr_par_assoc_rev_step.
Qed.
Lemma cgr_choice_nil : forall p, p + ⓪ ≡* p.
Proof.
constructor.
apply cgr_choice_nil_step.
Qed.
Lemma cgr_choice_nil_rev : forall p, (g' p) ≡* p + ⓪.
Proof.
constructor.
apply cgr_choice_nil_rev_step.
Qed.
Lemma cgr_choice_com : forall p q, p + q ≡* q + p.
Proof.
constructor.
apply cgr_choice_com_step.
Qed.
Lemma cgr_choice_assoc : forall p q r, (p + q) + r ≡* p + (q + r).
Proof.
constructor.
apply cgr_choice_assoc_step.
Qed.
Lemma cgr_choice_assoc_rev : forall p q r, p + (q + r) ≡* (p + q) + r.
Proof.
constructor.
apply cgr_choice_assoc_rev_step.
Qed.
Lemma cgr_recursion : forall x p q, p ≡* q -> (rec x • p) ≡* (rec x • q).
Proof.
intros. dependent induction H. 
constructor. 
apply cgr_recursion_step. exact H. eauto with cgr_eq.
Qed.
Lemma cgr_tau : forall p q, p ≡* q -> (t • p) ≡* (t • q).
Proof.
intros. dependent induction H. 
constructor. 
apply cgr_tau_step. exact H. eauto with cgr_eq.
Qed. 
Lemma cgr_input : forall c I i p q, p ≡* q -> (c ? I • closing_in_proc I 0 i p) ≡* (c ? I • closing_in_proc I 0 i q).
Proof.
intros.
dependent induction H. 
* constructor. apply cgr_input_step. auto.
* eauto with cgr_eq.
Qed.
Lemma cgr_output : forall c v p q, p ≡* q -> (c ! v • p) ≡* (c ! v • q).
Proof.
intros. dependent induction H. 
constructor.
apply cgr_output_step. exact H. eauto with cgr_eq.
Qed.
Lemma cgr_par : forall p q r, p ≡* q-> p ‖ r ≡* q ‖ r.
Proof.
intros. dependent induction H. 
constructor.
apply cgr_par_step. exact H. eauto with cgr_eq.
Qed.
Lemma cgr_if_left : forall C p q q', q ≡* q' -> (If C Then p Else q) ≡* (If C Then p Else q').
Proof.
intros. dependent induction H. 
constructor.
apply cgr_if_left_step. exact H. eauto with cgr_eq.
Qed.
Lemma cgr_if_right : forall C p p' q, p ≡* p' -> (If C Then p Else q) ≡* (If C Then p' Else q).
Proof.
intros. dependent induction H. 
constructor.
apply cgr_if_right_step. exact H. eauto with cgr_eq.
Qed.
Lemma cgr_choice : forall p q r, g' p ≡* g' q -> p + r ≡* q + r.
Proof.
intros. dependent induction H. 
constructor.
apply cgr_choice_step. exact H. admit. (* again and again *)
Admitted.


Lemma cgr_full_if : forall C p p' q q', p ≡* p' -> q ≡* q' -> (If C Then p Else q) ≡* (If C Then p' Else q').
Proof.
intros.
apply transitivity with (If C Then p Else q'). apply cgr_if_left. exact H0. 
apply cgr_if_right. exact H. 
Qed.


(* The sum of guards respects ≡* *)
Lemma cgr_fullchoice : forall M1 M2 M3 M4, g' M1 ≡* g' M2 -> g' M3 ≡* g' M4 -> M1 + M3 ≡* M2 + M4.
Proof.
intros.
apply transitivity with (g' (M2 + M3)). apply cgr_choice. exact H. apply transitivity with (g' (M3 + M2)).
apply cgr_choice_com. apply transitivity with (g' (M4 + M2)). apply cgr_choice. exact H0. apply cgr_choice_com.
Qed.
(* The parallele of process respects ≡* *)
Lemma cgr_fullpar : forall M1 M2 M3 M4, M1 ≡* M2 -> M3 ≡* M4 -> M1 ‖ M3 ≡* M2 ‖ M4.
Proof.
intros.
apply transitivity with (M2 ‖ M3). apply cgr_par. exact H. apply transitivity with (M3 ‖ M2).
apply cgr_par_com. apply transitivity with (M4 ‖ M2). apply cgr_par. exact H0. apply cgr_par_com.
Qed.


#[global] Hint Resolve cgr_par_nil cgr_par_nil_rev cgr_par_nil_rev cgr_par_com cgr_par_assoc 
cgr_par_assoc_rev cgr_choice_nil cgr_choice_nil_rev cgr_choice_com cgr_choice_assoc 
cgr_choice_assoc_rev cgr_recursion cgr_tau cgr_input cgr_output cgr_par cgr_choice 
cgr_refl cgr_symm cgr_trans:cgr.


(* Substition lemma, needed to contextualise the equivalence *)
Lemma cgr_subst1 p q q' x : q ≡* q' → pr_subst x p q ≡* pr_subst x p q'.
Proof.
(* Induction on the size of p*)
induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct p.
  - simpl. intro. apply cgr_fullpar.
    apply Hp. simpl. rewrite <-Nat.add_succ_r. apply PeanoNat.Nat.lt_add_pos_r. apply Nat.lt_0_succ. exact H. 
    apply Hp. simpl. rewrite <-Nat.add_succ_l. apply PeanoNat.Nat.lt_add_pos_l. apply Nat.lt_0_succ. exact H.
  - simpl. intro. destruct (decide (x = n)). exact H. reflexivity.
  - simpl. intro. destruct (decide (x = n)). reflexivity. apply cgr_recursion. apply Hp. simpl. auto. exact H.
  - simpl. intro. apply cgr_full_if.
    apply Hp. simpl. rewrite <-Nat.add_succ_r. apply PeanoNat.Nat.lt_add_pos_r. apply Nat.lt_0_succ. exact H. 
    apply Hp. simpl. rewrite <-Nat.add_succ_l. apply PeanoNat.Nat.lt_add_pos_l. apply Nat.lt_0_succ. exact H.  
  - destruct g.
Admitted.
(* ≡ respects the substitution of his variable*)
Lemma cgr_step_subst2 : forall p p' q x, p ≡ p' → pr_subst x p q ≡ pr_subst x p' q.
Proof.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros p' q n hcgr ; inversion hcgr; try auto; try (exact H).
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - simpl. destruct (decide (n = x)). constructor. exact H. constructor. apply Hp. subst. simpl. auto.  exact H.
  - simpl. constructor. apply Hp. subst. simpl. auto. exact H.
  - simpl. assert (pr_subst n (closing_in_proc I 0 i p0) q = (closing_in_proc I 0 i (pr_subst n  p0 q))).
    apply SubstAndClosing. 
    assert (pr_subst n (closing_in_proc I 0 i q0) q = (closing_in_proc I 0 i (pr_subst n  q0 q))).
    apply SubstAndClosing. rewrite H2. rewrite H3. 
    eapply cgr_input_step. apply Hp. subst. simpl.
    assert(size (closing_in_proc I 0 i p0) = size p0). apply SizeAndClosing. rewrite H0. auto. exact H. 
  - simpl. constructor. apply Hp. subst. simpl. auto. exact H. 
  - simpl. constructor. apply Hp. subst. simpl. rewrite <-Nat.add_succ_r. apply PeanoNat.Nat.lt_add_pos_r. apply Nat.lt_0_succ.
    exact H.
  - simpl. constructor. apply Hp. subst. simpl. rewrite <-Nat.add_succ_l. apply PeanoNat.Nat.lt_add_pos_l. apply Nat.lt_0_succ.
    exact H.
  - simpl. constructor. apply Hp. subst. simpl. rewrite <-Nat.add_succ_r. apply PeanoNat.Nat.lt_add_pos_r. apply Nat.lt_0_succ.
    exact H.
  - simpl. apply cgr_choice_step. 
    assert (pr_subst n (g' p1) q ≡ pr_subst n (g' q1) q). apply Hp. subst. simpl. rewrite <-Nat.add_succ_r. apply PeanoNat.Nat.lt_add_pos_r. apply Nat.lt_0_succ.
    exact H. exact H2.
Qed.

(* ≡* respects the substitution of his variable *)
Lemma cgr_subst2 q p p' x : p ≡* p' → pr_subst x p q ≡* pr_subst x p' q.
Proof. 
intros hcgr. induction hcgr. constructor. now eapply cgr_step_subst2. apply transitivity with (pr_subst x y q).
exact IHhcgr1. exact IHhcgr2.
Qed.

(* ≡ respects the substitution / recursion *)
Lemma cgr_subst p q x : p ≡ q -> pr_subst x p (rec x • p) ≡* pr_subst x q (rec x • q).
Proof.
  intro heq.
  etrans.
  eapply cgr_subst2. constructor. eassumption.
  eapply cgr_subst1. constructor. apply cgr_recursion_step. exact heq.
Qed.

#[global] Hint Resolve cgr_is_eq_rel: ccs.
#[global] Hint Constructors clos_trans:ccs.
#[global] Hint Unfold cgr:ccs.


Definition Type_Of (C_Or_V : ChannelsOrValues) : ChanOrVal :=
match C_Or_V with
| chan c => IndicChan
| val v => IndicVal
end.

(* State Transition System (STS-reduction) *)
Inductive sts : proc' -> proc' -> Prop :=
(*The axiomes*)
(* Communication of channels output and input that have the same name *)
| sts_com : forall {c v p1 g1 p2 g2}, process(((c ! v • p1) + g1) ‖ ((c ? (Type_Of v) • p2) + g2))  ->
    sts (((c ! v • p1) + g1) ‖ ((c ? (Type_Of v) • p2) + g2)) (p1 ‖ (subst_in_proc 0 v p2))
(* Nothing more , something less *)
| sts_tau : forall {p g}, process (((t • p) + g)) ->
    sts ((t • p) + g) p
(* Resursion *)
| sts_recursion : forall {x p}, process (rec x • p) ->
    sts (rec x • p) (pr_subst x p (rec x • p))
(*If Yes*)
| sts_ifOneChan : forall {p q v v'}, v = v' -> process (If (EqChannel(v == v')) Then p Else q) ->
    sts (If (EqChannel(v == v')) Then p Else q) p
| sts_ifOneVal : forall {p q v v'}, v = v' -> process (If (EqValue(v == v')) Then p Else q) ->
    sts (If (EqValue(v == v')) Then p Else q) p
(*If No*)
| sts_ifZeroChan : forall {p q v v'}, ~(v = v') -> process (If (EqChannel(v == v')) Then p Else q) ->
    sts (If (EqChannel(v == v')) Then p Else q) q
| sts_ifZeroVal : forall {p q v v'}, ~(v = v') -> process (If (EqValue(v == v')) Then p Else q) ->
    sts (If (EqValue(v == v')) Then p Else q) q

(* The left parallele respect the Reduction *)
| sts_par : forall {p1 p2 q},  process q ->
    sts p1 p2 ->
    sts (p1 ‖ q) (p2 ‖ q)

(*The Congruence respects the Reduction *)
| sts_cong : forall {p1 p2 q2 q1},
    p1 ≡* p2 -> sts p2 q2 -> q2 ≡* q1 -> sts p1 q1
.

#[global] Hint Constructors sts:ccs.

Lemma SanityCheckForSTS : forall p q, sts p q -> process p /\ process q.
Proof.
intros. dependent induction H; split; auto.
* simpl.
Admitted.

(* For the (STS-reduction), the reductible terms and reducted terms are pretty all the same, up to ≡* *)
Lemma ReductionShape : forall P Q, sts P Q ->
((exists c v I P1 P2 G1 G2 S, ((P ≡* (((c ! v • P1) + G1) ‖ ((c ? I • P2) + G2)) ‖ S)) /\ (Q ≡*((P1 ‖ (P2^v)) ‖ S)))
\/ (exists P1 G1 S, (P ≡* (((t • P1) + G1) ‖ S)) /\ (Q ≡* (P1 ‖ S)))
\/ (exists n P1 S, (P ≡* ((rec n • P1) ‖ S)) /\ (Q ≡* (pr_subst n P1 (rec n • P1) ‖ S)))
\/ (exists P1 P0 S v, (P ≡* ((If (EqChannel (v == v)) Then P1 Else P0) ‖ S)) /\ (Q ≡* P1 ‖ S))
\/ (exists P1 P0 S v, (P ≡* ((If (EqValue(v == v)) Then P1 Else P0) ‖ S)) /\ (Q ≡* P1 ‖ S))
\/ (exists P1 P0 S v v', (P ≡* ((If (EqChannel(v == v')) Then P1 Else P0) ‖ S)) /\ (Q ≡* P0 ‖ S) /\ ~(v = v'))
\/ (exists P1 P0 S v v', (P ≡* ((If (EqValue(v == v')) Then P1 Else P0) ‖ S)) /\ (Q ≡* P0 ‖ S) /\ ~(v = v'))
).
Proof.
(*
intros P Q Transition.
induction Transition.
  - left. exists c. exists v. exists p1. exists p2. exists m1. exists m2. exists (⓪). split; apply cgr_par_nil_rev.
  - right. left. exists p. exists m. exists ⓪. split; apply cgr_par_nil_rev.
  - right. right. left. exists x. exists p. exists ⓪. split; apply cgr_par_nil_rev.
  - right. right. right. left. exists p. exists q. exists ⓪. exists v. rewrite H.  split;apply cgr_par_nil_rev.
  - right. right. right. right. exists p. exists q. exists ⓪. exists v. exists v'. split. apply cgr_par_nil_rev.
    split. apply cgr_par_nil_rev. auto.
  - destruct IHTransition as [IH|[IH|[IH|[IH |IH]]]];  decompose record IH. 
    * left. exists x. exists x0. exists x1. exists x2. exists x3. exists x4. exists (x5 ‖ q). split.
        ** apply transitivity with (((((x ! x0 • x1) + x3) ‖ ((x ? l • x2) + x4)) ‖ x5) ‖ q). apply cgr_par. exact H0. apply cgr_par_assoc.
        ** apply transitivity with (((x1 ‖ x2^x0) ‖ x5) ‖ q). apply cgr_par. exact H1.  apply cgr_par_assoc. 
    * right. left. exists x. exists x0. exists (x1 ‖ q). split.
        ** apply transitivity with (((t • x + x0) ‖ x1) ‖ q). apply cgr_par. exact H0. apply cgr_par_assoc.
        ** apply transitivity with (x ‖ (x1) ‖ q). apply cgr_par. exact H1. apply cgr_par_assoc.
    * right. right. left. exists x. exists x0. exists (x1 ‖ q). split. 
        ** apply transitivity with ((rec x • x0 ‖ x1) ‖ q). apply cgr_par. exact H0. apply cgr_par_assoc.
        ** apply transitivity with ((pr_subst x x0 (rec x • x0) ‖ x1) ‖ q). apply cgr_par. exact H1. apply cgr_par_assoc.
    * right. right. right. left. exists x. exists x0. exists (x1 ‖ q). exists x2. split.
        ** apply transitivity with (((If (x2 == x2) Then x Else x0) ‖ x1) ‖ q). apply cgr_par. exact H. apply cgr_par_assoc.
        ** apply transitivity with ((x ‖ x1) ‖ q). apply cgr_par. exact H1. apply cgr_par_assoc.
    * right. right. right. right. exists x. exists x0. exists (x1 ‖ q). exists x2. exists x3. split.
        ** apply transitivity with (((If (x2 == x3) Then x Else x0) ‖ x1) ‖ q). apply cgr_par. exact H0. apply cgr_par_assoc.
        ** split. apply transitivity with ((x0 ‖ x1) ‖ q). apply cgr_par. exact H. apply cgr_par_assoc. auto.
  - destruct IHTransition as [IH|[IH|[IH|[IH |IH]]]]; decompose record IH. 
    * left. exists x. exists x0. exists x1. exists x2. exists x3. exists x4. exists x5 (* ?? *). split. apply cgr_trans with p2. exact H. exact H2.
      apply cgr_trans with q2. apply cgr_symm. exact H0. exact H3.
    * right. left. exists x. exists x0. exists x1. split. apply cgr_trans with p2. exact H. exact H2. apply cgr_trans with q2.
      apply cgr_symm. apply H0. apply H3.
    * right. right. left. exists x. exists x0. exists x1. split. apply cgr_trans with p2. exact H. exact H2. apply cgr_trans with q2.
      apply cgr_symm. apply H0. apply H3.
    * right. right. right. left. exists x. exists x0. exists x1. exists x2. split. apply cgr_trans with p2. exact H. exact H1. apply cgr_trans with q2.
      apply cgr_symm. apply H0. apply H3.
    * right. right. right. right. exists x. exists x0. exists x1. exists x2. exists x3. split. apply cgr_trans with p2. exact H. exact H2. split. apply cgr_trans with q2.
      apply cgr_symm. apply H0. apply H1. auto. *)
Admitted.

(* For the (LTS-transition), the transitable terms and transitted terms, that performs a INPUT,
are pretty all the same, up to ≡* *)
Lemma TransitionShapeForInput : forall P Q c v, (lts P (ActIn c v)) Q -> 
(exists P1 G R I, ((P ≡* ((c ? I • P1 + G) ‖ R)) /\ (Q ≡* (P1^v ‖ R)) /\ ((exists L,P = (g' L)) -> R = ⓪))).
Proof. (*
intros P Q c v Transition.
 dependent induction Transition.
- exists P. exists ⓪. exists ⓪. split ; try split.
  * apply cgr_trans with ((c ? x • P) + ⓪). apply cgr_trans with (c ? x • P). apply cgr_refl. apply cgr_choice_nil_rev. apply cgr_par_nil_rev.
  * apply cgr_par_nil_rev.
  * reflexivity.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists x0. exists (x1 ‖ q). split; try split.
  * apply cgr_trans with ((((c ? l • x) + x0) ‖ x1) ‖ q). apply cgr_par. exact H0. apply cgr_par_assoc.
  * apply cgr_trans with ((x^v ‖ x1) ‖ q). apply cgr_par. exact H1. apply cgr_par_assoc.
  * intros. inversion H2. inversion H4.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists x0. exists (x1 ‖ p). split; try split.
  * apply cgr_trans with ((((c ? l • x) + x0) ‖ x1) ‖ p). apply cgr_trans with (q1 ‖ p). apply cgr_par_com. apply cgr_par. exact H0. apply cgr_par_assoc.
  * apply cgr_trans with ((x^v ‖ x1) ‖ p). apply cgr_trans with (q2 ‖ p). apply cgr_par_com. apply cgr_par. exact H1. apply cgr_par_assoc.
  * intros. inversion H2. inversion H4.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists (x0 + p2). exists ⓪. split ; try split.
  * apply cgr_trans with ((c ? l • x) + (x0 + p2)). apply cgr_trans with (((c ? l • x) + x0) + p2).
    apply cgr_choice. assert (x1 = ⓪). apply H3. exists p1. reflexivity. rewrite H2 in H0. apply transitivity with (((c ? l • x) + x0) ‖ ⓪).
    exact H0. apply cgr_par_nil. apply cgr_choice_assoc. apply cgr_par_nil_rev.
  * assert (x1 = ⓪). apply H3. exists p1. reflexivity. rewrite H2 in H1. exact H1.
  * reflexivity.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists (x0 + p1). exists ⓪. split; try split.
  * apply cgr_trans with ((c ? l • x) + (x0 + p1)). apply cgr_trans with (((c ? l • x) + x0) + p1).
    apply cgr_trans with (p2 + p1). apply cgr_choice_com. apply cgr_choice. assert (x1 = ⓪). apply H3. exists p2. reflexivity.
    apply cgr_trans with (((c ? l • x) + x0) ‖ x1). exact H0. rewrite H2. apply cgr_par_nil. apply cgr_choice_assoc. apply cgr_par_nil_rev.
  * assert (x1 = ⓪). apply H3. exists p2. reflexivity. rewrite <-H2. exact H1.
  * reflexivity. *)
Admitted.

(* For the (LTS-transition), the transitable terms and transitted terms, that performs a OUPUT,
are pretty all the same, up to ≡* *)
Lemma TransitionShapeForOutput : forall P Q c v, (lts P (ActOut c v)) Q -> 
(exists P1 G R, ((P ≡* ((c ! v • P1 + G) ‖ R)) /\ (Q ≡* (P1 ‖ R)) /\ ((exists L,P = (g' L)) -> R = ⓪))).
Proof. (*
intros P Q c v Transition.
 dependent induction Transition.
- exists P. exists ⓪. exists ⓪. split ; try split.
  * apply cgr_trans with ((c ! v • P) + ⓪). apply cgr_trans with (c ! v • P). apply cgr_refl. apply cgr_choice_nil_rev. apply cgr_par_nil_rev.
  * apply cgr_par_nil_rev.
  * reflexivity.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists x0. exists (x1 ‖ q). split; try split.
  * apply cgr_trans with ((((c ! v • x) + x0) ‖ x1) ‖ q). apply cgr_par. exact H0. apply cgr_par_assoc.
  * apply cgr_trans with ((x ‖ x1) ‖ q). apply cgr_par. exact H1. apply cgr_par_assoc.
  * intros. inversion H2. inversion H4.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists x0. exists (x1 ‖ p). split; try split.
  * apply cgr_trans with ((((c ! v • x) + x0) ‖ x1) ‖ p). apply cgr_trans with (q1 ‖ p). apply cgr_par_com. apply cgr_par. exact H0. apply cgr_par_assoc.
  * apply cgr_trans with ((x ‖ x1) ‖ p). apply cgr_trans with (q2 ‖ p). apply cgr_par_com. apply cgr_par. exact H1. apply cgr_par_assoc.
  * intros. inversion H2. inversion H4.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists (x0 + p2). exists ⓪. split ; try split.
  * apply cgr_trans with ((c ! v • x) + (x0 + p2)). apply cgr_trans with (((c ! v • x) + x0) + p2).
    apply cgr_choice. assert (x1 = ⓪). apply H3. exists p1. reflexivity. rewrite H2 in H0. apply transitivity with (((c ! v • x) + x0) ‖ ⓪).
    exact H0. apply cgr_par_nil. apply cgr_choice_assoc. apply cgr_par_nil_rev.
  * assert (x1 = ⓪). apply H3. exists p1. reflexivity. rewrite H2 in H1. exact H1.
  * reflexivity.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists (x0 + p1). exists ⓪. split; try split.
  * apply cgr_trans with ((c ! v • x) + (x0 + p1)). apply cgr_trans with (((c ! v • x) + x0) + p1).
    apply cgr_trans with (p2 + p1). apply cgr_choice_com. apply cgr_choice. assert (x1 = ⓪). apply H3. exists p2. reflexivity.
    apply cgr_trans with (((c ! v • x) + x0) ‖ x1). exact H0. rewrite H2. apply cgr_par_nil. apply cgr_choice_assoc. apply cgr_par_nil_rev.
  * assert (x1 = ⓪). apply H3. exists p2. reflexivity. rewrite <-H2. exact H1.
  * reflexivity. *)
Admitted.



(* For the (LTS-transition), the transitable Guards and transitted terms, that performs a Tau ,
are pretty all the same, up to ≡* *)
Lemma TransitionShapeForTauAndGuard : forall P V, ((lts P τ V) /\ (exists L, P = (g' L))) -> 
(exists Q M, ((P ≡* ((t • Q) + M))) /\ (V ≡* (Q))).
Proof. (*
intros P V Hyp. 
destruct Hyp. rename H into Transition. dependent induction Transition.
- exists P. exists ⓪. split. 
  * apply cgr_choice_nil_rev.
  * apply cgr_refl.
- inversion H0. inversion H.
- inversion H0. inversion H1.
- inversion H0. inversion H1.
- inversion H0. inversion H.
- inversion H0. inversion H.
- inversion H0. inversion H.
- inversion H0. inversion H.
- destruct (IHTransition (reflexivity τ)). exists p1. reflexivity. destruct H. destruct H.  exists x. 
  exists (x0 + p2). split. apply cgr_trans with (((t • x) + x0) + p2).
  apply cgr_choice. exact H.
  apply cgr_choice_assoc. exact H1.
- destruct (IHTransition (reflexivity τ)). exists p2. reflexivity. destruct H. destruct H.  exists x. 
  exists (x0 + p1). split. apply cgr_trans with (((t • x) + x0) + p1). apply cgr_trans with (p2 + p1). 
  apply cgr_choice_com. apply cgr_choice. exact H. apply cgr_choice_assoc. exact H1. *)
Admitted.

(* p 'is equivalent some r 'and r performs α to q *)
Definition sc_then_lts p α q := exists r, p ≡* r /\ (lts r α q).

(* p performs α to some r and this is equivalent to q*)
Definition lts_then_sc p α q := exists r, ((lts p α r) /\ r ≡* q).


(* p 'is equivalent some r 'and r performs α to q , the congruence and the Transition can be reversed : *)
Lemma Congruence_Respects_Transition  : forall p q α, sc_then_lts p α q -> lts_then_sc p α q.
Proof. (*
(* by induction on the congruence and the step then...*)
  intros p q α (p' & hcgr & l).
  revert q α l.
  dependent induction hcgr.
  - dependent induction H. 
(* reasonning about all possible cases due to the structure of terms *)
    + intros. exists q.  split.  exact l. reflexivity. 
    + intros. exists (q ‖ ⓪). split. apply lts_parL. exact l. auto with cgr (*par contexte parallele*). 
    + intros. dependent destruction l. inversion l2. inversion l1. exists p2. split. exact l. auto with cgr. 
      inversion l.
    + intros. dependent destruction l.
      -- exists (q2 ‖ p2). split. eapply lts_comR. instantiate (1:= v). instantiate (1:= c). exact l1. exact l2. auto with cgr.
      -- exists (p2 ‖ q2). split. eapply lts_comL. instantiate (1:= v). instantiate (1:= c). exact l1. exact l2. auto with cgr.
      -- exists (p ‖ p2). split. apply lts_parR. exact l. auto with cgr.
      -- exists (q2 ‖ q). split. apply lts_parL. exact l. auto with cgr.
    + intros. dependent destruction l.
      -- dependent destruction l2. 
         * exists ((p2 ‖ p0) ‖ r). split.
           apply lts_parL. eapply lts_comL. instantiate (1:= v). instantiate (1:= c). exact l1. exact l2. auto with cgr.
         * exists ((p2 ‖ q) ‖ q2). split. eapply lts_comL. instantiate (1:= v). instantiate (1:= c). apply lts_parL. exact l1.
           exact l2. apply cgr_par_assoc.
      -- dependent destruction l1. 
         * exists ((q2 ‖ p2) ‖ r). split. apply lts_parL. eapply lts_comR. instantiate (1:= v). instantiate (1:= c). exact l1.
           exact l2. auto with cgr.
         * exists ((q2 ‖ q) ‖ q0). split. eapply lts_comR. instantiate (1:= v). instantiate (1:= c). exact l1. apply lts_parL.
           exact l2. auto with cgr.
      -- exists ((p2 ‖ q) ‖ r). split. apply lts_parL. apply lts_parL. exact l. auto with cgr.
      -- dependent destruction l.
         * exists ((p ‖ p2) ‖ q2). split. eapply lts_comL. instantiate (1:= v). instantiate (1:= c). apply lts_parR. exact l1.
           exact l2. auto with cgr.
         * exists ((p ‖ q2) ‖ p2). split. eapply lts_comR. instantiate (1:= v). instantiate (1:= c). exact l1. apply lts_parR.
           exact l2. auto with cgr.
         * exists ((p ‖ p2) ‖ r). split. apply lts_parL. apply lts_parR. exact l. auto with cgr.
         * exists ((p ‖ q) ‖ q2). split. apply lts_parR. exact l. auto with cgr.
    + intros. dependent destruction l.
      -- dependent destruction l1. 
         * exists (p2 ‖ (q ‖ q2)). split.
           eapply lts_comL. instantiate (1:= v). instantiate (1:= c). exact l1. apply lts_parR. exact l2. auto with cgr.
         * exists (p ‖ (q0 ‖ q2)). split. apply lts_parR. eapply lts_comL. instantiate (1:= v). instantiate (1:= c). exact l1.
           exact l2. auto with cgr.
      -- dependent destruction l2. 
         * exists (p0 ‖ (q ‖ p2)). split. eapply lts_comR. instantiate (1:= v). instantiate (1:= c). apply lts_parR.  exact l1.
           exact l2. auto with cgr.
         * exists (p ‖ (q2 ‖ p2)). split. apply lts_parR. eapply lts_comR. instantiate (1:= v). instantiate (1:= c). exact l1. 
           exact l2. auto with cgr.
      -- dependent destruction l.
         * exists (p2 ‖ (q2 ‖ r)). split. eapply lts_comL. instantiate (1:= v). instantiate (1:= c).  exact l1. apply lts_parL.
           exact l2. auto with cgr.
         * exists (q2 ‖ (p2 ‖ r)). split. eapply lts_comR. instantiate (1:= v). instantiate (1:= c). apply lts_parL. exact l1. 
           exact l2. auto with cgr.
         * exists (p2 ‖ ( q ‖ r)). split. apply lts_parL. exact l. auto with cgr.
         * exists (p ‖ (q2 ‖ r)). split. apply lts_parR. apply lts_parL. exact l. auto with cgr.
      -- exists (p ‖ (q ‖ q2)). split. apply lts_parR. apply lts_parR. exact l. auto with cgr.
    + intros. exists q.  split. apply lts_choiceL.  exact l. auto with cgr.
    + intros. dependent destruction l.
      -- exists q. split. exact l. auto with cgr.
      -- inversion l.
    + intros. dependent destruction l.
      -- exists q0. split. apply lts_choiceR. exact l. auto with cgr.
      -- exists q0. split. apply lts_choiceL. exact l. auto with cgr.
    + intros. dependent destruction l.
      -- exists q0. split. apply lts_choiceL. apply lts_choiceL. exact l. auto with cgr.
      -- dependent destruction l.
         * exists q0. split. apply lts_choiceL. apply lts_choiceR. exact l. auto with cgr.
         * exists q0. split. apply lts_choiceR. exact l. auto with cgr.
    + intros. dependent destruction l.
      -- dependent destruction l.
         * exists q0. split. apply lts_choiceL. exact l. auto with cgr.
         * exists q0. split. apply lts_choiceR. apply lts_choiceL. exact l. auto with cgr.
      -- exists q0. split. apply lts_choiceR. apply lts_choiceR. exact l. auto with cgr.
    + intros. dependent destruction l. exists (pr_subst x p (rec x • p)). split. apply lts_recursion.
      apply cgr_subst. exact H.
    + intros. dependent destruction l. exists p.  split. apply lts_tau. constructor. exact H.
    + intros. dependent destruction l. exists (p^v). split. apply lts_input. constructor. apply H.
    + intros. dependent destruction l. exists p. split. apply lts_output. constructor. apply H.
    + intros. dependent destruction l.
      -- destruct (IHcgr_step p2 (ActOut c v)). exact l1.
          eexists. split. eapply lts_comL. destruct H0. exact l. destruct H0. exact l2. 
          apply cgr_fullpar. destruct H0. exact H1. reflexivity.
      -- destruct (IHcgr_step q2 (ActIn c v)). exact l2. destruct H0.
          eexists. split.  eapply lts_comR. exact l1. exact H0.
          apply cgr_fullpar. exact H1. reflexivity.
      -- destruct (IHcgr_step p2 α). exact l. destruct H0.
          eexists. split. instantiate (1:= (x ‖ r)). apply lts_parL.  exact H0. apply cgr_fullpar.
          exact H1. reflexivity.
      -- eexists. split. instantiate (1:= (p ‖ q2)). apply lts_parR. exact l. apply cgr_par.
          constructor. exact H.
    + intros. dependent destruction l.
      -- eexists. split. instantiate (1:= p). apply lts_ifOne. reflexivity.
      -- eexists. split. instantiate (1:= q). apply lts_ifZero. constructor. exact H.
    + intros. dependent destruction l.
      -- eexists. split. instantiate (1:= p). apply lts_ifOne. constructor. exact H.
      -- eexists. split. instantiate (1:= q). apply lts_ifZero. reflexivity.
    + intros. dependent destruction l. 
      -- destruct (IHcgr_step q α). exact l. destruct H0. exists x. split. apply lts_choiceL. exact H0. exact H1.
      -- eexists. instantiate (1:= q). split. apply lts_choiceR. exact l. reflexivity.
  - intros. destruct (IHhcgr2 q α). exact l. destruct (IHhcgr1 x0 α). destruct H. exact H. exists x1. split. destruct H0. exact H0.
    destruct H. destruct H0. eauto with cgr. *)
Admitted.



(* One side of the Harmony Lemma *)
Lemma Reduction_Implies_TausAndCong : forall P Q, (sts P Q) -> (lts_then_sc P τ Q).
Proof. (*
intros P Q Reduction. 
assert ((exists c v P1 P2 M1 M2 S, ((P ≡* (((c ! v • P1) + M1) ‖ ((c ? x • P2) + M2)) ‖ S)) /\ (Q ≡*((P1 ‖ (P2 v)) ‖ S)))
\/ (exists P1 M1 S, (P ≡* (((t • P1) + M1) ‖ S)) /\ (Q ≡* (P1 ‖ S)))
\/ (exists n P1 S, (P ≡* ((rec n • P1) ‖ S)) /\ (Q ≡* (pr_subst n P1 (rec n • P1) ‖ S)))
\/ (exists P1 P0 S, (P ≡* ((If one Then P1 Else P0) ‖ S)) /\ (Q ≡* P1 ‖ S))
\/ (exists P1 P0 S, (P ≡* ((If zero Then P1 Else P0) ‖ S)) /\ (Q ≡* P0 ‖ S))
). 
apply ReductionShape. exact Reduction.
destruct H as [IH|[IH|[IH|[IH |IH]]]];  decompose record IH. 

(*First case τ by communication *)

- assert (lts (((x ! x0 • x1) + x3) ‖ ((x ? l • x2) + x4) ‖ x5) τ (x1 ‖ (x2 x0) ‖ x5)).
  * apply lts_parL. eapply lts_comL. apply lts_choiceL. instantiate (2:= x). instantiate (1:= x0). apply lts_output. apply lts_choiceL. apply lts_input.
  * assert (sc_then_lts P τ ((x1 ‖ x2 x0) ‖ x5)). exists ((((x ! x0 • x1) + x3) ‖ ((x ? l • x2) + x4)) ‖ x5). split. exact H0. exact H.
    assert (lts_then_sc P τ ((x1 ‖ x2 x0) ‖ x5)). apply Congruence_Respects_Transition. exact H2. destruct H3. destruct H3.
    exists x6. split. exact H3. apply transitivity with ((x1 ‖ x2 x0) ‖ x5). exact H4. symmetry. exact H1.

(*Second case τ by Tau Action *)

- assert (lts ((t • x + x0) ‖ x1) τ (x ‖ x1)). constructor. apply lts_choiceL. apply lts_tau.  
  assert (sc_then_lts P τ (x ‖ x1)). exists ((t • x + x0) ‖ x1). split. exact H0. exact H.
  assert (lts_then_sc P τ (x ‖ x1)). apply Congruence_Respects_Transition. exact H2. destruct H3. destruct H3. 
  exists x2. split. exact H3. apply transitivity with (x ‖ x1). exact H4. symmetry. exact H1.

(*Third case τ by recursion *)

- assert (lts (rec x • x0 ‖ x1) τ (pr_subst x x0 (rec x • x0) ‖ x1)). 
  constructor. apply lts_recursion. assert (sc_then_lts P τ ((pr_subst x x0 (rec x • x0) ‖ x1))). 
  exists (rec x • x0 ‖ x1). split. exact H0. exact H. assert (lts_then_sc P τ (pr_subst x x0 (rec x • x0) ‖ x1)). 
  apply Congruence_Respects_Transition. exact H2. destruct H3. destruct H3. 
  exists x2. split. exact H3. apply transitivity with (pr_subst x x0 (rec x • x0) ‖ x1). exact H4. 
  symmetry. exact H1.

(*Fourth case τ by If ONE*)

- assert (lts ((If one Then x Else x0) ‖ x1) τ (x ‖ x1)). constructor. apply lts_ifOne.
  assert (sc_then_lts P τ (x ‖ x1)). exists ((If one Then x Else x0) ‖ x1). split. exact H0. exact H.
  assert (lts_then_sc P τ (x ‖ x1)). apply Congruence_Respects_Transition. exact H2. destruct H3. destruct H3.
  exists x2. split. exact H3. apply transitivity with (x ‖ x1). exact H4. 
  symmetry. exact H1. 

(*Fifth case τ by If ZERO*)

- assert (lts ((If zero Then x Else x0) ‖ x1) τ (x0 ‖ x1)). constructor. apply lts_ifZero.
  assert (sc_then_lts P τ (x0 ‖ x1)). exists ((If zero Then x Else x0) ‖ x1). split. exact H0. exact H.
  assert (lts_then_sc P τ (x0 ‖ x1)). apply Congruence_Respects_Transition. exact H2. destruct H3. destruct H3.
  exists x2. split. exact H3. apply transitivity with (x0 ‖ x1). exact H4. 
  symmetry. exact H1.  *)
Admitted.


(* Some lemmas for multiple parallele processes to simplify the statements of proof*)
Lemma InversionParallele : forall P Q R S, (P ‖ Q) ‖ (R ‖ S) ≡* (P ‖ R) ‖ (Q ‖ S) . 
Proof. 
intros.
apply transitivity with (((P ‖ Q) ‖ R) ‖ S). apply cgr_par_assoc_rev.
apply transitivity with ((P ‖ (Q ‖ R)) ‖ S). apply cgr_par. apply cgr_par_assoc.
apply transitivity with (((Q ‖ R) ‖ P) ‖ S). apply cgr_par. apply cgr_par_com.
apply transitivity with ((Q ‖ R) ‖ (P ‖ S)). apply cgr_par_assoc.
apply transitivity with ((R ‖ Q) ‖ (P ‖ S)). apply cgr_par. apply cgr_par_com.
apply transitivity with (((R ‖ Q) ‖ P) ‖ S). apply cgr_par_assoc_rev.
apply transitivity with ((P ‖ (R ‖ Q)) ‖ S). apply cgr_par. apply cgr_par_com.
apply transitivity with (((P ‖ R) ‖ Q) ‖ S). apply cgr_par. apply cgr_par_assoc_rev.
apply transitivity with ((P ‖ R) ‖ (Q ‖ S)). apply cgr_par_assoc.
reflexivity. 
Qed.
Lemma InversionParallele2 : forall P Q R S, (P ‖ Q) ‖ (R ‖ S) ≡* (R ‖ P) ‖ (S ‖ Q).
Proof.
intros. 
apply transitivity with ((P ‖ R) ‖ (Q ‖ S)). apply InversionParallele.
apply transitivity with ((R ‖ P) ‖ (Q ‖ S)). apply cgr_par. apply cgr_par_com.
apply transitivity with ((Q ‖ S) ‖ (R ‖ P)). apply cgr_par_com.
apply transitivity with ((S ‖ Q) ‖ (R ‖ P)). apply cgr_par. apply cgr_par_com.
apply cgr_par_com.
Qed.
Lemma InversionParallele3 : forall P Q R S, (P ‖ Q) ‖ (R ‖ S) ≡* (R ‖ Q) ‖ (P ‖ S).
Proof.
intros.
apply transitivity with ((Q ‖ P) ‖ (R ‖ S)). apply cgr_par. apply cgr_par_com.
apply transitivity with ((Q ‖ R) ‖ (P ‖ S)). apply InversionParallele. apply cgr_par. apply cgr_par_com.
Qed.

(* The More Stronger Harmony Lemma (in one side) is more stronger *)
Lemma Congruence_Simplicity : (forall α , ((forall P Q, (((lts P α Q) -> (sts P Q)))) 
-> (forall P Q, ((lts_then_sc P α Q) -> (sts P Q))))).
Proof.
intros. destruct H0. destruct H0. eapply sts_cong. instantiate (1:=P). apply cgr_refl. instantiate (1:=x). apply H. exact H0. 
exact H1.
Qed.

Lemma Taus_Implies_Reduction : forall P Q, (lts P τ Q) -> (sts P Q).
Proof. (*
intros.
dependent induction H.
  - eapply sts_cong.  instantiate (1:=  ((t • P) + ⓪)). apply cgr_choice_nil_rev. instantiate (1:=P).
    apply sts_tau. apply cgr_refl.
  - apply sts_recursion.
  - apply sts_ifOne.
  - apply sts_ifZero.
  - destruct (TransitionShapeForOutput p1 p2 c v). exact H.  decompose record H1.
    destruct (TransitionShapeForInput q1 q2 c v). exact H0. decompose record H4.
    eapply sts_cong. instantiate (1:=(((c ! v • x) + x0) ‖ ((c ? l • x2) + x3)) ‖ (x1 ‖ x4)).
    apply cgr_trans with ((((c ! v • x) + x0) ‖ x1) ‖ (((c ? l • x2) + x3) ‖ x4)). apply cgr_fullpar. exact H2. exact H6.
    apply InversionParallele. 
    instantiate (1 := (x ‖ (x2 v)) ‖ (x1 ‖ x4)). apply sts_par. apply sts_com.
    apply transitivity with ((x ‖ x1) ‖ ((x2 v) ‖ x4)). apply InversionParallele. apply cgr_fullpar. 
    symmetry. exact H3. symmetry. exact H7.
  - destruct (TransitionShapeForOutput p1 p2 c v). exact H. decompose record H1.
    destruct (TransitionShapeForInput q1 q2 c v). exact H0. decompose record H4.
    eapply sts_cong. instantiate (1:=(((c ! v • x) + x0) ‖ ((c ? l • x2) + x3)) ‖ (x1 ‖ x4)).
    apply transitivity with (p1 ‖ q1). apply cgr_par_com.
    apply transitivity with ((((c ! v • x) + x0) ‖ x1) ‖ (((c ? l • x2) + x3) ‖ x4)).
    apply cgr_fullpar. exact H2. exact H6. apply InversionParallele. 
    instantiate (1 := (x ‖ (x2 v)) ‖ (x1 ‖ x4)). apply sts_par. apply sts_com.
    apply transitivity with ((x ‖ x1) ‖ ((x2 v) ‖ x4)). apply InversionParallele. apply transitivity with (p2 ‖ q2). apply cgr_fullpar. 
    symmetry. exact H3. symmetry. exact H7. apply cgr_par_com.
- apply sts_par. apply IHlts. reflexivity.
- eapply sts_cong. instantiate (1:= q1 ‖ p). apply cgr_par_com. instantiate (1:= q2 ‖ p).
  apply sts_par. apply IHlts. reflexivity. apply cgr_par_com.
- destruct (TransitionShapeForTauAndGuard (g p1) q). split. exact H. exists p1. reflexivity.
  destruct H0. destruct H0. eapply sts_cong. instantiate (1:= ((t • x) + (x0 + p2))).
  apply transitivity with (g (((t • x) + x0) + p2)). apply cgr_choice. exact H0. apply cgr_choice_assoc.
  instantiate (1:= x). apply sts_tau. symmetry. exact H1.
- destruct (TransitionShapeForTauAndGuard (g p2) q). split. exact H. exists p2. reflexivity.
  destruct H0. destruct H0. eapply sts_cong. instantiate (1:= ((t • x) + (x0 + p1))).
  apply transitivity with (g (((t • x) + x0 ) + p1)). apply transitivity with (g (p2 + p1)). apply cgr_choice_com.
  apply cgr_choice. exact H0. apply cgr_choice_assoc. instantiate (1:= x). apply sts_tau. symmetry. exact H1. *)
Admitted.

(* One side of the Harmony Lemma*)
Lemma TausAndCong_Implies_Reduction: forall P Q, (lts_then_sc P τ Q) -> (sts P Q).
Proof.
intros P Q H.
apply Congruence_Simplicity with τ. exact Taus_Implies_Reduction. exact H.
Qed.

Theorem HarmonyLemmaForCCS : forall P Q, (lts_then_sc P τ Q) <-> (sts P Q).
Proof.
intros. split.
* apply TausAndCong_Implies_Reduction.
* apply Reduction_Implies_TausAndCong.
Qed.