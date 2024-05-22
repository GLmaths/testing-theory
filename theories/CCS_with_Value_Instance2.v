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
Inductive ExtAct (ChannelType ValueType : Type) :=
| ActIn : ChannelType -> ValueType -> ExtAct ChannelType ValueType
| ActOut : ChannelType -> ValueType -> ExtAct ChannelType ValueType
.


Arguments ActIn {_} {_} _ _.
Arguments ActOut {_} {_} _ _.

Inductive Act (ChannelType ValueType : Type) :=
| ActExt (μ: ExtAct ChannelType ValueType )
| τ
.
Arguments ActExt {_} {_} _.
Arguments τ {_} {_}.


Coercion ActExt : ExtAct >-> Act.


(* Table des vérités *) 
Inductive Qbit :=
| one
| zero
| one_OR_zero
.




Definition names := string.

Inductive Variables :=
| fvar : names -> Variables
| bvar : nat -> Variables.

Coercion fvar : names >-> Variables.
Coercion bvar : nat >-> Variables.

Inductive Equation (A : Type) : Type :=
| Equality : A -> A -> Equation A.

Arguments  Equality {_} _ _.


Notation "x = y" := (Equality x y).



(*
Parameter ChannelType : Type.
(*(* Decision procedure for the name of channel *)
Hypothesis channel_eq_dec : EqDecision ChannelType. 

#[global] Instance channel_eqdecision : EqDecision ChannelType. by exact channel_eq_dec. Defined.*)

Parameter ValueType : Type.*)

(*
(* Definition of processes*)
Inductive proc : Type :=
(* To parallele two processes*)
| pr_par : proc -> proc -> proc
(* Variable in a process, for recursion and substitution*)
| pr_var : nat-> proc
(* recursion for process*)
| pr_rec : nat -> proc -> proc 
(* If test *NEW term in comparison of CCS* *)
| pr_if_then_else: Equation names -> proc -> proc -> proc 
(*The Guards*)
| g : gproc -> proc

with gproc : Type :=
(* The Success operation*)
| gpr_success : gproc
(* The Process that does nothing*)
| gpr_nil : gproc
(*An input is a name of a channel, an input variable, followed by a process*)
| gpr_input : names -> names -> proc -> gproc
(*An output is a name of a channel, an ouput value, followed by a process*)
| gpr_output : names -> names -> proc -> gproc
(*A tau action : does nothing *)
| gpr_tau : proc -> gproc
(* To choose between two processes*)
| gpr_choice : gproc -> gproc -> gproc
.

Coercion pr_var : nat >-> proc.
Coercion g : gproc >-> proc.

(*Some notation to simplify the view of the code*)

Notation "①" := (gpr_success).
Notation "⓪" := (gpr_nil).
Notation "'rec' x '•' p" := (pr_rec x p) (at level 50).
Notation "P + Q" := (gpr_choice P Q).
Notation "P ‖ Q" := (pr_par P Q) (at level 50).
Notation "c ! v • p" := (gpr_output c v p) (at level 50).
Notation "c ? x • P" := (gpr_input c x P) (at level 50).
Notation "'t' • P" := (gpr_tau P) (at level 50).
Notation "'If' C 'Then' P 'Else' Q" := (pr_if_then_else C P Q)
(at level 200, right associativity, format
"'[v   ' 'If'  C '/' '[' 'Then'  P  ']' '/' '[' 'Else'  Q ']' ']'"). 

Definition All_Names_of_Eq (E : Equation names) : gmultiset names :=
match E with 
| a = b => {[+ a +]} ⊎ {[+ b +]}
end.


Fixpoint All_Names_of_proc (p : proc) : gmultiset names :=
match p with 
| P ‖ Q => (All_Names_of_proc P) ⊎ (All_Names_of_proc Q)
| pr_var i => ∅
| rec x • P =>  (All_Names_of_proc P)
| If C Then P Else Q => (All_Names_of_Eq C) ⊎ (All_Names_of_proc P) ⊎ (All_Names_of_proc Q)
| g x => All_Names_of_gproc x
end

with All_Names_of_gproc x :=
match x with 
| ① => ∅
| ⓪ => ∅
| c ? x • p' => {[+ c +]} ⊎ All_Names_of_proc p'
| c ! v • p' => {[+ c +]} ⊎ {[+ v +]} ⊎ All_Names_of_proc p'
| t • p' => All_Names_of_proc p'
| p1 + p2 => (All_Names_of_gproc p1) ⊎ (All_Names_of_gproc p2)
end.




*)


(* Definition of processes*)
Inductive proc' : Type :=
(* To parallele two processes*)
| pr_par' : proc' -> proc' -> proc'
(* Variable in a process, for recursion and substitution*)
| pr_var' : nat -> proc'
(* recursion for process*)
| pr_rec' : nat -> proc' -> proc'
(* If test *NEW term in comparison of CCS* *)
| pr_if_then_else' : Equation (Variables) -> proc' -> proc' -> proc' 
(*The Guards*)
| g' : gproc' -> proc'

with gproc' : Type :=
(* The Success operation*)
| gpr_success' : gproc'
(* The Process that does nothing*)
| gpr_nil' : gproc'
(*An input is a name of a channel, an input variable, followed by a process*)
| gpr_input' : Variables -> proc' -> gproc'
(*An output is a name of a channel, an ouput value, followed by a process*)
| gpr_output' : Variables -> Variables -> proc' -> gproc'
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
Notation "c ? x • P" := (gpr_input' c P) (at level 50).
Notation "'t' • P" := (gpr_tau' P) (at level 50).
Notation "'If' C 'Then' P 'Else' Q" := (pr_if_then_else' C P Q)
(at level 200, right associativity, format
"'[v   ' 'If'  C '/' '[' 'Then'  P  ']' '/' '[' 'Else'  Q ']' ']'"). 


Definition All_Names_of_Eq (E : Equation names) : gmultiset names :=
match E with 
| a = b => {[+ a +]} ⊎ {[+ b +]}
end.

Definition RealNames (X : Variables) : gmultiset names := 
match X with
| fvar x => {[+ x +]} 
| bvar i => ∅
end.

#[global] Instance RealNames_are_singletons : SingletonMS (gmultiset names) (gmultiset names).
Proof. intro. exact H.
Qed.

Definition All_Names_of_Eq' (E : Equation (Variables)) : gmultiset names :=
match E with 
| a = b => (RealNames a) ⊎ (RealNames b)
end.

Fixpoint All_Names_of_proc' (p : proc') : gmultiset names :=
match p with 
| pr_par' P Q => (All_Names_of_proc' P) ⊎ (All_Names_of_proc' Q)
| pr_var' i => ∅
| pr_rec' x P =>  (All_Names_of_proc' P)
| pr_if_then_else' C P Q => (All_Names_of_Eq' C) ⊎ (All_Names_of_proc' P) ⊎ (All_Names_of_proc' Q)
| g' x => All_Names_of_gproc' x
end

with All_Names_of_gproc' x :=
match x with 
| gpr_success' => ∅
| gpr_nil' => ∅
| gpr_input' c p' => {[+ (RealNames c) +]} ⊎ (All_Names_of_proc' p')
| gpr_output' c v p' => {[+ (RealNames c) +]} ⊎ {[+ (RealNames v) +]} ⊎ All_Names_of_proc' p'
| gpr_tau' p' => All_Names_of_proc' p'
| gpr_choice' p1 p2 => (All_Names_of_gproc' p1) ⊎ (All_Names_of_gproc' p2)
end.

Definition open_rec_Variables (k : nat) (fresh : names) (X : Variables) : Variables := 
match X with
| fvar x => fvar x
| bvar i => if (decide(i = k)) then fvar fresh else bvar i
end.

Definition open_rec_Eq' (k : nat) (fresh : names) (E : Equation (Variables)) : (Equation (Variables)) :=
match E with 
| a = b => (open_rec_Variables k fresh a) = (open_rec_Variables k fresh b)
end.

Fixpoint open_rec_proc' (k : nat) (fresh : names) (p : proc') {struct p} : proc' :=
match p with
| pr_par' P Q => pr_par' (open_rec_proc' k fresh P) (open_rec_proc' k fresh Q)
| pr_var' i => pr_var' i
| pr_rec' x P =>  pr_rec' x (open_rec_proc' k fresh P)
| pr_if_then_else' C P Q => pr_if_then_else' (open_rec_Eq' k fresh C) (open_rec_proc' k fresh P) (open_rec_proc' k fresh Q)
| g' x => open_rec_gproc' k fresh x
end

with open_rec_gproc' k fresh x {struct x} : gproc' :=
match x with 
| gpr_success' => gpr_success'
| gpr_nil' => gpr_nil'
| gpr_input' c p' => gpr_input' (open_rec_Variables k fresh c) (open_rec_proc' (S k) fresh p')
| gpr_output' c v p' => gpr_output' (open_rec_Variables k fresh c) (open_rec_Variables k fresh v) (open_rec_proc' k fresh p')
| gpr_tau' p' => gpr_tau' (open_rec_proc' k fresh p')
| gpr_choice' p1 p2 => gpr_choice' (open_rec_gproc' k fresh p1) (open_rec_gproc' k fresh p2)
end.

Notation "t1 ^ x1" := (open_rec_proc' 0 x1 t1).


Inductive GoodCondition : Equation (Variables) -> Prop :=
| equation : forall x y, GoodCondition (fvar x = fvar y).

Inductive IsFree : Variables -> Prop :=
| fvar_is_free : forall x, IsFree (fvar x).

Inductive IsNotFree : Variables -> Prop :=
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
Qed.


Inductive process : proc' -> Prop :=
| process_par' : forall p1 p2, process p1 -> process p2 -> process (pr_par' p1 p2)
| process_var' : forall i, process (pr_var' i)
| process_rec' : forall x p1, process p1 -> process (pr_rec' x p1)
| process_if_then_else' : forall p1 p2 C, GoodCondition C -> process p1 -> process p2 
                        -> process (pr_if_then_else' C p1 p2)
| process_success' : process (gpr_success')
| process_nil' : process (gpr_nil')
| process_input' : forall (L : gmultiset names) c t1, 
                  (forall x, (x ∉ L) -> process (open_rec_proc' 0 x t1)) 
                  -> process (gpr_input' c t1)
| process_output' : forall c v p', IsFree c -> IsFree v -> process p' -> process (gpr_output' c v p')
| process_tau' : forall p', process p' -> process (gpr_tau' p')
| process_choice' : forall p1 p2 : gproc', process (g' p1) -> process (g' p2) -> process (g' (gpr_choice' p1 p2))
.

#[global] Hint Constructors process:ccs.

Definition body t1 := exists L : gmultiset names, forall x, x ∉ L -> process (open_rec_proc' 0 x t1).

Definition bodyOnCondition C := exists L : gmultiset names, forall x, x ∉ L -> GoodCondition (open_rec_Eq' 0 x C).

Check ((bvar 0) ! (fvar "v") • ⓪).
Check (fvar "c" ? x • ((bvar 0) ! (fvar "v") • ⓪)).
Lemma Exemple : (g' (((fvar "v") ! (fvar "v") • ⓪))) = open_rec_proc' 0 ("v") (((bvar 0) ! (fvar "v") • ⓪)) .
Proof.
simpl. reflexivity.
Qed.

Lemma Exemple2 : process ((fvar "c" ? x • ((bvar 0) ! (fvar "v") • ⓪))) .
Proof.
simpl. apply process_input' with ∅. intros. simpl. apply process_output'. apply fvar_is_free. apply fvar_is_free.
  apply process_nil'.
Qed.

Lemma Exemple3 : (g' ((fvar "l") ! (fvar "v") • ⓪) = (((bvar 0) ! (fvar "v") • ⓪))^("l")).
Proof. simpl. reflexivity.
Qed.


Check (fvar "c" ? x • (((bvar 0) ! (fvar "v") • ⓪) + ((fvar "v") ! (bvar 0) • ⓪))).

Lemma Exemple4 : g' (fvar "e" ! fvar "v" • ⓪ + (fvar "v" ! fvar "e" • ⓪)) = (((0 ! fvar "v" • ⓪) + (fvar "v" ! 0 • ⓪)) ^ "e").
Proof.
simpl. reflexivity.
Qed. 



Lemma Exemple5 : g' (fvar "e" ! fvar "v" • ⓪ + (fvar "v" ! fvar "e" • ⓪)) = (((0 ! fvar "v" • ⓪) + (fvar "v" ! 0 • ⓪)) ^ "e").
Proof.
simpl. reflexivity. 
Qed. 

Check (((0 ! fvar "v" • ⓪) + ((fvar "c") ? y • (fvar "v" ! 0 • ⓪))) ^ "e").

Compute (((0 ! fvar "v" • ⓪) + ((bvar 0) ? y • (fvar "v" ! 0 • ⓪))) ^ "e").

Check (process(fvar "c" ? x • (If ((bvar 1) = (fvar "a")) Then ① Else ⓪))).
Lemma Exemple6 : process(fvar "c" ? x • (If ((bvar 0) = (fvar "a")) Then ① Else ⓪)).
Proof.
eapply process_input' with ∅. intros. simpl. apply process_if_then_else'. apply equation. apply process_success'.
apply process_nil'.
Qed.

Lemma Exemple7 : process(fvar "c" ? x • (fvar "c" ? x • (If ((bvar 1) = (bvar 0)) Then ① Else ⓪))).
Proof.
econstructor. instantiate (1:=∅). intros. econstructor. instantiate (1:=∅). intros. simpl. constructor.
 apply equation. apply process_success'. apply process_nil'.
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

Lemma Bodies : forall p q, body (p ‖ q) <-> body p /\ body q.
Proof.
intros. split.
- intro. split.
  * destruct H. exists x. intros. assert (process (open_rec_proc' 0 x0 (p ‖ q))).
    apply H. exact H0. dependent destruction H1. exact H1_.
  * destruct H. exists x. intros. assert (process (open_rec_proc' 0 x0 (p ‖ q))).
    apply H. exact H0. dependent destruction H1. exact H1_0. 
- intros. destruct H. destruct H. destruct H0. exists (x ⊎ x0). intros. simpl. apply process_par'. apply H.
  admit. apply H0. admit.
Admitted.

Lemma Bodies2 : forall p n, body (rec n • p) <-> body p.
Proof.
intros. split.
* intros. inversion H. exists x. simpl in H0. intros. 
  assert (process (rec n • open_rec_proc' 0 x0 p)). apply H0. auto. inversion H2. auto.
* intros. destruct H. exists x. intros. simpl. apply process_rec'. apply H. auto.
Qed.

Lemma Bodies3 : forall C P Q, body (If C Then P Else Q) <-> (bodyOnCondition C) /\ body P /\ body Q.
Proof.
intros. split.
* intros. inversion H. split.
  ** exists x. intros. assert (process ((If C Then P Else Q) ^ x0)).
     apply H0. auto. inversion H2. auto. ** split.
  - exists x. simpl in H0. intros. 
  assert (process(If (open_rec_Eq' 0 x0 C) Then (open_rec_proc' 0 x0 P) Else (open_rec_proc' 0 x0 Q))).
  apply H0. auto. inversion H2. auto.
  - exists x. simpl in H0. intros. 
  assert (process(If (open_rec_Eq' 0 x0 C) Then (open_rec_proc' 0 x0 P) Else (open_rec_proc' 0 x0 Q))).
  apply H0. auto. inversion H2. auto.
* intros. destruct H. destruct H0. destruct H. destruct H0. destruct H1.
  exists (x ⊎ x0 ⊎ x1). intros. simpl. apply process_if_then_else'.
  ** apply H. admit.
  ** apply H0. admit.
  ** apply H1. admit.
Admitted.

Lemma Subst_with_Body : forall p q n, body p -> body q -> body (pr_subst n p q).
Proof.
intros. dependent induction p.
* simpl. assert (body p1 /\ body p2). apply Bodies. auto. destruct H1. apply Bodies. split. apply IHp1.  auto. auto.
  apply IHp2. auto. auto.
* simpl. destruct (decide(n0 = n)). auto. auto.
* simpl. destruct(decide (n0 = n)). auto. apply Bodies2. apply IHp. assert (body (rec n • p) <-> body p). apply Bodies2.
  destruct H1. apply H1. auto. auto.
* destruct H. destruct H0. simpl. apply Bodies3.
  split. exists (x ⊎ x0). intros. 
  ** assert (process ((If e Then p1 Else p2) ^ x1)). apply H. admit. inversion H2. auto. 
  ** split.
     *** apply IHp1. exists (x ⊎ x0). intros.
      assert (process ((If e Then p1 Else p2) ^ x1)). apply H. admit. inversion H2. auto.
      exists (x ⊎ x0). intros. apply H0. admit.
     *** apply IHp2. exists (x ⊎ x0). intros.
      assert (process ((If e Then p1 Else p2) ^ x1)). apply H. admit. inversion H2. auto.
      exists (x ⊎ x0). intros. apply H0. admit.
*
Admitted.

Fixpoint ChannelName_for_Input_of_proc' (p : proc') : gmultiset names :=
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
                | fvar x => {[+ x +]}
                | bvar i => ∅
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


(* The Labelled Transition System (LTS-transition) *)
Inductive lts : proc' -> Act names names -> proc' -> Prop :=
(*The Input and the Output*)
| lts_input : forall {c v P}, body P ->
    lts ((fvar c) ? x • P) (ActIn c v) (P ^ v)
| lts_output : forall {c v P},
    lts ((fvar c) ! (fvar v) • P) (ActOut c v) P

(*The actions Tau*)
| lts_tau : forall {P},
    lts (t • P) τ P 
| lts_recursion : forall {x p},
    lts (rec x • p) τ (pr_subst x p (rec x • p))
(*| lts_ifOne : forall {p q x y}, x = y ->
    lts (If (x = y) Then p Else q) τ p
| lts_ifZero : forall {p q}, 
    lts (If zero Then p Else q) τ q*)

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
| lts_parL : forall {α p1 p2 q},
    lts p1 α p2 ->
    lts (p1 ‖ q) α (p2 ‖ q)
| lts_parR : forall {α p q1 q2},
    lts q1 α q2 ->
    lts (p ‖ q1) α (p ‖ q2)
(*...for the sum*)
| lts_choiceL : forall {p1 p2 q α},
    lts (g' p1) α q ->
    lts (p1 + p2) α q
| lts_choiceR : forall {p1 p2 q α},
    lts (g' p2) α q ->
    lts (p1 + p2) α q
.

#[global] Hint Constructors lts:ccs.



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
| cgr_input_step : forall c p q x, body p -> body q ->
    cgr_step  (p^x) (q^x) ->
    cgr_step (c ? x • p) (c ? x • q)
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

(*Lemma Obvious :forall p q x, body p ->  p^x ≡ q^x -> body q.
Proof.
intros.
dependent induction H0.
*eauto.
Admitted.*)


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
Lemma cgr_input : forall c p q x, body p -> body q -> p^x ≡* q^x -> (c ? x • p ≡* c ? x • q).
Proof.
intros.
dependent induction H1. 
constructor. 
apply cgr_input_step with x. exact H. exact H0. auto.
Admitted.
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
  - simpl. eapply cgr_input_step. apply Hp. subst. simpl. auto. exact H. 
  - simpl. constructor. apply Hp. subst. simpl. auto. exact H. 
  - simpl. constructor. apply Hp. subst. simpl. rewrite <-Nat.add_succ_r. apply PeanoNat.Nat.lt_add_pos_r. apply Nat.lt_0_succ.
    exact H.
  - simpl. constructor. apply Hp. subst. simpl. rewrite <-Nat.add_succ_l. apply PeanoNat.Nat.lt_add_pos_l. apply Nat.lt_0_succ.
    exact H.
  - simpl. constructor. apply Hp. subst. simpl. rewrite <-Nat.add_succ_r. apply PeanoNat.Nat.lt_add_pos_r. apply Nat.lt_0_succ.
    exact H.
  - simpl. apply cgr_choice_step. 
    assert (pr_subst n (g p1) q ≡ pr_subst n (g q1) q). apply Hp. subst. simpl. rewrite <-Nat.add_succ_r. apply PeanoNat.Nat.lt_add_pos_r. apply Nat.lt_0_succ.
    exact H. exact H2.
Qed.

(* ≡* respects the substitution of his variable *)
Lemma cgr_subst2 q p p' x : p ≡* p' → pr_subst x p q ≡* pr_subst x p' q.
Proof. 
intros hcgr. induction hcgr. constructor. now eapply cgr_step_subst2. apply transitivity with (pr_subst x y q).
exact IHhcgr1. exact IHhcgr2.
Qed.

(* ≡ respects the substitution / recursion *)
Lemma cgr_subst p q x : p ≡ q -> pr_subst x p (pr_rec x p) ≡* pr_subst x q (pr_rec x q).
Proof.
  intro heq.
  etrans.
  eapply cgr_subst2. constructor. eassumption.
  eapply cgr_subst1. constructor. apply cgr_recursion_step. exact heq.
Qed.

#[global] Hint Resolve cgr_is_eq_rel: ccs.
#[global] Hint Constructors clos_trans:ccs.
#[global] Hint Unfold cgr:ccs.




(* State Transition System (STS-reduction) *)
Inductive sts : proc -> proc -> Prop :=
(*The axiomes*)
(* Communication of channels output and input that have the same name *)
| sts_com : forall {c v p1 m1 p2 m2},
    sts (((c ! v • p1) + (m1)) ‖ ((c ? x • p2) + m2)) (p1 ‖ (p2 v))
(* Nothing more , something less *)
| sts_tau : forall {p m},
    sts ((t • p) + m) p
(* Resursion *)
| sts_recursion : forall {x p},
    sts (rec x • p) (pr_subst x p (rec x • p))
(*If Yes*)
| sts_ifOne : forall {p q},
    sts (If one Then p Else q) p
(*If No*)
| sts_ifZero : forall {p q},
    sts (If zero Then p Else q) q

(* The left parallele respect the Reduction *)
| sts_par : forall {p1 p2 q},
    sts p1 p2 ->
    sts (p1 ‖ q) (p2 ‖ q)

(*The Congruence respects the Reduction *)
| sts_cong : forall {p1 p2 q2 q1},
    p1 ≡* p2 -> sts p2 q2 -> q2 ≡* q1 -> sts p1 q1
.

#[global] Hint Constructors sts:ccs.


(* For the (STS-reduction), the reductible terms and reducted terms are pretty all the same, up to ≡* *)
Lemma ReductionShape : forall P Q, sts P Q ->
((exists c v P1 P2 M1 M2 S, ((P ≡* (((c ! v • P1) + M1) ‖ ((c ? x • P2) + M2)) ‖ S)) /\ (Q ≡*((P1 ‖ (P2 v)) ‖ S)))
\/ (exists P1 M1 S, (P ≡* (((t • P1) + M1) ‖ S)) /\ (Q ≡* (P1 ‖ S)))
\/ (exists n P1 S, (P ≡* ((rec n • P1) ‖ S)) /\ (Q ≡* (pr_subst n P1 (rec n • P1) ‖ S)))
\/ (exists P1 P0 S, (P ≡* ((If one Then P1 Else P0) ‖ S)) /\ (Q ≡* P1 ‖ S))
\/ (exists P1 P0 S, (P ≡* ((If zero Then P1 Else P0) ‖ S)) /\ (Q ≡* P0 ‖ S))
).
Proof.
intros P Q Transition.
induction Transition.
  - left. exists c. exists v. exists p1. exists p2. exists m1. exists m2. exists (g gpr_nil). split; apply cgr_par_nil_rev.
  - right. left. exists p. exists m. exists ⓪. split; apply cgr_par_nil_rev.
  - right. right. left. exists x. exists p. exists ⓪. split; apply cgr_par_nil_rev.
  - right. right. right. left. exists p. exists q. exists ⓪. split; apply cgr_par_nil_rev.
  - right. right. right. right. exists p. exists q. exists ⓪. split; apply cgr_par_nil_rev.
  - destruct IHTransition as [IH|[IH|[IH|[IH |IH]]]];  decompose record IH. 
    * left. exists x. exists x0. exists x1. exists x2. exists x3. exists x4. exists (x5 ‖ q). split.
        ** apply transitivity with (((((x ! x0 • x1) + x3) ‖ ((x ? l • x2) + x4)) ‖ x5) ‖ q). apply cgr_par. exact H0. apply cgr_par_assoc.
        ** apply transitivity with (((x1 ‖ x2 x0) ‖ x5) ‖ q). apply cgr_par. exact H1.  apply cgr_par_assoc. 
    * right. left. exists x. exists x0. exists (x1 ‖ q). split.
        ** apply transitivity with (((t • x + x0) ‖ x1) ‖ q). apply cgr_par. exact H0. apply cgr_par_assoc.
        ** apply transitivity with (x ‖ (x1) ‖ q). apply cgr_par. exact H1. apply cgr_par_assoc.
    * right. right. left. exists x. exists x0. exists (x1 ‖ q). split. 
        ** apply transitivity with ((pr_rec x x0 ‖ x1) ‖ q). apply cgr_par. exact H0. apply cgr_par_assoc.
        ** apply transitivity with ((pr_subst x x0 (pr_rec x x0) ‖ x1) ‖ q). apply cgr_par. exact H1. apply cgr_par_assoc.
    * right. right. right. left. exists x. exists x0. exists (x1 ‖ q). split.
        ** apply transitivity with (((If one Then x Else x0) ‖ x1) ‖ q). apply cgr_par. exact H0. apply cgr_par_assoc.
        ** apply transitivity with ((x ‖ x1) ‖ q). apply cgr_par. exact H1. apply cgr_par_assoc.
    * right. right. right. right. exists x. exists x0. exists (x1 ‖ q). split.
        ** apply transitivity with (((If zero Then x Else x0) ‖ x1) ‖ q). apply cgr_par. exact H0. apply cgr_par_assoc.
        ** apply transitivity with ((x0 ‖ x1) ‖ q). apply cgr_par. exact H1. apply cgr_par_assoc.
  - destruct IHTransition as [IH|[IH|[IH|[IH |IH]]]]; decompose record IH. 
    * left. exists x. exists x0. exists x1. exists x2. exists x3. exists x4. exists x5 (* ?? *). split. apply cgr_trans with p2. exact H. exact H2.
      apply cgr_trans with q2. apply cgr_symm. exact H0. exact H3.
    * right. left. exists x. exists x0. exists x1. split. apply cgr_trans with p2. exact H. exact H2. apply cgr_trans with q2.
      apply cgr_symm. apply H0. apply H3.
    * right. right. left. exists x. exists x0. exists x1. split. apply cgr_trans with p2. exact H. exact H2. apply cgr_trans with q2.
      apply cgr_symm. apply H0. apply H3.
    * right. right. right. left. exists x. exists x0. exists x1. split. apply cgr_trans with p2. exact H. exact H2. apply cgr_trans with q2.
      apply cgr_symm. apply H0. apply H3.
    * right. right. right. right. exists x. exists x0. exists x1. split. apply cgr_trans with p2. exact H. exact H2. apply cgr_trans with q2.
      apply cgr_symm. apply H0. apply H3.
Qed.

(* For the (LTS-transition), the transitable terms and transitted terms, that performs a INPUT,
are pretty all the same, up to ≡* *)
Lemma TransitionShapeForInput : forall P Q c v, (lts P (ActIn c v)) Q -> 
(exists P1 G R, ((P ≡* ((c ? x • P1 + G) ‖ R)) /\ (Q ≡* (P1 v ‖ R)) /\ ((exists L,P = (g L)) -> R = ⓪))).
Proof.
intros P Q c v Transition.
 dependent induction Transition.
- exists P. exists ⓪. exists ⓪. split ; try split.
  * apply cgr_trans with ((c ? x • P) + ⓪). apply cgr_trans with (c ? x • P). apply cgr_refl. apply cgr_choice_nil_rev. apply cgr_par_nil_rev.
  * apply cgr_par_nil_rev.
  * reflexivity.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists x0. exists (x1 ‖ q). split; try split.
  * apply cgr_trans with ((((c ? l • x) + x0) ‖ x1) ‖ q). apply cgr_par. exact H0. apply cgr_par_assoc.
  * apply cgr_trans with ((x v ‖ x1) ‖ q). apply cgr_par. exact H1. apply cgr_par_assoc.
  * intros. inversion H2. inversion H4.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists x0. exists (x1 ‖ p). split; try split.
  * apply cgr_trans with ((((c ? l • x) + x0) ‖ x1) ‖ p). apply cgr_trans with (q1 ‖ p). apply cgr_par_com. apply cgr_par. exact H0. apply cgr_par_assoc.
  * apply cgr_trans with ((x v ‖ x1) ‖ p). apply cgr_trans with (q2 ‖ p). apply cgr_par_com. apply cgr_par. exact H1. apply cgr_par_assoc.
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
  * reflexivity.
Qed.

(* For the (LTS-transition), the transitable terms and transitted terms, that performs a OUPUT,
are pretty all the same, up to ≡* *)
Lemma TransitionShapeForOutput : forall P Q c v, (lts P (ActOut c v)) Q -> 
(exists P1 G R, ((P ≡* ((c ! v • P1 + G) ‖ R)) /\ (Q ≡* (P1 ‖ R)) /\ ((exists L,P = (g L)) -> R = ⓪))).
Proof.
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
  * reflexivity.
Qed.



(* For the (LTS-transition), the transitable Guards and transitted terms, that performs a Tau ,
are pretty all the same, up to ≡* *)
Lemma TransitionShapeForTauAndGuard : forall P V, ((lts P τ V) /\ (exists L, P = (g L))) -> 
(exists Q M, ((P ≡* ((t • Q) + M))) /\ (V ≡* (Q))).
Proof.
intros P V Hyp. 
destruct Hyp. rename H into Transition. dependent induction Transition.
- exists P. exists ⓪. split. 
  * apply cgr_choice_nil_rev.
  * apply cgr_refl.
- inversion H0. inversion H.
- inversion H0. inversion H.
- inversion H0. inversion H.
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
  apply cgr_choice_com. apply cgr_choice. exact H. apply cgr_choice_assoc. exact H1.
Qed.

(* p 'is equivalent some r 'and r performs α to q *)
Definition sc_then_lts p α q := exists r, p ≡* r /\ (lts r α q).

(* p performs α to some r and this is equivalent to q*)
Definition lts_then_sc p α q := exists r, ((lts p α r) /\ r ≡* q).


(* p 'is equivalent some r 'and r performs α to q , the congruence and the Transition can be reversed : *)
Lemma Congruence_Respects_Transition  : forall p q α, sc_then_lts p α q -> lts_then_sc p α q.
Proof.
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
    + intros. dependent destruction l. exists p. split. assert ((λ _ : ValueType, p) v = p). reflexivity. set (λ _ : ValueType, p) as P. 
      assert (P v = p).  exact H0. rewrite <-H1. apply lts_input. constructor. apply H.
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
    destruct H. destruct H0. eauto with cgr.
Qed.



(* One side of the Harmony Lemma *)
Lemma Reduction_Implies_TausAndCong : forall P Q, (sts P Q) -> (lts_then_sc P τ Q).
Proof.
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
  symmetry. exact H1. 
Qed.


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
Proof.
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
  apply cgr_choice. exact H0. apply cgr_choice_assoc. instantiate (1:= x). apply sts_tau. symmetry. exact H1.
Qed.

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