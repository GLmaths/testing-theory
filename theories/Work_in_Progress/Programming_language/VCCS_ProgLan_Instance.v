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
From Stdlib Require Import Relations.
From Stdlib.Wellfounded Require Import Inverse_Image.
From stdpp Require Import base countable finite gmap list gmultiset strings.
From TestingTheory Require Import InputOutputActions ActTau OldTransitionSystems.

(*
From Stdlib.Vectors Require Vector.
(* Module Import V := Coq.Vectors.Vector.
Import V.VectorNotations. *)
(* Require Import Coq.Lists.List.
Import ListNotations. *)
From Stdlib Require List.
Import ListNotations.
From stdpp Require Import vector list.


(* ChannelType est le type des canaux, par exemple des chaînes de caractères*)
(* ValueType est le type des données transmises, par exemple des entiers, des chaînes de caractères, des programmes (?) *)

(*************************************** Channels ******************************************)
Parameter (Channel : Type).

Parameter (channel_eq_dec : EqDecision Channel).
#[global] Instance channel_eqdecision : EqDecision Channel. by exact channel_eq_dec. Defined.

Parameter (channel_is_countable : Countable Channel).
#[global] Instance channel_countable : Countable Channel. by exact channel_is_countable. Defined.


(* (*************************************** Values ******************************************)
Parameter (Value : Type).

Parameter (value_eq_dec : EqDecision Value).
#[global] Instance value_eqdecision : EqDecision Value. by exact value_eq_dec. Defined.*)
#[global] Instance value_eqdecision : EqDecision nat. by exact Nat.eq_dec. Defined.

(*Parameter (value_is_countable : Countable Value).
#[global] Instance value_countable : Countable Value. by exact value_is_countable. Defined. *)
#[global] Instance value_countable : Countable nat. by exact nat_countable. Defined.

Definition Value := nat.

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

(* Labbels *)
Inductive TypeOfActions := 
| act : Channel -> Data -> TypeOfActions.

Notation "c ⋉ v" := (act c v) (at level 50).

(* Parameter (Equation : Type -> Type).

Parameter (Eval_Eq : Equation Data -> (option bool)). *)

(* Definition of processes*)
Inductive proc : Type :=
(* To parallele two processes*)
| pr_par : proc -> proc -> proc
(* Variable in a process, for recursion and substitution*)
| pr_var : nat -> proc
(* recursion for process*)
| pr_rec : nat -> proc -> proc
(* matching nat with 0 and S n *)
| pr_match : Data -> proc -> proc -> proc
(* (* matching nat with nats' in l o *)
| pr_match_list {n : nat}: Data -> vec Data n -> vec proc n -> proc -> proc *)
(* (* If test *NEW term in comparison of CCS* *)
| pr_if_then_else : (list Data -> Prop) -> proc -> proc -> proc *)
(*The Guards*)
| g : gproc -> proc

with gproc : Type :=
(* The Success operation*)
| gpr_success : gproc
(* The Process that does nothing*)
| gpr_nil : gproc
(*An input is a name of a channel, an input variable, followed by a process*)
| gpr_input : Channel -> proc -> gproc
(*An output is a name of a channel, an ouput value, followed by a process*)
| gpr_output : Channel -> Data -> proc -> gproc
(*A tau action : does nothing *)
| gpr_tau : proc -> gproc
(* To choose between two processes*)
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
Notation "c ! v • P" := (gpr_output c v P) (at level 50).
Notation "c ? P" := (gpr_input c P) (at level 50).
Notation "'t' • P" := (gpr_tau P) (at level 50).
(* Notation "'If' C 'Then' P 'Else' Q" := (pr_if_then_else C P Q)
(at level 200, right associativity, format
"'[v   ' 'If'  C '/' '[' 'Then'  P  ']' '/' '[' 'Else'  Q ']' ']'"). *)

Notation "'Match' d 'With' 'zero=>' P 'succ=>' Q" := (pr_match d P Q) 
(at level 200, right associativity, format
"'[v   ' 'Match'  d  'With' '/' '[' 'zero=>'  P  ']' '/' '[' 'succ=>'  Q ']' ']'").
(* Notation "'Match' d  'With' v_nat '=>' v_proc 'otherwise=>' p" := (pr_match_list d v_nat v_proc p) 
(at level 200, right associativity, format
"'[v   ' 'Match' d  '/' 'With' '/' '[' v_nat '=>'  v_proc  ']' '/' '[' 'otherwise=>'  p ']' ']'"). *)

(*Definition of the Substitution *)
Definition subst_Data (k : nat) (X : Data) (Y : Data) : Data := 
match Y with
| cst v => cst v
| bvar i => if (decide(i = k)) then X else if (decide(i < k)) then bvar i
                                                              else bvar (Nat.pred i)
end.

(* Definition subst_in_Equation (k : nat) (X : Data) (E : Equation Data) : Equation Data :=
match E with 
| D1 == D2 => (subst_Data k X D1) == (subst_Data k X D2)
end. *)

(* Definition subst_in_l (k : nat) (X : Data) (l : list Data) : list Data :=
match l with 
| [] => []
| d :: l => (subst_Data k X d) :: l
end. *)

(* Definition subst_in_vec_Data {n : nat} (k : nat) (X : Data) (V : vec Data n) : vec Data n :=
match V with 
| [#] => [#]
| d ::: l => (subst_Data k X d) ::: l
end. *)


(* Definition subst_in_Equation (k : nat) (X : Data) (P : list Data -> Prop) : list Data -> Prop 
    := fun l => P (subst_in_l k X l). *)

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
| Match d With zero=> P succ=> Q => Match (subst_Data k X d) With 
                                      zero=> (subst_in_proc (S k) (Succ_bvar X) P)
                                      succ=> (subst_in_proc (S k) (Succ_bvar X) Q)
(* | Match d With v_nat => v_proc otherwise=> p => Match (subst_Data k X d) With  
                                                      (subst_in_vec_Data k X v_nat) => (vmap (subst_in_proc (S k) (Succ_bvar X)) v_proc)
                                                      otherwise=> (subst_in_proc (S k) (Succ_bvar X) p) *)
(* | If C Then P Else Q => If (subst_in_Equation k X C)
                           Then (subst_in_proc k X P)
                           Else (subst_in_proc k X Q) *)
| g M => subst_in_gproc k X M
end

with subst_in_gproc k X M {struct M} : gproc :=
match M with 
| ① => ①
| 𝟘 => 𝟘
| c ? p => c ? (subst_in_proc (S k) (Succ_bvar X) p)
| c ! v • p => c ! (subst_Data k X v) • (subst_in_proc k X p)
| t • p => t • (subst_in_proc k X p)
| p1 + p2 => (subst_in_gproc k X p1) + (subst_in_gproc k X p2)
end. 

Notation "t1 ^ x1" := (subst_in_proc 0 x1 t1).

Definition subst_in_external_action (k : nat) (X : Data) (μ : ExtAct TypeOfActions) : ExtAct TypeOfActions :=
match μ with
| ActIn (c ⋉ v) => ActIn (c ⋉ (subst_Data k X v))
| ActOut (c ⋉ v) => ActOut (c ⋉ (subst_Data k X v))
end.

Definition subst_in_action (k : nat) (X : Data) (α : ActIO TypeOfActions) : (ActIO TypeOfActions) :=
match α with
| ActExt μ => ActExt (subst_in_external_action k X μ)
| τ => τ
end.

Notation "α '*^' x1" := (subst_in_action 0 x1 α) (at level 30).

Definition NewVar_in_Data (k : nat) (Y : Data) : Data := 
match Y with
| cst v => cst v
| bvar i => if (decide(k < S i)) then bvar (S i) else bvar i
end.

(* Definition NewVar_in_Equation (k : nat) (E : Equation Data) : Equation Data :=
match E with
| D1 == D2 => (NewVar_in_Data k D1) == (NewVar_in_Data k D2)
end. *)

(* Definition NewVar_in_l (k : nat) (l : list Data) : list Data :=
match l with 
| [] => []
| d :: l => (NewVar_in_Data k d) :: l
end.
 *)

(* Definition NewVar_in_vec_Data {n : nat} (k : nat) (V : vec Data n) : vec Data n :=
match V with 
| [#] => [#]
| d ::: l => (NewVar_in_Data k d) ::: l
end. *)

(* Definition NewVar_in_Equation (k : nat) (P : list Data -> Prop) : list Data -> Prop 
    := fun l => P (NewVar_in_l k l).
 *)

Fixpoint NewVar (k : nat) (p : proc) {struct p} : proc :=
match p with
| P ‖ Q => (NewVar k P) ‖ (NewVar k Q)
| pr_var i => pr_var i
| rec x • P =>  rec x • (NewVar k P)
| Match d With zero=> P succ=> Q => Match (NewVar_in_Data k d) With
                                  zero=> (NewVar (S k) P)
                                  succ=> (NewVar (S k) Q)
(* | Match d With v_nat => v_proc otherwise=> p => Match (NewVar_in_Data k d) With  
                                                      (NewVar_in_vec_Data k v_nat) => (vmap (NewVar (S k)) v_proc)
                                                      otherwise=> (NewVar (S k) p) *)
(* | If C Then P Else Q => If (NewVar_in_Equation k C)
                          Then (NewVar k P)
                          Else (NewVar k Q) *)
| g M => gNewVar k M
end

with gNewVar k M {struct M} : gproc :=
match M with 
| ① => ①
| 𝟘 => 𝟘
| c ? p => c ? (NewVar (S k) p)
| c ! v • p => c ! (NewVar_in_Data k v) • (NewVar k p)
| t • p => t • (NewVar k p)
| p1 + p2 => (gNewVar k p1) + (gNewVar k p2)
end.

(* Substitution for the Recursive Variable *)
Fixpoint pr_subst (id : nat) (p : proc) (q : proc) : proc :=
  match p with 
  | p1 ‖ p2 => (pr_subst id p1 q) ‖ (pr_subst id p2 q) 
  | pr_var id' => if decide (id = id') then q else p
  | rec id' • p => if decide (id = id') then p else rec id' • (pr_subst id p q)
  | Match n With zero=> P succ=> Q => Match n With
                                        zero=> (pr_subst id P (NewVar 0 q))
                                        succ=> (pr_subst id Q (NewVar 0 q))
(*   | Match d With v_nat => v_proc otherwise=> P => Match d With  
                                                      v_nat => (vmap (fun P' => pr_subst id P' (NewVar 0 q)) v_proc)
                                                      otherwise=> (pr_subst id P (NewVar 0 q)) *)
(*   | If C Then P Else Q => If C Then (pr_subst id P q) Else (pr_subst id Q q) *)
  | g gp => g (gpr_subst id gp q)
end

with gpr_subst id p q {struct p} := match p with
| ① => ①
| 𝟘 => 𝟘
| c ? p => c ? (pr_subst id p (NewVar 0 q))
| c ! v • p => c ! v • (pr_subst id p q)
| t • p => t • (pr_subst id p q)
| p1 + p2 => (gpr_subst id p1 q) + (gpr_subst id p2 q)
end.

(* #[global] Program Instance LOOK (n : nat) : LookupTotal nat proc (vec Data n).
Next Obligation.
intros. exact 𝟘. Defined. (* Delta in VCCS_SEQ, I think *) *)

(* The Labelled Transition System (LTS-transition) *)
Inductive lts : proc-> (ActIO TypeOfActions) -> proc -> Prop :=
(*The Input and the Output*)
| lts_input : forall {c v P},
    lts (c ? P) ((c ⋉ v) ?) (P^v)
| lts_output : forall {c v P},
    lts (c ! v • P) ((c ⋉ v) !) P

(* Patern matching on nat constructor *)
| lts_match_zero : forall {p q α p'}, lts (p^(cst 0)) α p' -> 
    lts (Match (cst 0) With zero=> p succ=> q) α p'
| lts_match_succ: forall {p q α q' n'}, lts (q^(cst n')) α q' -> 
    lts (Match (cst (S n')) With zero=> p succ=> q) α q'

(* (* Patern matching on nat list *)
| lts_match_any : forall {n'} {v_nat : vec Data n'} {i v_proc n α p' q},
  (cst n) = v_nat !!! i ->
  lts ((v_proc !!! i)^(cst n)) α p' ->
    lts (Match (cst n) With v_nat => v_proc otherwise=> q) α p' *)
(* | lts_match_none : forall {p q α q' n'}, lts (q^(cst n')) α q' -> 
    lts (Match (cst n) With zero=> otherwise=> q) α q' *) 

(*The actions Tau*)
| lts_tau : forall {P},
    lts (t • P) τ P 
| lts_recursion : forall {x P},
    lts (rec x • P) τ (pr_subst x P (rec x • P))
(* | lts_ifOne : forall {p q P l}, P l -> Decision (P l) -> 
    lts (If P Then p Else q) τ p
| lts_ifZero : forall {p q P l}, ¬ P l -> Decision (P l) ->
    lts (If P Then p Else q) τ q *)

(* Communication of a channel output and input that have the same name*)
| lts_comL : forall {c v p1 p2 q1 q2},
    lts p1 ((c ⋉ v) !) p2 ->
    lts q1 ((c ⋉v) ?) q2 ->
    lts (p1 ‖ q1) τ (p2 ‖ q2) 
| lts_comR : forall {c v p1 p2 q1 q2},
    lts p1 ((c ⋉ v) !) p2 ->
    lts q1 ((c ⋉ v) ?) q2 ->
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
  | Match d With zero=> P succ=> Q => S (size P + size Q)
(*   | Match d With v_nat => v_proc otherwise=> P  => S ((list_sum (vmap size v_proc)) + size P) *)
(*   | If C Then p Else q => S (size p + size q) *)
  | rec x • p => S (size p)
  | g p => gsize p
  end

with gsize p :=
  match p with
  | ① => 1
  | 𝟘 => 0
  | c ? p => S (size p)
  | c ! v • p => S (size p)
  | t • p => S (size p)
  | p + q => S (gsize p + gsize q)
end.

#[global] Hint Constructors lts:ccs.

Fixpoint MatchEq (d : Data) (v : Value) P Q :=
match v with 
| 0 => Match d With zero=> P succ=> Q
| S n'' => Match d With zero=> Q succ=> (MatchEq (bvar 0) n'' (NewVar 0 P) (NewVar 0 Q))
end.

Notation "'If' '(' d '==' n ')' 'Then' P 'Else' Q" := (MatchEq d n P Q)
(at level 200, right associativity, format
"'[v   ' 'If'  '('  d  '=='  n  ')'  '/' '[' 'Then'  P  ']' '/' '[' 'Else'  Q ']' ']'").

(*Naïve definition of a relation ≡ that will become a congruence ≡* by transitivity*)
Inductive cgr_step : proc -> proc -> Prop :=
(*  Reflexivity of the Relation ≡  *)
| cgr_refl_step : forall p, p ≡ p

(* Rules for pattern matching with nat constructor *)
| cgr_match_zero_step : forall p q, (Match (cst 0) With zero=> p succ=> q) ≡ p^(cst 0)
| cgr_match_zero_rev_step  : forall p q, p^(cst 0) ≡ (Match (cst 0) With zero=> p succ=> q)
| cgr_match_succ_step  : forall p q n', (Match (cst (S n')) With zero=> p succ=> q) ≡ q^(cst n')
| cgr_match_succ_rev_step  : forall p q n', q^(cst n') ≡ (Match (cst (S n')) With zero=> p succ=> q)

(* (* Rules for pattern matching with nat constructor *)
((v_nat !!! i)^(cst n))
| cgr_match_zero_step : forall p q, (Match (cst 0) With zero=> p succ=> q) ≡ p^(cst 0)
| cgr_match_zero_rev_step  : forall p q, p^(cst 0) ≡ (Match (cst 0) With zero=> p succ=> q)
| cgr_match_succ_step  : forall p q n', (Match (S n') With zero=> p succ=> q) ≡ q^(cst n')
| cgr_match_succ_rev_step  : forall p q n', q^(cst n') ≡ (Match (S n') With zero=> p succ=> q) *)

(* Rules for the Parallèle *)
| cgr_par_nil_step : forall p, 
    p ‖ 𝟘 ≡ p
| cgr_par_nil_rev_step : forall p,
    p ≡ p ‖ 𝟘
| cgr_par_com_step : forall p q,
    p ‖ q ≡ q ‖ p
| cgr_par_assoc_step : forall p q r,
    (p ‖ q) ‖ r ≡ p ‖ (q ‖ r)
| cgr_par_assoc_rev_step : forall p q r,
    p ‖ (q  ‖ r) ≡ (p ‖ q) ‖ r

(* Rules for the Summation *)
| cgr_choice_nil_step : forall p,
    cgr_step (p + 𝟘) p
| cgr_choice_nil_rev_step : forall p,
    cgr_step (g p) (p + 𝟘)
| cgr_choice_com_step : forall p q,
    cgr_step (p + q) (q + p)
| cgr_choice_assoc_step : forall p q r,
    cgr_step ((p + q) + r) (p + (q + r))
| cgr_choice_assoc_rev_step : forall p q r,
    cgr_step (p + (q + r)) ((p + q) + r)

(* Congruence through contexts to certain terms...*)
| cgr_recursion_step : forall x p q,
    cgr_step p q -> (rec x • p) ≡ (rec x • q)
| cgr_tau_step : forall p q,
    cgr_step p q ->
    cgr_step (t • p) (t • q)
| cgr_input_step : forall c p q,
    cgr_step p q ->
    cgr_step (c ? p) (c ? q)
| cgr_output_step : forall c v p q,
    cgr_step p q ->
    cgr_step (c ! v • p) (c ! v • q)
| cgr_par_step : forall p q r,
    cgr_step p q ->
    p ‖ r ≡ q ‖ r
(* | cgr_if_left_step : forall C p q q',
    cgr_step q q' ->
    (If C Then p Else q) ≡ (If C Then p Else q')
| cgr_if_right_step : forall C p p' q,
    cgr_step p p' ->
    (If C Then p Else q) ≡ (If C Then p' Else q) *)
| cgr_match_zero_branch_context_step : forall n p p' q, 
    cgr_step p p' ->
    (Match n With zero=> p succ=> q) ≡ (Match n With zero=> p' succ=> q)
| cgr_match_succ_branch_context_step : forall n p q q', 
    cgr_step q q' ->
    (Match n With zero=> p succ=> q) ≡ (Match n With zero=> p succ=> q')
   
(* | cgr_match_nat_any_branch : forall p p' v_proc i d v_nat q, 
    cgr_step p p' -> p = v_proc !!! i \/ p' = v_proc !!! i -> 
    (Match d With v_nat => v_proc succ=> q) ≡ (Match n With zero=> p' succ=> q)
    
    (Match (cst n) With v_nat => v_proc otherwise=> q)
| cgr_match_right_step : forall n p q q', 
    cgr_step q q' ->
    (Match n With zero=> p succ=> q) ≡ (Match n With zero=> p succ=> q') *)

(*...and sums (only for guards (by sanity))*)
| cgr_choice_step : forall p1 q1 p2,
    cgr_step (g p1) (g q1) -> 
    cgr_step (p1 + p2) (q1 + p2)
.


#[global] Hint Constructors cgr_step:cgr_step_structure.

Infix "≡" := cgr_step (at level 70).


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
Definition cgr := (clos_trans proc cgr_step).

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
Lemma cgr_match_zero : forall p q, (Match (cst 0) With zero=> p succ=> q) ≡* p^(cst 0).
Proof.
constructor.
apply cgr_match_zero_step; eauto.
Qed.
Lemma cgr_match_zero_rev : forall p q, p^(cst 0) ≡* (Match (cst 0) With zero=> p succ=> q).
Proof.
constructor.
apply cgr_match_zero_rev_step; eauto.
Qed.
Lemma cgr_match_succ : forall p q n', (Match (cst (S n')) With zero=> p succ=> q) ≡* q^(cst n').
Proof.
constructor.
apply cgr_match_succ_step; eauto.
Qed.
Lemma cgr_match_succ_rev : forall p q n', q^(cst n') ≡* (Match (cst (S n')) With zero=> p succ=> q).
Proof.
constructor.
apply cgr_match_succ_rev_step; eauto.
Qed.
Lemma cgr_par_nil : forall p, p ‖ 𝟘 ≡* p.
Proof.
constructor.
apply cgr_par_nil_step.
Qed.
Lemma cgr_par_nil_rev : forall p, p ≡* p ‖ 𝟘.
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
Lemma cgr_choice_nil : forall p, p + 𝟘 ≡* p.
Proof.
constructor.
apply cgr_choice_nil_step.
Qed.
Lemma cgr_choice_nil_rev : forall p, (g p) ≡* p + 𝟘.
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
Lemma cgr_input : forall c p q, p ≡* q -> (c ? p) ≡* (c ? q).
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
(* Lemma cgr_if_left : forall C p q q', q ≡* q' -> (If C Then p Else q) ≡* (If C Then p Else q').
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
Qed. *)
Lemma cgr_choice : forall p q r, g p ≡* g q -> p + r ≡* q + r.
Proof.
intros. dependent induction H. 
constructor.
apply cgr_choice_step. exact H. admit. (* again and again *)
Admitted.
Lemma cgr_match_zero_branch_context : forall n p p' q, p ≡* p' 
  -> (Match n With zero=> p succ=> q) ≡* (Match n With zero=> p' succ=> q).
Proof.
intros. dependent induction H. 
constructor.
apply cgr_match_zero_branch_context_step. exact H. eauto with cgr_eq.
Qed.
Lemma cgr_match_succ_branch_context : forall n p q q', q ≡* q' 
  -> (Match n With zero=> p succ=> q) ≡* (Match n With zero=> p succ=> q').
Proof.
intros. dependent induction H. 
constructor.
apply cgr_match_succ_branch_context_step. exact H. eauto with cgr_eq.
Qed.

Lemma cgr_full_match : forall n p p' q q', p ≡* p' -> q ≡* q'
  -> (Match n With zero=> p succ=> q) ≡* (Match n With zero=> p' succ=> q').
Proof.
intros.
apply transitivity with (Match n With zero=> p succ=> q'). apply cgr_match_succ_branch_context. exact H0. 
apply cgr_match_zero_branch_context. exact H. 
Qed.

(* Lemma cgr_full_if : forall C p p' q q', p ≡* p' -> q ≡* q' -> (If C Then p Else q) ≡* (If C Then p' Else q').
Proof.
intros.
apply transitivity with (If C Then p Else q'). apply cgr_if_left. exact H0. 
apply cgr_if_right. exact H. 
Qed. *)


(* The sum of guards respects ≡* *)
Lemma cgr_fullchoice : forall M1 M2 M3 M4, g M1 ≡* g M2 -> g M3 ≡* g M4 -> M1 + M3 ≡* M2 + M4.
Proof.
intros.
apply transitivity with (g (M2 + M3)). apply cgr_choice. exact H. apply transitivity with (g (M3 + M2)).
apply cgr_choice_com. apply transitivity with (g (M4 + M2)). apply cgr_choice. exact H0. apply cgr_choice_com.
Qed.
(* The parallele of process respects ≡* *)
Lemma cgr_fullpar : forall M1 M2 M3 M4, M1 ≡* M2 -> M3 ≡* M4 -> M1 ‖ M3 ≡* M2 ‖ M4.
Proof.
intros.
apply transitivity with (M2 ‖ M3). apply cgr_par. exact H. apply transitivity with (M3 ‖ M2).
apply cgr_par_com. apply transitivity with (M4 ‖ M2). apply cgr_par. exact H0. apply cgr_par_com.
Qed.


#[global] Hint Resolve cgr_match_zero cgr_match_zero_rev cgr_match_succ cgr_match_succ_rev
cgr_par_nil cgr_par_nil_rev cgr_par_com cgr_par_assoc cgr_par_assoc_rev 
cgr_choice_nil cgr_choice_nil_rev cgr_choice_com cgr_choice_assoc cgr_choice_assoc_rev
cgr_recursion cgr_tau cgr_input cgr_output (* cgr_if_left cgr_if_right *) cgr_par cgr_choice
cgr_match_zero_branch_context cgr_match_succ_branch_context
cgr_full_match (* cgr_full_if *) cgr_fullchoice cgr_fullpar 

cgr_refl cgr_symm cgr_trans:cgr.


(* Parameter (subst_true : forall k v eq, Eval_Eq eq = Some(true)
            -> Eval_Eq (subst_in_Equation k v eq) = Some(true)).
Parameter (subst_false : forall k v eq, Eval_Eq eq = Some(false)
            -> Eval_Eq (subst_in_Equation k v eq) = Some(false)).
Parameter (NewVar_true : forall j eq, Eval_Eq eq = Some(true)
            -> Eval_Eq (NewVar_in_Equation j eq) = Some(true)).
Parameter (NewVar_false : forall j eq, Eval_Eq eq = Some(false)
            -> Eval_Eq (NewVar_in_Equation j eq) = Some(false)). *)

Lemma Subst_For_Data k v j d m: subst_Data j (cst m) (subst_Data (j + (S k)) (NewVar_in_Data j v) d) 
          =  (subst_Data (j + k) v (subst_Data j (cst m) d)).
Proof.
  intros. revert k. revert v. revert j.
  dependent induction d; intros.
  - simpl. reflexivity.
  - simpl. destruct (decide (n = (j + S k)%nat)).
    + destruct (decide((n = j)%nat)).
      * simpl. subst. lia.
      * subst. simpl. rewrite decide_False; eauto with lia. simpl. 
        rewrite decide_True; eauto with lia. destruct v.
        -- simpl. eauto.
        -- simpl. destruct (decide ((j < S n))).
           ++ simpl. rewrite decide_False; eauto with lia.
              rewrite decide_False; eauto with lia.
           ++ simpl. rewrite decide_False; eauto with lia.
              rewrite decide_True; eauto with lia.
    + destruct (decide (n < j + S k)).
      * simpl. destruct (decide((n = j)%nat)).
        -- subst. simpl. reflexivity.
        -- destruct (decide (n < j)).
           ++ simpl. destruct (decide ((n = (j + k)%nat))).
              ** subst. lia.
              ** simpl. rewrite decide_True; eauto with lia.
           ++ destruct (decide (n=0) % nat).
              ** subst. lia.
              ** (* assert (exists n', n= S n') as (n' & eq). Search (_ ≠ 0). *)
                 simpl. destruct (decide (Nat.pred n = (j + k)%nat)).
                 --- lia.
                 --- rewrite decide_True; eauto with lia.
      * simpl. rewrite decide_False; eauto with lia. 
        rewrite decide_False; eauto with lia.
        rewrite decide_False; eauto with lia.
        rewrite decide_False; eauto with lia.
        simpl. rewrite decide_False; eauto with lia.
        rewrite decide_False; eauto with lia.
Qed.

Lemma Succ_bvar_and_NewVar_in_Data_0 : forall v, NewVar_in_Data 0 v = Succ_bvar v.
Proof.
intros. induction v; simpl; reflexivity.
Qed.

Lemma New_Var_And_NewVar_in_Data : forall j i e, NewVar_in_Data (i + S j) (NewVar_in_Data i e) = NewVar_in_Data i (NewVar_in_Data (i + j) e).
Proof.
intros. revert j. induction e.
* intros. simpl. reflexivity.
* intros. simpl. destruct (decide (i < S n)); destruct (decide (i + j < S n)); simpl; auto.
  - destruct (decide (i + S j < S (S n))); destruct ((decide (i < S (S n)))); simpl; auto with arith. exfalso. apply n0. auto with arith.
    exfalso. apply n0. simpl. assert ((i + S j)%nat = S (i + j)%nat). auto with arith. rewrite H. auto with arith.
  - destruct (decide (i + S j < S (S n))); destruct (decide (i < S n)); simpl; auto with arith. exfalso. apply n0. 
    assert ((i + S j)%nat = S (i + j)%nat). auto with arith. rewrite H in l0. auto with arith. exfalso. apply n1. assumption. exfalso. apply n2.
    assumption.
  - exfalso. apply n0. assert (i <= i + j). auto with arith. destruct H. assumption. apply transitivity with (S m). auto with arith. assumption.
  - destruct (decide (i + S j < S n)); destruct (decide (i < S n)); simpl; auto with arith. exfalso. apply n2. eauto with arith.
    exfalso. apply n0. assumption.
Qed.

Lemma Subst_For_Match k v j p m : subst_in_proc j (cst m) (subst_in_proc (j + (S k)) (NewVar_in_Data j v) p) 
          = subst_in_proc (k + j) v (subst_in_proc j (cst m) p).
Proof.
  intros. revert k. revert v. revert j.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; simpl; intros.
  * assert ((subst_in_proc j (cst m) (subst_in_proc (j + (S k)) (NewVar_in_Data j v) p1)) 
        = subst_in_proc (k + j) v (subst_in_proc j (cst m) p1)) as eq1.
    { apply Hp. simpl. auto with arith. }
    assert ((subst_in_proc j (cst m) (subst_in_proc (j + (S k)) (NewVar_in_Data j v) p2)) 
        = subst_in_proc (k + j) v (subst_in_proc j (cst m) p2)) as eq2.
    { apply Hp. simpl. auto with arith. }
    rewrite eq1. rewrite eq2. auto.
  * reflexivity.
  * assert ((subst_in_proc j (cst m) (subst_in_proc (j + (S k)) (NewVar_in_Data j v) p)) 
        = subst_in_proc (k + j) v (subst_in_proc j (cst m) p)) as eq.
    { apply Hp. simpl. auto with arith. }
    rewrite eq; auto.
  * assert (subst_Data j (cst m) (subst_Data (j + S k) (NewVar_in_Data j v) d)
          =  (subst_Data (j + k) v (subst_Data j (cst m) d))) as eq.
    { eapply Subst_For_Data. }
    assert (j + k = k + j)%nat as eq' by lia . rewrite eq' in eq.
    simpl in *. rewrite eq.
    assert (subst_in_proc (S j) (cst m) (subst_in_proc ((S j) + S k) (NewVar_in_Data (S j) (NewVar_in_Data 0 v)) p1) =
           subst_in_proc (k + (S j)) (NewVar_in_Data 0 v) (subst_in_proc (S j) (cst m) p1)) as eq1.
    { eapply Hp ;eauto with lia. }
    assert (subst_in_proc (S j) (cst m) (subst_in_proc ((S j) + S k) (NewVar_in_Data (S j) (NewVar_in_Data 0 v)) p2) =
           subst_in_proc (k + (S j)) (NewVar_in_Data 0 v) (subst_in_proc (S j) (cst m) p2)) as eq2.
    { eapply Hp ;eauto with lia. } simpl in *.
    rewrite<- (Succ_bvar_and_NewVar_in_Data_0 (NewVar_in_Data j v)).
    assert ((NewVar_in_Data 0 (NewVar_in_Data j v)) = (NewVar_in_Data (S j) (NewVar_in_Data 0 v))) as eq''.
    { assert (S j = 0 + S j)%nat as eq'1 by lia. assert (0 + j = j)%nat as eq'2 by lia.
      rewrite eq'1. rewrite<- eq'2. rewrite New_Var_And_NewVar_in_Data. eauto. }
    rewrite eq''.
    rewrite eq1, eq2. rewrite<- (Succ_bvar_and_NewVar_in_Data_0 v).
    assert ((k + S j) = S (k + j))%nat as eq''' by lia.
    rewrite eq'''. reflexivity.
  * destruct g0; simpl; auto.
    - rewrite<- (Succ_bvar_and_NewVar_in_Data_0 v).
      rewrite<- (Succ_bvar_and_NewVar_in_Data_0 ((NewVar_in_Data j v))).
      assert (S j = 0 + S j)%nat as eq'1 by lia. assert (0 + j = j)%nat as eq'2 by lia.
      rewrite eq'1. rewrite<- eq'2. rewrite<- New_Var_And_NewVar_in_Data.
      simpl in *. assert (S (k + j) = k + S j)%nat as eqd by lia.
      assert ((S (j + S k)) = ((S j) + S k))%nat as eqd' by lia.
      rewrite eqd. rewrite eqd'.
      assert ((subst_in_proc (S j) (cst m)
        (subst_in_proc ((S j) + S k) (NewVar_in_Data (S j) (NewVar_in_Data 0 v)) p)) =
          (subst_in_proc (k + S j) (NewVar_in_Data 0 v) (subst_in_proc (S j) (cst m) p))) as eq''.
      { eapply Hp. simpl; lia. }
      rewrite eq''. eauto.
    - assert (j + k = k + j)%nat as eq' by lia .
      simpl in *.
      assert (subst_Data j (cst m) (subst_Data (j + S k) (NewVar_in_Data j v) d)
        = subst_Data (k + j) v (subst_Data j (cst m) d)) as eq_data.
      { rewrite<- eq'. eapply Subst_For_Data. }
      rewrite eq_data.
      assert (subst_in_proc j (cst m) (subst_in_proc (j + S k) (NewVar_in_Data j v) p)
        = subst_in_proc (k + j) v (subst_in_proc j (cst m) p)) as eq''.
      { eapply Hp; lia. }
      rewrite eq''; eauto.
    - assert (subst_in_proc j (cst m) (subst_in_proc (j + S k) (NewVar_in_Data j v) p)
        = subst_in_proc (k + j) v (subst_in_proc j (cst m) p)) as eq''.
      { eapply Hp; simpl; lia. }
      rewrite eq''; eauto.
    - assert (subst_in_proc j (cst m) (subst_in_proc (j + S k) (NewVar_in_Data j v) g0_1) =
           subst_in_proc (k + j) v (subst_in_proc j (cst m) g0_1)) as eq1.
      { eapply Hp; simpl ; lia. }
      assert (subst_in_proc j (cst m) (subst_in_proc (j + S k) (NewVar_in_Data j v) g0_2) =
           subst_in_proc (k + j) v (subst_in_proc j (cst m) g0_2)) as eq2.
      { eapply Hp; simpl ; lia. } simpl in *.
      inversion eq1. inversion eq2.
      rewrite H0, H1. eauto.
Qed.


Lemma Congruence_Respects_Substitution : forall p q v k, p ≡* q -> (subst_in_proc k v p) ≡* (subst_in_proc k v q).
Proof.
intros. revert k. revert v. dependent induction H.
* dependent induction H; simpl; eauto with cgr.
  - intros. etrans. eapply cgr_match_zero.
    assert (S k = 0 + S k)%nat as eq by lia.
    assert (k = 0 + k)%nat as eq' by lia.
    assert (k + 0 = k)%nat as eq'' by lia.
    rewrite eq, eq'. rewrite Subst_For_Match. simpl. rewrite eq''. reflexivity.
  - intros. etrans. 2: { eapply cgr_match_zero_rev. }
    assert (S k = 0 + S k)%nat as eq by lia.
    assert (k = 0 + k)%nat as eq' by lia.
    assert (k + 0 = k)%nat as eq'' by lia.
    rewrite eq, eq'. rewrite Subst_For_Match. simpl. rewrite eq''. reflexivity.
  - intros. etrans. eapply cgr_match_succ.
    assert (S k = 0 + S k)%nat as eq by lia.
    assert (k = 0 + k)%nat as eq' by lia.
    assert (k + 0 = k)%nat as eq'' by lia.
    rewrite eq.  rewrite Subst_For_Match. simpl. rewrite eq''. reflexivity.
  - intros. etrans. 2: { eapply cgr_match_succ_rev. }
    assert (S k = 0 + S k)%nat as eq by lia.
    assert (k = 0 + k)%nat as eq' by lia.
    assert (k + 0 = k)%nat as eq'' by lia.
    rewrite eq, eq'. rewrite Subst_For_Match. simpl. rewrite eq''. reflexivity.
* eauto with cgr.
Qed.

Lemma New_Var_And_NewVar : forall j i p, NewVar (i + S j) (NewVar i p) = NewVar i (NewVar (i + j) p).
Proof.
intros. revert j i. induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct p; simpl; intros.
* assert (NewVar (i + S j) (NewVar i p1) = NewVar i (NewVar (i + j) p1)). apply Hp. simpl. auto with arith.
  assert (NewVar (i + S j) (NewVar i p2) = NewVar i (NewVar (i + j) p2)). apply Hp. simpl. auto with arith.
  rewrite H, H0. auto.
* reflexivity.
* assert (NewVar (i + S j) (NewVar i p) = NewVar i (NewVar (i + j) p)). apply Hp. simpl. auto with arith.
  rewrite H. auto.
* assert (NewVar_in_Data (i + S j) (NewVar_in_Data i d) = NewVar_in_Data i (NewVar_in_Data (i + j) d))
  as eq.
  { eapply  New_Var_And_NewVar_in_Data. }
  rewrite eq.
  assert (NewVar (S i + S j) (NewVar (S i) p1) = NewVar (S i) (NewVar ((S i) + j) p1)). apply Hp. simpl. auto with arith.
  assert (NewVar (S i + S j) (NewVar (S i) p2) = NewVar (S i) (NewVar ((S i) + j) p2)). apply Hp. simpl. auto with arith.
  assert ((S (i + S j)) = (S i) + S j)%nat as eq'' by lia.
  assert ((S (i + j)) = S i + j)%nat as eq''' by lia.
  rewrite eq''. rewrite eq'''.
  rewrite H, H0. auto.
* destruct g0.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. assert (NewVar (S (i + S j)) (NewVar (S i) p) = NewVar (S i) (NewVar (S (i + j)) p)).
    assert (S (i + S j%nat) = ((S i) + (S j))%nat). auto with arith. rewrite H. assert (S (i + j) = (S i + j)%nat).
    auto with arith. rewrite H0. 
    apply Hp. simpl. auto with arith. rewrite H. auto.
  - simpl. assert (NewVar_in_Data (i + S j) (NewVar_in_Data i d) = NewVar_in_Data i (NewVar_in_Data (i + j) d)).
    apply New_Var_And_NewVar_in_Data. rewrite H. auto.
    assert (NewVar (i + S j) (NewVar i p) = NewVar i (NewVar (i + j) p)). apply Hp. simpl. auto with arith.
    rewrite H0. auto.
  - simpl. assert (NewVar (i + S j) (NewVar i p) = NewVar i (NewVar (i + j) p)).
    apply Hp. simpl. auto with arith. rewrite H. auto.
  - simpl. assert (NewVar (i + S j) (NewVar i (g g0_1)) = NewVar i (NewVar (i + j) (g g0_1))).
    apply Hp. simpl. auto with arith. 
    assert (NewVar (i + S j) (NewVar i (g g0_2)) = NewVar i (NewVar (i + j) (g g0_2))).
    apply Hp. simpl. auto with arith. simpl in H , H0. inversion H. inversion H0.
    rewrite H2 , H3. auto.
Qed.

Lemma Subst_And_NewVar_in_Data : forall j k v d, (NewVar_in_Data j (subst_Data (j + k) v d))
                                        = subst_Data (j + S k) (NewVar_in_Data j v) (NewVar_in_Data j d).
Proof.
intros. revert k. revert v. revert j. dependent induction d.
* intros. simpl. reflexivity.
* intros. simpl. destruct (decide(n = (j+k)%nat)).
  - destruct (decide (j < S n)).
     -- simpl. destruct (decide ((S n = (j + S k)%nat))). 
        --- auto.
        --- exfalso. lia. (* pas top *)
     -- simpl. destruct (decide (n = (j + S k)%nat)).
        --- auto.
        --- exfalso. lia. (* pas top *) 
  -  destruct (decide (n < j + k)).
     -- simpl. destruct (decide (j < S n)). 
        --- simpl. destruct (decide (S n = (j + S k)%nat)). 
            ** exfalso. lia. (* pas top *)
            ** destruct (decide (S n < j + S k)).
               *** auto.
               *** exfalso. lia. (* pas top *) 
        --- simpl. destruct (decide(n = (j + S k)%nat)). 
            ** lia.
            ** destruct (decide (n < j + S k)).
              ---- auto.
              ---- lia. (* pas top *) 
     -- simpl. destruct (decide (j < S (Nat.pred n))).
        --- destruct (decide (j < S n)).
            ** simpl. destruct (decide (S n = (j + S k)%nat)).
              *** lia. (* pas top *) 
              *** destruct (decide (S n < j + S k)). 
                **** lia. (* pas top *) 
                **** assert (n ≠ 0). lia. destruct n. lia. simpl. auto. (* pas top *) 
            ** simpl. destruct (decide (n = (j + S k)%nat)).
              *** lia.
              *** destruct (decide (n < j + S k)).
                **** lia.
                **** lia.
       --- destruct (decide (j < S n)).
          ** simpl. destruct (decide(S n = (j + S k)%nat)).
              *** lia.
              *** lia.
         ** lia.
Qed.

Lemma Subst_And_NewVar : forall j k v P, NewVar j (subst_in_proc (j + k) v P) =
                                         subst_in_proc (j + S k) (NewVar_in_Data j v) (NewVar j P).
Proof.
intros. revert k. revert v. revert j. 
induction P as (P & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct P; simpl; intros.
* assert (NewVar j (subst_in_proc (j + k) v P1) = subst_in_proc (j + S k) (NewVar_in_Data j v) (NewVar j P1)). 
  apply Hp. simpl. auto with arith.
  assert (NewVar j (subst_in_proc (j + k) v P2) = subst_in_proc (j + (S k)) (NewVar_in_Data j v) (NewVar j P2)). 
  apply Hp. simpl. auto with arith.
  rewrite H. rewrite H0. auto.
* reflexivity.
* assert (NewVar j (subst_in_proc (j + k) v P) = subst_in_proc (j + (S k)) (NewVar_in_Data j v) (NewVar j P)). 
  apply Hp. simpl. auto with arith. rewrite H. auto.
* assert (S (j+k) = (S j + k))%nat as eq1 by lia.
  assert (S (j + S k) = (S j + S k))%nat as eq2 by lia.
  assert (NewVar (S j) (subst_in_proc (S (j + k)) (Succ_bvar v) P1) 
      = subst_in_proc (S (j + S k)) (Succ_bvar (NewVar_in_Data j v)) (NewVar (S j) P1) ). 
  { rewrite eq1, eq2. rewrite<- (Succ_bvar_and_NewVar_in_Data_0 (NewVar_in_Data j v)).
    assert (0 + j = j)%nat as eq'' by lia. rewrite<- eq''.
    rewrite<- New_Var_And_NewVar_in_Data. apply Hp. simpl. auto with arith. }
  assert (NewVar (S j) (subst_in_proc (S (j + k)) (Succ_bvar v) P2) 
      = subst_in_proc (S (j + S k)) (Succ_bvar (NewVar_in_Data j v)) (NewVar (S j) P2) ). 
  { rewrite eq1, eq2. rewrite<- (Succ_bvar_and_NewVar_in_Data_0 (NewVar_in_Data j v)).
    assert (0 + j = j)%nat as eq'' by lia. rewrite<- eq''.
    rewrite<- New_Var_And_NewVar_in_Data. apply Hp. simpl. auto with arith. }
  rewrite H. rewrite H0. auto.
  assert (NewVar_in_Data j (subst_Data (j + k) v d) 
      = subst_Data (j + S k) (NewVar_in_Data j v) (NewVar_in_Data j d)) as eq'''.
  { apply Subst_And_NewVar_in_Data. }
  rewrite eq'''; eauto.
* destruct g0; simpl; auto.
  - assert ((NewVar (S j) (subst_in_proc (S (j + k)) (NewVar_in_Data 0 v) p)) 
      = (subst_in_proc (S (j + S k)) (NewVar_in_Data (S j) (NewVar_in_Data 0 v)) (NewVar (S j) p))).
    { assert (size p < size (gpr_input c p)). simpl. auto with arith. eapply (Hp p H (S j) (NewVar_in_Data 0 v) k). }
    assert ((NewVar_in_Data 0 (NewVar_in_Data j v)) = NewVar_in_Data (S j) (NewVar_in_Data 0 v)).
    { assert (0 + j = j)%nat as eq' by lia. rewrite<- eq' at 1.
      assert (0 + S j = S j)%nat as eq'' by lia. rewrite<- eq''.
      rewrite New_Var_And_NewVar_in_Data. eauto. } 
    simpl in *. rewrite<- (Succ_bvar_and_NewVar_in_Data_0 (NewVar_in_Data j v)).
    rewrite H0. rewrite<- H. auto.
  - assert (NewVar j (subst_in_proc (j + k) v p) = subst_in_proc (j + (S k)) (NewVar_in_Data j v) (NewVar j p)). 
    apply Hp. simpl. auto with arith.
    assert (NewVar_in_Data j (subst_Data (j + k) v d) =  subst_Data (j + S k) (NewVar_in_Data j v) (NewVar_in_Data j d)). 
    eapply Subst_And_NewVar_in_Data. 
    rewrite H. rewrite H0. auto.
  - assert (NewVar j (subst_in_proc (j + k) v p) = subst_in_proc (j + S k) (NewVar_in_Data j v) (NewVar j p)). eapply Hp. 
    simpl. auto with arith. rewrite H. auto.
  - assert (NewVar j (subst_in_proc (j + k) v (g g0_1)) = subst_in_proc (j + S k) (NewVar_in_Data j v) (NewVar j (g g0_1))). 
    apply Hp. simpl. auto with arith.
    assert (NewVar j (subst_in_proc (j + k) v (g g0_2)) = subst_in_proc (j + (S k)) (NewVar_in_Data j v) (NewVar j (g g0_2))). 
    apply Hp. simpl. auto with arith. simpl in H0. simpl in H. inversion H. inversion H0.
    rewrite H2. rewrite H3. auto.
Qed.

Lemma Subst_And_NewVar_in_Data_trice : forall j i d m, NewVar_in_Data (j + i) (subst_Data i (cst m) d) 
      = subst_Data i (cst m) (NewVar_in_Data (j + (S i)) d).
Proof.
  intros. destruct d; simpl.
  - eauto.
  - destruct (decide (n = i)).
    + subst. simpl. destruct (decide (j + S i < S i)).
      * simpl. lia.
      * simpl. rewrite decide_True; eauto.
    + destruct (decide (n < i)).
      * rewrite decide_False; eauto with lia.
        simpl. rewrite decide_False; eauto with lia.
        rewrite decide_False; eauto with lia.
        rewrite decide_True; eauto with lia.
      * simpl. destruct (decide (j + i < S (Nat.pred n))).
        -- rewrite decide_True; eauto with lia. simpl.
           rewrite decide_False; eauto with lia.
           rewrite decide_False; eauto with lia.
        -- rewrite decide_False; eauto with lia. simpl.
           rewrite decide_False; eauto with lia.
           rewrite decide_False; eauto with lia.
Qed.

Lemma Subst_And_NewVar_trice : forall j i p m, NewVar (j + i) (subst_in_proc i (cst m) p) 
      = subst_in_proc i (cst m) (NewVar ((S j) + i) p).
Proof.
  intros. revert j i. 
  induction p as (p & Hp) using
      (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; simpl; intros.
  * assert (NewVar (j + i) (subst_in_proc i (cst m) p1) = subst_in_proc i (cst m) (NewVar ((S j)+i) p1)) as eq1. 
    { apply Hp. simpl. auto with arith. }
    assert (NewVar (j + i) (subst_in_proc i (cst m) p2) = subst_in_proc i (cst m) (NewVar ((S j) + i) p2)) as eq2. 
    { apply Hp. simpl. auto with arith. }
    rewrite eq1, eq2. auto.
  * reflexivity.
  * assert (NewVar (j + i) (subst_in_proc i (cst m) p) = subst_in_proc i (cst m) (NewVar ((S j) + i) p)) as eq. 
    { apply Hp. simpl. auto with arith. }
    rewrite eq. auto.
  * assert (S (j + i) = (j + S i))%nat as eq1 by lia.
    assert (S (j + S i) = (S j + S i))%nat as eq2 by lia.
    rewrite eq1 , eq2.
    assert (NewVar (j + S i) (subst_in_proc (S i) (cst m) p1)
        = subst_in_proc (S i) (cst m) (NewVar (S j + S i) p1)) as eq'1. 
    { apply Hp. simpl. auto with arith. }
    assert (NewVar (j + S i) (subst_in_proc (S i) (cst m) p2)
        = subst_in_proc (S i) (cst m) (NewVar (S j + S i) p2)) as eq'2.
    { apply Hp. simpl. auto with arith. }
    rewrite eq'1, eq'2.
    assert (NewVar_in_Data (j + i) (subst_Data i (cst m) d)
        = subst_Data i  (cst m) (NewVar_in_Data (j + S i) d)) as eq'''.
    { eapply Subst_And_NewVar_in_Data_trice. }
    rewrite eq'''; eauto.
  * destruct g0; simpl; auto.
    - assert ((NewVar (j + S i) (subst_in_proc (S i) (cst m) p)) 
        = (subst_in_proc (S i) (cst m) (NewVar (S j + S i) p))) as eq1.
      { eapply Hp. eauto with arith. }
      assert (S (j + i) = j + S i)%nat as eq2 by lia.
      assert (S (j + S i) = S j + S i)%nat as eq3 by lia.
      rewrite eq2, eq3, eq1. eauto.
    - assert (NewVar_in_Data (j + i) (subst_Data i (cst m) d) 
            = subst_Data i (cst m) (NewVar_in_Data (j + S i) d)) as eq1. 
      { eapply Subst_And_NewVar_in_Data_trice. }
      assert (NewVar (j + i) (subst_in_proc i (cst m) p) 
          = subst_in_proc i (cst m) (NewVar (S j + i) p)) as eq2.
      { apply Hp. simpl. auto with arith. }
      assert (S (j + i) = j + S i)%nat as eq3 by lia.
      rewrite eq3, eq1 ,eq2. eauto.
      assert (S j + i = j + S i)%nat as eq4 by lia.
      rewrite eq4. eauto.
    - assert (NewVar (j + i) (subst_in_proc i (cst m) p) 
        = subst_in_proc i (cst m) (NewVar (S (j + i)) p)) as eq.
      { eapply Hp. eauto with arith. }
      rewrite eq. eauto.
    - assert (S (j + i) = (j + S i))%nat as eq1 by lia.
      assert (NewVar (j + i) (subst_in_proc i (cst m) g0_1)
          = subst_in_proc i (cst m) (NewVar (S j + i) g0_1)) as eq'1. 
      { apply Hp. simpl. auto with arith. }
      assert (NewVar (j + i) (subst_in_proc i (cst m) g0_2)
          = subst_in_proc i (cst m) (NewVar (S j + i) g0_2)) as eq'2.
      { apply Hp. simpl. auto with arith. }
      inversion eq'1. inversion eq'2. eauto.
Qed.

Lemma NewVar_Respects_Congruence : forall p p' j, p ≡* p' -> NewVar j p ≡* NewVar j p'.
Proof.
intros.  revert j.  dependent induction H. dependent induction H ; simpl ; auto with cgr.
  - intros. etrans. eapply cgr_match_zero.
    assert (j = j + 0)%nat as eq by lia.
    rewrite eq. rewrite Subst_And_NewVar_trice.
    reflexivity.
  - intros. etrans. 2:{ eapply cgr_match_zero_rev. }
    assert (j = j + 0)%nat as eq by lia.
    rewrite eq. rewrite Subst_And_NewVar_trice.
    reflexivity.
  - intros. etrans. eapply cgr_match_succ.
    assert (j = j + 0)%nat as eq by lia.
    rewrite eq. rewrite Subst_And_NewVar_trice.
    reflexivity.
  - intros. etrans. 2:{ eapply cgr_match_succ_rev. }
    assert (j = j + 0)%nat as eq by lia.
    rewrite eq. rewrite Subst_And_NewVar_trice.
    reflexivity.
  - intros. apply cgr_choice. apply IHcgr_step. 
  - eauto with cgr.
Qed.

(* Substition lemma, needed to contextualise the equivalence *)
Lemma cgr_subst1 p q q' x : q ≡* q' → pr_subst x p q ≡* pr_subst x p q'.
Proof.
revert q q' x.
(* Induction on the size of p*)
induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct p; intros; simpl.
  - apply cgr_fullpar.
    apply Hp. simpl. rewrite <-Nat.add_succ_r. apply PeanoNat.Nat.lt_add_pos_r. apply Nat.lt_0_succ. exact H. 
    apply Hp. simpl. rewrite <-Nat.add_succ_l. apply PeanoNat.Nat.lt_add_pos_l. apply Nat.lt_0_succ. exact H.
  - destruct (decide (x = n)). exact H. reflexivity.
  - destruct (decide (x = n)). reflexivity. apply cgr_recursion. apply Hp. simpl. auto. exact H.
  - apply cgr_full_match.
    apply Hp. simpl. rewrite <-Nat.add_succ_r. apply PeanoNat.Nat.lt_add_pos_r. apply Nat.lt_0_succ.
    eapply NewVar_Respects_Congruence; eauto.
    apply Hp. simpl. rewrite <-Nat.add_succ_l. apply PeanoNat.Nat.lt_add_pos_l. apply Nat.lt_0_succ.
    eapply NewVar_Respects_Congruence; eauto.
  - destruct g0; intros; simpl.
    * reflexivity.
    * reflexivity.
    * apply cgr_input. apply Hp. simpl. auto with arith. apply NewVar_Respects_Congruence. assumption.
    * apply cgr_output. apply Hp. simpl. auto. auto.
    * apply cgr_tau. apply Hp. simpl. auto. auto.
    * apply cgr_fullchoice. 
      assert (pr_subst x (g g0_1) q ≡* pr_subst x (g g0_1) q'). apply Hp. simpl. auto with arith. auto.
      auto. assert (pr_subst x (g g0_2) q ≡* pr_subst x (g g0_2) q'). apply Hp. simpl. auto with arith. auto.
      auto. 
Qed.

Lemma PrSubst_NewVar : forall j n P p, pr_subst n (NewVar j P) (NewVar j p) = NewVar j (pr_subst n P p).
Proof.
intros. revert j n p. induction P as (P & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct P; intros.
* simpl. assert (pr_subst n (NewVar j P1) (NewVar j p) =  NewVar j (pr_subst n P1 p)). apply Hp. simpl. auto with arith.
  assert (pr_subst n (NewVar j P2) (NewVar j p) =  (NewVar j (pr_subst n P2 p))). apply Hp. simpl. auto with arith.
  rewrite H. rewrite H0. auto.
* simpl. destruct (decide (n0 = n)); simpl; auto.
* simpl. destruct (decide (n0 = n)); simpl ; auto. 
  assert (pr_subst n0 (NewVar j P) (NewVar j p) = NewVar j (pr_subst n0 P p)). apply Hp. simpl. auto with arith.
  rewrite H.  auto.
* simpl. assert (pr_subst n (NewVar (S j) P1) (NewVar (S j) (NewVar 0 p)) = NewVar (S j) (pr_subst n P1 (NewVar 0 p)) ).
  { apply Hp. simpl. auto with arith. }
  simpl. assert (pr_subst n (NewVar (S j) P2) (NewVar (S j) (NewVar 0 p)) = NewVar (S j) (pr_subst n P2 (NewVar 0 p)) ).
  { apply Hp. simpl. auto with arith. } assert (0 + j = j)%nat as eq1 by lia.
  rewrite<- eq1. rewrite<- New_Var_And_NewVar. simpl.
  rewrite H. rewrite H0. eauto.
* destruct g0; simpl; auto.
  - assert (NewVar (S j) (NewVar 0 p)= NewVar 0 (NewVar j p)). eapply (New_Var_And_NewVar j 0).
    rewrite <-H.
    assert (pr_subst n (NewVar (S j) p0) (NewVar (S j) (NewVar 0 p)) = NewVar (S j) (pr_subst n p0 (NewVar 0 p))).
    eapply (Hp p0). simpl. auto with arith. rewrite H0. auto.
  - assert (pr_subst n (NewVar j p0) (NewVar j p) = NewVar j (pr_subst n p0 p)).
    apply Hp. simpl. auto with arith. rewrite H. auto.
  - assert (pr_subst n (NewVar j p0) (NewVar j p) = NewVar j (pr_subst n p0 p)). apply Hp.
    simpl. auto with cgr. rewrite H. auto.
  - assert (pr_subst n (NewVar j (g g0_1)) (NewVar j p) = NewVar j (pr_subst n (g g0_1) p)).
    apply Hp. simpl. auto with arith.
    assert (pr_subst n (NewVar j (g g0_2)) (NewVar j p) = NewVar j (pr_subst n (g g0_2) p)).
    apply Hp. simpl. auto with arith.
    inversion H. inversion H0. auto.
Qed.

Lemma All_According_To_Data : forall k v d, (subst_Data k v (NewVar_in_Data k d) = d).
Proof.
intros. destruct d. 
- simpl. auto.
- simpl. destruct (decide (k < S n)). (* case decide. *)
  * simpl. destruct (decide (S n = k)) as [e | e].
    ** exfalso. dependent destruction l. eapply Nat.neq_succ_diag_l. exact e. 
       rewrite <-e in l. lia.
    ** destruct (decide (S n < k)). 
       *** lia.
       *** auto.
  * simpl. destruct (decide (n = k)).
    ** lia. 
    ** destruct n. 
      -- assert ( 0 < k). lia. destruct (decide (0 < k)). 
         *** auto. 
         *** exfalso. auto with arith.
      -- destruct (decide (S n < k)).
        *** auto.
        *** exfalso. lia.
Qed.

Lemma All_According : forall p k v, subst_in_proc k v (NewVar k p) = p.
Proof.
intros. revert v. revert k.
induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct p; intros. 
* simpl. assert (subst_in_proc k v (NewVar k p1) = p1) as eq1.
  { apply Hp. simpl. auto with arith. }
  assert (subst_in_proc k v (NewVar k p2) = p2) as eq2.
  { apply Hp. simpl. auto with arith. }
  rewrite eq1, eq2. auto.
* simpl. auto.
* simpl. assert (subst_in_proc k v (NewVar k p) = p).
  { apply Hp. simpl. auto with arith. }
  rewrite H. auto.
* simpl. assert (subst_Data k v (NewVar_in_Data k d) = d) as eq0.
  { apply All_According_To_Data. }
  assert (subst_in_proc (S k) (Succ_bvar v) (NewVar (S k) p1) = p1) as eq1.
  { apply Hp. simpl. auto with arith. }
  assert (subst_in_proc (S k) (Succ_bvar v) (NewVar (S k) p2) = p2) as eq2.
  { apply Hp. simpl. auto with arith. }
  rewrite eq0, eq1, eq2. auto.
* destruct g0.
  - simpl. auto.
  - simpl. auto.
  - simpl. assert (subst_in_proc (S k) (NewVar_in_Data 0 v) (NewVar (S k) p) = p) as eq.
    { apply Hp. simpl. auto with arith. }
    rewrite<- Succ_bvar_and_NewVar_in_Data_0. rewrite eq. auto.
  - simpl. assert (subst_Data k v (NewVar_in_Data k d) = d). apply All_According_To_Data.
    assert (subst_in_proc k v (NewVar k p) = p). apply Hp. simpl. auto with arith.
    rewrite H, H0. auto.
  - simpl. assert (subst_in_proc k v (NewVar k p) = p). apply Hp. simpl. auto with arith.
    rewrite H. auto.
  - simpl. assert (subst_in_proc k v (NewVar k (g g0_1)) = g g0_1) as eq1.
    { apply Hp. simpl. auto with arith. }
    assert (subst_in_proc k v (NewVar k (g g0_2)) = g g0_2) as eq2.
    { apply Hp. simpl. auto with arith. }
    dependent destruction eq1. dependent destruction eq2. rewrite x0, x. auto.
Qed.


Lemma PrSubst_NewVar2 : forall j n p q m, (subst_in_proc j (cst m) (pr_subst n p (NewVar j q))
              = pr_subst n (subst_in_proc j (cst m) p) q).
Proof.
intros. revert p j n q m. induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct p; intros.
* simpl. assert ((subst_in_proc j (cst m) (pr_subst n p1 (NewVar j q)) 
        = pr_subst n (subst_in_proc j (cst m) p1) q)) as eq1.
  { apply Hp. simpl. auto with arith. }
  assert (subst_in_proc j (cst m) (pr_subst n p2 (NewVar j q))
    = pr_subst n (subst_in_proc j (cst m) p2) q) as eq2.
  { apply Hp. simpl. auto with arith. }
  rewrite eq1, eq2. eauto.
* simpl. destruct (decide (n = n0)); simpl; auto.
  + rewrite decide_True;eauto. rewrite decide_True;eauto.
    rewrite (All_According q j (cst m)). eauto.
  + rewrite decide_False;eauto. rewrite decide_False;eauto.
* simpl. destruct (decide (n0 = n)); simpl ; auto.
  assert (subst_in_proc j (cst m) (pr_subst n0 p (NewVar j q)) = pr_subst n0 (subst_in_proc j (cst m) p) q) as eq.
  { apply Hp. simpl. auto with arith. }
  rewrite eq. auto.
* simpl.
  assert (subst_in_proc (S j) (cst m) (pr_subst n p1 (NewVar (S j) (NewVar 0 q))) =
      pr_subst n (subst_in_proc (S j) (cst m) p1) (NewVar 0 q)) as eq1.
  { apply Hp. simpl. auto with arith. }
  assert (subst_in_proc (S j) (cst m) (pr_subst n p2 (NewVar (S j) (NewVar 0 q))) =
      pr_subst n (subst_in_proc (S j) (cst m) p2) (NewVar 0 q)) as eq2.
  { apply Hp. simpl. auto with arith. }
  assert (0 + j = j)%nat as eq3 by lia.
  rewrite<- eq3. rewrite<- New_Var_And_NewVar.
  simpl in *. rewrite eq1, eq2. eauto.
* destruct g0; simpl; auto.
  - assert ((subst_in_proc (S j) (cst m) (pr_subst n p (NewVar (S j) (NewVar 0 q)))) =
          pr_subst n (subst_in_proc (S j) (cst m) p) (NewVar 0 q)) as eq1.
    { eapply Hp. eauto with arith. }
    assert ((0 + j) = j)%nat as eq2 by lia.
    rewrite<- eq2. rewrite<- New_Var_And_NewVar.
    simpl in *. rewrite eq1; eauto.
  - assert (subst_in_proc j (cst m) (pr_subst n p (NewVar j q)) =
        pr_subst n (subst_in_proc j (cst m) p) q) as eq.
    { apply Hp. simpl. auto with arith. }
    rewrite eq. auto.
  - assert (subst_in_proc j (cst m) (pr_subst n p (NewVar j q)) =
       pr_subst n (subst_in_proc j (cst m) p) q) as eq.
    { apply Hp. simpl. auto with cgr. }
    rewrite eq. auto.
  - simpl. assert (subst_in_proc j (cst m) (pr_subst n (g g0_1) (NewVar j q)) 
        = pr_subst n (subst_in_proc j (cst m) (g g0_1)) q) as eq1.
    { apply Hp. simpl. auto with arith. }
    assert (subst_in_proc j (cst m) (pr_subst n (g g0_2) (NewVar j q)) 
        = pr_subst n (subst_in_proc j (cst m) (g g0_2)) q) as eq2.
    { apply Hp. simpl. auto with arith. }
    dependent destruction eq1. dependent destruction eq2. rewrite x0, x. auto.
Qed.


(* ≡ respects the substitution of his variable*)
Lemma cgr_step_subst2 : forall p p' q x, p ≡ p' → pr_subst x p q ≡ pr_subst x p' q.
Proof.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros p' q n hcgr ; inversion hcgr; try auto; try (exact H).
  - constructor.
  - simpl. rewrite<- PrSubst_NewVar2. eapply cgr_match_zero_step.
  - simpl. rewrite<- PrSubst_NewVar2. eapply cgr_match_zero_rev_step.
  - simpl. rewrite<- PrSubst_NewVar2. eapply cgr_match_succ_step.
  - simpl. rewrite<- PrSubst_NewVar2. eapply cgr_match_succ_rev_step.
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
  - simpl. destruct (decide (n = x)). auto. constructor. apply Hp. subst. simpl. auto.  exact H.
  - simpl. constructor. apply Hp. subst. simpl. auto. exact H.
  - simpl. constructor. apply Hp. subst. simpl. auto. exact H. 
  - simpl. constructor. apply Hp. subst. simpl. auto. exact H. 
  - simpl. constructor. apply Hp. subst. simpl. rewrite <-Nat.add_succ_r. apply PeanoNat.Nat.lt_add_pos_r. apply Nat.lt_0_succ.
    exact H.
  - simpl. constructor. apply Hp. subst. simpl. rewrite <-Nat.add_succ_l. lia. exact H.
  - simpl. constructor. apply Hp. subst. simpl. rewrite <-Nat.add_succ_r. lia. exact H.
  - simpl. apply cgr_choice_step. 
    assert (pr_subst n (g p1) q ≡ pr_subst n (g q1) q). apply Hp. subst. simpl. rewrite <-Nat.add_succ_r. 
    apply PeanoNat.Nat.lt_add_pos_r. apply Nat.lt_0_succ.
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

(* State Transition System (STS-reduction) *)
Inductive sts : proc -> proc -> Prop :=
(*The axiomes*)
(* Communication of channels output and input that have the same name *)
| sts_com : forall {c v p1 g1 p2 g2}, (*Well_Defined_Input_in 0 (((c ! (cst v) • p1) + g1) ‖ ((c ? p2) + g2)) ->*)
    sts (((c ! v • p1) + g1) ‖ ((c ? p2) + g2)) (p1 ‖ (p2 ^ v))
(* Nothing more , something less *)
| sts_tau : forall {p g}, (* Well_Defined_Input_in 0 (((t • p) + g)) -> *)
    sts ((t • p) + g) p
(* Resursion *)
| sts_recursion : forall {x p}, (* Well_Defined_Input_in 0 (rec x • p) -> *)
    sts (rec x • p) (pr_subst x p (rec x • p))

(* The left parallele respect the Reduction *)
| sts_par : forall {p1 p2 q}, (* Well_Defined_Input_in 0 q ->*)
    sts p1 p2 ->
    sts (p1 ‖ q) (p2 ‖ q)

(*The Congruence respects the Reduction *)
| sts_cong : forall {p1 p2 q2 q1},
    p1 ≡* p2 -> sts p2 q2 -> q2 ≡* q1 -> sts p1 q1
.

#[global] Hint Constructors sts:ccs.


(* For the (STS-reduction), the reductible terms and reducted terms are pretty all the same, up to ≡* *)
Lemma ReductionShape : forall P Q, sts P Q ->
((exists c v P1 P2 G1 G2 S, ((P ≡* (((c ! v • P1) + G1) ‖ ((c ? P2) + G2)) ‖ S)) /\ (Q ≡*((P1 ‖ (P2^v)) ‖ S)))
\/ (exists P1 G1 S, (P ≡* (((t • P1) + G1) ‖ S)) /\ (Q ≡* (P1 ‖ S)))
\/ (exists n P1 S, (P ≡* ((rec n • P1) ‖ S)) /\ (Q ≡* (pr_subst n P1 (rec n • P1) ‖ S)))
).
Proof.
intros P Q Transition.
induction Transition.
  - left. exists c. exists v. exists p1. exists p2. exists g1. exists g2. exists (𝟘). split; apply cgr_par_nil_rev.
  - right. left. exists p. exists g0. exists 𝟘. split; apply cgr_par_nil_rev.
  - right. right. exists x. exists p. exists 𝟘. split; apply cgr_par_nil_rev.
  - destruct IHTransition as [IH|[IH|IH]];  decompose record IH. 
    * left. exists x. exists x0. exists x1. exists x2. exists x3. exists x4. exists (x5 ‖ q). split.
        ** apply transitivity with (((((x ! x0 • x1) + x3) ‖ ((x ? x2) + x4)) ‖ x5) ‖ q). apply cgr_par. auto. apply cgr_par_assoc.
        ** apply transitivity with (((x1 ‖ x2^x0) ‖ x5) ‖ q). apply cgr_par. auto.  apply cgr_par_assoc. 
    * right. left. exists x. exists x0. exists (x1 ‖ q). split.
        ** apply transitivity with (((t • x + x0) ‖ x1) ‖ q). apply cgr_par. auto. apply cgr_par_assoc.
        ** apply transitivity with (x ‖ (x1) ‖ q). apply cgr_par. auto. apply cgr_par_assoc.
    * right. right. exists x. exists x0. exists (x1 ‖ q). split. 
        ** apply transitivity with ((rec x • x0 ‖ x1) ‖ q). apply cgr_par. assumption. apply cgr_par_assoc.
        ** apply transitivity with ((pr_subst x x0 (rec x • x0) ‖ x1) ‖ q). apply cgr_par. assumption. apply cgr_par_assoc.
  - destruct IHTransition as [IH|[IH|IH]]; decompose record IH. 
    * left. exists x. exists x0. exists x1. exists x2. exists x3. exists x4. exists x5. split. apply cgr_trans with p2. exact H. exact H2.
      apply cgr_trans with q2. apply cgr_symm. exact H0. exact H3.
    * right. left. exists x. exists x0. exists x1. split. apply cgr_trans with p2. exact H. exact H2. apply cgr_trans with q2.
      apply cgr_symm. apply H0. apply H3.
    * right. right. exists x. exists x0. exists x1. split. apply cgr_trans with p2. exact H. exact H2. apply cgr_trans with q2.
      apply cgr_symm. apply H0. apply H3.
Qed.

(* For the (LTS-transition), the transitable terms and transitted terms, that performs a INPUT,
are pretty all the same, up to ≡* *)
Lemma TransitionShapeForInput : forall P Q c v, (lts P ((c ⋉ v) ?) Q) -> 
(exists P1 G R, ((P ≡* ((c ? P1 + G) ‖ R)) /\ (Q ≡* (P1^v ‖ R)) /\ ((exists L,P = (g L)) -> R = 𝟘))).
Proof.
intros P Q c v Transition.
 dependent induction Transition.
- exists P. exists 𝟘. exists 𝟘. split ; try split.
  * apply cgr_trans with ((c ? P) + 𝟘). apply cgr_trans with (c ? P). apply cgr_refl. apply cgr_choice_nil_rev. apply cgr_par_nil_rev.
  * apply cgr_par_nil_rev.
  * reflexivity.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists x0. exists x1. split; try split.
  * apply cgr_trans with (p^(cst 0)). apply cgr_match_zero. assumption.
  * assumption.
  * intros. inversion H2. inversion H4.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists x0. exists x1. split; try split.
  * apply cgr_trans with (q^(cst n')). apply cgr_match_succ. assumption.
  * assumption.
  * intros. inversion H2. inversion H4.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists x0. exists (x1 ‖ q). split; try split.
  * apply cgr_trans with ((((c ? x) + x0) ‖ x1) ‖ q). apply cgr_par. assumption. apply cgr_par_assoc.
  * apply cgr_trans with ((x^v ‖ x1) ‖ q). apply cgr_par. assumption. apply cgr_par_assoc.
  * intros. inversion H2. inversion H4.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists x0. exists (x1 ‖ p). split; try split.
  * apply cgr_trans with ((((c ? x) + x0) ‖ x1) ‖ p). apply cgr_trans with (q1 ‖ p). apply cgr_par_com. apply cgr_par. assumption. apply cgr_par_assoc.
  * apply cgr_trans with ((x^v ‖ x1) ‖ p). apply cgr_trans with (q2 ‖ p). apply cgr_par_com. apply cgr_par. assumption. apply cgr_par_assoc.
  * intros. inversion H2. inversion H4.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists (x0 + p2). exists 𝟘. split ; try split.
  * apply cgr_trans with ((c ? x) + (x0 + p2)). apply cgr_trans with (((c ? x) + x0) + p2).
    apply cgr_choice. assert (x1 = 𝟘). apply H3. exists p1. reflexivity. rewrite H2 in H0. apply transitivity with (((c ? x) + x0) ‖ 𝟘).
    assumption. apply cgr_par_nil. apply cgr_choice_assoc. apply cgr_par_nil_rev.
  * assert (x1 = 𝟘). apply H3. exists p1. reflexivity. rewrite H2 in H1. assumption.
  * reflexivity.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists (x0 + p1). exists 𝟘. split; try split.
  * apply cgr_trans with ((c ? x) + (x0 + p1)). apply cgr_trans with (((c ? x) + x0) + p1).
    apply cgr_trans with (p2 + p1). apply cgr_choice_com. apply cgr_choice. assert (x1 = 𝟘). apply H3. exists p2. reflexivity.
    apply cgr_trans with (((c ? x) + x0) ‖ x1). assumption. rewrite H2. apply cgr_par_nil. apply cgr_choice_assoc. apply cgr_par_nil_rev.
  * assert (x1 = 𝟘). apply H3. exists p2. reflexivity. rewrite <-H2. assumption. 
  * reflexivity.
Qed.

(* For the (LTS-transition), the transitable terms and transitted terms, that performs a OUPUT,
are pretty all the same, up to ≡* *)
Lemma TransitionShapeForOutput : forall P Q c v, (lts P ((c ⋉ v)!) Q) -> 
(exists P1 G R, ((P ≡* ((c ! v • P1 + G) ‖ R)) /\ (Q ≡* (P1 ‖ R)) /\ ((exists L,P = (g L)) -> R = 𝟘))).
Proof.
intros P Q c v Transition.
 dependent induction Transition.
- exists P. exists 𝟘. exists 𝟘. split ; try split.
  * apply cgr_trans with ((c ! v • P) + 𝟘). apply cgr_trans with (c ! v • P). apply cgr_refl. apply cgr_choice_nil_rev. apply cgr_par_nil_rev.
  * apply cgr_par_nil_rev.
  * reflexivity.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists x0. exists x1. split; try split.
  * apply cgr_trans with (p^(cst 0)). apply cgr_match_zero. assumption.
  * assumption.
  * intros. inversion H2. inversion H4.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists x0. exists x1. split; try split.
  * apply cgr_trans with (q^(cst n')). apply cgr_match_succ. assumption.
  * assumption.
  * intros. inversion H2. inversion H4.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists x0. exists (x1 ‖ q). split; try split.
  * apply cgr_trans with ((((c ! v • x) + x0) ‖ x1) ‖ q). apply cgr_par. assumption. apply cgr_par_assoc.
  * apply cgr_trans with ((x ‖ x1) ‖ q). apply cgr_par. assumption. apply cgr_par_assoc.
  * intros. inversion H2. inversion H4.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists x0. exists (x1 ‖ p). split; try split.
  * apply cgr_trans with ((((c ! v • x) + x0) ‖ x1) ‖ p). apply cgr_trans with (q1 ‖ p). apply cgr_par_com. apply cgr_par. assumption. apply cgr_par_assoc.
  * apply cgr_trans with ((x ‖ x1) ‖ p). apply cgr_trans with (q2 ‖ p). apply cgr_par_com. apply cgr_par. assumption. apply cgr_par_assoc.
  * intros. inversion H2. inversion H4.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists (x0 + p2). exists 𝟘. split ; try split.
  * apply cgr_trans with ((c ! v • x) + (x0 + p2)). apply cgr_trans with (((c ! v • x) + x0) + p2).
    apply cgr_choice. assert (x1 = 𝟘). apply H3. exists p1. reflexivity. rewrite H2 in H0. apply transitivity with (((c ! v • x) + x0) ‖ 𝟘).
    assumption. apply cgr_par_nil. apply cgr_choice_assoc. apply cgr_par_nil_rev.
  * assert (x1 = 𝟘). apply H3. exists p1. reflexivity. rewrite H2 in H1. assumption.
  * reflexivity.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists (x0 + p1). exists 𝟘. split; try split.
  * apply cgr_trans with ((c ! v • x) + (x0 + p1)). apply cgr_trans with (((c ! v • x) + x0) + p1).
    apply cgr_trans with (p2 + p1). apply cgr_choice_com. apply cgr_choice. assert (x1 = 𝟘). apply H3. exists p2. reflexivity.
    apply cgr_trans with (((c ! v • x) + x0) ‖ x1). assumption. rewrite H2. apply cgr_par_nil. apply cgr_choice_assoc. apply cgr_par_nil_rev.
  * assert (x1 = 𝟘). apply H3. exists p2. reflexivity. rewrite <-H2. assumption.
  * reflexivity.
Qed.

(* For the (LTS-transition), the transitable Guards and transitted terms, that performs a Tau ,
are pretty all the same, up to ≡* *)
Lemma TransitionShapeForTauAndGuard : forall P V, ((lts P τ V) /\ (exists L, P = (g L))) -> 
(exists Q M, ((P ≡* ((t • Q) + M))) /\ (V ≡* (Q))).
Proof.
intros P V Hyp. 
destruct Hyp. rename H into Transition. dependent induction Transition.
- inversion H0. inversion H.
- inversion H0. inversion H.
- exists P. exists 𝟘. split. 
  * apply cgr_choice_nil_rev.
  * apply cgr_refl.
- inversion H0. inversion H.
- inversion H0. inversion H.
- inversion H0. inversion H.
- inversion H0. inversion H.
- inversion H0. inversion H.
- edestruct IHTransition. reflexivity. exists p1. reflexivity. destruct H. destruct H.  exists x. 
  exists (x0 + p2). split. apply cgr_trans with (((t • x) + x0) + p2).
  apply cgr_choice. assumption.
  apply cgr_choice_assoc. assumption.
- edestruct IHTransition. reflexivity. exists p2. reflexivity. destruct H. destruct H.  exists x. 
  exists (x0 + p1). split. apply cgr_trans with (((t • x) + x0) + p1). apply cgr_trans with (p2 + p1). 
  apply cgr_choice_com. apply cgr_choice. assumption. apply cgr_choice_assoc. assumption.
Qed.

(* p 'is equivalent some r 'and r performs α to q *)
Definition sc_then_lts p α q := exists r, p ≡* r /\ (lts r α q).

(* p performs α to some r and this is equivalent to q*)
Definition lts_then_sc p α q := exists r, ((lts p α r) /\ r ≡* q).

(* Lemma supress_subst_action p μ p' n k: lts (subst_in_proc k (cst n) p) (ActExt μ)  p'
  -> exists p'' μ', p' = subst_in_proc k (cst n) p''
      /\ μ = subst_in_external_action k (cst n) μ'
      /\ lts p (ActExt μ') p''.
Proof.
  revert μ p' n k.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *; eauto.
  - inversion H; subst.
    + eapply Hp in H4 as (p'' & μ' & eq1 & eq2 & Tr); try lia.
      subst. exists (p'' ‖ p2). exists μ'. repeat split; simpl; eauto.
      eapply lts_parL; eauto.
    + eapply Hp in H4 as (p'' & μ' & eq1 & eq2 & Tr); try lia.
      subst. exists (p1 ‖ p''). exists μ'. repeat split; simpl; eauto.
      eapply lts_parR; eauto.
  - inversion H.
  - inversion H.
  - inversion H; subst.
    + admit.
    + admit. 
  - destruct g0; simpl in *.
    + inversion H.
    + inversion H.
    +  *)

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
    + intros. exists q0.  split. eapply lts_match_zero; eauto. reflexivity.
    + intros. dependent destruction l. exists p'. split; eauto. reflexivity.
    + intros. exists q0.  split. eapply lts_match_succ; eauto. reflexivity.
    + intros. dependent destruction l. exists q'. split; eauto. reflexivity.
    + intros. exists (q ‖ 𝟘). split. apply lts_parL. assumption. auto with cgr (*par contexte parallele*). 
    + intros. dependent destruction l. inversion l2. inversion l1. exists p2. split. exact l. auto with cgr. 
      inversion l.
    + intros. dependent destruction l.
      -- exists (q2 ‖ p2). split. eapply lts_comR. instantiate (1:= v). instantiate (1:= c). exact l1. exact l2. auto with cgr.
      -- exists (p2 ‖ q2). split. eapply lts_comL. instantiate (1:= v). instantiate (1:= c). exact l1. exact l2. auto with cgr.
      -- exists (p ‖ p2). split. apply lts_parR. assumption. auto with cgr.
      -- exists (q2 ‖ q). split. apply lts_parL. assumption. auto with cgr.
    + intros. dependent destruction l.
      -- dependent destruction l2. 
         * exists ((p2 ‖ p0) ‖ r). split.
           apply lts_parL. eapply lts_comL. instantiate (1:= v). instantiate (1:= c). assumption. assumption. auto with cgr.
         * exists ((p2 ‖ q) ‖ q2). split. eapply lts_comL. instantiate (1:= v). instantiate (1:= c). apply lts_parL. assumption. assumption.
           apply cgr_par_assoc.
      -- dependent destruction l1. 
         * exists ((q2 ‖ p2) ‖ r). split. apply lts_parL. eapply lts_comR. instantiate (1:= v). instantiate (1:= c). assumption.
           assumption. auto with cgr.
         * exists ((q2 ‖ q) ‖ q0). split. eapply lts_comR. instantiate (1:= v). instantiate (1:= c). assumption. apply lts_parL.
           assumption. auto with cgr.
      -- exists ((p2 ‖ q) ‖ r). split. apply lts_parL. apply lts_parL. assumption. auto with cgr.
      -- dependent destruction l.
         * exists ((p ‖ p2) ‖ q2). split. eapply lts_comL. instantiate (1:= v). instantiate (1:= c). apply lts_parR. assumption. assumption.
           auto with cgr.
         * exists ((p ‖ q2) ‖ p2). split. eapply lts_comR. instantiate (1:= v). instantiate (1:= c). assumption. apply lts_parR.
           assumption. auto with cgr.
         * exists ((p ‖ p2) ‖ r). split. apply lts_parL. apply lts_parR. assumption. auto with cgr.
         * exists ((p ‖ q) ‖ q2). split. apply lts_parR. assumption. auto with cgr.
    + intros. dependent destruction l.
      -- dependent destruction l1. 
         * exists (p2 ‖ (q ‖ q2)). split.
           eapply lts_comL. instantiate (1:= v). instantiate (1:= c). assumption. apply lts_parR. assumption. auto with cgr.
         * exists (p ‖ (q0 ‖ q2)). split. apply lts_parR. eapply lts_comL. instantiate (1:= v). instantiate (1:= c). assumption.
           assumption. auto with cgr.
      -- dependent destruction l2. 
         * exists (p0 ‖ (q ‖ p2)). split. eapply lts_comR. instantiate (1:= v). instantiate (1:= c). apply lts_parR. assumption.
           assumption. auto with cgr.
         * exists (p ‖ (q2 ‖ p2)). split. apply lts_parR.  eapply lts_comR. instantiate (1:= v). instantiate (1:= c). assumption.
           assumption. auto with cgr.
      -- dependent destruction l.
         * exists (p2 ‖ (q2 ‖ r)). split. eapply lts_comL. instantiate (1:= v). instantiate (1:= c).  assumption. apply lts_parL.
           assumption. auto with cgr.
         * exists (q2 ‖ (p2 ‖ r)). split. eapply lts_comR. instantiate (1:= v). instantiate (1:= c). apply lts_parL. assumption.
           assumption. auto with cgr.
         * exists (p2 ‖ ( q ‖ r)). split. apply lts_parL. assumption. auto with cgr.
         * exists (p ‖ (q2 ‖ r)). split. apply lts_parR. apply lts_parL. assumption. auto with cgr.
      -- exists (p ‖ (q ‖ q2)). split. apply lts_parR.  auto. apply lts_parR. assumption. auto with cgr.
    + intros. exists q.  split. apply lts_choiceL.  assumption. auto with cgr.
    + intros. dependent destruction l.
      -- exists q. split. assumption. auto with cgr.
      -- inversion l.
    + intros. dependent destruction l.
      -- exists q0. split. apply lts_choiceR. assumption. auto with cgr.
      -- exists q0. split. apply lts_choiceL. assumption. auto with cgr.
    + intros. dependent destruction l.
      -- exists q0. split. apply lts_choiceL. apply lts_choiceL. assumption. auto with cgr.
      -- dependent destruction l.
         * exists q0. split. apply lts_choiceL. apply lts_choiceR. assumption. auto with cgr.
         * exists q0. split. apply lts_choiceR. assumption. auto with cgr.
    + intros. dependent destruction l.
      -- dependent destruction l.
         * exists q0. split. apply lts_choiceL. assumption. auto with cgr.
         * exists q0. split. apply lts_choiceR. apply lts_choiceL. assumption. auto with cgr.
      -- exists q0. split. apply lts_choiceR. apply lts_choiceR. assumption. auto with cgr.
    + intros. dependent destruction l. exists (pr_subst x p (rec x • p)). split. apply lts_recursion. 
      apply cgr_subst. assumption.
    + intros. dependent destruction l. exists p.  split. apply lts_tau.
      constructor. assumption.
    + intros. dependent destruction l. exists (p^v). split. apply lts_input.
      apply Congruence_Respects_Substitution. constructor. apply H.
    + intros. dependent destruction l. exists p. split. apply lts_output. 
      constructor. assumption.
    + intros. dependent destruction l.
      -- destruct (IHcgr_step p2 ((c ⋉ v) ! )).  exact l1. destruct H0. exists (x ‖ q2).
          split. eapply lts_comL. exact H0. assumption.
          apply cgr_fullpar. assumption. reflexivity.
      -- destruct (IHcgr_step q2 ((c ⋉ v) ?)). assumption. destruct H0. exists (x ‖ p2).
          split.  eapply lts_comR. exact l1. assumption.
          apply cgr_fullpar. assumption. reflexivity.
      -- destruct (IHcgr_step p2 α). assumption. destruct H0. eexists.
          split. instantiate (1:= (x ‖ r)). apply lts_parL. assumption. apply cgr_fullpar.
          assumption. reflexivity.
      -- eexists. split. instantiate (1:= (p ‖ q2)). apply lts_parR.
          assumption. apply cgr_par.
          constructor. assumption.
    + intros. dependent destruction l.
      -- admit.
      -- admit.
    + intros. dependent destruction l.
      -- admit.
      -- admit.
      (* -- destruct (IHcgr_step p'0 α) as (p'1 & l' & equiv'). eauto.
         eexists. split. apply lts_ifOne; eauto. eauto.
      -- eexists. split. instantiate (1:= q'). apply lts_ifZero; eauto. reflexivity.  *)
    + intros. dependent destruction l. 
      -- destruct (IHcgr_step q α). assumption. destruct H0. exists x. split. apply lts_choiceL. assumption. assumption.
      -- eexists. instantiate (1:= q). split. apply lts_choiceR. assumption. reflexivity.
  - intros. destruct (IHhcgr2 q α). assumption. destruct (IHhcgr1 x0 α). destruct H. assumption. exists x1. split. destruct H0. assumption.
    destruct H. destruct H0. eauto with cgr.
Admitted.
*)
(*
(* One side of the Harmony Lemma *)
Lemma Reduction_Implies_TausAndCong : forall P Q, (sts P Q) -> (lts_then_sc P τ Q).
Proof. 
intros P Q Reduction. 
assert ((exists c v P1 P2 G1 G2 S, ((P ≡* (((c ! v • P1) + G1) ‖ ((c ? P2) + G2)) ‖ S)) /\ (Q ≡*((P1 ‖ (P2^v)) ‖ S)))
\/ (exists P1 G1 S, (P ≡* (((t • P1) + G1) ‖ S)) /\ (Q ≡* (P1 ‖ S)))
\/ (exists n P1 S, (P ≡* ((rec n • P1) ‖ S)) /\ (Q ≡* (pr_subst n P1 (rec n • P1) ‖ S)))
). 
apply ReductionShape. exact Reduction.
destruct H as [IH|[IH|IH]];  decompose record IH. 

(*First case τ by communication *)

- assert (lts (((x ! x0 • x1) + x3) ‖ ((x ? x2) + x4) ‖ x5) τ (x1 ‖ (x2^x0) ‖ x5)).
  * apply lts_parL.   
    eapply lts_comL. apply lts_choiceL. instantiate (2:= x). instantiate (1:= x0).
    apply lts_output. apply lts_choiceL. apply lts_input.
  * assert (sc_then_lts P τ ((x1 ‖ x2^x0) ‖ x5)). exists ((((x ! x0 • x1) + x3) ‖ ((x ? x2) + x4)) ‖ x5). split. assumption. assumption.
    assert (lts_then_sc P τ ((x1 ‖ x2^x0) ‖ x5)). apply Congruence_Respects_Transition. assumption. destruct H3. destruct H3.
    exists x6. split. assumption. apply transitivity with ((x1 ‖ x2^x0) ‖ x5). assumption. symmetry. assumption.

(*Second case τ by Tau Action *)

- assert (lts ((t • x + x0) ‖ x1) τ (x ‖ x1)). constructor.
  apply lts_choiceL. apply lts_tau.
  assert (sc_then_lts P τ (x ‖ x1)). exists ((t • x + x0) ‖ x1). split. assumption. apply lts_parL.
  apply lts_choiceL. apply lts_tau.
  assert (lts_then_sc P τ (x ‖ x1)). apply Congruence_Respects_Transition. assumption. destruct H3. destruct H3. 
  exists x2. split. assumption. apply transitivity with (x ‖ x1). assumption. symmetry. assumption.

(*Third case τ by recursion *)

- assert (lts (rec x • x0 ‖ x1) τ (pr_subst x x0 (rec x • x0) ‖ x1)). 
  constructor. apply lts_recursion. assert (sc_then_lts P τ ((pr_subst x x0 (rec x • x0) ‖ x1))). 
  exists (rec x • x0 ‖ x1). split. assumption. assumption. assert (lts_then_sc P τ (pr_subst x x0 (rec x • x0) ‖ x1)). 
  apply Congruence_Respects_Transition. assumption. destruct H3. destruct H3. 
  exists x2. split. assumption. apply transitivity with (pr_subst x x0 (rec x • x0) ‖ x1). assumption.
  symmetry. assumption.
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
  - eapply sts_cong.
    + eapply cgr_match_zero; eauto.
    + eauto.
    + reflexivity.
  - eapply sts_cong.
    + eapply cgr_match_succ; eauto.
    + eauto.
    + reflexivity.
  - eapply sts_cong.  instantiate (1:=  ((t • P) + 𝟘)). apply cgr_choice_nil_rev. instantiate (1:=P).
    apply sts_tau. constructor. constructor.
  - apply sts_recursion.
  - destruct (TransitionShapeForOutput p1 p2 c v). assumption.  decompose record H1.
    destruct (TransitionShapeForInput q1 q2 c v). assumption. decompose record H4.
    eapply sts_cong. instantiate (1:=(((c ! v • x) + x0) ‖ ((c ? x2) + x3)) ‖ (x1 ‖ x4)).
    apply cgr_trans with ((((c ! v • x) + x0) ‖ x1) ‖ (((c ? x2) + x3) ‖ x4)). apply cgr_fullpar. assumption. assumption.
    apply InversionParallele. 
    instantiate (1 := (x ‖ (x2^v)) ‖ (x1 ‖ x4)). apply sts_par.
    apply sts_com. 
    apply transitivity with ((x ‖ x1) ‖ ((x2^v) ‖ x4)). apply InversionParallele. apply cgr_fullpar. 
    symmetry. assumption. symmetry. assumption.
  - destruct (TransitionShapeForOutput p1 p2 c v). assumption. decompose record H1.
    destruct (TransitionShapeForInput q1 q2 c v). assumption. decompose record H4.
    eapply sts_cong. instantiate (1:=(((c ! v • x) + x0) ‖ ((c ? x2) + x3)) ‖ (x1 ‖ x4)).
    apply transitivity with (p1 ‖ q1). apply cgr_par_com.
    apply transitivity with ((((c ! v • x) + x0) ‖ x1) ‖ (((c ? x2) + x3) ‖ x4)).
    apply cgr_fullpar. assumption. assumption. apply InversionParallele. 
    instantiate (1 := (x ‖ (x2^v)) ‖ (x1 ‖ x4)). apply sts_par. apply sts_com.
    apply transitivity with ((x ‖ x1) ‖ ((x2^v) ‖ x4)). apply InversionParallele. apply transitivity with (p2 ‖ q2). apply cgr_fullpar. 
    symmetry. assumption. symmetry. assumption. apply cgr_par_com.
- apply sts_par. apply IHlts. reflexivity.
- eapply sts_cong. instantiate (1:= q1 ‖ p). apply cgr_par_com. instantiate (1:= q2 ‖ p).
  apply sts_par. apply IHlts. reflexivity. apply cgr_par_com.
- destruct (TransitionShapeForTauAndGuard (g p1) q). split. assumption. exists p1. reflexivity.
  decompose record H0.
  eapply sts_cong. instantiate (1:= ((t • x) + (x0 + p2))).
  apply transitivity with (g (((t • x) + x0) + p2)). apply cgr_choice. assumption. apply cgr_choice_assoc.
  instantiate (1:= x). apply sts_tau. symmetry. assumption.
- destruct (TransitionShapeForTauAndGuard (g p2) q). split. assumption. exists p2. reflexivity.
  decompose record H0. eapply sts_cong. instantiate (1:= ((t • x) + (x0 + p1))).
  apply transitivity with (g (((t • x) + x0 ) + p1)). apply transitivity with (g (p2 + p1)). apply cgr_choice_com.
  apply cgr_choice. assumption. apply cgr_choice_assoc. instantiate (1:= x). apply sts_tau.
  symmetry. assumption.
Qed.

(* One side of the Harmony Lemma*)
Lemma TausAndCong_Implies_Reduction: forall P Q, (lts_then_sc P τ Q) -> (sts P Q).
Proof.
intros P Q H.
apply Congruence_Simplicity with τ. exact Taus_Implies_Reduction. exact H.
Qed.

Theorem HarmonyLemmaForCCSWithValuePassing : forall P Q, (lts_then_sc P τ Q) <-> (sts P Q).
Proof.
intros. split.
* apply TausAndCong_Implies_Reduction.
* apply Reduction_Implies_TausAndCong.
Qed.

(* Definition for Well Abstracted bvariable *)
Inductive Well_Defined_Data : nat -> Data -> Prop :=
| bvar_is_defined_up_to_k: forall k x, (x < k) -> Well_Defined_Data k (bvar x)
| cst_is_always_defined : forall k x, Well_Defined_Data k (cst x).

(* Inductive Well_Defined_Condition : nat -> Equation Data -> Prop :=
| equationOnValueXX : forall k x y, Well_Defined_Data k x -> Well_Defined_Data k y -> Well_Defined_Condition k (x == y). *)

Inductive Well_Defined_Input_in : nat -> proc -> Prop :=
| WD_par : forall k p1 p2, Well_Defined_Input_in k p1 -> Well_Defined_Input_in k p2 
                -> Well_Defined_Input_in k (p1 ‖ p2)
| WD_var : forall k i, Well_Defined_Input_in k (pr_var i)
| WD_rec : forall k x p1, Well_Defined_Input_in k p1 -> Well_Defined_Input_in k (rec x • p1)
(* | WD_if_then_else : forall k p1 p2 C, Well_Defined_Condition k C -> Well_Defined_Input_in k p1 
                    -> Well_Defined_Input_in k p2 
                        -> Well_Defined_Input_in k (If C Then p1 Else p2) *)
| WD_match : forall k p1 p2 v, Well_Defined_Data k v -> Well_Defined_Input_in (S k) p1
                    -> Well_Defined_Input_in (S k) p2
                        -> Well_Defined_Input_in k (Match v With zero=> p1 succ=> p2)
| WD_success : forall k, Well_Defined_Input_in k (①)
| WD_nil : forall k, Well_Defined_Input_in k (𝟘)
| WD_input : forall k c p, Well_Defined_Input_in (S k) p
                  -> Well_Defined_Input_in k (c ? p)
| WD_output : forall k c v p, Well_Defined_Data k v 
                    -> Well_Defined_Input_in k p -> Well_Defined_Input_in k (c ! v • p)
| WD_tau : forall k p,  Well_Defined_Input_in k p -> Well_Defined_Input_in k (t • p)
| WD_choice : forall k p1 p2,  Well_Defined_Input_in k (g p1) ->  Well_Defined_Input_in k (g p2) 
              ->  Well_Defined_Input_in k (p1 + p2).

#[global] Hint Constructors Well_Defined_Input_in:ccs.

Lemma Inequation_k_data : forall k d, Well_Defined_Data k d -> Well_Defined_Data (S k) d.
Proof.
intros. dependent destruction d. constructor. dependent destruction H. constructor. auto with arith.
Qed.

(* Lemma Inequation_k_equation : forall k c, Well_Defined_Condition k c -> Well_Defined_Condition (S k) c.
Proof.
intros. dependent destruction c. destruct d; destruct d0.
- constructor; constructor.
- dependent destruction H. constructor. constructor. apply Inequation_k_data. assumption.
- dependent destruction H. constructor. apply Inequation_k_data. assumption. constructor. 
- dependent destruction H. constructor; apply Inequation_k_data; assumption.
Qed. *)

Lemma Inequation_k_proc : forall k p, Well_Defined_Input_in k p -> Well_Defined_Input_in (S k) p.
Proof.
intros. revert H. revert k.
induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct p.
- intros. dependent destruction H. constructor; apply Hp; simpl; auto with arith; assumption.
- intros. constructor.
- intros. constructor. apply Hp. simpl; auto with arith. dependent destruction H. assumption.
(* - intros. dependent destruction H. constructor. 
  ** apply Inequation_k_equation. assumption.
  ** apply Hp. simpl; auto with arith. assumption.
  ** apply Hp. simpl; auto with arith. assumption. *)
- intros. dependent destruction H. constructor. 
  ** apply Inequation_k_data. assumption.
  ** apply Hp. simpl; auto with arith. assumption.
  ** apply Hp. simpl; auto with arith. assumption.
- destruct g0.
  ** intros. constructor.
  ** intros. constructor.
  ** intros. constructor. apply Hp. simpl; auto with arith. dependent destruction H. assumption.
  ** intros. constructor. apply Inequation_k_data. dependent destruction H. assumption.
     apply Hp. simpl; auto with arith. dependent destruction H. assumption.
  ** intros. constructor. apply Hp. simpl; auto with arith. dependent destruction H. assumption.
  ** intros. dependent destruction H. constructor.
    -- apply Hp. simpl; auto with arith. assumption.
    -- apply Hp. simpl; auto with arith. assumption.
Qed.

(* False for the moment due to congruence on IF THEN ELSE *)
(* Lemma Congruence_step_Respects_WD_k : forall p q k, Well_Defined_Input_in k p -> p ≡ q -> Well_Defined_Input_in k q. 
Proof.
intros. revert H. revert k. dependent induction H0 ; intros.
* auto.
* dependent destruction H0; auto.
* constructor; eauto. dependent destruction H0; auto.
* dependent destruction H; auto.
* constructor; auto. constructor.
* dependent destruction H;constructor; auto.
* dependent destruction H. dependent destruction H. constructor. auto. constructor;auto.
* dependent destruction H. dependent destruction H0. constructor;auto. constructor; auto.
* dependent destruction H; auto.
* constructor; auto. constructor.
* dependent destruction H. constructor; auto. 
* dependent destruction H. dependent destruction H. constructor; auto. constructor; auto.
* dependent destruction H. dependent destruction H0. constructor; auto. constructor; auto.
* dependent destruction H. constructor. apply IHcgr_step. auto.
* dependent destruction H. constructor. apply IHcgr_step. auto.
* constructor. dependent destruction H. apply IHcgr_step. auto.
* dependent destruction H. constructor; auto.
* dependent destruction H. constructor; auto.
* dependent destruction H. constructor; auto.
* dependent destruction H. constructor; auto.
* dependent destruction H. constructor; auto.
Qed.

Lemma Congruence_Respects_WD_k : forall p q k, Well_Defined_Input_in k p -> p ≡* q -> Well_Defined_Input_in k q. 
Proof.
intros. dependent induction H0.
- apply Congruence_step_Respects_WD_k with x; auto.
- eauto.
Qed.

Lemma Congruence_Respects_WD : forall p q, Well_Defined_Input_in 0 p -> p ≡* q -> Well_Defined_Input_in 0 q.
Proof.
intros. eapply Congruence_Respects_WD_k; eauto.
Qed. *)

Lemma NotK : forall n k,  n < S k -> n ≠ k -> n < k.
Proof.
intros. assert (n ≤ k). auto with arith. destruct H1. exfalso. apply H0. reflexivity. auto with arith.
Qed.

Lemma ForData : forall k v d, Well_Defined_Data (S k) d -> Well_Defined_Data k (subst_Data k (cst v) d).
Proof.
intros. revert H. revert v. revert k. dependent induction d.
* intros. simpl. constructor.
* intros. simpl. destruct (decide (n = k )).
  - constructor. 
  - dependent destruction H.
    destruct (decide (n < k)). 
    -- constructor. assumption.
    -- constructor. apply NotK. apply transitivity with n. lia. (* pas top *) assumption. lia.
Qed.

(* Lemma ForEquation : forall k v e, Well_Defined_Condition (S k) e 
                -> Well_Defined_Condition k (subst_in_Equation k (cst v) e).
Proof.
intros. revert H. revert v. revert k. 
- dependent destruction e. dependent induction d; dependent induction d0.
  * intros. simpl. constructor; constructor.
  * intros. simpl. destruct (decide (n = k)).
    ** constructor; constructor.
    ** constructor. constructor. dependent destruction H. dependent destruction H0.
       destruct (decide(n < k)).
       --- constructor. assumption.
       --- constructor. lia.
  * intros. simpl. constructor; try constructor. destruct (decide (n = k)). constructor. dependent destruction H.
    dependent destruction H.
    destruct (decide(n < k)).
       --- constructor. assumption.
       --- constructor. lia. 
  * intros. simpl. constructor.
    ** destruct (decide (n = k)); try constructor. dependent destruction H. dependent destruction H. 
       destruct (decide(n < k)).
       --- constructor. assumption.
       --- constructor. lia. 
    ** destruct (decide (n0 = k)); try constructor. dependent destruction H. dependent destruction H0. 
       destruct (decide(n0 < k)).
       --- constructor. assumption.
       --- constructor. lia. 
Qed. *)

Lemma ForSTS : forall k p v, Well_Defined_Input_in (S k) p -> Well_Defined_Input_in k (subst_in_proc k (cst v) p).
Proof.
intros. revert v. revert H. revert k.
induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct p.
* intros. dependent destruction H. simpl. constructor. 
  - apply Hp. simpl. auto with arith. assumption.
  - apply Hp. simpl. auto with arith. assumption.
* intros. simpl. constructor.
* intros. simpl. dependent destruction H. constructor. apply Hp. simpl. auto with arith. assumption.
(* * intros. simpl. dependent destruction H. constructor.
  - apply ForEquation. assumption.
  - apply Hp. simpl. auto with arith. assumption.
  - apply Hp. simpl. auto with arith. assumption. *)
* intros. simpl. dependent destruction H. constructor.
  - apply ForData. assumption.
  - apply Hp. simpl. auto with arith. assumption.
  - apply Hp. simpl. auto with arith. assumption.
* destruct g0.
  - intros. simpl. constructor.
  - intros. simpl. constructor.
  - intros. simpl. constructor. apply Hp. simpl. auto. dependent destruction H. assumption.
  - intros. simpl. constructor.
    -- eapply ForData. dependent destruction H. assumption.
    -- apply Hp. simpl. auto. dependent destruction H. assumption.
  - intros. simpl. constructor. apply Hp. simpl. auto. dependent destruction H. assumption.
  - intros. simpl. dependent destruction H. constructor.
    -- assert (Well_Defined_Input_in k (subst_in_proc k v (g0_1))). apply Hp.
      simpl.  auto with arith. assumption. assumption.
    -- assert (Well_Defined_Input_in k (subst_in_proc k v (g0_2))). apply Hp.
      simpl.  auto with arith. assumption. assumption.
Qed.

Lemma WD_data_and_NewVar : forall d k i, Well_Defined_Data (k + i) d 
                          -> Well_Defined_Data (S (k + i)) (NewVar_in_Data i d).
Proof.
dependent induction d; intros.
- simpl. constructor.
- simpl. destruct (decide (i < S n)).
  * constructor. simpl. dependent destruction H. auto with arith.
  * constructor. dependent destruction H. apply transitivity with i.
    apply Nat.nlt_succ_r. assumption.
    auto with arith. 
Qed.

(* Lemma WD_eq_and_NewVar : forall e k i, Well_Defined_Condition (k + i) e 
                          -> Well_Defined_Condition (S (k + i)) (NewVar_in_Equation i e).
Proof.
intro. dependent induction e; intros; simpl. 
* dependent induction H. constructor. 
  - apply WD_data_and_NewVar. assumption.
  - apply WD_data_and_NewVar. assumption.
Qed. *)

Lemma WD_and_NewVar : forall k i p, Well_Defined_Input_in (k + i) p -> Well_Defined_Input_in ((S k) + i) (NewVar i p).
Proof.
intros. revert H. revert k i.
induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct p; intros; simpl.
* dependent destruction H. constructor.
   - apply Hp. simpl. auto with arith. assumption.
   - apply Hp. simpl. auto with arith. assumption.
* constructor.
* constructor. dependent destruction H. apply Hp. simpl. auto with arith. assumption.
(* * dependent destruction H. constructor. apply WD_eq_and_NewVar. assumption.
   - apply Hp. simpl. auto with arith. assumption.
   - apply Hp. simpl. auto with arith. assumption. *)
* dependent destruction H. constructor. apply WD_data_and_NewVar. assumption.
   - assert (S (S (k + i)) = (S k) + (S i))%nat as eq by lia.
     rewrite eq. apply Hp. simpl. auto with arith. 
     assert (S(k+i) = k + S i)%nat as eq' by lia.
     rewrite<- eq'. assumption.
   - assert (S (S (k + i)) = (S k) + (S i))%nat as eq by lia.
     rewrite eq. apply Hp. simpl. auto with arith. 
     assert (S(k+i) = k + S i)%nat as eq' by lia.
     rewrite<- eq'. assumption.
* destruct g0; intros; simpl.
  - constructor.
  - constructor.
  - dependent destruction H. constructor. 
    assert (S (S (k + i)) = (S k + S i)%nat). simpl. auto with arith.
    rewrite H0. apply Hp. simpl. auto with arith. assert ((k + S i)%nat = S (k + i)).  auto with arith. rewrite H1. assumption.
  - dependent destruction H. constructor. apply WD_data_and_NewVar. assumption.
    apply Hp. simpl. auto with arith. assumption.
  - constructor. apply Hp. simpl. auto. dependent destruction H. assumption.
  - dependent destruction H. constructor.
    -- assert (S (k + i) = (S k + i)%nat). auto with arith. rewrite H1.
       assert (Well_Defined_Input_in (S k + i) (NewVar i (g g0_1))).
       apply Hp. simpl. auto with arith. assumption. assumption.
    -- assert (S (k + i) = (S k + i)%nat). auto with arith. rewrite H1.
       assert (Well_Defined_Input_in (S k + i) (NewVar i (g g0_2))).
       apply Hp. simpl. auto with arith. assumption. assumption.
Qed.


Lemma ForRecursionSanity : forall p' p x k, Well_Defined_Input_in k p' -> Well_Defined_Input_in k p 
            -> Well_Defined_Input_in k (pr_subst x p' p).
Proof.
intros. revert H. revert H0. revert k. revert x. revert p.
induction p' as (p' & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct p'.
* intros. simpl. constructor. 
  ** apply Hp. simpl. auto with arith. assumption. dependent destruction H. assumption.
  ** apply Hp. simpl. auto with arith. assumption. dependent destruction H. assumption.
* intros. simpl. destruct (decide (x = n)). assumption. assumption.
* intros. simpl. destruct (decide (x=n)). 
  ** dependent destruction H. assumption.
  ** constructor. apply Hp. simpl; auto with arith. assumption. dependent destruction H. assumption.
* intros. simpl. dependent destruction H. constructor. 
    - simpl;auto with arith.
    - apply Hp. simpl; lia. assert ((S k) = ((S k) + 0)%nat). auto with arith. 
      rewrite H3. apply (WD_and_NewVar k 0 p).
      assert (k = (k + 0)%nat). auto with arith. rewrite <-H4. assumption. eauto.
    - apply Hp. simpl; lia. assert ((S k) = ((S k) + 0)%nat). auto with arith. 
      rewrite H3. apply (WD_and_NewVar k 0 p).
      assert (k = (k + 0)%nat). auto with arith. rewrite <-H4. assumption. eauto.
* destruct g0. 
  ** intros. simpl. constructor.
  ** intros. simpl. constructor.
  ** intros. simpl. constructor. dependent destruction H. apply Hp. 
    - simpl;auto with arith.
    - assert ((S k) = ((S k) + 0)%nat). auto with arith. rewrite H1. apply (WD_and_NewVar k 0 p0).
      assert (k = (k + 0)%nat). auto with arith. rewrite <-H2. assumption.
    - assumption.
  ** intros. simpl. constructor. dependent destruction H. assumption. apply Hp.
    - simpl; auto with arith.
    - assumption.
    - dependent destruction H. assumption.
  ** intros. simpl. constructor. apply Hp.
    - simpl; auto with arith.
    - assumption.
    - dependent destruction H. assumption.
  ** intros. simpl. dependent destruction H. constructor.
    - assert (Well_Defined_Input_in k (pr_subst x (g g0_1) p)). apply Hp. simpl; auto with arith. assumption.
      assumption. assumption.
    - assert (Well_Defined_Input_in k (pr_subst x (g g0_2) p)). apply Hp. simpl; auto with arith. assumption.
      assumption. assumption.
Qed.

Lemma RecursionOverReduction_is_WD : forall k x p, Well_Defined_Input_in k (rec x • p) -> Well_Defined_Input_in k (pr_subst x p (rec x • p)).
Proof.
intros. apply ForRecursionSanity. dependent destruction H. assumption. assumption.
Qed.

Lemma Well_Def_Data_Is_a_value : forall d, Well_Defined_Data 0 d <-> exists v, d = cst v.
Proof.
intros. split. 
- intro. dependent destruction H. exfalso. dependent induction H. exists x. reflexivity.
- intros. destruct H. subst. constructor.
Qed.

(* Lemma STS_Respects_WD : forall p q, Well_Defined_Input_in 0 p -> sts p q -> Well_Defined_Input_in 0 q.
Proof.
intros. revert H. rename H0 into Reduction. dependent induction Reduction.
* intros. constructor.
  - dependent destruction H. dependent destruction H. dependent destruction H. assumption.
  - dependent destruction H. dependent destruction H0. dependent destruction H0_. apply ForSTS. assumption. 
* intros. dependent destruction H. dependent destruction H. assumption.
* intros. dependent destruction H. apply RecursionOverReduction_is_WD. constructor. assumption.
* intros. dependent destruction H0. assumption.
* intros. dependent destruction H0. assumption.
* intros. dependent destruction H. constructor. apply IHReduction. assumption. assumption.
* intros. apply Congruence_Respects_WD with q2. apply IHReduction. apply Congruence_Respects_WD with p1. 
  assumption. assumption. assumption.
Qed. *)

Inductive Well_Defined_Action: (ActIO TypeOfActions) -> Prop :=
| ActionOuput_with_value_is_always_defined : forall c v, Well_Defined_Action ((c ⋉ (cst v))!)
| ActionInput_with_value_is_always_defined : forall c v, Well_Defined_Action ((c ⋉ (cst v))?)
| Tau_is_always_defined : Well_Defined_Action τ.

Inductive Well_Defined_ExtAction: (ExtAct TypeOfActions) -> Prop :=
| ExtActionOuput_with_value_is_always_defined : forall c v, Well_Defined_ExtAction (ActOut (c ⋉ (cst v)))
| ExtActionInput_with_value_is_always_defined : forall c v, Well_Defined_ExtAction (ActIn (c ⋉ (cst v))).

Lemma Output_are_good : forall p1 p2 c d, Well_Defined_Input_in 0 p1 -> lts p1 ((c ⋉ d) !) p2 
      -> exists v, d = cst v.
Proof.
intros. dependent induction H0. dependent destruction H. eapply Well_Def_Data_Is_a_value in H. destruct H.
subst. exists x. reflexivity.
- dependent destruction H. eapply IHlts with c. eapply ForSTS; eauto. reflexivity.
- dependent destruction H. eapply IHlts with c. eapply ForSTS; eauto. reflexivity.
- dependent destruction H. eapply IHlts with c. assumption. reflexivity.
- dependent destruction H. eapply IHlts with c. assumption. reflexivity.
- dependent destruction H. eapply IHlts with c. assumption. reflexivity.
- dependent destruction H. eapply IHlts with c. assumption. reflexivity.
Qed.

Lemma LTS_Respects_WD : forall p q α, Well_Defined_Input_in 0 p -> Well_Defined_Action α -> 
        lts p α q ->  Well_Defined_Input_in 0 q.
Proof.
intros. revert H. revert H0. rename H1 into Transition. dependent induction Transition.
* intros. dependent destruction H0. apply ForSTS. dependent destruction H. assumption.
* intros. dependent destruction H. assumption.
* intros. inversion H; subst. eapply IHTransition; eauto. eapply ForSTS; eauto.
* intros. inversion H; subst. eapply IHTransition; eauto. eapply ForSTS; eauto.
* intros. dependent destruction H. assumption.
* intros. apply ForRecursionSanity. dependent destruction H. assumption. assumption.
* intros. dependent destruction H. constructor. 
  ** apply IHTransition1. assert (exists v', v = cst v'). eapply Output_are_good. exact H.
     exact Transition1. destruct H2. subst. constructor. assumption.
  ** apply IHTransition2. assert (exists v', v = cst v'). eapply Output_are_good. exact H.
     exact Transition1. destruct H2. subst. constructor. assumption.
* intros. dependent destruction H. constructor.
  ** apply IHTransition2. assert (exists v', v = cst v'). eapply Output_are_good. exact H1.
     exact Transition1. destruct H2. subst. constructor. assumption.
  ** apply IHTransition1. assert (exists v', v = cst v'). eapply Output_are_good. exact H1.
     exact Transition1. destruct H2. subst. constructor. assumption.
* intros. dependent destruction H. constructor. apply IHTransition. assumption. assumption. assumption.
* intros. dependent destruction H. constructor. assumption. apply IHTransition. assumption. assumption.
* intros. dependent destruction H. apply IHTransition. assumption. assumption.
* intros. dependent destruction H. apply IHTransition. assumption. assumption.
Qed.

Definition encode_data (D : Data) : gen_tree (nat + Value) :=
match D with
  | cst v => GenLeaf (inr v)
  | bvar i => GenLeaf (inl i)
end.

Definition decode_data (tree : gen_tree (nat + Value)) : Data :=
match tree with
  | GenLeaf (inr v) => cst v
  | GenLeaf (inl i) => bvar i
  | _ => bvar 0
end.

Lemma encode_decide_datas d : decode_data (encode_data d) = d.
Proof. case d. 
* intros. simpl. reflexivity.
* intros. simpl. reflexivity.
Qed.

#[global] Instance data_countable : Countable Data.
Proof.
  refine (inj_countable' encode_data decode_data _).
  apply encode_decide_datas.
Qed.

Lemma TypeOfActions_dec : forall (x y : TypeOfActions) , {x = y} + {x <> y}.
Proof.
decide equality. 
* destruct (decide(d = d0)). left. assumption. right. assumption.
* destruct (decide (c = c0)). left. assumption. right. assumption.
Qed.

#[global] Instance TypeOfActions_eqdecision : EqDecision TypeOfActions. by exact TypeOfActions_dec . Defined.


Definition encode_TypeOfActions (a : TypeOfActions) : gen_tree (nat + (Channel + Data)) :=
match a with
  | act c v => GenNode 0 [GenLeaf (inr (inl c)) ; GenLeaf (inr (inr v))]
end.

Definition decode_TypeOfActions (tree :gen_tree (nat + (Channel + Data))) : option TypeOfActions :=
match tree with
  | GenNode 0 [GenLeaf (inr (inl c)); GenLeaf (inr (inr v))] => Some (act c v)
  | _ => None
end.

Lemma encode_decide_TypeOfActions p : decode_TypeOfActions (encode_TypeOfActions  p) = Some p.
Proof. 
induction p. 
* simpl. reflexivity.
Qed.

#[global] Instance TypeOfActions_countable : Countable TypeOfActions.
Proof.
  eapply inj_countable with encode_TypeOfActions decode_TypeOfActions. 
  intro. apply encode_decide_TypeOfActions.
Qed.

Definition encode_ExtAct_TypeOfActions (a : ExtAct TypeOfActions) : 
    gen_tree (nat + (Channel + Data)) :=
match a with
  | ActIn a => GenNode 0 [encode_TypeOfActions a]
  | ActOut a => GenNode 1 [encode_TypeOfActions a]
end.

Definition decode_ExtAct_TypeOfActions_raw (tree :gen_tree (nat + (Channel + Data))) 
  : option (ExtAct (option TypeOfActions)) :=
match tree with
  | GenNode 0 [l] => Some (ActIn (decode_TypeOfActions l))
  | GenNode 1 [l] => Some (ActOut (decode_TypeOfActions l))
  | _ => None
end.

Definition simpl_option (a : option (ExtAct (option TypeOfActions)))
  : option (ExtAct TypeOfActions) :=
match a with
  | Some (ActIn None) => None
  | Some (ActIn (Some b)) => Some (ActIn b)
  | Some (ActOut None) => None
  | Some (ActOut (Some b)) => Some (ActOut b)
  | None => None
end.

Definition decode_ExtAct_TypeOfActions (tree :gen_tree (nat + (Channel + Data))) 
  : option (ExtAct TypeOfActions) := simpl_option (decode_ExtAct_TypeOfActions_raw tree).

Lemma encode_decide_ExtAct_TypeOfActions a : 
  decode_ExtAct_TypeOfActions (encode_ExtAct_TypeOfActions  a) = Some a.
Proof. 
induction a. 
* unfold decode_ExtAct_TypeOfActions. simpl.
  rewrite encode_decide_TypeOfActions. eauto.
* unfold decode_ExtAct_TypeOfActions. simpl.
  rewrite encode_decide_TypeOfActions. eauto.
Qed.


#[global] Instance ExtAct_TypeOfActions_countable : Countable (ExtAct TypeOfActions).
Proof.
  eapply inj_countable with encode_ExtAct_TypeOfActions decode_ExtAct_TypeOfActions. 
  intro. apply encode_decide_ExtAct_TypeOfActions.
Qed.


(* Lemma Equation_dec : forall (x y : Equation Data) , {x = y} + {x <> y}.
Proof.
decide equality. apply Data_dec. apply Data_dec.
Qed.

#[global] Instance equation_dec : EqDecision (Equation Data). exact Equation_dec. Defined.

Definition encode_equation (E : Equation Data) : gen_tree (nat + Data) :=
match E with
  | D1 == D2 => GenNode 0 [GenLeaf (inr D1) ; GenLeaf (inr D2)]
end.

Definition decode_equation (tree : gen_tree (nat + Data)) : option (Equation Data) :=
match tree with
  | GenNode 0 [GenLeaf (inr d); GenLeaf (inr d')] => Some (d == d')
  | _ => None
end. 


Lemma encode_decide_equations p : decode_equation (encode_equation p) = Some p.
Proof. 
induction p.
* simpl. reflexivity.
Qed.

#[global] Instance equation_countable : Countable (Equation Data).
Proof.
  refine (inj_countable encode_equation decode_equation _).
  apply encode_decide_equations.
Qed.*)

Fixpoint proc_dec (x y : proc) : { x = y } + { x <> y }
with gproc_dec (x y : gproc) : { x = y } + { x <> y }.
Proof.
decide equality. 
* destruct (decide(n = n0));eauto.
* destruct (decide(n = n0));eauto.
* destruct (decide(d = d0));eauto. 
* decide equality; destruct (decide(c = c0));eauto.
  destruct (decide(d = d0));eauto.
Qed.

#[global] Instance proc_eqdecision : EqDecision proc. by exact proc_dec. Defined.


(* Fixpoint encode_proc (p: proc) : gen_tree (nat + (((Equation Data ) + TypeOfActions) + Channel)) :=
  match p with
  | p ‖ q  => GenNode 0 [encode_proc p; encode_proc q]
  | pr_var i => GenNode 2 [GenLeaf $ inl i]
  | rec x • P => GenNode 3 [GenLeaf $ inl x; encode_proc P]
  | If C Then A Else B => GenNode 4 [GenLeaf (inr ( inl (inl C))) ; encode_proc A; encode_proc B]
  | g gp => GenNode 1 [encode_gproc gp]
  end
with
encode_gproc (gp: gproc) : gen_tree (nat + (((Equation Data ) + TypeOfActions) + Channel)) :=
  match gp with
  | ① => GenNode 1 []
  | 𝟘 => GenNode 0 []
  | c ? p => GenNode 2 [GenLeaf (inr $ inr c); encode_proc p]
  | c ! v • p  => GenNode 5 [GenLeaf (inr $ inl $ inr $ (c ⋉ v)); encode_proc p]
  | t • p => GenNode 3 [encode_proc p]
  | gp + gq => GenNode 4 [encode_gproc gp; encode_gproc gq]
  end. *)

Fixpoint encode_proc (p: proc) : gen_tree (nat + ((Data + TypeOfActions) + Channel)) :=
  match p with
  | p ‖ q  => GenNode 0 [encode_proc p; encode_proc q]
  | pr_var i => GenNode 2 [GenLeaf $ inl i]
  | rec x • P => GenNode 3 [GenLeaf $ inl x; encode_proc P]
  | Match n With zero=> A succ=> B => GenNode 4 [GenLeaf (inr ( inl (inl n))) ; encode_proc A; encode_proc B]
  | g gp => GenNode 1 [encode_gproc gp]
  end
with
encode_gproc (gp: gproc) : gen_tree (nat + ((Data + TypeOfActions) + Channel)) :=
  match gp with
  | ① => GenNode 1 []
  | 𝟘 => GenNode 0 []
  | c ? p => GenNode 2 [GenLeaf (inr $ inr c); encode_proc p]
  | c ! v • p  => GenNode 5 [GenLeaf (inr $ inl $ inr $ (c ⋉ v)); encode_proc p]
  | t • p => GenNode 3 [encode_proc p]
  | gp + gq => GenNode 4 [encode_gproc gp; encode_gproc gq]
  end.

Definition Channel_of (a : TypeOfActions) : Channel := 
match a with 
| act c d => c
end.

Definition Data_of (a : TypeOfActions) : Data := 
match a with 
| act c d => d
end.

(* Fixpoint decode_proc (t': gen_tree (nat + (((Equation Data ) + TypeOfActions) + Channel))) : proc :=
  match t' with
  | GenNode 0 [ep; eq] => (decode_proc ep) ‖ (decode_proc eq)
  | GenNode 2 [GenLeaf (inl i)] => pr_var i
  | GenNode 3 [GenLeaf (inl i); egq] => rec i • (decode_proc egq)
  | GenNode 4 [GenLeaf (inr ( inl (inl C))); A; B] => If C Then (decode_proc A) Else (decode_proc B)
  | GenNode 1 [egp] => g (decode_gproc egp)
  | _ => ① 
  end
with
decode_gproc (t': gen_tree (nat + (((Equation Data ) + TypeOfActions) + Channel))): gproc :=
  match t' with
  | GenNode 1 [] => ①
  | GenNode 0 [] => 𝟘
  | GenNode 2 [GenLeaf (inr (inr c)); ep] => c ? (decode_proc ep)
  | GenNode 5 [GenLeaf (inr ( inl (inr a))) ; ep] => (Channel_of a) ! (Data_of a) • (decode_proc ep)
  | GenNode 3 [eq] => t • (decode_proc eq)
  | GenNode 4 [egp; egq] => (decode_gproc egp) + (decode_gproc egq)
  | _ => ① 
  end.
 *)

Fixpoint decode_proc (t': gen_tree (nat + ((Data + TypeOfActions) + Channel))) : proc :=
  match t' with
  | GenNode 0 [ep; eq] => (decode_proc ep) ‖ (decode_proc eq)
  | GenNode 2 [GenLeaf (inl i)] => pr_var i
  | GenNode 3 [GenLeaf (inl i); egq] => rec i • (decode_proc egq)
  | GenNode 4 [GenLeaf (inr ( inl (inl n))); A; B] => Match n With zero=> (decode_proc A) succ=> (decode_proc B)
  | GenNode 1 [egp] => g (decode_gproc egp)
  | _ => ① 
  end
with
decode_gproc (t': gen_tree (nat + ((Data + TypeOfActions) + Channel))): gproc :=
  match t' with
  | GenNode 1 [] => ①
  | GenNode 0 [] => 𝟘
  | GenNode 2 [GenLeaf (inr (inr c)); ep] => c ? (decode_proc ep)
  | GenNode 5 [GenLeaf (inr ( inl (inr a))) ; ep] => (Channel_of a) ! (Data_of a) • (decode_proc ep)
  | GenNode 3 [eq] => t • (decode_proc eq)
  | GenNode 4 [egp; egq] => (decode_gproc egp) + (decode_gproc egq)
  | _ => ① 
  end.

Lemma encode_decide_procs p : decode_proc (encode_proc p) = p
with encode_decide_gprocs p : decode_gproc (encode_gproc p) = p.
Proof. all: case p. 
* intros. simpl. rewrite (encode_decide_procs p0). rewrite (encode_decide_procs p1). reflexivity.
* intros. simpl. reflexivity.
* intros. simpl. rewrite (encode_decide_procs p0). reflexivity.
* intros. simpl. rewrite (encode_decide_procs p0). rewrite (encode_decide_procs p1). reflexivity.
* intros. simpl. rewrite (encode_decide_gprocs g0). reflexivity.
* intros. simpl. reflexivity. 
* intros. simpl. reflexivity. 
* intros. simpl. rewrite (encode_decide_procs p0). reflexivity.
* intros. simpl. rewrite (encode_decide_procs p0). reflexivity.
* intros. simpl. rewrite (encode_decide_procs p0). reflexivity.
* intros. simpl. rewrite (encode_decide_gprocs g0). rewrite (encode_decide_gprocs g1). reflexivity.
Qed.

#[global] Instance proc_count : Countable proc.
refine (inj_countable' encode_proc decode_proc _).
  apply encode_decide_procs.
Qed.

Definition subst_TypeOfActions (k : nat) (X : Data) (a : TypeOfActions) : TypeOfActions := 
  (Channel_of a ⋉ (subst_Data k X (Data_of a))).

Fixpoint moutputs_of_g (gp : gproc) : gmultiset (TypeOfActions) :=
  match gp with
  | ① => ∅
  | 𝟘 => ∅
  | c ? p => ∅
  | c ! v • p => {[+ (c ⋉ v) +]}
  | t • p => ∅
  | g1 + g2 => moutputs_of_g g1 ⊎ moutputs_of_g g2
  end.

Fixpoint moutputs_of p : gmultiset TypeOfActions := 
match p with
  | P ‖ Q => (moutputs_of P) ⊎ (moutputs_of Q)
  | pr_var _ => ∅
  | rec _ • _ => ∅
(*   | If E Then P Else => Q => match (Eval_Eq E) with 
                                        | Some true => moutputs_of P
                                        | Some false => moutputs_of Q
                                        | None => ∅
                                      end *)
  | Match (cst 0) With zero=> P succ=> Q => gmultiset_map (fun a => subst_TypeOfActions 0 (cst 0) a) (moutputs_of P)
  | Match (cst (S n)) With zero=> P succ=> Q => gmultiset_map (fun a => subst_TypeOfActions 0 (cst n) a) (moutputs_of P)
  | Match (bvar i) With zero=> P succ=> Q => ∅
  | g p => moutputs_of_g p
end.

Lemma eq_gmo_gmultiset p m (* k *) :
moutputs_of_g (subst_in_gproc 0 (cst m) p) = gmultiset_map (fun a => subst_TypeOfActions 0 (cst m) a) (moutputs_of_g p).
Proof.
  dependent induction p; simpl in * ;eauto.
  + rewrite gmultiset_map_singleton. unfold subst_TypeOfActions. simpl. eauto.
  + rewrite IHp1. rewrite IHp2. rewrite gmultiset_map_disj_union. eauto.
Qed.

(* Lemma eq_mo_gmultiset p m (* k *) :
moutputs_of (subst_in_proc 0 (cst m) p) = gmultiset_map (fun a => subst_TypeOfActions 0 (cst m) a) (moutputs_of p).
Proof.
  dependent induction p; simpl in * ;eauto.
  + rewrite gmultiset_map_disj_union.
    rewrite (IHp1 m (* k *) ). rewrite (IHp2 m (* k *) ). eauto.
  + destruct d.
    ++ destruct v.
       +++ simpl. 
  + eapply eq_gmo_gmultiset.
Admitted. *)

Definition outputs_of p := dom (moutputs_of p).

Lemma mo_equiv_spec_step : forall {p q}, p ≡ q -> moutputs_of p = moutputs_of q.
Proof. intros. dependent induction H; try multiset_solver; simpl in *.
+ rewrite eq_mo_gmultiset. eauto.
+ rewrite eq_mo_gmultiset. eauto.
+ rewrite eq_mo_gmultiset. eauto. admit.
+ rewrite eq_mo_gmultiset. eauto. admit.
+ rewrite IHcgr_step. eauto.
Admitted.

Lemma mo_equiv_spec : forall {p q}, p ≡* q -> moutputs_of p = moutputs_of q.
Proof.
  intros p q hcgr.
  induction hcgr. now eapply mo_equiv_spec_step.
  etrans; eauto.
Qed.

Lemma mo_spec_l e a :
  a ∈ moutputs_of e -> {e' | lts e (ActExt $ ActOut a) e'}.
Proof.
  intros mem.
  dependent induction e.
  + cbn in mem.
    destruct (decide (a ∈ moutputs_of e1)) as [mem_left | not_mem_left].
    ++ destruct (IHe1 a) as (e1' & lts__e1); eauto.
       exists (e1' ‖ e2). repeat split; eauto with ccs.
    ++ destruct (decide (a ∈ moutputs_of e2)) as [mem_right | not_mem_right].
       +++ destruct (IHe2 a) as (e2' & lts__e2); eauto.
           exists (e1 ‖ e2'). repeat split; eauto with ccs.
       +++ exfalso. multiset_solver.
    + exfalso. multiset_solver.
    + exfalso. multiset_solver.
    + simpl in mem. case_eq d. 
      ++ intros. destruct v; subst.
         +++ (* rewrite<- eq_mo_gmultiset in mem. 
             eapply IHe1 in mem as (e' & l').
             exists e'. econstructor; eauto. *) admit.
         +++ (* rewrite H in mem. 
             eapply IHe2 in mem as (e' & l').
             exists e'. eapply lts_ifZero; eauto. *) admit.
      ++ intros. subst. exfalso. inversion mem.
    + unfold moutputs_of in mem.
      remember g0.
      dependent induction g0; rewrite Heqg1 in mem; simpl in *.
      ++ exfalso;inversion mem.
      ++ exfalso;inversion mem.
      ++ exfalso;inversion mem.
      ++ subst. assert (a = c ⋉ d). multiset_solver. subst. eauto with ccs.
      ++ exfalso;inversion mem.
      ++ destruct (decide (a ∈ moutputs_of g0_2)) as [mem_right | not_mem_right].
         +++ destruct (IHg0_2 a g0_2) as (e2' & lts__e2); eauto.
             exists e2'. rewrite Heqg1. repeat split; eauto with ccs.
         +++ destruct (decide (a ∈ moutputs_of g0_1)) as [mem_left | not_mem_left].
             ++++ destruct (IHg0_1 a g0_1) as (e1' & lts__e1); eauto.
                  exists e1'. rewrite Heqg1. repeat split; eauto with ccs.
             ++++ exfalso. multiset_solver.
Admitted.

Lemma mo_spec_r p a :
  {p' | lts p (ActExt $ ActOut a) p'} -> a ∈ moutputs_of p.
Proof.
    induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros (e' & l).
  inversion l; subst.
  + simpl. multiset_solver.
  + simpl in *. rewrite<- eq_mo_gmultiset. eapply Hp; eauto. admit.
  + simpl in *. rewrite<- eq_mo_gmultiset. eapply Hp; eauto. admit. admit.
  + simpl. eapply gmultiset_elem_of_disj_union. left.
    eapply (Hp p1). simpl. lia. exists p2. eauto.
  + simpl. eapply gmultiset_elem_of_disj_union. right.
    eapply (Hp q1). simpl. lia. exists q2. eauto.
  + simpl. eapply gmultiset_elem_of_disj_union. left.
    eapply (Hp p1). simpl. lia. exists e'. eauto.
  + simpl. eapply gmultiset_elem_of_disj_union. right.
    eapply (Hp p2). simpl. lia. exists e'. eauto.
Admitted.


Lemma outputs_of_spec2 p a : a ∈ outputs_of p -> {q | lts p (ActExt (ActOut a)) q}.
Proof.
  intros mem.
  eapply gmultiset_elem_of_dom in mem.
  eapply mo_spec_l in mem.
  firstorder.
Qed.

Lemma outputs_of_spec1 (p : proc) (a : TypeOfActions) (q : proc) : lts p (ActExt (ActOut a)) q
      -> a ∈ outputs_of p.
Proof.
intros. eapply gmultiset_elem_of_dom. eapply mo_spec_r. eauto.
Qed.


Fixpoint lts_set_output_g (g : gproc) (a : TypeOfActions) : gset proc :=
  match g with
  | ① => ∅
  | 𝟘 => ∅
  | c ? p => ∅
  | c ! v • p => if decide(a = (c ⋉ v)) then {[ p ]} else ∅
  | t • p => ∅
  | g1 + g2 => lts_set_output_g g1 a ∪ lts_set_output_g g2 a
  end.

Fixpoint lts_set_output (p : proc) (a : TypeOfActions) {struct p} : gset proc:=
match p with
  | p1 ‖ p2 => 
      let ps1 := lts_set_output p1 a in
      let ps2 := lts_set_output p2 a in
      (* fixme: find a way to map over sets. *)
      list_to_set (map (fun p => p ‖ p2) (elements ps1)) ∪ list_to_set (map (fun p => p1 ‖ p) (elements ps2))
  | pr_var _ => ∅
  | rec _ • _ => ∅
(*   | If C Then A Else B => match (Eval_Eq C) with 
                          | Some true => lts_set_output A a
                          | Some false => lts_set_output B a
                          | None => ∅
                          end  *)
  | Match (cst 0) With zero=> P succ=> Q => lts_set_output (P^(cst 0)) a
  | Match (cst (S n)) With zero=> P succ=> Q => lts_set_output Q a
  | Match (bvar i) With zero=> P succ=> Q => ∅
  | g gp  => lts_set_output_g gp a
end.

Fixpoint lts_set_input_g (g : gproc) (a : TypeOfActions) : gset proc :=
 match g with
  | ① => ∅
  | 𝟘 => ∅
  | c' ? p => if decide(Channel_of a = c') then {[ p^(Data_of a) ]} else ∅
  | c' ! v • p => ∅
  | t • p => ∅
  | g1 + g2 => lts_set_input_g g1 a ∪ lts_set_input_g g2 a
  end.


Fixpoint lts_set_input (p : proc) (a : TypeOfActions) : gset proc :=
match p with
  | p1 ‖ p2 =>
      let ps1 := lts_set_input p1 a in
      let ps2 := lts_set_input p2 a in
      list_to_set (map (fun p => p ‖ p2) (elements ps1)) ∪ list_to_set (map (fun p => p1 ‖ p) (elements ps2))
  | pr_var _ => ∅
  | rec _ • _ => ∅ 
  | If C Then A Else B => match (Eval_Eq C) with 
                          | Some true => lts_set_input A a
                          | Some false => lts_set_input B a
                          | None => ∅
                          end 
  | g gp => lts_set_input_g gp a  
  end.


Fixpoint lts_set_tau_g (gp : gproc) : gset proc :=
match gp with
  | ① => ∅
  | 𝟘 => ∅
  | c ? p => ∅
  | c ! v • p => ∅
  | t • p => {[ p ]}
  | gp1 + gp2 => lts_set_tau_g gp1 ∪ lts_set_tau_g gp2
end.

(* Context (Eval_Eq : Equation Data -> (option bool)). 
à implémenter si du temps *)

Fixpoint lts_set_tau (p : proc) : gset proc :=
match p with
  | p1 ‖ p2 =>
      let ps1_tau : gset proc := list_to_set (map (fun p => p ‖ p2) (elements $ lts_set_tau p1)) in
      let ps2_tau : gset proc := list_to_set (map (fun p => p1 ‖ p) (elements $ lts_set_tau p2)) in
      let ps_tau := ps1_tau ∪ ps2_tau in
      let acts1 := outputs_of p1 in
      let acts2 := outputs_of p2 in
      let ps1 :=
        flat_map (fun a =>
                    map
                      (fun '(p1 , p2) => p1 ‖ p2)
                      (list_prod (elements $ lts_set_output p1 a) (elements $ lts_set_input p2 a)))
        (elements $ outputs_of p1) in
      let ps2 :=
        flat_map
          (fun a =>
             map
               (fun '(p1 , p2) => p1 ‖ p2)
               (list_prod (elements $ lts_set_input p1 a) (elements $ lts_set_output p2 a)))
          (elements $ outputs_of p2)
      in
      ps_tau ∪ list_to_set ps1 ∪ list_to_set ps2
  | pr_var _ => ∅
  | rec x • p => {[ pr_subst x p (rec x • p) ]}
  | If C Then A Else B => match (Eval_Eq C) with 
                          | Some true => lts_set_tau A
                          | Some false => lts_set_tau B
                          | None => ∅
                          end 
  | g gp => lts_set_tau_g gp
end.

Lemma lts_set_output_spec0 p a q : q ∈ lts_set_output p a -> lts p (ActExt (ActOut a)) q.
Proof.
  revert q.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0));
  destruct p; intros q mem; simpl in mem;  try now inversion mem.
  - eapply elem_of_union in mem as [mem | mem]. 
    * eapply elem_of_list_to_set, list_elem_of_fmap in mem as (q' & eq & mem). subst.
      apply lts_parL. rewrite elem_of_elements in mem. eapply Hp. simpl ; lia. eauto. 
    * eapply elem_of_list_to_set, list_elem_of_fmap in mem as (q' & eq & mem). subst.
      apply lts_parR. eapply Hp. simpl; lia. rewrite elem_of_elements in mem.  exact mem.
  - case_eq (Eval_Eq e).
    * intros. destruct b.
      ** rewrite H in mem. eapply lts_ifOne; eauto. eapply Hp; simpl. lia ; eauto. eauto.
      ** rewrite H in mem. eapply lts_ifZero; eauto. eapply Hp; simpl. lia ; eauto. eauto.
    * intros. rewrite H in mem. exfalso. inversion mem.
  - destruct g0; simpl in mem;  try now inversion mem.
    + case (TypeOfActions_dec a (c ⋉ d)) in mem.
          +++ subst. rewrite decide_True in mem; eauto.
              assert (q = p). set_solver. subst. eauto with ccs.
          +++ rewrite decide_False in mem; eauto. inversion mem.
    + eapply elem_of_union in mem as [mem | mem].
      ++ eapply lts_choiceL.
         eapply Hp. simpl; lia. eauto.
      ++ eapply lts_choiceR.
         eapply Hp. simpl; lia. eauto.
Qed.

Lemma lts_set_output_spec1 p a q : lts p (ActExt $ ActOut a) q -> q ∈ lts_set_output p a.
Proof.
  intro l. dependent induction l; try set_solver.
  - simpl. destruct (decide (c ⋉ v = c ⋉ v)) as [eq | not_eq]. 
    + set_solver.
    + exfalso. apply not_eq. reflexivity.
  - simpl in *. rewrite H. eapply IHl; eauto ; simpl.
  - simpl in *. rewrite H. eapply IHl; eauto ; simpl.
Qed.

Lemma lts_set_input_spec0 p a q : q ∈ lts_set_input p a -> lts p (ActExt $ ActIn a) q.
Proof.
  intro mem.
  dependent induction p; simpl in mem; try set_solver.
  + eapply elem_of_union in mem. destruct mem.
    ++ eapply elem_of_list_to_set in H.
       eapply list_elem_of_fmap in H as (q' & eq & mem). subst.
       rewrite elem_of_elements in mem. eauto with ccs.
    ++ eapply elem_of_list_to_set in H.
       eapply list_elem_of_fmap in H as (q' & eq & mem). subst.
       rewrite elem_of_elements in mem. eauto with ccs.
  + case_eq (Eval_Eq e).
    - intros. rewrite H in mem. destruct b.
      ++ eapply lts_ifOne; eauto.
      ++ eapply lts_ifZero; eauto.
    - intros. rewrite H in mem. exfalso. inversion mem.
  + dependent induction g0; simpl in mem; try set_solver.
      ++ destruct (decide (Channel_of a = c)).
         +++ subst. eapply elem_of_singleton_1 in mem. subst. destruct a. simpl. apply lts_input.
         +++ destruct a. simpl in *. inversion mem.
      ++ eapply elem_of_union in mem. destruct mem; eauto with ccs.
Qed.

(* Lemma simplify_input_cst p a q : lts p (ActExt $ ActIn a) q -> exists c v, a = act c (cst v).
Proof.
  revert q.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0));
  destruct p; intros q l; try now inversion l.
  + inversion l ; subst.
    ++ eapply Hp in H3 as (c & v & eq); subst; simpl; try now lia. eexists;eauto.
    ++ eapply Hp in H3 as (c & v & eq); subst; simpl; try now lia. eexists;eauto.
  + inversion l ; subst.
    ++ eapply Hp in H5 as (c & v & eq); subst; simpl; try now lia. eexists;eauto.
    ++ eapply Hp in H5 as (c & v & eq); subst; simpl; try now lia. eexists;eauto.
  + destruct g0; try now inversion l.
    ++ inversion l; subst. repeat eexists ;eauto. reflexivity.
    ++ inversion l; subst.
       +++ eapply Hp in H3 as (c & v & eq); subst; simpl; try now lia. eexists;eauto.
       +++ eapply Hp in H3 as (c & v & eq); subst; simpl; try now lia. eexists;eauto.
Qed.

Lemma simplify_output_cst p a q : lts p (ActExt $ ActOut a) q -> exists c v, a = act c (cst v).
Proof.
  revert q.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0));
  destruct p; intros q l; try now inversion l.
  + inversion l ; subst.
    ++ eapply Hp in H3 as (c & v & eq); subst; simpl; try now lia. eexists;eauto.
    ++ eapply Hp in H3 as (c & v & eq); subst; simpl; try now lia. eexists;eauto.
  + inversion l ; subst.
    ++ eapply Hp in H5 as (c & v & eq); subst; simpl; try now lia. eexists;eauto.
    ++ eapply Hp in H5 as (c & v & eq); subst; simpl; try now lia. eexists;eauto.
  + destruct g0; try now inversion l.
    ++ inversion l; subst. eexists ;eauto.
    ++ inversion l; subst.
       +++ eapply Hp in H3 as (c & v & eq); subst; simpl; try now lia. eexists;eauto.
       +++ eapply Hp in H3 as (c & v & eq); subst; simpl; try now lia. eexists;eauto.
Qed. *)

Lemma lts_set_input_spec1 p a q : lts p (ActExt $ ActIn a) q -> q ∈ lts_set_input p a.
Proof.
  intro l. destruct a. destruct d.
  + dependent induction l; try set_solver.
    ++ simpl. rewrite decide_True; eauto. set_solver.
    ++ simpl in *. rewrite H. eauto.
    ++ simpl in *. rewrite H. eauto.
  + dependent induction l; try set_solver.
    ++ simpl. rewrite decide_True; eauto. set_solver.
    ++ simpl in *. rewrite H. eauto.
    ++ simpl in *. rewrite H. eauto.
Qed.

(* Lemma simplify_output_data p a : a ∈ (moutputs_of p) -> exists c v, a = act c (cst v).
Proof.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0));
  destruct p; intro mem; try now inversion mem.
  + simpl. eapply gmultiset_elem_of_disj_union in mem.
    destruct mem as [in_left | in_right].
    ++ eapply Hp in in_left as (c & v & eq); subst;  try now simpl; lia.
       eauto.
    ++ eapply Hp in in_right as (c & v & eq); subst;  try now simpl; lia.
       eauto.
  + simpl in *. case_eq (Eval_Eq e).
    ++ intros. rewrite H in mem. destruct b.
       +++ eapply Hp; eauto. lia.
       +++ eapply Hp; eauto. lia.
    ++ intros. rewrite H in mem. exfalso. inversion mem.
  + destruct a. 
    destruct g0; simpl in * ; try now inversion mem.
    ++ destruct d0.
       +++ assert (act c d = act c0 (cst v)). multiset_solver.
           subst. eexists; eauto.
       +++ inversion mem.
    ++ eapply gmultiset_elem_of_disj_union in mem.
       destruct mem as [in_left | in_right].
       +++ assert (c ⋉ d ∈ moutputs_of  (g g0_1)) as Hyp_Left.
           simpl; eauto.
           eapply Hp in Hyp_Left as (c' & v' & eq); subst;  try now simpl; lia.
           inversion eq; subst.
           eexists; eauto.
       +++ assert (c ⋉ d ∈ moutputs_of  (g g0_2)) as Hyp_Right.
           simpl; eauto.
           eapply Hp in Hyp_Right as (c' & v' & eq); subst;  try now simpl; lia.
           inversion eq; subst.
           eexists; eauto.
Qed. *)

Lemma lts_set_tau_spec0 p q : q ∈ lts_set_tau p -> lts p τ q.
Proof.
  - intro mem.
    dependent induction p; simpl in mem.
    + eapply elem_of_union in mem. destruct mem as [mem1 | mem2].
      ++ eapply elem_of_union in mem1.
         destruct mem1.
         eapply elem_of_union in H as [mem1 | mem2]. 
         eapply elem_of_list_to_set, list_elem_of_fmap in mem1 as (t' & eq & h); subst.
         rewrite elem_of_elements in h. eauto with ccs.
         eapply elem_of_list_to_set, list_elem_of_fmap in mem2 as (t' & eq & h); subst.
         rewrite elem_of_elements in h. eauto with ccs.
         eapply elem_of_list_to_set, list_elem_of_In, in_flat_map in H as (t' & eq & h); subst.
         eapply list_elem_of_In, list_elem_of_fmap in h as ((t1 & t2) & eq' & h'). subst.
         eapply list_elem_of_In, in_prod_iff in h' as (mem1 & mem2).
         eapply list_elem_of_In in mem1. rewrite elem_of_elements in mem1.
         eapply list_elem_of_In in mem2. rewrite elem_of_elements in mem2.
         eapply lts_set_output_spec0 in mem1.
         eapply lts_set_input_spec0 in mem2. destruct t'. eapply lts_comL. exact mem1. exact mem2.
      ++ eapply elem_of_list_to_set, list_elem_of_In, in_flat_map in mem2 as (t' & eq & h); subst.
         eapply list_elem_of_In, list_elem_of_fmap in h as ((t1 & t2) & eq' & h'). subst.
         eapply list_elem_of_In, in_prod_iff in h' as (mem1 & mem2).
         eapply list_elem_of_In in mem1. rewrite elem_of_elements in mem1.
         eapply list_elem_of_In in mem2. rewrite elem_of_elements in mem2.
         eapply lts_set_input_spec0 in mem1.
         eapply lts_set_output_spec0 in mem2. destruct t'. eapply lts_comR. exact mem2. exact mem1.
    + inversion mem.
    + eapply elem_of_singleton_1 in mem. subst; eauto with ccs.
    + case_eq (Eval_Eq e); intros; rewrite H in mem.
      ++ destruct b.
         +++ eapply lts_ifOne; eauto.
         +++ eapply lts_ifZero; eauto.
      ++ exfalso. inversion mem.
    + dependent induction g0; simpl in mem; try set_solver;
        try eapply elem_of_singleton_1 in mem; subst; eauto with ccs.
      eapply elem_of_union in mem as [mem1 | mem2]; eauto with ccs.
Qed.

Lemma lts_set_tau_spec1 p q : lts p τ q -> q ∈ lts_set_tau p.
Proof. 
  intro l. dependent induction l; simpl; try set_solver.
  - rewrite H. eauto.
  - rewrite H. eauto.
  - eapply elem_of_union. left.
    eapply elem_of_union. right.
    eapply elem_of_list_to_set.
    rewrite list_elem_of_In. rewrite in_flat_map.
    exists (c ⋉ v). split.
    + eapply list_elem_of_In, elem_of_elements.
      eapply outputs_of_spec1. eauto.
    + eapply list_elem_of_In, list_elem_of_fmap.
      exists (p2 , q2). split.
      ++ reflexivity.
      ++ eapply list_elem_of_In, in_prod_iff; split; eapply list_elem_of_In, elem_of_elements.
         eapply lts_set_output_spec1; eauto with ccs.
         eapply lts_set_input_spec1; eauto with ccs.
  - eapply elem_of_union. right.
    eapply elem_of_list_to_set.
    rewrite list_elem_of_In. rewrite in_flat_map.
    exists (c ⋉ v). split.
    + eapply list_elem_of_In, elem_of_elements.
      eapply outputs_of_spec1. exact l1.
    + eapply list_elem_of_In, list_elem_of_fmap.
      exists (q2 , p2). split.
      ++ reflexivity.
      ++ eapply list_elem_of_In, in_prod_iff; split; eapply list_elem_of_In, elem_of_elements.
         eapply lts_set_input_spec1; eauto with ccs.
         eapply lts_set_output_spec1; eauto with ccs.
Qed.

Definition lts_set (p : proc) (α : ActIO TypeOfActions): gset proc :=
  match α with
  | τ => lts_set_tau p
  | a ? => lts_set_input p a
  | a ! => lts_set_output p a
  end.

Lemma lts_set_spec0 p α q : q ∈ lts_set p α -> lts p α q.
Proof.
  destruct α as [[a|a]|].
  - now eapply lts_set_input_spec0.
  - now eapply lts_set_output_spec0.
  - now eapply lts_set_tau_spec0.
Qed.

Lemma lts_set_spec1 p α q : lts p α q -> q ∈ lts_set p α.
Proof.
  destruct α as [[a|a]|].
  - now eapply lts_set_input_spec1.
  - now eapply lts_set_output_spec1.
  - now eapply lts_set_tau_spec1.
Qed.

Definition proc_stable p α := lts_set p α = ∅.

Lemma lts_dec p α q : { lts p α q } + { ~ lts p α q }.
Proof.
  destruct (decide (q ∈ lts_set p α)).
  - eapply lts_set_spec0 in e. eauto.
  - right. intro l. now eapply lts_set_spec1 in l.
Qed.

Lemma proc_stable_dec p α : Decision (proc_stable p α).
Proof. destruct (decide (lts_set p α = ∅)); [ left | right ]; eauto. Qed.

Lemma gset_nempty_ex (g : gset proc) : g ≠ ∅ -> {p | p ∈ g}.
Proof.
  intro n. destruct (elements g) eqn:eq.
  + destruct n. eapply elements_empty_iff in eq. set_solver.
  + exists p. eapply elem_of_elements. rewrite eq. set_solver.
Qed.

#[global] Program Instance VCCS_Label : Label TypeOfActions := 
  {| label_eqdec := TypeOfActions_dec ;
  label_countable := TypeOfActions_countable |}. (* useless, already said it, it is just a reminder *)

#[global] Program Instance VCCS_Lts : Lts proc TypeOfActions := 
  {| lts_step x ℓ y  := lts x ℓ y ;
     lts_state_eqdec := proc_dec ;
     lts_step_decidable p α q := lts_dec p α q ;
     lts_outputs := outputs_of ;
     lts_outputs_spec1 p1 x p2 := outputs_of_spec1 p1 x p2;
     lts_outputs_spec2 p1 x := outputs_of_spec2 p1 x;
     lts_stable p := proc_stable p;
     lts_stable_decidable p α := proc_stable_dec p α 
    |}.
    Next Obligation.
        intros p [[a|a]|]; intro hs;eapply gset_nempty_ex in hs as (r & l); eapply lts_set_spec0 in l; 
        exists r; assumption.
    Qed.
    Next Obligation.  
        intros p [[a|a]|]; intros (q & mem); intro eq; eapply lts_set_spec1 in mem; set_solver.
    Qed.

#[global] Program Instance VCCS_LtsEq : LtsEq proc TypeOfActions := 
  {| eq_rel x y  := cgr x y;
     eq_rel_refl p := cgr_refl p;
     eq_symm p q := cgr_symm p q;
     eq_trans x y z:= cgr_trans x y z;
     eq_spec p q α := Congruence_Respects_Transition p q α |}.

From TestingTheory Require Import gLts Bisimulation Lts_OBA Lts_FW Lts_OBA_FB GeneralizeLtsOutputs.

#[global] Program Instance VCCS_ggLts : gLts proc (ExtAct TypeOfActions) := ggLts gLabel_b.

#[global] Program Instance VCCS_ggLtsEq : gLtsEq proc (ExtAct TypeOfActions) := 
  ggLtsEq gLabel_b.

#[global] Program Instance VCCS_gLtsOBA : gLtsOba proc (ExtAct TypeOfActions) := ggLtsOba_b.

#[global] Program Instance VCCS_gLtsOBAFB : gLtsObaFB proc (ExtAct TypeOfActions) := ggLtsObaFB_b.

#[global] Program Instance VCCS_gLtsOBAFW : gLtsObaFW proc (ExtAct TypeOfActions) := ggLtsObaFW_b.

*)


