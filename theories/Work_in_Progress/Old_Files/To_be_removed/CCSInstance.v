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
(*

From Stdlib.Program Require Import Equality.
From Stdlib.Strings Require Import String.
From Stdlib Require Import Relations.
From Stdlib.Wellfounded Require Import Inverse_Image.

From stdpp Require Import base countable finite gmap list gmultiset strings.
From TestingTheory Require Import InListPropHelper InputOutputActions ActTau OldTransitionSystems Must 
      Completeness Soundness DefinitionCI Normalisation MultisetLTSConstruction
      GeneralizeLtsOutputs ForwarderConstruction ParallelLTSConstruction Testing_Predicate
      (* gLts *) (* Bisimulation *).

Parameter Channel : Type.

Definition Value := unit.

End M.

(** ** CCS *)

(*************************************** Channels ******************************************)

(* ChannelType est le type des canaux, par exemple des chaînes de caractères*)

Parameter (Channel : Type).
(*Exemple : Definition Channel := string.*)
Parameter (channel_eq_dec : EqDecision Channel).
#[global] Instance channel_eqdecision : EqDecision Channel. by exact channel_eq_dec. Defined.
(* Coercion ActExt : ExtAct >-> Act. *)
Parameter (channel_is_countable : Countable Channel).
#[global] Instance channel_countable : Countable Channel. by exact channel_is_countable. Defined.


(* Definition of processes*)
Inductive proc : Type :=
(* To parallele two processes*)
| pr_par : proc -> proc -> proc
(* Variable in a process, for recursion and substitution*)
| pr_var : nat -> proc
(* recursion for process*)
| pr_rec : nat -> proc -> proc
(*The Guards*)
| g : gproc -> proc

with gproc : Type :=
(* The success operation*)
| gpr_success : gproc
(* The Process that does nothing*)
| gpr_nil : gproc
(*An input is a Channel of a channel followed by a process*)
| gpr_input : Channel -> proc -> gproc
(*An output is a Channel of a channel followed by a process*)
| gpr_output : Channel -> proc -> gproc
(*A tau action : does nothing *)
| gpr_tau : proc -> gproc
(* To choose between two processes*)
| gpr_choice : gproc -> gproc -> gproc
.

Coercion pr_var : nat >-> proc.
Coercion g : gproc >-> proc.

Notation "①" := (gpr_success).
Notation "𝟘" := (gpr_nil).
Notation "'rec' x '•' p" := (pr_rec x p) (at level 50).
Notation "P + Q" := (gpr_choice P Q).
Notation "P ‖ Q" := (pr_par P Q) (at level 50).
Notation "c ! • P" := (gpr_output c P) (at level 50).
Notation "c ? • P" := (gpr_input c P) (at level 50).
Notation "'𝛕' • P" := (gpr_tau P) (at level 50).


(*Definition for the size of a term : proc, to do induction on it in the future*)
Fixpoint size (p : proc) :=
  match p with
  | p ‖ q  => S (size p + size q)
  | pr_var _ => 1
  | rec x • p => S (size p)
  | g p => gsize p
  end

with gsize p :=
  match p with
  | ① => 1
  | 𝟘 => 0
  | c ! • p => S (size p)
  | c ? • p => S (size p)
  | 𝛕 • p => S (size p)
  | p + q => S (gsize p + gsize q)
  end.


(* Substitution, usefull for Recursion def and Context definition (for congruence) *)
Fixpoint pr_subst id p q :=
  match p with
  | p1 ‖ p2 => pr_par (pr_subst id p1 q) (pr_subst id p2 q)
  | pr_var id' => if decide (id = id') then q else p
  | rec id' • p' =>
    if decide (id = id') then p else rec id' • (pr_subst id p' q)
  | g gp => g (gpr_subst id gp q)
end

with gpr_subst id p q {struct p} := match p with
| ① => p
| 𝟘 => p
| c ! • p =>
    c ! • (pr_subst id p q)
| c ? • p =>
    c ? • (pr_subst id p q)
| 𝛕 • p =>
    𝛕 • (pr_subst id p q)
| p1 + p2 =>
    (gpr_subst id p1 q) + (gpr_subst id p2 q)
end.


(* The Labelled Transition System (LTS-transition) *)
Inductive lts : proc -> ActIO Channel -> proc -> Prop :=
(*The Input and the Output*)
| lts_input : forall {c p},
    lts (c ? • p) (c ?) p
| lts_output : forall {c p},
    lts (c ! • p) (c !) p

(*The actions Tau*)
| lts_tau : forall {p},
    lts (𝛕 • p) τ p
| lts_rec : forall {x p},
    lts (rec x • p) τ (pr_subst x p (rec x • p))

(* Communication of a channel output and input that have the same Channel*)
| lts_comL : forall {a p1 p2 q1 q2},
    lts p1 (ActExt (ActOut a)) p2 ->
    lts q1 (ActExt (ActIn a)) q2 ->
    lts (p1 ‖ q1) τ (p2 ‖ q2)
| lts_comR : forall {a p1 p2 q1 q2},
    lts p1 (ActExt (ActOut a)) p2 ->
    lts q1 (ActExt (ActIn a)) q2 ->
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


Hint Constructors lts:ccs.

Reserved Notation "p ≡ q" (at level 70).
(*Naïve definition of a relation ≡ that will become a congruence ≡* by transitivity*)
Inductive cgr_step : proc -> proc -> Prop :=
(*  Reflexivity of the Relation ≡  *)
| cgr_refl_step : forall p, p ≡ p

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

(*The reduction is given to certain terms...*)
| cgr_recursion_step : forall x p q,
    cgr_step p q -> (rec x • p) ≡ (rec x • q)
| cgr_tau_step : forall p q,
    cgr_step p q ->
    cgr_step (𝛕 • p) (𝛕 • q)
| cgr_input_step : forall c p q,
    cgr_step p q ->
    cgr_step (c ? • p) (c ? • q)
| cgr_output_step : forall c p q,
    cgr_step p q ->
    cgr_step (c ! • p) (c ! • q)
| cgr_par_step : forall p q r,
    cgr_step p q ->
    p ‖ r ≡ q ‖ r

(*...and sums (only for guards (by sanity))*)
| cgr_choice_step : forall p1 q1 p2,
    cgr_step (g p1) (g q1) ->
    cgr_step (p1 + p2) (q1 + p2)
.



Hint Constructors cgr_step:cgr_step_structure.

Infix "≡" := cgr_step (at level 70).

(* The relation ≡ is an reflexive*)
#[global] Instance cgr_refl_step_is_refl : Reflexive cgr_step.
Proof. intro. apply cgr_refl_step. Qed.
(* The relation ≡ is symmetric*)
#[global] Instance cgr_symm_step : Symmetric cgr_step.
Proof. intros p q hcgr. induction hcgr; constructor ; auto. Qed.

(* Defining the transitive closure of ≡*)
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

Hint Resolve cgr_refl cgr_symm cgr_trans:cgr_eq.

(* The relation ≡* is an equivence relation*)
#[global] Instance cgr_is_eq_rel  : Equivalence cgr.
Proof. repeat split.
       + apply cgr_refl.
       + apply cgr_symm.
       + apply cgr_trans.
Qed.

(*the relation ≡* respects all the rules that ≡ respected*)
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
Lemma cgr_par_assoc : forall p q r, (p ‖ q) ‖ r ≡* p ‖(q ‖r).
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
Lemma cgr_choice_nil_rev : forall p, g p ≡* p + 𝟘.
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
Lemma cgr_tau : forall p q, p ≡* q -> (𝛕 • p) ≡* (𝛕 • q).
Proof.
intros. dependent induction H.
constructor.
apply cgr_tau_step. exact H. eauto with cgr_eq.
Qed.
Lemma cgr_input : forall c p q, p ≡* q -> (c ? • p) ≡* (c ? • q).
Proof.
intros. dependent induction H.
constructor.
apply cgr_input_step. exact H. eauto with cgr_eq.
Qed.
Lemma cgr_output : forall c p q, p ≡* q -> (c ! • p) ≡* (c ! • q).
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

(* This is all for cgr_choice *)
Lemma cgr_n_par_l p p' q n: clos_n cgr_step n p p' ->
  clos_n cgr_step n (p ‖ q) (p' ‖ q).
Proof.
induction 1 as [|n p p' p'' Hp' Hind].
- constructor.
- apply clos_n_step with (p' ‖ q).
  + now constructor.
  + apply IHHind.
Qed.

(* It takes two more steps to apply congruences on the right hand side of
  a parallel *)
Lemma cgr_n_par_r p p' q n: clos_n cgr_step n p p' ->
  clos_n cgr_step (S (S n)) (q ‖ p) (q ‖ p').
Proof.
intro Hp. apply clos_n_step with (p ‖ q); [constructor|].
replace (S n) with (n + 1)%nat by lia.
apply clos_n_trans with (p' ‖ q).
- apply cgr_n_par_l, Hp.
- apply clos_n_step with (q ‖ p'); constructor.
Qed.

Lemma cgr_n_par_guard p q g0 n : clos_n cgr_step n (p ‖ q) (g g0) ->
  exists np nq,
  (n >= (np + nq + 2)%nat /\ (clos_n cgr_step np p (g gpr_nil) /\ clos_n cgr_step nq q (g g0)) \/
   (n >= (np + nq + 2)%nat /\ clos_n cgr_step np p (g g0) /\ clos_n cgr_step nq q (g gpr_nil)) \/
   (n >= (np + 1)%nat /\ clos_n cgr_step np p (g g0) /\ clos_n cgr_step 0 q (g gpr_nil))).
Proof.
(* by strong induction *)
revert p q g0. induction n as [n IH] using lt_wf_ind; intros p q g0 H.
destruct n as [|n]; [inversion H|].
apply clos_n_S_inv in H as [Heq | [p' [Hpp' Hp'q]]]; [inversion Heq|].
dependent destruction Hpp'.
  + apply IH in Hp'q as (np & nq & [[Hnpq [Hp Hq]] | [[Hnpq [Hp Hq]] | [Hnpq [Hp Hq]]]]).
    * exists (S np), nq. left. repeat split; [lia| |]; trivial.
      apply clos_n_S, Hp.
    * exists (S np), nq. right. left. repeat split; [lia| |]; trivial.
      apply clos_n_S, Hp.
    * inversion Hq; subst. exists (S np), 0. right; right.
      repeat split; trivial.
      -- lia.
      -- apply clos_n_S, Hp.
    * constructor.
  + exists n, 0. right. right. repeat split; [lia| |]; trivial. constructor.
  + apply IH in Hp'q as (np & nq & [[Hnpq [Hp Hq]] | [[Hnpq [Hp Hq]] | [Hnpq [Hp Hq]]]]).
    * apply IH in Hp as (np' & nq' & [[Hnpq' [Hp' Hq']] | [[Hnpq' [Hp' Hq']] | [Hnpq' [Hp' Hq']]]]).
      -- exists (S (S np')), (nq' + nq)%nat. left.
         repeat split; [lia| |].
         ++ apply clos_n_S, clos_n_S, Hp'.
         ++ now apply clos_n_trans with (g gpr_nil).
      -- exists (np' + nq)%nat, (S (S nq')). right. left.
         repeat split; [lia| |].
         ++	now apply clos_n_trans with (g gpr_nil).
         ++ apply clos_n_S, clos_n_S, Hq'.
      -- subst. exists (np' + nq)%nat, 0. right. right.
         repeat split; [lia| |]; trivial.
         apply clos_n_trans with (g gpr_nil); trivial.
      -- lia.
    * apply IH in Hp as (np' & nq' & [[Hnpq' [Hp' Hq']] | [[Hnpq' [Hp' Hq']] | [Hnpq' [Hp' Hq']]]]).
      -- exists np', nq'. left.
         repeat split; [lia| |]; trivial.
      -- exists np', nq'. right. left. repeat split; [lia| |]; trivial.
      -- inversion Hq'; subst. exists np', 0. right; right.
         repeat split; trivial. lia.
      -- lia.
    * apply IH in Hp as (np' & nq' & [[Hnpq' [Hp' Hq']] | [[Hnpq' [Hp' Hq']] | [Hnpq' [Hp' Hq']]]]).
      -- exists np', nq'. left. repeat split; [lia| |]; trivial.
      -- exists np', nq'. right. left. repeat split; trivial. lia.
      -- inversion Hq'; subst. exists np', 0. right; right.
         repeat split; trivial. lia.
      -- lia.
    * lia.
  + apply IH in Hp'q as (np & nq & [[Hnpq [Hp Hq]] | [[Hnpq [Hp Hq]] | [Hnpq [Hp Hq]]]]).
    * exists nq, np. right. left. repeat split; trivial. lia.
    * exists nq, np. left. repeat split; trivial. lia.
    * inversion Hq; subst. exists 0, np. left. repeat split; trivial. lia.
    * lia.
  + apply IH in Hp'q as (np & nq & [[Hnpq [Hp Hq]] | [[Hnpq [Hp Hq]] | [Hnpq [Hp Hq]]]]).
    * apply IH in Hq as (np' & nq' & [[Hnpq' [Hp' Hq']] | [[Hnpq' [Hp' Hq']] | [Hnpq' [Hp' Hq']]]]).
      -- exists (np + (2 + np'))%nat, nq'. left. repeat split; trivial. lia.
         apply clos_n_trans with (g gpr_nil ‖ q0).
         ++ apply cgr_n_par_l, Hp.
         ++ apply clos_n_step with (q0 ‖ g gpr_nil); [constructor|].
            apply clos_n_step with q0; [constructor|]; trivial.
      -- exists (np + S (S np'))%nat, nq'. right. left.
         repeat split; trivial; [lia|].
         apply clos_n_trans with (g gpr_nil ‖ q0).
         ++ now apply cgr_n_par_l.
         ++ apply clos_n_step with (q0 ‖ g gpr_nil); [constructor|].
            apply clos_n_step with q0; [constructor|]. trivial.
      -- eexists (np + (2 + np'))%nat, 0; right; right.
         repeat split; trivial; [lia|].
         apply clos_n_trans with (g gpr_nil ‖ q0).
         ++ now apply cgr_n_par_l.
         ++ apply clos_n_step with (q0 ‖ g gpr_nil); [constructor|].
            apply clos_n_step with q0; [constructor|]. trivial.
      -- lia.
    * apply IH in Hq as (np' & nq' & [[Hnpq' [Hp' Hq']] | [[Hnpq' [Hp' Hq']] | [Hnpq' [Hp' Hq']]]]).
      -- exists (np + ((2 + np') + 1))%nat, nq'. right. left.
         repeat split; trivial; [lia|].
         apply clos_n_trans with (g g0 ‖ q0).
         ++ now apply cgr_n_par_l.
         ++ apply clos_n_trans with (g g0 ‖ g gpr_nil).
          ** now apply cgr_n_par_r.
          ** eapply clos_n_step; [|constructor]. constructor.
      -- exists (np + ((2 + np') + 1))%nat, nq'. right. left.
         repeat split; trivial; [lia|].
         apply clos_n_trans with (g g0 ‖ q0).
         ++ now apply cgr_n_par_l.
         ++ apply clos_n_trans with (g g0 ‖ g gpr_nil).
          ** now apply cgr_n_par_r.
          ** eapply clos_n_step; [|constructor]. constructor.
      -- exists (np + ((2 + np') + 1))%nat, 0. right. right. repeat split; trivial; [lia|].
         apply clos_n_trans with (g g0 ‖ q0).
         ++ now apply cgr_n_par_l.
         ++ apply clos_n_trans with (g g0 ‖ g gpr_nil).
          ** now apply cgr_n_par_r.
          ** eapply clos_n_step; [|constructor]. constructor.
      -- lia.
    * inversion Hq.
    * lia.
  + apply IH in Hp'q as (np & nq & [[Hnpq [Hp Hq]] | [[Hnpq [Hp Hq]] | [Hnpq [Hp Hq]]]]).
    * apply IH in Hp as (np' & nq' & [[Hnpq' [Hp' Hq']] | [[Hnpq' [Hp' Hq']] | [Hnpq' [Hp' Hq']]]]).
      -- exists np', (nq' + S (S nq))%nat. left. repeat split; trivial; [lia|].
         apply clos_n_trans with (g gpr_nil ‖ r).
         ++ now apply cgr_n_par_l.
         ++ apply clos_n_step with (r ‖ g gpr_nil); [constructor|].
            apply clos_n_step with r; [constructor|]. trivial.
      -- exists np', (nq' + S (S nq))%nat. left. repeat split; trivial; [lia|].
         apply clos_n_trans with (g gpr_nil ‖ r).
         ++ now apply cgr_n_par_l.
         ++ apply clos_n_step with (r ‖ g gpr_nil); [constructor|].
            apply clos_n_step with r; [constructor|]. trivial.
      -- exists np', (S (S nq)). left. repeat split; trivial; [lia|].
         inversion Hq'. apply clos_n_step with (r  ‖ g gpr_nil);[constructor|].
         apply clos_n_step with r;[constructor|]. trivial.
      -- lia.
    * apply IH in Hp as (np' & nq' & [[Hnpq' [Hp' Hq']] | [[Hnpq' [Hp' Hq']] | [Hnpq' [Hp' Hq']]]]).
      -- exists np', (nq' + (S (S nq) + 1))%nat. left. repeat split; trivial; [lia|].
         apply clos_n_trans with (g g0 ‖ r); [now apply cgr_n_par_l|].
         apply clos_n_trans with (g g0 ‖ g gpr_nil); [now apply cgr_n_par_r|].
         apply clos_n_step with (g g0); constructor.
      -- exists np', (nq' + (2 + nq))%nat. right. left.
         repeat split; trivial; [lia|].
         apply clos_n_trans with (g gpr_nil ‖ r); [now apply cgr_n_par_l|].
         apply clos_n_step with (r ‖ g gpr_nil); [constructor|].
         apply clos_n_step with r; [constructor|]. trivial.
      -- exists np', (2 + nq)%nat. right. left.
         repeat split; trivial; [lia|]. inversion Hq'; subst.
         apply clos_n_step with (r ‖ g gpr_nil); [constructor|].
         apply clos_n_step with r; [constructor|]. trivial.
      -- lia.
    * inversion Hq; subst.
      apply IH in Hp as (np' & nq' & [[Hnpq' [Hp' Hq']] | [[Hnpq' [Hp' Hq']] | [Hnpq' [Hp' Hq']]]]).
      -- exists np', (S nq'). left. repeat split; trivial; [lia|].
         apply clos_n_step with q0; [constructor|]. trivial.
      -- exists np', (S nq')%nat. right. left. repeat split; trivial; [lia|].
         apply clos_n_step with q0; [constructor|]. trivial.
      -- exists np', 1. right. left. repeat split; trivial; [lia|].
         inversion Hq'. apply clos_n_step with (g gpr_nil); constructor.
      -- lia.
    * lia.
  + apply IH in Hp'q as (np & nq & [[Hnpq [Hp Hq]] | [[Hnpq [Hp Hq]] | [Hnpq [Hp Hq]]]]).
    * exists (S np), nq. left. repeat split; [lia| |]; trivial.
      apply clos_n_step with q0; trivial.
    * exists (S np), nq. right. left. repeat split; [lia| |]; trivial.
      apply clos_n_step with q0; trivial.
    * exists (S np), nq. right. right. repeat split; [lia| |]; trivial.
      apply clos_n_step with q0; trivial.
    * constructor.
Qed.

Lemma cgr_n_par_nil_l p q n: clos_n cgr_step n (g p ‖ g gpr_nil) (g q) ->
  clos_n cgr_step n (g p) (g q).
Proof.
intro Hp. apply cgr_n_par_guard in Hp
  as (np & nq & [[Hnpq [Hp Hq]] | [[Hnpq [Hp Hq]] | [Hnpq [Hp Hq]]]]).
- assert (Hle : (np + nq)%nat <= n) by lia.
  unshelve eapply (clos_n_le _ Hle).
  eapply clos_n_trans; eassumption.
- apply (clos_n_le Hp). lia.
- apply (clos_n_le Hp). lia.
Qed.

Lemma cgr_choice : forall p q r, g p ≡* g q -> p + r ≡* q + r.
Proof.
(* By induction on the __length__ of the cgr-derivation *)
intros p q r H. apply clos_trans_clos_n in H as [n Hn].
revert n p q r Hn. induction n as [|n]; intros p q r Hn;
[inversion Hn; subst; reflexivity|].
apply clos_n_S_inv in Hn as [Heq|[p' [Hpp' Hp'q]]]; [now inversion Heq|].
dependent destruction Hpp';
try solve[etransitivity; [|eapply IHn; eauto]; repeat constructor].
- apply IHn, cgr_n_par_nil_l, Hp'q.
- transitivity (g (𝛕 • q0 + r)) ; [repeat constructor| apply IHn]; trivial.
- transitivity (g (c ? • q0 + r)); [repeat constructor| apply IHn]; trivial.
- transitivity (g (c ! • q0 + r)); [repeat constructor| apply IHn]; trivial.
- transitivity (g (q1 + p2 + r)); [repeat constructor| apply IHn]; trivial.
Qed.

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


Hint Resolve cgr_par_nil cgr_par_nil_rev cgr_par_nil_rev cgr_par_com cgr_par_assoc 
cgr_par_assoc_rev cgr_choice_nil cgr_choice_nil_rev cgr_choice_com cgr_choice_assoc 
cgr_choice_assoc_rev cgr_recursion cgr_tau cgr_input cgr_output cgr_par cgr_choice 
cgr_refl cgr_symm cgr_trans:cgr.


(* State Transition System (STS-reduction) *)
Inductive sts : proc -> proc -> Prop :=
(*The axiomes*)
(* Communication of channels output and input that have the same Channel *)
| sts_com : forall {c p1 g1 p2 g2},
    sts (((c ! • p1) + g1) ‖ ((c ? • p2) + g2)) (p1 ‖ p2)
(* Nothing more , something less *)
| sts_tau : forall {p g},
    sts ((𝛕 • p) + g) p
(* Resursion *)
| sts_rec : forall {x p},
    sts (rec x • p) (pr_subst x p (rec x • p))

(* The left parallele respect the Reduction *)
| sts_par : forall {p1 p2 q},
    sts p1 p2 ->
    sts (p1 ‖ q) (p2 ‖ q)

(*The Congruence respects the Reduction *)
| sts_cong : forall {p1 p2 q2 q1},
    p1 ≡* p2 -> sts p2 q2 -> q2 ≡* q1 -> sts p1 q1
.
Infix "➙" := sts (at level 50).

Hint Constructors sts:ccs.

(* For the (STS-reduction), the reductible terms and reducted terms are pretty all the same, up to ≡* *)
Lemma ReductionShape : forall P Q, P ➙ Q ->
((exists x P1 P2 M1 M2 S, ((P ≡* (((x ! • P1) + M1) ‖ ((x ? • P2) + M2)) ‖ S)) /\ (Q ≡*((P1 ‖ P2) ‖ S)))
\/ (exists P1 M1 S, (P ≡* (((𝛕 • P1) + M1) ‖ S)) /\ (Q ≡* (P1 ‖ S)))
\/ (exists n P1 S, (P ≡* ((rec n • P1) ‖ S)) /\ (Q ≡* (pr_subst n P1 (rec n • P1) ‖ S)))).
Proof.
intros P Q Transition.
induction Transition.
  - left. exists c. exists p1. exists p2. exists g1. exists g2. exists 𝟘. split; apply cgr_par_nil_rev.
  - right. left. exists p. exists g0. exists 𝟘. split; apply cgr_par_nil_rev.
  - right. right. exists x. exists p. exists 𝟘. split; apply cgr_par_nil_rev.
  - destruct IHTransition as [IH|[IH|IH]]; [ left | right; left | right; right]; decompose record IH.
    * exists x. exists x0. exists x1. exists x2. exists x3. exists (x4 ‖ q). split.
        ** apply transitivity with (((((x ! • x0) + x2) ‖ ((x ? • x1) + x3)) ‖ x4) ‖ q). apply cgr_par. exact H. apply cgr_par_assoc.
        ** apply transitivity with (((x0 ‖ x1) ‖ x4) ‖ q). apply cgr_par. exact H1.  apply cgr_par_assoc.
    * exists x. exists x0. exists (x1 ‖ q). split.
        ** apply transitivity with (((𝛕 • x + x0) ‖ x1) ‖ q). apply cgr_par. exact H0.
        apply cgr_par_assoc.
        ** apply transitivity with (x ‖(x1) ‖ q). apply cgr_par. exact H1. apply cgr_par_assoc.
    * exists x. exists x0. exists (x1 ‖ q). split.
        ** apply transitivity with ((rec x • x0 ‖ x1) ‖ q). apply cgr_par. exact H0. apply cgr_par_assoc.
        ** apply transitivity with ((pr_subst x x0 (rec x • x0) ‖ x1) ‖ q). apply cgr_par. exact H1. apply cgr_par_assoc.
  - destruct IHTransition as [IH|[IH|IH]]; [ left | right; left | right; right];  decompose record IH.
    * exists x. exists x0. exists x1. exists x2. exists x3. exists x4. split. apply cgr_trans with p2. exact H. exact H1.
      apply cgr_trans with q2. apply cgr_symm. exact H0. exact H3.
    * exists x. exists x0. exists x1. split. apply cgr_trans with p2. exact H. exact H2. apply cgr_trans with q2.
      apply cgr_symm. apply H0. apply H3.
    * exists x. exists x0. exists x1. split. apply cgr_trans with p2. exact H. exact H2. apply cgr_trans with q2.
      apply cgr_symm. apply H0. apply H3.
Qed.


(* For the (LTS-transition), the transitable terms and transitted terms, that performs a INPUT,
are pretty all the same, up to ≡* *)
Lemma TransitionShapeForInput : forall P V c, (lts P (c ?) V -> 
(exists Q M R, ((P ≡* ((c ? • Q) + M) ‖ R)) /\ (V ≡* (Q ‖ R)) /\ ((exists L,P = (g L)) -> R = 𝟘))).
Proof.
intros P V x Transition.
 dependent induction Transition.
- exists p. exists 𝟘. exists 𝟘. split ; try split.
  * apply cgr_trans with ((x ? • p) + 𝟘). apply cgr_trans with (x ? • p). apply cgr_refl. apply cgr_choice_nil_rev. apply cgr_par_nil_rev.
  * apply cgr_par_nil_rev.
  * reflexivity.
- edestruct IHTransition. reflexivity. decompose record H. exists x0. exists x1. exists (x2 ‖ q). split; try split.
  * apply cgr_trans with ((((x ? • x0) + x1) ‖ x2) ‖ q). apply cgr_par. exact H0. apply cgr_par_assoc.
  * apply cgr_trans with ((x0 ‖ x2) ‖ q). apply cgr_par. exact H1. apply cgr_par_assoc.
  * intros. inversion H2. inversion H4.
- edestruct IHTransition. reflexivity. decompose record H. exists x0. exists x1. exists (x2 ‖ p). split; try split.
  * apply cgr_trans with ((((x ? • x0) + x1) ‖ x2) ‖ p). apply cgr_trans with (q1 ‖ p). apply cgr_par_com. apply cgr_par. exact H0. apply cgr_par_assoc.
  * apply cgr_trans with ((x0 ‖ x2) ‖ p). apply cgr_trans with (q2 ‖ p). apply cgr_par_com. apply cgr_par. exact H1. apply cgr_par_assoc.
  * intros. inversion H2. inversion H4.
- edestruct IHTransition. reflexivity. decompose record H. exists x0. exists (x1 + p2). exists 𝟘. split ; try split.
  * apply cgr_trans with ((x ? • x0) + (x1 + p2)). apply cgr_trans with (((x ? • x0) + x1) + p2).
    apply cgr_choice. assert (x2 = 𝟘). apply H3. exists p1. reflexivity. rewrite H2 in H0. apply transitivity with (((x ? • x0) + x1) ‖ 𝟘).
    exact H0. apply cgr_par_nil. apply cgr_choice_assoc. apply cgr_par_nil_rev.
  * assert (x2 = 𝟘). apply H3. exists p1. reflexivity. rewrite H2 in H1. exact H1.
  * reflexivity.
- edestruct IHTransition. reflexivity. decompose record H. exists x0. exists (x1 + p1). exists 𝟘. split; try split.
  * apply cgr_trans with ((x ? • x0) + (x1 + p1)). apply cgr_trans with (((x ? • x0) + x1) + p1).
    apply cgr_trans with (p2 + p1). apply cgr_choice_com. apply cgr_choice. assert (x2 = 𝟘). apply H3. exists p2. reflexivity.
    apply cgr_trans with (((x ? • x0) + x1) ‖ x2). exact H0. rewrite H2. apply cgr_par_nil. apply cgr_choice_assoc. apply cgr_par_nil_rev.
  * assert (x2 = 𝟘). apply H3. exists p2. reflexivity. rewrite <-H2. exact H1.
  * reflexivity.
Qed.

(* For the (LTS-transition), the transitable terms and transitted terms, that performs a OUPUT,
are pretty all the same, up to ≡* *)
Lemma TransitionShapeForOutput : forall P V c, (lts P (c !) V -> 
(exists Q M R, ((P ≡* ((c ! • Q) + M) ‖ R)) /\ (V ≡* (Q ‖ R)) /\ ((exists L,P = (g L)) -> R = 𝟘))).
Proof.
intros P V x Transition.
 dependent induction Transition.
- exists p. exists 𝟘. exists 𝟘. split ; try split.
  * apply cgr_trans with ((x ! • p) + 𝟘). apply cgr_trans with (x ! • p). apply cgr_refl. apply cgr_choice_nil_rev. apply cgr_par_nil_rev.
  * apply cgr_par_nil_rev.
  * reflexivity.
- edestruct IHTransition. reflexivity. decompose record H. exists x0. exists x1. exists (x2 ‖ q). split; try split.
  * apply cgr_trans with ((((x ! • x0) + x1) ‖ x2) ‖ q). apply cgr_par. exact H0. apply cgr_par_assoc.
  * apply cgr_trans with ((x0 ‖ x2) ‖ q). apply cgr_par. exact H1. apply cgr_par_assoc.
  * intros. inversion H2. inversion H4.
- edestruct IHTransition. reflexivity. decompose record H. exists x0. exists x1. exists (x2 ‖ p). split; try split.
  * apply cgr_trans with ((((x ! • x0) + x1) ‖ x2) ‖ p). apply cgr_trans with (q1 ‖ p). apply cgr_par_com. apply cgr_par. exact H0. apply cgr_par_assoc.
  * apply cgr_trans with ((x0 ‖ x2) ‖ p). apply cgr_trans with (q2 ‖ p). apply cgr_par_com. apply cgr_par. exact H1. apply cgr_par_assoc.
  * intros. inversion H2. inversion H4.
- edestruct IHTransition. reflexivity. decompose record H. exists x0. exists (x1 + p2). exists 𝟘. split ; try split.
  * apply cgr_trans with ((x ! • x0) + (x1 + p2)). apply cgr_trans with (((x ! • x0) + x1) + p2).
    apply cgr_choice. assert (x2 = 𝟘). apply H3. exists p1. reflexivity. rewrite H2 in H0. apply transitivity with (((x ! • x0) + x1) ‖ 𝟘).
    exact H0. apply cgr_par_nil. apply cgr_choice_assoc. apply cgr_par_nil_rev.
  * assert (x2 = 𝟘). apply H3. exists p1. reflexivity. rewrite H2 in H1. exact H1.
  * reflexivity.
- edestruct IHTransition. reflexivity. decompose record H. exists x0. exists (x1 + p1). exists 𝟘. split; try split.
  * apply cgr_trans with ((x ! • x0) + (x1 + p1)). apply cgr_trans with (((x ! • x0) + x1) + p1).
    apply cgr_trans with (p2 + p1). apply cgr_choice_com. apply cgr_choice. assert (x2 = 𝟘). apply H3. exists p2. reflexivity.
    apply cgr_trans with (((x ! • x0) + x1) ‖ x2). exact H0. rewrite H2. apply cgr_par_nil. apply cgr_choice_assoc. apply cgr_par_nil_rev.
  * assert (x2 = 𝟘). apply H3. exists p2. reflexivity. rewrite <-H2. exact H1.
  * reflexivity.
Qed.

(* For the (LTS-transition), the transitable Guards and transitted terms, that performs a Tau ,
are pretty all the same, up to ≡* *)
Lemma TransitionShapeForTauAndGuard : forall P V, ((lts P τ V) /\ (exists L, P = (g L))) -> 
(exists Q M, ((P ≡* ((𝛕 • Q) + M))) /\ (V ≡* (Q))).
Proof.
intros P V Hyp.
destruct Hyp. rename H into Transition. dependent induction Transition.
- exists p. exists 𝟘. split. 
  * apply cgr_choice_nil_rev.
  * apply cgr_refl.
- inversion H0. inversion H.
- inversion H0. inversion H.
- inversion H0. inversion H.
- inversion H0. inversion H.
- inversion H0. inversion H.
- edestruct (IHTransition ). reflexivity. exists p1. reflexivity. destruct H. destruct H.  exists x. 
  exists (x0 + p2). split. apply cgr_trans with (((𝛕 • x) + x0) + p2). apply cgr_choice. exact H.
  apply cgr_choice_assoc. exact H1.
- edestruct (IHTransition ). reflexivity. exists p2. reflexivity. destruct H. destruct H.  exists x. 
  exists (x0 + p1). split. apply cgr_trans with (((𝛕 • x) + x0) + p1). apply cgr_trans with (p2 + p1). 
  apply cgr_choice_com. apply cgr_choice. exact H. apply cgr_choice_assoc. exact H1.
Qed.


(* Substition lemma, needed to contextualise the equivalence *)
Lemma cgr_subst1 p q q' x : q ≡* q' → pr_subst x p q ≡* pr_subst x p q'.
Proof.
(* Induction on the size of p*)
induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct p.
  - simpl. intro. apply cgr_fullpar.
    apply Hp. simpl. auto with arith. assumption.
    apply Hp. simpl. auto with arith. assumption.
  - simpl. intro. destruct (decide (x = n)). exact H. reflexivity.
  - simpl. intro. destruct (decide (x = n)). reflexivity. apply cgr_recursion. apply Hp. simpl. auto. exact H.
  - destruct g0.
    * reflexivity.
    * reflexivity.
    * intro. apply cgr_input. apply Hp. simpl. auto. exact H.
    * intro. apply cgr_output. apply Hp. simpl. auto. exact H.
    * intro. apply cgr_tau. apply Hp. simpl. auto. exact H.
    * intro. simpl. apply cgr_fullchoice.
      assert (pr_subst x (g g0_1) q ≡* pr_subst x (g g0_1) q'). apply Hp. simpl. auto with arith. assumption. assumption.
      assert (pr_subst x (g g0_2) q ≡* pr_subst x (g g0_2) q'). apply Hp. simpl. auto with arith. assumption. assumption.
Qed.

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
  - simpl. constructor. apply Hp. subst. simpl. auto. exact H.
  - simpl. constructor. apply Hp. subst. simpl. auto. exact H.
  - simpl. constructor. apply Hp. subst. simpl. auto with arith. assumption.
  - simpl. apply cgr_choice_step.
    assert (pr_subst n (g p1) q ≡ pr_subst n (g q1) q). apply Hp. subst. simpl. auto with arith. assumption. assumption.
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

(* p 'is equivalent some r 'and r performs α to q *)
Definition lts_sc1 p α q := exists r, p ≡* r /\ (lts r α q).

(* p performs α to some r and this is equivalent to q*)
Definition lts_sc p α q := exists r, ((lts p α r) /\ r ≡* q).

(* the structural congruence respects transition *)
Lemma Congruence_Respects_Transition : forall p q α, lts_sc1 p α q -> lts_sc p α q.
Proof.
(* by induction on the congruence and the step then...*)
  intros p q α (p' & hcgr & l).
  revert q α l.
  dependent induction hcgr.
  - dependent induction H.
(* reasonning about all possible cases due to the structure of terms *)
    + intros. exists q.  split.  exact l. reflexivity. 
    + intros. exists (q ‖ 𝟘). split. apply lts_parL. exact l. auto with cgr (*par contexte parallele*). 
    + intros. dependent destruction l. inversion l2. inversion l1. exists p2. split. exact l. auto with cgr. 
      inversion l.
    + intros. dependent destruction l.
      -- exists (q2 ‖ p2). split. eapply lts_comR. instantiate (1:= a). exact l1. exact l2. auto with cgr.
      -- exists (p2 ‖ q2). split. eapply lts_comL. instantiate (1:= a). exact l1. exact l2. auto with cgr.
      -- exists (p ‖ p2). split. apply lts_parR. exact l. auto with cgr.
      -- exists (q2 ‖ q). split. apply lts_parL. exact l. auto with cgr.
    + intros. dependent destruction l.
      -- dependent destruction l2.
         * exists ((p2 ‖ p0) ‖ r). split.
           apply lts_parL. eapply lts_comL. instantiate (1:= a). exact l1. exact l2. auto with cgr.
         * exists ((p2 ‖ q) ‖ q2). split. eapply lts_comL. instantiate (1:= a). apply lts_parL. exact l1.
           exact l2. apply cgr_par_assoc.
      -- dependent destruction l1.
         * exists ((q2 ‖ p2) ‖ r). split. apply lts_parL. eapply lts_comR. instantiate (1:= a). exact l1.
           exact l2. auto with cgr.
         * exists ((q2 ‖ q) ‖ q0). split. eapply lts_comR. instantiate (1:= a). exact l1. apply lts_parL.
           exact l2. auto with cgr.
      -- exists ((p2 ‖ q) ‖ r). split. apply lts_parL. apply lts_parL. exact l. auto with cgr.
      -- dependent destruction l.
         * exists ((p ‖ p2) ‖ q2). split. eapply lts_comL. instantiate (1:= a). apply lts_parR. exact l1.
           exact l2. auto with cgr.
         * exists ((p ‖ q2) ‖ p2). split. eapply lts_comR. instantiate (1:= a). exact l1. apply lts_parR.
           exact l2. auto with cgr.
         * exists ((p ‖ p2) ‖ r). split. apply lts_parL. apply lts_parR. exact l. auto with cgr.
         * exists ((p ‖ q) ‖ q2). split. apply lts_parR. exact l. auto with cgr.
    + intros. dependent destruction l.
      -- dependent destruction l1.
         * exists (p2 ‖ (q ‖ q2)). split.
           eapply lts_comL. instantiate (1:= a). exact l1. apply lts_parR. exact l2. auto with cgr.
         * exists (p ‖ (q0 ‖ q2)). split. apply lts_parR. eapply lts_comL. instantiate (1:= a). exact l1.
           exact l2. auto with cgr.
      -- dependent destruction l2.
         * exists (p0 ‖ (q ‖ p2)). split. eapply lts_comR. instantiate (1:= a). apply lts_parR.  exact l1.
           exact l2. auto with cgr.
         * exists (p ‖ (q2 ‖ p2)). split. apply lts_parR. eapply lts_comR. instantiate (1:= a). exact l1.
           exact l2. auto with cgr.
      -- dependent destruction l.
         * exists (p2 ‖ (q2 ‖ r)). split. eapply lts_comL. instantiate (1:= a).  exact l1. apply lts_parL.
           exact l2. auto with cgr.
         * exists (q2 ‖ (p2 ‖ r)). split. eapply lts_comR. instantiate (1:= a). apply lts_parL. exact l1.
           exact l2. auto with cgr.
         * exists (p2 ‖( q ‖ r)). split. apply lts_parL. exact l. auto with cgr.
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
    + intros. dependent destruction l. exists (pr_subst x p (pr_rec x p)). split. apply lts_rec.
      apply cgr_subst. exact H.
    + intros. dependent destruction l. exists p.  split. apply lts_tau. constructor. exact H.
    + intros. dependent destruction l. exists p. split. apply lts_input. constructor. apply H.
    + intros. dependent destruction l. exists p. split. apply lts_output. constructor. apply H.
    + intros. dependent destruction l.
      -- destruct (IHcgr_step p2 (ActExt (ActOut a))). exact l1. exists (x ‖ q2). split. eapply lts_comL. destruct H0. exact l.
         exact l2. destruct H0. auto with cgr.
      -- destruct (IHcgr_step q2 (ActExt (ActIn a))). exact l2. exists (x ‖ p2). split. eapply lts_comR. destruct H0. exact l1.
         destruct H0.  exact H0. destruct H0. auto with cgr.
      -- destruct (IHcgr_step p2 α). exact l. destruct H0. exists (x ‖ r). split. apply lts_parL. exact H0. auto with cgr.
      -- exists (p ‖ q2). split. apply lts_parR. exact l. apply cgr_par. constructor. exact H.
    + intros. dependent destruction l.
      -- destruct (IHcgr_step q α). exact l. destruct H0. exists x. split. apply lts_choiceL. exact H0. exact H1.
      -- exists q. split. apply lts_choiceR. exact l. auto with cgr.
  - intros. destruct (IHhcgr2 q α). exact l. destruct (IHhcgr1 x0 α). destruct H. exact H. exists x1. split. destruct H0. exact H0.
    destruct H. destruct H0. eauto with cgr.
Qed.

(* One side of the Harmony Lemma *)
Lemma Reduction_Implies_TausAndCong : forall P Q, (sts P Q) -> (lts_sc P τ Q).
Proof.
intros P Q Reduction.
assert (((exists x P1 P2 M1 M2 S, ((P ≡* (((x ! • P1) + M1) ‖ ((x ? • P2) + M2)) ‖ S)) /\ (Q ≡* ((P1 ‖ P2) ‖ S)))
\/ (exists P1 M1 S, (P ≡* (((𝛕 • P1) + M1) ‖ S)) /\ (Q ≡* (P1 ‖ S)))
\/ (exists n P1 S, (P ≡* ((rec n • P1) ‖ S)) /\ (Q ≡* (pr_subst n P1 (rec n • P1) ‖ S))))). 
apply ReductionShape. exact Reduction. destruct H.

(*First case τ by communication *)

- decompose record H. assert (lts ((((x ! • x0) + x2) ‖ ((x ? • x1) + x3)) ‖ x4) τ ((x0 ‖ x1) ‖ x4)).
  * apply lts_parL. eapply lts_comL. apply lts_choiceL. instantiate (1:= x). apply lts_output. apply lts_choiceL. apply lts_input.
  * assert (lts_sc1 P τ ((x0 ‖ x1) ‖ x4)). exists ((((x ! • x0) + x2) ‖ ((x ? • x1) + x3)) ‖ x4). split. exact H0. exact H1.
    assert (lts_sc P τ ((x0 ‖ x1) ‖ x4)). apply Congruence_Respects_Transition. exact H3. destruct H4. destruct H4.
    exists x5. split. exact H4. apply transitivity with ((x0 ‖ x1) ‖ x4). exact H5. symmetry. exact H2.

- destruct H.

(*Second case τ by Tau Action *)

  * decompose record H. assert (lts ((𝛕 • x + x0) ‖ x1) τ (x ‖ x1)). constructor. apply lts_choiceL. apply lts_tau.  
    assert (lts_sc1 P τ (x ‖ x1)). exists ((𝛕 • x + x0) ‖ x1). split. exact H1. exact H0.
    assert (lts_sc P τ (x ‖ x1)). apply Congruence_Respects_Transition. exact H3. destruct H4. destruct H4. 
    exists x2. split. exact H4. apply transitivity with (x ‖ x1). exact H5. symmetry. exact H2.

(*Third case τ by rec *)
  * decompose record H. assert (lts (rec x • x0 ‖ x1) τ (pr_subst x x0 (rec x • x0) ‖ x1)). constructor. apply lts_rec.
    assert (lts_sc1 P τ ((pr_subst x x0 (rec x • x0) ‖ x1))). exists (rec x • x0 ‖ x1). split. exact H1. exact H0.
    assert (lts_sc P τ (pr_subst x x0 (rec x • x0) ‖ x1)). apply Congruence_Respects_Transition. exact H3. destruct H4. destruct H4.
    exists x2. split. exact H4. apply transitivity with (pr_subst x x0 (rec x • x0) ‖ x1). exact H5. symmetry. exact H2.
Qed.


(* The More Stronger Harmony Lemma (in one side) is more stronger *)
Lemma Congruence_Simplicity : (forall α , ((forall P Q, (((lts P α Q) -> (sts P Q)))) -> (forall P Q, ((lts_sc P α Q) -> (sts P Q))))).
Proof.
intros. destruct H0. destruct H0. eapply sts_cong. instantiate (1:=P). apply cgr_refl. instantiate (1:=x). apply H. exact H0.
exact H1.
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


Lemma Taus_Implies_Reduction : forall P Q, (lts P τ Q) -> (sts P Q).
Proof.
intros.
dependent induction H.
  - eapply sts_cong. instantiate (1:=  ((𝛕 • p) + 𝟘)). apply cgr_choice_nil_rev. instantiate (1:=p).
    apply sts_tau. apply cgr_refl.
  - apply sts_rec.
  - destruct (TransitionShapeForOutput p1 p2 a). exact H. destruct H1. destruct H1. destruct H1. destruct H2.
    destruct (TransitionShapeForInput q1 q2 a). exact H0. destruct H4. destruct H4. destruct H4. destruct H5.
    eapply sts_cong. instantiate (1:=(((a ! • x) + x0) ‖ ((a ? • x2) + x3)) ‖ (x1 ‖ x4)).
    apply cgr_trans with ((((a ! • x) + x0) ‖ x1) ‖ (((a ? • x2) + x3) ‖ x4)). apply cgr_fullpar. exact H1. exact H4.
    apply InversionParallele.
    instantiate (1 := (x ‖ x2) ‖ (x1 ‖ x4)). apply sts_par. apply sts_com.
    apply transitivity with ((x ‖ x1) ‖ (x2 ‖ x4)). apply InversionParallele. apply cgr_fullpar.
    symmetry. exact H2. symmetry. exact H5.
  - destruct (TransitionShapeForOutput p1 p2 a). exact H. destruct H1. destruct H1. destruct H1. destruct H2.
    destruct (TransitionShapeForInput q1 q2 a). exact H0. destruct H4. destruct H4. destruct H4. destruct H5.
    eapply sts_cong. instantiate (1:=(((a ! • x) + x0) ‖ ((a ? • x2) + x3)) ‖ (x1 ‖ x4)).
    apply transitivity with (p1 ‖ q1). apply cgr_par_com.
    apply transitivity with ((((a ! • x) + x0) ‖ x1) ‖ (((a ? • x2) + x3) ‖ x4)).
    apply cgr_fullpar. exact H1. exact H4. apply InversionParallele.
    instantiate (1 := (x ‖ x2) ‖ (x1 ‖ x4)). apply sts_par. apply sts_com.
    apply transitivity with ((x ‖ x1) ‖ (x2 ‖ x4)). apply InversionParallele. apply transitivity with (p2 ‖ q2). apply cgr_fullpar.
    symmetry. exact H2. symmetry. exact H5. apply cgr_par_com.
- apply sts_par. apply IHlts. reflexivity.
- eapply sts_cong. instantiate (1:= q1 ‖ p). apply cgr_par_com. instantiate (1:= q2 ‖ p).
  apply sts_par. apply IHlts. reflexivity. apply cgr_par_com.
- destruct (TransitionShapeForTauAndGuard (g p1) q). split. exact H. exists p1. reflexivity.
  destruct H0. destruct H0. eapply sts_cong. instantiate (1:= (((𝛕 • x) + (x0 + p2)))).
  apply transitivity with (g (((𝛕 • x) + x0 ) + p2)). apply cgr_choice. exact H0. apply cgr_choice_assoc.
  instantiate (1:= x). apply sts_tau. symmetry. exact H1.
- destruct (TransitionShapeForTauAndGuard (g p2) q). split. exact H. exists p2. reflexivity.
  destruct H0. destruct H0. eapply sts_cong. instantiate (1:= (((𝛕 • x) + (x0 + p1)))).
  apply transitivity with (g (((𝛕 • x) + x0 ) + p1)). apply transitivity with (g (p2 + p1)). apply cgr_choice_com.
  apply cgr_choice. exact H0. apply cgr_choice_assoc. instantiate (1:= x). apply sts_tau. symmetry. exact H1.
Qed.

(* One side of the Harmony Lemma*)
Lemma TausAndCong_Implies_Reduction: forall P Q, (lts_sc P τ Q) -> (sts P Q).
Proof.
intros P Q H.
apply Congruence_Simplicity with τ. exact Taus_Implies_Reduction. exact H.
Qed.

Theorem HarmonyLemmaForCCS : forall P Q, (lts_sc P τ Q) <-> (sts P Q).
Proof.
intros. split.
* apply TausAndCong_Implies_Reduction.
* apply Reduction_Implies_TausAndCong.
Qed.


(* Definition encode_ExtAct_Channel (a : ExtAct Channel) : 
    gen_tree (nat + Channel) :=
match a with
  | ActIn a => GenNode 0 [encode_Channel a]
  | ActOut a => GenNode 1 [encode_Channel a]
end.

Definition decode_ExtAct_Channel_raw (tree :gen_tree (nat + (Channel + Data))) 
  : option (ExtAct (option Channel)) :=
match tree with
  | GenNode 0 [l] => Some (ActIn (decode_Channel l))
  | GenNode 1 [l] => Some (ActOut (decode_Channel l))
  | _ => None
end.

Definition simpl_option (a : option (ExtAct (option Channel)))
  : option (ExtAct Channel) :=
match a with
  | Some (ActIn None) => None
  | Some (ActIn (Some b)) => Some (ActIn b)
  | Some (ActOut None) => None
  | Some (ActOut (Some b)) => Some (ActOut b)
  | None => None
end.

Definition decode_ExtAct_Channel (tree :gen_tree (nat + (Channel + Data))) 
  : option (ExtAct Channel) := simpl_option (decode_ExtAct_Channel_raw tree).

Lemma encode_decide_ExtAct_Channel a : 
  decode_ExtAct_Channel (encode_ExtAct_Channel  a) = Some a.
Proof. 
induction a. 
* unfold decode_ExtAct_Channel. simpl.
  rewrite encode_decide_Channel. eauto.
* unfold decode_ExtAct_Channel. simpl.
  rewrite encode_decide_Channel. eauto.
Qed.


#[global] Instance ExtAct_Channel_countable : Countable (ExtAct Channel).
Proof.
  eapply inj_countable with encode_ExtAct_Channel decode_ExtAct_Channel. 
  intro. apply encode_decide_ExtAct_Channel.
Qed.
 *)

Fixpoint proc_dec (x y : proc) : { x = y } + { x <> y }
with gproc_dec (x y : gproc) : { x = y } + { x <> y }.
Proof.
decide equality. 
* destruct (decide(n = n0));eauto.
* destruct (decide(n = n0));eauto.
* decide equality ; destruct (decide(c = c0));eauto.
Qed.

#[global] Instance proc_eqdecision : EqDecision proc. by exact proc_dec. Defined.


Fixpoint encode_proc (p: proc) : gen_tree (nat + Channel) :=
  match p with
  | p ‖ q  => GenNode 0 [encode_proc p; encode_proc q]
  | pr_var i => GenNode 2 [GenLeaf $ inl i]
  | rec x • P => GenNode 3 [GenLeaf $ inl x; encode_proc P]
  | g gp => GenNode 1 [encode_gproc gp]
  end
with
encode_gproc (gp: gproc) : gen_tree (nat + Channel) :=
  match gp with
  | ① => GenNode 1 []
  | 𝟘 => GenNode 0 []
  | c ? • p => GenNode 2 [GenLeaf (inr $ c); encode_proc p]
  | c ! • p  => GenNode 5 [GenLeaf (inr $ c); encode_proc p]
  | 𝛕 • p => GenNode 3 [encode_proc p]
  | gp + gq => GenNode 4 [encode_gproc gp; encode_gproc gq]
  end.

Fixpoint decode_proc (t': gen_tree (nat + Channel)) : proc :=
  match t' with
  | GenNode 0 [ep; eq] => (decode_proc ep) ‖ (decode_proc eq)
  | GenNode 2 [GenLeaf (inl i)] => pr_var i 
  | GenNode 3 [GenLeaf (inl i); egq] => rec i • (decode_proc egq)
  | GenNode 1 [egp] => g (decode_gproc egp) 
  | _ => ① 
  end
with
decode_gproc (t': gen_tree (nat + Channel)): gproc :=
  match t' with
  | GenNode 1 [] => ① 
  | GenNode 0 [] => 𝟘 
  | GenNode 2 [GenLeaf (inr c); ep] => c ? • (decode_proc ep)
  | GenNode 5 [GenLeaf (inr c) ; ep] => c ! • (decode_proc ep)
  | GenNode 3 [eq] => 𝛕 • (decode_proc eq)
  | GenNode 4 [egp; egq] => (decode_gproc egp) + (decode_gproc egq)
  | _ => ① 
  end.

Lemma encode_decide_procs p : decode_proc (encode_proc p) = p
with encode_decide_gprocs p : decode_gproc (encode_gproc p) = p.
Proof. all: case p. 
* intros. simpl. rewrite (encode_decide_procs p0). rewrite (encode_decide_procs p1). reflexivity.
* intros. simpl. reflexivity.
* intros. simpl. rewrite (encode_decide_procs p0). reflexivity.
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

Fixpoint moutputs_of_g (gp : gproc) : gmultiset Channel :=
  match gp with
  | ① => ∅
  | 𝟘 => ∅
  | c ?  • p => ∅
  | c !  • p => {[+ c +]}
  | 𝛕 • p => ∅
  | g1 + g2 => moutputs_of_g g1 ⊎ moutputs_of_g g2
  end.


Fixpoint moutputs_of p : gmultiset Channel := 
match p with
  | P ‖ Q => (moutputs_of P) ⊎ (moutputs_of Q)
  | pr_var _ => ∅
  | rec _ • _ => ∅
  | g p => moutputs_of_g p
end.

Definition outputs_of p := dom (moutputs_of p).

Lemma mo_equiv_spec_step : forall {p q}, p ≡ q -> moutputs_of p = moutputs_of q.
Proof. intros. dependent induction H ; try multiset_solver; simpl in *; try rewrite H; eauto. Qed.

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
    + unfold moutputs_of in mem.
      remember g0.
      dependent induction g0; rewrite Heqg1 in mem; simpl in *.
      ++ exfalso;inversion mem.
      ++ exfalso;inversion mem.
      ++ exfalso;inversion mem.
      ++ subst. assert (a = c). multiset_solver. subst. eauto with ccs.
      ++ exfalso;inversion mem.
      ++ destruct (decide (a ∈ moutputs_of g0_2)) as [mem_right | not_mem_right].
         +++ destruct (IHg0_2 a g0_2) as (e2' & lts__e2); eauto.
             exists e2'. rewrite Heqg1. repeat split; eauto with ccs.
         +++ destruct (decide (a ∈ moutputs_of g0_1)) as [mem_left | not_mem_left].
             ++++ destruct (IHg0_1 a g0_1) as (e1' & lts__e1); eauto.
                  exists e1'. rewrite Heqg1. repeat split; eauto with ccs.
             ++++ exfalso. multiset_solver.
Qed.

Lemma mo_spec_r p a :
  {p' | lts p (ActExt $ ActOut a) p'} -> a ∈ moutputs_of p.
Proof.
    induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros (e' & l).
  inversion l; subst.
  + simpl. multiset_solver.
  + simpl. eapply gmultiset_elem_of_disj_union. left.
    eapply (Hp p1). simpl. lia. exists p2. eauto.
  + simpl. eapply gmultiset_elem_of_disj_union. right.
    eapply (Hp q1). simpl. lia. exists q2. eauto.
  + simpl. eapply gmultiset_elem_of_disj_union. left.
    eapply (Hp p1). simpl. lia. exists e'. eauto.
  + simpl. eapply gmultiset_elem_of_disj_union. right.
    eapply (Hp p2). simpl. lia. exists e'. eauto.
Qed.


Lemma outputs_of_spec2 p a : a ∈ outputs_of p -> {q | lts p (ActExt (ActOut a)) q}.
Proof.
  intros mem.
  eapply gmultiset_elem_of_dom in mem.
  eapply mo_spec_l in mem.
  firstorder.
Qed.

Lemma outputs_of_spec1 (p : proc) (a : Channel) (q : proc) : lts p (ActExt (ActOut a)) q
      -> a ∈ outputs_of p.
Proof.
intros. eapply gmultiset_elem_of_dom. eapply mo_spec_r. eauto.
Qed.

Fixpoint lts_set_output_g (g : gproc) (a : Channel) : gset proc :=
  match g with
  | ① => ∅
  | 𝟘 => ∅
  | c ? • p => ∅
  | c ! • p => if decide(a = c) then {[ p ]} else ∅
  | 𝛕 • p => ∅
  | g1 + g2 => lts_set_output_g g1 a ∪ lts_set_output_g g2 a
  end.

Fixpoint lts_set_output (p : proc) (a : Channel) : gset proc:=
match p with
  | p1 ‖ p2 => 
      let ps1 := lts_set_output p1 a in
      let ps2 := lts_set_output p2 a in
      (* fixme: find a way to map over sets. *)
      list_to_set (map (fun p => p ‖ p2) (elements ps1)) ∪ list_to_set (map (fun p => p1 ‖ p) (elements ps2))
  | pr_var _ => ∅
  | rec _ • _ => ∅
  | g gp  => lts_set_output_g gp a
end.

Fixpoint lts_set_input_g (g : gproc) (a : Channel) : gset proc :=
 match g with
  | ① => ∅
  | 𝟘 => ∅
  | c' ? • p => if decide (a = c') then {[ p ]} else ∅
  | c' ! • p => ∅
  | 𝛕 • p => ∅
  | g1 + g2 => lts_set_input_g g1 a ∪ lts_set_input_g g2 a
  end.


Fixpoint lts_set_input (p : proc) (a : Channel) : gset proc :=
match p with
  | p1 ‖ p2 =>
      let ps1 := lts_set_input p1 a in
      let ps2 := lts_set_input p2 a in
      list_to_set (map (fun p => p ‖ p2) (elements ps1)) ∪ list_to_set (map (fun p => p1 ‖ p) (elements ps2))
  | pr_var _ => ∅
  | rec _ • _ => ∅ 
  | g gp => lts_set_input_g gp a  
  end.


Fixpoint lts_set_tau_g (gp : gproc) : gset proc :=
match gp with
  | ① => ∅
  | 𝟘 => ∅
  | c ? • p => ∅
  | c ! • p => ∅
  | 𝛕 • p => {[ p ]}
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
  - destruct g0; simpl in mem;  try now inversion mem.
    + destruct (decide (a = c)); subst.
          +++ subst. assert (q = p). set_solver. subst. eauto with ccs.
          +++ inversion mem.
    + eapply elem_of_union in mem as [mem | mem].
      ++ eapply lts_choiceL.
         eapply Hp. simpl; lia. eauto.
      ++ eapply lts_choiceR.
         eapply Hp. simpl; lia. eauto.
Qed.

Lemma lts_set_output_spec1 p a q : lts p (ActExt $ ActOut a) q -> q ∈ lts_set_output p a.
Proof.
  intro l. dependent induction l; try set_solver.
  - simpl. rewrite decide_True; eauto. set_solver.
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
  + dependent induction g0; simpl in mem; try set_solver.
      ++ destruct (decide (a = c)).
         +++ subst. eapply elem_of_singleton_1 in mem. subst. apply lts_input.
         +++ inversion mem.
      ++ eapply elem_of_union in mem. destruct mem; eauto with ccs.
Qed.

Lemma lts_set_input_spec1 p a q : lts p (ActExt $ ActIn a) q -> q ∈ lts_set_input p a.
Proof.
  intro l. dependent induction l; try set_solver. simpl. rewrite decide_True; eauto with set_solver.
Qed.

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
         eapply lts_set_input_spec0 in mem2. eapply lts_comL. exact mem1. exact mem2.
      ++ eapply elem_of_list_to_set, list_elem_of_In, in_flat_map in mem2 as (t' & eq & h); subst.
         eapply list_elem_of_In, list_elem_of_fmap in h as ((t1 & t2) & eq' & h'). subst.
         eapply list_elem_of_In, in_prod_iff in h' as (mem1 & mem2).
         eapply list_elem_of_In in mem1. rewrite elem_of_elements in mem1.
         eapply list_elem_of_In in mem2. rewrite elem_of_elements in mem2.
         eapply lts_set_input_spec0 in mem1.
         eapply lts_set_output_spec0 in mem2. eapply lts_comR. exact mem2. exact mem1.
    + inversion mem.
    + eapply elem_of_singleton_1 in mem. subst; eauto with ccs.
    + dependent induction g0; simpl in mem; try set_solver;
        try eapply elem_of_singleton_1 in mem; subst; eauto with ccs.
      eapply elem_of_union in mem as [mem1 | mem2]; eauto with ccs.
Qed.

Lemma lts_set_tau_spec1 p q : lts p τ q -> q ∈ lts_set_tau p.
Proof. 
  intro l. dependent induction l; simpl; try set_solver.
  - eapply elem_of_union. left.
    eapply elem_of_union. right.
    eapply elem_of_list_to_set.
    rewrite list_elem_of_In. rewrite in_flat_map.
    exists a. split.
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
    exists a. split.
    + eapply list_elem_of_In, elem_of_elements.
      eapply outputs_of_spec1. exact l1.
    + eapply list_elem_of_In, list_elem_of_fmap.
      exists (q2 , p2). split.
      ++ reflexivity.
      ++ eapply list_elem_of_In, in_prod_iff; split; eapply list_elem_of_In, elem_of_elements.
         eapply lts_set_input_spec1; eauto with ccs.
         eapply lts_set_output_spec1; eauto with ccs.
Qed.

Definition lts_set (p : proc) (α : ActIO Channel): gset proc :=
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

From TestingTheory Require Import OldTransitionSystems.

#[global] Program Instance CCS_Label : Label Channel.

#[global] Program Instance CCS_Lts : Lts proc Channel := 
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

#[global] Program Instance CCS_LtsEq : LtsEq proc Channel := 
  {| eq_rel x y  := cgr x y;
     eq_rel_refl p := cgr_refl p;
     eq_symm p q := cgr_symm p q;
     eq_trans x y z:= cgr_trans x y z;
     eq_spec p q α := Congruence_Respects_Transition p q α |}.

From TestingTheory Require Import gLts Bisimulation Lts_OBA Lts_FW Lts_OBA_FB 
  FiniteImageLTS Lts_Finite_Output_Chain GeneralizeLtsOutputs.

#[global] Program Instance CCS_ggLts : @gLts proc (ExtAct Channel) gLabel_b := ggLts gLabel_b.

#[global] Program Instance CCS_ggLtsEq : @gLtsEq proc (ExtAct Channel) gLabel_b:= 
  ggLtsEq gLabel_b.

#[global] Program Instance CCS_gLtsOBA : @gLtsOba proc (ExtAct Channel) gLabel_b CCS_ggLtsEq := ggLtsOba_b.

#[global] Program Instance CCS_gLtsOBAFB : gLtsObaFB proc (ExtAct Channel) := ggLtsObaFB_b.

#[global] Program Instance CCS_gLtsOBAFW : gLtsObaFW proc (ExtAct Channel) := ggLtsObaFW_b.

#[global] Instance CCS_finite : FiniteLts proc Channel.
Proof.
  constructor; [apply _|]. intros p ℓ. unfold dsig.
  destruct ℓ as [[a|a]|].
  - eapply (in_list_finite (elements (lts_set_input p a))).
    intros q Htrans%bool_decide_unpack.
    now eapply elem_of_elements, lts_set_input_spec1.
  - eapply (in_list_finite (elements (lts_set_output p a))).
    intros q Htrans%bool_decide_unpack.
    now eapply elem_of_elements, lts_set_output_spec1.
  - eapply (in_list_finite (elements (lts_set_tau p))).
    intros q Htrans%bool_decide_unpack.
    now eapply elem_of_elements, lts_set_tau_spec1.
Defined.

#[global] Program Instance ACCS_gLtsFiniteImage :
  @FiniteImagegLts proc (ExtAct Channel) gLabel_b CCS_ggLts := ggFiniteLts gLabel_b.

From TestingTheory Require Import InteractionBetweenLts ParallelLTSConstruction 
gLts Lts_OBA Lts_FW Lts_OBA_FB GeneralizeLtsOutputs
  ForwarderConstruction MultisetLTSConstruction FiniteImageLTS.

#[global] Program Instance Interaction_between_parallel_CCS :
  @Prop_of_Inter proc proc (ExtAct Channel) dual gLabel_b
  CCS_ggLts CCS_ggLts :=  Inter_parallel_IO gLabel_b.
Next Obligation.
  intros μ1 μ2 inter. unfold dual in inter.
  unfold dual in inter. simpl in *. eauto.
Defined.


#[global] Program Instance Interaction_between_MB_and_CCS :
  @Prop_of_Inter proc (@mb (ExtAct Channel) (@gLabel_b Channel CCS_Label))
    (ExtAct Channel) (@fw_inter (ExtAct Channel) (@gLabel_b Channel CCS_Label))
    (@gLabel_b Channel CCS_Label)
    (@ggLts Channel (@gLabel_b Channel CCS_Label) proc _ _)
    (@MbgLts (ExtAct Channel) (@gLabel_b Channel CCS_Label))
  :=  Inter_FW_IO gLabel_b.
Next Obligation.
  intros μ1 μ2 inter. unfold dual in inter. simpl in *. eauto.
Defined.

#[global] Program Instance Interaction_between_FW_CCS_and_CCS :
  Prop_of_Inter (proc * mb (ExtAct Channel)) proc (ExtAct Channel) dual :=  Inter_FW_parallel_IO gLabel_b.
Next Obligation.
  intros μ1 nb. inversion nb.
Defined.

From TestingTheory Require Import Subset_Act.

Inductive CCS_good : proc -> Prop :=
| CCS_good_success : CCS_good ①
| CCS_good_par : forall p q, CCS_good p \/ CCS_good q -> CCS_good (pr_par p q)
| CCS_good_choice : forall p q, CCS_good (g p) \/ CCS_good (g q) -> CCS_good (p + q).

#[global] Hint Constructors CCS_good:ccs.

#[global] Instance CCS_good_decidable e : Decision $ CCS_good e.
Proof.
  dependent induction e; try (now right; inversion 1).
  - destruct IHe1; destruct IHe2; try (now left; eauto with ccs).
    right. inversion 1; naive_solver.
  - dependent induction g0; try (now right; inversion 1); try (now left; eauto with ccs).
    destruct IHg0_1; destruct IHg0_2; try (now left; eauto with ccs).
    right. inversion 1; naive_solver.
Qed.

Lemma CCS_good_preserved_by_cgr_step p q : CCS_good p -> p ≡ q -> CCS_good q.
Proof.
  intros hg hcgr.
  dependent induction hcgr;
    try (inversion hg; subst; destruct H0);
    try (inversion H; subst; destruct H1);
    eauto with ccs.
Qed.

Lemma CCS_good_preserved_by_cgr p q : CCS_good p -> p ≡* q -> CCS_good q.
Proof.
  intros hg hcgr.
  dependent induction hcgr; [eapply CCS_good_preserved_by_cgr_step|]; eauto.
Qed.




(* Lemma CCS_good_preserved_by_output p q a : CCS_good p -> lts p (ActExt $ ActOut a) q -> CCS_good q.
Proof.
  intros hhp hl.
  eapply output_shape in hl.
  eapply (good_preserved_by_cgr p (!a ∥ q)) in hhp; eauto with ccs.
  inversion hhp; subst. destruct H0; eauto with ccs. inversion H.
  now symmetry.
Qed.

Lemma CCS_good_preserved_by_lts_output_converse p q a : lts p (ActExt $ ActOut a) q -> CCS_good q -> CCS_good p.
Proof.
  intros hl hhq.
  eapply output_shape in hl.
  eapply CCS_good_preserved_by_cgr.
  eapply CCS_good_par. right.
  eauto with ccs. eauto with ccs.
Qed.

#[global] Program Instance CCS_Good : @Testing_Predicate proc (ExtAct name) gLabel_nb CCS_good _ (* CCS_lts *) (* CCS_EqLTS *).
Next Obligation. intros. eapply CCS_good_preserved_by_cgr; eassumption. Qed.
Next Obligation. intros. simpl in *. destruct H as (a & eq); subst. eapply CCS_good_preserved_by_output; eassumption. Qed.
Next Obligation. intros. simpl in *. destruct H as (a & eq); subst. eapply CCS_good_preserved_by_lts_output_converse; eassumption. Qed.

Fixpoint gen_test s p :=
  match s with
  | [] => p
  | ActIn a :: s' => gpr_input a (gen_test s' p) ⊕ gpr_tau pr_success
  | ActOut a :: s' => ! a ∥ gen_test s' p
  end.

Lemma gen_test_lts_mu μ s p :
  lts_eq (gen_test (μ :: s) p) (ActExt μ) (gen_test s p).
Proof. intros. destruct μ; simpl; eexists; split; eauto with ccs. Qed.

Lemma gen_test_gen_spec_out_lts_tau_ex s p :
  (exists q, lts p τ q) -> exists e, lts (gen_test s p) τ e.
Proof.
  intros hq. induction s.
  + eauto with ccs.
  + destruct a; subst; simpl; [destruct IHs|destruct IHs]; eexists; eauto with ccs.
Qed.

Lemma gen_test_gen_spec_out_lts_tau_ex_inst a s p :
  exists e', lts (gen_test (ActIn a :: s) p) τ e'.
Proof. simpl. eauto with ccs. Qed.

Lemma gen_test_ungood_if p : ¬ CCS_good p -> forall s, ¬ CCS_good (gen_test s p).
Proof.
  intros nhp s nhg.
  induction s as [|μ s']; simpl in *.
  - contradiction.
  - destruct μ.
    + inversion nhg; subst. destruct H0; inversion H.
    + inversion nhg; subst. destruct H0. inversion H. contradiction.
Qed.

Lemma gen_test_gen_spec_inp_lts_tau_good a s e p :
  lts (gen_test (ActIn a :: s) p) τ e -> CCS_good e.
Proof.
  inversion 1; subst; inversion H4; subst; eauto with ccs.
Qed.

Lemma gen_test_gen_spec_inp_lts_mu_uniq e a μ s p :
  lts (gen_test (ActIn a :: s) p) (ActExt $ μ) e -> e = gen_test s p /\ μ = ActIn a.
Proof.
  intros. inversion H; subst; inversion H4; subst; eauto.
Qed.

Definition gen_conv s := gen_test s (pr_tau pr_success).

From TestingTheory Require Import gLts InputOutputActions Bisimulation.

#[global] Instance dec_output μ : Decision (∃ a : name, ActOut a = μ).
Proof.
  destruct μ.
  + right. intros (a' & eq). inversion eq. 
  + left. exists a; eauto.
Defined.

#[global] Program Instance gen_conv_gen_test_inst : @test_spec proc (ExtAct name) gLabel_nb _ _ CCS_Good gen_conv.
Next Obligation.
  intros. eapply gen_test_ungood_if.
  intro imp. inversion imp.
Qed.
Next Obligation.
  intros. eapply gen_test_lts_mu.
Qed.
Next Obligation.
  intros. case_eq β.
  + intros. rewrite H0 in H.
    eapply gen_test_gen_spec_out_lts_tau_ex_inst.
  + intros. exfalso.
    eapply H. exists a ; eauto.
Qed.
Next Obligation.
  intros. case_eq β.
  + intros. rewrite H1 in H0.
    eapply gen_test_gen_spec_inp_lts_tau_good;eauto.
  + intros. exfalso.
    eapply H. exists a ; eauto.
Qed.
Next Obligation.
  intros. case_eq β.
  + intros. rewrite H1 in H0. eapply gen_test_gen_spec_inp_lts_mu_uniq in H0 as (eq & eq_act).
    constructor. rewrite eq. eauto. unfold gen_conv. reflexivity.
  + intros. exfalso.
    eapply H. exists a ; eauto.
Qed.
Next Obligation.
  intros. case_eq β.
  + intros. rewrite H2 in H0. eapply gen_test_gen_spec_inp_lts_mu_uniq in H0 as (eq & eq_act).
    subst. contradiction.
  + intros. exfalso.
    eapply H. exists a ; eauto.
Qed.

#[global] Program Instance gen_conv_gen_spec_conv_inst : @test_convergence_spec proc (ExtAct name) gLabel_nb _ _ CCS_Good gen_conv.
Next Obligation.
  intros [a|a]; simpl; unfold proc_stable; cbn; eauto.
Qed.
Next Obligation. cbn. eauto with ccs. Qed.
Next Obligation. intros e l. cbn in l. inversion l; subst; simpl; eauto with ccs. Qed.

Fixpoint unroll_fw (xs : list name) : proc :=
  match xs with
  | [] => pr_nil
  | x :: xs' => pr_input x pr_success ∥ unroll_fw xs'
  end.

Definition FinA := name.

Definition Φ (μ : ExtAct name) : FinA :=
match μ with
| ActIn c => c
| ActOut c => c
end.

From TestingTheory Require Import DefinitionAS.

#[global] Program Instance gAbsAction {A : Type} 
  : @AbsAction (ExtAct name) gLabel_nb proc FinA _ Φ.
Next Obligation.
  intros. destruct μ; destruct μ'.
  - simpl in H1. subst. eapply lts_refuses_spec1 in H2 as (e' & Tr).
    eapply lts_refuses_spec2. eauto.
  - exfalso. eapply H0. exists a0. eauto.
  - exfalso. eapply H. exists a. eauto.
  - exfalso. eapply H. exists a. eauto.
Qed.

Definition PreAct := FinA.

Definition 𝝳 (pre_μ : FinA) : PreAct := pre_μ.

#[global] Program Instance EqPreAct : EqDecision PreAct.

#[global] Program Instance CountaPreAct: Countable PreAct := name_countable'.

Fixpoint  mPreCoAct_of p : gmultiset PreAct := 
match p with
  | pr_par P Q => (mPreCoAct_of P) ⊎ (mPreCoAct_of Q)
  | pr_output c => {[+ c +]}
  | pr_var _ => ∅
  | pr_rec _ _ => ∅
  | g p => ∅
end.

Definition PreCoAct_of p := dom (mPreCoAct_of p).

Definition gen_acc (G : gset PreAct) s := gen_test s (unroll_fw (elements G)).

Lemma unroll_a_eq_perm (xs ys : list name) : xs ≡ₚ ys -> unroll_fw xs ≡* unroll_fw ys.
Proof.
  intro hperm. dependent induction hperm; simpl; eauto with ccs.
  - eapply cgr_par_right; eauto with ccs.
  - transitivity ((pr_input y pr_success ∥ pr_input x pr_success) ∥ unroll_fw l).
    eauto with ccs.
    transitivity ((pr_input x pr_success ∥ pr_input y pr_success) ∥ unroll_fw l).
    eauto with ccs. eauto with ccs.
Qed.

#[global] Program Instance gen_acc_gen_test_inst g : test_spec (fun s => gen_acc g s).
Next Obligation.
  intros G s hh. eapply gen_test_ungood_if; try eassumption.
  intro hh0. induction (elements G).
  - cbn in hh0. inversion hh0.
  - inversion hh0; subst. destruct H0.
    + inversion H.
    + contradiction.
Qed.
Next Obligation.
  intros. eapply gen_test_lts_mu.
Qed.
Next Obligation.
  intros. destruct β. 
  + eapply gen_test_gen_spec_out_lts_tau_ex_inst.
  + exfalso. unfold non_blocking in H. simpl in *.
    unfold non_blocking_output in H. unfold is_output in H.
    eapply H. exists a; eauto.
Qed.
Next Obligation.
  intros. destruct β. 
  + eapply gen_test_gen_spec_inp_lts_tau_good. simpl in H0. eassumption.
  + exfalso. unfold non_blocking in H. simpl in *.
    unfold non_blocking_output in H. unfold is_output in H.
    eapply H. exists a; eauto.
Qed.
Next Obligation.
  intros. destruct β. 
  + simpl in *. eapply gen_test_gen_spec_inp_lts_mu_uniq in H0 as (eq & eq_mu).
    subst. subst. reflexivity.
  + exfalso. unfold non_blocking in H. simpl in *.
    unfold non_blocking_output in H. unfold is_output in H.
    eapply H. exists a; eauto.
Qed.
Next Obligation.
  intros. destruct β.
  + simpl in *. eapply gen_test_gen_spec_inp_lts_mu_uniq in H0 as (eq & eq_mu).
    subst. exfalso. eauto.
  + exfalso. unfold non_blocking in H. simpl in *.
    unfold non_blocking_output in H. unfold is_output in H.
    eapply H. exists a; eauto.
Qed.

Lemma gen_acc_does_not_output : forall g t a, ~ lts (unroll_fw g) (ActExt $ ActOut a) t.
Proof.
  intros g.
  induction g as [| b g'].
  - cbn. intros t a R. inversion R.
  - cbn. intros t a R. inversion R; subst.
    + inversion H3.
    + eapply IHg', H3.
Qed.

Lemma gen_acc_does_not_tau : forall g t, ~ lts (unroll_fw g) τ t.
Proof.
  intros g.
  induction g as [| b g'].
  - cbn. intros t R. inversion R.
  - cbn. intros t R.
    inversion R; subst.
    + inversion H1; subst. cbn in H2.
      eapply gen_acc_does_not_output. eassumption.
    + inversion H3.
    + eapply IHg'. eassumption.
Qed.

Lemma gen_acc_gen_spec_acc_nil_mem_lts_inp G a : a ∈ G
    -> exists r, lts (gen_acc G []) (ActExt $ ActIn a) r.
Proof.
  remember G. revert g0 Heqg0.
  induction G using set_ind_L ; intros g0 Heqg0 mem.
  - subst. inversion mem.
  - rewrite Heqg0 in mem.
   assert (hn : {[x]} ## X) by set_solver.
    destruct (decide (x = a)).
    + subst.
      set (h := elements_disj_union {[a]} X hn).
      cbn. assert (exists t, lts (unroll_fw (a :: elements X)) (ActExt $ ActIn a) t).
      simpl. eauto with ccs.
      destruct H0 as (r & hl).
      edestruct
        (eq_spec 
         (* proc name gLabel_nb CCS_lts CCS_EqLTS *)
        (unroll_fw (elements ({[a]} ∪ X))) r (ActExt $ ActIn a)) as (t & hlt & heqt).
      exists (unroll_fw (a :: elements X)).
      split. eapply unroll_a_eq_perm.
      replace (elements {[a]}) with [a] in h. eauto.
      now rewrite elements_singleton.
      simpl in *. eapply hl. eauto.
    + assert (mem' : a ∈ X) by set_solver.
      edestruct (IHG X eq_refl mem') as (r & hlr); eauto.
      edestruct (eq_spec (unroll_fw (elements ({[x]} ∪ X))) (pr_par (pr_input x pr_success) r) 
        (ActExt $ ActIn a)) as (t & hlt & heqt).
      exists (unroll_fw (x :: elements X)).
      split. eapply unroll_a_eq_perm.
      set (h := elements_disj_union {[x]} X hn).
      replace (elements {[x]}) with [x] in h. eauto.
      now rewrite elements_singleton.
      simpl in *. eauto with ccs. subst. eauto.
Qed.

#[global] Program Instance gen_acc_gen_spec_acc_inst : test_co_acceptance_set_spec PreAct gen_acc (fun x => 𝝳 (Φ x)).
Next Obligation.
  intros g. simpl. unfold proc_stable. cbn.
  remember (lts_set_tau (unroll_fw (elements g))) as ps.
  destruct ps using set_ind_L; eauto.
  assert (mem : x ∈ lts_set_tau (unroll_fw (elements g))) by set_solver.
  eapply lts_set_tau_spec0 in mem.
  now eapply gen_acc_does_not_tau in mem.
Qed.
Next Obligation.
  intros g a nb. inversion nb; subst. inversion nb; subst. inversion H; subst.
  simpl. unfold proc_stable. cbn.
  remember (lts_set_output (unroll_fw (elements g)) x0) as ps.
  destruct ps using set_ind_L; eauto.
  assert (mem : x ∈ lts_set_output (unroll_fw (elements g)) x0) by set_solver.
  eapply lts_set_output_spec0 in mem.
  now eapply gen_acc_does_not_output in mem.
Qed.
Next Obligation.
  intros g.
  induction g using set_ind_L; intros.
  - inversion H0.
  - destruct β. 
    + edestruct (eq_spec (unroll_fw (x :: elements X)) e (ActExt (ActIn a))) as (t & hlt & heqt).
      ++ exists (gen_acc ({[x]} ∪ X) []).
         split.
         +++ eapply unroll_a_eq_perm.
             assert (hn : {[x]} ## X) by set_solver.
             set (h := elements_disj_union {[x]} X hn).
             replace (elements {[x]}) with [x] in h. symmetry. eauto.
             now rewrite elements_singleton.
         +++ eassumption.
      ++ cbn in hlt. inversion hlt; subst.
         +++ inversion H6; subst. set_solver.
         +++ set_solver.
    + exfalso. eapply H0. exists a. eauto.
Qed.
Next Obligation.
  intros. simpl in *. eapply gen_acc_gen_spec_acc_nil_mem_lts_inp in H as (r & tr).
  exists r. exists (ActIn pβ). split; eauto.
Qed.
Next Obligation.
  intros a e' g. revert a e'.
  induction g using set_ind_L; intros a e' nb hl.
  - inversion hl.
  - edestruct
      (eq_spec (unroll_fw (x :: elements X)) e' (ActExt a)) as (t & hlt & heqt).
    ++ exists (gen_acc ({[x]} ∪ X) []).
       split; eauto.
       eapply unroll_a_eq_perm.
       assert (hn : {[x]} ## X) by set_solver.
       set (h := elements_disj_union {[x]} X hn).
       replace (elements {[x]}) with [x] in h
           by now rewrite elements_singleton.
       symmetry. eauto.
    ++ simpl in hlt. inversion hlt; subst.
       +++ inversion H4; subst.
           eapply CCS_good_preserved_by_cgr; try eassumption. eauto with ccs.
       +++ eapply CCS_good_preserved_by_cgr; try eassumption. eauto with ccs.
Qed.

Lemma PreCoEquiv (p : proc) (q : proc) (c : PreAct) : p ≡* q -> c ∈ mPreCoAct_of p -> c ∈ mPreCoAct_of q.
Proof.
  intros eq mem. revert c mem. dependent induction eq.
  + dependent induction H; intros; simpl in *; subst; eauto; try multiset_solver.
  + eauto.
Qed.

#[global] Program Instance gPreExtAction : 
  @PreExtAction proc (ExtAct name) gLabel_nb FinA PreAct EqPreAct CountaPreAct 𝝳 Φ (ggLts gLabel_nb) :=
  {| pre_co_actions_of_fin p := fun pre_μ => (exists μ', pre_μ = Φ μ' /\ 
      μ' ∈ @co_actions_of proc (ExtAct name) (@gLabel_nb name _)
      (@ggLts name (@gLabel_nb name (* VACCS_Label *) _) proc _ CCS_lts) p) ;
     pre_co_actions_of p := PreCoAct_of p ; |}.
Next Obligation.
  intros. left. eauto.
Qed.
Next Obligation.
  intros. exists μ. split ;eauto.
Defined.
Next Obligation.
  intros; simpl in *.
  destruct H as (μ' & eq & mem). subst. destruct μ'.
  + exists (ActIn a). split; eauto.
  + exists (ActOut a). split; eauto.
Qed.
Next Obligation.
  intros. split.
  - intros. destruct H as (μ & eq & mem).
    destruct μ.
    + destruct mem as (μ' & Tr & duo & b). symmetry in duo.
      eapply simplify_match_input in duo. subst.
      eapply lts_refuses_spec1 in Tr as (p' & Tr).
      eapply output_shape in Tr as Eq.
      assert (𝝳 (Φ (ActIn a)) ∈ PreCoAct_of (! a ∥ p')).
      { eapply gmultiset_elem_of_dom. simpl. multiset_solver. }
      eapply gmultiset_elem_of_dom. eapply PreCoEquiv. eauto.
      eapply gmultiset_elem_of_dom. eauto.
    + destruct mem as (μ' & Tr & duo & b).
      destruct b. exists a; eauto.
  - intros; subst. revert H.
    induction p as (p & Hp) using
        (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
    destruct p; intros;  apply gmultiset_elem_of_dom in H; simpl in *.
    + apply gmultiset_elem_of_dom in H. simpl in H. assert (𝝳 pre_μ = n) by set_solver; subst.
      exists (ActIn pre_μ). split.
      * simpl; eauto.
      * exists (ActOut pre_μ). repeat split.
        -- eapply lts_refuses_spec2. exists 𝟘. eapply lts_output.
        -- intro. inversion H0. inversion H1.
    + eapply gmultiset_elem_of_disj_union in H. destruct H.
      * apply gmultiset_elem_of_dom in H. eapply (Hp p1) in H; simpl ; eauto with lia.
        destruct H as (μ & Hyp1 & μ' & Tr & duo & b). subst.
        exists μ. split; simpl; eauto. exists μ'. split. eapply lts_refuses_spec1 in Tr as (p'1 & Tr).
        eapply lts_refuses_spec2. exists (p'1 ∥ p2). constructor. eauto. split; eauto.
      * apply gmultiset_elem_of_dom in H. eapply (Hp p2) in H; simpl ; eauto with lia.
        destruct H as (μ & Hyp1 & μ' & Tr & duo & b). subst.
        exists μ. split; simpl; eauto. exists μ'. split. eapply lts_refuses_spec1 in Tr as (p'2 & Tr).
        eapply lts_refuses_spec2. exists (p1 ∥ p'2). constructor. eauto. split; eauto.
    + simpl in H. inversion H.
    + simpl in H. inversion H.
    + destruct g0.
      * simpl in H. inversion H.
      * simpl in H. inversion H.
      * simpl in H. inversion H.
      * simpl in H. inversion H.
      * simpl in H. inversion H.
Qed.

From TestingTheory Require Import Equivalence MustE FiniteImageLTS. 

Corollary bhv_iff_ctx_CCS (p q : proc) : p ⊑ₘᵤₛₜᵢ q <-> p ≼ₐₛ q.
Proof.
  split.
  - intro Hyp. eapply @equivalence_acc_set_and_must_i; eauto.

    exact ACCS_gLtsFiniteImage. exact ACCS_gLtsFiniteImage. exact ACCS_gLtsOBAFB. exact ACCS_gLtsFiniteImage.
    exact Interaction_between_FW_ACCS_and_ACCS. exact Interaction_between_FW_ACCS_and_ACCS.
    exact (@gAbsAction (ExtAct name)). exact gen_conv_gen_spec_conv_inst . exact gen_acc_gen_spec_acc_inst.

  - intro Hyp. eapply @equivalence_acc_set_and_must_i in Hyp; eauto.

    exact ACCS_gLtsFiniteImage. exact ACCS_gLtsFiniteImage. exact ACCS_gLtsOBAFB. exact ACCS_gLtsFiniteImage.
    exact Interaction_between_FW_ACCS_and_ACCS. exact Interaction_between_FW_ACCS_and_ACCS.
    exact (@gAbsAction (ExtAct name)). exact gen_conv_gen_spec_conv_inst . exact gen_acc_gen_spec_acc_inst.
Qed. *)

*)
