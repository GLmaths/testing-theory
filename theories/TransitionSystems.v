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

From stdpp Require Import base countable list decidable finite gmap gmultiset.

Lemma sig_eq {A} (P : A → Prop) (x y : sig P) :
  proj1_sig x = proj1_sig y → x = y.
Proof.
  destruct x as [x Px]; simpl.
  destruct y as [y Py]; simpl.
  intros ->.
  rewrite (proof_irrelevance _ Px Py); trivial.
Qed.

Section in_list_finite.
  Context `{!EqDecision A}.
  Context {P : A → Prop} `{!∀ x : A, ProofIrrel (P x)} `{∀ x, Decision (P x)}.

  Program Fixpoint Forall_to_sig (l : list A) : Forall P l → list (sig P) :=
    match l as u return Forall P u → list (sig P) with
    | [] => λ _, []
    | a :: l' => λ Hal, (exist P a _) :: Forall_to_sig l' _
    end.
  Next Obligation. intros ??? Hal. inversion Hal. by simplify_eq. Qed.
  Next Obligation. intros ??? Hal. by inversion Hal; simplify_eq. Qed.

  Lemma elem_of_Forall_to_sig_1 l HPl x : x ∈ Forall_to_sig l HPl → `x ∈ l.
  Proof.
    revert HPl; induction l as [|a l IHl]; simpl; intros HPl Hx.
    - by apply elem_of_nil in Hx.
    - apply elem_of_cons; apply elem_of_cons in Hx as [->|]; simpl in *; eauto.
  Qed.


  Lemma elem_of_Forall_to_sig_2 l HPl x :
    x ∈ l → ∃ Hx, x ↾ Hx ∈ Forall_to_sig l HPl.
  Proof.
    revert HPl; induction l as [|a l IHl]; simpl; intros HPl Hx.
    - by apply elem_of_nil in Hx.
    - inversion HPl as [|? ? Ha HPl']; simplify_eq.
      apply elem_of_cons in Hx as [->|]; simpl in *.
      + exists Ha; apply elem_of_cons; left; apply sig_eq; done.
      + edestruct IHl as [Hx Hxl]; first done.
        exists Hx; apply elem_of_cons; eauto.
  Qed.

  Lemma Forall_to_sig_NoDup l HPl : NoDup l → NoDup (Forall_to_sig l HPl).
  Proof.
    revert HPl; induction l as [|a l IHl]; simpl;
      intros HPl; first by constructor.
    inversion 1; inversion HPl; simplify_eq.
    constructor; last by apply IHl.
    intros ?%elem_of_Forall_to_sig_1; done.
  Qed.

  Lemma in_list_finite (l : list A) : (∀ x, P x → x ∈ l) → Finite {x : A | P x}.
  Proof.
    intros Hl.
    assert (Forall P (filter P (remove_dups l))) as Hels.
    { apply Forall_forall. intros ?; rewrite elem_of_list_filter; tauto. }
    refine {| enum := Forall_to_sig (filter P (remove_dups l)) Hels |}.
    - apply Forall_to_sig_NoDup. apply NoDup_filter, NoDup_remove_dups.
    - intros x.
      edestruct (elem_of_Forall_to_sig_2 _ Hels) as [Hx' ?].
      { apply elem_of_list_filter; split; first apply (proj2_sig x).
        apply elem_of_remove_dups, Hl; apply (proj2_sig x). }
      replace x with (`x ↾ Hx'); last by apply sig_eq.
      done.
  Qed.
End in_list_finite.

(** Multiset helpers. *)

Lemma gmultiset_eq_drop_l `{Countable A} (m1 m2 m3 : gmultiset A) : m1 ⊎ m2 = m1 ⊎ m3 -> m2 = m3.
Proof. by multiset_solver. Qed.

Lemma gmultiset_eq_pop_l `{Countable A} (m1 m2 m3 : gmultiset A) : m2 = m3 -> m1 ⊎ m2 = m1 ⊎ m3.
Proof. by multiset_solver. Qed.

Lemma gmultiset_neq_s `{Countable A} (m : gmultiset A) a : m ≠ {[+ a +]} ⊎ m.
Proof. by multiset_solver. Qed.

Lemma gmultiset_mono `{Countable A} (m : gmultiset A) a b : {[+ a +]} ⊎ m = {[+ b +]} ⊎ m -> a = b.
Proof. intros. eapply gmultiset_singleton_subseteq. multiset_solver. Qed.

Lemma gmultiset_elements_singleton_inv `{Countable A} (m : gmultiset A) a :
  elements m = [a] -> m = {[+ a +]}.
Proof.                          (* fixme: find a better way to do this *)
  intros eq.
  induction m using gmultiset_ind.
  + multiset_solver.
  + induction m using gmultiset_ind.
    ++ replace ({[+ x +]} ⊎ ∅) with ({[+ x +]} : gmultiset A) in *.
       assert (a = x); subst.
       eapply gmultiset_elem_of_singleton.
       eapply gmultiset_elem_of_elements. rewrite eq. set_solver.
       set_solver. multiset_solver.
    ++ exfalso.
       assert (length (elements ({[+ x +]} ⊎ ({[+ x0 +]} ⊎ m))) = length [a]) by now rewrite eq.
       rewrite 2 gmultiset_elements_disj_union in H0.
       rewrite 2 gmultiset_elements_singleton in H0.
       simpl in H0. lia.
Qed.

(** Actions  *)
(* 
Definition is_input {A} (μ : ExtAct A) := ∃ a, μ = ActIn a.

Definition are_inputs {A} (s : trace A) := Forall is_input s.
*)

Class ExtAction (A : Type) :=
  MkExtAction {
      extaction_eqdec: EqDecision A;
      extaction_countable: Countable A;
      non_blocking : A -> Prop;
      nb_dec a : Decision (non_blocking a);
      dual : A -> A -> Prop;
      d_dec a b: Decision (dual a b);
      
      lts_oba_fw_non_blocking_duo_spec η μ: non_blocking η -> dual η μ ->  ¬ non_blocking μ ;
      (* sinon chaine infini de n_b_actions avec le fw *)
      
      co : A -> A;
      unique_nb η μ: non_blocking η -> dual η μ -> η = (co μ);
      (* sinon, not finite lts ET en plus construction du fw pas valable *)
      
      (*Extra hypothesis for the moment *)
      duo_sym : Symmetric dual;
      
      exists_duo_nb η : (* non_blocking η ->  *) exists μ, dual η μ; (* que pour dual ?*)
      nb_not_nb η μ1 μ2 : non_blocking η -> dual η μ2 -> dual μ1 μ2 -> non_blocking μ1;
    }.
#[global] Existing Instance extaction_eqdec.
#[global] Existing Instance extaction_countable.
#[global] Existing Instance nb_dec.
#[global] Existing Instance d_dec.
#[global] Existing Instance duo_sym.

Inductive Act (A: Type) :=
| ActExt (μ: A)
| τ
.
Arguments ActExt {_} _.
Arguments τ {_}.

Definition trace A := list A.

#[global] Instance act_eqdec `{EqDecision A} : EqDecision (Act A).
Proof. solve_decision. Defined.

Class Lts (P A : Type) `{ExtAction A} :=
  MkLts {
      lts_step: P → Act A → P → Prop;
      lts_state_eqdec: EqDecision P;

      lts_step_decidable a α b : Decision (lts_step a α b);

      lts_refuses : P → Act A → Prop;
      lts_refuses_decidable p α : Decision (lts_refuses p α);
      lts_refuses_spec1 p α : ¬ lts_refuses p α → { q | lts_step p α q };
      lts_refuses_spec2 p α : { q | lts_step p α q } → ¬ lts_refuses p α;
    }.
#[global] Existing Instance lts_state_eqdec.
#[global] Existing Instance lts_step_decidable.
#[global] Existing Instance lts_refuses_decidable. 

Notation "p ⟶ q"      := (lts_step p τ q) (at level 30, format "p  ⟶  q").
Notation "p ⟶{ α } q" := (lts_step p α q) (at level 30, format "p  ⟶{ α }  q").
Notation "p ⟶[ μ ] q" := (lts_step p (ActExt μ) q) (at level 30, format "p  ⟶[ μ ]  q").

Notation "p ↛"      := (lts_refuses p τ) (at level 30, format "p  ↛").
Notation "p ↛{ α }" := (lts_refuses p α) (at level 30, format "p  ↛{ α }").
Notation "p ↛[ μ ]" := (lts_refuses p (ActExt μ)) (at level 30, format "p  ↛[ μ ]").

Class FiniteImageLts P A `{Lts P A} :=
  MkFlts {
      folts_states_countable: Countable P;
      folts_next_states_finite p α : Finite (dsig (fun q => lts_step p α q));
}.

#[global] Existing Instance folts_states_countable.
#[global] Existing Instance folts_next_states_finite.

Class LtsEq (P A : Type) `{Lts P A} := {
    (* todo: use Equivalence *)
    eq_rel : P -> P -> Prop;
    eq_rel_eq : Equivalence eq_rel;
    (* reference: L 1.4.15 p.51 Sangiorgi pi-book *)
    eq_spec p q (α : Act A) : (exists r, eq_rel p r /\ r ⟶{α} q) -> (exists r, p ⟶{α} r /\ eq_rel r q);
  }.


#[global] Instance rel_equivalence `{LtsEq P A }: Equivalence eq_rel.
  by exact eq_rel_eq.
Defined.
(* Add Parametric Relation `{Lts P A, ! LtsEq P A} : P eq_rel
    reflexivity proved by (eq_rel_refl)
    symmetry proved by (eq_symm)
    transitivity proved by (eq_trans)
    as sc_proc_rel. *)

Infix "⋍" := eq_rel (at level 70).

Definition lts_sc `{Lts P A, !LtsEq P A} p α q := exists r, p ⟶{α} r /\ r ⋍ q.

Notation "p ⟶⋍ q" := (lts_sc p τ q) (at level 30, format "p  ⟶⋍  q").
Notation "p ⟶⋍{ α } q" := (lts_sc p α q) (at level 30, format "p  ⟶⋍{ α }  q").
Notation "p ⟶⋍[ μ ] q" := (lts_sc p (ActExt μ) q) (at level 30, format "p  ⟶⋍[ μ ]  q").

Class LtsOba (P A : Type) `{H : ExtAction A} (* {I : InteractionAction A}   *)
            {M : @Lts P A H} {Rel : @LtsEq P A H M} 
                          (* `{@Prop_of_Inter P A H I M} *)  :=
  MkOBA {
      (* Multiset of outputs *)
      lts_oba_mo (p : P) : gmultiset A;

      (* lts_oba_mo_spec1 p η : η ∈ lts_oba_mo p -> η ∈ lts_essential_actions p; *) 
      (* à rajouter ? *)
      (* lts_non_blocking_action_spec1 p1 η p2 : non_blocking η -> lts_step p1 (ActExt η) p2 -> η ∈ lts_non_blocking_action p1; 
      lts_non_blocking_action_spec2 p1 η : η ∈ lts_non_blocking_action p1 -> {p2 | (non_blocking η /\ lts_step p1 (ActExt η) p2) } ; *)
      lts_oba_mo_spec_bis1 p1 η p2 : non_blocking η -> lts_step p1 (ActExt η) p2 -> η ∈ lts_oba_mo p1; 
      lts_oba_mo_spec_bis2 p1 η : η ∈ lts_oba_mo p1 -> {p2 | (non_blocking η /\ lts_step p1 (ActExt η) p2) } ; 

      (* à remplacer par axiom pas de suite infini de non_blocking ?*)
      lts_oba_mo_spec2 p η : forall q, non_blocking η -> p ⟶[ η ] q 
                    -> lts_oba_mo p = {[+ η +]} ⊎ lts_oba_mo q;

      (* Selinger axioms. *)
      lts_oba_non_blocking_action_delay {p q r η α} :
      non_blocking η -> p ⟶[ η ] q -> q ⟶{ α } r -> (∃ t, p ⟶{α} t /\ t ⟶⋍[ η ] r) ;
      lts_oba_non_blocking_action_confluence {p q1 q2 η μ} :
      non_blocking η -> μ ≠ η -> p ⟶[ η ] q1 -> p ⟶[ μ ] q2 ->
      ∃ r, q1 ⟶[ μ ] r /\ q2 ⟶⋍[ η ] r ; 
      lts_oba_non_blocking_action_tau {p q1 q2 η} :
      non_blocking η -> p ⟶[ η ] q1 -> p ⟶ q2 -> (∃ t, q1 ⟶ t /\ q2 ⟶⋍[ η ] t) \/ (∃ μ, (dual η μ) /\ q1 ⟶⋍[ μ ] q2) ; 
      lts_oba_non_blocking_action_deter {p1 p2 p3 η} :
      non_blocking η -> p1 ⟶[ η ] p2 -> p1 ⟶[ η ] p3 -> p2 ⋍ p3 ;
      (* Extra axiom, it would be nice to remove it, not used that much. *)
      lts_oba_non_blocking_action_deter_inv {p1 p2 q1 q2} η :
      non_blocking η -> p1 ⟶[ η ] q1 -> p2 ⟶[ η ] q2 -> q1 ⋍ q2 -> p1 ⋍ p2
    }.


Class LtsObaFB (P A: Type) `{LtsOba P A} :=
  MkLtsObaFB {
      lts_oba_fb_feedback {p1 p2 p3 η μ} : non_blocking η -> dual η μ -> p1 ⟶[ η ] p2 -> p2 ⟶[ μ ] p3 -> p1 ⟶⋍ p3
    }.

Class LtsObaFW (P A : Type) `{LtsOba P A} :=
  MkLtsObaFW {
      lts_oba_fw_forward p1 η μ : ∃ p2, non_blocking η -> dual η μ -> p1 ⟶[ μ ] p2 /\ p2 ⟶[ η ] p1 ;
      lts_oba_fw_feedback {p1 p2 p3 η μ } : non_blocking η -> dual η μ -> p1 ⟶[ η ] p2 -> p2 ⟶[ μ ] p3 -> p1 ⟶⋍ p3 \/ p1 ⋍ p3 ;
    }.


(* Signification between mailbox and non_blocking *)

Lemma lts_oba_mo_non_blocking_spec1 `{LtsOba P A} {p η} : 
  η ∈ lts_oba_mo p -> non_blocking η.
Proof.
intro Hyp. 
eapply lts_oba_mo_spec_bis2 in Hyp. destruct Hyp as (p2 & nb & tr). assumption.
Qed.

Lemma lts_oba_mo_non_blocking_contra `{LtsOba P A} {p η} : 
  ¬ non_blocking η -> η ∉ lts_oba_mo p.
Proof.
intro NotNB. intro Hyp. eapply lts_oba_mo_non_blocking_spec1 in Hyp. contradiction.
Qed.

Lemma BlockingAction_are_not_non_blocking `{LtsOba P A} {η μ} : 
  non_blocking η -> ¬ non_blocking μ -> μ ≠ η.
Proof.
  intro nb1. intro nb2. intro eq. rewrite eq in nb2. contradiction.
Qed.

(* Inductive definition of terminate. *)

Reserved Notation "p ⤓" (at level 60).

Inductive terminate `{Lts P A} (p : P) : Prop :=
| tstep : (forall q, p ⟶ q -> terminate q) -> terminate p

where "p ⤓" := (terminate p).

Global Hint Constructors terminate:mdb.

Lemma terminate_if_refuses `{Lts P A} p : p ↛ -> p ⤓.
Proof. intro st. constructor. intros q l. exfalso. eapply lts_refuses_spec2; eauto. Qed.

Lemma terminate_preserved_by_lts_tau `{Lts P A} p q : p ⤓ -> p ⟶ q -> q ⤓.
Proof. by inversion 1; eauto. Qed.

Lemma terminate_preserved_by_eq `{LtsEq P A} {p q} : p ⤓ -> p ⋍ q -> q ⤓.
Proof.
  intros ht. revert q.
  induction ht. intros.
  eapply tstep.
  intros q' l.
  edestruct eq_spec as (r & h2 & h3). eauto.
  eapply H3; eauto.
Qed.

Lemma terminate_preserved_by_eq2 `{LtsEq P A} {p q} : p ⋍ q -> p ⤓ -> q ⤓.
Proof. intros. eapply terminate_preserved_by_eq; eauto. Qed.

Lemma terminate_preserved_by_lts_non_blocking_action `{LtsOba P A} {p q η} : 
    non_blocking η  -> p ⟶[ η ] q -> p ⤓ -> q ⤓.
Proof.
  intros nb l ht. revert q η nb l.
  induction ht as [p Hyp1 Hyp2].
  intros q a nb l1.
  eapply tstep. intros q' l2.
  destruct (lts_oba_non_blocking_action_delay nb l1 l2) as (t & l3 & l4); eauto.
  destruct l4 as (q0 & l0 & eq0).
  eapply terminate_preserved_by_eq.
  eapply Hyp2. eapply l3. eapply nb. eapply l0. eassumption.
Qed.

Lemma refuses_tau_preserved_by_lts_non_blocking_action `{LtsOba P A} p q η : 
  non_blocking η -> p ↛ -> p ⟶[ η ] q -> q ↛.
Proof.
  intros nb st l.
  case (lts_refuses_decidable q τ); eauto.
  intro nst. eapply lts_refuses_spec1 in nst as (t & l').
  destruct (lts_oba_non_blocking_action_delay nb l l') as (r & l1 & l2).
  edestruct (lts_refuses_spec2 p τ); eauto with mdb.
Qed.

Lemma lts_different_action_preserved_by_lts_non_blocking_action `{LtsOba P A} p q η μ :
  non_blocking η -> μ ≠ η ->
  (exists t, p ⟶[μ] t) -> p ⟶[η] q -> (exists t, q ⟶[μ] t).
Proof.
  intros nb neq (t & hl1) hl2.
  edestruct (lts_oba_non_blocking_action_confluence nb neq hl2 hl1) as (r & l1 & l2). eauto.
Qed.

Lemma refuses_action_preserved_by_lts_non_blocking_action `{LtsOba P A} p q η μ :
  non_blocking η ->
  p ↛[μ] -> p ⟶[η] q -> q ↛[μ] .
Proof.
  intros nb st l.
  case (lts_refuses_decidable q (ActExt $ μ)); eauto.
  intro nst. eapply lts_refuses_spec1 in nst as (t & l').
  destruct (lts_oba_non_blocking_action_delay nb l l') as (r & l1 & l2).
  edestruct (lts_refuses_spec2 p (ActExt $ μ)); eauto with mdb.
Qed.

Inductive terminate_i`{Lts P A} (p : P) : Prop :=
| t_refuses' : p ↛ -> terminate_i p
| tstep' : (exists p', p ⟶ p') -> (forall q, p ⟶ q -> terminate_i q) -> terminate_i p.

Lemma terminate_i_to_terminate `{LtsP : Lts P A} (p : P) : terminate_i p -> p ⤓.
Proof.
  intro Hyp. induction Hyp as [| p witness spec Ind].
  + eapply terminate_if_refuses. assumption.
  + eapply tstep; eauto.
Qed.

Lemma terminate_to_terminate_i `{LtsP : Lts P A} (p : P) : p ⤓ -> terminate_i p .
Proof.
  intro Hyp. induction Hyp as [p Hyp1 Hyp2].
  destruct (decide (lts_refuses p τ)) as [refuses | not_refuses].
  + eapply t_refuses'. assumption.
  + eapply tstep'. eapply lts_refuses_spec1 in not_refuses. 
    destruct not_refuses as (p' & tr).
    ++ exists p'; eauto.
    ++ intro p'. intro tr. eapply Hyp2. assumption.
Qed.

Lemma terminate_i_equal_terminate' `{LtsP : Lts P A} (p : P) : p ⤓ <-> terminate_i p .
Proof.
  split ; [eapply terminate_to_terminate_i | eapply terminate_i_to_terminate].
Qed.


(* Weak transitions *)

Inductive wt `{Lts P A} : P -> trace A -> P -> Prop :=
| wt_nil p : wt p [] p
| wt_tau s p q t (l : p ⟶ q) (w : wt q s t) : wt p s t
| wt_act μ s p q t (l : p ⟶[μ] q) (w : wt q s t) : wt p (μ :: s) t
.

Global Hint Constructors wt:mdb.

Notation "p ⟹ q" := (wt p [] q) (at level 30).
Notation "p ⟹{ μ } q" := (wt p [μ] q) (at level 30, format "p  ⟹{ μ }  q").
Notation "p ⟹[ s ] q" := (wt p s q) (at level 30, format "p  ⟹[ s ]  q").

Definition wt_sc `{Lts P A, !LtsEq P A} p s q := ∃ r, p ⟹[s] r /\ r ⋍ q.

Notation "p ⟹⋍ q" := (wt_sc p [] q) (at level 30, format "p  ⟹⋍  q").
Notation "p ⟹⋍{ μ } q" := (wt_sc p [μ] q) (at level 30, format "p  ⟹⋍{ μ }  q").
Notation "p ⟹⋍[ s ] q" := (wt_sc p s q) (at level 30, format "p  ⟹⋍[ s ]  q").

Lemma wt_pop `{Lts P A} p q μ s : p ⟹[μ :: s] q -> ∃ t, p ⟹{μ} t /\ t ⟹[s] q.
Proof.
  intro w.
  dependent induction w; eauto with mdb.
  destruct (IHw μ s JMeq_refl) as (r & w1 & w2).
  exists r. eauto with mdb.
Qed.

Lemma wt_concat `{Lts P A} p q r s1 s2 :
  p ⟹[s1] q -> q ⟹[s2] r -> p ⟹[s1 ++ s2] r.
Proof. intros w1 w2. dependent induction w1; simpl; eauto with mdb. Qed.

Lemma wt_push_left `{Lts P A} {p q r μ s} :
  p ⟹{μ} q -> q ⟹[s] r -> p ⟹[μ :: s] r.
Proof.
  intros w1 w2.
  replace (μ :: s) with ([μ] ++ s) by eauto.
  eapply wt_concat; eauto.
Qed.

Lemma wt_split `{Lts P A} p q s1 s2 :
  p ⟹[s1 ++ s2] q -> ∃ r, p ⟹[s1] r /\ r ⟹[s2] q.
Proof.
  revert p q.
  dependent induction s1; intros p q w.
  - eauto with mdb.
  - simpl in w. eapply wt_pop in w as (r & w1 & w2).
    eapply IHs1 in w2 as (r' & w2 & w3).
    exists r'. split. eapply wt_push_left; eauto. assumption.
Qed.

Lemma wt_push_nil_left `{Lts P A} {p q r s} : p ⟹ q -> q ⟹[s] r -> p ⟹[s] r.
Proof. by intros w1 w2; dependent induction w1; eauto with mdb. Qed.

Lemma wt_push_nil_right `{Lts P A} p q r s : p ⟹[s] q -> q ⟹ r -> p ⟹[s] r.
Proof.
  intros w1 w2. replace s with (s ++ ([] : trace A)).
  eapply wt_concat; eauto. eapply app_nil_r.
Qed.

Lemma wt_push_right `{Lts P A} p q r μ s :
  p ⟹[s] q -> q ⟹{μ} r -> p ⟹[s ++ [μ]] r.
Proof. intros w1 w2. eapply wt_concat; eauto. Qed.

Lemma wt_decomp_one `{Lts P A} {μ p q} : p ⟹{μ} q -> ∃ r1 r2, p ⟹ r1 ∧ r1 ⟶[μ] r2 ∧ r2 ⟹ q.
Proof.
  intro w.
  dependent induction w; eauto with mdb.
  destruct (IHw μ JMeq_refl) as (r1 & r2 & w1 & l' & w2).
  exists r1, r2. eauto with mdb.
Qed.

Lemma refuses_tau_preserved_by_wt_non_blocking_action `{LtsOba P A} p q s :
  Forall non_blocking s ->  p ↛ -> p ⟹[s] q -> q ↛.
Proof.
  intros s_spec hst hw.
  induction hw; eauto.
  - eapply lts_refuses_spec2 in hst. now exfalso. eauto.
  - inversion s_spec; subst.
    eapply IHhw. eassumption. eapply refuses_tau_preserved_by_lts_non_blocking_action; eauto.
Qed. 


Lemma refuses_tau_action_preserved_by_wt_non_blocking_action `{LtsOba P A} p q s μ :
  Forall non_blocking s -> p ↛ -> p ↛[μ] -> p ⟹[s] q -> q ↛[μ].
Proof.
  intros s_spec hst_tau hst_inp hw.
  induction hw; eauto.
  - eapply lts_refuses_spec2 in hst_tau. now exfalso. eauto.
  - inversion s_spec; subst. eapply IHhw. 
    + assumption.
    + eapply refuses_tau_preserved_by_lts_non_blocking_action; eauto.
    + eapply refuses_action_preserved_by_lts_non_blocking_action; eauto.
Qed.

Definition Eq {A : Type} (s1 : A) (s2 : A) := s1 = s2.
Definition NotEq {A : Type} (s1 : A) (s2 : A) := s1 ≠ s2.

Lemma lts_input_preserved_by_wt_output `{LtsOba P A} p q s μ :
  Forall non_blocking s 
    -> Forall (NotEq μ) s -> p ↛ -> (exists t, p ⟶[μ] t) -> p ⟹[s] q 
      -> (exists t, q ⟶[μ] t).
Proof.
  intros s_spec1 s_spec2 hst_tau hst_inp hw.
  induction hw; eauto.
  - eapply lts_refuses_spec2 in hst_tau. now exfalso. eauto.
  - inversion s_spec1; subst. inversion s_spec2; subst. eapply IHhw. 
    + eassumption.
    + eassumption.
    + eapply refuses_tau_preserved_by_lts_non_blocking_action; eauto.
    + eapply lts_different_action_preserved_by_lts_non_blocking_action; eauto.
Qed.


(* Convergence *)

Reserved Notation "p ⇓ s" (at level 70).

Inductive cnv `{Lts P A} : P -> trace A -> Prop :=
| cnv_nil p : p ⤓ -> p ⇓ []
| cnv_act p μ s : p ⤓ -> (forall q, p ⟹{μ} q -> q ⇓ s) -> p ⇓ μ :: s

where "p ⇓ s" := (cnv p s).

Global Hint Constructors cnv:mdb.

Lemma cnv_terminate `{M : Lts P A} p s : p ⇓ s -> p ⤓.
Proof. by intros hcnv; now inversion hcnv. Qed.

Lemma cnv_preserved_by_lts_tau `{M : Lts P A} s p : p ⇓ s -> forall q, p ⟶ q -> q ⇓ s.
Proof.
  intros hcnv q l.
  inversion hcnv; subst.
  - eapply cnv_nil. inversion H0; eauto.
  - eapply cnv_act.
    + inversion H0; eauto.
    + eauto with mdb.
Qed.

Lemma cnv_preserved_by_wt_nil `{M : Lts P A} s p :
  p ⇓ s -> forall q, p ⟹ q -> q ⇓ s.
Proof.
  intros hcnv q w.
  dependent induction w; eauto with mdb.
  eapply IHw. eapply cnv_preserved_by_lts_tau; eauto. reflexivity.
Qed.

Lemma cnv_preserved_by_wt_act `{M: Lts P A} s p μ :
  p ⇓ μ :: s -> forall q, p ⟹{μ} q -> q ⇓ s.
Proof. by intros hcnv; inversion hcnv; eauto with mdb. Qed.

Lemma cnv_iff_prefix_terminate_l `{M: Lts P A} p s :
  p ⇓ s -> (forall t q, t `prefix_of` s -> p ⟹[t] q -> q ⤓).
Proof.
  intros hcnv t q hpre w.
  revert s p q hcnv hpre w.
  dependent induction t; intros.
  - eapply cnv_terminate, cnv_preserved_by_wt_nil; eassumption.
  - eapply wt_pop in w as (p' & w0 & w1).
    inversion hpre; subst. simpl in hcnv.
    eapply (IHt (t ++ x) p' q).
    eapply cnv_preserved_by_wt_act; eauto.
    now eapply prefix_cons_inv_2 in hpre.
    eassumption.
Qed.

Lemma cnv_iff_prefix_terminate_r `{M: Lts P A} p s :
  (forall t q, t `prefix_of` s -> p ⟹[t] q -> q ⤓) -> p ⇓ s.
Proof.
  intros h.
  revert p h.
  dependent induction s; intros; eauto with mdb.
  eapply cnv_act; eauto with mdb.
  eapply (h []) ; eauto with mdb; eapply prefix_nil.
  intros q w. eapply IHs.
  intros t r hpre w1.
  eapply (h (a :: t)); eauto with mdb. eapply prefix_cons. eassumption.
  eapply wt_push_left; eassumption.
Qed.

Corollary cnv_iff_prefix_terminate `{M: Lts P A} p s :
  p ⇓ s <-> (forall s0 q, s0 `prefix_of` s -> p ⟹[s0] q -> q ⤓).
Proof.
  split; [eapply cnv_iff_prefix_terminate_l|eapply cnv_iff_prefix_terminate_r].
Qed.

Lemma cnv_wt_prefix `{M: Lts P A} s1 s2 p :
  p ⇓ s1 ++ s2 -> forall q, p ⟹[s1] q -> q ⇓ s2.
Proof.
  revert s2 p.
  dependent induction s1; intros s2 p hcnv q w.
  - eapply cnv_preserved_by_wt_nil; eauto with mdb.
  - eapply wt_pop in w as (p' & w0 & w1).
    inversion hcnv; eauto with mdb.
Qed.

Lemma terminate_preserved_by_wt_nil `{M: Lts P A} p : p ⤓ -> forall q, p ⟹ q -> q ⤓.
Proof.
  intros hcnv q w.
  dependent induction w; eauto with mdb.
  eapply IHw. eapply terminate_preserved_by_lts_tau; eauto. reflexivity.
Qed.

Lemma terminate_preserved_by_wt_non_blocking_action `{M: LtsOba P A} p q η : 
  non_blocking η -> p ⤓ -> p ⟹{ η } q -> q ⤓.
Proof.
  intros nb ht w.
  dependent induction w.
  - eapply IHw; eauto. eapply terminate_preserved_by_lts_tau; eauto.
  - eapply terminate_preserved_by_wt_nil.
    eapply terminate_preserved_by_lts_non_blocking_action; eauto. assumption.
Qed.


Definition lts_tau_set `{FiniteImageLts P A} p : list P :=
  map proj1_sig (enum $ dsig (lts_step p τ)).

Lemma lts_tau_set_spec : forall `{FiniteImageLts P A} p q, q ∈ lts_tau_set p <-> p ⟶ q.
Proof.
  intros. split.
  intro mem. unfold lts_tau_set in mem.
  eapply elem_of_list_fmap in mem as ((r & l) & eq & mem). subst.
  eapply bool_decide_unpack. eassumption.
  intro. eapply elem_of_list_fmap.
  exists (dexist q H2). split.
  eauto. eapply elem_of_enum.
Qed.


(* Lemma lts_ht_input_ex `{LtsObaFW P A} (p : P) :
  forall η, non_blocking η -> exists μ, exists p', lts_step p (ActExt μ) p'.
Proof. 
  intro η. intro nb.
assert (exists μ , dual η μ) as Duo.
+ exists (co_nb η). symmetry. eapply (duo_nb_co_nb η). assumption.
+ destruct Duo as [μ Duo]. exists μ. edestruct (lts_oba_fw_forward  p η μ) as (t & l1 & l2); eauto. Qed.
 *)



Lemma eq_spec_wt `{LtsEq P A} p p' : p ⋍ p' -> forall q s, p ⟹[s] q -> p' ⟹⋍[s] q.
Proof.
  intros heq q s w.
  revert p' heq.
  dependent induction w; intros.
  + exists p'; split. eauto with mdb. now symmetry.
  + edestruct eq_spec as (t' & hlt' & heqt').
    exists p. split; [symmetry|]; eassumption.
    destruct (IHw t' (symmetry heqt')) as (u & hlu' & hequ').
    exists u. eauto with mdb.
  + edestruct eq_spec as (t' & hlt' & heqt').
    exists p. split; [symmetry|]; eassumption.
    destruct (IHw t' (symmetry heqt')) as (u & hlu' & hequ').
    exists u. eauto with mdb.
Qed.

(* fixme: ugly - remove in the caller ? *)
Lemma mk_lts_eq `{LtsEq P A} {p α q} : lts_step p α q -> lts_sc p α q.
Proof. intro. exists q; split. eauto with mdb. reflexivity. Qed.

Lemma delay_wt_non_blocking_action_nil `{LtsObaFW P A} {p q r η} :
  non_blocking η ->
  p ⟶⋍[η] q ->
  q ⟹ r ->
  exists t, p ⟹ t /\ t ⟶⋍[η] r.
Proof.
  intros nb l w.
  revert p η nb l.
  dependent induction w; intros p0 η nb (p' & hl & heq); eauto with mdb.
  - exists p0. split; eauto with mdb. exists p'. split; eauto with mdb.
  - destruct (eq_spec p' q τ) as (r & hlr & heqr); eauto with mdb.
    destruct (lts_oba_non_blocking_action_delay nb hl hlr) as (r' & l1 & (t' & l2 & heqt')).
    edestruct (IHw JMeq_refl r' η) as (r0 & w0 & (r1 & l1' & heq1)).
    exact nb. exists t'. split. eassumption. etrans; eassumption.
    exists r0. split. eapply wt_tau; eassumption. exists r1. eauto with mdb.
Qed.

Lemma delay_wt_non_blocking_action `{LtsObaFW P A} {p q r η s} :
  non_blocking η ->
  p ⟶⋍[η] q -> q ⟹[s] r ->
  exists t, p ⟹[s] t /\ t ⟶⋍[η] r.
Proof.
  revert p q r η.
  induction s as [|μ s']; intros p q r η nb l w.
  - eapply delay_wt_non_blocking_action_nil; eauto.
  - eapply wt_pop in w as (q' & w0 & w1).
    destruct (wt_decomp_one w0) as (q0 & q1 & w2 & l' & w3).
    destruct (delay_wt_non_blocking_action_nil nb l w2) as (t & w4 & (q0' & l1' & heq')).
    destruct (eq_spec q0' q1 (ActExt μ)) as (r' & hr' & heqr'). eauto with mdb.
    destruct (lts_oba_non_blocking_action_delay nb l1' hr') as (u & l2 & l3).
    edestruct (eq_spec_wt q1 r' (symmetry heqr') r) as (t1 & w5 & l4); eauto with mdb.
    eapply wt_push_nil_left; eassumption.
    edestruct (IHs' u r') as (t2 & w6 & l5); eauto with mdb.
    exists t2. split.
    eapply wt_push_left; [eapply wt_push_nil_left|]; eauto with mdb.
    destruct l5 as (t1' & hlt1' & heqt1'). exists t1'. split; eauto with mdb.
    etrans; eassumption.
Qed.

Lemma cnv_preserved_by_eq `{LtsEq P A} p q s : p ⋍ q -> p ⇓ s -> q ⇓ s.
Proof.
  intros heq hcnv. revert q heq.
  induction hcnv; intros.
  - eapply cnv_nil.
    eapply (terminate_preserved_by_eq H2 heq).
  - eapply cnv_act.
    + eapply (terminate_preserved_by_eq H2 heq).
    + intros t w.
      destruct (eq_spec_wt q p (symmetry heq) t [μ] w) as (t' & hlt' & heqt').
      eapply (H4 t' hlt' t heqt').
Qed.

Lemma cnv_preserved_by_lts_non_blocking_action `{LtsObaFW P A} p q η s :
  non_blocking η -> p ⇓ s -> p ⟶[η] q -> q ⇓ s.
Proof.
  revert p q η.
  induction s as [|μ s']; intros p q η nb hacnv l.
  - eapply cnv_nil. inversion hacnv. subst.
    eapply terminate_preserved_by_lts_non_blocking_action; eassumption.
  - inversion hacnv as [|p'  μ'  T  Hyp_p_conv Hyp_conv_through_μ];subst.
    eapply cnv_act.
    + eapply terminate_preserved_by_lts_non_blocking_action; eassumption.
    + intros r w.
      destruct (delay_wt_non_blocking_action nb (mk_lts_eq l) w) as (t & w0 & l1).
      destruct l1 as (r' & l2 & heq).
      eapply cnv_preserved_by_eq. eassumption.
      eapply IHs'. exact nb. eapply Hyp_conv_through_μ, w0.
      eassumption.
Qed.

Lemma cnv_preserved_by_wt_non_blocking_action `{LtsObaFW P A} p q η s :
  non_blocking η -> p ⇓ s -> p ⟹{η} q -> q ⇓ s.
Proof.
  intros nb hcnv w.
  destruct (wt_decomp_one w) as (r1 & r2 & w1 & l0 & w2).
  eapply (cnv_preserved_by_wt_nil _ r2); eauto.
  eapply (cnv_preserved_by_lts_non_blocking_action r1); eauto.
  eapply cnv_preserved_by_wt_nil; eauto.
Qed.


Lemma cnv_drop_input_hd `{LtsObaFW P A} p μ s :
  (exists η, non_blocking η /\ dual η μ) -> p ⇓ μ :: s -> p ⇓ s.
Proof.
  intros Hyp hacnv. destruct Hyp as [η Hyp]. destruct Hyp as [nb duo].
  inversion hacnv as [|p'  μ'  T  Hyp_p_conv Hyp_conv_through_μ];subst.
  destruct (lts_oba_fw_forward p η μ) as (r & l1 & l2). eassumption. eassumption.
  eapply cnv_preserved_by_lts_non_blocking_action. eassumption.
  eapply Hyp_conv_through_μ. eapply wt_act. eassumption. eapply wt_nil. eapply l2.
Qed. 


(* fixme: it should be enought to have ltsOBA + one of the feedback *)
Lemma cnv_retract_lts_non_blocking_action `{LtsObaFW P A} p q η μ s :
  non_blocking η -> dual η μ -> p ⇓ s -> p ⟶[η] q -> q ⇓ μ :: s.
Proof.
  intros nb duo hcnv l.
  eapply cnv_act.
  - inversion hcnv; eapply terminate_preserved_by_lts_non_blocking_action; eassumption.
  - intros q' w.
    destruct (wt_decomp_one w) as (r1 & r2 & w1 & l0 & w2).
    destruct (delay_wt_non_blocking_action nb (mk_lts_eq l) w1) as (t & w0 & l1).
    destruct l1 as (r' & l1 & heq).
    edestruct (eq_spec r' r2) as (r & hlr & heqr). exists r1. eauto.
    eapply (cnv_preserved_by_wt_nil _ r2); eauto.
    eapply cnv_preserved_by_eq. eassumption.
    destruct (lts_oba_fw_feedback nb duo l1 hlr) as [(t0 & hlt0 & heqt0)|].
    eapply cnv_preserved_by_eq. eassumption.
    eapply cnv_preserved_by_lts_tau.
    eapply (cnv_preserved_by_wt_nil _ p); eauto. eassumption.
    eapply cnv_preserved_by_eq. eassumption.
    eapply (cnv_preserved_by_wt_nil _ p); eauto.
Qed.

Lemma cnv_retract_wt_non_blocking_action `{LtsObaFW P A} p q η μ s :
  non_blocking η -> dual η μ -> p ⇓ s -> p ⟹{η} q -> q ⇓ μ :: s.
Proof.
  intros nb duo hcnv w.
  eapply wt_decomp_one in w as (t1 & t2 & w1 & l & w2).
  eapply cnv_preserved_by_wt_nil; eauto.
  eapply (cnv_retract_lts_non_blocking_action t1); eauto.
  eapply cnv_preserved_by_wt_nil; eauto.
Qed.

(* fixme: naming clash join/concat/push etc *)
Lemma wt_join_nil `{Lts P A} {p q r} : p ⟹ q -> q ⟹ r -> p ⟹ r.
Proof. intros w1 w2. dependent induction w1; eauto with mdb. Qed.

Lemma wt_join_nil_eq `{LtsEq P A} {p q r} : p ⟹⋍ q -> q ⟹⋍ r -> p ⟹⋍ r.
Proof.
  intros (q' & hwq' & heqq') (r' & hwr' & heqr').
  destruct (eq_spec_wt _ _ (symmetry heqq') r' [] hwr') as (r1 & hwr1 & heqr1).
  exists r1. split. eapply (wt_push_nil_left hwq' hwr1). etrans; eassumption.
Qed.

Lemma wt_join_nil_eq_l `{LtsEq P A} {p q r s} : p ⟹⋍ q -> q ⟹[s] r -> p ⟹⋍[s] r.
Proof.
  intros (q' & hwq' & heqq') w2.
  destruct (eq_spec_wt _ _ (symmetry heqq') r s w2) as (r1 & hwr1 & heqr1).
  exists r1. split. eapply (wt_push_nil_left hwq' hwr1). eassumption.
Qed.

Lemma wt_join_nil_eq_r `{LtsEq P A} {p q r s} : p ⟹[s] q -> q ⟹⋍ r -> p ⟹⋍[s] r.
  intros w1 (r' & hwr' & heqr').
  exists r'. split. eapply wt_push_nil_right; eauto. eassumption.
Qed.

Lemma wt_join_eq `{LtsEq P A} {p q r s1 s2} : p ⟹⋍[s1] q -> q ⟹⋍[s2] r -> p ⟹⋍[s1 ++ s2] r.
  revert p q r s2.
Proof.
  induction s1; intros p q r s2 (q' & hwq' & heqq') w2; simpl in *.
  - destruct w2 as  (r' & hwr' & heqr').
    destruct (eq_spec_wt _ _ (symmetry heqq') r' s2 hwr') as (r1 & hwr1 & heqr1).
    exists r1. split. eapply (wt_push_nil_left hwq' hwr1). etrans; eassumption.
  - eapply wt_pop in hwq' as (p0 & w0 & w1).
    edestruct IHs1 as (t' & hwt' & heqt').
    exists q'. split; eassumption. eassumption.
    exists t'. split. eapply (wt_push_left w0 hwt'). eassumption.
Qed.

Lemma wt_join_eq_l `{LtsEq P A} {p q r s1 s2} : p ⟹⋍[s1] q -> q ⟹[s2] r -> p ⟹⋍[s1 ++ s2] r.
Proof.
  intros (q' & hwq' & heqq') w2.
  destruct (eq_spec_wt _ _ (symmetry heqq') r s2 w2) as (r1 & hwr1 & heqr1).
  exists r1. split. eapply wt_concat; eassumption. eassumption.
Qed.

Lemma wt_join_eq_r `{LtsEq P A} {p q r s1 s2} : p ⟹[s1] q -> q ⟹⋍[s2] r -> p ⟹⋍[s1 ++ s2] r.
Proof.
  intros w1 (r' & hwr' & heqr').
  exists r'. split. eapply wt_concat; eassumption. eassumption.
Qed.

Lemma wt_annhil `{LtsObaFW P A} p q η μ : non_blocking η -> dual η μ -> p ⟹[[η ; μ]] q -> p ⟹⋍ q.
Proof.
  intros nb duo w.
  destruct (wt_pop p q (η) [μ] w) as (u & w1 & w2).
  eapply wt_decomp_one in w1 as (t1 & t2 & w3 & l1 & w4).
  eapply wt_decomp_one in w2 as (r1 & r2 & w5 & l2 & w6).
  eapply (wt_join_nil_eq_r w3).
  destruct (delay_wt_non_blocking_action_nil nb (mk_lts_eq l1) (wt_join_nil w4 w5)) as (v & w0 & (v' & hlv' & heqv')).
  eapply (wt_join_nil_eq_r w0).
  destruct (eq_spec v' r2 (ActExt $ μ)) as (r2' & hlr2' & heqr2'); eauto with mdb.
  edestruct (lts_oba_fw_feedback nb duo hlv' hlr2') as [(t & hlt & heqt)| Hyp_equiv].
  - eapply wt_join_nil_eq.
    exists t. split. eapply wt_tau; eauto with mdb. eassumption.
    eapply wt_join_nil_eq_r. eapply wt_nil.
    eapply eq_spec_wt. etrans. eapply (symmetry heqr2'). now symmetry. eassumption.
  - eapply eq_spec_wt. etrans. eapply (symmetry heqr2'). symmetry. now rewrite Hyp_equiv.
    eassumption.
Qed.

Lemma lts_to_wt `{Lts P A} {p q μ} : p ⟶[μ] q -> p ⟹{μ} q.
Proof. eauto with mdb. Qed.


Lemma are_actions_preserved_by_perm {A Pp} (s1 s2 : trace A) :
  s1 ≡ₚ s2 -> Forall Pp s1 -> Forall Pp s2.
Proof. intros hp hos. eapply Permutation_Forall; eauto. Qed.

Lemma wt_non_blocking_action_swap `{LtsObaFW P A} p q η1 η2 : 
      non_blocking η1 -> non_blocking η2 -> p ⟹[[η1 ; η2]] q -> p ⟹⋍[[η2; η1]] q.
Proof.
  intros nb1 nb2 w.
  destruct (wt_pop p q η1 [η2] w) as (t & w1 & w2).
  eapply wt_decomp_one in w1 as (t1 & t2 & w3 & l1 & w4).
  eapply wt_decomp_one in w2 as (r1 & r2 & w5 & l2 & w6).
  assert (h : t2 ⟹ r1) by (eapply wt_push_nil_left; eassumption).
  destruct (delay_wt_non_blocking_action nb1 (mk_lts_eq l1) h) as (r & w7 & (r1' & hlr1' & heqr1')).
  destruct (eq_spec r1' r2 (ActExt $ η2)) as (t' & hlt' & heqt'). eauto with mdb.
  destruct (lts_oba_non_blocking_action_delay nb1 hlr1' hlt') as (u & hlu & (t0 & hlt0 & heqt0)); eauto.
  eapply wt_join_nil_eq_r.
  eapply (wt_push_nil_left w3).
  eapply (wt_push_nil_left w7).
  eapply (wt_act _ _ _ _ _ hlu), (wt_act _ _ _ _ _ hlt0), wt_nil.
  eapply eq_spec_wt. symmetry. etrans. eapply heqt0. eapply heqt'. eapply w6.
Qed.


Lemma wt_input_swap `{LtsObaFW P A} p q μ1 μ2 : 
  (exists η2, non_blocking η2 /\ dual η2 μ2)
  -> p ⟹[[μ1 ; μ2]] q -> p ⟹⋍[[μ2; μ1]] q.
Proof.
  intro BlocDuo. destruct BlocDuo as (η2 & nb & duo).
  intro w.
  destruct (wt_pop p q (μ1) [μ2] w) as (t & w1 & w2).
  eapply wt_decomp_one in w1 as (t1 & t2 & w3 & l1 & w4).
  eapply wt_decomp_one in w2 as (r1 & r2 & w5 & l2 & w6).
  destruct (lts_oba_fw_forward t1 η2 μ2) as (t1' & l3 & l4); eauto.
  replace [μ2; μ1] with ([μ2] ++ [μ1]) by eauto.
  destruct (delay_wt_non_blocking_action nb (mk_lts_eq l4) (lts_to_wt l1)) as (r & l5 & l6).
  eapply wt_join_nil_eq_r.
  eapply (wt_push_nil_left w3).
  eapply (wt_act _ _ _ _ _ l3).
  eapply wt_decomp_one in l5 as (u1 & u2 & w7 & l7 & w8).
  eapply (wt_push_nil_left w7).
  eapply (wt_act _ _ _ _ _ l7 w8).
  assert (h : t2 ⟹ r1) by (eapply wt_push_nil_left; eassumption).
  destruct (delay_wt_non_blocking_action nb l6 h) as (v & wv & (v' & lv & heqv)).
  destruct (eq_spec v' r2 (ActExt $ μ2)) as (t' & hlt' & heqt'); eauto with mdb.
  eapply (wt_join_nil_eq_r wv).
  destruct (lts_oba_fw_feedback nb duo lv hlt') as [(t3 & hlt3 & heqt3)|]; subst; eauto with mdb.
  - eapply wt_join_nil_eq.
    exists t3. split; eauto with mdb.
    edestruct (eq_spec_wt r2 t') as (q' & hwq' & heqq').
    etrans. symmetry. eapply heqt'. now symmetry. eapply w6. exists q'. split; eauto with mdb.
  - edestruct (eq_spec_wt r2 v) as (q' & hwq' & heqq').
    etrans. symmetry. eassumption. now symmetry. eassumption.
    exists q'. split; eauto with mdb.
Qed.

Lemma cnv_input_swap `{LtsObaFW P A} p μ1 μ2 s :
  (exists η1, non_blocking η1 /\ dual η1 μ1) -> (exists η2, non_blocking η2 /\ dual η2 μ2)
  -> p ⇓ μ1 :: μ2 :: s -> p ⇓ μ2 :: μ1 :: s.
Proof.
  intros BlocDuo1 BlocDuo2 hcnv. 
  destruct BlocDuo1 as (η1 & nb1 & duo1).
  destruct BlocDuo2 as (η2 & nb2 & duo2).
  destruct (lts_oba_fw_forward p η1 μ1) as (t0 & l1 & l2). eassumption. eassumption.
  destruct (lts_oba_fw_forward t0 η2 μ2) as (t1 & l3 & l4). eassumption. eassumption.
  inversion hcnv; subst.
  eapply cnv_act; eauto.
  intros q w1. eapply cnv_act.
  - destruct (delay_wt_non_blocking_action nb1 (mk_lts_eq l2) w1) as (t' & w2 & (t2 & hlt2 & heqt2)).
    eapply (terminate_preserved_by_eq2 heqt2).
    eapply (terminate_preserved_by_lts_non_blocking_action nb1 hlt2).
    eapply (cnv_terminate t' s).
    eapply cnv_preserved_by_wt_act; eauto with mdb.
  - intros r w2.
    edestruct (wt_input_swap) as (t & w' & heq'). exists η1. eauto.
    eapply wt_push_left. eapply w1. eapply w2.
    eapply cnv_preserved_by_eq.
    eapply heq'.
    eapply (cnv_wt_prefix [μ1 ; μ2]); eauto.
Qed.


Definition exist_co_nba (* {A : Type} `{ExtAct A}  *)
      `{ExtAction A} (μ : A) := exists (η : A), (non_blocking η /\ dual η μ).

Lemma cnv_input_perm `{LtsObaFW P A} p s1 s2 :
  Forall exist_co_nba s1 -> s1 ≡ₚ s2 -> p ⇓ s1 -> p ⇓ s2.
Proof.
  intros his hp hcnv.
  revert p his hcnv.
  induction hp; intros; eauto with mdb.
  - inversion hcnv; subst.
    eapply cnv_act; eauto with mdb.
    intros q w. eapply IHhp; eauto with mdb.
    now inversion his.
  - inversion his as [|? ? Hyp_co_act Hyp_list_co_act]; subst. 
    inversion Hyp_list_co_act as [|? ? Hyp_co_act' Hyp_list_co_act']; subst.
    destruct Hyp_co_act, Hyp_co_act'. 
    eapply cnv_input_swap; eauto. 
  - eapply IHhp2. eapply are_actions_preserved_by_perm; eauto.
    eapply IHhp1. eapply are_actions_preserved_by_perm; eauto.
    eassumption.
Qed.

Lemma cnv_non_blocking_action_swap `{LtsObaFW P A} p η1 η2 s :
  non_blocking η1 -> non_blocking η2 ->
  p ⇓ η1 :: η2 :: s -> p ⇓ η2 :: η1 :: s.
Proof.
  intros nb1 nb2 hcnv.
  eapply cnv_act.
  - now inversion hcnv.
  - intros q hw1.
    eapply cnv_act.
    eapply (cnv_terminate q []).
    eapply cnv_preserved_by_wt_non_blocking_action; eauto. eapply cnv_nil. now inversion hcnv.
    intros t hw2.
    replace (η1 :: η2 :: s) with ([η1 ; η2] ++ s) in hcnv.
    set (hw3 := wt_concat _ _ _ _ _ hw1 hw2). simpl in hw3.
    eapply wt_non_blocking_action_swap in hw3 as (t' & hw4 & eq').
    eapply cnv_preserved_by_eq. eassumption.
    eapply cnv_wt_prefix. eauto. eassumption.
    now simpl. now simpl. now simpl.
Qed.

Lemma cnv_non_blocking_action_perm `{LtsObaFW P A} p s1 s2 :
  Forall non_blocking s1 -> s1 ≡ₚ s2 -> p ⇓ s1 -> p ⇓ s2.
Proof.
  intros hos hp hcnv.
  revert p hos hcnv.
  induction hp; intros; eauto with mdb.
  - inversion hcnv; subst.
    eapply cnv_act; eauto with mdb.
    intros q w. eapply IHhp; eauto with mdb.
    now inversion hos.
  - inversion hos as [| ? ? nb Hyp_nb_list]; subst. inversion Hyp_nb_list;subst.
    now eapply cnv_non_blocking_action_swap.
  - eapply IHhp2.
    eapply Permutation_Forall; eassumption.
    eapply IHhp1.
    eapply Permutation_Forall. now symmetry. eassumption.
    eassumption.
Qed.


Lemma wt_input_perm `{LtsObaFW P A} {p q} s1 s2 :
  Forall exist_co_nba s1 -> s1 ≡ₚ s2 -> p ⟹[s1] q -> p ⟹⋍[s2] q.
Proof.
  intros his hp w.
  revert p q his w.
  dependent induction hp; intros; eauto.
  - exists q. split. eassumption. reflexivity.
  - eapply wt_pop in w as (p' & w0 & w1).
    replace (x :: l') with ([x] ++ l') by eauto.
    eapply wt_join_eq_r. eassumption.
    eapply IHhp. now inversion his. eassumption.
  - inversion his as [| ? ? Hyp_co_act Hyp_co_act_list]; subst. 
    inversion Hyp_co_act_list as [| ? ? Hyp_co_act' Hyp_co_act_list']; subst. 
    destruct Hyp_co_act, Hyp_co_act'.
    replace (x :: y :: l) with ([x ; y] ++ l) by eauto.
    replace (y :: x :: l) with ([y ; x] ++ l) in w by eauto.
    eapply wt_split in w as (p' & w1 & w2).
    eapply wt_join_eq_l.
    eapply wt_input_swap. eauto. eassumption. eassumption.
  - eapply IHhp1 in w as (q' & hw' & heq'); eauto.
    eapply IHhp2 in hw' as (q'' & hw'' & heq''); eauto.
    exists q''. split; eauto. etrans; eauto.
    eapply are_actions_preserved_by_perm; eauto.
Qed.

Lemma wt_non_blocking_action_perm `{LtsObaFW P A} {p q} s1 s2 :
  Forall non_blocking s1 -> s1 ≡ₚ s2 -> p ⟹[s1] q -> p ⟹⋍[s2] q.
Proof.
  intros hos hp w.
  revert p q hos w.
  dependent induction hp; intros; eauto.
  - exists q. split. eassumption. reflexivity.
  - eapply wt_pop in w as (p' & w0 & w1).
    replace (x :: l') with ([x] ++ l') by eauto.
    eapply wt_join_eq_r. eassumption.
    eapply IHhp. now inversion hos. eassumption.
  - inversion hos as [| ? ? nb Hyp_nb_list].
    inversion Hyp_nb_list as [| ? ? nb' Hyp_nb_list']; subst. 
    replace (x :: y :: l) with ([x ; y] ++ l) by eauto.
    replace (y :: x :: l) with ([y ; x] ++ l) in w by eauto.
    eapply wt_split in w as (p' & w1 & w2).
    eapply wt_join_eq_l.
    eapply wt_non_blocking_action_swap. eassumption. eassumption. eassumption. eassumption.
  - eapply IHhp1 in w as (q' & hw' & heq'); eauto.
    eapply IHhp2 in hw' as (q'' & hw'' & heq''); eauto.
    exists q''. split; eauto. etrans; eauto.
    eapply are_actions_preserved_by_perm; eauto.
Qed.

Lemma push_wt_non_blocking_action `{LtsObaFW P A} {p q η s} :
  non_blocking η ->
  p ⟹[η :: s] q ->
  p ⟹⋍[s ++ [η]] q.
Proof.
  intros nb w.
  eapply wt_pop in w as (t & w1 & w2).
  eapply wt_decomp_one in w1 as (t1 & t2 & w3 & l & w4).
  set (w5 := wt_push_nil_left w4 w2).
  destruct (delay_wt_non_blocking_action nb (mk_lts_eq l) w5) as (r & w6 & w7).
  eapply wt_join_eq.
  exists r. split.
  eapply wt_push_nil_left; eassumption. reflexivity.
  destruct w7 as (u & hwu & hequ).
  exists u. split. eapply wt_act. eassumption. eapply wt_nil. eassumption.
Qed.

(* Fixpoint map2 {A B C} (f : A -> B -> C) (l1 : list A) (l2 : list B) : list C := 
  match l1 with
       | [] => []
       | a :: t => match l2 with 
                      | [] => []
                      | b :: t' => (f a b) :: map2 f t t'
                  end
  end. *)

(* necessary ? *)
Inductive Forall2 {A : Type} {B : Type} (P : A → B → Prop) : list A → list B → Prop :=
    Forall2_nil : Forall2 P [] [] 
    | Forall2_cons : ∀ (x : A) (y : B) (la : list A) (lb : list B), P x y → Forall2 P la lb → Forall2 P (x :: la) (y :: lb).

Lemma cnv_retract `{LtsObaFW P A} p q s1 s2 s3:
  Forall non_blocking s1 -> Forall2 dual s1 s3 -> p ⇓ s2 -> p ⟹[s1] q -> q ⇓ s3 ++ s2.
Proof. 
  revert s2 s3 p q.
  induction s1; intros s2 s3 p q hos duo hcnv w; inversion duo ; subst.
  - eapply cnv_preserved_by_wt_nil ; eauto.
  - inversion hos. subst. 
    eapply push_wt_non_blocking_action in w as (q' & hwq' & heqq').
    eapply wt_split in hwq' as (t & w1 & w2).
    eapply cnv_preserved_by_eq. eassumption. subst.
    eapply cnv_retract_wt_non_blocking_action; eauto. eauto.
Qed.

Lemma forward_s `{LtsObaFW P A} p s1 s3:
  Forall non_blocking s3 -> Forall2 dual s3 s1 -> exists t, p ⟹[s1] t /\ t ⟹⋍[s3] p.
Proof.
  intros nb duo. revert p nb duo. dependent induction s1; intros; inversion duo ; subst.
  - exists p. simpl. split ; eauto with mdb.
    exists p. split; eauto with mdb. reflexivity.
  - inversion nb as [|? ? nb' Hyp_nb_list']; subst. 
    edestruct (lts_oba_fw_forward p x a) as (q & l0 & l1); eauto.
    destruct (IHs1 la q Hyp_nb_list') as (q' & w1 & w2); eauto.
    exists q'. split.
    + eauto with mdb.
    + assert (q' ⟹⋍[la ++ [x]] p) as Hyp. 
      eapply wt_join_eq. eassumption. exists p. split. eauto with mdb. reflexivity.
      ++ destruct Hyp as (p' & hwp' & heqp').
         eapply (wt_non_blocking_action_perm (la ++ [x])) in hwp' as (p0 & hwp0 & heqp0).
         exists p0. split. eassumption. etrans; eassumption.
         eapply Forall_app. split. assumption. eauto. 
         symmetry. eapply Permutation_cons_append.
Qed.

Lemma EquivDef_inv1 `{ExtAction A} (s1 : trace A) : Forall exist_co_nba s1 
    -> (exists s3, Forall non_blocking s3 /\ Forall2 dual s3 s1).
Proof.
  dependent induction s1; intro Hyp.
  - exists []. split. eauto. eapply Forall2_nil.
  - inversion Hyp as [|? ? Hyp1 Hyp2] ; subst. destruct Hyp1 as (η & nb & duo).
    eapply IHs1 in Hyp2. destruct Hyp2 as (s3 & Hyp3).
    exists (η :: s3). destruct Hyp3 as (all_nb & all_dual).
    split. eapply Forall_cons; eauto.
    eapply Forall2_cons ; eauto.
Qed.

Lemma EquivDef_inv2 `{ExtAction A} (s1 : trace A) : (exists s3, Forall non_blocking s3 /\ Forall2 dual s3 s1) -> Forall exist_co_nba s1.
Proof.
  dependent induction s1; intro Hyp.
  - eauto.
  - destruct Hyp as (s3 & Hyp). induction s3 as [|η s3 ].  
    + destruct Hyp as (all_nb & all_duo). 
      inversion all_duo.
    + destruct Hyp as (all_nb & all_duo). inversion all_nb; subst. inversion all_duo; subst. 
      eapply Forall_cons. 
      * exists η. split; eauto.
      * eapply IHs1. exists s3. split; eauto.
Qed.

Lemma EquivDef `{ExtAction A} (s1 : trace A) : 
  (exists s3, Forall non_blocking s3 /\ Forall2 dual s3 s1) <-> Forall exist_co_nba s1.
Proof.
  split. 
  * eapply EquivDef_inv2.
  * eapply EquivDef_inv1.
Qed.

Lemma cnv_drop_non_blocking_action_in_the_middle `{LtsObaFW P A} p s1 s2 η :
  Forall exist_co_nba s1 -> non_blocking η ->
  p ⇓ s1 ++ [η] ++ s2 ->
  forall r, p ⟶[η] r -> r ⇓ s1 ++ s2.
Proof.
  intros Hyp nb hcnv r l.
  eapply EquivDef in Hyp as [s nbs_duos]. destruct nbs_duos as [nbs duos].
  destruct (forward_s r s1 s) as (t & w1 & w2); eauto.
  destruct (delay_wt_non_blocking_action nb (mk_lts_eq l) w1) as (t' & w3 & l4).
  destruct l4 as (t0 & hlt0 & heqt0).
  destruct w2 as (t1 & hwt1 & heqt1).
  set (h := eq_spec_wt t t0 (symmetry heqt0) t1 _ hwt1).
  destruct h as (t2 & hwt2 & heqt2).
  eapply cnv_preserved_by_eq. etrans. eapply heqt2. eassumption.
  eapply (cnv_retract t0); eauto.
  eapply (cnv_wt_prefix (s1 ++ [η]) _ p).
  now rewrite <- app_assoc. eapply wt_concat; eauto with mdb.
Qed.


Lemma cnv_drop_input_in_the_middle `{LtsObaFW P A} p s1 s2 μ :
  exist_co_nba μ ->
  Forall exist_co_nba s1 -> p ⇓ s1 ++ [μ] ++ s2 ->
  forall r, p ⟶[μ] r -> r ⇓ s1 ++ s2.
Proof.
  (* initial demo *)
  intros Hyp his hcnv r l.
  eapply EquivDef in his as [s nbs_duos]. destruct nbs_duos as [nbs duos].
  destruct (forward_s r s1 s) as (t & w1 & w2); eauto.
  (* replace s1 with (map co (map co s1)) by eapply map_co_involution. *)
  destruct w2 as (r' & hwr' & heqr').
  assert (p ⟹⋍[s1 ++ [μ]] t).
  eapply (wt_input_perm (μ :: s1)).
  eapply Forall_cons. assumption. eapply EquivDef. exists s. split; eauto.
  eapply Permutation_cons_append.
  eapply wt_act; eassumption.
  destruct H2 as (t' & hwt' & heqt').
  eapply cnv_preserved_by_eq. eapply heqr'.
  eapply (cnv_retract t); eauto.
  eapply cnv_preserved_by_eq. eassumption.
  eapply (cnv_wt_prefix (s1 ++ [μ]) _ p).
  now rewrite <- app_assoc.
  eassumption.
Qed.
(*   (* À VOIR *)
  revert p μ s2.
  induction s1 as [|ν s']; intros p μ s2 not_nb his hcnv p' HypTr; simpl in *.
  + eapply (cnv_wt_prefix ([μ])). exact hcnv. eapply lts_to_wt. exact HypTr.
  +   
(*   intros not_nb. 
  
  
  
  (* intros p μ hcnv.
  induction (cnv_terminate p (s1 ++ [μ] ++ s2) hcnv) as [p hp IHtp]. *)
  (* dependent induction hcnv. *)

    
    
    
  intros Hyp not_nb hcnv r l.
  eapply EquivDef in Hyp as [s nbs_duos]. destruct nbs_duos as [nbs duos].
  destruct (forward_s r s1 s) as (t & w1 & w2); eauto.
  destruct w2 as (r' & hwr' & heqr').
  assert (p ⟹⋍[s1 ++ [μ]] t).
  eapply (wt_input_perm (μ :: s1)).
  eapply Forall_cons. eexists. 
  
  
   reflexivity.  eassumption.
  eapply Permutation_cons_append.
  eapply wt_act; eassumption.
  destruct H3 as (t' & hwt' & heqt').
  eapply cnv_preserved_by_eq. eapply heqr'.
  eapply (cnv_retract t); eauto.
  eapply map_co_are_inputs_are_outputs. eassumption.
  eapply cnv_preserved_by_eq. eassumption.
  eapply (cnv_wt_prefix (s1 ++ [ActIn a]) _ p).
  now rewrite <- app_assoc.
  eassumption. *)
Admitted. *)

(* (* à voir *)
Lemma cnv_drop_in_the_middle `{LtsObaFW P A} p s1 s2 μ :
  Forall exist_co_nba s1 -> p ⇓ s1 ++ [μ] ++ s2 -> forall r, p ⟶[μ] r -> r ⇓ s1 ++ s2.
Proof.
  intros Hyp hcnv r l.
  destruct (decide(non_blocking μ)); [eapply cnv_drop_non_blocking_action_in_the_middle | eapply cnv_drop_input_in_the_middle; eauto]; eauto.
Qed. *)

Lemma Forall2_size {A B : Type} P (s1 : list A) (s2 : list B) : Forall2 P s1 s2 -> length s1 = length s2.
Proof.
  intros Hyp. dependent induction Hyp; simpl ; eauto.
Qed.

Lemma Forall2_app {A B : Type} P (s1 s3 : list A) (s2 s4 : list B) : 
      Forall2 P s1 s2 -> Forall2 P s3 s4 -> Forall2 P (s1 ++ s3) (s2 ++ s4).
Proof.
  dependent induction s1; dependent induction s2; 
  dependent induction s3; dependent induction s4; intros Hyp1 Hyp2 ; simpl in *; 
      eauto with mdb; try now inversion Hyp1; try now inversion Hyp2.
  + erewrite app_nil_r. erewrite app_nil_r. eauto.
  + constructor. inversion Hyp1; subst ; eauto. eapply IHs1.
    ++ inversion Hyp1; subst;  eauto.
    ++ eauto.
Qed.

Lemma cnv_annhil `{LtsObaFW P A} p μ η s1 s2 s3 :
  Forall exist_co_nba s1 -> Forall exist_co_nba s2 -> non_blocking η -> dual η μ ->
  p ⇓ s1 ++ [μ] ++ s2 ++ [η] ++ s3 ->
  p ⇓ s1 ++ s2 ++ s3.
Proof.
  intros his1 his2 nb duo hcnv.
  eapply EquivDef in his1 as [s1' nbs1_duos1]. destruct nbs1_duos1 as [nbs1 duos1].
  eapply EquivDef in his2 as [s2' nbs2_duos2]. destruct nbs2_duos2 as [nbs2 duos2].
  assert (Forall non_blocking (s1' ++ [η] ++ s2')).
  eapply Forall_app. split; eauto.
  eapply Forall_app. split; eauto.
  assert (Forall2 dual (s1' ++ [η] ++ s2') (s1 ++ [μ] ++ s2)).
  eapply Forall2_app. assumption.
  eapply Forall2_app. apply Forall2_cons. assumption. apply Forall2_nil. assumption.
  edestruct (forward_s p (s1 ++ [μ] ++ s2)) as (t & w1 & w2); eauto.
  destruct w2 as (r & hwr & heqr).
  eapply (wt_non_blocking_action_perm _ ([η] ++ s1' ++ s2')) in hwr as (r0 & hwr0 & heqr0).
  eapply wt_split in hwr0 as (r1 & hwr0 & hwr1).
  rewrite app_assoc.
  eapply cnv_preserved_by_eq. etrans. eapply heqr0. eapply heqr.
  assert (Forall non_blocking (s1' ++ s2')).
  eapply Forall_app. split; assumption.
  assert (Forall2 dual (s1' ++ s2') (s1 ++ s2)).
  eapply Forall2_app; assumption.
  eapply cnv_retract; eauto.
  eapply cnv_wt_prefix. rewrite 3 app_assoc in hcnv.
  eassumption.
  eapply wt_concat. rewrite <- app_assoc. eassumption. eassumption.
  eassumption.
  symmetry. eapply Permutation_app_swap_app.
Qed.


(* Class InteractionAction (A : Type) :=
  MkInteractionAction {
      inter : A -> A -> Prop;
      inter_dec a b: Decision (inter a b);
      (* i_r : Act A -> Act A -> Act A; *)
      (* à implémenter plus tard, pour généraliser l'interaction *)
    }.
#[global] Existing Instance inter_dec. *)

Class Prop_of_Inter  (P1 P2 A : Type) (inter : A -> A -> Prop) `{@Lts P1 A H} `{@Lts P2 A H} :=
  MkProp_of_Inter {
      inter_dec a b: Decision (inter a b);
      lts_essential_actions_left : P1 -> gset A; (*à mettre dans le LTS?*)
      lts_essential_action_spec_left p ξ: ξ ∈ lts_essential_actions_left p ->  
                      {p' | lts_step p (ActExt ξ) p'} ;(*à mettre dans le LTS?*)
      lts_essential_actions_right : P2 -> gset A; (*à mettre dans le LTS?*)
      lts_essential_action_spec_right p ξ: ξ ∈ lts_essential_actions_right p ->  
                      {p' | lts_step p (ActExt ξ) p'} ;(*à mettre dans le LTS?*)

      lts_essential_actions_spec_interact (p1 : P1) α1 p'1 (p2 : P2) α2 p'2: 
        lts_step p1 (ActExt α1) p'1 ->
        lts_step p2 (ActExt α2) p'2 -> 
        inter α1 α2 ->
          α1 ∈ lts_essential_actions_left p1 \/ α2 ∈ lts_essential_actions_right p2;

      lts_co_inter_action_left : A -> P1 -> gset A;
      lts_co_inter_action_spec_left p1 p'1 ξ μ p2 : 
                 ξ ∈ lts_essential_actions_right p2 ->  lts_step p1 (ActExt μ) p'1 -> inter μ ξ
                                             -> μ ∈ lts_co_inter_action_left ξ p1;

      lts_co_inter_action_right : A -> P2 -> gset A; (* pour le FW , = mb ?*)
      lts_co_inter_action_spec_right p2 p'2 ξ μ p1 : 
                ξ ∈ lts_essential_actions_left p1 ->  lts_step p2 (ActExt μ) p'2 -> inter ξ μ 
                                              -> μ ∈ lts_co_inter_action_right ξ p2;
    }.
#[global] Existing Instance inter_dec.
Fixpoint search_co_steps_right `{Prop_of_Inter S1 S2 A inter} 
  (s2: S2) s'2 ξ candidates (s1 : S1) :=
  match candidates with
  | [] => None
  | μ :: xs =>
    if decide (ξ ∈ lts_essential_actions_left s1 /\ lts_step s2 (ActExt μ) s'2  /\ inter ξ μ) 
      then Some μ
      else search_co_steps_right s2 s'2 ξ xs s1
  end.

Lemma search_co_steps_spec_helper_right `{Prop_of_Inter S1 S2 A inter}
  lnot (s2 : S2) (s'2 : S2) l (ξ : A) (s1 : S1) :
  (elements $ lts_co_inter_action_right ξ s2) = lnot ++ l →
  (∀ μ, μ ∈ lnot → ¬ (ξ ∈ lts_essential_actions_left s1 ∧ s2 ⟶[μ] s'2 ∧ inter ξ μ)) →
  is_Some $ search_co_steps_right s2 s'2 ξ l s1 ->
  { μ | (ξ ∈ lts_essential_actions_left s1 ∧ s2 ⟶[μ] s'2 ∧ inter ξ μ)}.
Proof.
  revert lnot. induction l; intros lnot.
  { simpl. intros Hels Hnots. intros Hc. exfalso. inversion Hc. done. }
  {intros Helems Hnots. simpl.
  destruct (decide (ξ ∈ lts_essential_actions_left s1 ∧ s2 ⟶[a] s'2 ∧ inter ξ a)).
  + eauto.
  + apply (IHl (lnot ++ [a])); [by simplify_list_eq|].
  intros x [Hin | Hin%elem_of_list_singleton]%elem_of_app; simplify_eq ; eauto. }
Qed.

Lemma search_co_steps_spec_helper_right_rev `{Prop_of_Inter S1 S2 A inter} 
  lnot (s2 : S2) s'2 l ξ (s1 : S1) :
  (elements $ lts_co_inter_action_right ξ s2) = lnot ++ l →
  (∀ μ, μ ∈ lnot → ¬ (ξ ∈ lts_essential_actions_left s1 ∧ s2 ⟶[μ] s'2 ∧ inter ξ μ)) →
  { μ | (ξ ∈ lts_essential_actions_left s1 ∧ s2 ⟶[μ] s'2 ∧ inter ξ μ)}  -> is_Some $ search_co_steps_right s2 s'2 ξ l s1.
Proof.
  revert lnot. induction l; intros lnot.
  { simpl. intros Hels Hnots. intros Hc. exfalso. inversion Hc as (μ & ess_act & Hstep & duo).
   eapply (lts_co_inter_action_spec_right s2 s'2 ξ μ s1) in Hstep as Hyp. simplify_list_eq. set_solver. exact ess_act. exact duo. }
  { intros Helems Hnots. simpl.
  destruct (decide (ξ ∈ lts_essential_actions_left s1 ∧ s2 ⟶[a] s'2 ∧ inter ξ a)).
  + eauto.
  + apply (IHl (lnot ++ [a])); [by simplify_list_eq|].
  intros x [Hin | Hin%elem_of_list_singleton]%elem_of_app; simplify_eq ; eauto. }
Qed.

Lemma search_co_steps_spec_1_right `{Prop_of_Inter S1 S2 A inter} 
  (s2 : S2) s'2 ξ s1:
  is_Some $ search_co_steps_right s2 s'2 ξ (elements $ lts_co_inter_action_right ξ s2) s1 ->
  { μ | (ξ ∈ lts_essential_actions_left s1 ∧ s2 ⟶[μ] s'2 ∧ inter ξ μ)}.
Proof. apply (search_co_steps_spec_helper_right []); [done| intros ??; set_solver]. Qed.

Lemma search_co_steps_spec_1_right_rev `{Prop_of_Inter S1 S2 A}
  (s2 : S2) s'2 ξ s1:
  { μ | (ξ ∈ lts_essential_actions_left s1 ∧ s2 ⟶[μ] s'2 ∧ inter ξ μ)} 
  -> is_Some $ search_co_steps_right s2 s'2 ξ (elements $ lts_co_inter_action_right ξ s2) s1.
Proof. apply (search_co_steps_spec_helper_right_rev []); [done| intros ??; set_solver]. Qed.

Lemma search_co_steps_spec_2_right `{Prop_of_Inter S1 S2 A inter}
  μ s2 s'2 l ξ s1:
  search_co_steps_right s2 s'2 ξ l s1 = Some μ →
  (ξ ∈ lts_essential_actions_left s1 ∧ s2 ⟶[μ] s'2 ∧ inter ξ μ).
Proof.
  induction l; [done|]. simpl.
  destruct (decide (ξ ∈ lts_essential_actions_left s1 ∧ s2 ⟶[a] s'2 ∧ inter ξ a)) ; [|eauto].
  intros ?. simplify_eq. done.
Qed. 

Definition decide_co_step_right `{Prop_of_Inter S1 S2 A inter}
  (s2: S2) (s'2 : S2) (ξ : A) (s1 : S1) :
  Decision (∃ μ, ξ ∈ lts_essential_actions_left s1 ∧ s2 ⟶[μ] s'2 ∧ inter ξ μ).
  destruct (search_co_steps_right s2 s'2 ξ (elements $ lts_co_inter_action_right ξ s2) s1) as [a|] eqn:Hpar1.
  { left. apply search_co_steps_spec_2_right in Hpar1. exists a. done. }
  { right; intros contra. destruct contra. assert ({ μ | (ξ ∈ lts_essential_actions_left s1 ∧ s2 ⟶[μ] s'2 ∧ inter ξ μ)} ). 
    exists x. eauto. apply search_co_steps_spec_1_right_rev in X. 
  inversion X. simplify_eq. }
Defined.

Lemma implication_simplified_right `{Prop_of_Inter S1 S2 A inter} 
  (s1: S1) (* (s'1 : S1) *) (s2 : S2) (s'2 : S2)  (ξ : A) :
  Decision (∃ μ, ξ ∈ lts_essential_actions_left s1 ∧ s2 ⟶[μ] s'2 ∧ inter ξ μ) 
  -> Decision (ξ ∈ lts_essential_actions_left s1 ∧ ∃ μ, s2 ⟶[μ] s'2 ∧ inter ξ μ).
Proof.
  intros Hyp. destruct Hyp as [case1 | case2]. 
  + left. decompose record case1. repeat split; eauto.
  + right. intro Hyp. apply case2. decompose record Hyp. eexists. repeat split; eauto.
Qed.

Definition decide_co_step_right' `{Prop_of_Inter S1 S2 A} 
  (s1: S1) (* (s'1 : S1) *) (s2 : S2) (s'2 : S2)  (ξ : A) :
  Decision (ξ ∈ lts_essential_actions_left s1 ∧ ∃ μ, s2 ⟶[μ] s'2 ∧ inter ξ μ).
  eapply implication_simplified_right. 
    + eapply decide_co_step_right.
Defined.

#[global] Instance dec_co_act_right `{Prop_of_Inter S1 S2 A} 
  (s1: S1) (* (s'1 : S1) *) (s2 : S2) (s'2 : S2)  (ξ : A) :
  Decision (ξ ∈ lts_essential_actions_left s1 ∧ ∃ μ, s2 ⟶[μ] s'2 ∧ inter ξ μ).
  eapply decide_co_step_right'.
Defined.




Fixpoint search_steps_essential_left `{Prop_of_Inter S1 S2 A}
  (s1: S1) (s2: S2) s'1 s'2 candidates :=
  match candidates with
  | [] => None
  | ξ::xs => if (decide (ξ ∈ lts_essential_actions_left s1 ∧ s1 ⟶[ξ] s'1
              ∧ is_Some $ (search_co_steps_right s2 s'2 ξ (elements $ lts_co_inter_action_right ξ s2) s1)))
                then Some ξ
                else search_steps_essential_left s1 s2 s'1 s'2 xs
  end.

Lemma search_steps_spec_helper_essential_left `{M12 : Prop_of_Inter S1 S2 A}
  lnot (s1 :S1) (s2 : S2) s'1 s'2 l:
  (elements $ lts_essential_actions_left s1) = lnot ++ l →
  (∀ ξ, ξ ∈ lnot → ¬ (ξ ∈ lts_essential_actions_left s1 ∧ s1 ⟶[ξ] s'1 
          ∧ is_Some $ search_co_steps_right s2 s'2 ξ (elements $ lts_co_inter_action_right ξ s2) s1)) →
  is_Some $ search_steps_essential_left s1 s2 s'1 s'2 l ->
  { ξ & { μ | ξ ∈ lts_essential_actions_left s1 ∧ s1 ⟶[ξ] s'1 ∧ s2 ⟶[μ] s'2 ∧ inter ξ μ}}.
Proof.
  revert lnot. induction l as [| ξ l]; intro lnot.
  { simpl. intros Hels Hnots Hc. exfalso. inversion Hc. done. }
  { intros Helems Hnots. simpl. 
        destruct (decide (ξ ∈ lts_essential_actions_left s1 ∧ s1 ⟶[ξ] s'1 
        ∧ is_Some (search_co_steps_right s2 s'2 ξ (elements (lts_co_inter_action_right ξ s2)) s1))) as [case1 | case2].
   + intro. destruct case1 as (ess_act & HypTr & Hyp_co_step). 
     eapply search_co_steps_spec_helper_right in Hyp_co_step. 
     destruct Hyp_co_step as (μ & ess_act' & HypTr_right & duo). exists ξ. exists μ. split; eauto.
     instantiate (1:= []). eauto. intro. intro impossible. inversion impossible.
   + apply (IHl (lnot ++ [ξ])); [by simplify_list_eq|].
  intros x [Hin | Hin%elem_of_list_singleton]%elem_of_app; simplify_eq ; eauto. }
Qed.

Lemma search_steps_spec_helper_essential_left_rev `{M12 : Prop_of_Inter S1 S2 A}
  lnot s1 s2 s'1 s'2 l:
  (elements $ lts_essential_actions_left s1) = lnot ++ l →
  (∀ ξ, ξ ∈ lnot → ¬ (ξ ∈ lts_essential_actions_left s1 ∧ s1 ⟶[ξ] s'1 
          ∧ is_Some $ search_co_steps_right s2 s'2 ξ (elements $ lts_co_inter_action_right ξ s2) s1)) →
  { ξ & { μ | ξ ∈ lts_essential_actions_left s1 ∧ s1 ⟶[ξ] s'1 ∧ s2 ⟶[μ] s'2 ∧ inter ξ μ}} ->
  is_Some $ search_steps_essential_left s1 s2 s'1 s'2 l.
Proof.
  revert lnot. induction l as [| ξ l]; intros lnot.
  { simpl. intros Hels Hnots. intros (ξ & μ & ess_act & Hstep1 & Hstep2 & duo). exfalso.
    simplify_list_eq. 
    eapply (Hnots ξ). eapply elem_of_elements. exact ess_act.
    split. exact ess_act. split. exact Hstep1.
    apply search_co_steps_spec_1_right_rev. exists μ. repeat split; eauto. }
  { intros Helems Hnots. simpl. 
       destruct (decide (ξ ∈ lts_essential_actions_left s1 ∧ s1 ⟶[ξ] s'1 
       ∧ is_Some (search_co_steps_right s2 s'2 ξ (elements (lts_co_inter_action_right ξ s2)) s1))) as [case1 | case2].
   + intro Hyp. eauto.
   + apply (IHl (lnot ++ [ξ])); [by simplify_list_eq|].
  intros x [Hin | Hin%elem_of_list_singleton]%elem_of_app; simplify_eq ; eauto. }
Qed.



Lemma search_steps_spec_1_essential_left `{M12 : Prop_of_Inter S1 S2 A}
  (s1 : S1) (s2 : S2) s'1 s'2:
  is_Some $ search_steps_essential_left s1 s2 s'1 s'2 (elements $ lts_essential_actions_left s1) ->
  { ξ & { μ | ξ ∈ lts_essential_actions_left s1 ∧ s1 ⟶[ξ] s'1 ∧ s2 ⟶[μ] s'2 ∧ inter ξ μ}}.
Proof. apply (search_steps_spec_helper_essential_left []) ; [done| intros ??; set_solver]. Qed.

Lemma search_steps_spec_1_essential_left_rev `{M12 : Prop_of_Inter S1 S2 A}
  s1 s2 s'1 s'2:
  { ξ & { μ | ξ ∈ lts_essential_actions_left s1 ∧ s1 ⟶[ξ] s'1 ∧ s2 ⟶[μ] s'2 ∧ inter ξ μ}} ->
  is_Some $ search_steps_essential_left s1 s2 s'1 s'2 (elements $ lts_essential_actions_left s1).
Proof. apply (search_steps_spec_helper_essential_left_rev []) ; [done| intros ??; set_solver]. Qed.

Lemma search_steps_spec_2_essential_left `{M12 : Prop_of_Inter S1 S2 A}
  ξ (s1 : S1) (s2 : S2) s'1 s'2 l:
  search_steps_essential_left s1 s2 s'1 s'2 l = Some ξ →
  { μ | ξ ∈ lts_essential_actions_left s1 ∧ s1 ⟶[ξ] s'1 ∧ s2 ⟶[μ] s'2  ∧ inter ξ μ}.
Proof.
  induction l as [| ξ' l] ; [done|]. simpl.
  destruct (decide (ξ' ∈ lts_essential_actions_left s1 ∧ s1 ⟶[ξ'] s'1 
    ∧ is_Some (search_co_steps_right s2 s'2 ξ' (elements (lts_co_inter_action_right ξ' s2)) s1))) as [case1 | case2].
  intros ?;simplify_eq. destruct case1 as (ess_act & HypTr & Hyp_co_step). 
  eapply search_co_steps_spec_1_right in Hyp_co_step. destruct Hyp_co_step as (μ & ess_act' & HypTr_right & duo). 
  exists μ. done. eauto.
Qed.

Fixpoint search_co_steps_left `{Prop_of_Inter S1 S2 A}
  (s1: S1) s'1 ξ candidates (s2 : S2) :=
  match candidates with 
  | [] => None
  | μ :: xs =>
    if decide (ξ ∈ lts_essential_actions_right s2 /\ lts_step s1 (ActExt μ) s'1  /\ inter μ ξ)
      then Some μ
      else search_co_steps_left s1 s'1 ξ xs s2
  end.

Lemma search_co_steps_spec_helper_left `{Prop_of_Inter S1 S2 A}
  lnot (s1 : S1) (s'1 : S1) l (ξ : A) s2 :
  (elements $ lts_co_inter_action_left ξ s1) = lnot ++ l →
  (∀ μ, μ ∈ lnot → ¬ (ξ ∈ lts_essential_actions_right s2 ∧ s1 ⟶[μ] s'1 ∧ inter μ ξ)) →
  is_Some $ search_co_steps_left s1 s'1 ξ l s2->
  { μ | (ξ ∈ lts_essential_actions_right s2 ∧ s1 ⟶[μ] s'1 ∧ inter μ ξ)}.
Proof.
  revert lnot. induction l; intros lnot.
  { simpl. intros Hels Hnots. intros Hc. exfalso. inversion Hc. done. }
  {intros Helems Hnots. simpl.
  destruct (decide (ξ ∈ lts_essential_actions_right s2 ∧ s1 ⟶[a] s'1 ∧ inter a ξ)).
  + eauto.
  + apply (IHl (lnot ++ [a])); [by simplify_list_eq|].
  intros x [Hin | Hin%elem_of_list_singleton]%elem_of_app; simplify_eq ; eauto. }
Qed.

Lemma search_co_steps_spec_helper_left_rev `{Prop_of_Inter S1 S2 A}
  lnot s1 s'1 l ξ s2:
  (elements $ lts_co_inter_action_left ξ s1) = lnot ++ l →
  (∀ μ, μ ∈ lnot → ¬ (ξ ∈ lts_essential_actions_right s2 ∧ s1 ⟶[μ] s'1 ∧ inter μ ξ)) →
  { μ | (ξ ∈ lts_essential_actions_right s2 ∧ s1 ⟶[μ] s'1 ∧ inter μ ξ)}  -> is_Some $ search_co_steps_left s1 s'1 ξ l s2.
Proof.
  revert lnot. induction l as [|μ l]; intros lnot.
  { simpl. intros Hels Hnots. intros Hc. exfalso. inversion Hc as (μ & ess_act & Hstep & duo).
   eapply (lts_co_inter_action_spec_left s1 s'1 ξ μ) in Hstep as Hyp. simplify_list_eq. set_solver. exact ess_act. exact duo. }
  { intros Helems Hnots. simpl.
  destruct (decide (ξ ∈ lts_essential_actions_right s2 ∧ s1 ⟶[μ] s'1 ∧ inter μ ξ)).
  + eauto.
  + apply (IHl (lnot ++ [μ])); [by simplify_list_eq|].
  intros x [Hin | Hin%elem_of_list_singleton]%elem_of_app; simplify_eq ; eauto. }
Qed.

Lemma search_co_steps_spec_1_left `{Prop_of_Inter S1 S2 A}
  (s1 : S1) s'1 ξ s2:
  is_Some $ search_co_steps_left s1 s'1 ξ (elements $ lts_co_inter_action_left ξ s1) s2 ->
  { μ | (ξ ∈ lts_essential_actions_right s2 ∧ s1 ⟶[μ] s'1 ∧ inter μ ξ)}.
Proof. apply (search_co_steps_spec_helper_left []); [done| intros ??; set_solver]. Qed.

Lemma search_co_steps_spec_1_left_rev `{Prop_of_Inter S1 S2 A}
  (s1 : S1) s'1 ξ s2:
  { μ | (ξ ∈ lts_essential_actions_right s2 ∧ s1 ⟶[μ] s'1 ∧ inter μ ξ)} 
  -> is_Some $ search_co_steps_left s1 s'1 ξ (elements $ lts_co_inter_action_left ξ s1) s2.
Proof. apply (search_co_steps_spec_helper_left_rev []); [done| intros ??; set_solver]. Qed.

Lemma search_co_steps_spec_2_left `{Prop_of_Inter S1 S2 A}
  μ s1 s'1 l ξ s2:
  search_co_steps_left s1 s'1 ξ l s2 = Some μ →
  (ξ ∈ lts_essential_actions_right s2 ∧ s1 ⟶[μ] s'1 ∧ inter μ ξ).
Proof.
  induction l  as [| μ' l ]; [done|]. simpl.
  destruct (decide (ξ ∈ lts_essential_actions_right s2 ∧ s1 ⟶[μ'] s'1 ∧ inter μ' ξ)) ; [|eauto].
  intros ?. simplify_eq. done.
Qed. 

Definition decide_co_step_left `{Prop_of_Inter S1 S2 A}
  (s1: S1) (s'1 : S1) (ξ : A) (s2 : S2) :
  Decision (∃ μ, ξ ∈ lts_essential_actions_right s2 ∧ s1 ⟶[μ] s'1 ∧ inter μ ξ).
  destruct (search_co_steps_left s1 s'1 ξ (elements $ lts_co_inter_action_left ξ s1) s2) as [a|] eqn:Hpar1.
  { left. apply search_co_steps_spec_2_left in Hpar1. exists a. done. }
  { right; intros contra. destruct contra as (μ & Hyp). 
    assert ({ μ | (ξ ∈ lts_essential_actions_right s2 ∧ s1 ⟶[μ] s'1 ∧ inter μ ξ)} ) as HypSup. 
    exists μ. eauto. apply search_co_steps_spec_1_left_rev in HypSup. 
    inversion HypSup. simplify_eq. }
Defined.

Lemma implication_simplified_left `{Prop_of_Inter S1 S2 A} 
  (s1: S1) (s'1 : S1) (s2 : S2) (* (s'2 : S2) *)  (ξ : A) :
  Decision (∃ μ, ξ ∈ lts_essential_actions_right s2 ∧ s1 ⟶[μ] s'1 ∧ inter μ ξ) 
  -> Decision (ξ ∈ lts_essential_actions_right s2 ∧ ∃ μ, s1 ⟶[μ] s'1 ∧ inter μ ξ).
Proof.
  intros Hyp. destruct Hyp as [case1 | case2]. left. decompose record case1. repeat split; eauto.
  right. intro HypContra. apply case2. decompose record HypContra. eexists. repeat split; eauto.
Qed.

Definition decide_co_step_left' `{Prop_of_Inter S1 S2 A} 
  (s1: S1) (s'1 : S1) (s2 : S2) (* (s'2 : S2) *)  (ξ : A) :
  Decision (ξ ∈ lts_essential_actions_right s2 ∧ ∃ μ, s1 ⟶[μ] s'1 ∧ inter μ ξ ).
  eapply implication_simplified_left. 
    + eapply decide_co_step_left.
Defined.

#[global] Instance dec_co_act_left `{M12 : Prop_of_Inter S1 S2 A}
  (s1: S1) (s'1 : S1) (s2 : S2) (* (s'2 : S2) *)  (ξ : A) :
  Decision (ξ ∈ lts_essential_actions_right s2 ∧ ∃ μ, s1 ⟶[μ] s'1 ∧ inter μ ξ).
  eapply decide_co_step_left'. 
Defined.  




Fixpoint search_steps_essential_right `{M12 : Prop_of_Inter S1 S2 A}
  (s1: S1) (s2: S2) s'1 s'2 candidates :=
  match candidates with
  | [] => None
  | ξ::xs => if (decide (ξ ∈ lts_essential_actions_right s2 ∧ s2 ⟶[ξ] s'2 
          ∧ is_Some $ search_co_steps_left s1 s'1 ξ (elements $ lts_co_inter_action_left ξ s1) s2))
                then Some ξ
                else search_steps_essential_right s1 s2 s'1 s'2 xs
  end.

Lemma search_steps_spec_helper_essential_right `{M12 : Prop_of_Inter S1 S2 A}
  lnot (s1 :S1) (s2 : S2) s'1 s'2 l:
  (elements $ lts_essential_actions_right s2) = lnot ++ l →
  (∀ ξ, ξ ∈ lnot → ¬ (ξ ∈ lts_essential_actions_right s2 ∧ s2 ⟶[ξ] s'2 
    ∧ is_Some $ search_co_steps_left s1 s'1 ξ (elements $ lts_co_inter_action_left ξ s1) s2)) →
  is_Some $ search_steps_essential_right s1 s2 s'1 s'2 l ->
  { ξ & { μ | ξ ∈ lts_essential_actions_right s2 ∧ s2 ⟶[ξ] s'2 ∧ s1 ⟶[μ] s'1 ∧ inter μ ξ}}.
Proof.
  revert lnot. induction l as [| ξ l]; intros lnot.
  { simpl. intros Hels Hnots Hc. exfalso. inversion Hc. done. }
  { intros Helems Hnots. simpl. 
        destruct (decide (ξ ∈ lts_essential_actions_right s2 ∧ s2 ⟶[ξ] s'2 
          ∧ is_Some (search_co_steps_left s1 s'1 ξ (elements (lts_co_inter_action_left ξ s1)) s2 )))  as [case1 | case2].
   + intro. destruct case1 as (ess_act & HypTr_right & Hyp_co_act_left). 
     eapply search_co_steps_spec_helper_left in Hyp_co_act_left. 
     destruct Hyp_co_act_left as (μ & ess_act' & HypTr_left & duo). 
     exists ξ. exists μ. split; eauto.
     instantiate (1:= []). eauto. intro. intro Hyp. inversion Hyp.
   + apply (IHl (lnot ++ [ξ])); [by simplify_list_eq|].
  intros x [Hin | Hin%elem_of_list_singleton]%elem_of_app; simplify_eq ; eauto. }
Qed.

Lemma search_steps_spec_helper_essential_right_rev `{M12 : Prop_of_Inter S1 S2 A}
  lnot s1 s2 s'1 s'2 l:
  (elements $ lts_essential_actions_right s2) = lnot ++ l →
  (∀ ξ, ξ ∈ lnot → ¬ (ξ ∈ lts_essential_actions_right s2 ∧ s2 ⟶[ξ] s'2 
    ∧ is_Some $ search_co_steps_left s1 s'1 ξ (elements $ lts_co_inter_action_left ξ s1) s2)) →
  { ξ & { μ | ξ ∈ lts_essential_actions_right s2 ∧ s2 ⟶[ξ] s'2 ∧ s1 ⟶[μ] s'1 ∧ inter μ ξ}} ->
  is_Some $ search_steps_essential_right s1 s2 s'1 s'2 l.
Proof.
  revert lnot. induction l as [| ξ l] ; intros lnot.
  { simpl. intros Hels Hnots. intros (ξ & μ & ess_act & Hstep1 & Hstep2 & duo). exfalso.
    simplify_list_eq. 
    eapply (Hnots ξ). eapply elem_of_elements. exact ess_act.
    split. exact ess_act. split. exact Hstep1.
    apply search_co_steps_spec_1_left_rev. exists μ. repeat split; eauto. }
  { intros Helems Hnots. simpl. 
        destruct (decide (ξ ∈ lts_essential_actions_right s2 ∧ s2 ⟶[ξ] s'2 
          ∧ is_Some (search_co_steps_left s1 s'1 ξ (elements (lts_co_inter_action_left ξ s1)) s2 )))  as [case1 | case2].
   + intro Hyp. eauto.
   + apply (IHl (lnot ++ [ξ])); [by simplify_list_eq|].
  intros x [Hin | Hin%elem_of_list_singleton]%elem_of_app; simplify_eq ; eauto. }
Qed. 

Lemma search_steps_spec_1_essential_right `{M12 : Prop_of_Inter S1 S2 A}
  (s1 : S1) (s2 : S2) s'1 s'2:
  is_Some $ search_steps_essential_right s1 s2 s'1 s'2 (elements $ lts_essential_actions_right s2) ->
  { ξ & { μ | ξ ∈ lts_essential_actions_right s2 ∧ s2 ⟶[ξ] s'2 ∧ s1 ⟶[μ] s'1 ∧ inter μ ξ}}.
Proof. apply (search_steps_spec_helper_essential_right []) ; [done| intros ??; set_solver]. Qed.

Lemma search_steps_spec_1_essential_right_rev `{M12 : Prop_of_Inter S1 S2 A}
  s1 s2 s'1 s'2:
  { ξ & { μ | ξ ∈ lts_essential_actions_right s2 ∧ s2 ⟶[ξ] s'2 ∧ s1 ⟶[μ] s'1 ∧ inter μ ξ}} ->
  is_Some $ search_steps_essential_right s1 s2 s'1 s'2 (elements $ lts_essential_actions_right s2).
Proof. apply (search_steps_spec_helper_essential_right_rev []) ; [done| intros ??; set_solver]. Qed.

Lemma search_steps_spec_2_essential_right `{M12 : Prop_of_Inter S1 S2 A}
  ξ (s1 : S1) (s2 : S2) s'1 s'2 l:
  search_steps_essential_right s1 s2 s'1 s'2 l = Some ξ →
  { μ | ξ ∈ lts_essential_actions_right s2 ∧ s2 ⟶[ξ] s'2 ∧ s1 ⟶[μ] s'1  ∧ inter μ ξ}.
Proof.
  induction l as [| ξ' l]; [done|].  simpl.
  destruct (decide (ξ' ∈ lts_essential_actions_right s2 ∧ s2 ⟶[ξ'] s'2 
      ∧ is_Some (search_co_steps_left s1 s'1 ξ' (elements (lts_co_inter_action_left ξ' s1)) s2))) as [case1 | case2].
  intros ?. simplify_eq. destruct case1 as (ess_act & HypTr_right & Hyp_co_act_left). 
  eapply search_co_steps_spec_1_left in Hyp_co_act_left. 
  destruct Hyp_co_act_left as (μ & ess_act' & HypTr_left & duo). exists μ. done. eauto.
Qed.

Inductive inter_step `{M12 : Prop_of_Inter P1 P2 A inter}
            : P1 * P2 → Act A → P1 * P2 → Prop :=
| ParLeft α a1 a2 b (l : a1 ⟶{α} a2) : inter_step (a1, b) α (a2, b)
| ParRight α a b1 b2 (l : b1 ⟶{α} b2) : inter_step (a, b1) α (a, b2)
| ParSync μ1 μ2 a1 a2 b1 b2 (eq : inter μ1 μ2) (l1 : a1 ⟶[μ1] a2) (l2 : b1 ⟶[μ2] b2) : inter_step (a1, b1) τ (a2, b2)
.


Global Hint Constructors inter_step:mdb.


Definition decide_inter_step `{M12 : Prop_of_Inter S1 S2 A inter}
            (s1: S1) (s2: S2) ℓ s'1 s'2:
  Decision (inter_step (s1, s2) ℓ (s'1, s'2)).
Proof.
  destruct (decide (lts_step s1 ℓ s'1 ∧ s2 = s'2)) as [[??]|Hnot1].
  { simplify_eq. left. by constructor. }
  destruct (decide (lts_step s2 ℓ s'2 ∧ s1 = s'1)) as [[??]|Hnot2].
  { simplify_eq. left. by constructor. }
  destruct ℓ.
  { right. intros contra; inversion contra; simplify_eq; eauto. }
  destruct (search_steps_essential_left s1 s2 s'1 s'2 (elements $ lts_essential_actions_left s1)) as [ξ|] eqn:Hpar1.
  { apply search_steps_spec_2_essential_left in Hpar1 as (μ & ess_act & step_left & step_right & duo). 
   left; eapply ParSync; eauto. }
  destruct (search_steps_essential_right s1 s2 s'1 s'2 (elements $ lts_essential_actions_right s2)) as [ξ|] eqn:Hpar2.
  { apply search_steps_spec_2_essential_right in Hpar2 as (μ & ess_act & step_right & step_left & duo).  
   left; eapply ParSync; eauto. }
  right; intros contra; inversion contra; simplify_eq; eauto.
  eapply lts_essential_actions_spec_interact in eq as case_essential; eauto. destruct case_essential as [ess_act1 | ess_act2].
  - assert (is_Some $ search_steps_essential_left s1 s2 s'1 s'2 (elements (lts_essential_actions_left s1))) as Hc; [|].
    eapply search_steps_spec_1_essential_left_rev. exists μ1. exists μ2. repeat split; eauto.
    inversion Hc. simplify_eq.
  - assert (is_Some $ search_steps_essential_right s1 s2 s'1 s'2 (elements (lts_essential_actions_right s2))) as Hc; [|].
    eapply search_steps_spec_1_essential_right_rev. exists μ2. exists μ1. repeat split; eauto.
    inversion Hc. simplify_eq.
Defined.

Lemma list_and_set {A : Type} `{ExtAction A} (a : A) (l : list A) (set : gset A) : 
elements (set) = a :: l -> a ∈ set.
Proof.
  intro Hyp. eapply elem_of_elements. rewrite Hyp. set_solver.
Qed.

Definition inter_not_refuses_essential_left (* {S1 S2 A: Type} `{ExtAction A} (M1: Lts S1 A) (M2: Lts S2 A) *) 
  `{Prop_of_Inter S1 S2 A}
          (s1: S1) (s2 : S2) (ξ : A) :=
        ¬lts_refuses s1 (ActExt $ ξ) ∧ (∃ μ, ¬lts_refuses s2 (ActExt $ μ) 
          ∧ inter ξ μ ∧ ξ ∈ lts_essential_actions_left s1). 
(*          ∧ (∃ s'2 : S2, is_Some (search_co_steps M2 s2 s'2 ξ (elements $ lts_dual_action ξ s2))). *)

(* Lemma inter_inter `{Prop_of_Inter S1 S2 A} p1 p2 ξ : {μ | μ ∈ lts_co_inter_action_right ξ p2 
              /\ ξ ∈ lts_essential_actions_left p1 /\ ¬lts_refuses p2 (ActExt $ μ) /\ inter ξ μ } + 
          {forall μ, μ ∈ lts_co_inter_action_right ξ p2 
          ->  lts_refuses p2 (ActExt $ μ) \/ ¬ inter ξ μ \/ ξ ∉ lts_essential_actions_left p1}.
Proof.
  remember (elements (lts_co_inter_action_right ξ p2)) as l.
  revert Heql. revert p2. revert p1. revert ξ.
  induction l as [| μ l]. 
  + intros. right. intros μ in_list. apply elem_of_elements in in_list.
    rewrite <-Heql in in_list. set_solver.
  + intros ξ p1 p2 elem_def. 
    destruct (decide (p2 ↛[μ])).
    ++ right. intros. destruct (decide (inter ξ μ)).
      +++ destruct (decide (ξ ∉ lts_essential_actions_left p1)). 
    
    destruct (decide ()).
    
    split; eauto. eapply elem_of_elements. set_solver. *)

























Fixpoint search_co_steps_right_not_refuses `{Prop_of_Inter S1 S2 A inter} 
  (s2: S2) ξ candidates (s1 : S1) :=
  match candidates with
  | [] => None
  | μ :: xs =>
    if decide (ξ ∈ lts_essential_actions_left s1 /\ ¬lts_refuses s2 (ActExt μ) /\ inter ξ μ) 
      then Some μ
      else search_co_steps_right_not_refuses s2 ξ xs s1
  end.

Lemma search_co_steps_spec_helper_right_not_refuses `{Prop_of_Inter S1 S2 A inter}
  lnot (s2 : S2) l (ξ : A) (s1 : S1) :
  (elements $ lts_co_inter_action_right ξ s2) = lnot ++ l →
  (∀ μ, μ ∈ lnot → ¬ (ξ ∈ lts_essential_actions_left s1 ∧  ¬lts_refuses s2 (ActExt μ) ∧ inter ξ μ)) →
  is_Some $ search_co_steps_right_not_refuses s2 ξ l s1 ->
  { μ | (ξ ∈ lts_essential_actions_left s1 ∧  ¬lts_refuses s2 (ActExt μ) ∧ inter ξ μ)}.
Proof.
  revert lnot. induction l; intros lnot.
  { simpl. intros Hels Hnots. intros Hc. exfalso. inversion Hc. done. }
  {intros Helems Hnots. simpl.
  destruct (decide (ξ ∈ lts_essential_actions_left s1 ∧ ¬lts_refuses s2 (ActExt a) ∧ inter ξ a)).
  + eauto.
  + apply (IHl (lnot ++ [a])); [by simplify_list_eq|].
  intros x [Hin | Hin%elem_of_list_singleton]%elem_of_app; simplify_eq ; eauto. }
Qed.

Lemma search_co_steps_spec_helper_right_not_refuses_rev `{Prop_of_Inter S1 S2 A inter} 
  lnot (s2 : S2) l ξ (s1 : S1) :
  (elements $ lts_co_inter_action_right ξ s2) = lnot ++ l →
  (∀ μ, μ ∈ lnot → ¬ (ξ ∈ lts_essential_actions_left s1 ∧ ¬lts_refuses s2 (ActExt μ) ∧ inter ξ μ)) →
  { μ | (ξ ∈ lts_essential_actions_left s1 ∧ ¬lts_refuses s2 (ActExt μ) ∧ inter ξ μ)}  
  -> is_Some $ search_co_steps_right_not_refuses s2 ξ l s1.
Proof.
  revert lnot. induction l; intros lnot.
  { simpl. intros Hels Hnots. intros Hc. exfalso. inversion Hc as (μ & ess_act & Hstep & duo).
   eapply lts_refuses_spec1 in Hstep as (s'2 & Hstep); eauto.
   eapply (lts_co_inter_action_spec_right s2 s'2 ξ μ s1) in Hstep as Hyp; eauto.
   simplify_list_eq.
   eapply elem_of_elements in Hyp. eapply Hnots; eauto.
   repeat split; eauto. eapply lts_refuses_spec2. eauto. }
  { intros Helems Hnots. simpl.
  destruct (decide (ξ ∈ lts_essential_actions_left s1 ∧ ¬ s2 ↛[a] ∧ inter ξ a)).
  + eauto.
  + apply (IHl (lnot ++ [a])); [by simplify_list_eq|].
  intros x [Hin | Hin%elem_of_list_singleton]%elem_of_app; simplify_eq ; eauto. }
Qed.

Lemma search_co_steps_spec_1_right_not_refuses `{Prop_of_Inter S1 S2 A inter} 
  (s2 : S2) ξ s1:
  is_Some $ search_co_steps_right_not_refuses s2 ξ (elements $ lts_co_inter_action_right ξ s2) s1 ->
  { μ | (ξ ∈ lts_essential_actions_left s1 ∧ ¬ s2 ↛[μ] ∧ inter ξ μ)}.
Proof. apply (search_co_steps_spec_helper_right_not_refuses []); [done| intros ??; set_solver]. Qed.

Lemma search_co_steps_spec_1_right_not_refuses_rev `{Prop_of_Inter S1 S2 A}
  (s2 : S2) ξ s1:
  { μ | (ξ ∈ lts_essential_actions_left s1 ∧ ¬ s2 ↛[μ] ∧ inter ξ μ)} 
  -> is_Some $ search_co_steps_right_not_refuses s2 ξ (elements $ lts_co_inter_action_right ξ s2) s1.
Proof. apply (search_co_steps_spec_helper_right_not_refuses_rev []); [done| intros ??; set_solver]. Qed.

Lemma search_co_steps_spec_2_right_not_refuses `{Prop_of_Inter S1 S2 A inter}
  μ s2 l ξ s1:
  search_co_steps_right_not_refuses s2 ξ l s1 = Some μ →
  (ξ ∈ lts_essential_actions_left s1 ∧ ¬ s2 ↛[μ] ∧ inter ξ μ).
Proof.
  induction l; [done|]. simpl.
  destruct (decide (ξ ∈ lts_essential_actions_left s1 ∧ ¬ s2 ↛[a] ∧ inter ξ a)) ; [|eauto].
  intros ?. simplify_eq. done.
Qed.


#[global] Instance dec_co_act_refuses_essential_left `{Prop_of_Inter S1 S2 A}
       (s1: S1) (s2 : S2) (ξ : A)
      : Decision (inter_not_refuses_essential_left s1 s2 ξ).
Proof.
  destruct (decide (is_Some $ search_co_steps_right_not_refuses s2 ξ 
  (elements $ lts_co_inter_action_right ξ s2) s1)) as [wit | not_wit].
  + left. 
    eapply search_co_steps_spec_1_right_not_refuses in wit.
    destruct wit as (μ' & h1 & h2 & h3). repeat split; eauto.
    eapply lts_essential_action_spec_left in h1. eapply lts_refuses_spec2; eauto.
  + right. intros (μ' & h1 & h2 & h3 & h4).
    assert ({ μ | (ξ ∈ lts_essential_actions_left s1 ∧ ¬ s2 ↛[μ] ∧ inter ξ μ)}) as wit.
    eauto. eapply search_co_steps_spec_1_right_not_refuses_rev in wit.
    contradiction.
Qed.


Lemma transition_to_not_refuses_essential_left `{Prop_of_Inter S1 S2 A}
  (s1 : S1) (s2 : S2) (s'2 : S2) (ξ : A) : 
  { μ | s2 ⟶[μ] s'2 ∧ inter ξ μ ∧ ξ ∈ lts_essential_actions_left s1} 
  -> { μ | ¬lts_refuses s2 (ActExt $ μ) ∧ inter ξ μ ∧ ξ ∈ lts_essential_actions_left s1}.
Proof.
  intro Hyp. destruct Hyp as [μ [HypTr2 [inter_prop ess_act]]].  eexists. repeat split; eauto. eapply lts_refuses_spec2. exists s'2. eauto.
Qed.

Lemma not_refuses_to_transition_essential_left `{Prop_of_Inter S1 S2 A}
  (s1 : S1) (s2 : S2) (* (s'2 : S2) *) (ξ : A) : 
  { μ | ¬lts_refuses s2 (ActExt $ μ) ∧ inter ξ μ ∧ ξ ∈ lts_essential_actions_left s1} 
  -> {s'2 & { μ | s2 ⟶[μ] s'2 ∧ inter ξ μ ∧ ξ ∈ lts_essential_actions_left s1}}.
Proof.
  intro Hyp. destruct Hyp as [μ [HypNotStable2 [inter_prop ess_act]]]. eapply lts_refuses_spec1 in HypNotStable2. 
  destruct HypNotStable2 as [s'2 HypTr2]. eexists. eexists. repeat split; eauto.
Qed.

Definition com_with_ess_left `{Prop_of_Inter S1 S2 A} 
    (s1 : S1) (s2 : S2) (ξ : A) (μ : A)
 := ¬ s2 ↛[μ] ∧ inter ξ μ ∧ ξ ∈ lts_essential_actions_left s1.


Lemma some_witness1_right' `{Prop_of_Inter S1 S2 A}
  (s1 : S1) (s2 : S2) (ξ : A) : 
  (∃ μ : A, ¬ s2 ↛[μ] ∧ inter ξ μ ∧ ξ ∈ lts_essential_actions_left s1) 
  -> { μ | ¬ s2 ↛[μ] ∧ inter ξ μ ∧ ξ ∈ lts_essential_actions_left s1}.
Proof.
  intro Hyp. exact (choice (com_with_ess_left s1 s2 ξ) Hyp).
Qed.

Lemma some_witness1_right `{Prop_of_Inter S1 S2 A}
  (s1 : S1) (s2 : S2) (ξ : A) : 
  (∃ μ : A, ¬ s2 ↛[μ] ∧ inter ξ μ ∧ ξ ∈ lts_essential_actions_left s1) 
  -> { μ & { s'2 | s2 ⟶[μ] s'2 ∧ inter ξ μ ∧ ξ ∈ lts_essential_actions_left s1}}.
Proof.
  intro Hyp.
  eapply some_witness1_right' in Hyp.
  destruct Hyp as (μ & not_refuses & inter_h & ess_act).
  eapply lts_refuses_spec1 in not_refuses.
  destruct not_refuses as (s'2 & HypTr).
  exists μ. exists s'2. repeat split; eauto.
Qed.

(* Lemma some_witness2 {S2 A: Type} `{ExtAction A} (M2: Lts S2 A)  (s2 : S2) (ξ : A) : 
is_Some $ search_co_steps M1 s2 s'2 ξ (elements $ lts_dual_action ξ s2) -> { μ : A | ∃ s'2, s2 ⟶[μ] s'2 ∧ dual μ ξ ∧ essential ξ}.
Proof.
  intro Hyp. exists ξ. destruct Hyp as (μ & not_refuses & duo & ess_act).
  eapply lts_refuses_spec1 in not_refuses. destruct not_refuses as (s'2 & HypTr). exists μ. exists s'2. repeat split; eauto.
Qed.

Lemma some_witness2 {S2 A: Type} `{ExtAction A} (M2: Lts S2 A)  (s2 : S2) (ξ : A) : 
(∃ μ : A, ¬ s2 ↛[μ] ∧ dual μ ξ ∧ essential ξ) -> (∃ μ : A, {s'2 | s2 ⟶[μ] s'2 ∧ dual μ ξ ∧ essential ξ}).
Proof.
Admitted.
 *)
Fixpoint inter_lts_refuses_helper_essential_left (* {S1 S2 A: Type} `{ExtAction A} {M1: Lts S1 A} {M2: Lts S2 A} *)
  `{Prop_of_Inter S1 S2 A}
  (s1: S1) (s2: S2) (l: list A) : bool :=
  match l with
  | [] => true
  | ξ::bs =>
      if decide (inter_not_refuses_essential_left s1 s2 ξ)
        then false 
        else inter_lts_refuses_helper_essential_left s1 s2 bs
  end.


(* Definition not_co_act_refuses {S1 S2 A: Type} `{ExtAction A} (M1: Lts S1 A) (M2: Lts S2 A) (s1: S1) (s2 : S2) (ξ : A) :=
        essential ξ ∧ (∃ s'2 : S2, is_Some (search_co_steps M2 s2 s'2 ξ (elements $ lts_dual_action ξ s2))).

#[global] Instance dec_co_act_refuses {S1 S2 A: Type} `{ExtAction A} (M1: Lts S1 A) (M2: Lts S2 A) (s1: S1) (s2 : S2) (ξ : A)
      : Decision (not_co_act_refuses M1 M2 s1 s2 ξ).
Proof.   destruct (decide (essential ξ)).
  + assert (∀ μ2, μ2 ∈ lts_dual_action ξ s2 → {s'2 : S2 | essential ξ ∧ s2 ⟶[μ2] s'2 ∧ dual μ2 ξ}) as dual_def.
  intro μ2. eapply lts_dual_action_spec2. 
  case_eq (elements (lts_dual_action ξ s2)).
    ++ intro case1. right. intro contra. destruct contra as [ess_act Hyp]. rewrite case1 in Hyp. simpl in *.
       destruct Hyp as [x impossible]. inversion impossible. simplify_eq.
    ++ intros a l case2. left. destruct (dual_def a) as [s'2 Hyp]. eapply list_and_set. eassumption. split; eauto. exists s'2.
       rewrite case2. decompose record Hyp. assert (s2 ⟶[a] s'2 ∧ essential ξ ∧ dual a ξ). repeat split; eauto.
       assert ((if decide (s2 ⟶[a] s'2 ∧ essential ξ ∧ dual a ξ) then Some a else search_co_steps M2 s2 s'2 ξ l) = Some a) as eq.
       eapply decide_True; eauto. simpl. rewrite eq. eapply (mk_is_Some). reflexivity.
  + right. intro contra. destruct contra. contradiction.
Defined.

Fixpoint parallel_lts_refuses_helper {S1 S2 A: Type} `{ExtAction A} {M1: Lts S1 A} {M2: Lts S2 A}
  (s1: S1) (s2: S2) (l: list A) : bool :=
  match l with
  | [] => true
  | ξ::bs =>
      if decide (not_co_act_refuses M1 M2 s1 s2 ξ)
        then false 
        else parallel_lts_refuses_helper s1 s2 bs
  end. *)

Lemma inter_sts_refuses_helper_spec_1_essential_left `{Prop_of_Inter S1 S2 A}
  (s1: S1) (s2: S2) (l: list A) :
  inter_lts_refuses_helper_essential_left s1 s2 l = false → {s' | inter_step (s1, s2) τ s'}.
Proof.
  induction l as [| ξ l ]; [done|].
  simpl. destruct (decide (inter_not_refuses_essential_left s1 s2 ξ)) as [Hyp | Hyp]; eauto. intros _.
  destruct Hyp as [not_refuses1 act_founded]. eapply some_witness1_right in act_founded.
  destruct act_founded as (μ & s'2 & HypTr2 & duo & ess_act).
  apply lts_refuses_spec1 in not_refuses1 as [s'1 HypTr1].
  exists (s'1, s'2). eapply ParSync. exact duo. exact HypTr1. exact HypTr2.
Qed.

Lemma inter_sts_refuses_helper_spec_2_essential_left `{Prop_of_Inter S1 S2 A}
  (s1: S1) (s2: S2) ξ μ s'1 s'2 :
  s1 ⟶[ξ] s'1 → s2 ⟶[μ] s'2 → inter ξ μ → ξ ∈ lts_essential_actions_left s1 →
  inter_lts_refuses_helper_essential_left s1 s2 (elements $ lts_essential_actions_left s1) = false.
Proof.
  intros Hs1 Hs2 duo ess_act.
  assert (∀ l rest,
             (elements $ lts_essential_actions_left s1) = rest ++ l →
             (∀ ξ, ξ ∈ rest → ¬ (s1 ⟶[ξ] s'1 ∧ (exists μ, s2 ⟶[μ] s'2 ∧ inter ξ μ ∧ ξ ∈ lts_essential_actions_left s1 ))) →
             inter_lts_refuses_helper_essential_left s1 s2 l = false) as Hccl.
  induction l as [| b l IHl].
  - intros rest Hrest Hnots. (* pose proof (lts_essential_action_spec_left _ ξ ess_act Hs1) as Hin.  *)
    simplify_list_eq.
    exfalso. eapply Hnots; eauto. set_solver.
  - intros rest Hrest Hnots. simplify_list_eq.
    destruct (decide (inter_not_refuses_essential_left s1 s2 b)) as [case1 | case2]; [auto|].
    eapply (IHl (rest ++ [b])); [by simplify_list_eq|].
    intros x [Hin | ->%elem_of_list_singleton]%elem_of_app; [eauto|].
    intros [Hstep1 Hstep2]. eapply case2. split. eapply lts_refuses_spec2. exists s'1. assumption.
    destruct Hstep2 as (μ2 & Tr2 & duo2 & ess_act2). exists μ2. split. eapply lts_refuses_spec2. exists s'2. assumption.
    split; eauto. 
  - apply (Hccl _ []); eauto. set_solver.
Qed.




Definition inter_not_refuses_essential_right (* {S1 S2 A: Type} `{ExtAction A} (M1: Lts S1 A) (M2: Lts S2 A) *) 
  `{Prop_of_Inter S1 S2 A}
          (s1: S1) (s2 : S2) (ξ : A) :=
        ¬lts_refuses s2 (ActExt $ ξ) ∧ (∃ μ, ¬lts_refuses s1 (ActExt $ μ) ∧ inter μ ξ ∧ ξ ∈ lts_essential_actions_right s2). 
(*          ∧ (∃ s'2 : S2, is_Some (search_co_steps M2 s2 s'2 ξ (elements $ lts_dual_action ξ s2))). *)

(* Lemma inter_inter `{Prop_of_Inter S1 S2 A} p1 p2 ξ : {μ | μ ∈ lts_co_inter_action_right ξ p2 
              /\ ξ ∈ lts_essential_actions_left p1 /\ ¬lts_refuses p2 (ActExt $ μ) /\ inter ξ μ } + 
          {forall μ, μ ∈ lts_co_inter_action_right ξ p2 
          ->  lts_refuses p2 (ActExt $ μ) \/ ¬ inter ξ μ \/ ξ ∉ lts_essential_actions_left p1}.
Proof.
  remember (elements (lts_co_inter_action_right ξ p2)) as l.
  revert Heql. revert p2. revert p1. revert ξ.
  induction l as [| μ l]. 
  + intros. right. intros μ in_list. apply elem_of_elements in in_list.
    rewrite <-Heql in in_list. set_solver.
  + intros ξ p1 p2 elem_def. 
    destruct (decide (p2 ↛[μ])).
    ++ right. intros. destruct (decide (inter ξ μ)).
      +++ destruct (decide (ξ ∉ lts_essential_actions_left p1)). 
    
    destruct (decide ()).
    
    split; eauto. eapply elem_of_elements. set_solver. *)




Fixpoint search_co_steps_left_not_refuses `{Prop_of_Inter S1 S2 A inter} 
  (s1: S1) ξ candidates (s2 : S2) :=
  match candidates with
  | [] => None
  | μ :: xs =>
    if decide (ξ ∈ lts_essential_actions_right s2 /\ ¬lts_refuses s1 (ActExt μ) /\ inter μ ξ) 
      then Some μ
      else search_co_steps_left_not_refuses s1 ξ xs s2
  end.

Lemma search_co_steps_spec_helper_left_not_refuses `{Prop_of_Inter S1 S2 A inter}
  lnot (s1 : S1) l (ξ : A) (s2 : S2) :
  (elements $ lts_co_inter_action_left ξ s1) = lnot ++ l →
  (∀ μ, μ ∈ lnot → ¬ (ξ ∈ lts_essential_actions_right s2 ∧  ¬lts_refuses s1 (ActExt μ) 
  ∧ inter μ ξ)) →
  is_Some $ search_co_steps_left_not_refuses s1 ξ l s2 ->
  { μ | (ξ ∈ lts_essential_actions_right s2 ∧  ¬lts_refuses s1 (ActExt μ) ∧ inter μ ξ )}.
Proof.
  revert lnot. induction l; intros lnot.
  { simpl. intros Hels Hnots. intros Hc. exfalso. inversion Hc. done. }
  {intros Helems Hnots. simpl.
  destruct (decide (ξ ∈ lts_essential_actions_right s2 ∧ ¬lts_refuses s1 (ActExt a) ∧ inter a ξ)).
  + eauto.
  + apply (IHl (lnot ++ [a])); [by simplify_list_eq|].
  intros x [Hin | Hin%elem_of_list_singleton]%elem_of_app; simplify_eq ; eauto. }
Qed.

Lemma search_co_steps_spec_helper_left_not_refuses_rev `{Prop_of_Inter S1 S2 A inter} 
  lnot (s1 : S1) l ξ (s2 : S2) :
  (elements $ lts_co_inter_action_left ξ s1) = lnot ++ l →
  (∀ μ, μ ∈ lnot → ¬ (ξ ∈ lts_essential_actions_right s2 ∧ ¬lts_refuses s1 (ActExt μ) 
  ∧ inter μ ξ )) →
  { μ | (ξ ∈ lts_essential_actions_right s2 ∧ ¬lts_refuses s1 (ActExt μ) ∧ inter μ ξ )}  
  -> is_Some $ search_co_steps_left_not_refuses s1 ξ l s2.
Proof.
  revert lnot. induction l; intros lnot.
  { simpl. intros Hels Hnots. intros Hc. exfalso. inversion Hc as (μ & ess_act & Hstep & duo).
   eapply lts_refuses_spec1 in Hstep as (s'1 & Hstep); eauto.
   eapply (lts_co_inter_action_spec_left s1 s'1 ξ μ s2) in Hstep as Hyp; eauto.
   simplify_list_eq.
   eapply elem_of_elements in Hyp. eapply Hnots; eauto.
   repeat split; eauto. eapply lts_refuses_spec2. eauto. }
  { intros Helems Hnots. simpl.
  destruct (decide (ξ ∈ lts_essential_actions_right s2 ∧ ¬ s1 ↛[a] ∧ inter a ξ )).
  + eauto.
  + apply (IHl (lnot ++ [a])); [by simplify_list_eq|].
  intros x [Hin | Hin%elem_of_list_singleton]%elem_of_app; simplify_eq ; eauto. }
Qed.

Lemma search_co_steps_spec_1_left_not_refuses `{Prop_of_Inter S1 S2 A inter} 
  (s1 : S1) ξ s2:
  is_Some $ search_co_steps_left_not_refuses s1 ξ (elements $ lts_co_inter_action_left ξ s1) s2 ->
  { μ | (ξ ∈ lts_essential_actions_right s2 ∧ ¬ s1 ↛[μ] ∧ inter μ ξ )}.
Proof. apply (search_co_steps_spec_helper_left_not_refuses []); [done| intros ??; set_solver]. Qed.

Lemma search_co_steps_spec_1_left_not_refuses_rev `{Prop_of_Inter S1 S2 A}
  (s1 : S1) ξ s2:
  { μ | (ξ ∈ lts_essential_actions_right s2 ∧ ¬ s1 ↛[μ] ∧ inter μ ξ )} 
  -> is_Some $ search_co_steps_left_not_refuses s1 ξ 
      (elements $ lts_co_inter_action_left ξ s1) s2.
Proof. apply (search_co_steps_spec_helper_left_not_refuses_rev []); [done| intros ??; set_solver]. Qed.

Lemma search_co_steps_spec_2_left_not_refuses `{Prop_of_Inter S1 S2 A inter}
  μ s1 l ξ s2:
  search_co_steps_left_not_refuses s1 ξ l s2 = Some μ →
  (ξ ∈ lts_essential_actions_right s2 ∧ ¬ s1 ↛[μ] ∧ inter μ ξ).
Proof.
  induction l; [done|]. simpl.
  destruct (decide (ξ ∈ lts_essential_actions_right s2 ∧ ¬ s1 ↛[a] ∧ inter a ξ )) ; [|eauto].
  intros ?. simplify_eq. done.
Qed.

#[global] Instance dec_co_act_refuses_essential_right `{Prop_of_Inter S1 S2 A}
       (s1: S1) (s2 : S2) (ξ : A)
      : Decision (inter_not_refuses_essential_right (* M1 M2 *) s1 s2 ξ).
Proof. 
  destruct (decide (is_Some $ search_co_steps_left_not_refuses s1 ξ 
  (elements $ lts_co_inter_action_left ξ s1) s2)) as [wit | not_wit].
  + left. 
    eapply search_co_steps_spec_1_left_not_refuses in wit.
    destruct wit as (μ' & h1 & h2 & h3). repeat split; eauto.
    eapply lts_essential_action_spec_right in h1. eapply lts_refuses_spec2; eauto.
  + right. intros ( h1 & μ'  & h2 & h3 & h4).
    assert ({ μ | (ξ ∈ lts_essential_actions_right s2 ∧ ¬ s1 ↛[μ] ∧ inter μ ξ)}) as wit.
    eauto. eapply search_co_steps_spec_1_left_not_refuses_rev in wit.
    contradiction.
Qed.

Lemma transition_to_not_refuses_essential_right `{Prop_of_Inter S1 S2 A}
  (s1 : S1) (s2 : S2) (s'1 : S1) (ξ : A) : 
  { μ | s1 ⟶[μ] s'1 ∧ inter μ ξ ∧ ξ ∈ lts_essential_actions_right s2} 
  -> { μ | ¬lts_refuses s1 (ActExt $ μ) ∧ inter μ ξ ∧ ξ ∈ lts_essential_actions_right s2}.
Proof.
  intro Hyp. destruct Hyp as [μ [HypTr2 [inter_prop ess_act]]].  eexists. repeat split; eauto. 
  eapply lts_refuses_spec2. exists s'1. eauto.
Qed.

Lemma not_refuses_to_transition_essential_right `{Prop_of_Inter S1 S2 A}
  (s1 : S1) (s2 : S2) (* (s'2 : S2) *) (ξ : A) : 
  { μ | ¬lts_refuses s1 (ActExt $ μ) ∧ inter μ ξ ∧ ξ ∈ lts_essential_actions_right s2} 
  -> {s'1 & { μ | s1 ⟶[μ] s'1 ∧ inter μ ξ ∧ ξ ∈ lts_essential_actions_right s2}}.
Proof.
  intro Hyp. destruct Hyp as [μ [HypNotStable2 [inter_prop ess_act]]]. eapply lts_refuses_spec1 in HypNotStable2. 
  destruct HypNotStable2 as [s'2 HypTr2]. eexists. eexists. repeat split; eauto.
Qed.

Definition com_with_ess_right `{Prop_of_Inter S1 S2 A} 
    (s1 : S1) (s2 : S2) (ξ : A) (μ : A)
 := ¬ s1 ↛[μ] ∧ inter μ ξ ∧ ξ ∈ lts_essential_actions_right s2.

Lemma some_witness1_left' `{Prop_of_Inter S1 S2 A}
  (s1 : S1) (s2 : S2) (ξ : A) : 
  (∃ μ : A, ¬ s1 ↛[μ] ∧ inter μ ξ ∧ ξ ∈ lts_essential_actions_right s2)
  -> { μ | ¬ s1 ↛[μ] ∧ inter μ ξ ∧ ξ ∈ lts_essential_actions_right s2}.
Proof.
  intro Hyp. exact (choice (com_with_ess_right s1 s2 ξ) Hyp).
Qed.

Lemma some_witness1_left `{Prop_of_Inter S1 S2 A}
  (s1 : S1) (s2 : S2) (ξ : A) : 
  (∃ μ : A, ¬ s1 ↛[μ] ∧ inter μ ξ ∧ ξ ∈ lts_essential_actions_right s2)
  -> { μ & { s'1 | s1 ⟶[μ] s'1 ∧ inter μ ξ ∧ ξ ∈ lts_essential_actions_right s2}}.
Proof.
  intro Hyp.
  eapply some_witness1_left' in Hyp.
  destruct Hyp as (μ & not_refuses & inter_h & ess_act).
  eapply lts_refuses_spec1 in not_refuses.
  destruct not_refuses as (s'1 & HypTr).
  exists μ. exists s'1. repeat split; eauto.
Qed.


Fixpoint inter_lts_refuses_helper_essential_right (* {S1 S2 A: Type} `{ExtAction A} {M1: Lts S1 A} {M2: Lts S2 A} *)
  `{Prop_of_Inter S1 S2 A}
  (s1: S1) (s2: S2) (l: list A) : bool :=
  match l with
  | [] => true
  | ξ::bs =>
      if decide (inter_not_refuses_essential_right s1 s2 ξ)
        then false 
        else inter_lts_refuses_helper_essential_right s1 s2 bs
  end.


(* Definition not_co_act_refuses {S1 S2 A: Type} `{ExtAction A} (M1: Lts S1 A) (M2: Lts S2 A) (s1: S1) (s2 : S2) (ξ : A) :=
        essential ξ ∧ (∃ s'2 : S2, is_Some (search_co_steps M2 s2 s'2 ξ (elements $ lts_dual_action ξ s2))).

#[global] Instance dec_co_act_refuses {S1 S2 A: Type} `{ExtAction A} (M1: Lts S1 A) (M2: Lts S2 A) (s1: S1) (s2 : S2) (ξ : A)
      : Decision (not_co_act_refuses M1 M2 s1 s2 ξ).
Proof.   destruct (decide (essential ξ)).
  + assert (∀ μ2, μ2 ∈ lts_dual_action ξ s2 → {s'2 : S2 | essential ξ ∧ s2 ⟶[μ2] s'2 ∧ dual μ2 ξ}) as dual_def.
  intro μ2. eapply lts_dual_action_spec2. 
  case_eq (elements (lts_dual_action ξ s2)).
    ++ intro case1. right. intro contra. destruct contra as [ess_act Hyp]. rewrite case1 in Hyp. simpl in *.
       destruct Hyp as [x impossible]. inversion impossible. simplify_eq.
    ++ intros a l case2. left. destruct (dual_def a) as [s'2 Hyp]. eapply list_and_set. eassumption. split; eauto. exists s'2.
       rewrite case2. decompose record Hyp. assert (s2 ⟶[a] s'2 ∧ essential ξ ∧ dual a ξ). repeat split; eauto.
       assert ((if decide (s2 ⟶[a] s'2 ∧ essential ξ ∧ dual a ξ) then Some a else search_co_steps M2 s2 s'2 ξ l) = Some a) as eq.
       eapply decide_True; eauto. simpl. rewrite eq. eapply (mk_is_Some). reflexivity.
  + right. intro contra. destruct contra. contradiction.
Defined.

Fixpoint parallel_lts_refuses_helper {S1 S2 A: Type} `{ExtAction A} {M1: Lts S1 A} {M2: Lts S2 A}
  (s1: S1) (s2: S2) (l: list A) : bool :=
  match l with
  | [] => true
  | ξ::bs =>
      if decide (not_co_act_refuses M1 M2 s1 s2 ξ)
        then false 
        else parallel_lts_refuses_helper s1 s2 bs
  end. *)

Lemma inter_sts_refuses_helper_spec_1_essential_right `{Prop_of_Inter S1 S2 A}
  (s1: S1) (s2: S2) (l: list A) :
  inter_lts_refuses_helper_essential_right s1 s2 l = false → {s' | inter_step (s1, s2) τ s'}.
Proof.
  induction l as [| ξ l ]; [done|].
  simpl. destruct (decide (inter_not_refuses_essential_right s1 s2 ξ)) as [Hyp | Hyp]; eauto. intros _.
  destruct Hyp as [not_refuses1 act_founded]. eapply some_witness1_left in act_founded.
  destruct act_founded as (μ & s'1 & HypTr1 & duo & ess_act).
  apply lts_refuses_spec1 in not_refuses1 as [s'2 HypTr2].
  exists (s'1, s'2). eapply ParSync. exact duo. exact HypTr1. exact HypTr2.
Qed.

Lemma inter_sts_refuses_helper_spec_2_essential_right `{Prop_of_Inter S1 S2 A}
  (s1: S1) (s2: S2) μ ξ s'1 s'2 :
  s1 ⟶[μ] s'1 → s2 ⟶[ξ] s'2 → inter μ ξ → ξ ∈ lts_essential_actions_right s2 →
  inter_lts_refuses_helper_essential_right s1 s2 (elements $ lts_essential_actions_right s2) = false.
Proof.
  intros Hs1 Hs2 duo ess_act.
  assert (∀ l rest,
             (elements $ lts_essential_actions_right s2) = rest ++ l →
             (∀ ξ, ξ ∈ rest → ¬ (s2 ⟶[ξ] s'2 ∧ (exists μ, s1 ⟶[μ] s'1 ∧ inter μ ξ ∧ ξ ∈ lts_essential_actions_right s2 ))) →
             inter_lts_refuses_helper_essential_right s1 s2 l = false) as Hccl.
  induction l as [| b l IHl].
  - intros rest Hrest Hnots. (* pose proof (lts_essential_action_spec_left _ ξ ess_act Hs1) as Hin.  *)
    simplify_list_eq.
    exfalso. eapply Hnots; eauto. set_solver.
  - intros rest Hrest Hnots. simplify_list_eq.
    destruct (decide (inter_not_refuses_essential_right s1 s2 b)) as [case1 | case2]; [auto|].
    eapply (IHl (rest ++ [b])); [by simplify_list_eq|].
    intros x [Hin | ->%elem_of_list_singleton]%elem_of_app; [eauto|].
    intros [Hstep1 Hstep2]. eapply case2. split. eapply lts_refuses_spec2. exists s'2. assumption.
    destruct Hstep2 as (μ2 & Tr2 & duo2 & ess_act2). exists μ2. split. eapply lts_refuses_spec2. exists s'1. assumption.
    split; eauto. 
  - apply (Hccl _ []); eauto. set_solver.
Qed.


Definition inter_lts_refuses `{Prop_of_Inter S1 S2 A}
  (s1: S1) (s2: S2) (ℓ : Act A): Prop :=
  lts_refuses s1 ℓ ∧ lts_refuses s2 ℓ ∧
    match ℓ with
    | τ => inter_lts_refuses_helper_essential_left s1 s2 (elements $ lts_essential_actions_left s1)
        ∧ inter_lts_refuses_helper_essential_right s1 s2 (elements $ lts_essential_actions_right s2)
    | _ => True
    end.

(* Definition parallel_dual_action {S1 S2 A: Type} `{ExtAction A} {M1: Lts S1 A} {M2: Lts S2 A}
   (ξ : A) (s: S1*S2) : gset A := M1.(lts_dual_action) ξ s.1 ∪  M2.(lts_dual_action) ξ s.2.


Lemma parallel_dual_action_spec1 {S1 S2 A: Type} `{ExtAction A} {M1: Lts S1 A} {M2: Lts S2 A} (s : S1*S2) s' ξ μ : 
          essential ξ -> parallel_step s (ActExt μ) s' -> dual μ ξ -> μ ∈ parallel_dual_action ξ s.
Proof.
  intros ess_act Hstep duo. eapply elem_of_union.
  inversion Hstep; subst.
  + left. simpl. eapply lts_dual_action_spec1; eauto.
  + right. simpl. eapply lts_dual_action_spec1; eauto.
Qed.

Lemma parallel_dual_action_spec2_raw {S1 S2 A: Type} `{ExtAction A} {M1: Lts S1 A} {M2: Lts S2 A} 
          (s : S1*S2) ξ μ : μ ∈ parallel_dual_action ξ s ->
                            {μ ∈ M1.(lts_dual_action) ξ s.1} + {μ ∈ M2.(lts_dual_action) ξ s.2}.
Proof.
  intro Hyp. destruct (decide (μ ∈ M1.(lts_dual_action) ξ s.1)).
  + left. eauto.
  + right. eapply (elem_of_union (M1.(lts_dual_action) ξ s.1) (M2.(lts_dual_action) ξ s.2)) in Hyp.
    destruct Hyp. contradiction. assumption.
Qed.

Lemma parallel_dual_action_spec2 {S1 S2 A: Type} `{ExtAction A} {M1: Lts S1 A} {M2: Lts S2 A} 
          (s : S1*S2) ξ μ : μ ∈ parallel_dual_action ξ s
                            -> {s' | essential ξ /\ parallel_step s (ActExt μ) s' /\ dual μ ξ}.
Proof.
  intros Hyp. destruct s as (s1 & s2). simpl in *.
  apply parallel_dual_action_spec2_raw in Hyp. destruct Hyp as [ duo_in_M1 | duo_in_M2].
  + eapply lts_dual_action_spec2 in duo_in_M1. destruct duo_in_M1 as (s'1 & ess_act & HypTr & duo). 
    exists ((s'1,s2)). repeat split; eauto. now eapply ParLeft.
  + eapply lts_dual_action_spec2 in duo_in_M2. destruct duo_in_M2 as (s'2 & ess_act & HypTr & duo). 
    exists ((s1,s'2)). repeat split; eauto. now eapply ParRight.
Qed. *)




#[global] Instance inter_lts 
  `(inter : A -> A -> Prop)
  `{Prop_of_Inter S1 S2 A inter} :
  Lts (S1 * S2) A. 
Proof.
  refine (MkLts _ _ _ inter_step _ _ (λ s, inter_lts_refuses s.1 s.2) _ _ _).
  - intros [s1 s2] ℓ [s'1 s'2]. apply decide_inter_step.
  - intros ??. unfold inter_lts_refuses.
    apply and_dec; [apply _|apply and_dec; [apply _|]]. destruct α; apply _.
  - intros [a b] ℓ Hns. simpl in Hns. unfold inter_lts_refuses in Hns.
    destruct (decide (lts_refuses a ℓ)) as [|Hns1]; cycle 1.
    { apply lts_refuses_spec1 in Hns1 as [s' ?]. refine ((s', b) ↾ _). by constructor. }
    destruct (decide (lts_refuses b ℓ)) as [|Hns2]; cycle 1.
    { apply lts_refuses_spec1 in Hns2 as [s' ?]. refine ((a, s') ↾ _). by constructor. }
    destruct ℓ as [n|]; [exfalso; by apply Hns|].
    destruct (inter_lts_refuses_helper_essential_left a b (elements (lts_essential_actions_left a))) eqn:Hs1; cycle 1.
    { by apply inter_sts_refuses_helper_spec_1_essential_left in Hs1. }
    destruct (inter_lts_refuses_helper_essential_right a b (elements (lts_essential_actions_right b))) eqn:Hs2; cycle 1.
    { by apply inter_sts_refuses_helper_spec_1_essential_right in Hs2. } 
    exfalso. apply Hns; eauto.
  - intros [s1 s2] ℓ [[s'1 s'2] Hstep].
    unfold inter_lts_refuses. rewrite !not_and_l.
    inversion Hstep; simplify_eq; simpl.
    + pose proof (lts_refuses_spec2 _ _ (s'1 ↾ l)). eauto.
    + pose proof (lts_refuses_spec2 _ _ (s'2 ↾ l)). eauto.
    + eapply lts_essential_actions_spec_interact in eq as where_is_the_essential_action; eauto.
      destruct where_is_the_essential_action as [ ess_act1 | ess_act2].
      ++ assert (inter_lts_refuses_helper_essential_left s1 s2 (elements $ lts_essential_actions_left s1) = false) as Hccl; cycle 1.
        { right; right. intros [??]. by rewrite Hccl in *. }
        eapply inter_sts_refuses_helper_spec_2_essential_left; eauto.
      ++ assert (inter_lts_refuses_helper_essential_right s1 s2 (elements $ lts_essential_actions_right s2) = false) as Hccl; cycle 1.
        { right; right. intros [??]. by rewrite Hccl in *. }
        eapply inter_sts_refuses_helper_spec_2_essential_right; eauto.
Defined.

Class Sts (P: Type) := MkSts {
    sts_step: P → P → Prop;
    sts_state_eqdec: EqDecision P;
    sts_step_decidable: RelDecision sts_step;

    sts_refuses: P → Prop;
    sts_refuses_decidable p : Decision (sts_refuses p);
    sts_refuses_spec1 p : ¬ sts_refuses p -> { q | sts_step p q };
    sts_refuses_spec2 p : { q | sts_step p q } → ¬ sts_refuses p;
}.
#[global] Existing Instance sts_state_eqdec.
#[global] Existing Instance sts_step_decidable.
#[global] Existing Instance sts_refuses_decidable.

Definition istep `{Lts A} p q := lts_step p τ q.

#[global]
Program Instance sts_of_lts {P A} `{H : ExtAction A} (M: Lts P A): Sts P :=
  {|
    sts_step := istep;
    sts_refuses s := lts_refuses s τ;
  |}.
Next Obligation. intros ??????. apply _. Defined.
Next Obligation. intros ??????. by apply lts_refuses_spec1. Qed.
Next Obligation. intros ??????. by apply lts_refuses_spec2. Qed.

Section sts_executions.
  Context `{Sts P}.

  CoInductive max_exec_from: P -> Type :=
  | MExStop x (Hrefuses: sts_refuses x): max_exec_from x
  | MExStep x x' (Hstep: sts_step x x') (η: max_exec_from x'): max_exec_from x.

  CoInductive iexec_from: P -> Type :=
  | IExStep x x' (Hstep: sts_step x x') (η: iexec_from x'): iexec_from x.

  Inductive finexec_from: P -> Type :=
  | FExSingl x : finexec_from x
  | FExStep x x' (Hstep: bool_decide (sts_step x x')) (η: finexec_from x'): finexec_from x.

  Definition iexec_from_first {x:P} (η: iexec_from x) :=
    match η with IExStep x _ _ _ => x end.

  Record iexec := MkExec {
    iex_start: P;
    iex: iexec_from iex_start;
  }.

  Definition ex_cons x η (Hstep: sts_step x η.(iex_start)) : iexec :=
    MkExec x (IExStep _ _ Hstep η.(iex)).

  Inductive finexec :=
  | FinExNil: finexec
  | FinExNonNil x (ρ: finexec_from x): finexec.

  Definition fex_cons x p :=
    match p with
    | FinExNil => Some $ FinExNonNil x (FExSingl x)
    | FinExNonNil y p =>
        match decide (sts_step x y) with
        | right _ => None
        | left Hstep => Some $ FinExNonNil _ $ FExStep x y (bool_decide_pack _ Hstep) p
        end
    end.

  Fixpoint iex_take_from (n: nat) {x} (η: iexec_from x) : finexec_from x :=
    match n with
    | 0 => FExSingl x
    | S n => match η with IExStep x x' Hstep η' =>
             let p' := iex_take_from n η' in
             FExStep x x' (bool_decide_pack _ Hstep) p'
            end
    end.

  Fixpoint mex_take_from (n: nat) {x} (η: max_exec_from x) : option (finexec_from x) :=
    match n with
    | 0 => Some $ FExSingl x
    | S n => match η with
            | MExStop x Hrefuses => None
            | MExStep x x' Hstep η' =>
                let p' := mex_take_from n η' in
                (λ p', FExStep x x' (bool_decide_pack _ Hstep) p') <$> p'
            end
    end.

  Definition iex_take (n: nat) (η: iexec) : finexec :=
    match n with
    | 0 => FinExNil
    | S n => FinExNonNil η.(iex_start) (iex_take_from n η.(iex))
    end.

  Lemma iex_fex_take_from n {x y η} Hstep:
    iex_take_from (1+n) (IExStep x y Hstep η) = FExStep x y (bool_decide_pack _ Hstep) (iex_take_from n η).
  Proof. revert x y η Hstep. induction n as [|n IHn]; intros x y η Hstep; easy. Qed.

  Lemma iex_fex_take n {x η} Hstep:
    Some $ iex_take (1+n) (ex_cons x η Hstep) = fex_cons x (iex_take n η).
  Proof.
    case n; simpl; [easy|].
    intros ?. destruct (decide (sts_step x (iex_start η))); [|easy].
    do 3 f_equal. assert (ProofIrrel $ bool_decide (sts_step x (iex_start η))) by apply _. naive_solver.
  Qed.

  Fixpoint iex_snoc_from x (ex1: finexec_from x) (a: P) : option (finexec_from x) :=
    match ex1 with
    | FExSingl x =>
        if decide (sts_step x a)
        then Some (FExStep x _ ltac:(eauto) (FExSingl a))
        else None
    | FExStep x x' Hstep η =>
        match iex_snoc_from x' η a with
        | None => None
        | Some p => Some(FExStep x x' Hstep p)
        end
    end.

  Definition iex_snoc (ex1: finexec) (a: P) : option finexec :=
    match ex1 with
    | FinExNil => Some (FinExNonNil _ (FExSingl a))
    | FinExNonNil x η =>
        match iex_snoc_from x η a with
        | None => None
        | Some η => Some (FinExNonNil x η)
        end
    end.

  Fixpoint fex_from_last {x} (p: finexec_from x) : P :=
    match p with
    | FExSingl y => y
    | FExStep _ y _ p' => fex_from_last p'
    end.

  Definition fex_last (p: finexec) : option P :=
    match p with
    | FinExNil => None
    | FinExNonNil _ p' => Some $ fex_from_last p'
    end.

  Definition fex_first (p: finexec) : option P :=
    match p with
    | FinExNil => None
    | FinExNonNil x _ => Some x
    end.

  Lemma fex_snoc_from_valid_last x z ρ:
    sts_step (fex_from_last ρ) z →
    is_Some (iex_snoc_from x ρ z).
  Proof.
    revert z. induction ρ as [| y t Hbstep ρ IH]; intros z Hstep; simpl in *.
    - by destruct (decide (sts_step x z)).
    - by destruct (IH _ Hstep) as [? ->].
  Qed.

  Lemma fex_snoc_valid_last ex y z:
    fex_last ex = Some y →
    sts_step y z →
    is_Some (iex_snoc ex z).
  Proof.
    case ex; [easy|]. simpl. intros ??? Hstep. simplify_eq.
    by destruct (fex_snoc_from_valid_last _ _ _ Hstep) as [? ->].
  Qed.

  Definition finex_singl x := FinExNonNil x (FExSingl x).

  Definition iexec_from_tail {x:P} (η: iexec_from x) : iexec :=
    match η with IExStep x x' _ η => MkExec x' η end.

  Lemma iex_snoc_step x η1 η2 a:
    iex_snoc_from x η1 a = Some η2 →
    fex_from_last η2 = a ∧ sts_step (fex_from_last η1) (fex_from_last η2).
  Proof.
    revert η2 a; induction η1 as [|b c Hstep η1 IHη]; intros η2 a.
    - simpl. destruct (decide (sts_step x a)); [injection 1; intros ?; simplify_eq|]; easy.
    - simpl. destruct (iex_snoc_from c η1 a) as [p|] eqn:Heq;
        [injection 1; intros ?; simplify_eq|easy].
      simpl. by destruct (IHη _ _ Heq) as [??].
  Qed.
End sts_executions.

Class CountableSts P `{Sts P} := MkCsts {
    csts_states_countable: Countable P;
    csts_next_states_countable: ∀ x, Countable (dsig (fun y => sts_step x y));
}.
#[global] Existing Instance csts_states_countable.
#[global] Existing Instance csts_next_states_countable.

Class CountableLts P A `{Lts P A} := MkClts {
    clts_states_countable: Countable P;
    clts_next_states_countable: ∀ x ℓ, Countable (dsig (fun y => lts_step x ℓ y));
}.
#[global] Existing Instance clts_states_countable.
#[global] Existing Instance clts_next_states_countable.

#[global]
Instance csts_of_clts {P A} `{Lts P A} (M: CountableLts P A): CountableSts P.
Proof.
  apply MkCsts.
  - exact clts_states_countable.
  - intros ?. apply clts_next_states_countable.
Defined.

#[global]
Instance inter_clts {S1 S2 A: Type} `{H : ExtAction A}  `{!Lts S1 A} `{!Lts S2 A} 
`{M1: !CountableLts S1 A} 
`{M2: !CountableLts S2 A} `{inter : A -> A -> Prop} 
`{i : !Prop_of_Inter S1 S2 A inter}: CountableLts (S1 * S2) A.
Proof.
  apply MkClts.
  -  eapply prod_countable.
  - intros x ℓ. apply countable_sig. intros y.
    destruct (decide (bool_decide (x ⟶{ℓ} y))); [left | right]; done.
Qed.

#[global] Instance finite_countable_lts `{FiniteImageLts P A} : CountableLts P A.
Proof. constructor; first apply _. intros *; apply finite_countable. Qed.



(** Parallel Lts extended with parallel. *)

Definition parallel_inter `{ExtAction A} μ1 μ2 := dual μ2 μ1 . (* \/ dual μ2 μ1. *)

#[global] Instance parallel_inter_sym `{ExtAction A} : Symmetric parallel_inter.
Proof. intros μ1 μ2. intro Hyp. eapply duo_sym. assumption. Defined.

#[global] Program Instance parallel_Lts {P1 P2 A : Type} `{H : ExtAction A} (M1: Lts P1 A) (M2: Lts P2 A)
  `{Prop_of_Inter P1 P2 A parallel_inter} 
: Lts (P1 * P2) A := inter_lts parallel_inter. 

(* #[global] Program Instance parallel_inter_spec `{ExtAction A} : InteractionAction A.
Next Obligation.
  intros ? ? μ1 μ2. exact (parallel_inter μ1 μ2).
Defined.
Next Obligation.
  intros ? ? μ1 μ2. unfold parallel_inter_spec_obligation_1.
  eapply or_dec.
  + exact (d_dec μ1 μ2).
  + exact (d_dec μ2 μ1).
Defined.
 *)


(* à voir *)
(* Lemma parallel_step_commutative 
(*     {S1 S2 A: Type} `{H : ExtAction A}  `{!Lts S1 A} `{!Lts S2 A} `{M1: !CountableLts S1 A} 
    `{M2: !CountableLts S2 A} `{C : InteractionAction A} `{i : !Prop_of_Inter S1 S2 A} *)
    `{Prop_of_Inter P1 P2 A}
    (s1 s'1: P1) (s2 s'2: P2) ℓ:
    inter_step (s1, s2) ℓ (s'1, s'2) → inter_step (s2, s1) ℓ (s'2, s'1).
Proof.
  intros Hstep. inversion Hstep; subst.
    * now eapply ParRight.
    * now eapply ParLeft.
    * eapply symmetry in eq. eapply ParSync.
      - exact eq.
      - assumption.
      - assumption.
Qed.  *) 

(** Lts extended with forwarders. *)

(** A mailbox is a multiset of names. *)

Definition mb (A : Type) `{ExtAction A} := gmultiset A. (* {m : gmultiset A | forall η, η ∈ m -> non_blocking η}. *)


(* #[global] Program Instance fw_inter_spec {A: Type} (H : ExtAction A) : InteractionAction A.
Next Obligation.
  intros ? ? μ1 μ2. exact (fw_inter μ1 μ2).
Defined.
Next Obligation.
  intros ? ? μ1 μ2. unfold fw_inter_spec_obligation_1.
  eapply and_dec.
  + exact (d_dec μ1 μ2).
  + exact (nb_dec μ2).
Defined. *)

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


(* #[global] Instance ProofIr `{ExtAction A} : ∀ x, ProofIrrel (non_blocking x).
intros. intro. intro. Admitted. *)

(* À VOIR *)
(* Inductive lts_multiset_step `{ExtAction A} : {m : mb A | forall η, η ∈ m -> non_blocking η}
-> Act A -> {m : mb A | forall η, η ∈ m -> non_blocking η} -> Prop :=
| lts_multiset_add (m : {m' : mb A | forall η, η ∈ m' -> non_blocking η}) 
        (η : A) (μ : A)
    (duo : dual η μ) (nb : non_blocking η) 
    {H : (forall η', η' ∈ ({[+ η +]} ⊎ (proj1_sig m)) -> non_blocking η')}:
   lts_multiset_step m (ActExt μ) (exist _ ({[+ η +]} ⊎ (proj1_sig m)) H )
| lts_multiset_minus m η (nb : non_blocking η) 
    {H : (forall η', η' ∈ ({[+ η +]} ⊎ (proj1_sig m)) -> non_blocking η')} :  
   lts_multiset_step (exist _ ({[+ η +]} ⊎ (proj1_sig m)) H) (ActExt η) m. *)

Inductive lts_multiset_step `{ExtAction A} : mb A -> Act A -> mb A -> Prop :=
| lts_multiset_add m η μ (duo : dual η μ) (nb : non_blocking η) :
   lts_multiset_step m (ActExt μ) ({[+ η +]} ⊎ m) 
| lts_multiset_minus m η (nb : non_blocking η):  
   lts_multiset_step ({[+ η +]} ⊎ m) (ActExt η) m.

Global Hint Constructors lts_multiset_step:mdb.


(* Lemma non_blocking_action_in_ms `{ExtAction A}  mb1 η mb2 :  
    non_blocking η -> (* mb1 ⟶[η] mb2 *) lts_multiset_step mb1 (ActExt η) mb2 
    ->  {[+ η +]} ⊎ (proj1_sig mb2) = (proj1_sig mb1).
Proof.
  intros nb Hstep.
  inversion Hstep as [ ? μ ? duo nb'|]; subst.
  + simpl in *. 
    assert (nb'' : non_blocking μ); eauto.
    apply (lts_oba_fw_non_blocking_duo_spec μ η ) in nb''; eauto. contradiction.
  + eauto.
Qed. *)

Lemma non_blocking_action_in_ms `{ExtAction A}  mb1 η mb2 :  
    non_blocking η -> (* mb1 ⟶[η] mb2 *) lts_multiset_step mb1 (ActExt η) mb2 
    ->  {[+ η +]} ⊎ mb2 = mb1.
Proof.
  intros nb Hstep.
  inversion Hstep as [ ? μ ? duo nb'|]; subst.
  + simpl in *. 
    assert (nb'' : non_blocking μ); eauto.
    apply (lts_oba_fw_non_blocking_duo_spec μ η ) in nb''; eauto. contradiction.
  + eauto.
Qed.

(* Lemma blocking_action_in_ms `{ExtAction A}  mb1 μ mb2 :  
    ¬ non_blocking μ -> (* mb1 ⟶[η] mb2 *) lts_multiset_step mb1 (ActExt μ) mb2 
    ->  (* ∃ η,  *) ({[+ co μ +]} ⊎ (proj1_sig mb1) = (proj1_sig mb2) /\ (dual (co μ) μ /\ non_blocking (co μ))).
Proof.
  intros nb Hstep.
  inversion Hstep as [ ? η ? duo nb'|]; subst.
  + assert (η =  co μ) as eq. eapply unique_nb;eauto. subst. eauto.
  + contradiction.
Qed. *)

Lemma blocking_action_in_ms `{ExtAction A}  mb1 μ mb2 :  
    ¬ non_blocking μ -> (* mb1 ⟶[η] mb2 *) lts_multiset_step mb1 (ActExt μ) mb2 
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
    assert (¬ non_blocking μ).
    eapply lts_oba_fw_non_blocking_duo_spec; eauto. contradiction.
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


(* Definition lts_multiset_step_decidable `{ExtAction A} m α m' : Decision (lts_multiset_step m α m').
Proof.
(*   destruct m as (m & m_nb).
  destruct m' as (m' & m_nb'). *)
  destruct α as [μ |].
  + destruct (decide (non_blocking μ)) as [nb | not_nb].
    - rename μ into η. destruct (decide (proj1_sig m =  {[+ η +]} ⊎ proj1_sig m')); subst.
      ++ left. 
         destruct m'. destruct m. 
        rewrite e. eapply lts_multiset_minus; eauto.
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
Qed. *)

Definition lts_multiset_step_decidable `{ExtAction A} m α m' : Decision (lts_multiset_step m α m').
Proof.
(*   destruct m as (m & m_nb).
  destruct m' as (m' & m_nb'). *)
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
                                               else (* ¬ (∃ *) forall η', dual η' η -> ¬ non_blocking η'
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
      ++ left. eauto.
  + left. simpl. eauto.
Qed.

#[global] Program Instance MbLts `{H : ExtAction A} : Lts (mb A) A :=
{|
    lts_step m α m' := lts_multiset_step m α m' ;
    lts_refuses p := lts_multiset_refuses p;
    lts_step_decidable m α m' := lts_multiset_step_decidable m α m';
    lts_refuses_decidable m α := lts_multiset_refuses_decidable m α;
(*     lts_essential_actions p := lts_essential_actions p.1 ∪ dom p.2; *)
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

Definition fw_inter `{ExtAction A} μ2 μ1 := dual μ1 μ2 /\ non_blocking μ1.


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
      ¬ non_blocking μ ->  
        mb_without_not_nb_on_list (μ :: l) = mb_without_not_nb_on_list l.
Proof.
  intro nb.
  unfold mb_without_not_nb_on_list at 1.
  erewrite decide_False. fold mb_without_not_nb_on_list. reflexivity. eauto.
Qed.


Lemma lts_mb_nb_on_list_perm `{H : ExtAction A} (l1 : list A) (l2 : list A) :
  l1 ≡ₚ l2 ->  mb_without_not_nb_on_list l1 = mb_without_not_nb_on_list l2.
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

(* Parameter mb_without_not_nb : forall A : Type, forall H : ExtAction A, mb A -> mb A.
Arguments mb_without_not_nb {_} {_} _. *)

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
      ¬ non_blocking μ ->  
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
    η ∈ (mb_without_not_nb (m  : mb A)  : mb A) -> non_blocking η /\ η ∈ m.
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

(* à voir si l'on ajoute ou on garde *)
(* #[global] Program Instance inter_for_fw `{LtsP : @Lts P A H} :
  @Prop_of_Inter P (mb A) A fw_inter H LtsP MbLts.
Next Obligation.
  intros P A H LtsP p. exact (empty : gset A).
Defined.
Next Obligation.
  intros P A H LtsP p ξ Hyp.
  simpl in Hyp. inversion Hyp.
Qed.
Next Obligation.
  intros P A H LtsP m. exact (dom (mb_without_not_nb m)).
Defined.
Next Obligation.
  intros P A H LtsP  m ξ Hyp.
  unfold inter_for_fw_obligation_3 in Hyp.
  eapply gmultiset_elem_of_dom in Hyp.
  eapply lts_mb_nb_with_nb_spec1 in Hyp as (nb & mem).
  eapply gmultiset_disj_union_difference' in mem.
  exists (m ∖ {[+ ξ +]}).
  rewrite mem at 1.
  eapply lts_multiset_minus; eauto.
Qed.
Next Obligation.
  intros ? ? ? ? ? ? ? ? ? ? l1 l2 (duo & nb).
  right. unfold inter_for_fw_obligation_3.
  eapply non_blocking_action_in_ms in nb as eq; eauto. 
  eapply gmultiset_elem_of_dom. eapply lts_mb_nb_with_nb_spec2; eauto.
  multiset_solver.
Qed.
Next Obligation.
  intros P A H LtsP ξ p.
  exact empty. (* à redéfinir *)
Defined.
Next Obligation.
  intros. simpl in *. inversion H0.
Admitted.
Next Obligation.
  intros P A H LtsP μ p.
  exact empty.
Defined.
Next Obligation.
  intros.
  unfold inter_for_fw_obligation_1 in H1. set_solver.
Qed.
 *)


#[global] Program Instance FW_Lts {P A : Type} `{H : ExtAction A} (M: Lts P A) 
  `{@Prop_of_Inter P (mb A) A fw_inter H M MbLts}
    : Lts (P * mb A) A := inter_lts fw_inter. 


(** Stout reduction. *)

Reserved Notation "p ⟿{ m } q" (at level 30, format "p  ⟿{ m }  q").

Inductive strip `{LtsEq P A} : P -> gmultiset A -> P -> Prop :=
| strip_nil p p'(eq : p ⋍ p') : p ⟿{∅} p'
| strip_step p1 p2 p3 η m :
  non_blocking η -> p1 ⟶[η] p2 -> p2 ⟿{m} p3 -> p1 ⟿{{[+ η +]} ⊎ m} p3

where "p ⟿{ m } q" := (strip p m q).

(** Equivalence between forwarders. *)

Definition fw_eq `{LtsOba P A} (p : P * mb A) (q : P * mb A) :=
  forall (p' q' : P),
    p.1 ⟿{lts_oba_mo p.1} p' ->
    q.1 ⟿{lts_oba_mo q.1} q' ->
    p' ⋍ q' /\ lts_oba_mo p.1 ⊎ (mb_without_not_nb p.2) = 
        lts_oba_mo q.1 ⊎ (mb_without_not_nb q.2).

Infix "≐" := fw_eq (at level 70).

Lemma strip_eq_sim_ex `{LtsOba P A} {e e' m} :
  e ⟿{m} e' -> forall r, r ⋍ e -> exists r', r ⟿{m} r' /\ r' ⋍ e'.
Proof.
  intro w.
  dependent induction w; intros r heq.
  - exists r. split. constructor. reflexivity. etransitivity; eauto.
  - destruct (eq_spec r p2 (ActExt $ η)) as (r0 & l0 & heq0). eauto.
    destruct (IHw r0 heq0) as (r' & hwo' & heq').
    exists r'. split. eapply strip_step; eassumption. eassumption.
Qed.

Lemma strip_mem_ex `{LtsOba P A} {p1 p2 m η} :
  p1 ⟿{{[+ η +]} ⊎ m} p2 -> (exists p', p1 ⟶[η] p' /\ non_blocking η) .
Proof.
  intros hw.
  dependent induction hw.
  - multiset_solver.
  - assert (mem : η ∈ {[+ η0 +]} ⊎ m0). rewrite x. multiset_solver.
    eapply gmultiset_elem_of_disj_union in mem as [here | there].
    + eapply gmultiset_elem_of_singleton in here. subst. firstorder.
    + edestruct IHhw as (p & HypTr & nb) ; eauto.
      eapply gmultiset_disj_union_difference' in there; eassumption.
      edestruct (lts_oba_non_blocking_action_delay H2 H1 HypTr) as (u & l2 & l3).
      eauto.
Qed.

Lemma strip_eq_step `{@LtsOba P A IL LA LOA} {e e' m η} :
  e ⟿{{[+ η +]} ⊎ m} e' -> forall r, e ⟶[η] r -> exists t, r ⟿{m} t /\ t ⋍ e'.
Proof.
  intro w.
  dependent induction w.
  - multiset_solver.
  - intros r l.
    destruct (decide (η = η0)); subst.
    + assert (eq_rel p2 r) by (eapply lts_oba_non_blocking_action_deter; eassumption).
      eapply gmultiset_disj_union_inj_1 in x. subst.
      eapply strip_eq_sim_ex. eassumption. symmetry. assumption.
    + assert (m0 = {[+ η +]} ⊎ m ∖ {[+ η0 +]}) by multiset_solver.
      assert (η ≠ η0) by set_solver.
      edestruct (lts_oba_non_blocking_action_confluence H1 H3 H0 l)
        as (t0 & l0 & (r1 & l1 & heq1)).
      eapply IHw in H2 as (t & hwo & heq); eauto.
      assert (mem : η0 ∈ m) by multiset_solver.
      eapply gmultiset_disj_union_difference' in mem. rewrite mem.
      edestruct (strip_eq_sim_ex hwo r1 heq1) as (t2 & hw2 & heq2).
      exists t2. split. eapply strip_step. eassumption. eassumption. eassumption.
      etrans; eassumption.
Qed.

Lemma strip_m_deter `{LtsOba P A} {m p p1 p2} :
  p ⟿{m} p1 -> p ⟿{m} p2 -> p1 ⋍ p2.
Proof.
  revert p p1 p2.
  induction m using gmultiset_ind; intros p p1 p2 hw1 hw2.
  - inversion hw1; inversion hw2; subst; try multiset_solver. 
    eapply symmetry in eq. etransitivity; eauto.
  - destruct (strip_mem_ex hw1) as (t1 & lt1). destruct lt1 as [ lt1 nb1].
    destruct (strip_mem_ex hw2) as (t2 & lt2). destruct lt2 as [ lt2 nb2].
    eapply strip_eq_step in hw1 as (r1 & hwr1 & heqr1); eauto.
    eapply strip_eq_step in hw2 as (r2 & hwr2 & heqr2); eauto.
    etrans. symmetry. eassumption.
    symmetry. etrans. symmetry. eassumption. eauto.
Qed.

Lemma strip_eq_sim `{LtsOba P A} {p q p' q' m} :
  p ⋍ q -> strip p m p' -> strip q m q' -> p' ⋍ q'.
Proof.
  intros heq hsp hsq.
  edestruct (strip_eq_sim_ex hsq) as (r & hsp' & heqr); eauto.
  transitivity r. eapply strip_m_deter; eauto. eassumption.
Qed.

Lemma fw_eq_refl `{LtsOba P A} : Reflexive fw_eq.
Proof.
  intros p p1 q2 hw1 hw2. split; [eapply strip_m_deter|]; eauto.
Qed.

Global Hint Resolve fw_eq_refl:mdb.

Lemma lts_oba_mo_eq `{LtsOba P A} {p q} : p ⋍ q -> lts_oba_mo p = lts_oba_mo q.
Proof.
  remember (lts_oba_mo p) as hmo.
  revert p q Heqhmo.
  induction hmo using gmultiset_ind; intros p q Heqhmo heq.
  - eapply leibniz_equiv. intros η.
    rewrite multiplicity_empty.
    destruct (nb_dec η).
    destruct (lts_refuses_decidable q (ActExt $ η)).
    + destruct (decide (η ∈ lts_oba_mo q)).
      ++ eapply (* lts_oba_mo_spec1, *) lts_oba_mo_spec_bis2 in e as (t & hl).
         eapply lts_refuses_spec2 in l. multiset_solver. destruct hl. now exists t. (* pourquoi ne marche pas ? => now eauto. *)
      ++ destruct (multiplicity η (lts_oba_mo q)) eqn:eq; multiset_solver.
    + eapply lts_refuses_spec1 in n0 as (t & hl).
      edestruct (eq_spec p t (ActExt $ η)) as (u & hlu & hequ); eauto with mdb. 
      eapply lts_oba_mo_spec_bis1 (* , lts_oba_mo_spec1 *) in hlu. multiset_solver. assumption.
    + eapply lts_oba_mo_non_blocking_contra in n. instantiate (1 := q) in n. multiset_solver.
  - assert {t | non_blocking x /\ p ⟶[x] t} as (t & hlt).
    eapply lts_oba_mo_spec_bis2. (* , lts_oba_mo_spec1. *) multiset_solver. destruct hlt as [nb hlt].
    edestruct (eq_spec q t (ActExt $ x)) as (u & hlu & hequ).
    exists p. split. now symmetry.  assumption. 
    eapply lts_oba_mo_spec2 in hlu, hlt.
    assert (x ∈ lts_oba_mo q) as mem by multiset_solver .
    eapply gmultiset_disj_union_difference' in mem.
    rewrite hlu.
    assert (hmo = lts_oba_mo t).
    eapply gmultiset_disj_union_inj_1. etrans; eassumption.
    eapply gmultiset_eq_pop_l. eapply IHhmo. eassumption. now symmetry. assumption. assumption.
Qed.

Lemma fw_eq_id_mb `{LtsOba P A} p q m : p ⋍ q -> fw_eq (p, m) (q, m).
Proof.
  intros heq p' q' hwp hwq. simpl in *.
  set (h := lts_oba_mo_eq heq).
  split. rewrite <- h in hwq. eapply (strip_eq_sim heq hwp hwq).
  multiset_solver.
Qed.

(** The structural congruence is symmetric. *)

Lemma fw_eq_symm `{LtsOba P A} : Symmetric fw_eq.
Proof.
  intros p q heq.
  intros q2 p2 hw1 hw2.
  destruct (heq p2 q2 hw2 hw1) as (heq2 & hmo2). naive_solver.
Qed.

Global Hint Resolve fw_eq_symm:mdb.

(** Lemmas about strip. *)

Lemma lts_oba_mo_strip `{LtsOba P A} (p : P) : exists (q : P), strip p (lts_oba_mo p) q.
Proof.
  remember (lts_oba_mo p) as ns.
  revert p Heqns.
  induction ns using gmultiset_ind; intros.
  - exists p. constructor. reflexivity.
  - assert (mem : x ∈ lts_oba_mo p) by multiset_solver.
    assert (exists q, non_blocking x /\ p ⟶[x] q) as (q & l).
    
    eapply (* lts_oba_mo_spec1, *) lts_oba_mo_spec_bis2 in mem as (q & nbTr); eauto.
    destruct l as (nb & l).
    
    set (h := lts_oba_mo_spec2 p x q nb l) in mem.
    assert (ns = lts_oba_mo q) as mb_name. rewrite <- Heqns in h. multiset_solver.
    eapply IHns in mb_name as (q0 & hw).
    exists q0. eapply strip_step; eassumption.
Qed.

(** The structural congruence is transitive. *)

Lemma fw_eq_trans `{LtsOba P A} : Transitive fw_eq.
Proof.
  intros p q t.
  intros heq1 heq2 p2 t2 hwp hwt.
  edestruct (lts_oba_mo_strip q.1) as (q2 & hwq).
  destruct (heq1 p2 q2 hwp hwq) as (heq3 & heq4).
  destruct (heq2 q2 t2 hwq hwt) as (heq5 & heq6).
  split. etrans; naive_solver. multiset_solver.
Qed.

Global Hint Resolve fw_eq_trans:mdb.

(** Congruence is an Equivalence. *)

Lemma fw_eq_equiv `{LtsOba P A} : Equivalence fw_eq.
Proof. constructor; eauto with mdb. Qed.

Global Hint Resolve fw_eq_equiv:mdb.

(* #[global] Program Instance Lts_of_OBA `{LtsOba P A} : Lts P A.
Next Obligation.
intros. := . *)

(* Parameter (P : Type).
Parameter (A : Type).
Parameter (H : ExtAction A).
Parameter (LL : @Lts P A H).

Check ((FW_Lts LL).(lts_step)). *)
Definition lts_fw_sc
  `{M1 : @LtsOba P A H LtsP LtsEqP}
  `{@Prop_of_Inter P (mb A) A fw_inter H LtsP MbLts}
  (p : P * mb A) α (q : P * mb A) :=
  exists r, ((FW_Lts LtsP).(lts_step) p α r) /\ r ≐ q.

Notation "p ⟶≐ q" := (lts_fw_sc p τ q) (at level 90, format "p  ⟶≐  q").
Notation "p ⟶≐{ α } q" := (lts_fw_sc p α q) (at level 90, format "p  ⟶≐{ α }  q").
Notation "p ⟶≐[ μ ] q" := (lts_fw_sc p (ActExt μ) q) (at level 90, format "p  ⟶≐[ μ ]  q").

Lemma strip_retract_act `{LtsOba P A}
  {p q m t α} : p ⟿{m} q -> q ⟶{α} t -> exists r t', p ⟶{α} r /\ r ⟿{m} t' /\ t ⋍ t'.
Proof.
  intros HypStrip HypTr. 
  induction HypStrip as [| ? ? ? ? ? nb HypTr' ?  InductionHyp]; eauto.
  + edestruct (eq_spec p t) as (t' & l & equiv). exists p'. split; eauto.
    exists t', t. repeat split; eauto. constructor;eauto. reflexivity.
  + eapply InductionHyp in HypTr as (r & t' & l & hwo & heq).
    edestruct (lts_oba_non_blocking_action_delay nb HypTr' l) as (u & l1 & (r' & lr' & heqr')).
    edestruct (strip_eq_sim_ex hwo _ heqr') as (t0 & hwo0 & heq0).
    exists u, t0. repeat split; eauto. eapply strip_step; eassumption.
    etrans. eassumption. now symmetry.
Qed.


(* Inductive ForallMSET `{H : ExtAction} (P : A → Prop) : 
      gmultiset A → Prop :=
    | Forall_nil : ForallMSET P ∅ 
    | Forall_cons : ∀ (x : A) (m : gmultiset A), P x → ForallMSET P m 
            → ForallMSET P ({[+ x +]} ⊎ m).

(* Lemma simplifyMSET {A : Type} `{H : ExtAction A} P η m : ForallMSET P ({[+ η +]} ⊎ m) 
-> P η /\ ForallMSET P m.
Admitted. *)

Lemma simplifyMSET {A : Type} `{H : ExtAction A} (P : A -> Prop) (η : A) (m : gmultiset A) : 
      ForallMSET P ({[+ η +]} ⊎ m) -> P η /\ ForallMSET P m.
Proof.
  revert η.
  induction m using gmultiset_ind; intros.
  + assert (ForallMSET P ({[+ η +]})). admit.
    inversion H1; subst. assert (x = η). multiset_solver. subst.
    split;eauto; try constructor.
  + inversion H0. multiset_solver.
    assert (η ∈ {[+ x0 +]} ⊎ m0). multiset_solver.
    destruct (decide (x0 = η)) as [eq | not_eq ].
    ++ subst. split. eauto. 
       assert (ForallMSET P ({[+ η +]} ⊎ m0)).
       econstructor; eauto.
       admit.
    ++ admit. 
Admitted. *)

(* Lemma SimplifyMultiSet_and_eq : forall μ η m, μ ∉ {[+ η +]} ⊎ m -> μ ≠ η /\ μ ∉ m. *)

Lemma strip_delay_action_not_in_m `{LtsOba P A} {p q m t μ} :
  μ ∉ m -> p ⟿{m} q -> p ⟶[μ] t -> exists r, q ⟶[μ] r.
Proof.
  intros not_in_mem HypStrip HypTr. revert t not_in_mem HypTr.
  induction HypStrip as [? ? equiv| ? ? ? ? ? nb HypTr' HypStrip]. 
  + intros. symmetry in equiv. 
    edestruct (eq_spec p' t) as (p'' & l' & equiv'). exists p. split; eauto.
    exists p''. eauto.
  + intros.
    assert (neq : μ ≠ η /\ μ ∉ m) by now multiset_solver. destruct neq as [neq not_in].
    edestruct (lts_oba_non_blocking_action_confluence nb neq HypTr' HypTr) as (r & l1 & l2). eauto.
Qed.

Lemma strip_delay_m `{LtsOba P A} {p q m t μ} :
  μ ∉ m ->
  p ⟿{m} q -> p ⟶[μ] t -> exists r, t ⟿{m} r.
Proof.
  intros Hyp hwp hlp. revert p q t μ Hyp hwp hlp.
  induction m using gmultiset_ind; intros.
  - inversion hwp.
    + subst. exists t. eapply strip_nil. reflexivity.
    + multiset_solver.
  - eapply strip_mem_ex in hwp as h0.
    destruct h0 as (e & hle). destruct hle as [hle nb].
    assert (neq : μ ≠ x /\ μ ∉ m) by now multiset_solver. destruct neq as [neq not_in].
    edestruct (lts_oba_non_blocking_action_confluence nb neq hle hlp) as (u & l2 & l3).
    destruct l3 as (v & hlv & heqv).
    eapply strip_eq_step in hle as h1; eauto. destruct h1 as (r & hwr & heqr).
    destruct (IHm _ _ _ _ not_in hwr l2) as (r0 & hwu).
    edestruct (strip_eq_sim_ex hwu v heqv) as (w & hww & heqw).
    exists w. eapply strip_step; eauto.
Qed. 

Lemma strip_after `{LtsOba P A} {p q m} :
  strip p m q -> lts_oba_mo p = m ⊎ lts_oba_mo q.
Proof.
  intros hwp. revert p q hwp.
  induction m using gmultiset_ind; intros.
  - inversion hwp; subst. 
    -- assert (∅ ⊎ lts_oba_mo q = lts_oba_mo q) as mem by multiset_solver.
       rewrite mem. eapply lts_oba_mo_eq; eauto.
    -- multiset_solver.
  - eapply strip_mem_ex in hwp as h0.
    destruct h0 as (e & hle). destruct hle as [hle nb].
    eapply strip_eq_step in hle as h1; eauto. destruct h1 as (r & hwr & heqr).
    eapply lts_oba_mo_spec2 in hle.
    rewrite hle. eapply IHm in hwr.
    rewrite hwr.
    rewrite gmultiset_disj_union_assoc.
    eapply gmultiset_eq_pop_l.
    eapply lts_oba_mo_eq. eassumption. eassumption.
Qed.

Lemma strip_aux2 `{LtsOba P A} {p q q' m} :
  p ⋍ q -> strip q m q' -> exists p', strip p m p' /\ p' ⋍ q'.
Proof.
  intros hwp1 hwp. revert p hwp1.
  dependent induction hwp; intros.
  - exists p. split; eauto. constructor. eauto.
  - edestruct (eq_spec p p2) as (p' & l & equiv). exists p1. split; eauto.
    edestruct (IHhwp p') as (p'3 & stripped & equiv'); eauto.
    exists p'3.
    split. econstructor; eauto. eauto.
Qed.

Lemma strip_aux1 `{LtsOba P A} {p q t m1 m2} :
  strip p m1 t -> strip p (m1 ⊎ m2) q -> exists r, strip t m2 r /\ r ⋍ q.
Proof.
  intros hwp1 hwp. revert q m2 hwp.
  dependent induction hwp1; intros.
  - rewrite gmultiset_disj_union_left_id in hwp.
    symmetry in eq. eapply strip_aux2 in eq; eauto.
  - rewrite <- gmultiset_disj_union_assoc in hwp.
    eapply strip_eq_step in hwp as (r1 & hwr1 & heqr1); eauto.
    destruct (IHhwp1 _ _ hwr1) as (u & hwp3 & hequ).
    exists u. split. eassumption. transitivity r1; eauto.
Qed.

Lemma strip_delay_inp4 `{LtsOba P A} {p q t μ} :
  ¬ non_blocking μ -> p ⟶[μ] t -> strip t (lts_oba_mo p) q -> exists r, strip p (lts_oba_mo p) r /\ r ⟶⋍[μ] q.
Proof.
  intros Not_nb hlp hwt.
  remember (lts_oba_mo p) as pmo.
  revert p q t μ Not_nb hwt hlp Heqpmo.
  induction pmo using gmultiset_ind; intros.
  - inversion hwt.
    + subst. exists p. split. eapply strip_nil. reflexivity. exists t. split. assumption. eauto.
    + multiset_solver.
  - assert (mem : x ∈ lts_oba_mo p) by multiset_solver.
    eapply lts_oba_mo_spec_bis2 in mem as (p1 & hlp1). destruct hlp1 as [nb hlp1].
    assert (neq : μ ≠ x).  eapply BlockingAction_are_not_non_blocking; eauto.
    edestruct (lts_oba_non_blocking_action_confluence nb neq hlp1 hlp) as (u & l2 & l3).
    destruct l3 as (u' & hlu & hequ).
    eapply strip_eq_step in hlu as h1; eauto. destruct h1 as (r & hwr & heqr).
    edestruct (strip_eq_sim_ex hwr u (symmetry hequ)) as (r' & hwu & heqr').
    eapply lts_oba_mo_spec2 in hlp1 as hmop.
    assert (hmoeq : pmo = lts_oba_mo p1) by multiset_solver.
    destruct (IHpmo p1 r' u μ Not_nb hwu l2 hmoeq) as (pt & hwpt & hlpt).
    exists pt. split. eapply strip_step; eauto.
    destruct hlpt as (r0 & hlpt & heqt0).
    exists r0. split. eassumption.
    transitivity r'. eassumption.
    transitivity r. eassumption. eassumption. eassumption.
Qed.

Notation "p ▷ m" := (p, m) (at level 60).

Lemma fw_eq_input_simulation `{LtsOba P A} {p q mp mq μ q'} :
   p ▷ mp ≐ q ▷ mq -> ¬ non_blocking μ  -> q ⟶[μ] q' ->
  exists p', p ⟶[μ] p' /\ p' ▷ mp ≐ q' ▷ mq.
Proof.
  intros heq not_nb hlq. 
  edestruct (lts_oba_mo_strip p) as (p0 & hwp).
  edestruct (lts_oba_mo_strip q) as (q0 & hwq).
  edestruct (heq p0 q0) as (heqp0 & heqm); eauto. simpl in *.
  eapply lts_oba_mo_non_blocking_contra in not_nb as not_in. instantiate (1 := q) in not_in.
  edestruct (strip_delay_m not_in hwq hlq) as (q1 & hwq').
  edestruct (strip_delay_inp4 not_nb hlq hwq') as (q2 & hwq2 & hlq2).
  assert (q0 ⋍ q2) by (eapply strip_m_deter; eauto).
  destruct hlq2 as (r & hlr & heqr).
  edestruct (eq_spec p0 r (ActExt $ μ)) as (p0' & hlp0' & heqp0').
  exists q2. split; eauto. transitivity q0; eauto.
  edestruct (strip_retract_act hwp hlp0' ) as (p' & p1 & wp' & hwp' & heqp').
  exists p'. split. eassumption.
  intros pt qt hwpt hwqt. simpl in *.
  assert (heq1 : lts_oba_mo p' = lts_oba_mo p ⊎ lts_oba_mo p1).
  eapply strip_after; eauto.
  assert (heq2 : lts_oba_mo q' = lts_oba_mo q ⊎ lts_oba_mo q1).
  eapply strip_after; eauto.
  assert (heq3 : lts_oba_mo p1 = lts_oba_mo q1).
  eapply lts_oba_mo_eq. transitivity p0'. now symmetry. transitivity r; eauto.
  split.
  - rewrite heq1 in hwpt.
    rewrite heq2 in hwqt.
    eapply strip_aux1 in hwpt as (pt' & hwp1 & heqpt'); eauto.
    eapply strip_aux1 in hwqt as (qt' & hwq1 & heqqt'); eauto.
    transitivity pt'. now symmetry.
    transitivity qt'.
    assert (heq0 : p1 ⋍ q1).
    transitivity p0'. now symmetry. transitivity r; eauto.
    eapply (strip_eq_sim heq0); eauto.
    now rewrite heq3. assumption.
  - multiset_solver.
Qed.


Lemma strip_delay_tau `{LtsOba P A} {p q m t} :
  p ⟿{m} q -> p ⟶ t ->
  (exists η μ r, dual η μ /\ non_blocking η /\ p ⟶[η] r /\ r ⟶⋍[μ] t) \/ (exists r w, q ⟶ r /\ t ⟿{m} w /\ w ⋍ r).
Proof.
  intros hr hl. revert t hl.
  induction hr as [| ? ? ? ? ? nb HypTr' ?]; intros.
  + right. edestruct (eq_spec p' t) as (p'' & l & equiv). symmetry in eq. exists p. split;eauto.
    exists p'', t. repeat split; eauto. eapply strip_nil. reflexivity. symmetry; eauto.
  + edestruct (lts_oba_non_blocking_action_tau nb HypTr' hl) as [(r & l1 & l2)|].
    ++ eapply IHhr in l1 as [(b & c & r' & duo & nb' & l3 & l4) |(u, (w, (hu & hw & heq)))].
       +++ edestruct (lts_oba_non_blocking_action_delay nb HypTr' l3) as (z & l6 & l7).
           left. exists b, c , z. split. assumption. split. assumption. split. assumption.
           destruct l7 as (t0 & hlt0 & eqt0).
           destruct l4 as (t1 & hlt1 & eqt1).
           destruct (eq_spec t0 t1 (ActExt $ c)) as (t2 & hlt2 & eqt2); eauto.
           edestruct (lts_oba_non_blocking_action_delay nb hlt0 hlt2) as (w & lw1 & lw2).
           exists w. split. assumption.
           destruct l2 as (v1 & hlv1 & heqv1).
           destruct lw2 as (u1 & hlu1 & hequ1).
           eapply (lts_oba_non_blocking_action_deter_inv η); try eassumption. 
           etrans. eassumption.
           etrans. eassumption.
           etrans. eassumption.
           now symmetry.
       +++ right.
           destruct l2 as (r' & hlr' & heqr').
           destruct (strip_eq_sim_ex hw _ heqr') as (w' & hww' & heqw').
           exists u, w'. repeat split. assumption. eapply strip_step; eauto.
           etrans; eauto.
    ++ destruct H1 as (μ & duo & r & hlr & heq).
       left. exists η, μ. exists p2. split; eauto. split. eassumption. split. eauto. exists r. eauto.
Qed.

Lemma lts_fw_eq_spec_left_tau
  `{M : @LtsObaFB P A H LtsP LtsEqP V}
  `{@Prop_of_Inter P (mb A) A fw_inter H LtsP MbLts}
  (p : P) (q : P) q' (mp : mb A) (mq : mb A) :
  p ▷ mp ≐ q ▷ mq -> q ⟶ q' -> p ▷ mp ⟶≐ q' ▷ mq.
Proof.
  intros heq l.
  edestruct (lts_oba_mo_strip q) as (q0 & hwq).
  edestruct (lts_oba_mo_strip p) as (p0 & hwp).
  edestruct (heq p0 q0) as (heq0 & heqm0); eauto. simpl in *.
  destruct (strip_delay_tau hwq l) as
    [(a & b & q1 & duo & nb  & l1 & l2) | (qt & q1 & hltqt & hwq1 & heq1)].
  - destruct l2 as (q'' & hlq1 & heq'').
    edestruct (lts_oba_non_blocking_action_delay nb l1 hlq1) as (q2 & hlq & hlq2).
    assert (¬ non_blocking b) as not_nb. eapply lts_oba_fw_non_blocking_duo_spec; eauto.
    edestruct (fw_eq_input_simulation heq not_nb hlq) as (p2 & hlp_inp & heqp2).
    assert (mem : a ∈ lts_oba_mo p ⊎ (mb_without_not_nb mp))
      by (eapply lts_oba_mo_spec_bis1 in l1; multiset_solver).
    eapply gmultiset_elem_of_disj_union in mem as [hleft | hright].
    + assert {p1 | non_blocking a /\ p ⟶[a] p1} as (p1 & nb1 & tr1)
          by now eapply lts_oba_mo_spec_bis2.
      (* p ->[!a] p1 *)
      assert (neq : b ≠ a). now eapply BlockingAction_are_not_non_blocking. 
      edestruct (lts_oba_non_blocking_action_confluence nb neq tr1 hlp_inp)
        as (p'' & hlp1 & hlp2).
      (* p1 ->[a] p''   p2 ->[!a] p'' *)
      destruct (lts_oba_fb_feedback nb duo tr1 hlp1)
        as (p' & hlp_tau & heqp').
      exists (p', mp). split. 

      eapply ParLeft. (*nécessaire ?*)  eauto with mdb.

      intros pt qt hwpt hwqt. simpl in *.
      edestruct (lts_oba_mo_strip p2) as (pt' & hwpt').
      edestruct (lts_oba_mo_strip q2) as (qt' & hwqt').
      edestruct heqp2 as (heqpqt' & heqmpt'); eauto; simpl in *.
      destruct hlp2 as (p''' & hlp2 & heqp'').
      assert (heqm1 : lts_oba_mo p2 = {[+ a +]} ⊎ lts_oba_mo p').
      replace (lts_oba_mo p') with (lts_oba_mo p''').
      now eapply lts_oba_mo_spec2.
      eapply lts_oba_mo_eq. etrans. eapply heqp''. now symmetry.
      destruct hlq2 as (q''' & hlq2 & heqq'').
      assert (heqm2 : lts_oba_mo q2 = {[+ a +]} ⊎ lts_oba_mo q').
      replace (lts_oba_mo q') with (lts_oba_mo q''').
      now eapply lts_oba_mo_spec2.
      eapply lts_oba_mo_eq. etrans. eapply heqq''. now symmetry.
      split.
      ++ rewrite heqm1 in hwpt'. rewrite heqm2 in hwqt'.
         eapply strip_eq_step in hwpt' as (pr & hwpr & heqpr); eauto.
         eapply strip_eq_step in hwqt' as (qr & hwqr & heqqr); eauto.
         etrans. eapply strip_eq_sim.
         etrans. eapply heqp'. symmetry.
         eapply heqp''. eassumption. eassumption.
         symmetry.
         etrans. eapply strip_eq_sim.
         etrans. symmetry. eapply heq''. symmetry.
         eapply heqq''. eassumption. eassumption.
         symmetry. etrans. apply heqpr. etrans. apply heqpqt'. now symmetry.
      ++ multiset_solver.
    + eapply lts_mb_nb_with_nb_spec1 in hright as (nb' & hright).
      exists (p2, mp ∖ {[+ a +]}). split.
      ++ eapply gmultiset_disj_union_difference' in hright.
         rewrite hright at 1. 
         
         eapply ParSync; eauto. (*nécessaire ?*) unfold fw_inter.  
         split; eauto.
         eapply lts_multiset_minus; eauto.
         
      ++ destruct hlq2 as (q''' & hlq2 & heqq'').
         assert (heqm2 : lts_oba_mo q2 = {[+ a +]} ⊎ lts_oba_mo q').
         replace (lts_oba_mo q') with (lts_oba_mo q''').
         now eapply lts_oba_mo_spec2.
         eapply lts_oba_mo_eq. etrans. eapply heqq''. now symmetry.
         intros pt qt hwpt hwqt. simpl in *.
         assert (heq' : q''' ⋍ q') by (etrans; eassumption).
         edestruct (strip_eq_sim_ex hwqt _ heq') as (qt' & hwqt' & heqqt').
         edestruct heqp2 as (heqpqt' & heqmpt'); eauto; simpl in *.
         rewrite heqm2. eapply strip_step; eassumption.
         split.
         symmetry. etrans. symmetry. eapply heqqt'. now symmetry.
         eapply (gmultiset_disj_union_inj_1 {[+ a +]}).
         replace ({[+ a +]} ⊎ (lts_oba_mo q' ⊎ (mb_without_not_nb mq))) with
           ({[+ a +]} ⊎ lts_oba_mo q' ⊎ (mb_without_not_nb mq)) by multiset_solver.
         rewrite <- heqm2.
         rewrite <- heqmpt'.
         rewrite gmultiset_disj_union_assoc.
         replace ({[+ a +]} ⊎ lts_oba_mo p2) with (lts_oba_mo p2 ⊎ {[+ a +]}) 
         by multiset_solver.
         rewrite <- gmultiset_disj_union_assoc.
         eapply gmultiset_eq_pop_l.
         apply lts_mb_nb_with_nb_spec2 in hright; eauto.
         assert (mb_without_not_nb (mp ∖ {[+ a +]}) = (mb_without_not_nb mp) ∖ {[+ a +]}) as eq.
         eapply lts_mb_nb_with_nb_diff; eauto.
         eapply lts_mb_nb_with_nb_spec1 in hright as (nb'' & mem'').
         eauto.
         rewrite eq. multiset_solver.
  - edestruct (eq_spec p0 qt τ) as (pt & hlpt & heqpt); eauto.
    edestruct (strip_retract_act hwp hlpt )
      as (p' & p1 & wp' & hwp' & heqpr0).
    exists (p', mp). split.

    eapply ParLeft. (*nécessaire ?*)  eauto with mdb.

    intros pr qr hwpr hwqr. simpl in *.
    assert (heqr1 : lts_oba_mo p' = lts_oba_mo p ⊎ lts_oba_mo p1).
    eapply strip_after; eauto.
    assert (heqr2 : lts_oba_mo q' = lts_oba_mo q ⊎ lts_oba_mo q1).
    eapply strip_after; eauto.
    assert (heqr3 : lts_oba_mo p1 = lts_oba_mo q1).
    eapply lts_oba_mo_eq.
    transitivity pt. now symmetry. transitivity qt; eauto. now symmetry.
    split.
    + rewrite heqr1 in hwpr. rewrite heqr2 in hwqr.
      eapply strip_aux1 in hwpr as (pt' & hwp1' & heqpt'); eauto.
      eapply strip_aux1 in hwqr as (qt' & hwq1' & heqqt'); eauto.
      transitivity pt'. now symmetry. transitivity qt'.
      assert (heqr0 : p1 ⋍ q1).
      transitivity pt. now symmetry.
      transitivity qt; eauto. now symmetry.
      eapply (strip_eq_sim heqr0); eauto.
      now rewrite heqr3. assumption.
    + multiset_solver.
Qed.

Lemma lts_fw_eq_spec_left_output `{
  M : @LtsObaFB P A H LtsP LtsEqP V}  
  `{@Prop_of_Inter P (mb A) A fw_inter H LtsP MbLts}
  p q q' mp mq η :
  p ▷ mp ≐ q ▷ mq -> non_blocking η -> q ⟶[η] q' -> p ▷ mp ⟶≐[η] q' ▷ mq.
Proof.
  intros heq nb l.
  edestruct (lts_oba_mo_strip p) as (p0 & hwp).
  edestruct (lts_oba_mo_strip q) as (q0 & hwq).
  assert (η ∈ lts_oba_mo q) as h0. eapply lts_oba_mo_spec_bis1; eauto.
  edestruct (heq p0 q0) as (heq0 & heqm0); eauto. simpl in *.
  assert (h1 : η ∈ lts_oba_mo p ⊎ mb_without_not_nb mp) by multiset_solver.
  eapply gmultiset_elem_of_disj_union in h1 as [hleft|hright].
  ++ eapply gmultiset_disj_union_difference' in hleft as heqmop.
     eapply lts_oba_mo_spec_bis2 in hleft as (p' & nb1 & hl').
     rewrite heqmop in hwp.
     eapply strip_eq_step in hwp as (p0' & hwop0' & heqp0'); eauto.
     assert (η ∈ lts_oba_mo q) as h2. eapply (lts_oba_mo_spec_bis1 _ _ _ nb l).
     eapply gmultiset_disj_union_difference' in h2 as heqmoq.
     rewrite heqmoq in hwq.
     eapply strip_eq_step in hwq as (q0' & hwoq0' & heqq0'); eauto.
     exists (p', mp). 
     
     split. eapply ParLeft. eauto with mdb.
     
     intros pt qt hwopt hwoqt. simpl in *.
     eapply lts_oba_mo_spec2 in hl', l; eauto.
     assert (heq1 : lts_oba_mo q' = lts_oba_mo q ∖ {[+ η +]})
       by multiset_solver.
     assert (heq2 : lts_oba_mo p' = lts_oba_mo p ∖ {[+ η +]})
       by multiset_solver.
     rewrite heq1 in hwoqt. rewrite heq2 in hwopt.
     split.
     +++ transitivity p0'. eapply strip_m_deter; eauto.
         transitivity p0. assumption.
         transitivity q0. assumption.
         transitivity q0'. now symmetry.
         eapply strip_m_deter; eauto.
     +++ multiset_solver.
  ++ assert (η ∈ mp) as hright'. eapply lts_mb_nb_with_nb_spec1; eauto.
     eapply gmultiset_disj_union_difference' in hright'.
     rewrite hright'.
     eexists. split.
     
     eapply (ParRight (ActExt η) p ({[+ η +]} ⊎ mp ∖ {[+ η +]}) (mp ∖ {[+ η +]})).  
     eapply lts_multiset_minus. eauto with mdb.
     
     intros pt qt hwopt hwoqt. simpl in *.
     split.
     +++ edestruct (heq pt q0) as (heq1 & heqm1); eauto. simpl in *.
         transitivity q0. assumption.
         eapply gmultiset_disj_union_difference' in h0 as heqmoq.
         rewrite heqmoq in hwq.
         eapply strip_eq_step in hwq as (q0' & hwoq0' & heqq0'); eauto.
         transitivity q0'. now symmetry.
         eapply lts_oba_mo_spec2 in l; eauto.
         assert (heq2 : lts_oba_mo q' = lts_oba_mo q ∖ {[+ η +]})
           by multiset_solver.
         rewrite heq2 in hwoqt. eapply strip_m_deter; eauto.
     +++ eapply lts_oba_mo_spec2 in l; eauto.
         assert (η ∈ mb_without_not_nb mp). eauto.
         eapply lts_mb_nb_with_nb_spec1 in hright as (nb'' & mem'').
         rewrite lts_mb_nb_with_nb_diff;eauto. multiset_solver.
Qed.

Lemma lts_fw_eq_spec_left_input `{
   M : @LtsObaFB P A H LtsP LtsEqP V}
   `{@Prop_of_Inter P (mb A) A fw_inter H LtsP MbLts}
   p q q' mp mq μ :
   p ▷ mp ≐ q ▷ mq -> ¬ non_blocking μ -> q ⟶[μ] q' -> p ▷ mp ⟶≐[μ] q' ▷ mq.
Proof.
  intros not_nb heq l.
  edestruct (fw_eq_input_simulation not_nb heq l) as (p' & hl' & heq').
  exists (p' ▷ mp). 
  
  (*nécessaire?*) split.
  + eapply ParLeft. eauto with mdb.
  + eauto with mdb.
Qed.

Lemma lts_fw_eq_spec_left `{
  M : @LtsObaFB P A H LtsP LtsEqP LtsOBAP}
  `{@Prop_of_Inter P (mb A) A fw_inter H LtsP MbLts}
  p q q' α mp mq :
  p ▷ mp ≐ q ▷ mq -> q ⟶{α} q' -> p ▷ mp ⟶≐{α} q' ▷ mq.
Proof.
  intros heq l. destruct α as [μ | ].
  + destruct (decide (non_blocking μ)).
   ++ eapply lts_fw_eq_spec_left_output; eauto.
   ++ eapply lts_fw_eq_spec_left_input; eauto.
  + eapply lts_fw_eq_spec_left_tau; eauto.
Qed.

Lemma lts_fw_eq_spec_right_nb `{
  M : @LtsObaFB P A H LtsP LtsEqP LtsOBAP}
  `{@Prop_of_Inter P (mb A) A fw_inter H LtsP MbLts}
  p q mp mq η :
  non_blocking η -> p ▷ mp ≐ q ▷ {[+ η +]} ⊎ mq -> p ▷ mp ⟶≐[η] q ▷ mq.
Proof.
  intros nb heq.
  destruct (decide (η ∈ mp)) as [eq | not_eq].
  + assert (η ∈ mb_without_not_nb mp). eapply lts_mb_nb_with_nb_spec2;eauto.
    assert (η ∈ lts_oba_mo p ⊎ mb_without_not_nb mp) as eq'. multiset_solver.
    exists (p, mp ∖ {[+ η +]}). split.
    eapply gmultiset_disj_union_difference' in eq as eq''. rewrite eq'' at 1. 
    eapply ParRight. eapply lts_multiset_minus. eauto with mdb.
    
    intros p' q' hw1 hw2. simpl in *.
    edestruct (heq p' q') as (equiv & same_mb) ; eauto; simpl in *.
    split. eassumption.
    eapply gmultiset_disj_union_difference' in eq as eq''.
    eapply (gmultiset_disj_union_inj_1 {[+ η +]}).
    symmetry.
    transitivity (lts_oba_mo q ⊎ ({[+ η +]} ⊎ mb_without_not_nb mq)).
    multiset_solver. rewrite lts_mb_nb_with_nb_diff;eauto.
    unfold mb.
    erewrite<- lts_mb_nb_spec1;eauto. unfold mb in same_mb. rewrite<- same_mb.
    multiset_solver.
  + edestruct (lts_oba_mo_strip p) as (p' & hwp).
    assert (η ∈ lts_oba_mo p) as Hyp.
    edestruct (lts_oba_mo_strip q) as (q' & hwq).
    destruct (heq p' q' hwp hwq) as (heq' & heqmo). simpl in *.
    assert (η ∈ lts_oba_mo p ⊎ mb_without_not_nb mp) as Hyp'. rewrite heqmo.
    unfold mb.
    erewrite lts_mb_nb_spec1;eauto.  multiset_solver.
    eapply gmultiset_elem_of_disj_union in Hyp' as [hleft | hright].
    ++ multiset_solver.
    ++ eapply lts_mb_nb_with_nb_spec1 in hright as (nb' & mem'). multiset_solver.
    ++ eapply lts_oba_mo_spec_bis2 in Hyp as (p0 & nb1 & hl0).
    exists (p0, mp). split.
    
    (*nécessaire*) eapply ParLeft. eauto with mdb.
    
    intros p1 q1 hw1 hw2. simpl in *. split.
    edestruct (heq p' q1); eauto; simpl in *.
    set (heqmo := lts_oba_mo_spec2 _ _ _ nb1 hl0).
    rewrite heqmo in hwp.
    eapply strip_eq_step in hwp as (p4 & hwo4 & heq4); eauto.
    set (h := strip_m_deter hw1 hwo4).
    etrans. eassumption. etrans; eassumption.
    set (heqmo := lts_oba_mo_spec2 _ _ _ nb1 hl0).
    edestruct (heq p' q1) as (equiv & mb_equal); eauto; simpl in *.
    rewrite heqmo in mb_equal.
    assert (mb_without_not_nb ({[+ η +]} ⊎ mq) = {[+ η +]} ⊎ mb_without_not_nb mq) as eq.
    eapply lts_mb_nb_spec1; eauto. rewrite eq in mb_equal.
    replace (lts_oba_mo q ⊎ ({[+ η +]} ⊎ (mb_without_not_nb mq)))
      with ({[+ η +]} ⊎ lts_oba_mo q ⊎ mb_without_not_nb mq) in mb_equal.
    eapply (gmultiset_disj_union_inj_1 ({[+ η +]})). multiset_solver.
    rewrite <- gmultiset_disj_union_assoc.
    rewrite gmultiset_disj_union_comm.
    rewrite <- gmultiset_disj_union_assoc.
    eapply gmultiset_eq_pop_l.
    now rewrite gmultiset_disj_union_comm.
Qed.



Lemma lts_fw_eq_spec_right_not_nb `{
  M : @LtsObaFB P A H LtsP LtsEqP LtsOBAP}
  `{@Prop_of_Inter P (mb A) A fw_inter H LtsP MbLts}
   p q mp mq η μ:
  (* ¬  *) non_blocking η (* utile OU prouvable ?*) -> dual η μ -> p ▷ mp ≐ q ▷ mq 
  -> p ▷ mp ⟶≐[μ] q ▷ {[+ η +]} ⊎ mq.
Proof.
  intros nb duo heq.
  exists (p ▷ ({[+ η +]} ⊎ mp)). split.
  + eapply ParRight. eapply lts_multiset_add; eauto.
  + constructor; simpl in *. 
    - edestruct heq; simpl in *; eauto.
    - edestruct heq; simpl in *; eauto.
      unfold mb.
      rewrite (lts_mb_nb_spec1 η mp nb).
      rewrite (lts_mb_nb_spec1 η mq nb). multiset_solver.
Qed.


Lemma lts_fw_com_eq_spec `{
  M : @LtsObaFB P A H LtsP LtsEqP LtsOBAP}
  `{@Prop_of_Inter P (mb A) A fw_inter H LtsP MbLts}
  p q q' mp mq μ η:
  ¬ non_blocking μ (* utile OU prouvable ?*) -> dual η μ 
  -> non_blocking η (* à enlever si multiset de nb action *)
  -> p ▷ mp ≐ q ▷ {[+ η +]} ⊎ mq -> q ⟶[μ] q' 
  -> p ▷ mp ⟶≐ q' ▷ mq.
Proof.
  intros not_nb duo nb' heq hl.
  edestruct (fw_eq_input_simulation heq not_nb hl) as (p' & hl' & heq').
  edestruct (lts_oba_mo_strip p) as (p0 & hwp).
  edestruct (lts_oba_mo_strip q) as (q0 & hwq).
  edestruct (heq p0 q0) as (heqp0 & heqm); eauto. simpl in *.
  assert (mb_without_not_nb ({[+ η +]} ⊎ mq) = {[+ η +]} ⊎ mb_without_not_nb mq) as eq;eauto.
  eapply (lts_mb_nb_spec1 η mq nb'). rewrite eq in heqm.
  assert (mem : η ∈ lts_oba_mo p ⊎ (mb_without_not_nb mp)) 
    by (now rewrite heqm; multiset_solver).
  eapply gmultiset_elem_of_disj_union in mem as [hleft | hright].
  - eapply lts_oba_mo_spec_bis2 in hleft as (p1 & nb & hl1).
    assert (neq : μ ≠ η). eapply BlockingAction_are_not_non_blocking; eauto.
    edestruct (lts_oba_non_blocking_action_confluence nb neq hl1 hl') as (p2 & hlp1 & hlp').
    edestruct (lts_oba_fb_feedback nb duo hl1 hlp1) as (p3 & hlp & heqp3).
    exists (p3, mp). split.

    + (*nécessaire?*) eapply ParLeft. eauto with mdb.
    
    
    + intros ph qh hsph hsqh. simpl in *.
      destruct hlp' as (p2' & hlp2' & heqp2').
      destruct (lts_oba_mo_strip p') as (ph' & hsph').
      destruct (heq' ph' qh) as (heqt0 & heqmt); eauto. simpl in *.
      eapply lts_oba_mo_spec2 in hlp2' as hmeqp2'; eauto.
      assert (heqmu : lts_oba_mo p2' = lts_oba_mo p' ∖ {[+ η +]}) by multiset_solver.
      split.
      ++ eapply lts_oba_mo_spec_bis1 in hlp2' as hmem; eauto.
         eapply gmultiset_disj_union_difference' in hmem.
         rewrite hmem in hsph'.
         eapply strip_eq_step in hsph' as h1; eauto.
         destruct h1 as (p4 & hsu & heqp4).
         symmetry. transitivity ph'. now symmetry. transitivity p4. now symmetry.
         eapply (@strip_eq_sim _ _ _ _ _ _ p2' p3). transitivity p2. assumption. now symmetry.
         eassumption.
         replace (lts_oba_mo p' ∖ {[+ η +]}) with (lts_oba_mo p3). assumption.
         rewrite <- heqmu. eapply lts_oba_mo_eq. transitivity p2. assumption. now symmetry.
      ++ eapply (gmultiset_disj_union_inj_1 {[+ η +]}).
         replace (lts_oba_mo p3) with (lts_oba_mo p2'). rewrite heqmu.
         replace ({[+ η +]} ⊎ (lts_oba_mo q' ⊎ (mb_without_not_nb mq))) with (lts_oba_mo q' ⊎ ({[+ η +]} ⊎ (mb_without_not_nb mq))).
         rewrite <- heqmu. multiset_solver.
         rewrite 2 gmultiset_disj_union_assoc.
         replace (lts_oba_mo q' ⊎ {[+ η +]}) with ({[+ η +]} ⊎ lts_oba_mo q')
           by multiset_solver.
         reflexivity. eapply lts_oba_mo_eq.
         transitivity p2. assumption. now symmetry.
  - eapply lts_mb_nb_with_nb_spec1 in hright as (nb'' & hright);eauto.
    assert (mem : η ∈ mp); eauto.
    eapply gmultiset_disj_union_difference' in hright.
    exists (p' ▷ mp ∖ {[+ η +]}).
    split. rewrite hright at 1.
    (* assert (non_blocking η) as nb. admit. (* can be admitted *) *)
    
    eapply ParSync. split; eauto. eauto with mdb. eapply lts_multiset_minus; eauto.
    
    intros pt qt hw1 hw2. simpl in *.
    edestruct (heq' pt qt) as (heqt0 & heqmt); eauto.
    split; simpl in *; eauto.
    eapply (gmultiset_disj_union_inj_1 {[+ η +]}).
    symmetry.
    assert (mb_without_not_nb ({[+ η +]} ⊎ mq) = {[+ η +]} ⊎ mb_without_not_nb mq) as eq'. 
    eapply lts_mb_nb_spec1;eauto. rewrite eq' in heqmt.
    transitivity (({[+ η +]} ⊎ lts_oba_mo q') ⊎ mb_without_not_nb mq). multiset_solver.
    transitivity ((lts_oba_mo q' ⊎ {[+ η +]}) ⊎ mb_without_not_nb mq). multiset_solver.
    transitivity (lts_oba_mo p' ⊎ mb_without_not_nb mp).
    by now rewrite <- gmultiset_disj_union_assoc.
    symmetry.
    transitivity (lts_oba_mo p' ⊎ {[+ η +]} ⊎  (mb_without_not_nb mp) ∖ {[+ η +]}).
    assert (mb_without_not_nb (mp ∖ {[+ η +]}) = (mb_without_not_nb mp) ∖ {[+ η +]}) as eq''.
    eapply lts_mb_nb_with_nb_diff; eauto.
    rewrite eq''.
    multiset_solver.
    rewrite <- gmultiset_disj_union_assoc.
    f_equal. assert (η ∈ mb_without_not_nb mp). eapply lts_mb_nb_with_nb_spec2; eauto.
    multiset_solver.
Qed.


Lemma lts_fw_eq_spec  `{
  M : @LtsObaFB P A H LtsP LtsEqP LtsOBAP}
  `{@Prop_of_Inter P (mb A) A fw_inter H LtsP MbLts}
  (p : P) (q : P) (t : P) (mp : mb A) (mq : mb A) (mt : mb A) (α : Act A) :
  (p ▷ mp) ≐ (t ▷ mt) -> (t ▷ mt) ⟶{α} (q ▷ mq) -> p ▷ mp ⟶≐{α} q ▷ mq.
Proof.
  intros heq hl. inversion hl as [ | ? ? ? ? Hstep | ] ; subst.
  - eapply lts_fw_eq_spec_left; eauto.
  - destruct α. 
    + destruct (decide (non_blocking μ)) as [nb | not_nb]. 
      ++ eapply (non_blocking_action_in_ms mt μ mq) in nb as equal_mb; eauto.
         eapply lts_fw_eq_spec_right_nb; eauto. rewrite equal_mb. eauto. 
      ++ assert (¬ non_blocking μ) as not_nb'. assumption.
         eapply (blocking_action_in_ms mt μ mq) in not_nb' as (equal_mb & duo & nb); eauto.
         rewrite <-equal_mb.
         eapply lts_fw_eq_spec_right_not_nb; eauto.
    + inversion Hstep.
  - destruct eq as (duo & nb).
    assert ({[+ μ2 +]} ⊎ mq = mt) as equal_mb.
    apply non_blocking_action_in_ms; eauto.
    eapply lts_fw_com_eq_spec; eauto. eapply lts_oba_fw_non_blocking_duo_spec; eauto.
    rewrite equal_mb. eauto.
Qed.


#[global] Program Instance MbLtsEq 
  `{M : @LtsObaFB P A H LtsP LtsEqP LtsOBAP}  
  `{@Prop_of_Inter P (mb A) A fw_inter H LtsP MbLts}
  : LtsEq (P * mb A) A :=
  {| eq_rel := fw_eq |}.
Next Obligation. intros. split.
  + eapply fw_eq_refl.
  + eapply fw_eq_symm.
  + eapply fw_eq_trans.
Qed.
Next Obligation.
  intros ? ? ? ? ? ? ? ? (p, mp) (q, mq) α ((t, mt) & heq & hl).
  eapply lts_fw_eq_spec; eauto.
Qed.



#[global] Program Instance LtsMBOba 
  `{M : @LtsObaFB P A H LtsP LtsEqP LtsOBAP}  
  `{@Prop_of_Inter P (mb A) A fw_inter H LtsP MbLts}
  : LtsOba (P * mb A) A :=
  {| lts_oba_mo p := lts_oba_mo p.1 ⊎ mb_without_not_nb p.2 |}.
Next Obligation.
  intros ? ? ? ? ? ? ? ? p1 η p2 nb Hstep; simpl in *.
  inversion Hstep; subst; simpl in *.
  + apply (lts_oba_mo_spec_bis1 a1 η a2) in nb; eauto. set_solver.
  + apply (non_blocking_action_in_ms b1 η b2) in nb as eq ; subst;  eauto. 
    assert (η ∈ mb_without_not_nb ({[+ η +]} ⊎ b2)).
    eapply lts_mb_nb_with_nb_spec2; eauto; try multiset_solver.
    set_solver.
Qed.
Next Obligation.
  intros ? ? ? ? ? ? ? ? (p , mem) η mem_non_blocking; simpl in *.
  rewrite gmultiset_elem_of_disj_union in mem_non_blocking. 
  destruct (decide (η ∈ lts_oba_mo p)) as [non_blocking_in_p | non_blocking_not_in_p].
  + eapply lts_oba_mo_spec_bis2 in non_blocking_in_p as (p' & nb & Hstep).
    exists (p', mem). split.
    ++ exact nb.
    ++ eauto with mdb.
  + destruct (decide (η ∈ mb_without_not_nb mem)) as [non_blocking_in_mem | non_blocking_not_in_mem].
    eapply lts_mb_nb_with_nb_spec1 in non_blocking_in_mem as (nb & mem').
    * exists (p , mem ∖ {[+ η +]}). split.
      ++ exact nb.
      ++ eapply ParRight. assert (mem = {[+ η +]} ⊎ mem ∖ {[+ η +]}) as eq. multiset_solver.
         rewrite eq at 1. eapply lts_multiset_minus. exact nb. 
    * exfalso. destruct mem_non_blocking; contradiction.
Qed.
Next Obligation.
  intros ? ? ? ? ? ? ? ? ? ? ? nb Hstep ; simpl in *.
  inversion Hstep; subst; simpl in *.
  - apply (lts_oba_mo_spec2 a1 η a2) in nb; eauto. multiset_solver.
  - apply (non_blocking_action_in_ms b1 η b2) in nb as eq; eauto; subst.
    rewrite gmultiset_disj_union_assoc. 
    assert ({[+ η +]} ⊎ lts_oba_mo a ⊎ mb_without_not_nb b2 = 
    lts_oba_mo a ⊎ ({[+ η +]} ⊎ mb_without_not_nb b2)) as eq. multiset_solver.
    rewrite eq.
    erewrite gmultiset_eq_pop_l; eauto.
    eapply lts_mb_nb_spec1;eauto.
Qed.
Next Obligation.
intros ? ? ? ? ? ? ? ? ? ? ? ? ? nb Hstep_nb Hstep. destruct p as (p, mp), q as (q, mq), r as (r, mr).
  inversion Hstep_nb (* as [a b c d e f| a b c d e f| a b c d e f] *) ; inversion Hstep; subst.
  - destruct (lts_oba_non_blocking_action_delay nb l l0) as (t & hlt0 & (r0 & hlr0 & heqr0)).
    exists (t, mr). split; simpl in *. eauto with mdb.
    exists (r0, mr). split. simpl in *. eauto with mdb.
    now eapply fw_eq_id_mb.
  - exists (p, mr). split; simpl in *. eauto with mdb.
    exists (r, mr). split. simpl in *. eauto with mdb. reflexivity.
  - destruct (lts_oba_non_blocking_action_delay nb l l1) as (t & hlt0 & (r0 & hlr0 & heqr0)).
    exists (t, mr). split. simpl in *. eauto with mdb.
    exists (r0, mr). split. simpl in *. eauto with mdb.
    now eapply fw_eq_id_mb.
  - apply (non_blocking_action_in_ms mp η mr) in nb as eq; subst; eauto.
    exists (r, {[+ η +]} ⊎ mr).
    split. simpl in *. eauto with mdb.
    exists (r, mr). split. simpl in *. eauto with mdb. reflexivity.
  - destruct α as [μ |]. 
    + apply (non_blocking_action_in_ms mp η mq) in nb as eq; subst; eauto.
      destruct ((decide (non_blocking μ))) as [nb' | not_nb'].
      ++ apply (non_blocking_action_in_ms mq μ mr) in nb' as eq; subst; eauto.
         replace ({[+ η +]} ⊎ ({[+ μ +]} ⊎ mr))
         with ({[+ μ +]} ⊎ ({[+ η +]} ⊎ mr)) by multiset_solver.
         exists (r, {[+ η +]} ⊎ mr). split.
         * eapply ParRight. eapply lts_multiset_minus. exact nb'.
         * exists (r, mr). split. eapply ParRight. eapply lts_multiset_minus. exact nb. reflexivity.
      ++ apply (blocking_action_in_ms mq μ mr) in not_nb' as (eq & duo & nb'); subst; eauto.
         exists (r, {[+ co μ +]} ⊎ ({[+ η +]} ⊎ mq)).
         split.
         * eapply ParRight. eapply lts_multiset_add; eauto.
         * replace ({[+ co μ +]} ⊎ ({[+ η +]} ⊎ mq))
           with ({[+ η +]} ⊎ ({[+ co μ +]} ⊎ mq)) by multiset_solver.
           exists (r ▷ {[+ co μ +]} ⊎ mq). split. eapply ParRight. eapply lts_multiset_minus. exact nb. reflexivity.
    + inversion l0.
  - destruct eq as (duo & nb').
    apply (non_blocking_action_in_ms mp η mq) in nb as eq_mem; subst; eauto.
    apply (non_blocking_action_in_ms mq μ2 mr) in nb' as eq_mem; subst; eauto.
    replace ({[+ η +]} ⊎ ({[+ μ2 +]} ⊎ mr))
    with ({[+ μ2 +]} ⊎ ({[+ η +]} ⊎ mr)) by multiset_solver.
    exists (r, ({[+ η +]} ⊎ mr)). split. eapply (ParSync μ1 μ2); eauto.
    + split; eauto.
    + apply lts_multiset_minus. exact nb'.
    + exists (r ▷ mr). split. eapply ParRight. apply lts_multiset_minus; exact nb. reflexivity.
Qed.
Next Obligation.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? nb not_eq Hstep_nb Hstep. 
  destruct p as (p, mp), q1 as (q, mq), q2 as (r, mr).
  inversion Hstep_nb; subst.
  - inversion Hstep; subst.
    + edestruct (lts_oba_non_blocking_action_confluence nb not_eq l l0) as (t & hlt0 & (r0 & hlr0 & heqr0)).
      exists (t, mr). split; simpl in *. eauto with mdb.
      exists (r0, mr). split. simpl in *. eauto with mdb.
      now eapply fw_eq_id_mb.
    + exists (q, mr). split. simpl in *. eauto with mdb.
      exists (q, mr). split. simpl in *. eauto with mdb. reflexivity.
  - inversion Hstep; subst.
    + exists (r, mq). split; simpl in *. eauto with mdb.
      exists (r, mq). split. simpl in *. eauto with mdb. reflexivity.
    + eapply (non_blocking_action_in_ms mp η mq) in nb as eq; eauto ; subst.
      destruct (decide (non_blocking μ)) as [nb' | not_nb'].
      * eapply (non_blocking_action_in_ms ({[+ η +]} ⊎ mq) μ mr) in nb' as eq; eauto ; subst.
        assert (neq : η ≠ μ) by naive_solver.
        assert (μ ∈ mq) as mem. multiset_solver.
        assert (μ ∈ {[+ η +]} ⊎ mq) as mem'. multiset_solver.
        eapply gmultiset_disj_union_difference' in mem. rewrite mem.
        exists (r, mq ∖ {[+ μ +]}). split.
        ++ eapply ParRight. eapply lts_multiset_minus; eauto.
        ++ assert (η ∈ mr) as mem''. multiset_solver. 
           assert (mr = {[+ η +]} ⊎ (mq ∖ {[+ μ +]})) as mem'''. multiset_solver.
           rewrite mem'''. exists (r ▷ mq ∖ {[+ μ +]}). split. 
           eapply ParRight. eapply lts_multiset_minus; eauto. reflexivity.
      * eapply (blocking_action_in_ms ({[+ η +]} ⊎ mq) μ mr) in not_nb' as (eq & duo & nb'); eauto ; subst.
        exists (r ▷ {[+ co μ +]} ⊎ mq). split.
        ++ eapply ParRight. eapply lts_multiset_add; eauto.
        ++ assert ({[+ co μ +]} ⊎ ({[+ η +]} ⊎ mq) = {[+ η +]} ⊎ ({[+ co μ +]} ⊎ mq)) as eq. multiset_solver.
           rewrite eq. exists (r ▷ {[+ co μ +]} ⊎ mq). split. 
           eapply ParRight. eapply lts_multiset_minus; eauto. reflexivity.
Qed.
Next Obligation.
Proof.
  intros ? ? ? ? ? ? ? ? (p1, m1) (p2, m2) (p3, m3) η nb Hstep_nb Hstep.
  inversion Hstep_nb ;subst.
  - inversion Hstep ; subst.
    + edestruct (lts_oba_non_blocking_action_tau nb l l0) as
        [(t & hl1 & (t0 & hl0 & heq0)) | (μ & duo & t0 & hl0 & heq0)].
      left. exists (t, m3).
      split. simpl. eauto with mdb.
      exists (t0, m3). split. simpl. eauto with mdb.
      now eapply fw_eq_id_mb.
      right. exists μ. split.  exact duo. exists (t0, m3). split. simpl. eauto with mdb.
      now eapply fw_eq_id_mb.
    + inversion l0.
    + destruct eq as (duo' & nb').
      assert (¬ non_blocking μ1). eapply lts_oba_fw_non_blocking_duo_spec; eauto.
      assert (neq : μ1 ≠ η). intro. subst. contradiction. 
      edestruct (lts_oba_non_blocking_action_confluence nb neq l l1)
        as (t & hl1 & (t1 & hl2 & heq1)).
      left. exists (t, m3). split. eapply ParSync; eauto. split; eauto.
      exists (t1, m3). split. simpl. eauto with mdb.
      now eapply fw_eq_id_mb.
  - eapply (non_blocking_action_in_ms m1 η m2) in nb as eq; subst; eauto. 
    inversion Hstep ; subst.
    + left. exists (p3, m2).
      split. simpl. eauto with mdb.
      exists (p3, m2). split. eapply ParRight; eassumption. reflexivity.
    + inversion l0.
    + destruct eq as (duo & nb').
      eapply (non_blocking_action_in_ms ({[+ η +]} ⊎ m2) μ2 m3) in nb' as eq'; subst; eauto. 
      destruct (decide (μ2 = η)) as [eq | not_eq]; subst.
      ++ right. assert (m2 = m3) as eq_mem. multiset_solver. rewrite <-eq_mem in l2.  
         exists μ1. split; eauto. exists (p3, m2). split. simpl. eauto with mdb. rewrite eq_mem. reflexivity.
      ++ left. eapply (non_blocking_action_in_ms ({[+ η +]} ⊎ m2) μ2 m3) in nb' as eq; subst; eauto.
         assert (η ∈ m3). multiset_solver.
         assert (η ∈ {[+ μ2 +]} ⊎ m3). multiset_solver.
         assert (μ2 ∈ m2). multiset_solver.
         assert (μ2 ∈ {[+ η +]} ⊎ m2). multiset_solver.
         exists (p3, m2 ∖ {[+ μ2 +]}). split. eapply (ParSync μ1 μ2); eauto.
         split; eauto. assert (m2 = {[+ μ2 +]} ⊎ (m2 ∖ {[+ μ2 +]})) as eq_mem. multiset_solver.
         rewrite eq_mem at 1. eapply lts_multiset_minus; eauto.
         assert (m3 = ({[+ η +]} ⊎ (m2 ∖ {[+ μ2 +]}))) as eq_mem'. multiset_solver.
         rewrite eq_mem'. exists (p3 ▷ m2 ∖ {[+ μ2 +]}). split.
         eapply ParRight. eapply lts_multiset_minus; eauto. reflexivity.
Qed.
Next Obligation.
  intros ? ? ? ? ? ? ? ? (p1, m1) (p2, m2) (p3, m3) η nb Hstep_nb Hstep_nb'.
  intros p2' p3' hwp2 hwp3; simpl in *.
  inversion Hstep_nb ; subst.
  - inversion Hstep_nb' ; subst.
    + eapply fw_eq_id_mb; eauto.
      eapply lts_oba_non_blocking_action_deter; eauto.
    + eapply (non_blocking_action_in_ms m2 η m3) in nb as eq; subst; eauto.
      set (he1 := lts_oba_mo_spec2 _ _ _ nb l).
      rewrite he1 in hwp3.
      eapply strip_eq_step in hwp3 as (p0 & hw0 & heq0); eauto. split.
      etrans. eapply strip_m_deter; eauto. eassumption.
      assert (mb_without_not_nb ({[+ η +]} ⊎ m3) = {[+ η +]} ⊎ mb_without_not_nb m3) as eq.
      eapply lts_mb_nb_spec1;eauto. rewrite eq.
      rewrite he1.
      rewrite gmultiset_disj_union_comm at 1.
      rewrite <- 2 gmultiset_disj_union_assoc.
      eapply gmultiset_eq_pop_l. multiset_solver.
  - inversion Hstep_nb' ; subst.
    + eapply (non_blocking_action_in_ms m3 η m2) in nb as eq; subst; eauto.
      set (he1 := lts_oba_mo_spec2 _ _ _ nb l0).
      rewrite he1 in hwp2.
      eapply strip_eq_step in hwp2 as (p0 & hw0 & heq0); eauto. split.
      etrans. symmetry. eassumption.
      eapply strip_m_deter; eauto.
      assert (mb_without_not_nb ({[+ η +]} ⊎ m2) = {[+ η +]} ⊎ mb_without_not_nb m2) as eq.
      eapply lts_mb_nb_spec1;eauto. rewrite eq.
      symmetry. rewrite he1.
      rewrite gmultiset_disj_union_comm at 1.
      rewrite <- 2 gmultiset_disj_union_assoc.
      eapply gmultiset_eq_pop_l. multiset_solver.
    + eapply (non_blocking_action_in_ms m1 η m2) in nb as eq; subst; eauto.
      eapply (non_blocking_action_in_ms ({[+ η +]} ⊎ m2) η m3) in nb as eq; subst; eauto.
      assert (m3 = m2) by multiset_solver; subst.
      split.  eapply strip_m_deter; eauto. multiset_solver.
Qed.
Next Obligation.
  intros ? ? ? ? ? ? ? ? (p1, mp1) (p2, mp2) (q1, mq1) (q2, mq2) η nb Hstep_nb Hstep_nb' equiv.
  inversion Hstep_nb; subst;  intros p1' p2' hwp1 hwp2; simpl in *.
  - eapply lts_oba_mo_spec2 in l as hd1; eauto.
    edestruct (lts_oba_mo_strip q1) as (q1' & hwq1).
    inversion Hstep_nb'; subst.
    + edestruct (lts_oba_mo_strip q2) as (q2' & hwq2).
      edestruct (equiv q1' q2'); eauto; simpl in *.
      eapply lts_oba_mo_spec2 in l0 as hd2; eauto.
      split.
      ++ rewrite hd1 in hwp1. rewrite hd2 in hwp2.
         eapply strip_eq_step in hwp1, hwp2; eauto.
         destruct hwp1 as (t1 & hwq1' & heq1').
         destruct hwp2 as (t2 & hwq2' & heq2').
         set (heq1 := strip_m_deter hwq1 hwq1').
         set (heq2 := strip_m_deter hwq2 hwq2').
         transitivity t1. now symmetry.
         transitivity q1'. now symmetry.
         transitivity q2'. now symmetry.
         transitivity t2. now symmetry. eassumption.
      ++ multiset_solver.
    + edestruct (equiv q1' p2'); eauto; simpl in *.
      split.
      ++ rewrite hd1 in hwp1.
         eapply strip_eq_step in hwp1; eauto.
         destruct hwp1 as (t1 & hwq1' & heq1').
         set (heq1 := strip_m_deter hwq1 hwq1').
         transitivity t1. naive_solver.
         transitivity q1'; naive_solver.
      ++ rewrite hd1. symmetry.
         rewrite gmultiset_disj_union_comm at 1.
         eapply (non_blocking_action_in_ms mp2 η mq2) in nb as eq; eauto ; subst.
         assert (mb_without_not_nb ({[+ η +]} ⊎ mq2) = {[+ η +]} ⊎ mb_without_not_nb mq2) as eq.
         eapply lts_mb_nb_spec1;eauto. rewrite eq.
         rewrite <- 2 gmultiset_disj_union_assoc.
         eapply gmultiset_eq_pop_l. multiset_solver.
  - inversion Hstep_nb'; subst.
    + eapply lts_oba_mo_spec2 in l0 as hd1; eauto.
      edestruct (lts_oba_mo_strip q2) as (q2' & hwq2).
      edestruct (equiv p1' q2'); eauto; simpl in *.
      split.
      ++ rewrite hd1 in hwp2.
         eapply strip_eq_step in hwp2; eauto.
         destruct hwp2 as (t2 & hwq2' & heq2').
         set (heq1 := strip_m_deter hwq2 hwq2').
         transitivity q2'. naive_solver.
         transitivity t2; naive_solver.
      ++ rewrite hd1.
         rewrite gmultiset_disj_union_comm at 1.
         eapply (non_blocking_action_in_ms mp1 η mq1) in nb as eq; eauto; subst.
         assert (mb_without_not_nb ({[+ η +]} ⊎ mq1) = {[+ η +]} ⊎ mb_without_not_nb mq1) as eq.
         eapply lts_mb_nb_spec1;eauto. rewrite eq.
         rewrite <- 2 gmultiset_disj_union_assoc.
         eapply gmultiset_eq_pop_l. multiset_solver.
    + eapply (non_blocking_action_in_ms mp1 η mq1) in nb as eq; subst; eauto.
      assert (mb_without_not_nb ({[+ η +]} ⊎ mq1) = {[+ η +]} ⊎ mb_without_not_nb mq1) as eq.
      eapply lts_mb_nb_spec1;eauto. rewrite eq.
      edestruct (equiv p1' p2'); eauto; simpl in *.
      eapply (non_blocking_action_in_ms mp2 η mq2) in nb as eq'; subst; eauto.
      split. assumption.
      assert (mb_without_not_nb ({[+ η +]} ⊎ mq2) = {[+ η +]} ⊎ mb_without_not_nb mq2) as eq''.
      eapply lts_mb_nb_spec1;eauto. rewrite eq''.
      multiset_solver.
Qed.

#[global] Program Instance LtsMBObaFW 
  `{M : @LtsObaFB P A H LtsP LtsEqP LtsOBAP}
  `{@Prop_of_Inter P (mb A) A fw_inter H LtsP MbLts}
  : LtsObaFW (P * mb A) A.
Next Obligation.
  intros ? ? ? ? ? ? ? ? (p, m) η μ.
  exists (p, {[+ η +]} ⊎ m). split; eauto with mdb.
  eapply ParRight. eapply lts_multiset_add; eauto.
  eapply ParRight. eapply lts_multiset_minus; eauto.
Qed.
Next Obligation.
  intros ? ? ? ? ? ? ? ? (p1, m1) (p2, m2) (p3, m3) η μ nb duo Hstep_nb Hstep.
  inversion Hstep_nb; subst.
  + inversion Hstep; subst.
    ++ left. destruct (lts_oba_fb_feedback nb duo l l0) as (t & l1 & heq).
       exists (t, m3). split. eapply ParLeft; assumption.
       now eapply fw_eq_id_mb.
    ++ right. simpl. unfold fw_eq.
       intros p' q' strip_p strip_q. simpl in *.
       assert ( ¬ non_blocking μ) as not_nb. eapply lts_oba_fw_non_blocking_duo_spec; eauto.
       eapply (blocking_action_in_ms m2 μ m3) in not_nb as (eq & duo' & nb'); subst.
       set (heq := lts_oba_mo_spec2 _ _ _ nb l).
       rewrite heq in strip_p. rewrite heq. split.
       +++ destruct (strip_mem_ex strip_p) as (e & l' & nb'').
           destruct (strip_eq_step strip_p e l') as (t & hwo & heq'); eauto.
           set (h := lts_oba_non_blocking_action_deter nb'' l l').
           etrans. symmetry. eassumption.
           symmetry. eapply strip_eq_sim; eassumption.
       +++ assert (mb_without_not_nb ({[+ co μ +]} ⊎ m2) 
              = {[+ co μ +]} ⊎ mb_without_not_nb m2) as eq''.
           eapply lts_mb_nb_spec1;eauto. rewrite eq''.
           rewrite <- gmultiset_disj_union_assoc.
           rewrite gmultiset_disj_union_comm.
           rewrite <- gmultiset_disj_union_assoc.
           eapply gmultiset_eq_pop_l.
           assert (η = co μ) as eq_nb. eapply unique_nb; eauto; subst. subst.
           now rewrite gmultiset_disj_union_comm.
       +++ assumption.
  + inversion Hstep; subst.
    ++ left. exists (p3, m3). split. eapply ParSync; eauto. split; eauto. reflexivity.
    ++ right. 
       eapply (non_blocking_action_in_ms m1 η m2) in nb as eq; subst; eauto.
       assert (¬ non_blocking μ) as not_nb. eapply lts_oba_fw_non_blocking_duo_spec; eauto.
       eapply (blocking_action_in_ms m2 μ m3) in not_nb as (eq & duo' & nb'); subst; eauto.
       assert (η = co μ) as eq_nb. eapply unique_nb; eauto. subst.
       reflexivity.
Qed.

(** Derivatives. *)
(* η *) (* ¬ non_blocking μ *)

(* Definition co_set `{ExtAction A} (μ : A) := {η | non_blocking η /\ dual η μ /\ ¬ non_blocking μ}.
Definition co `{ExtAction A} (μ : A) := 
              if decide ({η | non_blocking η  /\dual η μ /\ ¬ non_blocking μ})
              then μ
              else μ. *)
              
(* Definition lts_fw_input_set `{FiniteLts A L} p (m : mb L) a :=
  (p, {[+ a +]} ⊎ m) :: map (fun p => (proj1_sig p, m)) (enum $ dsig (lts_step p (ActExt $ ActIn a))).*)
(* Parameter A : Type.
Parameter μ : A. 
Check (proj1_sig (co μ)). *)
Definition lts_fw_not_non_blocking_action_set `{FiniteImageLts P A} 
  (p : P) (m : mb A) μ :=
  if (decide (dual (co μ) μ /\ non_blocking (co μ))) 
  then (p, {[+ (co μ) +]} ⊎ m) :: map (fun p => (proj1_sig p, m)) (enum $ dsig (lts_step p (ActExt $ μ)))
  else map (fun p => (proj1_sig p, m)) (enum $ dsig (lts_step p (ActExt $ μ))).


Definition lts_fw_non_blocking_action_set `{FiniteImageLts P A} 
  (p : P) (m : mb A) η :=
  let ps := map (fun p => (proj1_sig p, m)) (enum $ dsig (lts_step p (ActExt $ η))) in
  if (decide (η ∈ m)) then (p, m ∖ {[+ η +]}) :: ps else ps.


Definition lts_fw_co_fin `{@FiniteImageLts P A H M}
  `{@Prop_of_Inter P (mb A) A fw_inter H M MbLts}
  (p : P) (η : A) (* : list (A * list P) *) :=
  map (fun μ => (η, map proj1_sig (enum $ dsig (lts_step p (ActExt $ μ))))) 
    (elements (lts_co_inter_action_left η p)).

Definition lts_fw_com_fin `{@FiniteImageLts P A H M}
  `{@Prop_of_Inter P (mb A) A fw_inter H M MbLts}
  (p : P) (m : list A) : list (A * list P) :=
  concat (map (fun η => (lts_fw_co_fin p η)) m). (* flat_map (fun η => (lts_fw_co_fin p η)) m. *)

Definition lts_fw_tau_set `{@FiniteImageLts P A H M} 
  `{@Prop_of_Inter P (mb A) A fw_inter H M MbLts}
  (p : P) (m : mb A) : list (P * mb A) :=
  let xs := map (fun p' => (proj1_sig p', m)) (enum $ dsig (fun q => p ⟶ q)) in
  let ys :=
    concat (map
              (fun '(a, ps) => map (fun p => (p, m ∖ {[+ a +]})) ps)
              (lts_fw_com_fin p (elements m) ))
    in xs ++ ys.



(* #[global] Program Instance inter_for_fw `{LtsP : @Lts P A H} `{@mb_without_not_nb A H} :
  @Prop_of_Inter P (mb A) A fw_inter H LtsP MbLts. *)


Lemma lts_fw_tau_set_spec1 
  `{LtsP : @Lts P A H}
  `{@FiniteImageLts P A H LtsP} 

  `{@Prop_of_Inter P (mb A) A fw_inter H LtsP MbLts}
  p1 m1 p2 m2 :
  (p1, m1) ⟶ (p2, m2) ->
  (p2, m2) ∈ lts_fw_tau_set p1 m1.
Proof.
  intros l.
  inversion l; subst.
  + eapply elem_of_app. left.
    eapply elem_of_list_fmap.
    exists (dexist p2 l0). split. reflexivity. eapply elem_of_enum.
  + inversion l0.
  + assert (inter : fw_inter μ1 μ2). eauto.
    destruct eq as (duo & nb).
    eapply elem_of_app. right.
    eapply elem_of_list_In.
    eapply in_concat.
    exists (map (fun p => (p, m2))
         (map proj1_sig (enum $ dsig (lts_step p1 (ActExt $ μ1))))
      ).
    split.
    eapply elem_of_list_In.
    eapply elem_of_list_fmap.
    exists (co μ1, map proj1_sig (enum $ dsig (lts_step p1 (ActExt $ μ1)))).
    eapply (non_blocking_action_in_ms m1 μ2 m2) in nb as eq; subst; eauto.
    assert (μ2 = co μ1) as eq. eapply unique_nb; eauto. subst.
    split.
    
    
    
    now replace (({[+ co μ1 +]} ⊎ m2) ∖ {[+ co μ1 +]}) with m2 by multiset_solver.
    

    (* assert (co μ1 ▷ map proj1_sig (enum (dsig (lts_step p1 (ActExt μ1)))) =
co μ1 ▷ map proj1_sig (enum (dsig (lts_step p1 (ActExt μ1))))
∧ co μ1 ∈ elements ({[+ co μ1 +]} ⊎ m2) 
    -> co μ1 ▷ map proj1_sig (enum (dsig (lts_step p1 (ActExt μ1))))
        ∈ concat (map (λ η : A, lts_fw_co_fin p1 η) (elements ({[+ co μ1 +]} ⊎ m2)))) as Hyp. *)
    (* Search (concat _).
    Search (map _). *)
    assert (elements ({[+ co μ1 +]} ⊎ m2) ≡ₚ 
    elements (gmultiset_singleton (co μ1)) ++ elements (m2)) as equiv.
    unfold singletonMS. eapply gmultiset_elements_disj_union.
    assert (map (λ η : A, lts_fw_co_fin p1 η) (elements ({[+ co μ1 +]} ⊎ m2)) ≡ₚ 
    map (λ η : A, lts_fw_co_fin p1 η) (elements ({[+ (co μ1)+]} : gmultiset A) ++ elements m2))
    as equiv2.
    eapply Permutation_map. eauto.
    erewrite gmultiset_elements_singleton in equiv2.
    simpl in equiv2. (*  intro. *) (* eapply in_concat. *)
    
    
    assert (eq : co μ1 ▷ map proj1_sig (enum (dsig (lts_step p1 (ActExt μ1)))) ∈ 
    lts_fw_co_fin p1 (co μ1)).
    (* unfold lts_fw_co_fin.
    assert (μ1 ∈ lts_co_inter_action_left (co μ1) p1).
    eapply lts_co_inter_action_spec_left ; eauto.
    edestruct (lts_essential_actions_spec_interact _ _ _ _ _ _ l1 l2 inter) 
      as [ess_act | not_ess_act].
    ++ admit.
    ++ eauto. *)
    admit. 
    (* Search (map _). *)
    
    
    unfold lts_fw_com_fin. 
    rewrite<- flat_map_concat_map.
    assert (eq' : flat_map (λ η : A, lts_fw_co_fin p1 η) (elements ({[+ co μ1 +]} ⊎ m2))
    ≡ₚ flat_map (λ η : A, lts_fw_co_fin p1 η) (elements ({[+ co μ1 +]} : gmultiset A) 
      ++ (elements m2))).
    eapply Permutation_flat_map. eauto.
    erewrite gmultiset_elements_singleton in eq'.
    simpl in *.
(*     assert (co μ1 ▷ map proj1_sig (enum (dsig (lts_step p1 (ActExt μ1)))) ∈ lts_fw_co_fin p1 (co μ1)).
    eauto.  *)
   (*  unfold elem_of. Search (_ ≡ₚ_ -> _). *)
    eapply elem_of_Permutation_proper; eauto. 
    eapply elem_of_list_In. (* eapply Permutation_in; eauto. *)
    eapply in_or_app. left. eapply elem_of_list_In in eq. eauto.
    (* set_solver.  *)(* eapply Permutation_in; eauto. 
    Permutation_flat_map   Permutation_in
map_app
    Search (concat _).
    erewrite gmultiset_elements_singleton in equiv2. *)
    (* admit. Check elem_of_Permutation_proper. *)
    (* assert ((∃ μ : A,
    co μ1 ▷ map proj1_sig (enum (dsig (lts_step p1 (ActExt μ1)))) =
    co μ ▷ map proj1_sig (enum (dsig (lts_step p1 (ActExt μ)))) 
    ∧ (co μ) ∈ elements ({[+ co μ1 +]} ⊎ m2)) 
    -> co μ1 ▷ map proj1_sig (enum (dsig (lts_step p1 (ActExt μ1))))
        ∈ concat (map (λ η : A, lts_fw_co_fin p1 η) (elements ({[+ co μ1 +]} ⊎ m2)))) as Hyp. *)

    (* eapply elem_of_list_fmap. *)

    (* eapply elem_of_list_fmap. *)
    (* exists μ1. *)

(*     eapply elem_of_Permutation_proper.
    eapply (gmultiset_elements_disj_union {[+ co μ1 +]} m2).
    rewrite gmultiset_elements_singleton. set_solver.
    
     *)
    eapply elem_of_list_In.
    eapply elem_of_list_fmap.
    eexists.  split. reflexivity.
    eapply elem_of_list_fmap.
    exists (dexist p2 l1). split. reflexivity. eapply elem_of_enum.
Admitted.

Lemma lts_fw_input_set_spec1 `{@FiniteImageLts P A H LtsP}
  `{@Prop_of_Inter P (mb A) A fw_inter H LtsP MbLts}
  p1 m1 p2 m2 μ :
  (p1, m1) ⟶[μ] (p2, m2) -> ¬ non_blocking μ -> 
  (p2, m2) ∈ lts_fw_not_non_blocking_action_set p1 m1 μ.
Proof.
  intros l not_nb.
  inversion l; subst.
  + unfold lts_fw_not_non_blocking_action_set.
    destruct (decide (dual (co μ) μ /\ non_blocking (co μ))) as [(duo & nb) | case2].
    - right. eapply elem_of_list_fmap.
      exists (dexist p2 l0). split. reflexivity. eapply elem_of_enum.
    - eapply elem_of_list_fmap.
      exists (dexist p2 l0). split. reflexivity. eapply elem_of_enum.
  + eapply (blocking_action_in_ms m1 μ m2) in not_nb as (eq & duo & nb); eauto; subst.
    unfold lts_fw_not_non_blocking_action_set.
    destruct (decide (dual (co μ) μ /\ non_blocking (co μ))) as [toto | impossible].
    ++ left.
    ++ assert (dual (co μ) μ ∧ non_blocking (co μ)); eauto. contradiction.
Qed. 


Lemma lts_fw_non_blocking_action_set_spec1 `{@FiniteImageLts P A H LtsP}
  `{@Prop_of_Inter P (mb A) A fw_inter H LtsP MbLts}
  p1 m1 p2 m2 η :
  (p1, m1) ⟶[η] (p2, m2) -> non_blocking η -> 
  (p2, m2) ∈ lts_fw_non_blocking_action_set p1 m1 η.
Proof.
  intros l nb.
  inversion l; subst.
  + unfold lts_fw_non_blocking_action_set.
    destruct (decide (η ∈ m2)) as [in_mem | not_in_mem].
    right. eapply elem_of_list_fmap. 
    exists (dexist p2 l0). split. reflexivity. eapply elem_of_enum. 
    eapply elem_of_list_fmap.
    exists (dexist p2 l0). split. reflexivity. eapply elem_of_enum. 
  + unfold lts_fw_non_blocking_action_set.
    eapply (non_blocking_action_in_ms m1 η m2) in nb as eq; subst ; eauto.
    destruct (decide (η ∈ {[+ η +]} ⊎ m2)).
    ++ replace (({[+ η +]} ⊎ m2) ∖ {[+ η +]}) with m2 by multiset_solver.
       left.
    ++ multiset_solver.
Qed.



#[global] Program Instance LtsMBFinite `{@FiniteImageLts P A H LtsP} 
  `{@Prop_of_Inter P (mb A) A fw_inter H LtsP MbLts}
  : FiniteImageLts (P * mb A) A.
Next Obligation. 
  intros ? ? ? ? ? ? (p, m) α.
  destruct α as [η | ].
  + destruct (decide (non_blocking η)) as [nb | not_nb].
    - eapply (in_list_finite (lts_fw_non_blocking_action_set p m η));
      intros (p0, m0) h%bool_decide_unpack.
      now eapply lts_fw_non_blocking_action_set_spec1.
    - rename η into μ. 
      eapply (in_list_finite (lts_fw_not_non_blocking_action_set p m μ)). simpl in *.
      intros (p0, m0) h%bool_decide_unpack.
      now eapply lts_fw_input_set_spec1. 
  + eapply (in_list_finite (lts_fw_tau_set p m)).
      intros (p0, m0) h%bool_decide_unpack.
      now eapply lts_fw_tau_set_spec1.
Qed.

Definition lts_tau_set_from_pset_spec1 `{Countable P, Lts P A}
  (ps : gset P) (qs : gset P) :=
  forall q, q ∈ qs -> exists p, p ∈ ps /\ p ⟶ q.

Definition lts_tau_set_from_pset_spec2 `{Countable P, Lts P A}
  (ps : gset P) (qs : gset P) :=
  forall p q, p ∈ ps -> p ⟶ q -> q ∈ qs.

Definition lts_tau_set_from_pset_spec `{Countable P, Lts P A}
  (ps : gset P) (qs : gset P) :=
  lts_tau_set_from_pset_spec1 ps qs /\ lts_tau_set_from_pset_spec2 ps qs.

Definition lts_tau_set_from_pset `{FiniteImageLts P A} (ps : gset P) : gset P :=
  ⋃ (map (fun p => list_to_set (lts_tau_set p)) (elements ps)).

Lemma lts_tau_set_from_pset_ispec `{Lts P A, !FiniteImageLts P A}
  (ps : gset P) :
  lts_tau_set_from_pset_spec ps (lts_tau_set_from_pset ps).
Proof.
  split.
  - intros a mem.
    eapply elem_of_union_list in mem as (xs & mem1 & mem2).
    eapply elem_of_list_fmap in mem1 as (p & heq0 & mem1).
    subst.  eapply elem_of_list_to_set in mem2.
    eapply lts_tau_set_spec in mem2. multiset_solver.
  - intros p q mem l.
    eapply elem_of_union_list.
    exists (list_to_set (lts_tau_set p)).
    split.
    + multiset_solver.
    + eapply lts_tau_set_spec in l. multiset_solver.
Qed.

Fixpoint wt_set_nil `{FiniteImageLts P A} (p : P) (t : terminate p) : gset P :=
  let '(tstep _ f) := t in
  let k q := wt_set_nil (`q) (f (`q) (proj2_dsig q)) in
  {[ p ]} ∪ ⋃ map k (enum $ dsig (lts_step p τ)).

Lemma wt_set_nil_spec1 `{FiniteImageLts P A} p q (tp : terminate p) :
  q ∈ wt_set_nil p tp -> p ⟹ q.
Proof.
  case tp. induction tp.
  intros t mem. simpl in mem.
  eapply elem_of_union in mem as [here | there].
  + eapply elem_of_singleton_1 in here. subst. eauto with mdb.
  + eapply elem_of_union_list in there as (ps & mem1 & mem2).
    eapply elem_of_list_fmap in mem1 as (r & mem1 & eq). subst.
    eapply wt_tau; [|destruct (t (`r) (proj2_dsig r)) eqn:eqn0].
    ++ eapply (proj2_dsig r).
    ++ eapply H3. eapply (proj2_dsig r). eassumption.
Qed.

Lemma wt_set_nil_spec2 `{FiniteImageLts P A} p q : 
    forall (tp : terminate p), p ⟹ q -> q ∈ wt_set_nil p tp.
Proof.
  intros. revert tp. dependent induction H2; intros tp; destruct tp.
  + set_solver.
  + eapply elem_of_union. right.
    eapply elem_of_union_list.
    set (qr := dexist q l).
    exists (wt_set_nil (`qr) (t0 (`qr) (proj2_dsig qr))).
    split. eapply elem_of_list_fmap.
    exists qr. split. reflexivity.
    eapply elem_of_enum. simpl.
    eapply IHwt. eauto.
Qed.

Lemma wt_nil_set_dec `{FiniteImageLts P A} p (ht : p ⤓) : forall q, Decision (p ⟹ q).
Proof.
  intro q.
  destruct (decide (q ∈ wt_set_nil p ht)).
  - left. eapply (wt_set_nil_spec1 _ _ _ e).
  - right. intro wt. eapply n. now eapply wt_set_nil_spec2.
Qed.

Lemma wt_set_nil_fin_aux `{FiniteImageLts P A}
  (p : P) (ht : terminate p) (d : ∀ q, Decision (p ⟹ q)) : 
      Finite (dsig (fun q => p ⟹ q)).
Proof.
  unfold dsig.
  eapply (in_list_finite (elements (wt_set_nil p ht))).
  intros q Htrans%bool_decide_unpack.
  now eapply elem_of_elements, wt_set_nil_spec2.
Qed.

Definition wt_set_nil_fin `{FiniteImageLts P A}
  (p : P) (ht : p ⤓) : Finite (dsig (fun q => p ⟹ q)) :=
  wt_set_nil_fin_aux p ht (wt_nil_set_dec p ht).

Lemma wt_push_nil_left_lts `{Lts P A} {p q r μ} : p ⟹ q -> q ⟶[μ] r -> p ⟹{μ} r.
Proof. by intros w1 lts; dependent induction w1; eauto with mdb. Qed.

Definition wt_set_mu
  `{FiniteImageLts P A} (p : P)
  (μ : A) (s : trace A) (hcnv : p ⇓ μ :: s) : gset P :=
  let ht := cnv_terminate p (μ :: s) hcnv in
  let ps0 := @enum (dsig (fun q => p ⟹ q)) _ (wt_set_nil_fin p ht) in
  let f p : list (dsig (lts_step p (ActExt μ))) := enum (dsig (lts_step p (ActExt μ))) in
  ⋃ map (fun t =>
           ⋃ map (fun r =>
                    let w := wt_push_nil_left_lts (proj2_dsig t) (proj2_dsig r) in
                    let hcnv := cnv_preserved_by_wt_act s p μ hcnv (`r) w in
                    let htr := cnv_terminate (`r) s hcnv in
                    let ts := @enum (dsig (fun q => (`r) ⟹ q)) _ (wt_set_nil_fin (`r) htr) in
                    list_to_set (map (fun t => (`t)) ts)
             ) (f (`t))
    ) ps0.

Lemma wt_set_mu_spec1 `{FiniteImageLts P A}
  (p q : P) (μ : A) (s : trace A) (hcnv : p ⇓ μ :: s) :
  q ∈ wt_set_mu p μ s hcnv -> p ⟹{μ} q.
Proof.
  intros mem.
  eapply elem_of_union_list in mem as (g & mem1 & mem2).
  eapply elem_of_list_fmap in mem1 as ((t & hw1) & eq & mem1). subst.
  eapply elem_of_union_list in mem2 as (g & mem3 & mem4).
  eapply elem_of_list_fmap in mem3 as ((u & hlts) & eq & mem3). subst.
  eapply elem_of_list_to_set, elem_of_list_fmap in mem4 as ((v & hw2) & eq & mem4). subst.
  eapply wt_push_nil_left. eapply bool_decide_unpack. eassumption.
  eapply wt_act. eapply bool_decide_unpack. eassumption.
  eapply bool_decide_unpack. eassumption.
Qed.

Lemma wt_set_mu_spec2 `{FiniteImageLts P A}
  (p q : P) (μ : A) (s : trace A) (hcnv : p ⇓ μ :: s) :
  p ⟹{μ} q -> q ∈ wt_set_mu p μ s hcnv.
Proof.
  intros w.
  eapply wt_decomp_one in w as (p0 & p1 & hw1 & hlts & hw2).
  eapply elem_of_union_list. eexists. split.
  eapply elem_of_list_fmap. exists (dexist p0 hw1). split. reflexivity. eapply elem_of_enum.
  eapply elem_of_union_list. eexists. split.
  eapply elem_of_list_fmap. exists (dexist p1 hlts). split. reflexivity. eapply elem_of_enum.
  eapply elem_of_list_to_set, elem_of_list_fmap.
  exists (dexist q hw2). split. reflexivity. eapply elem_of_enum.
Qed.

Lemma wt_mu_set_dec `{FiniteImageLts P A} p μ s (hcnv : p ⇓ μ :: s) : 
    forall q, Decision (p ⟹{μ} q).
Proof.
  intro q.
  destruct (decide (q ∈ wt_set_mu p μ s hcnv)).
  - left. eapply  (wt_set_mu_spec1 p q μ s hcnv e).
  - right. intro wt. eapply n. now eapply wt_set_mu_spec2.
Qed.

Lemma wt_mu_set_fin_aux `{FiniteImageLts P A}
  (p : P) μ s (hcnv : p ⇓ μ :: s) (d : ∀ q, Decision (p ⟹{μ} q)) : 
    Finite (dsig (fun q => p ⟹{μ} q)).
Proof.
  unfold dsig.
  eapply (in_list_finite (elements (wt_set_mu p μ s hcnv))).
  intros q Htrans%bool_decide_unpack.
  now eapply elem_of_elements, wt_set_mu_spec2.
Qed.

Definition wt_set_mu_fin `{FiniteImageLts P A}
  (p : P) μ s (hcnv : p ⇓ μ :: s) : Finite (dsig (fun q => p ⟹{μ} q)) :=
  wt_mu_set_fin_aux p μ s hcnv (wt_mu_set_dec p μ s hcnv).

Fixpoint wt_set `{FiniteImageLts P A} (p : P) (s : trace A) (hcnv : cnv p s) : gset P :=
  match s as s0 return cnv p s0 -> gset P with
  | [] =>
      fun _ => wt_set_nil p (cnv_terminate p _ hcnv)
  | μ :: s' =>
      fun f =>
        let ts := @enum (dsig (fun q => p ⟹{μ} q)) _ (wt_set_mu_fin p μ s' f) in
        ⋃ map (fun t =>
                 let hcnv := cnv_preserved_by_wt_act s' p μ f (`t) (proj2_dsig t) in
                 wt_set (`t) s' hcnv
          ) ts
  end hcnv.

Lemma wt_set_spec1 `{FiniteImageLts P A}
  (p q : P) (s : trace A) (hcnv : p ⇓ s) :
  q ∈ wt_set p s hcnv -> p ⟹[s] q.
Proof.
  revert p q hcnv. induction s; intros p q hcnv mem; simpl in *.
  - eapply wt_set_nil_spec1. eassumption.
  - eapply elem_of_union_list in mem as (g & mem1 & mem2).
    eapply elem_of_list_fmap in mem1 as ((t & hw1) & eq & mem1). subst.
    eapply wt_push_left. eapply bool_decide_unpack. eassumption.
    eapply IHs. eassumption.
Defined.

Lemma wt_set_spec2 `{FiniteImageLts P A}
  (p q : P) (s : trace A) (hcnv : p ⇓ s) :
  p ⟹[s] q -> q ∈ wt_set p s hcnv.
Proof.
  revert p q hcnv.
  induction s as [|μ s']; intros p q hcnv w; simpl in *.
  - eapply wt_set_nil_spec2. eauto with mdb.
  - eapply wt_pop in w as (t & w1 & w2).
    eapply elem_of_union_list.
    eexists. split.
    + eapply elem_of_list_fmap.
      exists (dexist t w1). now split; [|eapply elem_of_enum].
    + now eapply IHs'.
Defined.

Lemma wt_set_dec `{FiniteImageLts P A} p s (hcnv : p ⇓ s) : 
    forall q, Decision (p ⟹[s] q).
Proof.
  intro q.
  destruct (decide (q ∈ wt_set p s hcnv)).
  - left. eapply  (wt_set_spec1 p q s hcnv e).
  - right. intro wt. eapply n. now eapply wt_set_spec2.
Qed.

Lemma wt_set_fin_aux `{FiniteImageLts P A}
  (p : P) s (hcnv : p ⇓ s) (d : ∀ q, Decision (p ⟹[s] q)) : 
    Finite (dsig (fun q => p ⟹[s] q)).
Proof.
  unfold dsig.
  eapply (in_list_finite (elements (wt_set p s hcnv))).
  intros q Htrans%bool_decide_unpack.
  now eapply elem_of_elements, wt_set_spec2.
Qed.

Definition wt_set_fin `{FiniteImageLts P A}
  (p : P) s (hcnv : p ⇓ s) : Finite (dsig (fun q => p ⟹[s] q)) :=
  wt_set_fin_aux p s hcnv (wt_set_dec p s hcnv).

Fixpoint wt_nil_refuses_set `{FiniteImageLts P A} (p : P) (ht : p ⤓) : gset P :=
  match lts_refuses_decidable p τ with
  | left  _ => {[ p ]}
  | right _ =>
      let '(tstep _ f) := ht in
      let k p := wt_nil_refuses_set (`p) (f (`p) (proj2_dsig p)) in
      ⋃ map k (enum (dsig (fun q => p ⟶ q)))
  end.

Lemma wt_nil_refuses_set_spec1 `{FiniteImageLts P A}
  (p q : P) (ht : p ⤓) :
  q ∈ wt_nil_refuses_set p ht -> p ⟹ q /\ q ↛.
Proof.
  case ht. induction ht.
  intros ht mem.
  simpl in mem.
  case (lts_refuses_decidable p τ) in mem.
  - eapply elem_of_singleton_1 in mem. subst. eauto with mdb.
  - eapply elem_of_union_list in mem as (g & mem1 & mem2).
    eapply elem_of_list_fmap in mem1 as ((t & hw1) & eq & mem1). subst.
    simpl in mem2. case (ht t (proj2_dsig (t ↾ hw1))) eqn:eq.
    edestruct (H3 t). now eapply bool_decide_unpack. eassumption.
    split; eauto with mdb. eapply wt_tau. eapply bool_decide_unpack.
    eassumption. eassumption.
Qed.

Lemma wt_nil_refuses_set_spec2 `{FiniteImageLts P A}
  (p q : P) (ht : p ⤓) :
  (p ⟹ q /\ q ↛) -> q ∈ wt_nil_refuses_set p ht.
Proof.
  intros (hw & hst). dependent induction hw; case ht; induction ht; intros ht; simpl.
  - case (lts_refuses_decidable p τ); set_solver.
  - case (lts_refuses_decidable p τ); intro hst'.
    + exfalso. eapply (lts_refuses_spec2 p τ); eauto.
    + eapply elem_of_union_list.
      eexists. split. eapply elem_of_list_fmap.
      exists (dexist q l). split. reflexivity. eapply elem_of_enum. eapply IHhw; eauto.
Qed.

Lemma wt_nil_refuses_set_dec `{FiniteImageLts P A} p (ht : p ⤓) : 
  forall q, Decision (p ⟹ q /\ q ↛).
Proof.
  intro q.
  destruct (decide (q ∈ wt_nil_refuses_set p ht)).
  - left. eapply (wt_nil_refuses_set_spec1 p q ht e).
  - right. intro wt. eapply n. now eapply wt_nil_refuses_set_spec2.
Qed.

Lemma wt_nil_refuses_set_fin_aux `{FiniteImageLts P A}
  (p : P) (ht : p ⤓) (d : ∀ q, Decision (p ⟹ q /\ q ↛)) : 
    Finite (dsig (fun q => p ⟹ q /\ q ↛)).
Proof.
  unfold dsig.
  eapply (in_list_finite (elements (wt_nil_refuses_set p ht))).
  intros q Htrans%bool_decide_unpack.
  now eapply elem_of_elements, wt_nil_refuses_set_spec2.
Qed.

Definition wt_nil_refuses_set_fin `{FiniteImageLts P A}
  (p : P) (ht : p ⤓) : Finite (dsig (fun q => p ⟹ q /\ q ↛)) :=
  wt_nil_refuses_set_fin_aux p ht (wt_nil_refuses_set_dec p ht).

Lemma cnv_wt_s_terminate `{Lts P A}
  (p q : P) s (hcnv : p ⇓ s) : p ⟹[s] q -> q ⤓.
Proof. eapply cnv_iff_prefix_terminate; eauto. Qed.

Definition wt_refuses_set `{FiniteImageLts P A} (p : P) s (hcnv : p ⇓ s) : gset P :=
  let ps := @enum (dsig (fun q => p ⟹[s] q)) _ (wt_set_fin p s hcnv) in
  let k t := wt_nil_refuses_set (`t) (cnv_wt_s_terminate p (`t) s hcnv (proj2_dsig t)) in
  ⋃ map k ps.

Lemma wt_refuses_set_spec1 `{FiniteImageLts P A}
  (p q : P) s (hcnv : p ⇓ s) :
  q ∈ wt_refuses_set p s hcnv -> p ⟹[s] q /\ q ↛.
Proof.
  intro mem.
  eapply elem_of_union_list in mem as (g & mem1 & mem2).
  eapply elem_of_list_fmap in mem1 as ((t & hw1) & eq & mem1). subst.
  simpl in mem2.
  eapply wt_nil_refuses_set_spec1 in mem2.
  split. eapply wt_push_nil_right. eapply bool_decide_unpack. eassumption. firstorder.
  firstorder.
Qed.

Lemma wt_refuses_set_spec2 `{FiniteImageLts P A}
  (p q : P) s (hcnv : p ⇓ s) :
  (p ⟹[s] q /\ q ↛) -> q ∈ wt_refuses_set p s hcnv.
Proof.
  intros (hw & hst).
  eapply elem_of_union_list.
  eexists. split. eapply elem_of_list_fmap.
  exists (dexist q hw). split. reflexivity. eapply elem_of_enum.
  simpl. eapply wt_nil_refuses_set_spec2. eauto with mdb.
Qed.

Lemma wt_refuses_set_fin_aux `{FiniteImageLts P A}
  (p : P) s (hcnv : p ⇓ s) (d : ∀ q, Decision (p ⟹[s] q /\ q ↛)) : 
  Finite (dsig (fun q => p ⟹[s] q /\ q ↛)).
Proof.
  unfold dsig.
  eapply (in_list_finite (elements (wt_refuses_set p s hcnv))).
  intros q Htrans%bool_decide_unpack.
  now eapply elem_of_elements, wt_refuses_set_spec2.
Qed.


Lemma wt_refuses_set_dec `{FiniteImageLts P A} p s (hcnv : p ⇓ s) : 
  forall q, Decision (p ⟹[s] q /\ q ↛).
Proof.
  intro q.
  destruct (decide (q ∈ wt_refuses_set p s hcnv)).
  - left. eapply (wt_refuses_set_spec1 p q s hcnv e).
  - right. intro wt. eapply n. now eapply wt_refuses_set_spec2.
Qed.

Definition wt_refuses_set_fin `{FiniteImageLts P A}
  (p : P) s (hcnv : p ⇓ s) : Finite (dsig (fun q => p ⟹[s] q /\ q ↛)) :=
  wt_refuses_set_fin_aux p s hcnv (wt_refuses_set_dec p s hcnv).

Lemma wt_nil_set_refuses `{FiniteImageLts P A} p hcnv :
  lts_refuses p τ -> wt_set p [] hcnv = {[ p ]}.
Proof.
  intros hst.
  eapply leibniz_equiv.
  intro q. split.
  - intro mem.
    eapply wt_set_spec1 in mem.
    inversion mem; subst.
    + set_solver.
    + exfalso. eapply lts_refuses_spec2; eauto.
  - intro mem. eapply wt_set_spec2. replace q with p.
    eauto with mdb. set_solver.
Qed.

Lemma wt_refuses_set_refuses_singleton `{FiniteImageLts P A} p hcnv :
  lts_refuses p τ -> wt_refuses_set p [] hcnv = {[ p ]}.
Proof.
  intro hst.
  eapply leibniz_equiv.
  intro q. split; intro mem.
  - eapply wt_refuses_set_spec1 in mem as (w & hst').
    inversion w; subst. set_solver. exfalso. eapply lts_refuses_spec2; eauto.
  - eapply elem_of_singleton_1 in mem. subst.
    eapply wt_refuses_set_spec2. split; eauto with mdb.
Qed.

Fixpoint wt_s_set_from_pset_xs `{Lts P A, !FiniteImageLts P A}
  (ps : list P) s (hcnv : forall p, p ∈ ps -> p ⇓ s) : gset P :=
  match ps as ps0 return (forall p, p ∈ ps0 -> p ⇓ s) -> gset P with
  | [] => fun _ => ∅
  | p :: ps' =>
      fun ha =>
        let pr := ha p (elem_of_list_here p ps') in
        let ys := wt_set p s pr in
        let ha' := fun q mem => ha q (elem_of_list_further q p ps' mem) in
        ys ∪ wt_s_set_from_pset_xs ps' s ha'
  end hcnv.

Definition wt_set_from_pset_spec1_xs `{FiniteImageLts P A}
  (ps : list P) (s : trace A) (qs : gset P) :=
  forall q, q ∈ qs -> exists p, p ∈ ps /\ p ⟹[s] q.

Definition wt_set_from_pset_spec2_xs `{FiniteImageLts P A}
  (ps : list P) (s : trace A) (qs : gset P) :=
  forall p q, p ∈ ps -> p ⟹[s] q -> q ∈ qs.

Definition wt_set_from_pset_spec_xs `{FiniteImageLts P A}
  (ps : list P) (s : trace A) (qs : gset P) :=
  wt_set_from_pset_spec1_xs ps s qs /\ wt_set_from_pset_spec2_xs ps s qs.

Lemma wt_s_set_from_pset_xs_ispec `{Lts P A, !FiniteImageLts P A}
  (ps : list P) s (hcnv : forall p, p ∈ ps -> p ⇓ s) :
  wt_set_from_pset_spec_xs ps s (wt_s_set_from_pset_xs ps s hcnv).
Proof.
  split.
  - induction ps as [|p ps].
    intros p mem. set_solver.
    intros p' mem. simpl in *.
    eapply elem_of_union in mem as [hl|hr].
    exists p. split.
    set_solver. now eapply wt_set_spec1 in hl.
    eapply IHps in hr as (p0 & mem & hwp0).
    exists p0. repeat split; set_solver.
  - induction ps as [|p ps].
    + intros p'. set_solver.
    + intros p' q mem hwp'.
      eapply elem_of_union.
      inversion mem; subst.
      ++ left. eapply wt_set_spec2; eauto.
      ++ right. eapply IHps in hwp'; eauto.
Qed.

Lemma lift_cnv_elements `{Lts P A, !FiniteImageLts P A}
  (ps : gset P) s (hcnv : forall p, p ∈ ps -> p ⇓ s) :
  forall p, p ∈ (elements ps) -> p ⇓ s.
Proof.
  intros p mem.
  eapply hcnv. now eapply elem_of_elements.
Qed.

Definition wt_s_set_from_pset `{Lts P A, !FiniteImageLts P A}
  (ps : gset P) s (hcnv : forall p, p ∈ ps -> p ⇓ s) : gset P :=
  wt_s_set_from_pset_xs (elements ps) s (lift_cnv_elements ps s hcnv).

Definition wt_set_from_pset_spec1 `{Countable P, Lts P A}
  (ps : gset P) (s : trace A) (qs : gset P) :=
  forall q, q ∈ qs -> exists p, p ∈ ps /\ p ⟹[s] q.

Definition wt_set_from_pset_spec2 `{FiniteImageLts P A}
  (ps : gset P) (s : trace A) (qs : gset P) :=
  forall p q, p ∈ ps -> p ⟹[s] q -> q ∈ qs.

Definition wt_set_from_pset_spec `{FiniteImageLts P A}
  (ps : gset P) (s : trace A) (qs : gset P) :=
  wt_set_from_pset_spec1 ps s qs /\ wt_set_from_pset_spec2 ps s qs.

Lemma wt_s_set_from_pset_ispec `{Lts P A, !FiniteImageLts P A}
  (ps : gset P) s (hcnv : forall p, p ∈ ps -> p ⇓ s) :
  wt_set_from_pset_spec ps s (wt_s_set_from_pset ps s hcnv).
Proof.
  split.
  - intros p mem.
    eapply wt_s_set_from_pset_xs_ispec in mem as (p' & mem & hwp').
    exists p'. split; set_solver.
  - intros p q mem hwp.
    eapply wt_s_set_from_pset_xs_ispec.
    eapply elem_of_elements; eassumption. eassumption.
Qed.
