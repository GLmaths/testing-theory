(*
   Copyright (c) 2026 Gaëtan Lopez <glopez@irif.fr>

   This file formalises the LTS from:
   R. De Nicola, R. Pugliese, "Linda-based applicative and imperative
   process algebras", Theoretical Computer Science 238 (2000) 389-437.

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

From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable option gmap.
From TestingTheory Require Import ActTau gLts InputOutputActions Bisimulation Lts_OBA Lts_FW Lts_OBA_FB
  FiniteImageLTS coFiniteImage InteractionBetweenLts InListPropHelper PAL_Syntax.

(** * PAL: a Process Algebra based on Linda

    A [gLts] formalisation of the LTS from:

    R. De Nicola, R. Pugliese, "Linda-based applicative and imperative
    process algebras", Theoretical Computer Science 238 (2000) 389-437.

    The syntax, tuple evaluation and pattern matching are in [PAL_Syntax.v].
    This file builds the LTS itself (Table 3 Action Relation, Table 4
    Internal Relation, Definition 4.2's combination into one transition
    system) — the paper's testing theory / proof system / denotational
    semantics (Sections 5-9) and the IPAL extension (Section 8) are out of
    scope. *)

Section PAL.
  Context (Val : Type) `{Countable Val}.

  Notation vexp := (vexp Val).
  Notation field := (field Val).
  Notation tuple := (tuple Val).
  Notation bexp := (bexp Val).
  Notation term := (term Val).
  Notation out_field := (out_field Val).
  Notation eot := (eot Val).
  Notation in_field := (in_field Val).
  Notation eit := (eit Val).

  Definition PAL_Act := ExtAct eot.

  Definition comp_act (mu : PAL_Act) : PAL_Act :=
    match mu with ActIn ot => ActOut ot | ActOut ot => ActIn ot end.

  (** ** The LTS (Tables 3-4, Definition 4.2)

      Action Relation (AR1-AR8, Table 3) carries visible labels only;
      Internal Relation (IR1-IR13, Table 4) is always [τ] — combined here
      into one [lts_step] relation per this project's [Act A := ActExt a
      | τ] convention, with each constructor kept faithful to a single
      named rule of the paper. *)
  Open Scope pal_scope.
  Inductive lts_step : term -> Act PAL_Act -> term -> Prop :=
    (* AR1 *)
    | ar1 t E it ot :
        eval_in_tuple t = Some it -> tuple_match it ot ->
        lts_step (in( t ) • E) (ot ?) (subst_term (build_subst it ot) E)
    (* AR2 *)
    | ar2 t E it ot :
        eval_in_tuple t = Some it -> tuple_match it ot ->
        lts_step (read( t ) • E) (ot ?)
          ((out( eot_to_tuple ot ) • 𝟘) ‖ (subst_term (build_subst it ot) E))
    (* AR3 *)
    | ar3 t ot :
        eval_out_tuple t = Some ot ->
        lts_step (out( t ) • 𝟘) (ot !) 𝟘
    (* AR4, + symmetric *)
    | ar4_l E1 E2 mu E1' : lts_step E1 (ActExt mu) E1' -> lts_step (E1 □ E2) (ActExt mu) E1'
    | ar4_r E1 E2 mu E2' : lts_step E2 (ActExt mu) E2' -> lts_step (E1 □ E2) (ActExt mu) E2'
    (* AR5, + symmetric *)
    | ar5_l E1 E2 mu E1' : lts_step E1 (ActExt mu) E1' -> lts_step (E1 ‖ E2) (ActExt mu) (E1' ‖ E2)
    | ar5_r E1 E2 mu E2' : lts_step E2 (ActExt mu) E2' -> lts_step (E1 ‖ E2) (ActExt mu) (E1 ‖ E2')
    (* AR6 *)
    | ar6 E1 E2 mu E1' : lts_step E1 (ActExt mu) E1' -> lts_step (E1 ⌊ E2) (ActExt mu) (E1' ‖ E2)
    (* AR7 *)
    | ar7 be E1 E2 mu E1' :
        eval_bexp be = Some true -> lts_step E1 (ActExt mu) E1' -> lts_step (IF be THEN E1 ELSE E2) (ActExt mu) E1'
    (* AR8 *)
    | ar8 be E1 E2 mu E2' :
        eval_bexp be = Some false -> lts_step E2 (ActExt mu) E2' -> lts_step (IF be THEN E1 ELSE E2) (ActExt mu) E2'
    (* IR1 *)
    | ir1 : lts_step Ω τ Ω
    (* IR2 *)
    | ir2 X E : lts_step (rec X • E) τ (psubst X (rec X • E) E)
    (* IR3 *)
    | ir3 be E1 E2 E1' : eval_bexp be = Some true -> lts_step E1 τ E1' -> lts_step (IF be THEN E1 ELSE E2) τ E1'
    (* IR4 *)
    | ir4 be E1 E2 E2' : eval_bexp be = Some false -> lts_step E2 τ E2' -> lts_step (IF be THEN E1 ELSE E2) τ E2'
    (* IR5 *)
    | ir5 t E : E <> 𝟘 -> lts_step (out( t ) • E) τ ((out( t ) • 𝟘) ‖ E)
    (* IR6 *)
    | ir6 E1 E2 : lts_step (eval( E1 ) • E2) τ (E1 ‖ E2)
    (* IR7, both summands (paper's "symmetrical version") *)
    | ir7_l E1 E2 : lts_step (E1 ⊕ E2) τ E1
    | ir7_r E1 E2 : lts_step (E1 ⊕ E2) τ E2
    (* IR8, + symmetric *)
    | ir8_l E1 E2 E1' : lts_step E1 τ E1' -> lts_step (E1 □ E2) τ (E1' □ E2)
    | ir8_r E1 E2 E2' : lts_step E2 τ E2' -> lts_step (E1 □ E2) τ (E1 □ E2')
    (* IR9, + symmetric *)
    | ir9_l E1 E2 E1' : lts_step E1 τ E1' -> lts_step (E1 ‖ E2) τ (E1' ‖ E2)
    | ir9_r E1 E2 E2' : lts_step E2 τ E2' -> lts_step (E1 ‖ E2) τ (E1 ‖ E2')
    (* IR10, + symmetric (comm-merge congruence) *)
    | ir10_l E1 E2 E1' : lts_step E1 τ E1' -> lts_step (E1 |ₖ E2) τ (E1' |ₖ E2)
    | ir10_r E1 E2 E2' : lts_step E2 τ E2' -> lts_step (E1 |ₖ E2) τ (E1 |ₖ E2')
    (* IR11 (left-merge, no symmetric: only the left process is "in control") *)
    | ir11 E1 E2 E1' : lts_step E1 τ E1' -> lts_step (E1 ⌊ E2) τ (E1' ⌊ E2)
    (* IR12 (parallel synchronisation via complementary actions) *)
    | ir12 E1 E2 mu E1' E2' :
        lts_step E1 (ActExt mu) E1' -> lts_step E2 (ActExt (comp_act mu)) E2' ->
        lts_step (E1 ‖ E2) τ (E1' ‖ E2')
    (* IR13 (comm-merge synchronisation) *)
    | ir13 E1 E2 mu E1' E2' :
        lts_step E1 (ActExt mu) E1' -> lts_step E2 (ActExt (comp_act mu)) E2' ->
        lts_step (E1 |ₖ E2) τ (E1' ‖ E2').
  Close Scope pal_scope.

  #[global] Instance PAL_Act_eqdec : EqDecision PAL_Act.
  Proof. solve_decision. Defined.

  (** ** Decidability

      The paper's own Proposition 4.4 notes this LTS is "in general not
      finitely branching" (e.g. [t_in t E] has infinitely many
      derivations when [Val] is infinite), so successors cannot be
      brute-force enumerated over the whole action type.  [all_steps]
      computes, for a given label, the FULL finite list of successors,
      bounding the search for IR12/IR13's synchronising partner via
      [collect_out] — mirroring the paper's own Proposition 4.4 idea that
      one side of a successful synchronisation is always a deterministic,
      finitely-many-derivations [t_out t t_nil]-congruence leaf. *)

  (* the (syntactically finite) set of output tuples reachable from [E] via a
     single congruence step of AR3-AR8 alone (never touching in/read) — the
     "OT(P)" set of the paper's Proposition 4.4, needed to bound the search for
     IR12/IR13's synchronising partner without enumerating all input tuples *)
  Fixpoint collect_out (E : term) : list eot :=
    match E with
    | t_out t t_nil => match eval_out_tuple t with Some ot => [ot] | None => [] end
    | t_echoice E1 E2 => collect_out E1 ++ collect_out E2
    | t_par E1 E2 => collect_out E1 ++ collect_out E2
    | t_lmerge E1 E2 => collect_out E1
    | t_if be E1 E2 =>
        match eval_bexp be with
        | Some true => collect_out E1
        | Some false => collect_out E2
        | None => []
        end
    | _ => []
    end.

  (* the computable "all reachable successors for a given label" function —
     mirrors [lts_step]'s 24 constructors directly; the SOS rules that search
     for a synchronising partner (IR12/IR13) are bounded via [collect_out]
     (finite) rather than searching over the whole, possibly-infinite, action
     type, exactly as sketched in the paper's own Proposition 4.4. *)
  Fixpoint all_steps (p : term) (alpha : Act PAL_Act) : list term :=
    match p with
    | t_nil => []
    | t_pvar _ => []
    | t_success => []
    | t_undef => match alpha with τ => [t_undef] | _ => [] end
    | t_rec X E => match alpha with τ => [psubst X (t_rec X E) E] | _ => [] end
    | t_out t E =>
        match alpha with
        | ActExt (ActOut ot) =>
            if bool_decide (E = t_nil) then
              match eval_out_tuple t with
              | Some ot' => if bool_decide (ot = ot') then [t_nil] else []
              | None => []
              end
            else []
        | τ => if bool_decide (E <> t_nil) then [t_par (t_out t t_nil) E] else []
        | _ => []
        end
    | t_in t E =>
        match alpha with
        | ActExt (ActIn ot) =>
            match eval_in_tuple t with
            | Some it => if tuple_match_b it ot then [subst_term (build_subst it ot) E] else []
            | None => []
            end
        | _ => []
        end
    | t_read t E =>
        match alpha with
        | ActExt (ActIn ot) =>
            match eval_in_tuple t with
            | Some it => if tuple_match_b it ot
                         then [t_par (t_out (eot_to_tuple ot) t_nil) (subst_term (build_subst it ot) E)]
                         else []
            | None => []
            end
        | _ => []
        end
    | t_eval E1 E2 => match alpha with τ => [t_par E1 E2] | _ => [] end
    | t_if be E1 E2 =>
        match eval_bexp be with
        | Some true => all_steps E1 alpha
        | Some false => all_steps E2 alpha
        | None => []
        end
    | t_ichoice E1 E2 => match alpha with τ => [E1; E2] | _ => [] end
    | t_echoice E1 E2 =>
        match alpha with
        | τ => map (fun E1' => t_echoice E1' E2) (all_steps E1 τ)
               ++ map (fun E2' => t_echoice E1 E2') (all_steps E2 τ)
        | ActExt _ => all_steps E1 alpha ++ all_steps E2 alpha
        end
    | t_lmerge E1 E2 =>
        match alpha with
        | τ => map (fun E1' => t_lmerge E1' E2) (all_steps E1 τ)
        | ActExt _ => map (fun E1' => t_par E1' E2) (all_steps E1 alpha)
        end
    | t_cmerge E1 E2 =>
        match alpha with
        | τ =>
            map (fun E1' => t_cmerge E1' E2) (all_steps E1 τ)
            ++ map (fun E2' => t_cmerge E1 E2') (all_steps E2 τ)
            ++ flat_map (fun ot =>
                 flat_map (fun E1' => map (fun E2' => t_par E1' E2') (all_steps E2 (ActExt (ActIn ot))))
                   (all_steps E1 (ActExt (ActOut ot))))
                 (collect_out E1)
            ++ flat_map (fun ot =>
                 flat_map (fun E2' => map (fun E1' => t_par E1' E2') (all_steps E1 (ActExt (ActIn ot))))
                   (all_steps E2 (ActExt (ActOut ot))))
                 (collect_out E2)
        | ActExt _ => []
        end
    | t_par E1 E2 =>
        match alpha with
        | τ =>
            map (fun E1' => t_par E1' E2) (all_steps E1 τ)
            ++ map (fun E2' => t_par E1 E2') (all_steps E2 τ)
            ++ flat_map (fun ot =>
                 flat_map (fun E1' => map (fun E2' => t_par E1' E2') (all_steps E2 (ActExt (ActIn ot))))
                   (all_steps E1 (ActExt (ActOut ot))))
                 (collect_out E1)
            ++ flat_map (fun ot =>
                 flat_map (fun E2' => map (fun E1' => t_par E1' E2') (all_steps E1 (ActExt (ActIn ot))))
                   (all_steps E2 (ActExt (ActOut ot))))
                 (collect_out E2)
        | ActExt _ =>
            map (fun E1' => t_par E1' E2) (all_steps E1 alpha)
            ++ map (fun E2' => t_par E1 E2') (all_steps E2 alpha)
        end
    end.

  Hint Constructors lts_step : mdb.

  Lemma all_steps_sound p alpha q : In q (all_steps p alpha) -> lts_step p alpha q.
  Proof.
    revert alpha q.
    induction p; intros alpha q Hin; simpl in Hin;
      try (destruct alpha as [mu|]; simpl in Hin).
    all: try (exact (match Hin with end)).
    - destruct Hin as [<- | []]. eauto with mdb.
    - destruct mu as [ot|ot]; [contradiction |].
      case_bool_decide as Heq; [subst | contradiction].
      destruct (eval_out_tuple t) as [ot'|] eqn:Hev; [| contradiction].
      case_bool_decide as Heq2; [subst | contradiction].
      destruct Hin as [<- | []].
      eauto with mdb.
    - case_bool_decide as Heq; [destruct Hin as [<- | []]; eauto with mdb | contradiction].
    - destruct mu as [ot|ot]; [| contradiction].
      destruct (eval_in_tuple t) as [it|] eqn:Hev; [| contradiction].
      destruct (tuple_match_b it ot) eqn:Hm; [| contradiction].
      destruct Hin as [<- | []].
      apply tuple_match_b_correct in Hm.
      eauto with mdb.
    - destruct mu as [ot|ot]; [| contradiction].
      destruct (eval_in_tuple t) as [it|] eqn:Hev; [| contradiction].
      destruct (tuple_match_b it ot) eqn:Hm; [| contradiction].
      destruct Hin as [<- | []].
      apply tuple_match_b_correct in Hm.
      eauto with mdb.
    - destruct Hin as [<- | []]. eauto with mdb.
    - destruct (eval_bexp be) as [b|] eqn:Hbe; [destruct b |]; simpl in Hin.
      + eapply ar7; [exact Hbe | apply IHp1, Hin].
      + eapply ar8; [exact Hbe | apply IHp2, Hin].
      + contradiction.
    - destruct (eval_bexp be) as [b|] eqn:Hbe; [destruct b |]; simpl in Hin.
      + eapply ir3; [exact Hbe | apply IHp1, Hin].
      + eapply ir4; [exact Hbe | apply IHp2, Hin].
      + contradiction.
    - destruct Hin as [<- | [<- | []]]; eauto with mdb.
    - apply in_app_iff in Hin as [Hin | Hin].
      + eapply ar4_l, IHp1, Hin.
      + eapply ar4_r, IHp2, Hin.
    - apply in_app_iff in Hin as [Hin | Hin].
      + apply in_map_iff in Hin as (E1' & <- & Hin). eapply ir8_l, IHp1, Hin.
      + apply in_map_iff in Hin as (E2' & <- & Hin). eapply ir8_r, IHp2, Hin.
    - apply in_app_iff in Hin as [Hin | Hin].
      + apply in_map_iff in Hin as (E1' & <- & Hin). eapply ar5_l, IHp1, Hin.
      + apply in_map_iff in Hin as (E2' & <- & Hin). eapply ar5_r, IHp2, Hin.
    - apply in_app_iff in Hin as [Hin | Hin];
        [| apply in_app_iff in Hin as [Hin | Hin];
           [| apply in_app_iff in Hin as [Hin | Hin]]].
      + apply in_map_iff in Hin as (E1' & <- & Hin). eapply ir9_l, IHp1, Hin.
      + apply in_map_iff in Hin as (E2' & <- & Hin). eapply ir9_r, IHp2, Hin.
      + apply in_flat_map in Hin as (ot & Hot & Hin2).
        apply in_flat_map in Hin2 as (E1' & HE1' & Hin3).
        apply in_map_iff in Hin3 as (E2' & <- & HE2').
        eapply ir12; [apply IHp1, HE1' | apply IHp2, HE2'].
      + apply in_flat_map in Hin as (ot & Hot & Hin2).
        apply in_flat_map in Hin2 as (E2' & HE2' & Hin3).
        apply in_map_iff in Hin3 as (E1' & <- & HE1').
        eapply ir12; [apply IHp1, HE1' | apply IHp2, HE2'].
    - apply in_map_iff in Hin as (E1' & <- & Hin). eapply ar6, IHp1, Hin.
    - apply in_map_iff in Hin as (E1' & <- & Hin). eapply ir11, IHp1, Hin.
    - apply in_app_iff in Hin as [Hin | Hin];
        [| apply in_app_iff in Hin as [Hin | Hin];
           [| apply in_app_iff in Hin as [Hin | Hin]]].
      + apply in_map_iff in Hin as (E1' & <- & Hin). eapply ir10_l, IHp1, Hin.
      + apply in_map_iff in Hin as (E2' & <- & Hin). eapply ir10_r, IHp2, Hin.
      + apply in_flat_map in Hin as (ot & Hot & Hin2).
        apply in_flat_map in Hin2 as (E1' & HE1' & Hin3).
        apply in_map_iff in Hin3 as (E2' & <- & HE2').
        eapply ir13; [apply IHp1, HE1' | apply IHp2, HE2'].
      + apply in_flat_map in Hin as (ot & Hot & Hin2).
        apply in_flat_map in Hin2 as (E2' & HE2' & Hin3).
        apply in_map_iff in Hin3 as (E1' & <- & HE1').
        eapply ir13; [apply IHp1, HE1' | apply IHp2, HE2'].
    - destruct Hin as [<- | []]. eauto with mdb.
  Qed.

  Lemma out_step_in_collect_out E ot E' : lts_step E (ActExt (ActOut ot)) E' -> In ot (collect_out E).
  Proof.
    intros Hstep.
    remember (ActExt (ActOut ot)) as alpha eqn:Heq.
    induction Hstep; try discriminate Heq; simpl; auto.
    - injection Heq as <-. rewrite H0. left. reflexivity.
    - inversion Heq; subst. apply in_or_app. left. apply IHHstep. reflexivity.
    - inversion Heq; subst. apply in_or_app. right. apply IHHstep. reflexivity.
    - inversion Heq; subst. apply in_or_app. left. apply IHHstep. reflexivity.
    - inversion Heq; subst. apply in_or_app. right. apply IHHstep. reflexivity.
    - inversion Heq; subst. rewrite H0. apply IHHstep. reflexivity.
    - inversion Heq; subst. rewrite H0. apply IHHstep. reflexivity.
  Qed.

  Lemma all_steps_complete p alpha q : lts_step p alpha q -> In q (all_steps p alpha).
  Proof.
    intros Hstep.
    induction Hstep; simpl.
    - rewrite H0.
      assert (Hb : tuple_match_b it ot = true) by (apply tuple_match_b_correct; exact H1).
      rewrite Hb. left. reflexivity.
    - rewrite H0.
      assert (Hb : tuple_match_b it ot = true) by (apply tuple_match_b_correct; exact H1).
      rewrite Hb. left. reflexivity.
    - rewrite H0. case_bool_decide as Hc; [left; reflexivity | congruence].
    - apply in_or_app. left. exact IHHstep.
    - apply in_or_app. right. exact IHHstep.
    - apply in_or_app. left. apply in_map_iff. exists E1'. split; [reflexivity | exact IHHstep].
    - apply in_or_app. right. apply in_map_iff. exists E2'. split; [reflexivity | exact IHHstep].
    - apply in_map_iff. exists E1'. split; [reflexivity | exact IHHstep].
    - rewrite H0. exact IHHstep.
    - rewrite H0. exact IHHstep.
    - left. reflexivity.
    - left. reflexivity.
    - rewrite H0. exact IHHstep.
    - rewrite H0. exact IHHstep.
    - case_bool_decide as Hc; [left; reflexivity | contradiction].
    - left. reflexivity.
    - left. reflexivity.
    - right. left. reflexivity.
    - apply in_or_app. left. apply in_map_iff. exists E1'. split; [reflexivity | exact IHHstep].
    - apply in_or_app. right. apply in_map_iff. exists E2'. split; [reflexivity | exact IHHstep].
    - apply in_or_app. left. apply in_map_iff. exists E1'. split; [reflexivity | exact IHHstep].
    - apply in_or_app. right. apply in_or_app. left. apply in_map_iff. exists E2'. split; [reflexivity | exact IHHstep].
    - apply in_or_app. left. apply in_map_iff. exists E1'. split; [reflexivity | exact IHHstep].
    - apply in_or_app. right. apply in_or_app. left. apply in_map_iff. exists E2'. split; [reflexivity | exact IHHstep].
    - apply in_map_iff. exists E1'. split; [reflexivity | exact IHHstep].
    - destruct mu as [ot|ot].
      + pose proof (out_step_in_collect_out E2 ot E2' Hstep2) as Hot.
        apply in_or_app; right; apply in_or_app; right; apply in_or_app; right.
        apply in_flat_map. exists ot. split; [exact Hot |].
        apply in_flat_map. exists E2'. split; [exact IHHstep2 |].
        apply in_map_iff. exists E1'. split; [reflexivity | exact IHHstep1].
      + pose proof (out_step_in_collect_out E1 ot E1' Hstep1) as Hot.
        apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
        apply in_flat_map. exists ot. split; [exact Hot |].
        apply in_flat_map. exists E1'. split; [exact IHHstep1 |].
        apply in_map_iff. exists E2'. split; [reflexivity | exact IHHstep2].
    - destruct mu as [ot|ot].
      + pose proof (out_step_in_collect_out E2 ot E2' Hstep2) as Hot.
        apply in_or_app; right; apply in_or_app; right; apply in_or_app; right.
        apply in_flat_map. exists ot. split; [exact Hot |].
        apply in_flat_map. exists E2'. split; [exact IHHstep2 |].
        apply in_map_iff. exists E1'. split; [reflexivity | exact IHHstep1].
      + pose proof (out_step_in_collect_out E1 ot E1' Hstep1) as Hot.
        apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
        apply in_flat_map. exists ot. split; [exact Hot |].
        apply in_flat_map. exists E1'. split; [exact IHHstep1 |].
        apply in_map_iff. exists E2'. split; [reflexivity | exact IHHstep2].
  Qed.

  #[global] Instance PAL_Act_countable : Countable PAL_Act := _.

  (** ** [ExtAction]/[gLts] instances

      [non_blocking] is set to always-[False]: no PAL action is treated as
      non-blocking here (per project convention, this is a per-calculus
      choice — PAL's own asynchronous output is instead reflected directly
      in the SOS rules, via IR5's eager detachment of [t_out t E]'s
      continuation). *)

  Definition PAL_non_blocking (_ : PAL_Act) : Prop := False.

  #[global] Instance PAL_non_blocking_dec a : Decision (PAL_non_blocking a).
  Proof. right. intro H'. exact H'. Defined.

  Lemma PAL_dual_blocks (beta eta : PAL_Act) :
    PAL_non_blocking eta -> ext_act_match beta eta -> ~ PAL_non_blocking beta.
  Proof. intros Hnb _. contradiction. Qed.

  Definition PAL_exists_dual (mu : PAL_Act) : {eta | ext_act_match mu eta}.
  Proof.
    exists (match mu with ActIn a => ActOut a | ActOut a => ActIn a end).
    destruct mu; reflexivity.
  Defined.

  Lemma PAL_unique_nb (eta beta : PAL_Act) :
    ext_act_match beta eta -> eta = proj1_sig (PAL_exists_dual beta).
  Proof.
    intro Hdual.
    destruct beta as [a|a]; simpl.
    - apply simplify_match_input in Hdual. subst. reflexivity.
    - apply simplify_match_output in Hdual. subst. reflexivity.
  Qed.

  #[global] Instance PAL_ExtAction : ExtAction PAL_Act := {|
    eqdec := PAL_Act_eqdec;
    countable := PAL_Act_countable;
    non_blocking := PAL_non_blocking;
    non_blocking_dec := PAL_non_blocking_dec;
    dual := ext_act_match;
    dual_dec := ext_act_match_dec;
    dual_blocks := PAL_dual_blocks;
    duo_sym := ext_act_match_sym;
    exists_dual := PAL_exists_dual;
  |}.

  #[global] Instance PAL_UniqueDual : UniqueDual PAL_Act := PAL_unique_nb.

  Definition PAL_lts_refuses (p : term) (alpha : Act PAL_Act) : Prop := all_steps p alpha = [].

  #[global] Instance PAL_lts_step_decidable p alpha q : Decision (lts_step p alpha q).
  Proof.
    destruct (in_dec term_eqdec q (all_steps p alpha)) as [Hin|Hnin].
    - left. exact (all_steps_sound p alpha q Hin).
    - right. intro Hstep. exact (Hnin (all_steps_complete p alpha q Hstep)).
  Defined.

  #[global] Instance PAL_lts_refuses_decidable p alpha : Decision (PAL_lts_refuses p alpha).
  Proof.
    unfold PAL_lts_refuses.
    destruct (all_steps p alpha) as [| q l].
    - left. reflexivity.
    - right. discriminate.
  Defined.

  Definition PAL_lts_refuses_spec1 p alpha : ~ PAL_lts_refuses p alpha -> {q | lts_step p alpha q}.
  Proof.
    unfold PAL_lts_refuses. intro Hne.
    destruct (all_steps p alpha) as [|q l] eqn:E.
    - exfalso. apply Hne. reflexivity.
    - exists q. apply all_steps_sound. rewrite E. left. reflexivity.
  Defined.

  Definition PAL_lts_refuses_spec2 p alpha : {q | lts_step p alpha q} -> ~ PAL_lts_refuses p alpha.
  Proof.
    intros [q Hstep] Href.
    unfold PAL_lts_refuses in Href.
    pose proof (all_steps_complete p alpha q Hstep) as Hin.
    rewrite Href in Hin. exact Hin.
  Defined.

  #[global] Instance PAL_gLts : gLts term PAL_ExtAction :=
    @MkgLts term PAL_Act PAL_ExtAction
      lts_step term_eqdec PAL_lts_step_decidable
      PAL_lts_refuses PAL_lts_refuses_decidable
      PAL_lts_refuses_spec1 PAL_lts_refuses_spec2.

  (** ** [gLtsEq]/[gLtsOba]/forwarder instances

      [gLtsEq]'s bisimulation is plain syntactic equality (its own
      spec obligation is then a one-line rewrite).  Every [gLtsOba]/
      [gLtsObaFW]/[gLtsObaFB] proof obligation is guarded by a
      [non_blocking η] hypothesis, and [PAL_non_blocking] is always
      [False] (see above) — so all five axioms, [boomerang],
      [fwd_feedback], and [feedback] are vacuous. *)

  Lemma PAL_eq_spec p q (alpha : Act PAL_Act) :
    (exists r, p = r /\ lts_step r alpha q) -> (exists r, lts_step p alpha r /\ r = q).
  Proof.
    intros (r & -> & Hr). exists q. split; [exact Hr | reflexivity].
  Qed.

  #[global] Instance PAL_gLtsEq : gLtsEq term PAL_ExtAction := {|
    gLtsEq_gLts := PAL_gLts;
    eq_rel := eq;
    eq_rel_eq := eq_equivalence;
    eq_spec := PAL_eq_spec;
  |}.

  #[global] Instance PAL_gLtsOba : gLtsOba term (H:=PAL_ExtAction) (Rel:=PAL_gLtsEq).
  Proof.
    unshelve econstructor.
    - intros p q r eta alpha nb Hl1 Hl2. destruct nb.
    - intros p q1 q2 eta mu nb Hne Hl1 Hl2. destruct nb.
    - intros p q1 q2 eta nb Hl1 Hl2. destruct nb.
    - intros p1 p2 p3 eta nb Hl1 Hl2. destruct nb.
    - intros p1 p2 q1 q2 eta nb Hl1 Hl2 Heq. destruct nb.
  Defined.

  #[global] Instance PAL_gLtsObaFW : gLtsObaFW term PAL_Act.
  Proof.
    unshelve econstructor.
    - intros p1 eta beta. exists p1. intro nb. destruct nb.
    - intros p1 p2 p3 eta beta nb Hdual Hl1 Hl2. destruct nb.
  Defined.

  #[global] Instance PAL_gLtsObaFB : gLtsObaFB term PAL_Act.
  Proof.
    unshelve econstructor.
    intros p1 p2 p3 eta beta nb Hdual Hl1 Hl2. destruct nb.
  Defined.

  (** ** [FiniteImagegLts]/[coFiniteImagegLts]

      Both reuse [all_steps]: a literal-[α] successor set is exactly
      [all_steps p α] (via [all_steps_sound]/[all_steps_complete]), and
      a dual-[α] successor set is exactly [all_steps p (ActExt (comp_act
      α))] — since [dual]/[ext_act_match] pairs [ActIn ot] with
      [ActOut ot] on the very same payload, "some action dual to [α]"
      collapses to the single, determined action [comp_act α]
      ([PAL_co_next_iff]), never a genuine search over the (possibly
      infinite) alphabet. *)

  #[global] Instance PAL_FiniteImagegLts : FiniteImagegLts term PAL_Act.
  Proof.
    unshelve econstructor.
    - exact term_countable.
    - intros p alpha. unfold dsig.
      eapply (in_list_finite (all_steps p alpha)).
      intros q Hq%bool_decide_unpack.
      apply list_elem_of_In. apply all_steps_complete. exact Hq.
  Defined.

  Lemma PAL_co_next_iff p alpha q :
    (exists alpha', ext_act_match alpha' alpha /\ lts_step p (ActExt alpha') q) <->
    lts_step p (ActExt (comp_act alpha)) q.
  Proof.
    split.
    - intros (alpha' & Hdual & Hl).
      destruct alpha' as [a|a]; simpl in Hdual.
      + apply simplify_match_input in Hdual. subst. exact Hl.
      + apply simplify_match_output in Hdual. subst. exact Hl.
    - intro Hl. exists (comp_act alpha). split; [| exact Hl].
      destruct alpha as [a|a]; reflexivity.
  Qed.

  #[global] Instance PAL_co_next_states_decidable p alpha q :
    Decision (exists alpha', ext_act_match alpha' alpha /\ lts_step p (ActExt alpha') q).
  Proof.
    destruct (PAL_lts_step_decidable p (ActExt (comp_act alpha)) q) as [Hy|Hn].
    - left. apply PAL_co_next_iff. exact Hy.
    - right. intro Hc. apply Hn. apply PAL_co_next_iff. exact Hc.
  Defined.

  #[global] Instance PAL_coFiniteImagegLts : coFiniteImagegLts term PAL_Act.
  Proof.
    unshelve econstructor.
    - exact term_countable.
    - intros p. unfold dsig.
      eapply (in_list_finite (all_steps p τ)).
      intros q Hq%bool_decide_unpack.
      apply list_elem_of_In. apply all_steps_complete. exact Hq.
    - intros p alpha. unfold dsig.
      eapply (in_list_finite (all_steps p (ActExt (comp_act alpha)))).
      intros q Hq%bool_decide_unpack.
      apply list_elem_of_In. apply all_steps_complete. apply PAL_co_next_iff. exact Hq.
  Defined.

  (** ** [Prop_of_Inter term term PAL_Act ext_act_match]

      PAL interacting with itself.  The "essential actions" of a process
      are exactly its [ActOut ot] steps — i.e. [collect_out p] wrapped
      back into [PAL_Act] — never the (possibly infinite) [ActIn]
      side: [ext_act_match] forces one side of any synchronising pair to
      be an output, so [lts_essential_actions_spec_interact] only ever
      needs to place ONE of the two labels in the corresponding set, and
      that's always the output one.  [collect_out_witnesses] is the
      constructive converse of [out_step_in_collect_out] (built earlier
      for [all_steps]): every [ot] the function collects is genuinely
      reachable.  [lts_co_inter_action_left]/[_right] don't need to
      search at all — [ext_act_match]'s dual is a function
      ([ext_act_match_det]), so the "candidate" set is always the
      singleton [{[comp_act ξ]}]. *)

  Lemma collect_out_witnesses (E : term) (ot : eot) :
    In ot (collect_out E) -> {E' | lts_step E (ActExt (ActOut ot)) E'}.
  Proof.
    induction E; simpl; intro Hin; try contradiction.
    - destruct E; simpl in Hin; try contradiction.
      destruct (eval_out_tuple t) as [ot'|] eqn:Hev; [| contradiction].
      assert (Heq : ot = ot') by (destruct Hin as [H1|[]]; auto).
      subst ot'. exists t_nil. eapply ar3. exact Hev.
    - destruct (eval_bexp be) as [b|] eqn:Hbe; [destruct b |]; simpl in Hin; [| | contradiction].
      + specialize (IHE1 Hin) as [E1' HE1']. exists E1'. eapply ar7; [exact Hbe | exact HE1'].
      + specialize (IHE2 Hin) as [E2' HE2']. exists E2'. eapply ar8; [exact Hbe | exact HE2'].
    - destruct (in_dec (fun x y : eot => decide (x = y)) ot (collect_out E1)) as [Hin1|Hnin1].
      { specialize (IHE1 Hin1) as [E1' HE1']. exists E1'. eapply ar4_l. exact HE1'. }
      { assert (Hin2 : In ot (collect_out E2)) by (apply in_app_or in Hin as [?|?]; [contradiction | assumption]).
        specialize (IHE2 Hin2) as [E2' HE2']. exists E2'. eapply ar4_r. exact HE2'. }
    - destruct (in_dec (fun x y : eot => decide (x = y)) ot (collect_out E1)) as [Hin1|Hnin1].
      { specialize (IHE1 Hin1) as [E1' HE1']. exists (t_par E1' E2). eapply ar5_l. exact HE1'. }
      { assert (Hin2 : In ot (collect_out E2)) by (apply in_app_or in Hin as [?|?]; [contradiction | assumption]).
        specialize (IHE2 Hin2) as [E2' HE2']. exists (t_par E1 E2'). eapply ar5_r. exact HE2'. }
    - specialize (IHE1 Hin) as [E1' HE1']. exists (t_par E1' E2). eapply ar6. exact HE1'.
  Qed.

  Lemma ext_act_match_det mu xi : ext_act_match mu xi -> mu = comp_act xi.
  Proof.
    destruct xi as [a|a]; simpl; intro Hm; apply ext_act_match_sym in Hm.
    - apply simplify_match_input in Hm. subst. reflexivity.
    - apply simplify_match_output in Hm. subst. reflexivity.
  Qed.

  Definition PAL_essential_actions (p : term) : gset PAL_Act :=
    list_to_set (map ActOut (collect_out p)).

  Lemma PAL_essential_action_spec p xi :
    xi ∈ PAL_essential_actions p -> {p' | lts_step p (ActExt xi) p'}.
  Proof.
    intro Hmem. unfold PAL_essential_actions in Hmem.
    apply elem_of_list_to_set in Hmem. apply list_elem_of_In in Hmem.
    destruct xi as [a|a].
    - exfalso. apply in_map_iff in Hmem as (x & Heq & Hin). discriminate.
    - assert (Ha : In a (collect_out p)).
      { apply in_map_iff in Hmem as (x & Heq & Hin). injection Heq as ->. exact Hin. }
      destruct (collect_out_witnesses p a Ha) as [E' HE'].
      exists E'. exact HE'.
  Defined.

  Lemma PAL_essential_actions_spec_interact (p1 : term) mu1 p1' (p2 : term) mu2 p2' :
    lts_step p1 (ActExt mu1) p1' -> lts_step p2 (ActExt mu2) p2' -> ext_act_match mu1 mu2 ->
    mu1 ∈ PAL_essential_actions p1 \/ mu2 ∈ PAL_essential_actions p2.
  Proof.
    intros Hl1 Hl2 Hinter.
    destruct mu1 as [a|a].
    - right.
      apply ext_act_match_sym in Hinter. apply ext_act_match_det in Hinter. simpl in Hinter. subst mu2.
      apply elem_of_list_to_set. apply list_elem_of_In. apply in_map_iff.
      exists a. split; [reflexivity |].
      apply list_elem_of_In. apply list_elem_of_In. exact (out_step_in_collect_out p2 a p2' Hl2).
    - left.
      apply elem_of_list_to_set. apply list_elem_of_In. apply in_map_iff.
      exists a. split; [reflexivity |].
      exact (out_step_in_collect_out p1 a p1' Hl1).
  Qed.

  Lemma PAL_co_inter_action_spec mu xi :
    ext_act_match mu xi -> mu ∈ ({[comp_act xi]} : gset PAL_Act).
  Proof. intro Hx. apply ext_act_match_det in Hx. subst. apply elem_of_singleton_2. reflexivity. Qed.

  Lemma PAL_co_inter_action_spec' xi mu :
    ext_act_match xi mu -> mu ∈ ({[comp_act xi]} : gset PAL_Act).
  Proof. intro Hx. apply ext_act_match_sym in Hx. apply (PAL_co_inter_action_spec mu xi Hx). Qed.

  #[global] Instance PAL_Prop_of_Inter : Prop_of_Inter term term PAL_Act ext_act_match := {|
    inter_dec := ext_act_match_dec;
    lts_essential_actions_left := PAL_essential_actions;
    lts_essential_action_spec_left := PAL_essential_action_spec;
    lts_essential_actions_right := PAL_essential_actions;
    lts_essential_action_spec_right := PAL_essential_action_spec;
    lts_essential_actions_spec_interact := PAL_essential_actions_spec_interact;
    lts_co_inter_action_left := fun xi p1 => {[comp_act xi]};
    lts_co_inter_action_spec_left := fun p1 p1' xi mu p2 _ _ Hinter => PAL_co_inter_action_spec mu xi Hinter;
    lts_co_inter_action_right := fun xi p2 => {[comp_act xi]};
    lts_co_inter_action_spec_right := fun p2 p2' xi mu p1 _ _ Hinter => PAL_co_inter_action_spec' xi mu Hinter;
  |}.

End PAL.
