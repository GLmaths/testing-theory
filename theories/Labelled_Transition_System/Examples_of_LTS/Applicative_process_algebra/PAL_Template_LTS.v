(*
   Copyright (c) 2026 Gaëtan Lopez <glopez@irif.fr>

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

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base tactics countable option list gmap.
From TestingTheory Require Import ActTau gLts InputOutputActions Bisimulation Lts_OBA Lts_FW Lts_OBA_FB
  FiniteImageLTS coFiniteImage InteractionBetweenLts InListPropHelper PAL_Syntax.

(* * The alternative LTS of PAL

   An LTS on the terms of [PAL_Syntax] whose visible labels are the tuples of
   values: an input step receiving [ot] is labelled [ActIn ot], an output
   step emitting [ot] is labelled [ActOut ot], and the dual of [ActIn ot] is
   [ActOut ot]. The τ-transitions are those of [Applicative_process_algebra]
   ([PAL_Template_Tau.v]). *)

Section PAL_T.
  Context (Val : Type) `{Countable Val}.

  Notation term := (term Val).
  Notation tuple := (tuple Val).
  Notation eot := (eot Val).
  Notation eit := (eit Val).
  Notation in_field := (in_field Val).
  Notation out_field := (out_field Val).

  (** ** Labels *)

  Definition PALT_Act := ExtAct eot.

  #[global] Instance PALT_Act_eqdec : EqDecision PALT_Act.
  Proof. solve_decision. Defined.

  #[global] Instance PALT_Act_countable : Countable PALT_Act := _.

  Definition co_t (μ : PALT_Act) : PALT_Act :=
    match μ with ActIn a => ActOut a | ActOut a => ActIn a end.

  (** As in PAL, no action is non-blocking. *)
  Definition PALT_non_blocking (_ : PALT_Act) : Prop := False.

  #[global] Instance PALT_non_blocking_dec a : Decision (PALT_non_blocking a).
  Proof. right. intros []. Defined.

  Definition PALT_exists_dual (μ : PALT_Act) : {η | ext_act_match μ η}.
  Proof. exists (co_t μ). destruct μ; reflexivity. Defined.

  Lemma PALT_unique_nb (η β : PALT_Act) : ext_act_match β η → η = proj1_sig (PALT_exists_dual β).
  Proof.
    intros h. destruct β as [a|a]; simpl.
    - apply simplify_match_input in h. by subst.
    - apply simplify_match_output in h. by subst.
  Qed.

  #[global] Instance PALT_ExtAction : ExtAction PALT_Act := {|
    eqdec := PALT_Act_eqdec;
    countable := PALT_Act_countable;
    non_blocking := PALT_non_blocking;
    non_blocking_dec := PALT_non_blocking_dec;
    dual := ext_act_match;
    dual_dec := ext_act_match_dec;
    dual_blocks := λ _ _ nb _, match nb with end;
    duo_sym := ext_act_match_sym;
    exists_dual := PALT_exists_dual;
    unique_nb := PALT_unique_nb;
  |}.

  Lemma ext_act_match_det_t (μ ξ : PALT_Act) : ext_act_match μ ξ → μ = co_t ξ.
  Proof.
    destruct ξ as [a|a]; simpl; intros hm; apply ext_act_match_sym in hm.
    - apply simplify_match_input in hm. by subst.
    - apply simplify_match_output in hm. by subst.
  Qed.

  (** ** The LTS (Tables 3-4) *)

  Open Scope pal_scope.
  Inductive lts_step_t : term → Act PALT_Act → term → Prop :=
    (* AR1 *)
    | tar1 t E it ot :
        eval_in_tuple t = Some it → tuple_match it ot →
        lts_step_t (in( t ) • E) (ActExt (ActIn ot)) (subst_term (build_subst it ot) E)
    (* AR2 *)
    | tar2 t E it ot :
        eval_in_tuple t = Some it → tuple_match it ot →
        lts_step_t (read( t ) • E) (ActExt (ActIn ot))
          ((out( eot_to_tuple ot ) • 𝟘) ‖ (subst_term (build_subst it ot) E))
    (* AR3 *)
    | tar3 t ot :
        eval_out_tuple t = Some ot →
        lts_step_t (out( t ) • 𝟘) (ActExt (ActOut ot)) 𝟘
    (* AR4, + symmetric *)
    | tar4_l E1 E2 mu E1' : lts_step_t E1 (ActExt mu) E1' → lts_step_t (E1 □ E2) (ActExt mu) E1'
    | tar4_r E1 E2 mu E2' : lts_step_t E2 (ActExt mu) E2' → lts_step_t (E1 □ E2) (ActExt mu) E2'
    (* AR5, + symmetric *)
    | tar5_l E1 E2 mu E1' : lts_step_t E1 (ActExt mu) E1' → lts_step_t (E1 ‖ E2) (ActExt mu) (E1' ‖ E2)
    | tar5_r E1 E2 mu E2' : lts_step_t E2 (ActExt mu) E2' → lts_step_t (E1 ‖ E2) (ActExt mu) (E1 ‖ E2')
    (* AR6 *)
    | tar6 E1 E2 mu E1' : lts_step_t E1 (ActExt mu) E1' → lts_step_t (E1 ⌊ E2) (ActExt mu) (E1' ‖ E2)
    (* AR7 *)
    | tar7 be E1 E2 mu E1' :
        eval_bexp be = Some true → lts_step_t E1 (ActExt mu) E1' → lts_step_t (IF be THEN E1 ELSE E2) (ActExt mu) E1'
    (* AR8 *)
    | tar8 be E1 E2 mu E2' :
        eval_bexp be = Some false → lts_step_t E2 (ActExt mu) E2' → lts_step_t (IF be THEN E1 ELSE E2) (ActExt mu) E2'
    (* IR1 *)
    | tir1 : lts_step_t Ω τ Ω
    (* IR2 *)
    | tir2 X E : lts_step_t (rec X • E) τ (psubst X (rec X • E) E)
    (* IR3 *)
    | tir3 be E1 E2 E1' : eval_bexp be = Some true → lts_step_t E1 τ E1' → lts_step_t (IF be THEN E1 ELSE E2) τ E1'
    (* IR4 *)
    | tir4 be E1 E2 E2' : eval_bexp be = Some false → lts_step_t E2 τ E2' → lts_step_t (IF be THEN E1 ELSE E2) τ E2'
    (* IR5 *)
    | tir5 t E : E <> 𝟘 → lts_step_t (out( t ) • E) τ ((out( t ) • 𝟘) ‖ E)
    (* IR6 *)
    | tir6 E1 E2 : lts_step_t (eval( E1 ) • E2) τ (E1 ‖ E2)
    (* IR7 *)
    | tir7_l E1 E2 : lts_step_t (E1 ⊕ E2) τ E1
    | tir7_r E1 E2 : lts_step_t (E1 ⊕ E2) τ E2
    (* IR8, + symmetric *)
    | tir8_l E1 E2 E1' : lts_step_t E1 τ E1' → lts_step_t (E1 □ E2) τ (E1' □ E2)
    | tir8_r E1 E2 E2' : lts_step_t E2 τ E2' → lts_step_t (E1 □ E2) τ (E1 □ E2')
    (* IR9, + symmetric *)
    | tir9_l E1 E2 E1' : lts_step_t E1 τ E1' → lts_step_t (E1 ‖ E2) τ (E1' ‖ E2)
    | tir9_r E1 E2 E2' : lts_step_t E2 τ E2' → lts_step_t (E1 ‖ E2) τ (E1 ‖ E2')
    (* IR10, + symmetric *)
    | tir10_l E1 E2 E1' : lts_step_t E1 τ E1' → lts_step_t (E1 |ₖ E2) τ (E1' |ₖ E2)
    | tir10_r E1 E2 E2' : lts_step_t E2 τ E2' → lts_step_t (E1 |ₖ E2) τ (E1 |ₖ E2')
    (* IR11 *)
    | tir11 E1 E2 E1' : lts_step_t E1 τ E1' → lts_step_t (E1 ⌊ E2) τ (E1' ⌊ E2)
    (* IR12: synchronisation along dual labels *)
    | tir12 E1 E2 mu E1' E2' :
        lts_step_t E1 (ActExt mu) E1' → lts_step_t E2 (ActExt (co_t mu)) E2' →
        lts_step_t (E1 ‖ E2) τ (E1' ‖ E2')
    (* IR13 *)
    | tir13 E1 E2 mu E1' E2' :
        lts_step_t E1 (ActExt mu) E1' → lts_step_t E2 (ActExt (co_t mu)) E2' →
        lts_step_t (E1 |ₖ E2) τ (E1' ‖ E2').
  Close Scope pal_scope.

  (** ** Enumerating successors *)

  (** The outputs offered by a term. *)
  Fixpoint collect_out_t (E : term) : list eot :=
    match E with
    | t_out t t_nil =>
        match eval_out_tuple t with Some ot => [ot] | None => [] end
    | t_echoice E1 E2 => collect_out_t E1 ++ collect_out_t E2
    | t_par E1 E2 => collect_out_t E1 ++ collect_out_t E2
    | t_lmerge E1 E2 => collect_out_t E1
    | t_if be E1 E2 =>
        match eval_bexp be with
        | Some true => collect_out_t E1
        | Some false => collect_out_t E2
        | None => []
        end
    | _ => []
    end.

  Lemma out_step_in_collect_out_t E a E' :
    lts_step_t E (ActExt (ActOut a)) E' → In a (collect_out_t E).
  Proof.
    intros h. remember (ActExt (ActOut a)) as α eqn:eq.
    induction h; try discriminate eq; simpl.
    - injection eq as <-. match goal with hev : eval_out_tuple _ = Some _ |- _ => rewrite hev end.
      by left.
    - apply in_or_app. left. by apply IHh.
    - apply in_or_app. right. by apply IHh.
    - apply in_or_app. left. by apply IHh.
    - apply in_or_app. right. by apply IHh.
    - by apply IHh.
    - match goal with hb : eval_bexp _ = Some true |- _ => rewrite hb end. by apply IHh.
    - match goal with hb : eval_bexp _ = Some false |- _ => rewrite hb end. by apply IHh.
  Qed.

  Lemma collect_out_witnesses_t (E : term) (a : eot) :
    In a (collect_out_t E) → {E' | lts_step_t E (ActExt (ActOut a)) E'}.
  Proof.
    induction E; simpl; intros hin; try contradiction.
    - destruct E; simpl in hin; try contradiction.
      destruct (eval_out_tuple t) as [ot|] eqn:ev; [| contradiction].
      exists t_nil. destruct hin as [<- | []]. by apply tar3.
    - destruct (eval_bexp be) as [b|] eqn:hbe; [destruct b |]; simpl in hin; [| | contradiction].
      + destruct (IHE1 hin) as [E1' h1]. exists E1'. by eapply tar7.
      + destruct (IHE2 hin) as [E2' h2]. exists E2'. by eapply tar8.
    - destruct (in_dec (λ x y : eot, decide (x = y)) a (collect_out_t E1)) as [hin1|hnin1].
      + destruct (IHE1 hin1) as [E1' h1]. exists E1'. by eapply tar4_l.
      + assert (In a (collect_out_t E2)) as hin2 by (apply in_app_or in hin as [?|?]; [contradiction | done]).
        destruct (IHE2 hin2) as [E2' h2]. exists E2'. by eapply tar4_r.
    - destruct (in_dec (λ x y : eot, decide (x = y)) a (collect_out_t E1)) as [hin1|hnin1].
      + destruct (IHE1 hin1) as [E1' h1]. exists (t_par E1' E2). by eapply tar5_l.
      + assert (In a (collect_out_t E2)) as hin2 by (apply in_app_or in hin as [?|?]; [contradiction | done]).
        destruct (IHE2 hin2) as [E2' h2]. exists (t_par E1 E2'). by eapply tar5_r.
    - destruct (IHE1 hin) as [E1' h1]. exists (t_par E1' E2). by eapply tar6.
  Qed.

  Fixpoint all_steps_t (p : term) (α : Act PALT_Act) : list term :=
    match p with
    | t_nil => []
    | t_pvar _ => []
    | t_success => []
    | t_undef => match α with τ => [t_undef] | _ => [] end
    | t_rec X E => match α with τ => [psubst X (t_rec X E) E] | _ => [] end
    | t_out t E =>
        match α with
        | ActExt (ActOut ot) =>
            if bool_decide (E = t_nil) then
              match eval_out_tuple t with
              | Some ot' => if bool_decide (ot' = ot) then [t_nil] else []
              | None => []
              end
            else []
        | τ => if bool_decide (E <> t_nil) then [t_par (t_out t t_nil) E] else []
        | _ => []
        end
    | t_in t E =>
        match α with
        | ActExt (ActIn ot) =>
            match eval_in_tuple t with
            | Some it =>
                if tuple_match_b it ot
                then [subst_term (build_subst it ot) E] else []
            | None => []
            end
        | _ => []
        end
    | t_read t E =>
        match α with
        | ActExt (ActIn ot) =>
            match eval_in_tuple t with
            | Some it =>
                if tuple_match_b it ot
                then [t_par (t_out (eot_to_tuple ot) t_nil) (subst_term (build_subst it ot) E)]
                else []
            | None => []
            end
        | _ => []
        end
    | t_eval E1 E2 => match α with τ => [t_par E1 E2] | _ => [] end
    | t_if be E1 E2 =>
        match eval_bexp be with
        | Some true => all_steps_t E1 α
        | Some false => all_steps_t E2 α
        | None => []
        end
    | t_ichoice E1 E2 => match α with τ => [E1; E2] | _ => [] end
    | t_echoice E1 E2 =>
        match α with
        | τ => map (λ E1', t_echoice E1' E2) (all_steps_t E1 τ)
               ++ map (λ E2', t_echoice E1 E2') (all_steps_t E2 τ)
        | ActExt _ => all_steps_t E1 α ++ all_steps_t E2 α
        end
    | t_lmerge E1 E2 =>
        match α with
        | τ => map (λ E1', t_lmerge E1' E2) (all_steps_t E1 τ)
        | ActExt _ => map (λ E1', t_par E1' E2) (all_steps_t E1 α)
        end
    | t_cmerge E1 E2 =>
        match α with
        | τ =>
            map (λ E1', t_cmerge E1' E2) (all_steps_t E1 τ)
            ++ map (λ E2', t_cmerge E1 E2') (all_steps_t E2 τ)
            ++ flat_map (λ a,
                 flat_map (λ E1', map (λ E2', t_par E1' E2') (all_steps_t E2 (ActExt (ActIn a))))
                   (all_steps_t E1 (ActExt (ActOut a))))
                 (collect_out_t E1)
            ++ flat_map (λ a,
                 flat_map (λ E2', map (λ E1', t_par E1' E2') (all_steps_t E1 (ActExt (ActIn a))))
                   (all_steps_t E2 (ActExt (ActOut a))))
                 (collect_out_t E2)
        | ActExt _ => []
        end
    | t_par E1 E2 =>
        match α with
        | τ =>
            map (λ E1', t_par E1' E2) (all_steps_t E1 τ)
            ++ map (λ E2', t_par E1 E2') (all_steps_t E2 τ)
            ++ flat_map (λ a,
                 flat_map (λ E1', map (λ E2', t_par E1' E2') (all_steps_t E2 (ActExt (ActIn a))))
                   (all_steps_t E1 (ActExt (ActOut a))))
                 (collect_out_t E1)
            ++ flat_map (λ a,
                 flat_map (λ E2', map (λ E1', t_par E1' E2') (all_steps_t E1 (ActExt (ActIn a))))
                   (all_steps_t E2 (ActExt (ActOut a))))
                 (collect_out_t E2)
        | ActExt _ =>
            map (λ E1', t_par E1' E2) (all_steps_t E1 α)
            ++ map (λ E2', t_par E1 E2') (all_steps_t E2 α)
        end
    end.

  Lemma all_steps_t_sound p α q : In q (all_steps_t p α) → lts_step_t p α q.
  Proof.
    revert α q.
    induction p; intros α q hin; simpl in hin.
    - contradiction.
    - destruct α as [μ|]; [contradiction |]. destruct hin as [<- | []]. apply tir1.
    - destruct α as [[ot|ot]|].
      + contradiction.
      + case_bool_decide as hE; [subst | contradiction].
        destruct (eval_out_tuple t) as [ot'|] eqn:ev; [| contradiction].
        case_bool_decide as hb; [subst | contradiction].
        destruct hin as [<- | []]. by apply tar3.
      + case_bool_decide as hE; [| contradiction]. destruct hin as [<- | []]. by apply tir5.
    - destruct α as [[ot|ot]|]; try contradiction.
      destruct (eval_in_tuple t) as [it|] eqn:ev; [| contradiction].
      destruct (tuple_match_b it ot) eqn:hb; [| contradiction].
      destruct hin as [<- | []]. apply tar1; [done |]. by apply tuple_match_b_correct.
    - destruct α as [[ot|ot]|]; try contradiction.
      destruct (eval_in_tuple t) as [it|] eqn:ev; [| contradiction].
      destruct (tuple_match_b it ot) eqn:hb; [| contradiction].
      destruct hin as [<- | []]. apply tar2; [done |]. by apply tuple_match_b_correct.
    - destruct α as [μ|]; [contradiction |]. destruct hin as [<- | []]. apply tir6.
    - destruct (eval_bexp be) as [[]|] eqn:hbe; [| | contradiction]; destruct α as [μ|].
      + eapply tar7; [done | by apply IHp1].
      + eapply tir3; [done | by apply IHp1].
      + eapply tar8; [done | by apply IHp2].
      + eapply tir4; [done | by apply IHp2].
    - destruct α as [μ|]; [contradiction |]. destruct hin as [<- | [<- | []]]; [apply tir7_l | apply tir7_r].
    - destruct α as [μ|]; apply in_app_iff in hin as [hin | hin].
      + by apply tar4_l, IHp1.
      + by apply tar4_r, IHp2.
      + apply in_map_iff in hin as (E1' & <- & hin). by apply tir8_l, IHp1.
      + apply in_map_iff in hin as (E2' & <- & hin). by apply tir8_r, IHp2.
    - destruct α as [μ|].
      + apply in_app_iff in hin as [hin | hin].
        * apply in_map_iff in hin as (E1' & <- & hin). by apply tar5_l, IHp1.
        * apply in_map_iff in hin as (E2' & <- & hin). by apply tar5_r, IHp2.
      + apply in_app_iff in hin as [hin | hin];
          [| apply in_app_iff in hin as [hin | hin]; [| apply in_app_iff in hin as [hin | hin]]].
        * apply in_map_iff in hin as (E1' & <- & hin). by apply tir9_l, IHp1.
        * apply in_map_iff in hin as (E2' & <- & hin). by apply tir9_r, IHp2.
        * apply in_flat_map in hin as (a & ha & hin2).
          apply in_flat_map in hin2 as (E1' & hE1' & hin3).
          apply in_map_iff in hin3 as (E2' & <- & hE2').
          eapply (tir12 _ _ (ActOut a)); [by apply IHp1 | by apply IHp2].
        * apply in_flat_map in hin as (a & ha & hin2).
          apply in_flat_map in hin2 as (E2' & hE2' & hin3).
          apply in_map_iff in hin3 as (E1' & <- & hE1').
          eapply (tir12 _ _ (ActIn a)); [by apply IHp1 | by apply IHp2].
    - destruct α as [μ|]; apply in_map_iff in hin as (E1' & <- & hin).
      + by apply tar6, IHp1.
      + by apply tir11, IHp1.
    - destruct α as [μ|]; [contradiction |].
      apply in_app_iff in hin as [hin | hin];
        [| apply in_app_iff in hin as [hin | hin]; [| apply in_app_iff in hin as [hin | hin]]].
      + apply in_map_iff in hin as (E1' & <- & hin). by apply tir10_l, IHp1.
      + apply in_map_iff in hin as (E2' & <- & hin). by apply tir10_r, IHp2.
      + apply in_flat_map in hin as (a & ha & hin2).
        apply in_flat_map in hin2 as (E1' & hE1' & hin3).
        apply in_map_iff in hin3 as (E2' & <- & hE2').
        eapply (tir13 _ _ (ActOut a)); [by apply IHp1 | by apply IHp2].
      + apply in_flat_map in hin as (a & ha & hin2).
        apply in_flat_map in hin2 as (E2' & hE2' & hin3).
        apply in_map_iff in hin3 as (E1' & <- & hE1').
        eapply (tir13 _ _ (ActIn a)); [by apply IHp1 | by apply IHp2].
    - contradiction.
    - destruct α as [μ|]; [contradiction |]. destruct hin as [<- | []]. apply tir2.
    - contradiction.
  Qed.

  Lemma all_steps_t_complete p α q : lts_step_t p α q → In q (all_steps_t p α).
  Proof.
    induction 1; simpl.
    - match goal with hev : eval_in_tuple _ = Some _ |- _ => rewrite hev end.
      match goal with hm : tuple_match _ _ |- _ => apply tuple_match_b_correct in hm; rewrite hm end. by left.
    - match goal with hev : eval_in_tuple _ = Some _ |- _ => rewrite hev end.
      match goal with hm : tuple_match _ _ |- _ => apply tuple_match_b_correct in hm; rewrite hm end. by left.
    - try (rewrite bool_decide_true; [| done]).
      match goal with hev : eval_out_tuple _ = Some _ |- _ => rewrite hev end.
      rewrite bool_decide_true; [by left | done].
    - apply in_or_app. by left.
    - apply in_or_app. by right.
    - apply in_or_app. left. apply in_map_iff. by exists E1'.
    - apply in_or_app. right. apply in_map_iff. by exists E2'.
    - apply in_map_iff. by exists E1'.
    - match goal with hb : eval_bexp _ = Some true |- _ => by rewrite hb end.
    - match goal with hb : eval_bexp _ = Some false |- _ => by rewrite hb end.
    - by left.
    - by left.
    - match goal with hb : eval_bexp _ = Some true |- _ => by rewrite hb end.
    - match goal with hb : eval_bexp _ = Some false |- _ => by rewrite hb end.
    - rewrite bool_decide_true; [by left | done].
    - by left.
    - by left.
    - right. by left.
    - apply in_or_app. left. apply in_map_iff. by exists E1'.
    - apply in_or_app. right. apply in_map_iff. by exists E2'.
    - apply in_or_app. left. apply in_map_iff. by exists E1'.
    - apply in_or_app. right. apply in_or_app. left. apply in_map_iff. by exists E2'.
    - apply in_or_app. left. apply in_map_iff. by exists E1'.
    - apply in_or_app. right. apply in_or_app. left. apply in_map_iff. by exists E2'.
    - apply in_map_iff. by exists E1'.
    - destruct mu as [a|a].
      + pose proof (out_step_in_collect_out_t E2 a E2' ltac:(assumption)) as ha.
        apply in_or_app; right; apply in_or_app; right; apply in_or_app; right.
        apply in_flat_map. exists a. split; [done |].
        apply in_flat_map. exists E2'. split; [exact IHlts_step_t2 |].
        apply in_map_iff. exists E1'. split; [done | exact IHlts_step_t1].
      + pose proof (out_step_in_collect_out_t E1 a E1' ltac:(assumption)) as ha.
        apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
        apply in_flat_map. exists a. split; [done |].
        apply in_flat_map. exists E1'. split; [exact IHlts_step_t1 |].
        apply in_map_iff. exists E2'. split; [done | exact IHlts_step_t2].
    - destruct mu as [a|a].
      + pose proof (out_step_in_collect_out_t E2 a E2' ltac:(assumption)) as ha.
        apply in_or_app; right; apply in_or_app; right; apply in_or_app; right.
        apply in_flat_map. exists a. split; [done |].
        apply in_flat_map. exists E2'. split; [exact IHlts_step_t2 |].
        apply in_map_iff. exists E1'. split; [done | exact IHlts_step_t1].
      + pose proof (out_step_in_collect_out_t E1 a E1' ltac:(assumption)) as ha.
        apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
        apply in_flat_map. exists a. split; [done |].
        apply in_flat_map. exists E1'. split; [exact IHlts_step_t1 |].
        apply in_map_iff. exists E2'. split; [done | exact IHlts_step_t2].
  Qed.

  (** ** [gLts] instance *)

  Definition PALT_refuses (p : term) (α : Act PALT_Act) : Prop := all_steps_t p α = [].

  #[global] Instance PALT_step_dec p α q : Decision (lts_step_t p α q).
  Proof.
    destruct (in_dec term_eqdec q (all_steps_t p α)) as [hin|hnin].
    - left. by apply all_steps_t_sound.
    - right. intros h. by apply hnin, all_steps_t_complete.
  Defined.

  #[global] Instance PALT_refuses_dec p α : Decision (PALT_refuses p α).
  Proof. unfold PALT_refuses. destruct (all_steps_t p α); [left | right]; done. Defined.

  Definition PALT_refuses_spec1 p α : ¬ PALT_refuses p α → {q | lts_step_t p α q}.
  Proof.
    unfold PALT_refuses. intros hne.
    destruct (all_steps_t p α) as [|q l] eqn:e; [done |].
    exists q. apply all_steps_t_sound. rewrite e. by left.
  Defined.

  Definition PALT_refuses_spec2 p α : {q | lts_step_t p α q} → ¬ PALT_refuses p α.
  Proof.
    intros [q h] href. unfold PALT_refuses in href.
    apply all_steps_t_complete in h. by rewrite href in h.
  Defined.

  #[global] Instance PALT_gLts : gLts term PALT_ExtAction :=
    @MkgLts term PALT_Act PALT_ExtAction lts_step_t term_eqdec PALT_step_dec
      PALT_refuses PALT_refuses_dec PALT_refuses_spec1 PALT_refuses_spec2.

  (** ** [FiniteImagegLts]/[coFiniteImagegLts] *)

  #[global] Instance PALT_FiniteImagegLts : FiniteImagegLts term PALT_Act.
  Proof.
    unshelve econstructor.
    - exact term_countable.
    - intros p α. unfold dsig.
      eapply (in_list_finite (all_steps_t p α)).
      intros q hq%bool_decide_unpack. apply list_elem_of_In. by apply all_steps_t_complete.
  Defined.

  Lemma PALT_co_next_iff p α q :
    (∃ α', ext_act_match α' α ∧ lts_step_t p (ActExt α') q) ↔ lts_step_t p (ActExt (co_t α)) q.
  Proof.
    split.
    - intros (α' & hd & hl). apply ext_act_match_det_t in hd. by subst.
    - intros hl. exists (co_t α). split; [by destruct α | done].
  Qed.

  #[global] Instance PALT_co_next_states_decidable p α q :
    Decision (∃ α', ext_act_match α' α ∧ lts_step_t p (ActExt α') q).
  Proof.
    destruct (PALT_step_dec p (ActExt (co_t α)) q) as [hy|hn].
    - left. by apply PALT_co_next_iff.
    - right. intros hc. by apply hn, PALT_co_next_iff.
  Defined.

  #[global] Instance PALT_coFiniteImagegLts : coFiniteImagegLts term PALT_Act.
  Proof.
    unshelve econstructor.
    - exact term_countable.
    - intros p. unfold dsig.
      eapply (in_list_finite (all_steps_t p τ)).
      intros q hq%bool_decide_unpack. apply list_elem_of_In. by apply all_steps_t_complete.
    - intros p α. unfold dsig.
      eapply (in_list_finite (all_steps_t p (ActExt (co_t α)))).
      intros q hq%bool_decide_unpack. apply list_elem_of_In.
      apply all_steps_t_complete. by apply PALT_co_next_iff.
  Defined.

  (** ** [Prop_of_Inter term term PALT_Act ext_act_match] *)

  Definition PALT_essential_actions (p : term) : gset PALT_Act :=
    list_to_set (map ActOut (collect_out_t p)).

  Definition PALT_essential_action_spec p ξ :
    ξ ∈ PALT_essential_actions p → {p' | lts_step_t p (ActExt ξ) p'}.
  Proof.
    intros hmem. unfold PALT_essential_actions in hmem.
    apply elem_of_list_to_set, list_elem_of_In in hmem.
    destruct ξ as [a|a].
    - exfalso. apply in_map_iff in hmem as (x & heq & _). discriminate.
    - assert (In a (collect_out_t p)) as ha.
      { apply in_map_iff in hmem as (x & heq & hin). by injection heq as ->. }
      exact (collect_out_witnesses_t p a ha).
  Defined.

  Lemma PALT_essential_actions_spec_interact (p1 : term) μ1 p1' (p2 : term) μ2 p2' :
    lts_step_t p1 (ActExt μ1) p1' → lts_step_t p2 (ActExt μ2) p2' → ext_act_match μ1 μ2 →
    μ1 ∈ PALT_essential_actions p1 ∨ μ2 ∈ PALT_essential_actions p2.
  Proof.
    intros hl1 hl2 hinter. unfold PALT_essential_actions.
    destruct μ1 as [a|a].
    - right. apply ext_act_match_sym, ext_act_match_det_t in hinter. subst μ2.
      apply elem_of_list_to_set, list_elem_of_In, in_map_iff.
      exists a. split; [done | by eapply out_step_in_collect_out_t].
    - left. apply elem_of_list_to_set, list_elem_of_In, in_map_iff.
      exists a. split; [done | by eapply out_step_in_collect_out_t].
  Qed.

  Lemma PALT_co_inter_action_spec (μ ξ : PALT_Act) :
    ext_act_match μ ξ → μ ∈ ({[co_t ξ]} : gset PALT_Act).
  Proof. intros hx. apply ext_act_match_det_t in hx. subst. by apply elem_of_singleton_2. Qed.

  Lemma PALT_co_inter_action_spec' (ξ μ : PALT_Act) :
    ext_act_match ξ μ → μ ∈ ({[co_t ξ]} : gset PALT_Act).
  Proof. intros hx. apply ext_act_match_sym in hx. by apply PALT_co_inter_action_spec. Qed.

  #[global] Instance PALT_Prop_of_Inter : Prop_of_Inter term term PALT_Act ext_act_match := {|
    inter_dec := ext_act_match_dec;
    lts_essential_actions_left := PALT_essential_actions;
    lts_essential_action_spec_left := PALT_essential_action_spec;
    lts_essential_actions_right := PALT_essential_actions;
    lts_essential_action_spec_right := PALT_essential_action_spec;
    lts_essential_actions_spec_interact := PALT_essential_actions_spec_interact;
    lts_co_inter_action_left := λ ξ _, {[co_t ξ]};
    lts_co_inter_action_spec_left := λ _ _ ξ μ _ _ _ hinter, PALT_co_inter_action_spec μ ξ hinter;
    lts_co_inter_action_right := λ ξ _, {[co_t ξ]};
    lts_co_inter_action_spec_right := λ _ _ ξ μ _ _ _ hinter, PALT_co_inter_action_spec' ξ μ hinter;
  |}.
End PAL_T.
