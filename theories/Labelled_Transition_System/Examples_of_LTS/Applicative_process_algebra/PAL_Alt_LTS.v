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
From TestingTheory Require Import ActTau gLts FiniteImageLTS coFiniteImage InteractionBetweenLts
  InListPropHelper PAL_Syntax.

(* * PAL with alternative labels

   An LTS on the terms of [PAL_Syntax] whose τ-transitions are those of
   [Applicative_process_algebra] ([PAL_Alt_Tau.v]), with labels:
   - [AIn l] for an input: [l] pairs the received tuple [ltuple l] with the
     template of the pattern [ltemplate l] (the pattern with the names of its
     formal fields erased), field by field;
   - [AOut ot] for an output of the tuple [ot].
   Only the receiver knows the pattern: an output has a single label, and
   [AIn l] is dual to [AOut ot] when [ltuple l = ot]. The dual is not unique:
   [AOut ot] is dual to one input label per template matching [ot]. *)

Section PAL_Alt.
  Context (Val : Type) `{Countable Val}.

  Notation term := (term Val).
  Notation tuple := (tuple Val).
  Notation eot := (eot Val).
  Notation eit := (eit Val).
  Notation in_field := (in_field Val).
  Notation out_field := (out_field Val).

  (** ** Templates *)

  Inductive tfield := tf_formal | tf_val (v : Val) | tf_star.

  Definition template := list tfield.

  Definition tfield_of (f : in_field) : tfield :=
    match f with if_formal _ => tf_formal | if_val v => tf_val v | if_star => tf_star end.

  (** The template of an evaluated pattern. *)
  Definition template_of (it : eit) : template := map tfield_of it.

  #[global] Instance tfield_eqdec : EqDecision tfield.
  Proof. solve_decision. Defined.

  #[global] Instance tfield_countable : Countable tfield.
  Proof.
    refine (inj_countable'
      (λ f, match f with tf_formal => None | tf_star => Some None | tf_val v => Some (Some v) end)
      (λ o, match o with None => tf_formal | Some None => tf_star | Some (Some v) => tf_val v end)
      _).
    by intros [].
  Defined.

  (** ** Input labels: a tuple with a template matching it *)

  Inductive lfield := lf_formal (v : Val) | lf_val (v : Val) | lf_star.

  Definition label := list lfield.

  Definition lf_tfield (f : lfield) : tfield :=
    match f with lf_formal _ => tf_formal | lf_val v => tf_val v | lf_star => tf_star end.

  Definition lf_ofield (f : lfield) : out_field :=
    match f with lf_formal v | lf_val v => of_val v | lf_star => of_star end.

  Definition ltemplate (l : label) : template := map lf_tfield l.

  Definition ltuple (l : label) : eot := map lf_ofield l.

  #[global] Instance lfield_eqdec : EqDecision lfield.
  Proof. solve_decision. Defined.

  #[global] Instance lfield_countable : Countable lfield.
  Proof.
    refine (inj_countable'
      (λ f, match f with lf_formal v => inl v | lf_val v => inr (Some v) | lf_star => inr None end)
      (λ o, match o with inl v => lf_formal v | inr (Some v) => lf_val v | inr None => lf_star end)
      _).
    by intros [].
  Defined.

  (** A label is determined by its template and its tuple. *)
  Lemma label_inj l l' : ltemplate l = ltemplate l' → ltuple l = ltuple l' → l = l'.
  Proof.
    revert l'. induction l as [|f l IH]; intros [|f' l'] ht ho; try discriminate; [done |].
    cbn in ht, ho. injection ht as hf ht. injection ho as hf' ho. f_equal; [| by apply IH].
    destruct f, f'; cbn in *; congruence.
  Qed.

  (** The label of a pattern matching a tuple. *)
  Definition lfield_of (f : in_field) (o : out_field) : lfield :=
    match f, o with
    | if_formal _, of_val v => lf_formal v
    | _, of_val v => lf_val v
    | _, of_star => lf_star
    end.

  Definition label_of (it : eit) (ot : eot) : label := zip_with lfield_of it ot.

  Lemma label_of_spec it ot :
    tuple_match it ot → ltemplate (label_of it ot) = template_of it ∧ ltuple (label_of it ot) = ot.
  Proof.
    induction 1 as [|f o it ot hf _ [IH1 IH2]]; [done |].
    unfold ltemplate, ltuple, template_of in *. simpl. rewrite IH1, IH2.
    destruct hf; split; reflexivity.
  Qed.

  Lemma template_tuple_match it l : template_of it = ltemplate l → tuple_match it (ltuple l).
  Proof.
    revert l. induction it as [|f it IH]; intros [|g l] e; try discriminate; [constructor |].
    cbn in e. injection e as ef el. constructor; [| by apply IH].
    destruct f, g; cbn in ef; try discriminate; try (injection ef as ->); constructor.
  Qed.

  (** The finitely many input labels receiving a tuple. *)
  Fixpoint labels_of (ot : eot) : list label :=
    match ot with
    | [] => [[]]
    | of_star :: ot' => map (cons lf_star) (labels_of ot')
    | of_val v :: ot' => map (cons (lf_formal v)) (labels_of ot') ++ map (cons (lf_val v)) (labels_of ot')
    end.

  Lemma labels_of_spec l ot : In l (labels_of ot) ↔ ltuple l = ot.
  Proof.
    revert l. induction ot as [|[|v] ot IH]; intros l; simpl.
    - split; [by intros [<- | []] |]. destruct l; [by left | discriminate].
    - rewrite in_map_iff. split.
      + intros (l' & <- & hin). unfold ltuple in *. simpl. f_equal. by apply IH.
      + destruct l as [|[] l]; try discriminate. injection 1 as h. exists l. split; [done | by apply IH].
    - rewrite in_app_iff, !in_map_iff. split.
      + intros [(l' & <- & hin) | (l' & <- & hin)]; unfold ltuple in *; simpl; f_equal; by apply IH.
      + destruct l as [|[w|w|] l]; try discriminate; injection 1 as <- h.
        * left. exists l. split; [done | by apply IH].
        * right. exists l. split; [done | by apply IH].
  Qed.

  (** The label receiving [ot] with the template matching exactly [ot]. *)
  Definition exact_label (ot : eot) : label :=
    map (λ o, match o with of_val v => lf_val v | of_star => lf_star end) ot.

  Lemma ltuple_exact_label ot : ltuple (exact_label ot) = ot.
  Proof. induction ot as [|[|v] ot IH]; [done | ..]; unfold ltuple in *; simpl; by rewrite IH. Qed.

  (** ** Labels and dual *)

  Inductive PALA_Act := AIn (l : label) | AOut (ot : eot).

  #[global] Instance PALA_Act_eqdec : EqDecision PALA_Act.
  Proof. solve_decision. Defined.

  #[global] Instance PALA_Act_countable : Countable PALA_Act.
  Proof.
    refine (inj_countable'
      (λ a, match a with AIn l => inl l | AOut ot => inr ot end)
      (λ s, match s with inl l => AIn l | inr ot => AOut ot end)
      _).
    by intros [].
  Defined.

  Definition PALA_dual (μ η : PALA_Act) : Prop :=
    match μ, η with
    | AIn l, AOut ot | AOut ot, AIn l => ltuple l = ot
    | _, _ => False
    end.

  #[global] Instance PALA_dual_dec μ η : Decision (PALA_dual μ η).
  Proof. destruct μ, η; simpl; apply _. Defined.

  #[global] Instance PALA_dual_sym : Symmetric PALA_dual.
  Proof. by intros [] []. Qed.

  (** As in PAL, no action is non-blocking. *)
  Definition PALA_non_blocking (_ : PALA_Act) : Prop := False.

  #[global] Instance PALA_non_blocking_dec a : Decision (PALA_non_blocking a).
  Proof. right. intros []. Defined.

  Definition PALA_exists_dual (μ : PALA_Act) : {η | PALA_dual μ η}.
  Proof.
    destruct μ as [l|ot].
    - exists (AOut (ltuple l)). reflexivity.
    - exists (AIn (exact_label ot)). apply ltuple_exact_label.
  Defined.

  #[global] Instance PALA_ExtAction : ExtAction PALA_Act := {|
    eqdec := PALA_Act_eqdec;
    countable := PALA_Act_countable;
    non_blocking := PALA_non_blocking;
    non_blocking_dec := PALA_non_blocking_dec;
    dual := PALA_dual;
    dual_dec := PALA_dual_dec;
    dual_blocks := λ _ _ nb _, match nb with end;
    duo_sym := PALA_dual_sym;
    exists_dual := PALA_exists_dual;
  |}.

  (** The labels dual to a label. *)
  Definition co_labels (α : PALA_Act) : list PALA_Act :=
    match α with
    | AIn l => [AOut (ltuple l)]
    | AOut ot => map AIn (labels_of ot)
    end.

  Lemma co_labels_spec α α' : In α' (co_labels α) ↔ PALA_dual α' α.
  Proof.
    destruct α as [l|ot]; simpl.
    - split; [by intros [<- | []] |]. destruct α' as [l'|ot']; simpl; [done |]. intros <-. by left.
    - rewrite in_map_iff. split.
      + intros (l & <- & hl). simpl. by apply labels_of_spec.
      + destruct α' as [l|ot']; simpl; [| done]. intros e. exists l. split; [done | by apply labels_of_spec].
  Qed.

  (** ** The LTS (Tables 3-4, with alternative labels) *)

  Open Scope pal_scope.
  Inductive lts_step_a : term → Act PALA_Act → term → Prop :=
    (* AR1 *)
    | aar1 t E it l :
        eval_in_tuple t = Some it → template_of it = ltemplate l →
        lts_step_a (in( t ) • E) (ActExt (AIn l)) (subst_term (build_subst it (ltuple l)) E)
    (* AR2 *)
    | aar2 t E it l :
        eval_in_tuple t = Some it → template_of it = ltemplate l →
        lts_step_a (read( t ) • E) (ActExt (AIn l))
          ((out( eot_to_tuple (ltuple l) ) • 𝟘) ‖ (subst_term (build_subst it (ltuple l)) E))
    (* AR3 *)
    | aar3 t ot :
        eval_out_tuple t = Some ot →
        lts_step_a (out( t ) • 𝟘) (ActExt (AOut ot)) 𝟘
    (* AR4, + symmetric *)
    | aar4_l E1 E2 mu E1' : lts_step_a E1 (ActExt mu) E1' → lts_step_a (E1 □ E2) (ActExt mu) E1'
    | aar4_r E1 E2 mu E2' : lts_step_a E2 (ActExt mu) E2' → lts_step_a (E1 □ E2) (ActExt mu) E2'
    (* AR5, + symmetric *)
    | aar5_l E1 E2 mu E1' : lts_step_a E1 (ActExt mu) E1' → lts_step_a (E1 ‖ E2) (ActExt mu) (E1' ‖ E2)
    | aar5_r E1 E2 mu E2' : lts_step_a E2 (ActExt mu) E2' → lts_step_a (E1 ‖ E2) (ActExt mu) (E1 ‖ E2')
    (* AR6 *)
    | aar6 E1 E2 mu E1' : lts_step_a E1 (ActExt mu) E1' → lts_step_a (E1 ⌊ E2) (ActExt mu) (E1' ‖ E2)
    (* AR7 *)
    | aar7 be E1 E2 mu E1' :
        eval_bexp be = Some true → lts_step_a E1 (ActExt mu) E1' → lts_step_a (IF be THEN E1 ELSE E2) (ActExt mu) E1'
    (* AR8 *)
    | aar8 be E1 E2 mu E2' :
        eval_bexp be = Some false → lts_step_a E2 (ActExt mu) E2' → lts_step_a (IF be THEN E1 ELSE E2) (ActExt mu) E2'
    (* IR1 *)
    | air1 : lts_step_a Ω τ Ω
    (* IR2 *)
    | air2 X E : lts_step_a (rec X • E) τ (psubst X (rec X • E) E)
    (* IR3 *)
    | air3 be E1 E2 E1' : eval_bexp be = Some true → lts_step_a E1 τ E1' → lts_step_a (IF be THEN E1 ELSE E2) τ E1'
    (* IR4 *)
    | air4 be E1 E2 E2' : eval_bexp be = Some false → lts_step_a E2 τ E2' → lts_step_a (IF be THEN E1 ELSE E2) τ E2'
    (* IR5 *)
    | air5 t E : E <> 𝟘 → lts_step_a (out( t ) • E) τ ((out( t ) • 𝟘) ‖ E)
    (* IR6 *)
    | air6 E1 E2 : lts_step_a (eval( E1 ) • E2) τ (E1 ‖ E2)
    (* IR7 *)
    | air7_l E1 E2 : lts_step_a (E1 ⊕ E2) τ E1
    | air7_r E1 E2 : lts_step_a (E1 ⊕ E2) τ E2
    (* IR8, + symmetric *)
    | air8_l E1 E2 E1' : lts_step_a E1 τ E1' → lts_step_a (E1 □ E2) τ (E1' □ E2)
    | air8_r E1 E2 E2' : lts_step_a E2 τ E2' → lts_step_a (E1 □ E2) τ (E1 □ E2')
    (* IR9, + symmetric *)
    | air9_l E1 E2 E1' : lts_step_a E1 τ E1' → lts_step_a (E1 ‖ E2) τ (E1' ‖ E2)
    | air9_r E1 E2 E2' : lts_step_a E2 τ E2' → lts_step_a (E1 ‖ E2) τ (E1 ‖ E2')
    (* IR10, + symmetric *)
    | air10_l E1 E2 E1' : lts_step_a E1 τ E1' → lts_step_a (E1 |ₖ E2) τ (E1' |ₖ E2)
    | air10_r E1 E2 E2' : lts_step_a E2 τ E2' → lts_step_a (E1 |ₖ E2) τ (E1 |ₖ E2')
    (* IR11 *)
    | air11 E1 E2 E1' : lts_step_a E1 τ E1' → lts_step_a (E1 ⌊ E2) τ (E1' ⌊ E2)
    (* IR12: synchronisation along dual labels *)
    | air12 E1 E2 mu1 mu2 E1' E2' :
        lts_step_a E1 (ActExt mu1) E1' → lts_step_a E2 (ActExt mu2) E2' → PALA_dual mu1 mu2 →
        lts_step_a (E1 ‖ E2) τ (E1' ‖ E2')
    (* IR13 *)
    | air13 E1 E2 mu1 mu2 E1' E2' :
        lts_step_a E1 (ActExt mu1) E1' → lts_step_a E2 (ActExt mu2) E2' → PALA_dual mu1 mu2 →
        lts_step_a (E1 |ₖ E2) τ (E1' ‖ E2').
  Close Scope pal_scope.

  (** ** Enumerating successors *)

  (** The outputs offered by a term. *)
  Fixpoint collect_out_a (E : term) : list eot :=
    match E with
    | t_out t t_nil =>
        match eval_out_tuple t with Some ot => [ot] | None => [] end
    | t_echoice E1 E2 => collect_out_a E1 ++ collect_out_a E2
    | t_par E1 E2 => collect_out_a E1 ++ collect_out_a E2
    | t_lmerge E1 E2 => collect_out_a E1
    | t_if be E1 E2 =>
        match eval_bexp be with
        | Some true => collect_out_a E1
        | Some false => collect_out_a E2
        | None => []
        end
    | _ => []
    end.

  Lemma out_step_in_collect_out_a E a E' :
    lts_step_a E (ActExt (AOut a)) E' → In a (collect_out_a E).
  Proof.
    intros h. remember (ActExt (AOut a)) as α eqn:eq.
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

  Lemma collect_out_witnesses_a (E : term) (a : eot) :
    In a (collect_out_a E) → {E' | lts_step_a E (ActExt (AOut a)) E'}.
  Proof.
    induction E; simpl; intros hin; try contradiction.
    - destruct E; simpl in hin; try contradiction.
      destruct (eval_out_tuple t) as [ot|] eqn:ev; [| contradiction].
      exists t_nil. destruct hin as [<- | []]. by apply aar3.
    - destruct (eval_bexp be) as [b|] eqn:hbe; [destruct b |]; simpl in hin; [| | contradiction].
      + destruct (IHE1 hin) as [E1' h1]. exists E1'. by eapply aar7.
      + destruct (IHE2 hin) as [E2' h2]. exists E2'. by eapply aar8.
    - destruct (in_dec (λ x y : eot, decide (x = y)) a (collect_out_a E1)) as [hin1|hnin1].
      + destruct (IHE1 hin1) as [E1' h1]. exists E1'. by eapply aar4_l.
      + assert (In a (collect_out_a E2)) as hin2 by (apply in_app_or in hin as [?|?]; [contradiction | done]).
        destruct (IHE2 hin2) as [E2' h2]. exists E2'. by eapply aar4_r.
    - destruct (in_dec (λ x y : eot, decide (x = y)) a (collect_out_a E1)) as [hin1|hnin1].
      + destruct (IHE1 hin1) as [E1' h1]. exists (t_par E1' E2). by eapply aar5_l.
      + assert (In a (collect_out_a E2)) as hin2 by (apply in_app_or in hin as [?|?]; [contradiction | done]).
        destruct (IHE2 hin2) as [E2' h2]. exists (t_par E1 E2'). by eapply aar5_r.
    - destruct (IHE1 hin) as [E1' h1]. exists (t_par E1' E2). by eapply aar6.
  Qed.

  Fixpoint all_steps_a (p : term) (α : Act PALA_Act) : list term :=
    match p with
    | t_nil => []
    | t_pvar _ => []
    | t_success => []
    | t_undef => match α with τ => [t_undef] | _ => [] end
    | t_rec X E => match α with τ => [psubst X (t_rec X E) E] | _ => [] end
    | t_out t E =>
        match α with
        | ActExt (AOut ot) =>
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
        | ActExt (AIn l) =>
            match eval_in_tuple t with
            | Some it =>
                if bool_decide (template_of it = ltemplate l)
                then [subst_term (build_subst it (ltuple l)) E] else []
            | None => []
            end
        | _ => []
        end
    | t_read t E =>
        match α with
        | ActExt (AIn l) =>
            match eval_in_tuple t with
            | Some it =>
                if bool_decide (template_of it = ltemplate l)
                then [t_par (t_out (eot_to_tuple (ltuple l)) t_nil) (subst_term (build_subst it (ltuple l)) E)]
                else []
            | None => []
            end
        | _ => []
        end
    | t_eval E1 E2 => match α with τ => [t_par E1 E2] | _ => [] end
    | t_if be E1 E2 =>
        match eval_bexp be with
        | Some true => all_steps_a E1 α
        | Some false => all_steps_a E2 α
        | None => []
        end
    | t_ichoice E1 E2 => match α with τ => [E1; E2] | _ => [] end
    | t_echoice E1 E2 =>
        match α with
        | τ => map (λ E1', t_echoice E1' E2) (all_steps_a E1 τ)
               ++ map (λ E2', t_echoice E1 E2') (all_steps_a E2 τ)
        | ActExt _ => all_steps_a E1 α ++ all_steps_a E2 α
        end
    | t_lmerge E1 E2 =>
        match α with
        | τ => map (λ E1', t_lmerge E1' E2) (all_steps_a E1 τ)
        | ActExt _ => map (λ E1', t_par E1' E2) (all_steps_a E1 α)
        end
    | t_cmerge E1 E2 =>
        match α with
        | τ =>
            map (λ E1', t_cmerge E1' E2) (all_steps_a E1 τ)
            ++ map (λ E2', t_cmerge E1 E2') (all_steps_a E2 τ)
            ++ flat_map (λ a,
                 flat_map (λ E1', map (λ E2', t_par E1' E2')
                                    (flat_map (λ l, all_steps_a E2 (ActExt (AIn l))) (labels_of a)))
                   (all_steps_a E1 (ActExt (AOut a))))
                 (collect_out_a E1)
            ++ flat_map (λ a,
                 flat_map (λ E2', map (λ E1', t_par E1' E2')
                                    (flat_map (λ l, all_steps_a E1 (ActExt (AIn l))) (labels_of a)))
                   (all_steps_a E2 (ActExt (AOut a))))
                 (collect_out_a E2)
        | ActExt _ => []
        end
    | t_par E1 E2 =>
        match α with
        | τ =>
            map (λ E1', t_par E1' E2) (all_steps_a E1 τ)
            ++ map (λ E2', t_par E1 E2') (all_steps_a E2 τ)
            ++ flat_map (λ a,
                 flat_map (λ E1', map (λ E2', t_par E1' E2')
                                    (flat_map (λ l, all_steps_a E2 (ActExt (AIn l))) (labels_of a)))
                   (all_steps_a E1 (ActExt (AOut a))))
                 (collect_out_a E1)
            ++ flat_map (λ a,
                 flat_map (λ E2', map (λ E1', t_par E1' E2')
                                    (flat_map (λ l, all_steps_a E1 (ActExt (AIn l))) (labels_of a)))
                   (all_steps_a E2 (ActExt (AOut a))))
                 (collect_out_a E2)
        | ActExt _ =>
            map (λ E1', t_par E1' E2) (all_steps_a E1 α)
            ++ map (λ E2', t_par E1 E2') (all_steps_a E2 α)
        end
    end.

  Lemma all_steps_a_sound p α q : In q (all_steps_a p α) → lts_step_a p α q.
  Proof.
    revert α q.
    induction p; intros α q hin; simpl in hin.
    - contradiction.
    - destruct α as [μ|]; [contradiction |]. destruct hin as [<- | []]. apply air1.
    - destruct α as [[l|ot]|].
      + contradiction.
      + case_bool_decide as hE; [subst | contradiction].
        destruct (eval_out_tuple t) as [ot'|] eqn:ev; [| contradiction].
        case_bool_decide as hb; [subst | contradiction].
        destruct hin as [<- | []]. by apply aar3.
      + case_bool_decide as hE; [| contradiction]. destruct hin as [<- | []]. by apply air5.
    - destruct α as [[l|ot]|]; try contradiction.
      destruct (eval_in_tuple t) as [it|] eqn:ev; [| contradiction].
      case_bool_decide as hb; [| contradiction].
      destruct hin as [<- | []]. by apply aar1.
    - destruct α as [[l|ot]|]; try contradiction.
      destruct (eval_in_tuple t) as [it|] eqn:ev; [| contradiction].
      case_bool_decide as hb; [| contradiction].
      destruct hin as [<- | []]. by apply aar2.
    - destruct α as [μ|]; [contradiction |]. destruct hin as [<- | []]. apply air6.
    - destruct (eval_bexp be) as [[]|] eqn:hbe; [| | contradiction]; destruct α as [μ|].
      + eapply aar7; [done | by apply IHp1].
      + eapply air3; [done | by apply IHp1].
      + eapply aar8; [done | by apply IHp2].
      + eapply air4; [done | by apply IHp2].
    - destruct α as [μ|]; [contradiction |]. destruct hin as [<- | [<- | []]]; [apply air7_l | apply air7_r].
    - destruct α as [μ|]; apply in_app_iff in hin as [hin | hin].
      + by apply aar4_l, IHp1.
      + by apply aar4_r, IHp2.
      + apply in_map_iff in hin as (E1' & <- & hin). by apply air8_l, IHp1.
      + apply in_map_iff in hin as (E2' & <- & hin). by apply air8_r, IHp2.
    - destruct α as [μ|].
      + apply in_app_iff in hin as [hin | hin].
        * apply in_map_iff in hin as (E1' & <- & hin). by apply aar5_l, IHp1.
        * apply in_map_iff in hin as (E2' & <- & hin). by apply aar5_r, IHp2.
      + apply in_app_iff in hin as [hin | hin];
          [| apply in_app_iff in hin as [hin | hin]; [| apply in_app_iff in hin as [hin | hin]]].
        * apply in_map_iff in hin as (E1' & <- & hin). by apply air9_l, IHp1.
        * apply in_map_iff in hin as (E2' & <- & hin). by apply air9_r, IHp2.
        * apply in_flat_map in hin as (a & ha & hin2).
          apply in_flat_map in hin2 as (E1' & hE1' & hin3).
          apply in_map_iff in hin3 as (E2' & <- & hE2').
          apply in_flat_map in hE2' as (l & hl & hE2'). apply labels_of_spec in hl.
          eapply (air12 _ _ (AOut a) (AIn l)); [by apply IHp1 | by apply IHp2 | exact hl].
        * apply in_flat_map in hin as (a & ha & hin2).
          apply in_flat_map in hin2 as (E2' & hE2' & hin3).
          apply in_map_iff in hin3 as (E1' & <- & hE1').
          apply in_flat_map in hE1' as (l & hl & hE1'). apply labels_of_spec in hl.
          eapply (air12 _ _ (AIn l) (AOut a)); [by apply IHp1 | by apply IHp2 | exact hl].
    - destruct α as [μ|]; apply in_map_iff in hin as (E1' & <- & hin).
      + by apply aar6, IHp1.
      + by apply air11, IHp1.
    - destruct α as [μ|]; [contradiction |].
      apply in_app_iff in hin as [hin | hin];
        [| apply in_app_iff in hin as [hin | hin]; [| apply in_app_iff in hin as [hin | hin]]].
      + apply in_map_iff in hin as (E1' & <- & hin). by apply air10_l, IHp1.
      + apply in_map_iff in hin as (E2' & <- & hin). by apply air10_r, IHp2.
      + apply in_flat_map in hin as (a & ha & hin2).
        apply in_flat_map in hin2 as (E1' & hE1' & hin3).
        apply in_map_iff in hin3 as (E2' & <- & hE2').
        apply in_flat_map in hE2' as (l & hl & hE2'). apply labels_of_spec in hl.
        eapply (air13 _ _ (AOut a) (AIn l)); [by apply IHp1 | by apply IHp2 | exact hl].
      + apply in_flat_map in hin as (a & ha & hin2).
        apply in_flat_map in hin2 as (E2' & hE2' & hin3).
        apply in_map_iff in hin3 as (E1' & <- & hE1').
        apply in_flat_map in hE1' as (l & hl & hE1'). apply labels_of_spec in hl.
        eapply (air13 _ _ (AIn l) (AOut a)); [by apply IHp1 | by apply IHp2 | exact hl].
    - contradiction.
    - destruct α as [μ|]; [contradiction |]. destruct hin as [<- | []]. apply air2.
    - contradiction.
  Qed.

  Lemma all_steps_a_complete p α q : lts_step_a p α q → In q (all_steps_a p α).
  Proof.
    induction 1; simpl.
    - match goal with hev : eval_in_tuple _ = Some _ |- _ => rewrite hev end.
      rewrite bool_decide_true; [by left | done].
    - match goal with hev : eval_in_tuple _ = Some _ |- _ => rewrite hev end.
      rewrite bool_decide_true; [by left | done].
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
    - destruct mu1 as [l1|a1], mu2 as [l2|a2]; simpl in *; try contradiction.
      + pose proof (out_step_in_collect_out_a E2 a2 E2' ltac:(assumption)) as ha.
        apply in_or_app; right; apply in_or_app; right; apply in_or_app; right.
        apply in_flat_map. exists a2. split; [done |].
        apply in_flat_map. exists E2'. split; [exact IHlts_step_a2 |].
        apply in_map_iff. exists E1'. split; [done |].
        apply in_flat_map. exists l1. split; [by apply labels_of_spec | exact IHlts_step_a1].
      + pose proof (out_step_in_collect_out_a E1 a1 E1' ltac:(assumption)) as ha.
        apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
        apply in_flat_map. exists a1. split; [done |].
        apply in_flat_map. exists E1'. split; [exact IHlts_step_a1 |].
        apply in_map_iff. exists E2'. split; [done |].
        apply in_flat_map. exists l2. split; [by apply labels_of_spec | exact IHlts_step_a2].
    - destruct mu1 as [l1|a1], mu2 as [l2|a2]; simpl in *; try contradiction.
      + pose proof (out_step_in_collect_out_a E2 a2 E2' ltac:(assumption)) as ha.
        apply in_or_app; right; apply in_or_app; right; apply in_or_app; right.
        apply in_flat_map. exists a2. split; [done |].
        apply in_flat_map. exists E2'. split; [exact IHlts_step_a2 |].
        apply in_map_iff. exists E1'. split; [done |].
        apply in_flat_map. exists l1. split; [by apply labels_of_spec | exact IHlts_step_a1].
      + pose proof (out_step_in_collect_out_a E1 a1 E1' ltac:(assumption)) as ha.
        apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
        apply in_flat_map. exists a1. split; [done |].
        apply in_flat_map. exists E1'. split; [exact IHlts_step_a1 |].
        apply in_map_iff. exists E2'. split; [done |].
        apply in_flat_map. exists l2. split; [by apply labels_of_spec | exact IHlts_step_a2].
  Qed.

  (** ** [gLts] instance *)

  Definition PALA_refuses (p : term) (α : Act PALA_Act) : Prop := all_steps_a p α = [].

  #[global] Instance PALA_step_dec p α q : Decision (lts_step_a p α q).
  Proof.
    destruct (in_dec term_eqdec q (all_steps_a p α)) as [hin|hnin].
    - left. by apply all_steps_a_sound.
    - right. intros h. by apply hnin, all_steps_a_complete.
  Defined.

  #[global] Instance PALA_refuses_dec p α : Decision (PALA_refuses p α).
  Proof. unfold PALA_refuses. destruct (all_steps_a p α); [left | right]; done. Defined.

  Definition PALA_refuses_spec1 p α : ¬ PALA_refuses p α → {q | lts_step_a p α q}.
  Proof.
    unfold PALA_refuses. intros hne.
    destruct (all_steps_a p α) as [|q l] eqn:e; [done |].
    exists q. apply all_steps_a_sound. rewrite e. by left.
  Defined.

  Definition PALA_refuses_spec2 p α : {q | lts_step_a p α q} → ¬ PALA_refuses p α.
  Proof.
    intros [q h] href. unfold PALA_refuses in href.
    apply all_steps_a_complete in h. by rewrite href in h.
  Defined.

  #[global] Instance PALA_gLts : gLts term PALA_ExtAction :=
    @MkgLts term PALA_Act PALA_ExtAction lts_step_a term_eqdec PALA_step_dec
      PALA_refuses PALA_refuses_dec PALA_refuses_spec1 PALA_refuses_spec2.

  (** ** [FiniteImagegLts]/[coFiniteImagegLts] *)

  #[global] Instance PALA_FiniteImagegLts : FiniteImagegLts term PALA_Act.
  Proof.
    unshelve econstructor.
    - exact term_countable.
    - intros p α. unfold dsig.
      eapply (in_list_finite (all_steps_a p α)).
      intros q hq%bool_decide_unpack. apply list_elem_of_In. by apply all_steps_a_complete.
  Defined.

  Definition co_next_a (p : term) (α : PALA_Act) : list term :=
    flat_map (λ α', all_steps_a p (ActExt α')) (co_labels α).

  Lemma co_next_a_spec p α q :
    In q (co_next_a p α) ↔ ∃ α', PALA_dual α' α ∧ lts_step_a p (ActExt α') q.
  Proof.
    unfold co_next_a. rewrite in_flat_map. split.
    - intros (α' & hα' & hq). exists α'. split; [by apply co_labels_spec | by apply all_steps_a_sound].
    - intros (α' & hd & hs). exists α'. split; [by apply co_labels_spec | by apply all_steps_a_complete].
  Qed.

  #[global] Instance PALA_co_next_states_decidable p α q :
    Decision (∃ α', PALA_dual α' α ∧ lts_step_a p (ActExt α') q).
  Proof.
    destruct (in_dec term_eqdec q (co_next_a p α)) as [hin|hnin].
    - left. by apply co_next_a_spec.
    - right. intros hc. by apply hnin, co_next_a_spec.
  Defined.

  #[global] Instance PALA_coFiniteImagegLts : coFiniteImagegLts term PALA_Act.
  Proof.
    unshelve econstructor.
    - exact term_countable.
    - intros p. unfold dsig.
      eapply (in_list_finite (all_steps_a p τ)).
      intros q hq%bool_decide_unpack. apply list_elem_of_In. by apply all_steps_a_complete.
    - intros p α. unfold dsig.
      eapply (in_list_finite (co_next_a p α)).
      intros q hq%bool_decide_unpack. apply list_elem_of_In. by apply co_next_a_spec.
  Defined.

  (** ** [Prop_of_Inter term term PALA_Act PALA_dual] *)

  Definition PALA_essential_actions (p : term) : gset PALA_Act :=
    list_to_set (map AOut (collect_out_a p)).

  Definition PALA_essential_action_spec p ξ :
    ξ ∈ PALA_essential_actions p → {p' | lts_step_a p (ActExt ξ) p'}.
  Proof.
    intros hmem. unfold PALA_essential_actions in hmem.
    apply elem_of_list_to_set, list_elem_of_In in hmem.
    destruct ξ as [l|a].
    - exfalso. apply in_map_iff in hmem as (x & heq & _). discriminate.
    - assert (In a (collect_out_a p)) as ha.
      { apply in_map_iff in hmem as (x & heq & hin). by injection heq as ->. }
      exact (collect_out_witnesses_a p a ha).
  Defined.

  Lemma PALA_essential_actions_spec_interact (p1 : term) μ1 p1' (p2 : term) μ2 p2' :
    lts_step_a p1 (ActExt μ1) p1' → lts_step_a p2 (ActExt μ2) p2' → PALA_dual μ1 μ2 →
    μ1 ∈ PALA_essential_actions p1 ∨ μ2 ∈ PALA_essential_actions p2.
  Proof.
    intros hl1 hl2 hinter. unfold PALA_essential_actions.
    destruct μ1 as [l1|a1], μ2 as [l2|a2]; simpl in hinter; try contradiction.
    - right. apply elem_of_list_to_set, list_elem_of_In, in_map_iff.
      exists a2. split; [done | by eapply out_step_in_collect_out_a].
    - left. apply elem_of_list_to_set, list_elem_of_In, in_map_iff.
      exists a1. split; [done | by eapply out_step_in_collect_out_a].
  Qed.

  Lemma PALA_co_inter_action_spec (μ ξ : PALA_Act) :
    PALA_dual μ ξ → μ ∈ (list_to_set (co_labels ξ) : gset PALA_Act).
  Proof. intros hx. apply elem_of_list_to_set, list_elem_of_In. by apply co_labels_spec. Qed.

  #[global] Instance PALA_Prop_of_Inter : Prop_of_Inter term term PALA_Act PALA_dual := {|
    inter_dec := PALA_dual_dec;
    lts_essential_actions_left := PALA_essential_actions;
    lts_essential_action_spec_left := PALA_essential_action_spec;
    lts_essential_actions_right := PALA_essential_actions;
    lts_essential_action_spec_right := PALA_essential_action_spec;
    lts_essential_actions_spec_interact := PALA_essential_actions_spec_interact;
    lts_co_inter_action_left := λ ξ _, list_to_set (co_labels ξ);
    lts_co_inter_action_spec_left := λ _ _ ξ μ _ _ _ hinter, PALA_co_inter_action_spec μ ξ hinter;
    lts_co_inter_action_right := λ ξ _, list_to_set (co_labels ξ);
    lts_co_inter_action_spec_right := λ _ _ ξ μ _ _ _ hinter,
      PALA_co_inter_action_spec μ ξ (PALA_dual_sym _ _ hinter);
  |}.
End PAL_Alt.
