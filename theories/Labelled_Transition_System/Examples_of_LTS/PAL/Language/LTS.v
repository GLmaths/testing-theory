(* begin hide *)
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
(* end hide *)

(* begin hide *)
From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base tactics countable option list gmap.
From TestingTheory Require Import ActTau gLts FiniteImageLTS coFiniteImage InteractionBetweenLts
  InListPropHelper PAL.Language.Syntax.
(* * PAL with alternative labels

   An LTS on the terms of [PAL.Language.Syntax] whose τ-transitions are those of
   [PAL.Language.Paper_LTS] ([PAL.Language.Paper_Correspondence]), with labels:
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

  (* ** Templates *)

  Inductive tfield := tf_formal | tf_val (v : Val) | tf_star.

  Definition template := list tfield.

  Definition tfield_of (f : in_field) : tfield :=
    match f with if_formal _ => tf_formal | if_val v => tf_val v | if_star => tf_star end.

  (* The template of an evaluated pattern. *)
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

  (* ** Input labels: a tuple with a template matching it *)

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

  (* A label is determined by its template and its tuple. *)
  Lemma label_inj l l' : ltemplate l = ltemplate l' → ltuple l = ltuple l' → l = l'.
  Proof.
    revert l'. induction l as [|f l IH]; intros [|f' l'] ht ho; try discriminate; [done |].
    cbn in ht, ho. injection ht as hf ht. injection ho as hf' ho. f_equal; [| by apply IH].
    destruct f, f'; cbn in *; congruence.
  Qed.

  (* The label of a pattern matching a tuple. *)
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

  (* The finitely many input labels receiving a tuple. *)
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

  (* The label receiving [ot] with the template matching exactly [ot]. *)
  Definition exact_label (ot : eot) : label :=
    map (λ o, match o with of_val v => lf_val v | of_star => lf_star end) ot.

  Lemma ltuple_exact_label ot : ltuple (exact_label ot) = ot.
  Proof. induction ot as [|[|v] ot IH]; [done | ..]; unfold ltuple in *; simpl; by rewrite IH. Qed.

  (* ** Labels and dual *)

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

  (* As in PAL, no action is non-blocking. *)
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

  (* The labels dual to a label. *)
  Definition co_labels (𝜆 : PALA_Act) : list PALA_Act :=
    match 𝜆 with
    | AIn l => [AOut (ltuple l)]
    | AOut ot => map AIn (labels_of ot)
    end.

  Lemma co_labels_spec 𝜆 𝜆' : In 𝜆' (co_labels 𝜆) ↔ PALA_dual 𝜆' 𝜆.
  Proof.
    destruct 𝜆 as [l|ot]; simpl.
    - split; [by intros [<- | []] |]. destruct 𝜆' as [l'|ot']; simpl; [done |]. intros <-. by left.
    - rewrite in_map_iff. split.
      + intros (l & <- & hl). simpl. by apply labels_of_spec.
      + destruct 𝜆' as [l|ot']; simpl; [| done]. intros e. exists l. split; [done | by apply labels_of_spec].
  Qed.

  (* ** The LTS (Tables 3-4, with alternative labels) *)

  Open Scope pal_scope.
  Inductive lts_step_a : term → Labels PALA_Act → term → Prop :=
    (* AR1 *)
    | aar1 t E it l :
        eval_in_tuple t = Some it → template_of it = ltemplate l →
        lts_step_a (in( t ) • E) (ActExt (AIn l)) (subst_term (build_subst it (ltuple l)) E)
    (* AR2 *)
    | aar2 t E it l :
        eval_in_tuple t = Some it → template_of it = ltemplate l →
        lts_step_a (read( t ) • E) (ActExt (AIn l))
          ((out( eot_to_tuple (ltuple l) ) • 𝟘) │ (subst_term (build_subst it (ltuple l)) E))
    (* AR3 *)
    | aar3 t ot :
        eval_out_tuple t = Some ot →
        lts_step_a (out( t ) • 𝟘) (ActExt (AOut ot)) 𝟘
    (* AR4, + symmetric *)
    | aar4_l E1 E2 μ E1' : lts_step_a E1 (ActExt μ) E1' → lts_step_a (E1 □ E2) (ActExt μ) E1'
    | aar4_r E1 E2 μ E2' : lts_step_a E2 (ActExt μ) E2' → lts_step_a (E1 □ E2) (ActExt μ) E2'
    (* AR5, + symmetric *)
    | aar5_l E1 E2 μ E1' : lts_step_a E1 (ActExt μ) E1' → lts_step_a (E1 │ E2) (ActExt μ) (E1' │ E2)
    | aar5_r E1 E2 μ E2' : lts_step_a E2 (ActExt μ) E2' → lts_step_a (E1 │ E2) (ActExt μ) (E1 │ E2')
    (* AR6 *)
    | aar6 E1 E2 μ E1' : lts_step_a E1 (ActExt μ) E1' → lts_step_a (E1 ⌊⌊ E2) (ActExt μ) (E1' │ E2)
    (* AR7 *)
    | aar7 be E1 E2 μ E1' :
        eval_bexp be = Some true → lts_step_a E1 (ActExt μ) E1' → lts_step_a (IF be THEN E1 ELSE E2) (ActExt μ) E1'
    (* AR8 *)
    | aar8 be E1 E2 μ E2' :
        eval_bexp be = Some false → lts_step_a E2 (ActExt μ) E2' → lts_step_a (IF be THEN E1 ELSE E2) (ActExt μ) E2'
    (* IR1 *)
    | air1 : lts_step_a Ω τ Ω
    (* IR2 *)
    | air2 X E : lts_step_a (rec X • E) τ (psubst X (rec X • E) E)
    (* IR3 *)
    | air3 be E1 E2 E1' : eval_bexp be = Some true → lts_step_a E1 τ E1' → lts_step_a (IF be THEN E1 ELSE E2) τ E1'
    (* IR4 *)
    | air4 be E1 E2 E2' : eval_bexp be = Some false → lts_step_a E2 τ E2' → lts_step_a (IF be THEN E1 ELSE E2) τ E2'
    (* IR5 *)
    | air5 t E : E <> 𝟘 → lts_step_a (out( t ) • E) τ ((out( t ) • 𝟘) │ E)
    (* IR6 *)
    | air6 E1 E2 : lts_step_a (eval( E1 ) • E2) τ (E1 │ E2)
    (* IR7 *)
    | air7_l E1 E2 : lts_step_a (E1 ⊕ E2) τ E1
    | air7_r E1 E2 : lts_step_a (E1 ⊕ E2) τ E2
    (* IR8, + symmetric *)
    | air8_l E1 E2 E1' : lts_step_a E1 τ E1' → lts_step_a (E1 □ E2) τ (E1' □ E2)
    | air8_r E1 E2 E2' : lts_step_a E2 τ E2' → lts_step_a (E1 □ E2) τ (E1 □ E2')
    (* IR9, + symmetric *)
    | air9_l E1 E2 E1' : lts_step_a E1 τ E1' → lts_step_a (E1 │ E2) τ (E1' │ E2)
    | air9_r E1 E2 E2' : lts_step_a E2 τ E2' → lts_step_a (E1 │ E2) τ (E1 │ E2')
    (* IR10, + symmetric *)
    | air10_l E1 E2 E1' : lts_step_a E1 τ E1' → lts_step_a (E1 ║ E2) τ (E1' ║ E2)
    | air10_r E1 E2 E2' : lts_step_a E2 τ E2' → lts_step_a (E1 ║ E2) τ (E1 ║ E2')
    (* IR11 *)
    | air11 E1 E2 E1' : lts_step_a E1 τ E1' → lts_step_a (E1 ⌊⌊ E2) τ (E1' ⌊⌊ E2)
    (* IR12: synchronisation along dual labels *)
    | air12 E1 E2 μ1 μ2 E1' E2' :
        lts_step_a E1 (ActExt μ1) E1' → lts_step_a E2 (ActExt μ2) E2' → PALA_dual μ1 μ2 →
        lts_step_a (E1 │ E2) τ (E1' │ E2')
    (* IR13 *)
    | air13 E1 E2 μ1 μ2 E1' E2' :
        lts_step_a E1 (ActExt μ1) E1' → lts_step_a E2 (ActExt μ2) E2' → PALA_dual μ1 μ2 →
        lts_step_a (E1 ║ E2) τ (E1' │ E2').

  (* ** Enumerating successors *)

  (* The outputs offered by a term. *)
  Fixpoint collect_out_a (E : term) : list eot :=
    match E with
    | out( t ) • 𝟘 =>
        match eval_out_tuple t with Some ot => [ot] | None => [] end
    | E1 □ E2 => collect_out_a E1 ++ collect_out_a E2
    | E1 │ E2 => collect_out_a E1 ++ collect_out_a E2
    | E1 ⌊⌊ E2 => collect_out_a E1
    | IF be THEN E1 ELSE E2 =>
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
    intros h. remember (ActExt (AOut a)) as 𝜆 eqn:eq.
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
      exists 𝟘. destruct hin as [<- | []]. by apply aar3.
    - destruct (eval_bexp be) as [b|] eqn:hbe; [destruct b |]; simpl in hin; [| | contradiction].
      + destruct (IHE1 hin) as [E1' h1]. exists E1'. by eapply aar7.
      + destruct (IHE2 hin) as [E2' h2]. exists E2'. by eapply aar8.
    - destruct (in_dec (λ x y : eot, decide (x = y)) a (collect_out_a E1)) as [hin1|hnin1].
      + destruct (IHE1 hin1) as [E1' h1]. exists E1'. by eapply aar4_l.
      + assert (In a (collect_out_a E2)) as hin2 by (apply in_app_or in hin as [?|?]; [contradiction | done]).
        destruct (IHE2 hin2) as [E2' h2]. exists E2'. by eapply aar4_r.
    - destruct (in_dec (λ x y : eot, decide (x = y)) a (collect_out_a E1)) as [hin1|hnin1].
      + destruct (IHE1 hin1) as [E1' h1]. exists (E1' │ E2). by eapply aar5_l.
      + assert (In a (collect_out_a E2)) as hin2 by (apply in_app_or in hin as [?|?]; [contradiction | done]).
        destruct (IHE2 hin2) as [E2' h2]. exists (E1 │ E2'). by eapply aar5_r.
    - destruct (IHE1 hin) as [E1' h1]. exists (E1' │ E2). by eapply aar6.
  Qed.

  Fixpoint all_recv_a (p : term) (ot : eot) : list term :=
    match p with
    | in( t ) • E =>
        match eval_in_tuple t with
        | Some it => if tuple_match_b it ot then [subst_term (build_subst it ot) E] else []
        | None => []
        end
    | read( t ) • E =>
        match eval_in_tuple t with
        | Some it =>
            if tuple_match_b it ot
            then [(out( eot_to_tuple ot ) • 𝟘) │ subst_term (build_subst it ot) E] else []
        | None => []
        end
    | IF be THEN E1 ELSE E2 =>
        match eval_bexp be with
        | Some true => all_recv_a E1 ot
        | Some false => all_recv_a E2 ot
        | None => []
        end
    | E1 □ E2 => all_recv_a E1 ot ++ all_recv_a E2 ot
    | E1 ⌊⌊ E2 => map (λ E1', E1' │ E2) (all_recv_a E1 ot)
    | E1 │ E2 => map (λ E1', E1' │ E2) (all_recv_a E1 ot) ++ map (λ E2', E1 │ E2') (all_recv_a E2 ot)
    | _ => []
    end.

  Fixpoint all_steps_a (p : term) (𝜆 : Labels PALA_Act) : list term :=
    match p with
    | 𝟘 => []
    | t_pvar _ => []
    | ✓ => []
    | Ω => match 𝜆 with τ => [Ω] | _ => [] end
    | rec X • E => match 𝜆 with τ => [psubst X (rec X • E) E] | _ => [] end
    | out( t ) • E =>
        match 𝜆 with
        | ActExt (AOut ot) =>
            if bool_decide (E = 𝟘) then
              match eval_out_tuple t with
              | Some ot' => if bool_decide (ot' = ot) then [𝟘] else []
              | None => []
              end
            else []
        | τ => if bool_decide (E <> 𝟘) then [(out( t ) • 𝟘) │ E] else []
        | _ => []
        end
    | in( t ) • E =>
        match 𝜆 with
        | ActExt (AIn l) =>
            match eval_in_tuple t with
            | Some it =>
                if bool_decide (template_of it = ltemplate l)
                then [subst_term (build_subst it (ltuple l)) E] else []
            | None => []
            end
        | _ => []
        end
    | read( t ) • E =>
        match 𝜆 with
        | ActExt (AIn l) =>
            match eval_in_tuple t with
            | Some it =>
                if bool_decide (template_of it = ltemplate l)
                then [(out( eot_to_tuple (ltuple l) ) • 𝟘) │ subst_term (build_subst it (ltuple l)) E]
                else []
            | None => []
            end
        | _ => []
        end
    | eval( E1 ) • E2 => match 𝜆 with τ => [E1 │ E2] | _ => [] end
    | IF be THEN E1 ELSE E2 =>
        match eval_bexp be with
        | Some true => all_steps_a E1 𝜆
        | Some false => all_steps_a E2 𝜆
        | None => []
        end
    | E1 ⊕ E2 => match 𝜆 with τ => [E1; E2] | _ => [] end
    | E1 □ E2 =>
        match 𝜆 with
        | τ => map (λ E1', E1' □ E2) (all_steps_a E1 τ)
               ++ map (λ E2', E1 □ E2') (all_steps_a E2 τ)
        | ActExt _ => all_steps_a E1 𝜆 ++ all_steps_a E2 𝜆
        end
    | E1 ⌊⌊ E2 =>
        match 𝜆 with
        | τ => map (λ E1', E1' ⌊⌊ E2) (all_steps_a E1 τ)
        | ActExt _ => map (λ E1', E1' │ E2) (all_steps_a E1 𝜆)
        end
    | E1 ║ E2 =>
        match 𝜆 with
        | τ =>
            map (λ E1', E1' ║ E2) (all_steps_a E1 τ)
            ++ map (λ E2', E1 ║ E2') (all_steps_a E2 τ)
            ++ flat_map (λ a,
                 flat_map (λ E1', map (λ E2', E1' │ E2')
                                    (all_recv_a E2 a))
                   (all_steps_a E1 (ActExt (AOut a))))
                 (collect_out_a E1)
            ++ flat_map (λ a,
                 flat_map (λ E2', map (λ E1', E1' │ E2')
                                    (all_recv_a E1 a))
                   (all_steps_a E2 (ActExt (AOut a))))
                 (collect_out_a E2)
        | ActExt _ => []
        end
    | E1 │ E2 =>
        match 𝜆 with
        | τ =>
            map (λ E1', E1' │ E2) (all_steps_a E1 τ)
            ++ map (λ E2', E1 │ E2') (all_steps_a E2 τ)
            ++ flat_map (λ a,
                 flat_map (λ E1', map (λ E2', E1' │ E2')
                                    (all_recv_a E2 a))
                   (all_steps_a E1 (ActExt (AOut a))))
                 (collect_out_a E1)
            ++ flat_map (λ a,
                 flat_map (λ E2', map (λ E1', E1' │ E2')
                                    (all_recv_a E1 a))
                   (all_steps_a E2 (ActExt (AOut a))))
                 (collect_out_a E2)
        | ActExt _ =>
            map (λ E1', E1' │ E2) (all_steps_a E1 𝜆)
            ++ map (λ E2', E1 │ E2') (all_steps_a E2 𝜆)
        end
    end.

  Lemma all_recv_a_spec p ot q :
    In q (all_recv_a p ot) ↔ ∃ l, ltuple l = ot ∧ In q (all_steps_a p (ActExt (AIn l))).
  Proof.
    revert q. induction p; intros q; simpl.
    all: try (split; [intros [] | intros (? & _ & [])]; done).
    all: try (destruct (eval_bexp _) as [[]|];
              [apply IHp1 | apply IHp2 | split; [intros [] | intros (? & _ & [])]]; done).
    all: try (destruct (eval_in_tuple _) as [it|]; [| split; [intros [] | intros (? & _ & [])]];
      split;
      [ destruct (tuple_match_b it ot) eqn:hb; [| intros []];
        apply tuple_match_b_correct in hb; destruct (label_of_spec it ot hb) as [h1 h2];
        intros [<- | []]; exists (label_of it ot); split; [exact h2 |];
        rewrite bool_decide_true by (symmetry; exact h1); rewrite h2; by left
      | intros (l & <- & hin); case_bool_decide as he; [| destruct hin];
        rewrite (proj2 (tuple_match_b_correct it (ltuple l)) (template_tuple_match it l he));
        exact hin ]; done).
    all: try setoid_rewrite in_app_iff; try setoid_rewrite in_map_iff;
      setoid_rewrite IHp1; try setoid_rewrite IHp2; naive_solver.
  Qed.

  Lemma all_steps_a_sound p 𝜆 q : In q (all_steps_a p 𝜆) → lts_step_a p 𝜆 q.
  Proof.
    revert 𝜆 q.
    induction p; intros 𝜆 q hin; simpl in hin.
    - contradiction.
    - destruct 𝜆 as [μ|]; [contradiction |]. destruct hin as [<- | []]. apply air1.
    - destruct 𝜆 as [[l|ot]|].
      + contradiction.
      + case_bool_decide as hE; [subst | contradiction].
        destruct (eval_out_tuple t) as [ot'|] eqn:ev; [| contradiction].
        case_bool_decide as hb; [subst | contradiction].
        destruct hin as [<- | []]. by apply aar3.
      + case_bool_decide as hE; [| contradiction]. destruct hin as [<- | []]. by apply air5.
    - destruct 𝜆 as [[l|ot]|]; try contradiction.
      destruct (eval_in_tuple t) as [it|] eqn:ev; [| contradiction].
      case_bool_decide as hb; [| contradiction].
      destruct hin as [<- | []]. by apply aar1.
    - destruct 𝜆 as [[l|ot]|]; try contradiction.
      destruct (eval_in_tuple t) as [it|] eqn:ev; [| contradiction].
      case_bool_decide as hb; [| contradiction].
      destruct hin as [<- | []]. by apply aar2.
    - destruct 𝜆 as [μ|]; [contradiction |]. destruct hin as [<- | []]. apply air6.
    - destruct (eval_bexp be) as [[]|] eqn:hbe; [| | contradiction]; destruct 𝜆 as [μ|].
      + eapply aar7; [done | by apply IHp1].
      + eapply air3; [done | by apply IHp1].
      + eapply aar8; [done | by apply IHp2].
      + eapply air4; [done | by apply IHp2].
    - destruct 𝜆 as [μ|]; [contradiction |]. destruct hin as [<- | [<- | []]]; [apply air7_l | apply air7_r].
    - destruct 𝜆 as [μ|]; apply in_app_iff in hin as [hin | hin].
      + by apply aar4_l, IHp1.
      + by apply aar4_r, IHp2.
      + apply in_map_iff in hin as (E1' & <- & hin). by apply air8_l, IHp1.
      + apply in_map_iff in hin as (E2' & <- & hin). by apply air8_r, IHp2.
    - destruct 𝜆 as [μ|].
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
          apply all_recv_a_spec in hE2' as (l & hl & hE2').
          eapply (air12 _ _ (AOut a) (AIn l)); [by apply IHp1 | by apply IHp2 | exact hl].
        * apply in_flat_map in hin as (a & ha & hin2).
          apply in_flat_map in hin2 as (E2' & hE2' & hin3).
          apply in_map_iff in hin3 as (E1' & <- & hE1').
          apply all_recv_a_spec in hE1' as (l & hl & hE1').
          eapply (air12 _ _ (AIn l) (AOut a)); [by apply IHp1 | by apply IHp2 | exact hl].
    - destruct 𝜆 as [μ|]; apply in_map_iff in hin as (E1' & <- & hin).
      + by apply aar6, IHp1.
      + by apply air11, IHp1.
    - destruct 𝜆 as [μ|]; [contradiction |].
      apply in_app_iff in hin as [hin | hin];
        [| apply in_app_iff in hin as [hin | hin]; [| apply in_app_iff in hin as [hin | hin]]].
      + apply in_map_iff in hin as (E1' & <- & hin). by apply air10_l, IHp1.
      + apply in_map_iff in hin as (E2' & <- & hin). by apply air10_r, IHp2.
      + apply in_flat_map in hin as (a & ha & hin2).
        apply in_flat_map in hin2 as (E1' & hE1' & hin3).
        apply in_map_iff in hin3 as (E2' & <- & hE2').
        apply all_recv_a_spec in hE2' as (l & hl & hE2').
        eapply (air13 _ _ (AOut a) (AIn l)); [by apply IHp1 | by apply IHp2 | exact hl].
      + apply in_flat_map in hin as (a & ha & hin2).
        apply in_flat_map in hin2 as (E2' & hE2' & hin3).
        apply in_map_iff in hin3 as (E1' & <- & hE1').
        apply all_recv_a_spec in hE1' as (l & hl & hE1').
        eapply (air13 _ _ (AIn l) (AOut a)); [by apply IHp1 | by apply IHp2 | exact hl].
    - contradiction.
    - destruct 𝜆 as [μ|]; [contradiction |]. destruct hin as [<- | []]. apply air2.
    - contradiction.
  Qed.

  Lemma all_steps_a_complete p 𝜆 q : lts_step_a p 𝜆 q → In q (all_steps_a p 𝜆).
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
    - destruct μ1 as [l1|a1], μ2 as [l2|a2]; simpl in *; try contradiction.
      + pose proof (out_step_in_collect_out_a E2 a2 E2' ltac:(assumption)) as ha.
        apply in_or_app; right; apply in_or_app; right; apply in_or_app; right.
        apply in_flat_map. exists a2. split; [done |].
        apply in_flat_map. exists E2'. split; [exact IHlts_step_a2 |].
        apply in_map_iff. exists E1'. split; [done |].
        apply all_recv_a_spec. exists l1. split; [done | exact IHlts_step_a1].
      + pose proof (out_step_in_collect_out_a E1 a1 E1' ltac:(assumption)) as ha.
        apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
        apply in_flat_map. exists a1. split; [done |].
        apply in_flat_map. exists E1'. split; [exact IHlts_step_a1 |].
        apply in_map_iff. exists E2'. split; [done |].
        apply all_recv_a_spec. exists l2. split; [done | exact IHlts_step_a2].
    - destruct μ1 as [l1|a1], μ2 as [l2|a2]; simpl in *; try contradiction.
      + pose proof (out_step_in_collect_out_a E2 a2 E2' ltac:(assumption)) as ha.
        apply in_or_app; right; apply in_or_app; right; apply in_or_app; right.
        apply in_flat_map. exists a2. split; [done |].
        apply in_flat_map. exists E2'. split; [exact IHlts_step_a2 |].
        apply in_map_iff. exists E1'. split; [done |].
        apply all_recv_a_spec. exists l1. split; [done | exact IHlts_step_a1].
      + pose proof (out_step_in_collect_out_a E1 a1 E1' ltac:(assumption)) as ha.
        apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
        apply in_flat_map. exists a1. split; [done |].
        apply in_flat_map. exists E1'. split; [exact IHlts_step_a1 |].
        apply in_map_iff. exists E2'. split; [done |].
        apply all_recv_a_spec. exists l2. split; [done | exact IHlts_step_a2].
  Qed.

  (* ** [gLts] instance *)

  Definition PALA_performs (p : term) (𝜆 : Labels PALA_Act) : Prop := all_steps_a p 𝜆 ≠ [].

  #[global] Instance PALA_step_dec p 𝜆 q : Decision (lts_step_a p 𝜆 q).
  Proof.
    destruct (in_dec term_eqdec q (all_steps_a p 𝜆)) as [hin|hnin].
    - left. by apply all_steps_a_sound.
    - right. intros h. by apply hnin, all_steps_a_complete.
  Defined.

  #[global] Instance PALA_performs_dec p 𝜆 : Decision (PALA_performs p 𝜆).
  Proof. unfold PALA_performs. destruct (all_steps_a p 𝜆); [right; intros hne; by apply hne | left; discriminate]. Defined.

  Definition PALA_performs_spec1 p 𝜆 : PALA_performs p 𝜆 → {q | lts_step_a p 𝜆 q}.
  Proof.
    unfold PALA_performs. intros hne.
    destruct (all_steps_a p 𝜆) as [|q l] eqn:e; [done |].
    exists q. apply all_steps_a_sound. rewrite e. by left.
  Defined.

  Definition PALA_performs_spec2 p 𝜆 : {q | lts_step_a p 𝜆 q} → PALA_performs p 𝜆.
  Proof.
    intros [q h] href.
    apply all_steps_a_complete in h. by rewrite href in h.
  Defined.

  #[global] Instance PALA_gLts : gLts term PALA_ExtAction :=
    @MkgLts term PALA_Act PALA_ExtAction lts_step_a term_eqdec PALA_step_dec
      PALA_performs PALA_performs_dec PALA_performs_spec1 PALA_performs_spec2.

  (* ** [FiniteImagegLts]/[coFiniteImagegLts] *)

  #[global] Instance PALA_FiniteImagegLts : FiniteImagegLts term PALA_Act.
  Proof.
    unshelve econstructor.
    - exact term_countable.
    - intros p 𝜆. unfold dsig.
      apply (list_finite (all_steps_a p 𝜆)).
      intros q. rewrite bool_decide_spec, list_elem_of_In.
      split; [apply all_steps_a_complete | apply all_steps_a_sound].
  Defined.

  Definition co_next_a (p : term) (𝜆 : PALA_Act) : list term :=
    match 𝜆 with
    | AIn l => all_steps_a p (ActExt (AOut (ltuple l)))
    | AOut ot => all_recv_a p ot
    end.

  Lemma co_next_a_spec p 𝜆 q :
    In q (co_next_a p 𝜆) ↔ ∃ 𝜆', PALA_dual 𝜆' 𝜆 ∧ lts_step_a p (ActExt 𝜆') q.
  Proof.
    destruct 𝜆 as [l|ot]; simpl.
    - split.
      + intros hin. exists (AOut (ltuple l)). split; [reflexivity | by apply all_steps_a_sound].
      + intros ([l'|ot'] & hd & hs); simpl in hd; [done |]. subst. by apply all_steps_a_complete.
    - rewrite all_recv_a_spec. split.
      + intros (l & hl & hin). exists (AIn l). split; [exact hl | by apply all_steps_a_sound].
      + intros ([l|ot'] & hd & hs); simpl in hd; [| done]. exists l. split; [exact hd | by apply all_steps_a_complete].
  Qed.

  #[global] Instance PALA_co_next_states_decidable p 𝜆 q :
    Decision (∃ 𝜆', PALA_dual 𝜆' 𝜆 ∧ lts_step_a p (ActExt 𝜆') q).
  Proof.
    destruct (in_dec term_eqdec q (co_next_a p 𝜆)) as [hin|hnin].
    - left. by apply co_next_a_spec.
    - right. intros hc. by apply hnin, co_next_a_spec.
  Defined.

  #[global] Instance PALA_coFiniteImagegLts : coFiniteImagegLts term PALA_Act.
  Proof.
    unshelve econstructor.
    - exact term_countable.
    - intros p. unfold dsig.
      apply (list_finite (all_steps_a p τ)).
      intros q. rewrite bool_decide_spec, list_elem_of_In.
      split; [apply all_steps_a_complete | apply all_steps_a_sound].
    - intros p 𝜆. unfold dsig.
      apply (list_finite (co_next_a p 𝜆)).
      intros q. rewrite bool_decide_spec, list_elem_of_In. symmetry. apply co_next_a_spec.
  Defined.

  (* ** [Prop_of_Inter term term PALA_Act PALA_Act PALA_dual] *)

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

  Lemma PALA_co_inter_action_spec (μ2 μ1 : PALA_Act) :
    PALA_dual μ2 μ1 → μ2 ∈ (list_to_set (co_labels μ1) : gset PALA_Act).
  Proof. intros hx. apply elem_of_list_to_set, list_elem_of_In. by apply co_labels_spec. Qed.

  #[global] Instance PALA_Prop_of_Inter : Prop_of_Inter term term PALA_Act PALA_Act PALA_dual := {|
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
(* end hide *)
