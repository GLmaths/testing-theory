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
(* * lqCCS: the linear typing of qubit ownership

    The type system of Ceragioli, Gadducci, Lomurno, Tedeschi
    (arXiv:2604.23756, "Typing rules for lqCCS"), on the asynchronous syntax:
    [Σ ⊢ P] says that [P] owns exactly the qubits [Σ].

    - Channels and variables are typed globally ([qchan], [qvar]): a channel
      carries qubits or classical values, a variable holds a qubit or a
      classical value.
    - [Σ] holds qubit names and the qubit variables bound by receptions,
      [QN q] and [QV x] (rule [QRecv]: [Σ ∪ {x} ⊢ P]).
    - An output is a process of its own: on a qubit channel it owns the qubit
      it sends ([{e} ⊢ c!e], rule [QSend] with the continuation [0]); on a
      classical channel it owns nothing.
    - [0_ẽ] owns exactly [ẽ] (rule [Nil]); parallel components own disjoint
      qubits (rule [Par]); success [①] owns anything.

    The results: substitution lemmas, and subject reduction for the steps of
    a program ([lqCCS_Program.v]) — silent steps keep the qubits owned, an
    emission on a qubit channel gives one away, a reception takes one; an
    operation or a measurement only acts on owned qubits. *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list sets gmap.
From TestingTheory Require Import lqCCS_Syntax lqCCS_Program.
(* ** Qubit terms *)

Inductive qt : Type :=
| QN (q : qubit)
| QV (x : var).

#[global] Instance qt_eq_dec : EqDecision qt.
Proof. solve_decision. Defined.

#[global] Instance qt_countable : Countable qt.
Proof.
  refine (inj_countable' (λ a, match a with QN q => inl q | QV x => inr x end : qubit + var)
    (λ s, match s with inl q => QN q | inr x => QV x end) _).
  by intros [].
Defined.

Definition vclass (v : val) : Prop := match v with VQubit _ => False | _ => True end.

Section Typing.
  (* The global typing of channels and variables: [true] for qubits. *)
  Context (qchan : chan → bool) (qvar : var → bool).

  Definition qterm (e : exp) : option qt :=
    match e with
    | EVal (VQubit q) => Some (QN q)
    | EVar x => if qvar x then Some (QV x) else None
    | _ => None
    end.

  Definition qterms (es : list exp) : option (list qt) := mapM qterm es.

  Fixpoint classical (e : exp) : Prop :=
    match e with
    | EVar x => qvar x = false
    | EVal v => vclass v
    | ENot e => classical e
    | EOr e1 e2 | ELe e1 e2 | EEq e1 e2 => classical e1 ∧ classical e2
    end.

  Inductive wt : gset qt → proc → Prop :=
  | wt_send_c t c e :
      qchan c = false → classical e → wt ∅ (PSend t c e)
  | wt_send_q t c e a :
      qchan c = true → qterm e = Some a → wt {[ a ]} (PSend t c e)
  | wt_ite Σ e P Q :
      classical e → wt Σ P → wt Σ Q → wt Σ (PIte e P Q)
  | wt_par Σ1 Σ2 P Q :
      Σ1 ## Σ2 → wt Σ1 P → wt Σ2 Q → wt (Σ1 ∪ Σ2) (PPar P Q)
  | wt_res Σ P c :
      wt Σ P → wt Σ (PRes P c)
  | wt_guard Σ g :
      gwt Σ g → wt Σ (PG g)
  with gwt : gset qt → guard → Prop :=
  | gwt_nil Σ es l :
      qterms es = Some l → NoDup l → Σ = list_to_set l → gwt Σ (GNil es)
  | gwt_succ Σ :
      gwt Σ GSucc
  | gwt_tau Σ t P :
      wt Σ P → gwt Σ (GPre (PTau t) P)
  | gwt_taupair Σ t t' P :
      wt Σ P → gwt Σ (GPre (PTauPair t t') P)
  | gwt_op Σ t E es l P :
      qterms es = Some l → NoDup l → list_to_set l ⊆ Σ → wt Σ P →
      gwt Σ (GPre (POp t E es) P)
  | gwt_meas Σ t M es x l P :
      qterms es = Some l → NoDup l → list_to_set l ⊆ Σ → qvar x = false → wt Σ P →
      gwt Σ (GPre (PMeas t M es x) P)
  | gwt_recv_c Σ t c x P :
      qchan c = false → qvar x = false → wt Σ P → gwt Σ (GPre (PRecv t c x) P)
  | gwt_recv_q Σ t c x P :
      qchan c = true → qvar x = true → QV x ∉ Σ → wt ({[ QV x ]} ∪ Σ) P →
      gwt Σ (GPre (PRecv t c x) P)
  | gwt_sum Σ g1 g2 :
      gwt Σ g1 → gwt Σ g2 → gwt Σ (GSum g1 g2).

  Scheme wt_mut := Induction for wt Sort Prop
    with gwt_mut := Induction for gwt Sort Prop.
  Combined Scheme wt_gwt_ind from wt_mut, gwt_mut.

  (* Only qubit names: the context of a closed process. *)
  Definition names (Σ : gset qt) : Prop := ∀ a, a ∈ Σ → ∃ q, a = QN q.

  (* ** Expressions *)

  Lemma classical_eval e v : classical e → eval e = Some v → vclass v.
  Proof.
    revert v. induction e as [y|w|e IH|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2];
      intros v Hc He; simpl in *; try done.
    - by simplify_eq.
    - destruct (eval e) as [[]|]; simplify_eq; done.
    - destruct (eval e1) as [[]|], (eval e2) as [[]|]; simplify_eq; done.
    - destruct (eval e1), (eval e2); simplify_eq. unfold option_map in He.
      destruct (val_le _ _); simplify_eq; done.
    - destruct (eval e1), (eval e2); simplify_eq; done.
  Qed.

  Lemma classical_subst_q e x v : classical e → qvar x = true → exp_subst e x v = e.
  Proof.
    induction e as [y|w|e IH|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2];
      intros Hc Hx; simpl in *; try done.
    all: try (case_decide; [subst; congruence|done]).
    all: try (by rewrite IH).
    all: destruct Hc; by rewrite IH1, IH2.
  Qed.

  Lemma classical_subst_c e x v : classical e → vclass v → classical (exp_subst e x v).
  Proof.
    induction e as [y|w|e IH|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2];
      intros Hc Hv; simpl in *; try done.
    all: try (case_decide; done).
    all: try (by apply IH).
    all: destruct Hc; split; auto.
  Qed.

  (* The renaming of [x] into [q] on qubit terms. *)
  Definition ren (x : var) (q : qubit) (a : qt) : qt :=
    if decide (a = QV x) then QN q else a.

  Lemma qterm_subst_q e x q :
    qvar x = true → qterm (exp_subst e x (VQubit q)) = ren x q <$> qterm e.
  Proof.
    intros Hx. unfold ren.
    destruct e as [y|[b|n|q']|e|e1 e2|e1 e2|e1 e2]; simpl; try done.
    - case_decide as Hxy; simpl.
      + subst. rewrite Hx. simpl. by rewrite decide_True.
      + destruct (qvar y); simpl; [|done]. rewrite decide_False; congruence.
  Qed.

  Lemma qterm_subst_c e x v :
    qvar x = false → vclass v → qterm (exp_subst e x v) = qterm e.
  Proof.
    intros Hx Hv.
    destruct e as [y|w|e|e1 e2|e1 e2|e1 e2]; simpl; try done.
    case_decide as Hxy; simpl; [subst; rewrite Hx; by destruct v|done].
  Qed.

  Lemma qterm_subst_other e x v a :
    qterm e = Some a → a ≠ QV x → exp_subst e x v = e.
  Proof.
    destruct e as [y|[b|n|q']|e|e1 e2|e1 e2|e1 e2]; simpl; try done.
    case_decide as Hxy; [|done]. subst. destruct (qvar y); intros; simplify_eq.
  Qed.

  Lemma qterms_subst_q es x q :
    qvar x = true → qterms (exps_subst es x (VQubit q)) = fmap (M := list) (ren x q) <$> qterms es.
  Proof.
    intros Hx. unfold qterms, exps_subst. induction es as [|e es IH]; [done|].
    simpl. rewrite qterm_subst_q by done.
    change (mapM qterm (map (λ e, exp_subst e x (VQubit q)) es)) with
      (mapM qterm (exps_subst es x (VQubit q))).
    unfold exps_subst. rewrite IH.
    destruct (qterm e), (mapM qterm es); done.
  Qed.

  Lemma qterms_subst_c es x v :
    qvar x = false → vclass v → qterms (exps_subst es x v) = qterms es.
  Proof.
    intros Hx Hv. unfold qterms, exps_subst. induction es as [|e es IH]; [done|].
    simpl. rewrite qterm_subst_c by done.
    change (mapM qterm (map (λ e, exp_subst e x v) es)) with
      (mapM qterm (exps_subst es x v)).
    unfold exps_subst. by rewrite IH.
  Qed.

  Lemma qterms_subst_other es x v l :
    qterms es = Some l → QV x ∉ l → exps_subst es x v = es.
  Proof.
    unfold qterms, exps_subst. revert l. induction es as [|e es IH]; intros l Hq Hl; [done|].
    simpl in Hq. destruct (qterm e) as [a|] eqn:Ea; [|done].
    destruct (mapM qterm es) as [l'|] eqn:El; [|done].
    inversion Hq; subst l.
    simpl. rewrite (qterm_subst_other e x v a); [|done|intros ->; apply Hl; by left].
    f_equal. apply (IH l'); [done|intros ?; apply Hl; by right].
  Qed.

  (* ** The renaming on lists of qubit terms *)

  Lemma ren_NoDup x q l : NoDup l → QN q ∉ l → NoDup (ren x q <$> l).
  Proof.
    induction l as [|a l IH]; intros Hl Hq; simpl; [constructor|].
    apply NoDup_cons in Hl as [Ha Hl]. constructor; [|apply IH; set_solver].
    intros (b & Eb & Hb)%list_elem_of_fmap. unfold ren in Eb.
    repeat case_decide; subst; try done; set_solver.
  Qed.

  Lemma ren_set_in x q l :
    QV x ∈ l → list_to_set (ren x q <$> l) = ({[ QN q ]} ∪ (list_to_set l ∖ {[ QV x ]}) : gset qt).
  Proof.
    intros Hx. apply set_eq. intros a.
    rewrite elem_of_union, elem_of_difference, !elem_of_list_to_set, elem_of_singleton,
      list_elem_of_fmap.
    unfold ren. split.
    - intros (b & -> & Hb). case_decide; [by left|right; set_solver].
    - intros [->|[Ha Hne]].
      + exists (QV x). by rewrite decide_True.
      + exists a. rewrite decide_False; [done|set_solver].
  Qed.

  Lemma ren_set_sub x q l (Σ : gset qt) :
    list_to_set l ⊆ Σ → list_to_set (ren x q <$> l) ⊆ ({[ QN q ]} ∪ (Σ ∖ {[ QV x ]}) : gset qt).
  Proof.
    intros Hl a. rewrite elem_of_list_to_set, list_elem_of_fmap.
    intros (b & -> & Hb). unfold ren. case_decide; [set_solver|].
    apply elem_of_union_r, elem_of_difference. split; [|set_solver].
    apply Hl. by apply elem_of_list_to_set.
  Qed.

  (* ** Substitution *)

  (* A qubit variable that a process does not own does not occur in it. *)
  Lemma wt_subst_absent :
    (∀ Σ P, wt Σ P → ∀ x v, qvar x = true → QV x ∉ Σ → subst P x v = P)
    ∧ (∀ Σ g, gwt Σ g → ∀ x v, qvar x = true → QV x ∉ Σ → gsubst g x v = g).
  Proof.
    apply wt_gwt_ind.
    - intros t c e Hc He x v Hx Hn. simpl. by rewrite classical_subst_q.
    - intros t c e a Hc Ha x v Hx Hn. simpl.
      rewrite (qterm_subst_other e x v a); [done|done|]. intros ->. set_solver.
    - intros Σ e P Q He HP IHP HQ IHQ x v Hx Hn. simpl.
      by rewrite classical_subst_q, IHP, IHQ.
    - intros Σ1 Σ2 P Q Hd HP IHP HQ IHQ x v Hx Hn. simpl.
      rewrite IHP, IHQ; [done|done|set_solver|done|set_solver].
    - intros Σ P c HP IHP x v Hx Hn. simpl. by rewrite IHP.
    - intros Σ g Hg IHg x v Hx Hn. simpl. by rewrite IHg.
    - intros Σ es l Hq Hnd -> x v Hx Hn. simpl.
      rewrite (qterms_subst_other es x v l); [done|done|].
      intros Hin. apply Hn. by apply elem_of_list_to_set.
    - done.
    - intros Σ t P HP IHP x v Hx Hn. simpl. by rewrite IHP.
    - intros Σ t t' P HP IHP x v Hx Hn. simpl. by rewrite IHP.
    - intros Σ t E es l P Hq Hnd Hs HP IHP x v Hx Hn. simpl.
      rewrite (qterms_subst_other es x v l); [|done|].
      + by rewrite IHP.
      + intros Hin. apply Hn, Hs. by apply elem_of_list_to_set.
    - intros Σ t M es y l P Hq Hnd Hs Hy HP IHP x v Hx Hn. simpl.
      rewrite (qterms_subst_other es x v l); [|done|].
      + case_decide; [done|]. by rewrite IHP.
      + intros Hin. apply Hn, Hs. by apply elem_of_list_to_set.
    - intros Σ t c y P Hc Hy HP IHP x v Hx Hn. simpl.
      case_decide; [done|]. by rewrite IHP.
    - intros Σ t c y P Hc Hy Hny HP IHP x v Hx Hn. simpl.
      case_decide as Hb; [done|]. rewrite IHP; [done|done|].
      intros [Hxy%elem_of_singleton|Hin]%elem_of_union; [|done].
      simplify_eq; try (by apply Hb).
    - intros Σ g1 g2 H1 IH1 H2 IH2 x v Hx Hn. simpl. by rewrite IH1, IH2.
  Qed.

  Lemma wt_subst_c :
    (∀ Σ P, wt Σ P → ∀ x v, qvar x = false → vclass v → wt Σ (subst P x v))
    ∧ (∀ Σ g, gwt Σ g → ∀ x v, qvar x = false → vclass v → gwt Σ (gsubst g x v)).
  Proof.
    apply wt_gwt_ind.
    - intros t c e Hc He x v Hx Hv. simpl. constructor; [done|]. by apply classical_subst_c.
    - intros t c e a Hc Ha x v Hx Hv. simpl. econstructor; [done|].
      by rewrite qterm_subst_c.
    - intros Σ e P Q He HP IHP HQ IHQ x v Hx Hv. simpl.
      constructor; auto. by apply classical_subst_c.
    - intros Σ1 Σ2 P Q Hd HP IHP HQ IHQ x v Hx Hv. simpl. constructor; auto.
    - intros Σ P c HP IHP x v Hx Hv. simpl. constructor; auto.
    - intros Σ g Hg IHg x v Hx Hv. simpl. constructor; auto.
    - intros Σ es l Hq Hnd HΣ x v Hx Hv. simpl.
      econstructor; [|done|done]. by rewrite qterms_subst_c.
    - intros. simpl. constructor.
    - intros Σ t P HP IHP x v Hx Hv. simpl. constructor; auto.
    - intros Σ t t' P HP IHP x v Hx Hv. simpl. constructor; auto.
    - intros Σ t E es l P Hq Hnd Hs HP IHP x v Hx Hv. simpl.
      econstructor; [|done|done|auto]. by rewrite qterms_subst_c.
    - intros Σ t M es y l P Hq Hnd Hs Hy HP IHP x v Hx Hv. simpl.
      econstructor; [by rewrite qterms_subst_c|done|done|done|].
      case_decide; auto.
    - intros Σ t c y P Hc Hy HP IHP x v Hx Hv. simpl.
      constructor; [done|done|]. case_decide; auto.
    - intros Σ t c y P Hc Hy Hny HP IHP x v Hx Hv. simpl.
      constructor; [done|done|done|]. case_decide; auto.
    - intros Σ g1 g2 H1 IH1 H2 IH2 x v Hx Hv. simpl. constructor; auto.
  Qed.

  (* Receiving the fresh qubit [q] for the qubit variable [x]. *)
  Lemma wt_subst_q :
    (∀ Σ P, wt Σ P → ∀ x q, qvar x = true → QV x ∈ Σ → QN q ∉ Σ →
       wt ({[ QN q ]} ∪ (Σ ∖ {[ QV x ]})) (subst P x (VQubit q)))
    ∧ (∀ Σ g, gwt Σ g → ∀ x q, qvar x = true → QV x ∈ Σ → QN q ∉ Σ →
       gwt ({[ QN q ]} ∪ (Σ ∖ {[ QV x ]})) (gsubst g x (VQubit q))).
  Proof.
    apply wt_gwt_ind.
    - intros t c e Hc He x q Hx Hin Hq. set_solver.
    - intros t c e a Hc Ha x q Hx Hin Hq. simpl.
      apply elem_of_singleton in Hin. subst a.
      replace ({[QN q]} ∪ ({[QV x]} ∖ {[QV x]}) : gset qt) with ({[QN q]} : gset qt)
        by set_solver.
      econstructor; [done|]. rewrite qterm_subst_q, Ha by done. simpl.
      unfold ren. by rewrite decide_True.
    - intros Σ e P Q He HP IHP HQ IHQ x q Hx Hin Hq. simpl.
      constructor; auto. by rewrite classical_subst_q.
    - intros Σ1 Σ2 P Q Hd HP IHP HQ IHQ x q Hx Hin Hq. simpl.
      apply elem_of_union in Hin as [Hin|Hin].
      + replace ({[QN q]} ∪ ((Σ1 ∪ Σ2) ∖ {[QV x]}) : gset qt)
          with (({[QN q]} ∪ (Σ1 ∖ {[QV x]})) ∪ Σ2) by set_solver.
        rewrite ((proj1 wt_subst_absent) Σ2 Q HQ x (VQubit q)); [|done|set_solver].
        constructor; [set_solver|apply IHP; [done|done|set_solver]|done].
      + replace ({[QN q]} ∪ ((Σ1 ∪ Σ2) ∖ {[QV x]}) : gset qt)
          with (Σ1 ∪ ({[QN q]} ∪ (Σ2 ∖ {[QV x]}))) by set_solver.
        rewrite ((proj1 wt_subst_absent) Σ1 P HP x (VQubit q)); [|done|set_solver].
        constructor; [set_solver|done|apply IHQ; [done|done|set_solver]].
    - intros Σ P c HP IHP x q Hx Hin Hq. simpl. constructor; auto.
    - intros Σ g Hg IHg x q Hx Hin Hq. simpl. constructor; auto.
    - intros Σ es l Hql Hnd -> x q Hx Hin Hq. simpl. econstructor.
      + rewrite qterms_subst_q, Hql by done. done.
      + apply ren_NoDup; [done|]. intros Hl. apply Hq. by apply elem_of_list_to_set.
      + symmetry. apply ren_set_in. by apply elem_of_list_to_set in Hin.
    - intros. simpl. constructor.
    - intros Σ t P HP IHP x q Hx Hin Hq. simpl. constructor; auto.
    - intros Σ t t' P HP IHP x q Hx Hin Hq. simpl. constructor; auto.
    - intros Σ t E es l P Hql Hnd Hs HP IHP x q Hx Hin Hq. simpl.
      econstructor.
      + by rewrite qterms_subst_q, Hql.
      + apply ren_NoDup; [done|]. intros Hl. apply Hq, Hs. by apply elem_of_list_to_set.
      + by apply ren_set_sub.
      + auto.
    - intros Σ t M es y l P Hql Hnd Hs Hy HP IHP x q Hx Hin Hq. simpl.
      econstructor.
      + by rewrite qterms_subst_q, Hql.
      + apply ren_NoDup; [done|]. intros Hl. apply Hq, Hs. by apply elem_of_list_to_set.
      + by apply ren_set_sub.
      + done.
      + rewrite decide_False; [auto|congruence].
    - intros Σ t c y P Hc Hy HP IHP x q Hx Hin Hq. simpl.
      constructor; [done|done|]. rewrite decide_False; [auto|congruence].
    - intros Σ t c y P Hc Hy Hny HP IHP x q Hx Hin Hq. simpl.
      assert (Hyx : y ≠ x) by (intros ->; done).
      constructor; [done|done|set_solver|].
      rewrite decide_False; [|congruence].
      replace ({[QV y]} ∪ ({[QN q]} ∪ (Σ ∖ {[QV x]})) : gset qt)
        with ({[QN q]} ∪ (({[QV y]} ∪ Σ) ∖ {[QV x]})) by set_solver.
      apply IHP; [done|set_solver|set_solver].
    - intros Σ g1 g2 H1 IH1 H2 IH2 x q Hx Hin Hq. simpl. constructor; auto.
  Qed.

  (* ** Subject reduction *)

  Lemma qterm_eval e a v : qterm e = Some a → eval e = Some v → ∃ q, a = QN q ∧ v = VQubit q.
  Proof.
    destruct e as [y|[b|n|q]|e|e1 e2|e1 e2|e1 e2]; simpl; intros Ha Hv; try done.
    simplify_eq. eauto.
  Qed.

  Lemma qterms_eval es l qs : qterms es = Some l → eval_qubits es = Some qs → l = QN <$> qs.
  Proof.
    unfold qterms, eval_qubits. revert l qs. induction es as [|e es IH]; intros l qs Hl Hq.
    - simpl in *. inversion Hl; inversion Hq; done.
    - simpl in Hl, Hq.
      destruct (qterm e) as [a|] eqn:Ea; [|done].
      destruct (mapM qterm es) as [l'|] eqn:El; [|done].
      destruct (eval_qubit e) as [q|] eqn:Eq; [|done].
      destruct (mapM eval_qubit es) as [qs'|] eqn:Eqs; [|done].
      inversion Hl; inversion Hq; subst. simpl. f_equal; [|by apply IH].
      unfold eval_qubit in Eq. destruct (eval e) as [[]|] eqn:Ev; simplify_eq.
      by destruct (qterm_eval e a (VQubit q) Ea Ev) as (q' & -> & [= ->]).
  Qed.

  (* What a step does to the qubits owned: nothing for a silent step, an
      operation or a measurement (which only use owned qubits); an emission
      on a qubit channel gives the qubit away, a reception takes one. *)
  Definition sr_post (Σ : gset qt) (l : plbl) (P' : proc) : Prop :=
    match l with
    | LTau _ => wt Σ P'
    | LAct _ (AOp E qs) => list_to_set (QN <$> qs) ⊆ Σ ∧ wt Σ P'
    | LAct _ (AMeas M qs x) => list_to_set (QN <$> qs) ⊆ Σ ∧ qvar x = false ∧ wt Σ P'
    | LAct _ (AOut c v) =>
        if qchan c then ∃ q, v = VQubit q ∧ QN q ∈ Σ ∧ wt (Σ ∖ {[ QN q ]}) P'
        else vclass v ∧ wt Σ P'
    | LAct _ (AIn c v) =>
        if qchan c then ∀ q, v = VQubit q → QN q ∉ Σ → wt ({[ QN q ]} ∪ Σ) P'
        else vclass v → wt Σ P'
    end.

  Lemma move_l (Σ1 Σ2 : gset qt) a : a ∈ Σ1 → Σ1 ∪ Σ2 = (Σ1 ∖ {[a]}) ∪ ({[a]} ∪ Σ2).
  Proof.
    intros Ha. apply set_eq. intros b.
    rewrite !elem_of_union, elem_of_difference, elem_of_singleton.
    destruct (decide (b = a)); naive_solver.
  Qed.

  Lemma move_r (Σ1 Σ2 : gset qt) a : a ∈ Σ2 → Σ1 ∪ Σ2 = ({[a]} ∪ Σ1) ∪ (Σ2 ∖ {[a]}).
  Proof.
    intros Ha. apply set_eq. intros b.
    rewrite !elem_of_union, elem_of_difference, elem_of_singleton.
    destruct (decide (b = a)); naive_solver.
  Qed.

  Lemma wt_nil : wt ∅ (PG (GNil [])).
  Proof. constructor. by econstructor; [done|constructor|]. Qed.

  Lemma sr_guard Σ g l P' : gwt Σ g → gstep g l P' → sr_post Σ l P'.
  Proof.
    intros Hg Hs. revert Σ Hg.
    induction Hs as [t P|t t' P|t c x v P|t E es qs P Hq|t M es x qs P Hq
                    |g1 g2 l P' Hs IH|g1 g2 l P' Hs IH]; intros Σ Hg; simpl.
    - by inversion Hg.
    - by inversion Hg.
    - inversion Hg as [| | | | | |? ? ? ? ? Hc Hx HP|? ? ? ? ? Hc Hx Hn HP|]; subst.
      + rewrite Hc. intros Hv. by apply (proj1 wt_subst_c).
      + rewrite Hc. intros q -> Hq.
        replace ({[QN q]} ∪ Σ) with ({[QN q]} ∪ (({[QV x]} ∪ Σ) ∖ {[QV x]})) by set_solver.
        apply (proj1 wt_subst_q); [done|done|set_solver|set_solver].
    - inversion Hg as [| | | |? ? ? ? l ? Hl Hnd Hs HP| | | |]; subst.
      rewrite <- (qterms_eval es l qs Hl Hq). split; [done|done].
    - inversion Hg as [| | | | |? ? ? ? ? l ? Hl Hnd Hs Hx HP| | |]; subst.
      rewrite <- (qterms_eval es l qs Hl Hq). split_and!; done.
    - inversion Hg; subst. by apply IH.
    - inversion Hg; subst. by apply IH.
  Qed.

  Theorem subject_reduction Σ P l P' : wt Σ P → pstep P l P' → sr_post Σ l P'.
  Proof.
    intros HP Hs. revert Σ HP.
    induction Hs as [g l P' Hg|t c e v He|e P Q l P' He Hs IH|e P Q l Q' He Hs IH
                    |P Q l P' Hs IH|P Q l Q' Hs IH
                    |P Q t t' c v P' Q' Hs1 IH1 Hs2 IH2|P Q t t' c v P' Q' Hs1 IH1 Hs2 IH2
                    |P d l P' Hd Hs IH]; intros Σ HP.
    - inversion HP; subst. by eapply sr_guard.
    - simpl. inversion HP as [? ? ? Hc He'|? ? ? a Hc Ha| | | |]; subst.
      + rewrite Hc. split; [by eapply classical_eval|apply wt_nil].
      + rewrite Hc. destruct (qterm_eval e a v Ha He) as (q & -> & ->).
        exists q. split_and!; [done|set_solver|].
        replace ({[QN q]} ∖ {[QN q]} : gset qt) with (∅ : gset qt) by set_solver.
        apply wt_nil.
    - inversion HP; subst. by apply IH.
    - inversion HP; subst. by apply IH.
    - inversion HP as [| | |Σ1 Σ2 ? ? Hd H1 H2| |]; subst.
      specialize (IH Σ1 H1). destruct l as [s|t [c v|c v|E qs|M qs x]]; simpl in *.
      + constructor; auto.
      + destruct (qchan c).
        * destruct IH as (q & -> & Hq & HP').
          exists q. split_and!; [done|set_solver|].
          replace ((Σ1 ∪ Σ2) ∖ {[QN q]}) with ((Σ1 ∖ {[QN q]}) ∪ Σ2) by set_solver.
          constructor; [set_solver|done|done].
        * destruct IH as [Hv HP']. split; [done|]. by constructor.
      + destruct (qchan c).
        * intros q -> Hq. replace ({[QN q]} ∪ (Σ1 ∪ Σ2)) with (({[QN q]} ∪ Σ1) ∪ Σ2)
            by set_solver.
          constructor; [set_solver|apply IH; [done|set_solver]|done].
        * intros Hv. constructor; auto.
      + destruct IH as [Hq HP']. split; [set_solver|]. by constructor.
      + destruct IH as (Hq & Hx & HP'). split_and!; [set_solver|done|]. by constructor.
    - inversion HP as [| | |Σ1 Σ2 ? ? Hd H1 H2| |]; subst.
      specialize (IH Σ2 H2). destruct l as [s|t [c v|c v|E qs|M qs x]]; simpl in *.
      + constructor; auto.
      + destruct (qchan c).
        * destruct IH as (q & -> & Hq & HQ').
          exists q. split_and!; [done|set_solver|].
          replace ((Σ1 ∪ Σ2) ∖ {[QN q]}) with (Σ1 ∪ (Σ2 ∖ {[QN q]})) by set_solver.
          constructor; [set_solver|done|done].
        * destruct IH as [Hv HQ']. split; [done|]. by constructor.
      + destruct (qchan c).
        * intros q -> Hq. replace ({[QN q]} ∪ (Σ1 ∪ Σ2)) with (Σ1 ∪ ({[QN q]} ∪ Σ2))
            by set_solver.
          constructor; [set_solver|done|apply IH; [done|set_solver]].
        * intros Hv. constructor; auto.
      + destruct IH as [Hq HQ']. split; [set_solver|]. by constructor.
      + destruct IH as (Hq & Hx & HQ'). split_and!; [set_solver|done|]. by constructor.
    - inversion HP as [| | |Σ1 Σ2 ? ? Hd H1 H2| |]; subst. simpl.
      specialize (IH1 Σ1 H1). specialize (IH2 Σ2 H2). simpl in IH1, IH2.
      destruct (qchan c).
      + destruct IH1 as (q & -> & Hq & HP').
        rewrite (move_l Σ1 Σ2 (QN q) Hq).
        constructor; [set_solver|done|apply IH2; [done|set_solver]].
      + destruct IH1 as [Hv HP']. constructor; auto.
    - inversion HP as [| | |Σ1 Σ2 ? ? Hd H1 H2| |]; subst. simpl.
      specialize (IH1 Σ1 H1). specialize (IH2 Σ2 H2). simpl in IH1, IH2.
      destruct (qchan c).
      + destruct IH2 as (q & -> & Hq & HQ').
        rewrite (move_r Σ1 Σ2 (QN q) Hq).
        constructor; [set_solver|apply IH1; [done|set_solver]|done].
      + destruct IH2 as [Hv HQ']. constructor; auto.
    - inversion HP; subst. specialize (IH Σ ltac:(done)).
      destruct l as [s|t [c v|c v|E qs|M qs x]]; simpl in *.
      + by constructor.
      + destruct (qchan c).
        * destruct IH as (q & -> & Hq & HP'). exists q. split_and!; [done|done|by constructor].
        * destruct IH as [Hv HP']. split; [done|by constructor].
      + destruct (qchan c).
        * intros q -> Hq. constructor. by apply IH.
        * intros Hv. constructor. by apply IH.
      + destruct IH as [Hq HP']. split; [done|by constructor].
      + destruct IH as (Hq & Hx & HP'). split_and!; [done|done|by constructor].
  Qed.

  (* The silent steps of a program keep its qubits: Theorem 4.5 of the
      paper, for programs. *)
  Corollary subject_reduction_tau Σ P s P' : wt Σ P → pstep P (LTau s) P' → wt Σ P'.
  Proof. apply subject_reduction. Qed.
End Typing.
(* end hide *)
