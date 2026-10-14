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
(* * lqCCS: computing the successors of a program

    The program LTS [pstep] labels its steps with schedulers.  Forgetting
    them ([erase]), the successors of a program for a given label are
    finitely many, and computed by [succ] ([succ_spec]); the outputs of a
    program are listed by [prog_outs] ([prog_outs_spec]).  This is what makes the
    LTSs of [lqCCS_LTS.v] decidable. *)
(* end hide *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list sets.
From TestingTheory Require Import lqCCS_Syntax lqCCS_Program.
(* begin hide *)
(* ** Labels without schedulers *)

Inductive ulbl : Type :=
| UTau
| UAct (a : pact).

#[global] Instance ulbl_eq_dec : EqDecision ulbl.
Proof. solve_decision. Defined.

Definition erase (l : plbl) : ulbl :=
  match l with LTau _ => UTau | LAct _ a => UAct a end.

Definition on_chan_u (c : chan) (u : ulbl) : Prop :=
  match u with UAct (AOut c' _) | UAct (AIn c' _) => c' = c | _ => False end.

#[global] Instance on_chan_u_dec c u : Decision (on_chan_u c u).
Proof. destruct u as [|[]]; simpl; apply _. Defined.

Lemma on_chan_erase c l : on_chan c l ↔ on_chan_u c (erase l).
Proof.
  unfold on_chan. split.
  - intros (t & v & [->| ->]); done.
  - destruct l as [s|t [c' v|c' v| |]]; simpl; try done; intros ->; eauto.
Qed.

(* ** Outputs (guards never output) *)

Fixpoint prog_outs (P : proc) : list (chan * val * proc) :=
  match P with
  | PSend _ c e => match eval e with Some v => [(c, v, PG (GNil []))] | None => [] end
  | PIte e P Q =>
      match eval e with
      | Some (VBool true) => prog_outs P
      | Some (VBool false) => prog_outs Q
      | _ => []
      end
  | PPar P Q =>
      ((λ '(c, v, P'), (c, v, PPar P' Q)) <$> prog_outs P)
      ++ ((λ '(c, v, Q'), (c, v, PPar P Q')) <$> prog_outs Q)
  | PRes P c => (λ '(c', v, P'), (c', v, PRes P' c)) <$> filter (λ '(c', _, _), c' ≠ c) (prog_outs P)
  | PG _ => []
  end.

Lemma prog_outs_spec P c v P' :
  (c, v, P') ∈ prog_outs P ↔ ∃ t, pstep P (LAct t (AOut c v)) P'.
Proof.
  revert P'. induction P as [t c0 e|e P IHP Q IHQ|P IHP Q IHQ|P IHP c0|g]; intros P0; simpl.
  - split.
    + destruct (eval e) eqn:He; [|set_solver]. intros Hin.
      apply list_elem_of_singleton in Hin; simplify_eq. eexists. by constructor.
    + intros (t' & Hs). inversion Hs; subst.
      match goal with He : eval _ = Some _ |- _ => rewrite He end. set_solver.
  - destruct (eval e) as [[[]| |]|] eqn:He.
    + rewrite IHP. split.
      * intros (t & Hs). eexists. by apply ps_iteT.
      * intros (t & Hs). inversion Hs; subst; [by eexists|congruence].
    + rewrite IHQ. split.
      * intros (t & Hs). eexists. by apply ps_iteF.
      * intros (t & Hs). inversion Hs; subst; [congruence|by eexists].
    + split; [set_solver|]. intros (t & Hs). inversion Hs; congruence.
    + split; [set_solver|]. intros (t & Hs). inversion Hs; congruence.
    + split; [set_solver|]. intros (t & Hs). inversion Hs; congruence.
  - rewrite elem_of_app, !list_elem_of_fmap. split.
    + intros [([[c' v'] P'] & Heq & Hin)|([[c' v'] Q'] & Heq & Hin)]; simplify_eq.
      * apply IHP in Hin as (t & Hs). exists t. by apply ps_parL.
      * apply IHQ in Hin as (t & Hs). exists t. by apply ps_parR.
    + intros (t & Hs). inversion Hs; subst.
      * left. exists (c, v, P'). split; [done|]. apply IHP. eauto.
      * right. exists (c, v, Q'). split; [done|]. apply IHQ. eauto.
  - rewrite list_elem_of_fmap. split.
    + intros ([[c' v'] P'] & Heq & Hin). simplify_eq.
      apply list_elem_of_filter in Hin as [Hne Hin]. apply IHP in Hin as (t & Hs).
      exists t. apply ps_res; [|done]. intros (?&?&[[=]|[=]]). congruence.
    + intros (t & Hs). inversion Hs; subst. exists (c, v, P'). split; [done|].
      apply list_elem_of_filter. split.
      * intros Heq. subst. match goal with Hn : ¬ on_chan _ _ |- _ => apply Hn end.
        do 2 eexists. by left.
      * apply IHP. eauto.
  - split; [set_solver|]. intros (t & Hs). inversion Hs; subst. exfalso. by eapply gstep_not_out.
Qed.

(* ** Successors for a label *)

Fixpoint gsucc (g : guard) (u : ulbl) : list proc :=
  match g with
  | GPre α P0 =>
      match α, u with
      | PTau _, UTau | PTauPair _ _, UTau => [P0]
      | PRecv _ c x, UAct (AIn c' v) =>
          if decide (c = c') then [subst P0 x v] else []
      | POp _ E es, UAct (AOp E' qs) =>
          if decide (E = E' ∧ eval_qubits es = Some qs) then [P0] else []
      | PMeas _ M es x, UAct (AMeas M' qs x') =>
          if decide (M = M' ∧ x = x' ∧ eval_qubits es = Some qs) then [P0] else []
      | _, _ => []
      end
  | GSum g1 g2 => gsucc g1 u ++ gsucc g2 u
  | _ => []
  end.

Fixpoint succ (P : proc) (u : ulbl) {struct P} : list proc :=
  match P with
  | PSend _ c e =>
      match u with
      | UAct (AOut c' v) => if decide (c = c' ∧ eval e = Some v) then [PG (GNil [])] else []
      | _ => []
      end
  | PIte e P Q =>
      match eval e with
      | Some (VBool true) => succ P u
      | Some (VBool false) => succ Q u
      | _ => []
      end
  | PPar P Q =>
      ((λ P', PPar P' Q) <$> succ P u)
      ++ ((λ Q', PPar P Q') <$> succ Q u)
      ++ match u with
         | UTau =>
             (prog_outs P ≫= λ '(c, v, P'), (λ Q', PPar P' Q') <$> succ Q (UAct (AIn c v)))
             ++ (prog_outs Q ≫= λ '(c, v, Q'), (λ P', PPar P' Q') <$> succ P (UAct (AIn c v)))
         | _ => []
         end
  | PRes P c => if decide (on_chan_u c u) then [] else (λ P', PRes P' c) <$> succ P u
  | PG g => gsucc g u
  end.

Definition ustep (P : proc) (u : ulbl) (P' : proc) : Prop :=
  ∃ l, erase l = u ∧ pstep P l P'.

Lemma gsucc_spec g u P' : P' ∈ gsucc g u ↔ ∃ l, erase l = u ∧ gstep g l P'.
Proof.
  revert u P'. induction g as [es| |α P|g1 IH1 g2 IH2]; intros u P0; simpl.
  - split; [set_solver|]. intros (l & _ & Hs). inversion Hs.
  - split; [set_solver|]. intros (l & _ & Hs). inversion Hs.
  - split.
    + destruct α, u as [|[]]; try set_solver; repeat case_decide; try set_solver;
        intros Hin; apply list_elem_of_singleton in Hin as ->.
      * by exists (LTau (STag t)); split; [|constructor].
      * by exists (LTau (SPair t t')); split; [|constructor].
      * subst. exists (LAct t (AIn c0 v)). split; [done|]. constructor.
      * destruct H as [-> He]. exists (LAct t (AOp E0 qs)). split; [done|]. by constructor.
      * destruct H as (-> & -> & He). exists (LAct t (AMeas M0 qs x0)). split; [done|].
        by constructor.
    + intros (l & <- & Hs). inversion Hs; subst; simpl; try set_solver;
        rewrite decide_True; try set_solver.
  - rewrite elem_of_app, IH1, IH2. split.
    + intros [(l & <- & Hs)|(l & <- & Hs)]; exists l; (split; [done|]);
        [by apply gs_sumL|by apply gs_sumR].
    + intros (l & <- & Hs). inversion Hs; subst; [left|right]; eauto.
Qed.

Lemma succ_spec P u P' : P' ∈ succ P u ↔ ustep P u P'.
Proof.
  unfold ustep. revert u P'.
  induction P as [t c0 e|e P IHP Q IHQ|P IHP Q IHQ|P IHP c0|g]; intros u P0; simpl.
  - split.
    + destruct u as [|[c' v| | |]]; try set_solver. case_decide as Hd; [|set_solver].
      destruct Hd as [-> He]. intros Hin. apply list_elem_of_singleton in Hin as ->.
      exists (LAct t (AOut c' v)). split; [done|]. by constructor.
    + intros (l & <- & Hs). inversion Hs; subst. simpl. rewrite decide_True; set_solver.
  - destruct (eval e) as [[[]| |]|] eqn:He.
    + rewrite IHP. split.
      * intros (l & <- & Hs). exists l. split; [done|]. by apply ps_iteT.
      * intros (l & <- & Hs). inversion Hs; subst; [by exists l|congruence].
    + rewrite IHQ. split.
      * intros (l & <- & Hs). exists l. split; [done|]. by apply ps_iteF.
      * intros (l & <- & Hs). inversion Hs; subst; [congruence|by exists l].
    + split; [set_solver|]. intros (l & _ & Hs). inversion Hs; congruence.
    + split; [set_solver|]. intros (l & _ & Hs). inversion Hs; congruence.
    + split; [set_solver|]. intros (l & _ & Hs). inversion Hs; congruence.
  - rewrite !elem_of_app. split.
    + intros [Hin|[Hin|Hin]].
      * apply list_elem_of_fmap in Hin as (P' & -> & Hin).
        apply IHP in Hin as (l & <- & Hs). exists l. split; [done|]. by apply ps_parL.
      * apply list_elem_of_fmap in Hin as (Q' & -> & Hin).
        apply IHQ in Hin as (l & <- & Hs). exists l. split; [done|]. by apply ps_parR.
      * destruct u; [|set_solver]. apply elem_of_app in Hin as [Hin|Hin];
          apply list_elem_of_bind in Hin as ([[c v] X] & Hin & Hout);
          apply list_elem_of_fmap in Hin as (Y & -> & Hin).
        -- apply prog_outs_spec in Hout as (t & Hs). apply IHQ in Hin as (l & El & Hs').
           destruct l as [|t' a]; simpl in El; simplify_eq.
           exists (LTau (SPair t t')). split; [done|]. by eapply ps_syncL.
        -- apply prog_outs_spec in Hout as (t & Hs). apply IHP in Hin as (l & El & Hs').
           destruct l as [|t' a]; simpl in El; simplify_eq.
           exists (LTau (SPair t' t)). split; [done|]. by eapply ps_syncR.
    + intros (l & <- & Hs). inversion Hs; subst.
      * left. apply list_elem_of_fmap. eexists. split; [done|]. apply IHP. eauto.
      * right; left. apply list_elem_of_fmap. eexists. split; [done|]. apply IHQ. eauto.
      * right; right. simpl. apply elem_of_app. left.
        apply list_elem_of_bind. exists (c, v, P'). split.
        -- apply list_elem_of_fmap. eexists. split; [done|]. apply IHQ.
           exists (LAct t' (AIn c v)). done.
        -- apply prog_outs_spec. eauto.
      * right; right. simpl. apply elem_of_app. right.
        apply list_elem_of_bind. exists (c, v, Q'). split.
        -- apply list_elem_of_fmap. eexists. split; [done|]. apply IHP.
           exists (LAct t (AIn c v)). done.
        -- apply prog_outs_spec. eauto.
  - split.
    + case_decide as Hd; [set_solver|]. intros Hin.
      apply list_elem_of_fmap in Hin as (P' & -> & Hin). apply IHP in Hin as (l & <- & Hs).
      exists l. split; [done|]. apply ps_res; [|done]. by rewrite on_chan_erase.
    + intros (l & <- & Hs). inversion Hs; subst.
      rewrite decide_False by (by rewrite <- on_chan_erase).
      apply list_elem_of_fmap. eexists. split; [done|]. apply IHP. eauto.
  - rewrite gsucc_spec. split.
    + intros (l & <- & Hs). exists l. split; [done|]. by constructor.
    + intros (l & <- & Hs). inversion Hs; subst. eauto.
Qed.

#[global] Instance ustep_dec P u P' : Decision (ustep P u P').
Proof.
  destruct (decide (P' ∈ succ P u)) as [H|H];
    [left; by apply succ_spec | right; by rewrite <- succ_spec].
Defined.

(* ** Actions other than receptions

    Outputs, superoperators and measurements: finitely many, listed with
    their targets. *)

Definition not_in (a : pact) : Prop := match a with AIn _ _ => False | _ => True end.

#[global] Instance not_in_dec a : Decision (not_in a).
Proof. destruct a; simpl; apply _. Defined.

Definition prefix_act (α : prefix) : option pact :=
  match α with
  | POp _ E es => (λ qs, AOp E qs) <$> eval_qubits es
  | PMeas _ M es x => (λ qs, AMeas M qs x) <$> eval_qubits es
  | _ => None
  end.

Fixpoint gacts (g : guard) : list (pact * proc) :=
  match g with
  | GPre α P0 => match prefix_act α with Some a => [(a, P0)] | None => [] end
  | GSum g1 g2 => gacts g1 ++ gacts g2
  | _ => []
  end.

Fixpoint acts (P : proc) : list (pact * proc) :=
  match P with
  | PSend _ c e => match eval e with Some v => [(AOut c v, PG (GNil []))] | None => [] end
  | PIte e P Q =>
      match eval e with
      | Some (VBool true) => acts P
      | Some (VBool false) => acts Q
      | _ => []
      end
  | PPar P Q =>
      ((λ '(a, P'), (a, PPar P' Q)) <$> acts P) ++ ((λ '(a, Q'), (a, PPar P Q')) <$> acts Q)
  | PRes P c =>
      (λ '(a, P'), (a, PRes P' c)) <$> filter (λ '(a, _), ¬ on_chan_u c (UAct a)) (acts P)
  | PG g => gacts g
  end.

Lemma gacts_spec g a P' :
  (a, P') ∈ gacts g ↔ not_in a ∧ ∃ t, gstep g (LAct t a) P'.
Proof.
  revert P'. induction g as [es| |α P|g1 IH1 g2 IH2]; intros P0; simpl.
  - split; [set_solver|]. intros (_ & t & Hs). inversion Hs.
  - split; [set_solver|]. intros (_ & t & Hs). inversion Hs.
  - split.
    + destruct α; simpl; try set_solver;
        destruct (eval_qubits es) as [qs|] eqn:He; simpl; try set_solver;
        intros Hin; apply list_elem_of_singleton in Hin; simplify_eq;
        (split; [done|]); eexists; by constructor.
    + intros (Hni & t' & Hs). inversion Hs; subst; simpl; try done;
        match goal with He : eval_qubits _ = Some _ |- _ => rewrite He end; set_solver.
  - rewrite elem_of_app, IH1, IH2. split.
    + intros [(Hni & t & Hs)|(Hni & t & Hs)]; (split; [done|]); eexists;
        [by apply gs_sumL|by apply gs_sumR].
    + intros (Hni & t & Hs). inversion Hs; subst; [left|right]; eauto.
Qed.

Lemma acts_spec P a P' :
  (a, P') ∈ acts P ↔ not_in a ∧ ∃ t, pstep P (LAct t a) P'.
Proof.
  revert P'. induction P as [t c0 e|e P IHP Q IHQ|P IHP Q IHQ|P IHP c0|g]; intros P0; simpl.
  - split.
    + destruct (eval e) eqn:He; [|set_solver]. intros Hin.
      apply list_elem_of_singleton in Hin; simplify_eq. split; [done|].
      eexists. by constructor.
    + intros (_ & t' & Hs). inversion Hs; subst.
      match goal with He : eval _ = Some _ |- _ => rewrite He end. set_solver.
  - destruct (eval e) as [[[]| |]|] eqn:He.
    + rewrite IHP. split.
      * intros (Hni & t & Hs). split; [done|]. eexists. by apply ps_iteT.
      * intros (Hni & t & Hs). split; [done|]. inversion Hs; subst; [by eexists|congruence].
    + rewrite IHQ. split.
      * intros (Hni & t & Hs). split; [done|]. eexists. by apply ps_iteF.
      * intros (Hni & t & Hs). split; [done|]. inversion Hs; subst; [congruence|by eexists].
    + split; [set_solver|]. intros (_ & t & Hs). inversion Hs; congruence.
    + split; [set_solver|]. intros (_ & t & Hs). inversion Hs; congruence.
    + split; [set_solver|]. intros (_ & t & Hs). inversion Hs; congruence.
  - rewrite elem_of_app, !list_elem_of_fmap. split.
    + intros [([a' P'] & Heq & Hin)|([a' Q'] & Heq & Hin)]; simplify_eq.
      * apply IHP in Hin as (Hni & t & Hs). split; [done|]. exists t.
        by apply ps_parL.
      * apply IHQ in Hin as (Hni & t & Hs). split; [done|]. exists t.
        by apply ps_parR.
    + intros (Hni & t & Hs). inversion Hs; subst.
      * left. exists (a, P'). split; [done|]. apply IHP. eauto.
      * right. exists (a, Q'). split; [done|]. apply IHQ. eauto.
  - rewrite list_elem_of_fmap. split.
    + intros ([a' P'] & Heq & Hin). simplify_eq.
      apply list_elem_of_filter in Hin as [Hne Hin]. apply IHP in Hin as (Hni & t & Hs).
      split; [done|]. exists t. apply ps_res; [|done]. by rewrite on_chan_erase.
    + intros (Hni & t & Hs). inversion Hs; subst. exists (a, P'). split; [done|].
      apply list_elem_of_filter. split.
      * by rewrite <- (on_chan_erase c0 (LAct t a)).
      * apply IHP. eauto.
  - rewrite gacts_spec. split.
    + intros (Hni & t & Hs). split; [done|]. exists t. by constructor.
    + intros (Hni & t & Hs). split; [done|]. inversion Hs; subst. eauto.
Qed.
(* end hide *)
