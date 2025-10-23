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

From Coq.Program Require Import Equality.
From stdpp Require Import countable decidable.
From Must Require Import gLts InputOutputActions GeneralizeLtsOutputs Must VACCS_Instance Testing_Predicate.


Inductive good_VACCS : proc -> Prop :=
| good_success : good_VACCS ①
| good_par : forall p q, good_VACCS p \/ good_VACCS q -> good_VACCS (p ‖ q)
| good_choice : forall p q, good_VACCS (g p) \/ good_VACCS (g q) -> good_VACCS (p + q)
| good_if_true : forall E p q, good_VACCS p -> Eval_Eq E = Some true -> good_VACCS (If E Then p Else q)
| good_if_false : forall E p q, good_VACCS q -> Eval_Eq E = Some false -> good_VACCS (If E Then p Else q).

#[global] Hint Constructors good_VACCS:ccs.

#[global] Instance good_decidable e : Decision $ good_VACCS e.
Proof.
  dependent induction e; try (now right; inversion 1).
  - destruct IHe1; destruct IHe2; try (now left; eauto with ccs).
    right. inversion 1; naive_solver.
  - case_eq (Eval_Eq e1); intros.
    + destruct b.
      * destruct IHe1; destruct IHe2; try (now left; eauto with ccs).
        right. inversion 1; naive_solver.
        right. inversion 1; naive_solver.
      * destruct IHe1; destruct IHe2; try (now left; eauto with ccs).
        right. inversion 1; naive_solver.
        right. inversion 1; naive_solver.
    + right. inversion 1; naive_solver.
  - dependent induction g; try (now right; inversion 1); try (now left; eauto with ccs).
    destruct IHg1; destruct IHg2; try (now left; eauto with ccs).
    right. inversion 1; naive_solver.
Qed.

Lemma good_preserved_by_cgr_step p q : good_VACCS p -> p ≡ q -> good_VACCS q.
Proof.
  intros happy cong.
  dependent induction cong; try (now (inversion happy; subst; eauto)).
  + inversion happy; subst; eauto. rewrite H in H4. dependent destruction H4.
  + eapply good_if_true; eauto.
  + inversion happy; subst; eauto. rewrite H in H4. dependent destruction H4.
  + eapply good_if_false; eauto.
  + inversion happy; subst; eauto. destruct H0; eauto. dependent destruction H.
  + eapply good_par. left; eauto.
  + dependent destruction happy. eapply good_par.  destruct H; eauto.
  + dependent destruction happy. dependent destruction H.
    dependent destruction H. eapply good_par. destruct H; eauto. right. eapply good_par; eauto.
    eapply good_par. right. eapply good_par; eauto.
  + dependent destruction happy. dependent destruction H.
    eapply good_par; eauto. left. eapply good_par; eauto.
    dependent destruction H. eapply good_par. destruct H; eauto. left. eapply good_par; eauto.
  + dependent destruction happy ;eauto. destruct H; eauto. inversion H.
  + eapply good_choice. left; eauto.
  + dependent destruction happy ;eauto. eapply good_choice. destruct H; eauto.
  + dependent destruction happy ;eauto. dependent destruction H ;eauto.
    dependent destruction H ;eauto. eapply good_choice; eauto. destruct H;eauto.
    right. eapply good_choice; eauto. eapply good_choice; eauto. right. eapply good_choice; eauto.
  + dependent destruction happy ;eauto. dependent destruction H ;eauto.
    eapply good_choice; eauto. left. eapply good_choice; eauto.
    dependent destruction H ;eauto. eapply good_choice; eauto. destruct H;eauto.
    left. eapply good_choice; eauto.
  + dependent destruction happy. destruct H. eapply good_par. left. eauto.
    eapply good_par. right. eauto.
  + dependent destruction happy. eapply good_if_true; eauto.
    eapply good_if_false; eauto.
  + dependent destruction happy. eapply good_if_true; eauto.
    eapply good_if_false; eauto.
  + dependent destruction happy. destruct H. eapply good_choice. left; eauto.
    eapply good_choice. right. eauto.
Qed.

Lemma good_preserved_by_cgr p q : good_VACCS p -> p ≡* q -> good_VACCS q.
Proof.
  intros hg hcgr.
  dependent induction hcgr; [eapply good_preserved_by_cgr_step|]; eauto.
Qed.

Lemma good_preserved_by_non_bloking_actions p q a : good_VACCS p -> lts p (a !) q -> good_VACCS q.
Proof.
  intros hhp hl. destruct a.
  eapply TransitionShapeForOutputSimplified in hl.
  eapply (good_preserved_by_cgr p ((c ! d • 𝟘) ‖ q)) in hhp; eauto with ccs.
  inversion hhp; subst. destruct H0; eauto with ccs. inversion H.
Qed.

Lemma good_preserved_by_non_bloking_actions_converse p q a : lts p (a !) q -> good_VACCS q -> good_VACCS p.
Proof.
  intros hl hhq. destruct a.
  eapply TransitionShapeForOutputSimplified in hl.
  eapply good_preserved_by_cgr.
  eapply good_par. right.
  eauto with ccs. symmetry. eauto with ccs.
Qed.

#[global] Program Instance VACCS_Good : @Testing_Predicate proc (ExtAct TypeOfActions) good_VACCS gLabel_nb VACCS_ggLts VACCS_ggLtsEq.
Next Obligation. 
 intros. eapply good_preserved_by_cgr; eassumption.
Qed.
Next Obligation.
 intros. unfold non_blocking in H.  simpl in *.
 destruct H as (a & eq); subst.
 eapply good_preserved_by_non_bloking_actions; eassumption.
Qed.
Next Obligation.
  intros. unfold non_blocking in H. simpl in *.
  destruct H as (a & eq); subst.
  eapply good_preserved_by_non_bloking_actions_converse; eassumption.
Qed.


