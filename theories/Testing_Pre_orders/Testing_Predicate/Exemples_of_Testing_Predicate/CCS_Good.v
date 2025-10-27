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
From Must Require Import gLts InputOutputActions GeneralizeLtsOutputs Must CCSInstance Testing_Predicate.


Inductive good_CCS : proc -> Prop :=
| good_success : good_CCS ①
| good_par : forall p q, good_CCS p \/ good_CCS q -> good_CCS (p ‖ q)
| good_choice : forall p q, good_CCS (g p) \/ good_CCS (g q) -> good_CCS (p + q).

#[global] Hint Constructors good_CCS:ccs.

#[global] Instance good_decidable e : Decision $ good_CCS e.
Proof.
  dependent induction e; try (now right; inversion 1).
  - destruct IHe1; destruct IHe2; try (now left; eauto with ccs).
    right. inversion 1; naive_solver.
  - dependent induction g; try (now right; inversion 1); try (now left; eauto with ccs).
    destruct IHg1; destruct IHg2; try (now left; eauto with ccs).
    right. inversion 1; naive_solver.
Qed.

Lemma good_preserved_by_cgr_step p q : good_CCS p -> p ≡ q -> good_CCS q.
Proof.
  intros happy cong.
  dependent induction cong; try (now (inversion happy; subst; eauto)).
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
  + dependent destruction happy. destruct H. eapply good_choice. left; eauto.
    eapply good_choice. right. eauto.
Qed.

Lemma good_preserved_by_cgr p q : good_CCS p -> p ≡* q -> good_CCS q.
Proof.
  intros hg hcgr.
  dependent induction hcgr; [eapply good_preserved_by_cgr_step|]; eauto.
Qed.


#[global] Program Instance CCS_Good : @Testing_Predicate proc (ExtAct Channel) good_CCS gLabel_b CCS_ggLts CCS_ggLtsEq.
Next Obligation. 
 intros. eapply good_preserved_by_cgr; eassumption.
Qed.
Next Obligation.
 intros. unfold non_blocking in H.  simpl in *. inversion H.
Qed.
Next Obligation.
 intros. unfold non_blocking in H.  simpl in *. inversion H.
Qed.