(* begin hide *)
From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base countable list sets.
From TestingTheory Require Import ActTau InputOutputActions VACCS.Language.LTS VACCS.Helper.Atom_Swap.

Section VACCS_Divergence.

Context `{VP : VACCS_Parameters}.

Fixpoint act_var (x : nat) (p : proc) : bool :=
  match p with
  | p1 ‖ p2 => act_var x p1 || act_var x p2
  | pr_var y => bool_decide (x = y)
  | rec y • p' => if decide (x = y) then false else act_var x p'
  | If C Then P1 Else P2 => match (Eval_Eq 0 C) with
                            | Some true => act_var x P1
                            | Some false => act_var x P2
                            | None => false
                            end
  | ν p' => act_var x p'
  | g gp => act_var_g x gp
  | _ => false
  end

with act_var_g (x : nat) (gp : gproc) : bool :=
  match gp with
  | 𝛕 • p => act_var x p
  | g1 + g2 => act_var_g x g1 || act_var_g x g2
  | _ => false
  end.

Fixpoint act_div (p : proc) : bool :=
  match p with
  | p1 ‖ p2 => act_div p1 || act_div p2
  | rec y • p' => act_var y p' || act_div p'
  | If C Then P1 Else P2 => match (Eval_Eq 0 C) with
                            | Some true => act_div P1
                            | Some false => act_div P2
                            | None => false
                            end
  | ν p' => act_div p'
  | g gp => act_div_g gp
  | _ => false
  end

with act_div_g (gp : gproc) : bool :=
  match gp with
  | 𝛕 • p => act_div p
  | g1 + g2 => act_div_g g1 || act_div_g g2
  | _ => false
  end.

Lemma act_NewVarC :
  (∀ P k, (∀ x, act_var x (NewVarC k P) = act_var x P) ∧ act_div (NewVarC k P) = act_div P) ∧
  (∀ G k, (∀ x, act_var_g x (gNewVarC k G) = act_var_g x G) ∧ act_div_g (gNewVarC k G) = act_div_g G).
Proof.
  apply vaccs_proc_ind'; simpl; intros.
  - destruct (H k) as [h1 h2], (H0 k) as [h3 h4]. split; [intros x; by rewrite h1, h3 | by rewrite h2, h4].
  - split; reflexivity.
  - destruct (H k) as [h1 h2]. split; [intros x; by rewrite h1 | by rewrite h1, h2].
  - destruct (H k) as [h1 h2], (H0 k) as [h3 h4].
    split; [intros x; by rewrite h1, h3 | by rewrite h2, h4].
  - split; reflexivity.
  - exact (H (S k)).
  - exact (H k).
  - split; reflexivity.
  - split; reflexivity.
  - split; reflexivity.
  - exact (H k).
  - destruct (H k) as [h1 h2], (H0 k) as [h3 h4]. split; [intros x; by rewrite h1, h3 | by rewrite h2, h4].
Qed.

Lemma act_var_subst x y (hxy : x ≠ y) :
  (∀ P R, act_var x P = true → act_var x (pr_subst y P R) = true) ∧
  (∀ G R, act_var_g x G = true → act_var_g x (gpr_subst y G R) = true).
Proof.
  apply vaccs_proc_ind'; simpl; intros.
  - apply orb_true_iff in H1 as [h | h]; apply orb_true_iff; [left | right]; eauto.
  - apply bool_decide_eq_true in H as ->. rewrite decide_False by congruence. simpl.
    by apply bool_decide_eq_true.
  - destruct (decide (x = n)); [discriminate |].
    destruct (decide (y = n)); simpl; rewrite decide_False by congruence; eauto.
  - destruct (Eval_Eq 0 e) as [[] |]; eauto.
  - discriminate.
  - eauto.
  - eauto.
  - discriminate.
  - discriminate.
  - discriminate.
  - eauto.
  - apply orb_true_iff in H1 as [h | h]; apply orb_true_iff; [left | right]; eauto.
Qed.

Lemma act_div_subst y :
  (∀ P R, act_div P = true → act_div (pr_subst y P R) = true) ∧
  (∀ G R, act_div_g G = true → act_div_g (gpr_subst y G R) = true).
Proof.
  apply vaccs_proc_ind'; simpl; intros.
  - apply orb_true_iff in H1 as [h | h]; apply orb_true_iff; [left | right]; eauto.
  - discriminate.
  - destruct (decide (y = n)); simpl; [exact H0 |].
    apply orb_true_iff in H0 as [h | h]; apply orb_true_iff; [left | right].
    + apply (proj1 (act_var_subst n y (not_eq_sym n0))). exact h.
    + eauto.
  - destruct (Eval_Eq 0 e) as [[] |]; eauto.
  - discriminate.
  - eauto.
  - eauto.
  - discriminate.
  - discriminate.
  - discriminate.
  - eauto.
  - apply orb_true_iff in H1 as [h | h]; apply orb_true_iff; [left | right]; eauto.
Qed.

Lemma act_var_subst_div x :
  (∀ P R, act_var x P = true → act_div R = true → act_div (pr_subst x P R) = true) ∧
  (∀ G R, act_var_g x G = true → act_div R = true → act_div_g (gpr_subst x G R) = true).
Proof.
  apply vaccs_proc_ind'; simpl; intros.
  - apply orb_true_iff in H1 as [h | h]; apply orb_true_iff; [left | right]; eauto.
  - apply bool_decide_eq_true in H as ->. rewrite decide_True by reflexivity. exact H0.
  - destruct (decide (x = n)); [discriminate |]. simpl.
    apply orb_true_iff. right. eauto.
  - destruct (Eval_Eq 0 e) as [[] |]; eauto.
  - discriminate.
  - apply H; [exact H0 |]. rewrite (proj2 ((proj1 act_NewVarC) R 0)). exact H1.
  - eauto.
  - discriminate.
  - discriminate.
  - discriminate.
  - eauto.
  - apply orb_true_iff in H1 as [h | h]; apply orb_true_iff; [left | right]; eauto.
Qed.

Lemma act_div_step :
  (∀ P, act_div P = true → ∃ P', lts P τ P' ∧ act_div P' = true) ∧
  (∀ G, act_div_g G = true → ∃ P', lts (g G) τ P' ∧ act_div P' = true).
Proof.
  apply vaccs_proc_ind'; simpl; intros.
  - apply orb_true_iff in H1 as [h | h].
    + destruct (H h) as (p' & l & h'). exists (p' ‖ p0). split; [apply lts_parL, l |].
      simpl. rewrite h'. reflexivity.
    + destruct (H0 h) as (p' & l & h'). exists (p ‖ p'). split; [apply lts_parR, l |].
      simpl. rewrite h', orb_true_r. reflexivity.
  - discriminate.
  - exists (pr_subst n p (rec n • p)). split; [apply lts_recursion |].
    apply orb_true_iff in H0 as [h | h].
    + apply (proj1 (act_var_subst_div n)); [exact h |]. simpl. rewrite h. reflexivity.
    + apply (proj1 (act_div_subst n)). exact h.
  - destruct (Eval_Eq 0 e) as [[] |] eqn:he; [| | discriminate].
    + destruct (H H1) as (p' & l & h'). exists p'. split; [eapply lts_ifOne; eassumption | exact h'].
    + destruct (H0 H1) as (p' & l & h'). exists p'. split; [eapply lts_ifZero; eassumption | exact h'].
  - discriminate.
  - destruct (H H0) as (p' & l & h'). exists (ν p'). split; [apply lts_res_tau, l | exact h'].
  - exact (H H0).
  - discriminate.
  - discriminate.
  - discriminate.
  - exists p. split; [apply lts_tau | exact H0].
  - apply orb_true_iff in H1 as [h | h].
    + destruct (H h) as (p' & l & h'). exists p'. split; [apply lts_choiceL, l | exact h'].
    + destruct (H0 h) as (p' & l & h'). exists p'. split; [apply lts_choiceR, l | exact h'].
Qed.

End VACCS_Divergence.
(* end hide *)
