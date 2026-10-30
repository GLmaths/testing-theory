(* begin hide *)
From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base countable list sets.
From TestingTheory Require Import ActTau PAL.Language.Syntax PAL.Language.LTS.
Import ListNotations.

Section PAL_Divergence.

Context (Val : Type) `{Countable Val}.

Fixpoint act_var (X : PVar) (E : term Val) : bool :=
  match E with
  | t_pvar Y => bool_decide (X = Y)
  | t_rec Y E1 => if decide (X = Y) then false else act_var X E1
  | t_out _ E1 => act_var X E1
  | t_eval E1 E2 | t_ichoice E1 E2 | t_echoice E1 E2 | t_par E1 E2 | t_cmerge E1 E2 =>
      act_var X E1 || act_var X E2
  | t_lmerge E1 _ => act_var X E1
  | t_if be E1 E2 => match eval_bexp be with
                     | Some true => act_var X E1
                     | Some false => act_var X E2
                     | None => false
                     end
  | _ => false
  end.

Fixpoint act_div (E : term Val) : bool :=
  match E with
  | t_undef => true
  | t_rec Y E1 => act_var Y E1 || act_div E1
  | t_out _ E1 => act_div E1
  | t_eval E1 E2 | t_ichoice E1 E2 | t_echoice E1 E2 | t_par E1 E2 | t_cmerge E1 E2 =>
      act_div E1 || act_div E2
  | t_lmerge E1 _ => act_div E1
  | t_if be E1 E2 => match eval_bexp be with
                     | Some true => act_div E1
                     | Some false => act_div E2
                     | None => false
                     end
  | _ => false
  end.

Lemma act_var_psubst X Y Q (hxy : X ≠ Y) E : act_var X E = true → act_var X (psubst Y Q E) = true.
Proof.
  induction E; simpl; intros h; rewrite ?orb_true_iff in *; try tauto; try discriminate.
  - destruct (eval_bexp be) as [[] |]; [exact (IHE1 h) | exact (IHE2 h) | discriminate].
  - apply bool_decide_eq_true in h as <-. rewrite decide_False by congruence. simpl.
    by apply bool_decide_eq_true.
  - destruct (decide (X = X0)); [discriminate |].
    destruct (decide (Y = X0)); simpl; rewrite decide_False by congruence; [exact h | exact (IHE h)].
Qed.

Lemma act_div_psubst Y Q E : act_div E = true → act_div (psubst Y Q E) = true.
Proof.
  induction E; simpl; intros h; rewrite ?orb_true_iff in *; try tauto; try discriminate.
  - destruct (eval_bexp be) as [[] |]; [exact (IHE1 h) | exact (IHE2 h) | discriminate].
  - destruct (decide (Y = X)); simpl; [by apply orb_true_iff |]. rewrite orb_true_iff.
    destruct h as [h | h]; [left; exact (act_var_psubst X Y Q (not_eq_sym n) E h) | right; exact (IHE h)].
Qed.

Lemma act_var_psubst_div X Q E : act_var X E = true → act_div Q = true → act_div (psubst X Q E) = true.
Proof.
  intros h hQ. induction E; simpl in *; rewrite ?orb_true_iff in *; try tauto; try discriminate.
  - destruct (eval_bexp be) as [[] |]; [exact (IHE1 h) | exact (IHE2 h) | discriminate].
  - apply bool_decide_eq_true in h as <-. rewrite decide_True by reflexivity. exact hQ.
  - destruct (decide (X = X0)); [discriminate |]. simpl. rewrite orb_true_iff. right. exact (IHE h).
Qed.

Lemma act_div_step E : act_div E = true → ∃ E', lts_step_a Val E τ E' ∧ act_div E' = true.
Proof.
  induction E; simpl; intros h; rewrite ?orb_true_iff in h; try discriminate.
  - exists t_undef. split; [apply air1 | reflexivity].
  - assert (E ≠ t_nil) as hne by (intros ->; discriminate).
    exists (t_par (t_out t t_nil) E). split; [by apply air5 |]. simpl. exact h.
  - exists (t_par E1 E2). split; [apply air6 |]. simpl. by apply orb_true_iff.
  - destruct (eval_bexp be) as [[] |] eqn:hb; [| | discriminate].
    + destruct (IHE1 h) as (E' & l & h'). exists E'. split; [by apply air3 | exact h'].
    + destruct (IHE2 h) as (E' & l & h'). exists E'. split; [by apply air4 | exact h'].
  - destruct h as [h | h]; [exists E1 | exists E2]; split; [apply air7_l | exact h | apply air7_r | exact h].
  - destruct h as [h | h].
    + destruct (IHE1 h) as (E' & l & h'). exists (t_echoice E' E2). split; [by apply air8_l |]. simpl. by rewrite h'.
    + destruct (IHE2 h) as (E' & l & h'). exists (t_echoice E1 E'). split; [by apply air8_r |]. simpl. by rewrite h', orb_true_r.
  - destruct h as [h | h].
    + destruct (IHE1 h) as (E' & l & h'). exists (t_par E' E2). split; [by apply air9_l |]. simpl. by rewrite h'.
    + destruct (IHE2 h) as (E' & l & h'). exists (t_par E1 E'). split; [by apply air9_r |]. simpl. by rewrite h', orb_true_r.
  - destruct (IHE1 h) as (E' & l & h'). exists (t_lmerge E' E2). split; [by apply air11 | exact h'].
  - destruct h as [h | h].
    + destruct (IHE1 h) as (E' & l & h'). exists (t_cmerge E' E2). split; [by apply air10_l |]. simpl. by rewrite h'.
    + destruct (IHE2 h) as (E' & l & h'). exists (t_cmerge E1 E'). split; [by apply air10_r |]. simpl. by rewrite h', orb_true_r.
  - exists (psubst X (t_rec X E) E). split; [apply air2 |].
    destruct h as [h | h].
    + apply act_var_psubst_div; [exact h |]. simpl. by rewrite h.
    + by apply act_div_psubst.
Qed.

End PAL_Divergence.
(* end hide *)
