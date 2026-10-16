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
(* * lqCCS: structural congruence

    The structural congruence of Ceragioli, Gadducci, Lomurno, Tedeschi,
    /Quantum Bisimilarity via Barbs and Contexts/ (POPL 2024, Figure 2), on
    guarded sums:

    - [P ∥ 0 ≡ P], [P ∥ Q ≡ Q ∥ P], [P ∥ (Q ∥ R) ≡ (P ∥ Q) ∥ R];
    - [g + 0_ẽ ≡ g], [g + h ≡ h + g], [g + (h + k) ≡ (g + h) + k] (on guards);
    - [if tt then P else Q ≡ P], [if ff then P else Q ≡ Q];
    - [P ≡ P[v/e]] when [e ⇓ v] (in an output, a conditional, a prefix, [0_ẽ]);
    - [0_ẽ \ c ≡ 0_ẽ], [P \ c \ d ≡ P \ d \ c],
      [(P ∥ Q) \ c ≡ P ∥ (Q \ c)] when [c ∉ fc(P)];
    - closed under all contexts.

    The paper asks congruent processes to be typed by the same [Σ].  Our
    semantics does not depend on the qubits owned ([lqCCS_Program.v]), so
    no such side condition is needed: [≡] is a bisimulation on all terms. *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list sets relations.
From TestingTheory Require Import lqCCS_Syntax lqCCS_Program lqCCS_Succ.
(* ** Free channels *)

Definition prefix_chans (𝜆 : prefix) : list chan :=
  match 𝜆 with PRecv _ c _ => [c] | _ => [] end.

Fixpoint fc (P : proc) : list chan :=
  match P with
  | PSend _ c _ => [c]
  | PIte _ P Q | PPar P Q => fc P ++ fc Q
  | PRes P c => filter (λ d, d ≠ c) (fc P)
  | PG g => gfc g
  end
with gfc (g : guard) : list chan :=
  match g with
  | GNil _ | GSucc => []
  | GPre 𝜆 P => prefix_chans 𝜆 ++ fc P
  | GSum g1 g2 => gfc g1 ++ gfc g2
  end.

(* ** Expressions that evaluate *)

(* [e ⇓ v]. *)
Definition exp_val (e : exp) (v : val) : Prop := eval e = Some v.

Inductive exp_eqv : exp → exp → Prop :=
| ee_refl e : exp_eqv e e
| ee_val e v : exp_val e v → exp_eqv e (EVal v).

Definition exps_eqv : list exp → list exp → Prop := Forall2 exp_eqv.

(* Same prefix, up to the evaluation of its expressions and its tags (tags
    only matter to schedulers, see [lqCCS_AlmostSure.v]). *)
Inductive prefix_eqv : prefix → prefix → Prop :=
| pe_tau t t' : prefix_eqv (PTau t) (PTau t')
| pe_taupair t1 t2 t1' t2' : prefix_eqv (PTauPair t1 t2) (PTauPair t1' t2')
| pe_recv t t' c x : prefix_eqv (PRecv t c x) (PRecv t' c x)
| pe_op t t' E es es' : exps_eqv es es' → prefix_eqv (POp t E es) (POp t' E es')
| pe_meas t t' M es es' x : exps_eqv es es' → prefix_eqv (PMeas t M es x) (PMeas t' M es' x).

(* Inclusion of lists, as sets. *)
Definition incl {A} (l1 l2 : list A) : Prop := ∀ x, x ∈ l1 → x ∈ l2.

(* ** One step of congruence *)

Inductive cs : proc → proc → Prop :=
| cs_par_nil P : cs (PPar P (PG (GNil []))) P
| cs_par_comm P Q : cs (PPar P Q) (PPar Q P)
| cs_par_assoc P Q R : cs (PPar P (PPar Q R)) (PPar (PPar P Q) R)
| cs_ite_t e P Q : eval e = Some (VBool true) → cs (PIte e P Q) P
| cs_ite_f e P Q : eval e = Some (VBool false) → cs (PIte e P Q) Q
| cs_send_val t t' c e e' : exp_eqv e e' → cs (PSend t c e) (PSend t' c e')
| cs_ite_val e e' P Q : exp_eqv e e' → cs (PIte e P Q) (PIte e' P Q)
| cs_res_nil es c : cs (PRes (PG (GNil es)) c) (PG (GNil es))
| cs_res_ord P c d : cs (PRes (PRes P c) d) (PRes (PRes P d) c)
| cs_res_par P Q c : c ∉ fc P → cs (PRes (PPar P Q) c) (PPar P (PRes Q c))
(* contexts *)
| cs_ite_l e P P' Q : cs P P' → cs (PIte e P Q) (PIte e P' Q)
| cs_ite_r e P Q Q' : cs Q Q' → cs (PIte e P Q) (PIte e P Q')
| cs_par_l P P' Q : cs P P' → cs (PPar P Q) (PPar P' Q)
| cs_par_r P Q Q' : cs Q Q' → cs (PPar P Q) (PPar P Q')
| cs_res P P' c : cs P P' → cs (PRes P c) (PRes P' c)
| cs_guard g g' : gcs g g' → cs (PG g) (PG g')
with gcs : guard → guard → Prop :=
| gcs_sum_nil g es : gcs (GSum g (GNil es)) g
| gcs_sum_comm g h : gcs (GSum g h) (GSum h g)
| gcs_sum_assoc g h k : gcs (GSum g (GSum h k)) (GSum (GSum g h) k)
| gcs_nil_val es es' : exps_eqv es es' → gcs (GNil es) (GNil es')
| gcs_pre_val 𝜆 𝜆' P : prefix_eqv 𝜆 𝜆' → gcs (GPre 𝜆 P) (GPre 𝜆' P)
(* contexts *)
| gcs_pre 𝜆 P P' : cs P P' → gcs (GPre 𝜆 P) (GPre 𝜆 P')
| gcs_sum_l g g' h : gcs g g' → gcs (GSum g h) (GSum g' h)
| gcs_sum_r g h h' : gcs h h' → gcs (GSum g h) (GSum g h').

Scheme cs_mut_ind := Induction for cs Sort Prop
  with gcs_mut_ind := Induction for gcs Sort Prop.
Combined Scheme cs_gcs_ind from cs_mut_ind, gcs_mut_ind.

(* ** The congruence *)

Definition cgr : relation proc := rtsc cs.

Notation "P ≡* Q" := (cgr P Q) (at level 70).

#[global] Instance cgr_equivalence : Equivalence cgr.
Proof. apply rtsc_equivalence. Qed.

(* ** What a step of congruence keeps *)

Lemma eval_closed e v : eval e = Some v → exp_fv e = [].
Proof.
  revert v. induction e; intros w He; simpl in He |- *; try done.
  all: repeat (destruct (eval _) as [[]|] eqn:? in He; try discriminate);
    repeat match goal with
    | IH : ∀ v, eval ?e = Some v → _, H : eval ?e = Some _ |- _ => rewrite (IH _ H); clear IH
    end; done.
Qed.

Lemma exp_eqv_eval e e' : exp_eqv e e' → eval e = eval e'.
Proof. destruct 1 as [|e v He]; [done|]. done. Qed.

Lemma exps_eqv_eval es es' : exps_eqv es es' → eval_qubits es = eval_qubits es'.
Proof.
  induction 1 as [|e e' es es' He _ IH]; [done|]. unfold eval_qubits in *. simpl.
  assert (E : eval_qubit e = eval_qubit e')
    by (unfold eval_qubit; by rewrite (exp_eqv_eval _ _ He)).
  by rewrite E, IH.
Qed.

(* Success is invariant. *)
Lemma cs_gcs_goodb :
  (∀ P Q, cs P Q → goodb P = goodb Q) ∧ (∀ g h, gcs g h → ggoodb g = ggoodb h).
Proof.
  apply cs_gcs_ind; simpl; intros; try congruence.
  all: try (by rewrite orb_false_r); try apply orb_comm; try apply orb_assoc;
    try (by rewrite e0); try (by rewrite (exp_eqv_eval _ _ e0)); try (by rewrite H).
Qed.

(* ** Substitution *)

Lemma exp_subst_closed e w x v : eval e = Some w → exp_subst e x v = e.
Proof. intros He. apply exp_subst_fresh. rewrite (eval_closed _ _ He). set_solver. Qed.

Lemma exp_eqv_subst e e' x v : exp_eqv e e' → exp_eqv (exp_subst e x v) (exp_subst e' x v).
Proof.
  destruct 1 as [|e w Hw]; [constructor|]. simpl.
  rewrite (exp_subst_closed e w) by apply Hw. by constructor.
Qed.

Lemma exps_eqv_subst es es' x v :
  exps_eqv es es' → exps_eqv (exps_subst es x v) (exps_subst es' x v).
Proof. induction 1; constructor; [by apply exp_eqv_subst|done]. Qed.

Lemma prefix_eqv_subst 𝜆 𝜆' x v :
  prefix_eqv 𝜆 𝜆' → prefix_eqv (prefix_subst 𝜆 x v) (prefix_subst 𝜆' x v).
Proof. destruct 1; simpl; constructor; by try apply exps_eqv_subst. Qed.

Lemma prefix_eqv_binder 𝜆 𝜆' : prefix_eqv 𝜆 𝜆' → prefix_binder 𝜆 = prefix_binder 𝜆'.
Proof. by destruct 1. Qed.

Lemma fc_subst x v : (∀ P, fc (subst P x v) = fc P) ∧ (∀ g, gfc (gsubst g x v) = gfc g).
Proof.
  apply proc_guard_ind; simpl; intros; try congruence.
  case_decide; destruct 𝜆; simpl; congruence.
Qed.

Lemma cs_subst x v :
  (∀ P Q, cs P Q → cs (subst P x v) (subst Q x v))
  ∧ (∀ g h, gcs g h → gcs (gsubst g x v) (gsubst h x v)).
Proof.
  apply cs_gcs_ind; simpl; intros; try (constructor; done).
  - rewrite (exp_subst_closed _ _ x v e0). by apply cs_ite_t.
  - rewrite (exp_subst_closed _ _ x v e0). by apply cs_ite_f.
  - constructor. by apply exp_eqv_subst.
  - constructor. by apply exp_eqv_subst.
  - apply cs_res_par. by rewrite (proj1 (fc_subst x v)).
  - constructor. by apply exps_eqv_subst.
  - rewrite (prefix_eqv_binder _ _ p). apply gcs_pre_val. by apply prefix_eqv_subst.
  - case_decide; by apply gcs_pre.
Qed.

Lemma cgr_subst P Q x v : P ≡* Q → subst P x v ≡* subst Q x v.
Proof.
  induction 1 as [P|P Q R [HPQ|HQP] _ IH]; [done| |].
  - etrans; [|exact IH]. apply rtsc_lr. by apply cs_subst.
  - etrans; [|exact IH]. apply rtsc_rl. by apply cs_subst.
Qed.

(* ** Congruence under contexts *)

Lemma cgr_of_cs P Q : cs P Q → P ≡* Q.
Proof. apply rtsc_lr. Qed.

Lemma cgr_ctx (f : proc → proc) :
  (∀ P Q, cs P Q → cs (f P) (f Q)) → ∀ P Q, P ≡* Q → f P ≡* f Q.
Proof.
  intros Hf P Q. induction 1 as [P|P Q R [HPQ|HQP] _ IH]; [done| |].
  - etrans; [|exact IH]. apply rtsc_lr. by apply Hf.
  - etrans; [|exact IH]. apply rtsc_rl. by apply Hf.
Qed.

Lemma cgr_par_l P P' Q : P ≡* P' → PPar P Q ≡* PPar P' Q.
Proof. apply (cgr_ctx (λ P, PPar P Q)). intros. by constructor. Qed.

Lemma cgr_par_r P Q Q' : Q ≡* Q' → PPar P Q ≡* PPar P Q'.
Proof. apply (cgr_ctx (λ Q, PPar P Q)). intros. by constructor. Qed.

Lemma cgr_res P P' c : P ≡* P' → PRes P c ≡* PRes P' c.
Proof. apply (cgr_ctx (λ P, PRes P c)). intros. by constructor. Qed.

Lemma cgr_par P P' Q Q' : P ≡* P' → Q ≡* Q' → PPar P Q ≡* PPar P' Q'.
Proof. intros. etrans; [by apply cgr_par_l|by apply cgr_par_r]. Qed.

(* ** Facts on steps *)

Lemma gstep_nil es l P' : ¬ gstep (GNil es) l P'.
Proof. by inversion 1. Qed.

Lemma pstep_nil es l P' : ¬ pstep (PG (GNil es)) l P'.
Proof. inversion 1; subst. by eapply gstep_nil. Qed.

Lemma gstep_fc g l P' : gstep g l P' → incl (fc P') (gfc g).
Proof.
  induction 1; simpl; intros d Hd; rewrite ?elem_of_app; try set_solver.
  rewrite (proj1 (fc_subst x v)) in Hd. set_solver.
Qed.

Lemma pstep_fc P l P' : pstep P l P' → incl (fc P') (fc P).
Proof.
  induction 1; simpl; intros d Hd; rewrite ?elem_of_app in *; try set_solver.
  - by eapply gstep_fc.
  - rewrite list_elem_of_filter in *. naive_solver.
Qed.

Lemma gstep_chan g l P' c : gstep g l P' → on_chan c l → c ∈ gfc g.
Proof.
  induction 1; simpl; intros Hc; rewrite ?elem_of_app.
  all: try (destruct Hc as (? & ? & [Heq|Heq]); discriminate).
  - destruct Hc as (? & ? & [Heq|Heq]); simplify_eq. set_solver.
  - left. by apply IHgstep.
  - right. by apply IHgstep.
Qed.

Lemma pstep_chan P l P' c : pstep P l P' → on_chan c l → c ∈ fc P.
Proof.
  intros Hs. induction Hs; simpl; intros Hc; rewrite ?elem_of_app.
  all: try (destruct Hc as (? & ? & [Heq|Heq]); discriminate).
  - by eapply gstep_chan.
  - destruct Hc as (? & ? & [Heq|Heq]); simplify_eq. set_solver.
  - left. by apply IHHs.
  - right. by apply IHHs.
  - left. by apply IHHs.
  - right. by apply IHHs.
  - apply list_elem_of_filter. split; [|by apply IHHs]. intros ->. done.
Qed.

(* ** Structural congruence is a bisimulation

    Up to the tags of the labels: commuting a parallel composition swaps
    the two tags of a synchronisation. *)

Definition fwd (P Q : proc) : Prop :=
  ∀ l P', pstep P l P' → ∃ l' Q', erase l' = erase l ∧ pstep Q l' Q' ∧ P' ≡* Q'.

Definition gfwd (g h : guard) : Prop :=
  ∀ l P', gstep g l P' → ∃ l' Q', erase l' = erase l ∧ gstep h l' Q' ∧ P' ≡* Q'.

Ltac no_nil :=
  match goal with
  | H : pstep (PG (GNil _)) _ _ |- _ => exfalso; by eapply pstep_nil
  | H : gstep (GNil _) _ _ |- _ => exfalso; by eapply gstep_nil
  end.

Lemma fwd_par_nil P : fwd (PPar P (PG (GNil []))) P ∧ fwd P (PPar P (PG (GNil []))).
Proof.
  split.
  - intros l X Hs. inversion Hs; subst; try no_nil.
    exists l, P'. split_and!; [done|done|]. apply cgr_of_cs, cs_par_nil.
  - intros l P' Hs. exists l, (PPar P' (PG (GNil []))). split_and!; [done|by apply ps_parL|].
    symmetry. apply cgr_of_cs, cs_par_nil.
Qed.

Lemma fwd_par_comm P Q : fwd (PPar P Q) (PPar Q P).
Proof.
  intros l X Hs. inversion Hs; subst.
  - exists l, (PPar Q P'). split_and!; [done|by apply ps_parR|]. apply cgr_of_cs, cs_par_comm.
  - exists l, (PPar Q' P). split_and!; [done|by apply ps_parL|]. apply cgr_of_cs, cs_par_comm.
  - exists (LTau (SPair t' t)), (PPar Q' P'). split_and!; [done|by eapply ps_syncR|].
    apply cgr_of_cs, cs_par_comm.
  - exists (LTau (SPair t' t)), (PPar Q' P'). split_and!; [done|by eapply ps_syncL|].
    apply cgr_of_cs, cs_par_comm.
Qed.

Lemma fwd_par_assoc P Q R :
  fwd (PPar P (PPar Q R)) (PPar (PPar P Q) R) ∧ fwd (PPar (PPar P Q) R) (PPar P (PPar Q R)).
Proof.
  split.
  - intros l X Hs. inversion Hs as [| | | |? ? ? P' HP|? ? ? X' HX|? ? t t' c v P' X' HP HX|? ? t t' c v P' X' HP HX|];
      subst.
    + exists l, (PPar (PPar P' Q) R). split_and!; [done|by do 2 apply ps_parL|].
      apply cgr_of_cs, cs_par_assoc.
    + inversion HX as [| | | |? ? ? Q' HQ|? ? ? R' HR|? ? t t' c v Q' R' HQ HR|? ? t t' c v Q' R' HQ HR|];
        subst.
      * exists l, (PPar (PPar P Q') R). split_and!; [done|by apply ps_parL, ps_parR|].
        apply cgr_of_cs, cs_par_assoc.
      * exists l, (PPar (PPar P Q) R'). split_and!; [done|by apply ps_parR|].
        apply cgr_of_cs, cs_par_assoc.
      * exists (LTau (SPair t t')), (PPar (PPar P Q') R'). split_and!; [done| |].
        -- eapply ps_syncL; [by apply ps_parR|done].
        -- apply cgr_of_cs, cs_par_assoc.
      * exists (LTau (SPair t t')), (PPar (PPar P Q') R'). split_and!; [done| |].
        -- eapply ps_syncR; [by apply ps_parR|done].
        -- apply cgr_of_cs, cs_par_assoc.
    + inversion HX as [| | | |? ? ? Q' HQ|? ? ? R' HR| | |]; subst.
      * exists (LTau (SPair t t')), (PPar (PPar P' Q') R). split_and!; [done| |].
        -- apply ps_parL. by eapply ps_syncL.
        -- apply cgr_of_cs, cs_par_assoc.
      * exists (LTau (SPair t t')), (PPar (PPar P' Q) R'). split_and!; [done| |].
        -- eapply ps_syncL; [by apply ps_parL|done].
        -- apply cgr_of_cs, cs_par_assoc.
    + inversion HX as [| | | |? ? ? Q' HQ|? ? ? R' HR| | |]; subst.
      * exists (LTau (SPair t t')), (PPar (PPar P' Q') R). split_and!; [done| |].
        -- apply ps_parL. by eapply ps_syncR.
        -- apply cgr_of_cs, cs_par_assoc.
      * exists (LTau (SPair t t')), (PPar (PPar P' Q) R'). split_and!; [done| |].
        -- eapply ps_syncR; [by apply ps_parL|done].
        -- apply cgr_of_cs, cs_par_assoc.
  - intros l X Hs. inversion Hs as [| | | |? ? ? X' HX|? ? ? R' HR|? ? t t' c v X' R' HX HR|? ? t t' c v X' R' HX HR|];
      subst.
    + inversion HX as [| | | |? ? ? P' HP|? ? ? Q' HQ|? ? t t' c v P' Q' HP HQ|? ? t t' c v P' Q' HP HQ|];
        subst.
      * exists l, (PPar P' (PPar Q R)). split_and!; [done|by apply ps_parL|].
        symmetry. apply cgr_of_cs, cs_par_assoc.
      * exists l, (PPar P (PPar Q' R)). split_and!; [done|by apply ps_parR, ps_parL|].
        symmetry. apply cgr_of_cs, cs_par_assoc.
      * exists (LTau (SPair t t')), (PPar P' (PPar Q' R)). split_and!; [done| |].
        -- eapply ps_syncL; [done|by apply ps_parL].
        -- symmetry. apply cgr_of_cs, cs_par_assoc.
      * exists (LTau (SPair t t')), (PPar P' (PPar Q' R)). split_and!; [done| |].
        -- eapply ps_syncR; [done|by apply ps_parL].
        -- symmetry. apply cgr_of_cs, cs_par_assoc.
    + exists l, (PPar P (PPar Q R')). split_and!; [done|by do 2 apply ps_parR|].
      symmetry. apply cgr_of_cs, cs_par_assoc.
    + inversion HX as [| | | |? ? ? P' HP|? ? ? Q' HQ| | |]; subst.
      * exists (LTau (SPair t t')), (PPar P' (PPar Q R')). split_and!; [done| |].
        -- eapply ps_syncL; [done|by apply ps_parR].
        -- symmetry. apply cgr_of_cs, cs_par_assoc.
      * exists (LTau (SPair t t')), (PPar P (PPar Q' R')). split_and!; [done| |].
        -- apply ps_parR. by eapply ps_syncL.
        -- symmetry. apply cgr_of_cs, cs_par_assoc.
    + inversion HX as [| | | |? ? ? P' HP|? ? ? Q' HQ| | |]; subst.
      * exists (LTau (SPair t t')), (PPar P' (PPar Q R')). split_and!; [done| |].
        -- eapply ps_syncR; [done|by apply ps_parR].
        -- symmetry. apply cgr_of_cs, cs_par_assoc.
      * exists (LTau (SPair t t')), (PPar P (PPar Q' R')). split_and!; [done| |].
        -- apply ps_parR. by eapply ps_syncR.
        -- symmetry. apply cgr_of_cs, cs_par_assoc.
Qed.

Lemma fwd_refl_step P Q : (∀ l P', pstep P l P' → pstep Q l P') → fwd P Q.
Proof. intros H l P' Hs. exists l, P'. split_and!; [done|by apply H|done]. Qed.

Lemma fwd_ite_t e P Q : eval e = Some (VBool true) → fwd (PIte e P Q) P ∧ fwd P (PIte e P Q).
Proof.
  intros He. split; apply fwd_refl_step; intros l P' Hs.
  - inversion Hs; subst; [done|congruence].
  - by apply ps_iteT.
Qed.

Lemma fwd_ite_f e P Q : eval e = Some (VBool false) → fwd (PIte e P Q) Q ∧ fwd Q (PIte e P Q).
Proof.
  intros He. split; apply fwd_refl_step; intros l P' Hs.
  - inversion Hs; subst; [congruence|done].
  - by apply ps_iteF.
Qed.

Lemma fwd_send_val t t' c e e' :
  exp_eqv e e' → fwd (PSend t c e) (PSend t' c e') ∧ fwd (PSend t' c e') (PSend t c e).
Proof.
  intros He. pose proof (exp_eqv_eval _ _ He) as E.
  split; intros l P' Hs; inversion Hs as [|? ? ? v Hv| | | | | | |]; subst.
  - exists (LAct t' (AOut c v)), (PG (GNil [])). split_and!; [done|constructor; congruence|done].
  - exists (LAct t (AOut c v)), (PG (GNil [])). split_and!; [done|constructor; congruence|done].
Qed.

Lemma fwd_ite_val e e' P Q : exp_eqv e e' → fwd (PIte e P Q) (PIte e' P Q) ∧ fwd (PIte e' P Q) (PIte e P Q).
Proof.
  intros He. pose proof (exp_eqv_eval _ _ He) as E.
  split; apply fwd_refl_step; intros l P' Hs; inversion Hs; subst;
    [apply ps_iteT|apply ps_iteF|apply ps_iteT|apply ps_iteF]; congruence.
Qed.

Lemma fwd_res_nil es c : fwd (PRes (PG (GNil es)) c) (PG (GNil es)) ∧ fwd (PG (GNil es)) (PRes (PG (GNil es)) c).
Proof.
  split; intros l P' Hs; inversion Hs; subst; no_nil.
Qed.

Lemma fwd_res_ord P c d : fwd (PRes (PRes P c) d) (PRes (PRes P d) c).
Proof.
  intros l X Hs. inversion Hs as [| | | | | | | |? ? ? Y Hd HY]; subst.
  inversion HY as [| | | | | | | |? ? ? P' Hc HP]; subst.
  exists l, (PRes (PRes P' d) c). split_and!; [done| |].
  - apply ps_res; [done|]. by apply ps_res.
  - apply cgr_of_cs, cs_res_ord.
Qed.

Lemma fwd_res_par P Q c : c ∉ fc P →
  fwd (PRes (PPar P Q) c) (PPar P (PRes Q c)) ∧ fwd (PPar P (PRes Q c)) (PRes (PPar P Q) c).
Proof.
  intros Hc. split.
  - intros l X Hs. inversion Hs as [| | | | | | | |? ? ? Y Hn HY]; subst.
    inversion HY as [| | | |? ? ? P' HP|? ? ? Q' HQ|? ? t t' c' v P' Q' HP HQ|? ? t t' c' v P' Q' HP HQ|];
      subst.
    + exists l, (PPar P' (PRes Q c)). split_and!; [done|by apply ps_parL|].
      apply cgr_of_cs, cs_res_par. intros Hin. apply Hc. by eapply pstep_fc.
    + exists l, (PPar P (PRes Q' c)). split_and!; [done|by apply ps_parR, ps_res|].
      by apply cgr_of_cs, cs_res_par.
    + exists (LTau (SPair t t')), (PPar P' (PRes Q' c)). split_and!; [done| |].
      * eapply ps_syncL; [done|]. apply ps_res; [|done].
        intros (? & ? & [Heq|Heq]); simplify_eq. apply Hc.
        eapply pstep_chan; [exact HP|]. do 2 eexists. by left.
      * apply cgr_of_cs, cs_res_par. intros Hin. apply Hc. by eapply pstep_fc.
    + exists (LTau (SPair t t')), (PPar P' (PRes Q' c)). split_and!; [done| |].
      * eapply ps_syncR; [done|]. apply ps_res; [|done].
        intros (? & ? & [Heq|Heq]); simplify_eq. apply Hc.
        eapply pstep_chan; [exact HP|]. do 2 eexists. by right.
      * apply cgr_of_cs, cs_res_par. intros Hin. apply Hc. by eapply pstep_fc.
  - intros l X Hs.
    inversion Hs as [| | | |? ? ? P' HP|? ? ? Y HY|? ? t t' c' v P' Y HP HY|? ? t t' c' v P' Y HP HY|];
      subst.
    + exists l, (PRes (PPar P' Q) c). split_and!; [done| |].
      * apply ps_res; [|by apply ps_parL]. intros Hon. apply Hc. by eapply pstep_chan.
      * symmetry. apply cgr_of_cs, cs_res_par. intros Hin. apply Hc. by eapply pstep_fc.
    + inversion HY as [| | | | | | | |? ? ? Q' Hn HQ]; subst.
      exists l, (PRes (PPar P Q') c). split_and!; [done|by apply ps_res, ps_parR|].
      symmetry. by apply cgr_of_cs, cs_res_par.
    + inversion HY as [| | | | | | | |? ? ? Q' Hn HQ]; subst.
      exists (LTau (SPair t t')), (PRes (PPar P' Q') c). split_and!; [done| |].
      * apply ps_res; [by intros (? & ? & [Heq|Heq])|]. by eapply ps_syncL.
      * symmetry. apply cgr_of_cs, cs_res_par. intros Hin. apply Hc. by eapply pstep_fc.
    + inversion HY as [| | | | | | | |? ? ? Q' Hn HQ]; subst.
      exists (LTau (SPair t t')), (PRes (PPar P' Q') c). split_and!; [done| |].
      * apply ps_res; [by intros (? & ? & [Heq|Heq])|]. by eapply ps_syncR.
      * symmetry. apply cgr_of_cs, cs_res_par. intros Hin. apply Hc. by eapply pstep_fc.
Qed.

Lemma gfwd_refl_step g h : (∀ l P', gstep g l P' → gstep h l P') → gfwd g h.
Proof. intros H l P' Hs. exists l, P'. split_and!; [done|by apply H|done]. Qed.

Lemma gfwd_sum_nil g es : gfwd (GSum g (GNil es)) g ∧ gfwd g (GSum g (GNil es)).
Proof.
  split; apply gfwd_refl_step; intros l P' Hs.
  - inversion Hs; subst; [done|no_nil].
  - by apply gs_sumL.
Qed.

Lemma gfwd_sum_comm g h : gfwd (GSum g h) (GSum h g).
Proof.
  apply gfwd_refl_step. intros l P' Hs. inversion Hs; subst; [by apply gs_sumR|by apply gs_sumL].
Qed.

Lemma gfwd_sum_assoc g h k :
  gfwd (GSum g (GSum h k)) (GSum (GSum g h) k) ∧ gfwd (GSum (GSum g h) k) (GSum g (GSum h k)).
Proof.
  split; apply gfwd_refl_step; intros l P' Hs.
  - inversion Hs as [| | | | |? ? ? ? H1|? ? ? ? H2]; subst.
    + by do 2 apply gs_sumL.
    + inversion H2; subst; [by apply gs_sumL, gs_sumR|by apply gs_sumR].
  - inversion Hs as [| | | | |? ? ? ? H1|? ? ? ? H2]; subst.
    + inversion H1; subst; [by apply gs_sumL|by apply gs_sumR, gs_sumL].
    + by do 2 apply gs_sumR.
Qed.

Lemma gfwd_nil_val es es' : gfwd (GNil es) (GNil es').
Proof. intros l P' Hs. no_nil. Qed.

Lemma gfwd_pre_val 𝜆 𝜆' P : prefix_eqv 𝜆 𝜆' → gfwd (GPre 𝜆 P) (GPre 𝜆' P) ∧ gfwd (GPre 𝜆' P) (GPre 𝜆 P).
Proof.
  intros H𝜆. destruct H𝜆 as [t t'|t1 t2 t1' t2'|t t' c x|t t' E es es' Hes|t t' M es es' x Hes];
    try pose proof (exps_eqv_eval _ _ Hes) as Ev; split; intros l X Hs; inversion Hs; subst.
  - exists (LTau (STag t')), X. split_and!; [done|constructor|done].
  - exists (LTau (STag t)), X. split_and!; [done|constructor|done].
  - exists (LTau (SPair t1' t2')), X. split_and!; [done|constructor|done].
  - exists (LTau (SPair t1 t2)), X. split_and!; [done|constructor|done].
  - exists (LAct t' (AIn c v)), (subst P x v). split_and!; [done|constructor|done].
  - exists (LAct t (AIn c v)), (subst P x v). split_and!; [done|constructor|done].
  - exists (LAct t' (AOp E qs)), X. split_and!; [done|constructor; congruence|done].
  - exists (LAct t (AOp E qs)), X. split_and!; [done|constructor; congruence|done].
  - exists (LAct t' (AMeas M qs x)), X. split_and!; [done|constructor; congruence|done].
  - exists (LAct t (AMeas M qs x)), X. split_and!; [done|constructor; congruence|done].
Qed.

(* *** Contexts *)

Lemma fwd_ite_l e P P' Q : fwd P P' → fwd (PIte e P Q) (PIte e P' Q).
Proof.
  intros H l X Hs. inversion Hs as [| |? ? ? ? ? He Hp|? ? ? ? ? He Hq| | | | |]; subst.
  - destruct (H _ _ Hp) as (l' & Y & El & Hs' & HY). exists l', Y. split_and!; [done| |done].
    by apply ps_iteT.
  - exists l, X. split_and!; [done|by apply ps_iteF|done].
Qed.

Lemma fwd_ite_r e P Q Q' : fwd Q Q' → fwd (PIte e P Q) (PIte e P Q').
Proof.
  intros H l X Hs. inversion Hs as [| |? ? ? ? ? He Hp|? ? ? ? ? He Hq| | | | |]; subst.
  - exists l, X. split_and!; [done|by apply ps_iteT|done].
  - destruct (H _ _ Hq) as (l' & Y & El & Hs' & HY). exists l', Y. split_and!; [done| |done].
    by apply ps_iteF.
Qed.

Lemma fwd_vis P P' t a X : fwd P P' → pstep P (LAct t a) X →
  ∃ t' Y, pstep P' (LAct t' a) Y ∧ X ≡* Y.
Proof.
  intros H Hs. destruct (H _ _ Hs) as ([s|t' a'] & Y & El & Hs' & HY); simpl in El; simplify_eq.
  eauto.
Qed.

Lemma fwd_par_l P P' Q : P ≡* P' → fwd P P' → fwd (PPar P Q) (PPar P' Q).
Proof.
  intros Hc H l X Hs.
  inversion Hs as [| | | |? ? ? P1 HP|? ? ? Q1 HQ|? ? t t' c v P1 Q1 HP HQ|? ? t t' c v P1 Q1 HP HQ|];
    subst.
  - destruct (H _ _ HP) as (l' & Y & El & Hs' & HY). exists l', (PPar Y Q).
    split_and!; [done|by apply ps_parL|by apply cgr_par_l].
  - exists l, (PPar P' Q1). split_and!; [done|by apply ps_parR|by apply cgr_par_l].
  - destruct (fwd_vis _ _ _ _ _ H HP) as (t'' & Y & Hs' & HY).
    exists (LTau (SPair t'' t')), (PPar Y Q1). split_and!; [done|by eapply ps_syncL|by apply cgr_par_l].
  - destruct (fwd_vis _ _ _ _ _ H HP) as (t'' & Y & Hs' & HY).
    exists (LTau (SPair t'' t')), (PPar Y Q1). split_and!; [done|by eapply ps_syncR|by apply cgr_par_l].
Qed.

Lemma fwd_par_r P Q Q' : Q ≡* Q' → fwd Q Q' → fwd (PPar P Q) (PPar P Q').
Proof.
  intros Hc H l X Hs.
  inversion Hs as [| | | |? ? ? P1 HP|? ? ? Q1 HQ|? ? t t' c v P1 Q1 HP HQ|? ? t t' c v P1 Q1 HP HQ|];
    subst.
  - exists l, (PPar P1 Q'). split_and!; [done|by apply ps_parL|by apply cgr_par_r].
  - destruct (H _ _ HQ) as (l' & Y & El & Hs' & HY). exists l', (PPar P Y).
    split_and!; [done|by apply ps_parR|by apply cgr_par_r].
  - destruct (fwd_vis _ _ _ _ _ H HQ) as (t'' & Y & Hs' & HY).
    exists (LTau (SPair t t'')), (PPar P1 Y). split_and!; [done|by eapply ps_syncL|by apply cgr_par_r].
  - destruct (fwd_vis _ _ _ _ _ H HQ) as (t'' & Y & Hs' & HY).
    exists (LTau (SPair t t'')), (PPar P1 Y). split_and!; [done|by eapply ps_syncR|by apply cgr_par_r].
Qed.

Lemma fwd_res P P' c : fwd P P' → fwd (PRes P c) (PRes P' c).
Proof.
  intros H l X Hs. inversion Hs as [| | | | | | | |? ? ? P1 Hn HP]; subst.
  destruct (H _ _ HP) as (l' & Y & El & Hs' & HY). exists l', (PRes Y c). split_and!; [done| |].
  - apply ps_res; [|done]. rewrite on_chan_erase, El. by rewrite <- on_chan_erase.
  - by apply cgr_res.
Qed.

Lemma fwd_guard g g' : gfwd g g' → fwd (PG g) (PG g').
Proof.
  intros H l X Hs. inversion Hs as [? ? ? Hg| | | | | | | |]; subst.
  destruct (H _ _ Hg) as (l' & Y & El & Hs' & HY). exists l', Y. split_and!; [done|by constructor|done].
Qed.

Lemma gfwd_pre 𝜆 P P' : P ≡* P' → gfwd (GPre 𝜆 P) (GPre 𝜆 P').
Proof.
  intros Hc l X Hs. inversion Hs; subst.
  - exists (LTau (STag t)), P'. split_and!; [done|constructor|done].
  - exists (LTau (SPair t t')), P'. split_and!; [done|constructor|done].
  - exists (LAct t (AIn c v)), (subst P' x v). split_and!; [done|constructor|by apply cgr_subst].
  - exists (LAct t (AOp E qs)), P'. split_and!; [done|by constructor|done].
  - exists (LAct t (AMeas M qs x)), P'. split_and!; [done|by constructor|done].
Qed.

Lemma gfwd_sum_l g g' h : gfwd g g' → gfwd (GSum g h) (GSum g' h).
Proof.
  intros H l X Hs. inversion Hs as [| | | | |? ? ? ? Hg|? ? ? ? Hh]; subst.
  - destruct (H _ _ Hg) as (l' & Y & El & Hs' & HY). exists l', Y.
    split_and!; [done|by apply gs_sumL|done].
  - exists l, X. split_and!; [done|by apply gs_sumR|done].
Qed.

Lemma gfwd_sum_r g h h' : gfwd h h' → gfwd (GSum g h) (GSum g h').
Proof.
  intros H l X Hs. inversion Hs as [| | | | |? ? ? ? Hg|? ? ? ? Hh]; subst.
  - exists l, X. split_and!; [done|by apply gs_sumL|done].
  - destruct (H _ _ Hh) as (l' & Y & El & Hs' & HY). exists l', Y.
    split_and!; [done|by apply gs_sumR|done].
Qed.

(* *** The bisimulation *)

Theorem cs_bisim :
  (∀ P Q, cs P Q → fwd P Q ∧ fwd Q P) ∧ (∀ g h, gcs g h → gfwd g h ∧ gfwd h g).
Proof.
  apply cs_gcs_ind; intros.
  - apply fwd_par_nil.
  - split; apply fwd_par_comm.
  - apply fwd_par_assoc.
  - by apply fwd_ite_t.
  - by apply fwd_ite_f.
  - by apply fwd_send_val.
  - by apply fwd_ite_val.
  - apply fwd_res_nil.
  - split; apply fwd_res_ord.
  - by apply fwd_res_par.
  - destruct H. split; by apply fwd_ite_l.
  - destruct H. split; by apply fwd_ite_r.
  - destruct H. split; apply fwd_par_l; try done; [apply cgr_of_cs, c|symmetry; apply cgr_of_cs, c].
  - destruct H. split; apply fwd_par_r; try done; [apply cgr_of_cs, c|symmetry; apply cgr_of_cs, c].
  - destruct H. split; by apply fwd_res.
  - destruct H. split; by apply fwd_guard.
  - apply gfwd_sum_nil.
  - split; apply gfwd_sum_comm.
  - apply gfwd_sum_assoc.
  - split; apply gfwd_nil_val.
  - by apply gfwd_pre_val.
  - split; apply gfwd_pre; [apply cgr_of_cs, c|symmetry; apply cgr_of_cs, c].
  - destruct H. split; by apply gfwd_sum_l.
  - destruct H. split; by apply gfwd_sum_r.
Qed.

(* [≡*] is a bisimulation, up to tags. *)
Theorem cgr_bisim P Q : P ≡* Q → fwd P Q.
Proof.
  induction 1 as [P|P Q R [H|H] _ IH]; [by apply fwd_refl_step| |].
  all: intros l P' Hs.
  - destruct (proj1 (proj1 cs_bisim P Q H) l P' Hs) as (l1 & Q' & E1 & Hs1 & H1).
    destruct (IH _ _ Hs1) as (l2 & R' & E2 & Hs2 & H2).
    exists l2, R'. split_and!; [congruence|done|by etrans].
  - destruct (proj2 (proj1 cs_bisim Q P H) l P' Hs) as (l1 & Q' & E1 & Hs1 & H1).
    destruct (IH _ _ Hs1) as (l2 & R' & E2 & Hs2 & H2).
    exists l2, R'. split_and!; [congruence|done|by etrans].
Qed.
(* end hide *)
