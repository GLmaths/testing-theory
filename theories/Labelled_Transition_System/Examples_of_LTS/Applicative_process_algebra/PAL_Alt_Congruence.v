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
From stdpp Require Import base tactics relations countable.
From TestingTheory Require Import ActTau gLts InputOutputActions Bisimulation Lts_OBA Lts_FW Lts_OBA_FB
  PAL_Syntax PAL_Alt_LTS.

(* * Structural congruence for the alternative LTS of PAL

   As for VCCS: [𝟘] is a unit of [‖] and [□], both are commutative and
   associative, [⊕] and [|ₖ] are commutative, and a conditional whose guard
   evaluates is its branch. For the left merge, [E ⌊ 𝟘 ≡ E] and [𝟘 ⌊ E ≡ 𝟘]
   (laws LM4 and LM3; note that [𝟘 ⌊ E] has no transition). The congruence is
   closed under the static contexts and under the prefixes [in(t)], [read(t)]
   and [out(t)]:
   - under [in(t)] and [read(t)], the body is exposed by a substitution of
     values, which preserves the congruence ([cgr_step_subst]);
   - under [out(t)], only between bodies different from [𝟘], as rule IR5
     tests [E = 𝟘] syntactically ([out(t).(𝟘 ‖ 𝟘)] has a τ, [out(t).𝟘] an output).
   It is not closed under [rec]. *)

Section PAL_Alt_Congruence.
  Context (Val : Type) `{Countable Val}.

  Notation term := (term Val).
  Notation step := (lts_step_a Val).

  Open Scope pal_scope.
  Inductive cgr_step : term → term → Prop :=
    (* laws *)
    | cgr_par_nil E : cgr_step (E ‖ 𝟘) E
    | cgr_par_nil_rev E : cgr_step E (E ‖ 𝟘)
    | cgr_par_com E F : cgr_step (E ‖ F) (F ‖ E)
    | cgr_par_assoc E F G : cgr_step ((E ‖ F) ‖ G) (E ‖ (F ‖ G))
    | cgr_par_assoc_rev E F G : cgr_step (E ‖ (F ‖ G)) ((E ‖ F) ‖ G)
    | cgr_choice_nil E : cgr_step (E □ 𝟘) E
    | cgr_choice_nil_rev E : cgr_step E (E □ 𝟘)
    | cgr_choice_com E F : cgr_step (E □ F) (F □ E)
    | cgr_choice_assoc E F G : cgr_step ((E □ F) □ G) (E □ (F □ G))
    | cgr_choice_assoc_rev E F G : cgr_step (E □ (F □ G)) ((E □ F) □ G)
    | cgr_ichoice_com E F : cgr_step (E ⊕ F) (F ⊕ E)
    (* left merge: laws LM4 and LM3 of De Nicola–Pugliese *)
    | cgr_lmerge_nil E : cgr_step (E ⌊ 𝟘) E
    | cgr_lmerge_nil_rev E : cgr_step E (E ⌊ 𝟘)
    | cgr_lmerge_nil_l E : cgr_step (𝟘 ⌊ E) 𝟘
    | cgr_lmerge_nil_l_rev E : cgr_step 𝟘 (𝟘 ⌊ E)
    | cgr_cmerge_com E F : cgr_step (E |ₖ F) (F |ₖ E)
    | cgr_if_true be E F : eval_bexp be = Some true → cgr_step (IF be THEN E ELSE F) E
    | cgr_if_true_rev be E F : eval_bexp be = Some true → cgr_step E (IF be THEN E ELSE F)
    | cgr_if_false be E F : eval_bexp be = Some false → cgr_step (IF be THEN E ELSE F) F
    | cgr_if_false_rev be E F : eval_bexp be = Some false → cgr_step F (IF be THEN E ELSE F)
    (* static contexts *)
    | cgr_par_l E E' F : cgr_step E E' → cgr_step (E ‖ F) (E' ‖ F)
    | cgr_par_r E F F' : cgr_step F F' → cgr_step (E ‖ F) (E ‖ F')
    | cgr_choice_l E E' F : cgr_step E E' → cgr_step (E □ F) (E' □ F)
    | cgr_choice_r E F F' : cgr_step F F' → cgr_step (E □ F) (E □ F')
    | cgr_ichoice_l E E' F : cgr_step E E' → cgr_step (E ⊕ F) (E' ⊕ F)
    | cgr_ichoice_r E F F' : cgr_step F F' → cgr_step (E ⊕ F) (E ⊕ F')
    | cgr_lmerge_l E E' F : cgr_step E E' → cgr_step (E ⌊ F) (E' ⌊ F)
    | cgr_lmerge_r E F F' : cgr_step F F' → cgr_step (E ⌊ F) (E ⌊ F')
    | cgr_cmerge_l E E' F : cgr_step E E' → cgr_step (E |ₖ F) (E' |ₖ F)
    | cgr_cmerge_r E F F' : cgr_step F F' → cgr_step (E |ₖ F) (E |ₖ F')
    | cgr_if_l be E E' F : cgr_step E E' → cgr_step (IF be THEN E ELSE F) (IF be THEN E' ELSE F)
    | cgr_if_r be E F F' : cgr_step F F' → cgr_step (IF be THEN E ELSE F) (IF be THEN E ELSE F')
    | cgr_eval_l E E' F : cgr_step E E' → cgr_step (eval( E ) • F) (eval( E' ) • F)
    | cgr_eval_r E F F' : cgr_step F F' → cgr_step (eval( E ) • F) (eval( E ) • F')
    (* prefixes *)
    | cgr_in t E E' : cgr_step E E' → cgr_step (in( t ) • E) (in( t ) • E')
    | cgr_read t E E' : cgr_step E E' → cgr_step (read( t ) • E) (read( t ) • E')
    | cgr_out t E E' : E ≠ 𝟘 → E' ≠ 𝟘 → cgr_step E E' → cgr_step (out( t ) • E) (out( t ) • E').
  Close Scope pal_scope.

  (** The structural congruence. *)
  Definition cgr : term → term → Prop := rtc cgr_step.

  Lemma cgr_step_symmetric : Symmetric cgr_step.
  Proof. intros E F h. induction h; eauto using cgr_step. Qed.

  #[global] Instance cgr_equivalence : Equivalence cgr.
  Proof. apply rtc_equivalence, cgr_step_symmetric. Qed.

  Lemma cgr_once E F : cgr_step E F → cgr E F.
  Proof. apply rtc_once. Qed.

  Lemma cgr_refl E : cgr E E.
  Proof. reflexivity. Qed.

  (** Lifting [cgr] through the static contexts. *)
  Local Ltac lift C := intros h; induction h as [|x y z hxy _ IH]; [reflexivity | eapply rtc_l; [apply C, hxy | exact IH]].

  Lemma cgr_par_l_lift E E' F : cgr E E' → cgr (t_par E F) (t_par E' F).
  Proof. lift cgr_par_l. Qed.
  Lemma cgr_par_r_lift E F F' : cgr F F' → cgr (t_par E F) (t_par E F').
  Proof. lift cgr_par_r. Qed.
  Lemma cgr_choice_l_lift E E' F : cgr E E' → cgr (t_echoice E F) (t_echoice E' F).
  Proof. lift cgr_choice_l. Qed.
  Lemma cgr_lmerge_l_lift E E' F : cgr E E' → cgr (t_lmerge E F) (t_lmerge E' F).
  Proof. lift cgr_lmerge_l. Qed.
  Lemma cgr_cmerge_l_lift E E' F : cgr E E' → cgr (t_cmerge E F) (t_cmerge E' F).
  Proof. lift cgr_cmerge_l. Qed.
  Lemma cgr_cmerge_r_lift E F F' : cgr F F' → cgr (t_cmerge E F) (t_cmerge E F').
  Proof. lift cgr_cmerge_r. Qed.
  Lemma cgr_choice_r_lift E F F' : cgr F F' → cgr (t_echoice E F) (t_echoice E F').
  Proof. lift cgr_choice_r. Qed.

  Lemma cgr_par_lift E E' F F' : cgr E E' → cgr F F' → cgr (t_par E F) (t_par E' F').
  Proof. intros h1 h2. etransitivity; [apply cgr_par_l_lift, h1 | apply cgr_par_r_lift, h2]. Qed.

  (** Synchronisations read from the other side. *)
  Lemma air12_sym E1 E2 mu1 mu2 E1' E2' :
    step E1 (ActExt mu1) E1' → step E2 (ActExt mu2) E2' → PALA_dual Val mu2 mu1 →
    step (t_par E1 E2) τ (t_par E1' E2').
  Proof. intros h1 h2 hd. eapply air12; [exact h1 | exact h2 | by symmetry]. Qed.

  Lemma air13_sym E1 E2 mu1 mu2 E1' E2' :
    step E1 (ActExt mu1) E1' → step E2 (ActExt mu2) E2' → PALA_dual Val mu2 mu1 →
    step (t_cmerge E1 E2) τ (t_par E1' E2').
  Proof. intros h1 h2 hd. eapply air13; [exact h1 | exact h2 | by symmetry]. Qed.

  (** Steps in contexts, for any label. *)
  Lemma step_par_l E F α E' : step E α E' → step (t_par E F) α (t_par E' F).
  Proof. destruct α; [apply aar5_l | apply air9_l]. Qed.
  Lemma step_par_r E F α F' : step F α F' → step (t_par E F) α (t_par E F').
  Proof. destruct α; [apply aar5_r | apply air9_r]. Qed.

  Lemma no_step_nil α q : ¬ step t_nil α q.
  Proof. inversion 1. Qed.

  Local Hint Constructors lts_step_a cgr_step : pal_cgr.
  Local Hint Resolve cgr_once cgr_refl cgr_par_l_lift cgr_par_r_lift cgr_choice_l_lift cgr_choice_r_lift
    cgr_lmerge_l_lift cgr_cmerge_l_lift cgr_cmerge_r_lift cgr_par_lift
    air12_sym air13_sym step_par_l step_par_r : pal_cgr.

  Local Ltac invert_steps :=
    repeat match goal with
    | h : step t_nil _ _ |- _ => inversion h
    | h : step (t_par _ _) _ _ |- _ => inversion h; subst; clear h
    | h : step (t_echoice _ _) _ _ |- _ => inversion h; subst; clear h
    end.

  Local Ltac use_ih :=
    match goal with
    | IH : ∀ α p', step ?E α p' → ∃ r', _, h : step ?E _ _ |- _ =>
        let r0 := fresh "r" in let h0 := fresh "h" in let c0 := fresh "c" in
        destruct (IH _ _ h) as (r0 & h0 & c0); clear IH
    end.

  (** ** Substitution of values *)

  (** A guard which evaluates has no variable. *)
  Lemma subst_bexp_eval (σ : vsubst Val) be b : eval_bexp be = Some b → subst_bexp σ be = be.
  Proof.
    revert b. induction be as [| | e1 e2 | b1 IH1 b2 IH2 | b1 IH1 b2 IH2 | b1 IH1]; intros b h; cbn in *;
      try done.
    - destruct e1, e2; by try discriminate.
    - destruct (eval_bexp b1) as [r1|] eqn:h1, (eval_bexp b2) as [r2|] eqn:h2; try discriminate.
      by rewrite (IH1 r1), (IH2 r2).
    - destruct (eval_bexp b1) as [r1|] eqn:h1, (eval_bexp b2) as [r2|] eqn:h2; try discriminate.
      by rewrite (IH1 r1), (IH2 r2).
    - destruct (eval_bexp b1) as [r1|] eqn:h1; try discriminate. by rewrite (IH1 r1).
  Qed.

  Lemma subst_term_nil (σ : vsubst Val) E : subst_term σ E = t_nil → E = t_nil.
  Proof. by destruct E. Qed.

  Lemma cgr_step_subst (σ : vsubst Val) E E' : cgr_step E E' → cgr_step (subst_term σ E) (subst_term σ E').
  Proof.
    intros h. revert σ. induction h; intros σ; cbn;
      try (match goal with hb : eval_bexp ?be = Some _ |- _ =>
             rewrite (subst_bexp_eval σ be _ hb) end);
      eauto using cgr_step.
    apply cgr_out; [| | apply IHh]; intros e; apply subst_term_nil in e; contradiction.
  Qed.

  Local Hint Resolve cgr_step_subst : pal_cgr.

  (** One congruence step is a strong simulation. *)
  Lemma cgr_step_simulation p r :
    cgr_step p r → ∀ α p', step p α p' → ∃ r', step r α r' ∧ cgr p' r'.
  Proof.
    induction 1; intros α p' hs.
    all: first
      [ solve [destruct α; eauto 6 with pal_cgr]
      | inversion hs; subst; try congruence; invert_steps; try use_ih; eauto 7 with pal_cgr ].
  Qed.
  (** [cgr] is a strong bisimulation. *)
  Lemma cgr_simulation p r α p' : cgr p r → step p α p' → ∃ r', step r α r' ∧ cgr p' r'.
  Proof.
    intros h. revert α p'. induction h as [|x y z hxy _ IH]; intros α p' hs.
    - exists p'. split; [done | reflexivity].
    - destruct (cgr_step_simulation _ _ hxy _ _ hs) as (y' & hy & cy).
      destruct (IH _ _ hy) as (z' & hz & cz). exists z'. split; [done | by etransitivity].
  Qed.

  Lemma PALA_cgr_spec p q (α : Act (PALA_Act Val)) :
    (∃ r, cgr p r ∧ step r α q) → (∃ r, step p α r ∧ cgr r q).
  Proof.
    intros (r & hpr & hs). symmetry in hpr.
    destruct (cgr_simulation r p α q hpr hs) as (r' & h' & c'). exists r'. split; [done | by symmetry].
  Qed.

  (** ** [gLtsEq]/[gLtsOba]/[gLtsObaFW]/[gLtsObaFB]; the last three are vacuous, no action being non-blocking *)

  #[global] Instance PALA_gLtsEq : gLtsEq term (PALA_ExtAction Val) := {|
    gLtsEq_gLts := PALA_gLts Val;
    eq_rel := cgr;
    eq_rel_eq := cgr_equivalence;
    eq_spec := PALA_cgr_spec;
  |}.

  #[global] Instance PALA_gLtsOba : gLtsOba term (H:=PALA_ExtAction Val) (Rel:=PALA_gLtsEq).
  Proof.
    unshelve econstructor.
    - intros p q r eta alpha nb Hl1 Hl2. destruct nb.
    - intros p q1 q2 eta mu nb Hne Hl1 Hl2. destruct nb.
    - intros p q1 q2 eta nb Hl1 Hl2. destruct nb.
    - intros p1 p2 p3 eta nb Hl1 Hl2. destruct nb.
    - intros p1 p2 q1 q2 eta nb Hl1 Hl2 Heq. destruct nb.
  Defined.

  #[global] Instance PALA_gLtsObaFW : gLtsObaFW term (PALA_Act Val).
  Proof.
    unshelve econstructor.
    - intros p1 eta beta. exists p1. intro nb. destruct nb.
    - intros p1 p2 p3 eta beta nb Hdual Hl1 Hl2. destruct nb.
  Defined.

  #[global] Instance PALA_gLtsObaFB : gLtsObaFB term (PALA_Act Val).
  Proof.
    unshelve econstructor.
    intros p1 p2 p3 eta beta nb Hdual Hl1 Hl2. destruct nb.
  Defined.
End PAL_Alt_Congruence.
