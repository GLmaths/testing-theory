(* begin hide *)
From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base countable list sets.
From TestingTheory Require Import ActTau PAL.Language.Syntax PAL.Language.LTS PAL.Language.Phi.
Import ListNotations.

Section PAL_Value_Swap.

Context (Val : Type) `{Countable Val}.

Definition swv (a b v : Val) : Val := if decide (v = a) then b else if decide (v = b) then a else v.

Lemma swv_invol a b v : swv a b (swv a b v) = v.
Proof. unfold swv. repeat case_decide; subst; congruence. Qed.

Lemma swv_inj a b v w : swv a b v = swv a b w → v = w.
Proof. intros h. by rewrite <- (swv_invol a b v), <- (swv_invol a b w), h. Qed.

Definition sw_vexp a b (e : vexp Val) : vexp Val :=
  match e with
  | ve_var x => ve_var x
  | ve_val v => ve_val (swv a b v)
  end.

Definition sw_field a b (f : field Val) : field Val :=
  match f with
  | f_formal x => f_formal x
  | f_actual e => f_actual (sw_vexp a b e)
  | f_star => f_star
  end.

Definition sw_tuple a b (t : tuple Val) : tuple Val := map (sw_field a b) t.

Fixpoint sw_bexp a b (be : bexp Val) : bexp Val :=
  match be with
  | b_true => b_true
  | b_false => b_false
  | b_eq e1 e2 => b_eq (sw_vexp a b e1) (sw_vexp a b e2)
  | b_and b1 b2 => b_and (sw_bexp a b b1) (sw_bexp a b b2)
  | b_or b1 b2 => b_or (sw_bexp a b b1) (sw_bexp a b b2)
  | b_not b1 => b_not (sw_bexp a b b1)
  end.

Fixpoint sw_term a b (E : term Val) : term Val :=
  match E with
  | t_nil => t_nil
  | t_undef => t_undef
  | t_out t E1 => t_out (sw_tuple a b t) (sw_term a b E1)
  | t_in t E1 => t_in (sw_tuple a b t) (sw_term a b E1)
  | t_read t E1 => t_read (sw_tuple a b t) (sw_term a b E1)
  | t_eval E1 E2 => t_eval (sw_term a b E1) (sw_term a b E2)
  | t_if be E1 E2 => t_if (sw_bexp a b be) (sw_term a b E1) (sw_term a b E2)
  | t_ichoice E1 E2 => t_ichoice (sw_term a b E1) (sw_term a b E2)
  | t_echoice E1 E2 => t_echoice (sw_term a b E1) (sw_term a b E2)
  | t_par E1 E2 => t_par (sw_term a b E1) (sw_term a b E2)
  | t_lmerge E1 E2 => t_lmerge (sw_term a b E1) (sw_term a b E2)
  | t_cmerge E1 E2 => t_cmerge (sw_term a b E1) (sw_term a b E2)
  | t_pvar X => t_pvar X
  | t_rec X E1 => t_rec X (sw_term a b E1)
  | t_success => t_success
  end.

Definition sw_of a b (o : out_field Val) : out_field Val :=
  match o with
  | of_star => of_star
  | of_val v => of_val (swv a b v)
  end.

Definition sw_eot a b (ot : eot Val) : eot Val := map (sw_of a b) ot.

Definition sw_if a b (f : in_field Val) : in_field Val :=
  match f with
  | if_formal x => if_formal x
  | if_val v => if_val (swv a b v)
  | if_star => if_star
  end.

Definition sw_eit a b (it : eit Val) : eit Val := map (sw_if a b) it.

Definition sw_tf a b (f : tfield Val) : tfield Val :=
  match f with
  | tf_formal _ => tf_formal Val
  | tf_val _ v => tf_val Val (swv a b v)
  | tf_star _ => tf_star Val
  end.

Definition sw_template a b (tp : template Val) : template Val := map (sw_tf a b) tp.

Definition sw_lf a b (f : lfield Val) : lfield Val :=
  match f with
  | lf_formal _ v => lf_formal Val (swv a b v)
  | lf_val _ v => lf_val Val (swv a b v)
  | lf_star _ => lf_star Val
  end.

Definition sw_label a b (l : label Val) : label Val := map (sw_lf a b) l.

Definition sw_act a b (μ : PALA_Act Val) : PALA_Act Val :=
  match μ with
  | AIn _ l => AIn Val (sw_label a b l)
  | AOut _ ot => AOut Val (sw_eot a b ot)
  end.

Definition sw_lab a b (α : Labels (PALA_Act Val)) : Labels (PALA_Act Val) :=
  match α with
  | ActExt μ => ActExt (sw_act a b μ)
  | τ => τ
  end.

Definition sw_event a b (e : Event Val) : Event Val :=
  match e with
  | EvIn _ tp => EvIn Val (sw_template a b tp)
  | EvOut _ ot => EvOut Val (sw_eot a b ot)
  end.

Definition sw_σ a b (σ : vsubst Val) : vsubst Val := map (λ p, (p.1, swv a b p.2)) σ.

Lemma map_invol {X} (f : X → X) (l : list X) : (∀ x, f (f x) = x) → map f (map f l) = l.
Proof. intros h. induction l as [| x l IH]; simpl; [done | by rewrite h, IH]. Qed.

Lemma sw_term_invol a b E : sw_term a b (sw_term a b E) = E.
Proof.
  assert (hv : ∀ e, sw_vexp a b (sw_vexp a b e) = e) by (intros []; simpl; rewrite ?swv_invol; done).
  assert (hf : ∀ f, sw_field a b (sw_field a b f) = f) by (intros []; simpl; rewrite ?hv; done).
  assert (ht : ∀ t, sw_tuple a b (sw_tuple a b t) = t) by (intros t; apply map_invol, hf).
  assert (hb : ∀ be, sw_bexp a b (sw_bexp a b be) = be) by (induction be; simpl; rewrite ?hv; congruence).
  induction E; simpl; rewrite ?ht, ?hb; congruence.
Qed.

Lemma sw_act_invol a b μ : sw_act a b (sw_act a b μ) = μ.
Proof.
  destruct μ as [l | ot]; simpl; f_equal; apply map_invol;
    intros []; simpl; by rewrite ?swv_invol.
Qed.

Lemma sw_event_invol a b e : sw_event a b (sw_event a b e) = e.
Proof.
  destruct e as [tp | ot]; simpl; f_equal; apply map_invol;
    intros []; simpl; by rewrite ?swv_invol.
Qed.

Lemma sw_eval_out_tuple a b t : eval_out_tuple (sw_tuple a b t) = sw_eot a b <$> eval_out_tuple t.
Proof.
  induction t as [| f t IH]; [done |]. unfold eval_out_tuple in *. simpl. rewrite IH.
  destruct f as [x | [x | v] |]; simpl; destruct (mapM eval_out_field t); reflexivity.
Qed.

Lemma sw_eval_in_tuple a b t : eval_in_tuple (sw_tuple a b t) = sw_eit a b <$> eval_in_tuple t.
Proof.
  induction t as [| f t IH]; [done |]. unfold eval_in_tuple in *. simpl. rewrite IH.
  destruct f as [x | [x | v] |]; simpl; destruct (mapM eval_in_field t); reflexivity.
Qed.

Lemma sw_template_of a b it : template_of Val (sw_eit a b it) = sw_template a b (template_of Val it).
Proof. induction it as [| [] it IH]; simpl; f_equal; done. Qed.

Lemma sw_ltemplate a b l : ltemplate Val (sw_label a b l) = sw_template a b (ltemplate Val l).
Proof. induction l as [| [] l IH]; simpl; f_equal; done. Qed.

Lemma sw_ltuple a b l : ltuple Val (sw_label a b l) = sw_eot a b (ltuple Val l).
Proof. induction l as [| [] l IH]; simpl; f_equal; done. Qed.

Lemma sw_build_subst a b it ot : build_subst (sw_eit a b it) (sw_eot a b ot) = sw_σ a b (build_subst it ot).
Proof.
  revert ot. induction it as [| f it IH]; intros [| o ot]; simpl; try done.
  - by destruct f.
  - destruct f, o; simpl; rewrite ?IH; reflexivity.
Qed.

Lemma sw_vlookup a b σ x : vlookup (sw_σ a b σ) x = swv a b <$> vlookup σ x.
Proof. induction σ as [| [y v] σ IH]; simpl; [done |]. case_decide; [done | exact IH]. Qed.

Lemma filter_map_inv {X} (P : X → Prop) `{∀ x, Decision (P x)} (f : X → X) (l : list X) :
  (∀ x, P (f x) ↔ P x) → filter P (map f l) = map f (filter P l).
Proof.
  intros hP. induction l as [| x l IH]; [done |]. cbn [map]. rewrite !filter_cons.
  destruct (decide (P (f x))) as [h | h], (decide (P x)) as [h' | h']; cbn [map]; rewrite ?IH;
    try reflexivity; exfalso; [apply h', hP, h | apply h, hP, h'].
Qed.

Lemma sw_vsubst_drop a b xs σ : vsubst_drop xs (sw_σ a b σ) = sw_σ a b (vsubst_drop xs σ).
Proof. unfold vsubst_drop, sw_σ. apply filter_map_inv. intros [x v]. reflexivity. Qed.

Lemma sw_tuple_formals a b t : tuple_formals (sw_tuple a b t) = tuple_formals t.
Proof. unfold tuple_formals, sw_tuple. induction t as [| [] t IH]; [done | ..]; cbn [map omap list_omap]; rewrite ?IH; reflexivity. Qed.

Lemma sw_subst_vexp a b σ e : subst_vexp (sw_σ a b σ) (sw_vexp a b e) = sw_vexp a b (subst_vexp σ e).
Proof. destruct e as [x | v]; simpl; [rewrite sw_vlookup; by destruct (vlookup σ x) | done]. Qed.

Lemma sw_subst_tuple a b σ t : subst_tuple (sw_σ a b σ) (sw_tuple a b t) = sw_tuple a b (subst_tuple σ t).
Proof.
  induction t as [| f t IH]; [done |]. unfold subst_tuple, sw_tuple in *. simpl. rewrite IH.
  destruct f; simpl; rewrite ?sw_subst_vexp; reflexivity.
Qed.

Lemma sw_subst_bexp a b σ be : subst_bexp (sw_σ a b σ) (sw_bexp a b be) = sw_bexp a b (subst_bexp σ be).
Proof. induction be; simpl; rewrite ?sw_subst_vexp; congruence. Qed.

Lemma sw_subst_term a b E : ∀ σ, subst_term (sw_σ a b σ) (sw_term a b E) = sw_term a b (subst_term σ E).
Proof.
  induction E; intros σ; simpl;
    rewrite ?sw_subst_tuple, ?sw_subst_bexp, ?sw_tuple_formals, ?sw_vsubst_drop; congruence.
Qed.

Lemma sw_psubst a b X Q E : sw_term a b (psubst X Q E) = psubst X (sw_term a b Q) (sw_term a b E).
Proof. induction E; simpl; try case_decide; simpl; congruence. Qed.

Lemma sw_eot_to_tuple a b ot : eot_to_tuple (sw_eot a b ot) = sw_tuple a b (eot_to_tuple ot).
Proof. induction ot as [| [] ot IH]; simpl; f_equal; done. Qed.

Lemma sw_eval_bexp a b be : eval_bexp (sw_bexp a b be) = eval_bexp be.
Proof.
  induction be; simpl; rewrite ?IHbe, ?IHbe1, ?IHbe2; try reflexivity.
  destruct e1, e2; simpl; try reflexivity. f_equal.
  apply bool_decide_ext. split; [apply swv_inj | intros ->; reflexivity].
Qed.

Lemma sw_term_nil a b E : E ≠ t_nil → sw_term a b E ≠ t_nil.
Proof. intros h e. apply h. rewrite <- (sw_term_invol a b E), e. reflexivity. Qed.

Lemma sw_dual a b μ1 μ2 : PALA_dual Val μ1 μ2 → PALA_dual Val (sw_act a b μ1) (sw_act a b μ2).
Proof. destruct μ1, μ2; simpl; try done; intros <-; apply sw_ltuple. Qed.

Lemma lts_sw a b E α E' : lts_step_a Val E α E' → lts_step_a Val (sw_term a b E) (sw_lab a b α) (sw_term a b E').
Proof.
  induction 1; simpl.
  - rewrite <- sw_subst_term, <- sw_build_subst, <- sw_ltuple. apply (aar1 Val _ _ (sw_eit a b it)).
    + rewrite sw_eval_in_tuple, H0. reflexivity.
    + rewrite sw_template_of, H1, sw_ltemplate. reflexivity.
  - rewrite <- sw_subst_term, <- sw_build_subst, <- sw_eot_to_tuple, <- !sw_ltuple.
    apply (aar2 Val _ _ (sw_eit a b it)).
    + rewrite sw_eval_in_tuple, H0. reflexivity.
    + rewrite sw_template_of, H1, sw_ltemplate. reflexivity.
  - apply aar3. rewrite sw_eval_out_tuple, H0. reflexivity.
  - by apply aar4_l.
  - by apply aar4_r.
  - by apply aar5_l.
  - by apply aar5_r.
  - by apply aar6.
  - apply aar7; [by rewrite sw_eval_bexp | done].
  - apply aar8; [by rewrite sw_eval_bexp | done].
  - apply air1.
  - rewrite sw_psubst. apply air2.
  - apply air3; [by rewrite sw_eval_bexp | done].
  - apply air4; [by rewrite sw_eval_bexp | done].
  - apply air5. by apply sw_term_nil.
  - apply air6.
  - apply air7_l.
  - apply air7_r.
  - by apply air8_l.
  - by apply air8_r.
  - by apply air9_l.
  - by apply air9_r.
  - by apply air10_l.
  - by apply air10_r.
  - by apply air11.
  - eapply air12; [exact IHlts_step_a1 | exact IHlts_step_a2 | by apply sw_dual].
  - eapply air13; [exact IHlts_step_a1 | exact IHlts_step_a2 | by apply sw_dual].
Qed.

End PAL_Value_Swap.
(* end hide *)
