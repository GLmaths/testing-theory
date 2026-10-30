(* begin hide *)
From Stdlib.Unicode Require Import Utf8.
From Stdlib Require Import Lia.
From stdpp Require Import base countable gmap list sets sorting.
From TestingTheory Require Import Termination ActTau gLts Bisimulation SyncActions Must RelationKernel Subset_Act
  Lts_OBA Lts_FW Lts_OBA_FB LtsFW InteractionBetweenLts Testing_Predicate InListPropHelper
  coFiniteImage coConvergence coWeakTransition DefinitionASrel CompletenessASco
  Label_Abstraction.LabelAbstraction
  PAL.Language.Syntax PAL.Language.LTS PAL.Language.Phi PAL.Language.AbsAction PAL.Language.Congruence
  PAL.Language.Dichotomy PAL.Language.Label_Abstraction PAL.Language.Value_Swap PAL.Language.Divergence PAL_Good PAL.Testing.Must_Preorder
  PAL.Testing.Tests PAL.Testing.Test_Spec PAL.Testing.CoTrace_Hypotheses PAL.Characterisations.Must_Characterisation
  Decision.Tools_in_construction.Inductive.Generic.Helpers Decision.Tools_in_construction.Inductive.Generic.Acceptance_Tests_Gamma
  Decision.Tools_in_construction.Inductive.PAL.Tests Decision.Tools_in_construction.Inductive.Generic.Bisim Decision.Tools_in_construction.Inductive.Generic.Interface Decision.Tools_in_construction.Inductive.Generic.Sets Decision.Tools_in_construction.Inductive.Generic.Graph Decision.Tools_in_construction.Inductive.Generic.Swaps Decision.Tools_in_construction.Inductive.Generic.Adequacy Decision.Tools_in_construction.Inductive.Generic.Verdict.
Import ListNotations.

#[local] Hint Mode ExtAction ! : typeclass_instances.

Section PAL_Trace_Search.

Notation proc := (term nat).
Notation A := (PALA_Act nat).

Notation Γᴘᴀʟ := (λ μ : A, αᴘᴇᴠ nat (αᴛᴀᴘᴀʟ nat μ)).

#[local] Instance SyncAction_PAL : SyncAction A A := SyncAction_of_dual.

Definition atoms_vexp (e : vexp nat) : list nat :=
  match e with
  | ve_var _ => []
  | ve_val v => [v]
  end.

Definition atoms_field (f : field nat) : list nat :=
  match f with
  | f_actual e => atoms_vexp e
  | _ => []
  end.

Definition atoms_tuple (t : tuple nat) : list nat := flat_map atoms_field t.

Fixpoint atoms_bexp (be : bexp nat) : list nat :=
  match be with
  | b_eq e1 e2 => atoms_vexp e1 ++ atoms_vexp e2
  | b_and b1 b2 | b_or b1 b2 => atoms_bexp b1 ++ atoms_bexp b2
  | b_not b1 => atoms_bexp b1
  | _ => []
  end.

Fixpoint atoms_term (E : proc) : list nat :=
  match E with
  | t_out t E1 | t_in t E1 | t_read t E1 => atoms_tuple t ++ atoms_term E1
  | t_eval E1 E2 | t_ichoice E1 E2 | t_echoice E1 E2 | t_par E1 E2 | t_lmerge E1 E2 | t_cmerge E1 E2 =>
      atoms_term E1 ++ atoms_term E2
  | t_if be E1 E2 => atoms_bexp be ++ atoms_term E1 ++ atoms_term E2
  | t_rec _ E1 => atoms_term E1
  | _ => []
  end.

Lemma swv_fix (a b v : nat) : v ≠ a → v ≠ b → swv nat a b v = v.
Proof. intros ha hb. unfold swv. repeat case_decide; congruence. Qed.

Lemma sw_vexp_fix a b e : a ∉ atoms_vexp e → b ∉ atoms_vexp e → sw_vexp nat a b e = e.
Proof. destruct e as [x | v]; simpl; intros ha hb; [done |]. rewrite swv_fix; set_solver. Qed.

Lemma sw_tuple_fix a b t : a ∉ atoms_tuple t → b ∉ atoms_tuple t → sw_tuple nat a b t = t.
Proof.
  unfold sw_tuple. induction t as [| f t IH]; simpl; intros ha hb; [done |]. f_equal; [| apply IH; set_solver].
  destruct f as [x | e |]; simpl in *; [done | | done]. rewrite sw_vexp_fix by set_solver. done.
Qed.

Lemma sw_bexp_fix a b be : a ∉ atoms_bexp be → b ∉ atoms_bexp be → sw_bexp nat a b be = be.
Proof. induction be; simpl; intros ha hb; rewrite ?sw_vexp_fix, ?IHbe, ?IHbe1, ?IHbe2 by set_solver; done. Qed.

Lemma sw_term_fix a b E : a ∉ atoms_term E → b ∉ atoms_term E → sw_term nat a b E = E.
Proof.
  induction E; simpl; intros ha hb;
    rewrite ?sw_tuple_fix, ?sw_bexp_fix, ?IHE, ?IHE1, ?IHE2 by set_solver; done.
Qed.

Definition atoms_lf (f : lfield nat) : list nat :=
  match f with
  | lf_formal _ v | lf_val _ v => [v]
  | lf_star _ => []
  end.

Definition atoms_of (o : out_field nat) : list nat :=
  match o with
  | of_val v => [v]
  | of_star => []
  end.

Definition atoms_act (μ : A) : list nat :=
  match μ with
  | AIn _ l => flat_map atoms_lf l
  | AOut _ ot => flat_map atoms_of ot
  end.

Lemma atoms_act_swap a b μ : atoms_act (sw_act nat a b μ) = map (swv nat a b) (atoms_act μ).
Proof.
  destruct μ as [l | ot]; simpl.
  - induction l as [| [] l IH]; simpl; [done | ..]; by rewrite IH.
  - induction ot as [| [] ot IH]; simpl; [done | ..]; by rewrite IH.
Qed.

Fixpoint gen_ots (vals : list nat) (tp : template nat) : list (eot nat) :=
  match tp with
  | [] => [[]]
  | tf_formal _ :: tp' => flat_map (λ v, map (cons (of_val v)) (gen_ots vals tp')) vals
  | tf_val _ v :: tp' => map (cons (of_val v)) (gen_ots vals tp')
  | tf_star _ :: tp' => map (cons of_star) (gen_ots vals tp')
  end.

Lemma gen_ots_spec vals (l : label nat) :
  (∀ v, v ∈ flat_map atoms_of (ltuple nat l) → v ∈ vals) → ltuple nat l ∈ gen_ots vals (ltemplate nat l).
Proof.
  induction l as [| f l IH]; simpl; intros hv; [by left |].
  destruct f as [v | v |]; simpl in *.
  - apply elem_of_flat_map_list. exists v. split; [apply hv; left |].
    apply elem_of_map_list. exists (ltuple nat l). split; [reflexivity |]. apply IH. intros w m. apply hv. right. exact m.
  - apply elem_of_map_list. exists (ltuple nat l). split; [reflexivity |]. apply IH. intros w m. apply hv. right. exact m.
  - apply elem_of_map_list. exists (ltuple nat l). split; [reflexivity |]. exact (IH hv).
Qed.

Definition next_pal (vals : list nat) (E : proc) : list A :=
  flat_map (λ tp, map (AOut nat) (gen_ots vals tp)) (collect_in_a nat E) ++
  flat_map (λ ot, map (AIn nat) (labels_of nat ot)) (collect_out_a nat E).

Lemma next_pal_spec vals (E : proc) μ μ' E' :
  sync μ' μ → E ⟶[μ'] E' → (∀ a, a ∈ atoms_act μ → a ∈ vals) → μ ∈ next_pal vals E.
Proof.
  intros duo l hv. unfold next_pal. rewrite elem_of_app.
  destruct μ' as [l' | ot'], μ as [l0 | ot0]; simpl in duo; try contradiction.
  - left. subst ot0. apply elem_of_flat_map_list. exists (ltemplate nat l'). split.
    + apply list_elem_of_In. exact (in_step_in_collect_in_a nat E l' E' l).
    + apply elem_of_map_list. exists (ltuple nat l'). split; [reflexivity |]. apply gen_ots_spec. exact hv.
  - right. apply elem_of_flat_map_list. exists ot'. split.
    + apply list_elem_of_In. exact (out_step_in_collect_out_a nat E ot' E' l).
    + apply elem_of_map_list. exists l0. split; [reflexivity |].
      apply list_elem_of_In, labels_of_spec. exact duo.
Qed.

Definition arity_pal (E : proc) : nat :=
  foldr max 0 (map length (collect_in_a nat E) ++ map length (collect_out_a nat E)).

Lemma foldr_max_spec (l : list nat) j : j ∈ l → j ≤ foldr max 0 l.
Proof. induction l as [| x l IH]; simpl; intros m; [inversion m |]. apply elem_of_cons in m as [-> | m]; [lia | specialize (IH m); lia]. Qed.

Lemma atoms_lf_length (l : label nat) : length (flat_map atoms_lf l) ≤ length (ltemplate nat l).
Proof. induction l as [| [] l IH]; simpl; lia. Qed.

Lemma atoms_of_length (ot : eot nat) : length (flat_map atoms_of ot) ≤ length ot.
Proof. induction ot as [| [] ot IH]; simpl; lia. Qed.

Lemma ltuple_length (l : label nat) : length (ltuple nat l) = length (ltemplate nat l).
Proof. unfold ltuple, ltemplate. by rewrite !length_map. Qed.

Lemma arity_pal_spec (E : proc) (μ μ' : A) E' : sync μ' μ → E ⟶[μ'] E' → length (atoms_act μ) ≤ arity_pal E.
Proof.
  intros duo l. destruct μ' as [l' | ot'], μ as [l0 | ot0]; simpl in duo; try contradiction; simpl.
  - subst ot0. pose proof (atoms_of_length (ltuple nat l')) as h. rewrite ltuple_length in h.
    assert (length (ltemplate nat l') ≤ arity_pal E); [| lia].
    apply foldr_max_spec, elem_of_app. left. apply elem_of_map_list. exists (ltemplate nat l').
    split; [reflexivity |]. apply list_elem_of_In. exact (in_step_in_collect_in_a nat E l' E' l).
  - pose proof (atoms_lf_length l0) as h. rewrite <- ltuple_length, duo in h.
    assert (length ot' ≤ arity_pal E); [| lia].
    apply foldr_max_spec, elem_of_app. right. apply elem_of_map_list. exists ot'.
    split; [reflexivity |]. apply list_elem_of_In. exact (out_step_in_collect_out_a nat E ot' E' l).
Qed.

Definition pool (avoid : list nat) (N : nat) : list nat := (λ i, Nat.add (S (foldr max 0 avoid)) i) <$> seq 0 N.

Lemma pool_avoid avoid N f : f ∈ pool avoid N → f ∉ avoid.
Proof. intros (i & -> & _)%list_elem_of_fmap m. apply foldr_max_spec in m. lia. Qed.

Lemma pool_spec avoid N a M :
  length M ≤ N → a ∈ M → a ∉ pool avoid N → ∃ f, f ∈ pool avoid N ∧ f ∉ M ∧ swv nat a f a = f.
Proof.
  intros hM ha hap. destruct (decide (Forall (λ f, f ∈ M) (pool avoid N))) as [h | h].
  - exfalso. assert (a :: pool avoid N ⊆+ M) as sub.
    { apply NoDup_submseteq.
      - constructor; [exact hap |]. apply NoDup_fmap_2; [intros i j e; lia | apply NoDup_seq].
      - intros x [-> | m]%elem_of_cons; [exact ha | rewrite Forall_forall in h; exact (h x m)]. }
    apply submseteq_length in sub. simpl in sub. unfold pool in sub. rewrite length_fmap, length_seq in sub. lia.
  - apply not_Forall_Exists, Exists_exists in h as (f & m & hf); [| intros x; apply _].
    exists f. split_and!; [exact m | exact hf |]. unfold swv. rewrite decide_True; reflexivity.
Qed.

Lemma swap_atom_other (a b c : nat) : c ≠ a → c ≠ b → swv nat a b c = c.
Proof. exact (swv_fix a b c). Qed.

Lemma pal_step_swap a b (E : proc) μ E' : E ⟶[μ] E' → sw_term nat a b E ⟶[sw_act nat a b μ] sw_term nat a b E'.
Proof. exact (lts_sw nat a b E (ActExt μ) E'). Qed.

Lemma pal_tau_swap a b (E E' : proc) : E ⟶ E' → sw_term nat a b E ⟶ sw_term nat a b E'.
Proof. exact (lts_sw nat a b E τ E'). Qed.

Lemma pal_Γ_swap a b μ : Γᴘᴀʟ (sw_act nat a b μ) = sw_event nat a b (Γᴘᴀʟ μ).
Proof. destruct μ as [l | ot]; simpl; [by rewrite sw_ltemplate | reflexivity]. Qed.

Definition is_nil (E : proc) : bool :=
  match E with
  | t_nil => true
  | _ => false
  end.

Lemma is_nil_spec E : is_nil E = true → E = t_nil.
Proof. destruct E; try discriminate. reflexivity. Qed.

Definition leaf (E : proc) : list proc := if is_nil E then [] else [E].

Fixpoint par_comps (E : proc) : list proc :=
  match E with
  | t_par E1 E2 => par_comps E1 ++ par_comps E2
  | _ => leaf E
  end.

Fixpoint par_build (l : list proc) : proc :=
  match l with
  | [] => t_nil
  | [a] => a
  | a :: l => t_par a (par_build l)
  end.

Definition proc_le (a b : proc) : Prop := Pos.leb (encode a) (encode b) = true.

#[local] Instance proc_le_dec : RelDecision proc_le :=
  λ a b, decide (Pos.leb (encode a) (encode b) = true).

Definition sort_procs (l : list proc) : list proc := merge_sort proc_le l.

Notation "E ≡ₚₐₗ F" := (cgr nat E F) (at level 70).

Lemma leaf_cgr E : par_build (leaf E) ≡ₚₐₗ E.
Proof. unfold leaf. destruct (is_nil E) eqn:e; [apply is_nil_spec in e as ->; apply cgr_refl | apply cgr_refl]. Qed.

Lemma par_build_cons a l : par_build (a :: l) ≡ₚₐₗ t_par a (par_build l).
Proof. destruct l; [apply cgr_once, cgr_par_nil_rev | apply cgr_refl]. Qed.

Lemma par_build_app l1 l2 : par_build (l1 ++ l2) ≡ₚₐₗ t_par (par_build l1) (par_build l2).
Proof.
  induction l1 as [| a l1 IH].
  - etransitivity; [apply cgr_once, cgr_par_nil_rev | apply cgr_once, cgr_par_com].
  - etransitivity; [apply par_build_cons |].
    etransitivity; [apply cgr_par_lift; [apply cgr_refl | exact IH] |].
    etransitivity; [apply cgr_once, cgr_par_assoc_rev |].
    apply cgr_par_lift; [symmetry; apply par_build_cons | apply cgr_refl].
Qed.

Lemma par_build_perm l1 l2 : l1 ≡ₚ l2 → par_build l1 ≡ₚₐₗ par_build l2.
Proof.
  induction 1 as [| x l l' _ IH | x y l | l l' l'' _ IH1 _ IH2].
  - apply cgr_refl.
  - etransitivity; [apply par_build_cons |].
    etransitivity; [apply cgr_par_lift; [apply cgr_refl | exact IH] |]. symmetry. apply par_build_cons.
  - etransitivity; [apply par_build_cons |].
    etransitivity; [apply cgr_par_lift; [apply cgr_refl | apply par_build_cons] |].
    etransitivity; [apply cgr_once, cgr_par_assoc_rev |].
    etransitivity; [apply cgr_par_lift; [apply cgr_once, cgr_par_com | apply cgr_refl] |].
    etransitivity; [apply cgr_once, cgr_par_assoc |]. symmetry.
    etransitivity; [apply par_build_cons |]. apply cgr_par_lift; [apply cgr_refl | apply par_build_cons].
  - etransitivity; [exact IH1 | exact IH2].
Qed.

Lemma par_comps_cgr E : par_build (par_comps E) ≡ₚₐₗ E.
Proof.
  induction E; cbn [par_comps]; try apply leaf_cgr.
  etransitivity; [apply par_build_app | apply cgr_par_lift; assumption].
Qed.

Fixpoint pal_nf (E : proc) : proc :=
  match E with
  | t_par E1 E2 => par_build (sort_procs (par_comps (pal_nf E1) ++ par_comps (pal_nf E2)))
  | _ => E
  end.

Lemma pal_nf_cgr E : pal_nf E ≡ₚₐₗ E.
Proof.
  induction E; simpl; try apply cgr_refl.
  etransitivity; [apply par_build_perm, merge_sort_Permutation |].
  etransitivity; [apply par_build_app |].
  etransitivity; [apply cgr_par_lift; apply par_comps_cgr |]. apply cgr_par_lift; assumption.
Qed.

Lemma pal_nf_spec (E : proc) : sbisim (pal_nf E) E.
Proof. exact (eq_sbisim (gLtsEqP := PALA_gLtsEq nat) _ _ (pal_nf_cgr E)). Qed.

Lemma pal_div (E : proc) : act_div nat E = true → ¬ E ⤓.
Proof.
  intros h t. revert h. induction t as [E _ IH]. intros h.
  destruct (act_div_step nat E h) as (E' & l & h'). exact (IH E' l h').
Qed.

Lemma pal_tau_next_spec (p q : proc) : q ∈ all_steps_a nat p τ ↔ lts_step_a nat p τ q.
Proof. rewrite list_elem_of_In. split; [apply all_steps_a_sound | apply all_steps_a_complete]. Qed.

Lemma pal_co_next_spec (p : proc) (μ : A) (q : proc) :
  q ∈ co_next_a nat p μ ↔ ∃ μ', PALA_dual nat μ' μ ∧ lts_step_a nat p (ActExt μ') q.
Proof. rewrite list_elem_of_In. apply co_next_a_spec. Qed.

Fixpoint pal_size (E : proc) : nat :=
  match E with
  | t_out _ E1 | t_in _ E1 | t_read _ E1 | t_rec _ E1 => S (pal_size E1)
  | t_eval E1 E2 | t_if _ E1 E2 | t_ichoice E1 E2 | t_echoice E1 E2 | t_par E1 E2 | t_lmerge E1 E2 | t_cmerge E1 E2 =>
      S (Nat.add (pal_size E1) (pal_size E2))
  | _ => 1
  end.

#[global] Instance PAL_TraceSearch : TraceSearchLang proc A nat (Event nat) proc :=
  {| ts_Γ := Γᴘᴀʟ;
     ts_dichotomy := PALA_coR_dichotomy;
     ts_must p t := p must_pass t;
     ts_tc := t_conv nat;
     ts_ta := ta nat;
     ts_tc_spec := must_iff_cocnv_PAL;
     ts_ta_spec p q q' s X hp w st hXC hXS := ta_distinguishes p q q' s hp X w st hXC hXS;
     ts_swap := sw_term nat;
     ts_swap_act := sw_act nat;
     ts_swap_atom := swv nat;
     ts_swap_pre := sw_event nat;
     ts_swap_invol := sw_term_invol nat;
     ts_swap_act_invol := sw_act_invol nat;
     ts_swap_pre_invol := sw_event_invol nat;
     ts_swap_atom_other := swap_atom_other;
     ts_step_swap := pal_step_swap;
     ts_tau_swap := pal_tau_swap;
     ts_sync_swap := sw_dual nat;
     ts_nb_swap _ _ _ h := h;
     ts_Γ_swap := pal_Γ_swap;
     ts_atoms := atoms_term;
     ts_atoms_act := atoms_act;
     ts_atoms_act_swap := atoms_act_swap;
     ts_swap_fix := sw_term_fix;
     ts_next := next_pal;
     ts_next_spec := next_pal_spec;
     ts_arity := arity_pal;
     ts_arity_spec := arity_pal_spec;
     ts_pool := pool;
     ts_pool_avoid := pool_avoid;
     ts_pool_spec := pool_spec;
     ts_tau_next p := all_steps_a nat p τ;
     ts_tau_next_spec := pal_tau_next_spec;
     ts_co_next := co_next_a nat;
     ts_co_next_spec := pal_co_next_spec;
     ts_div := act_div nat;
     ts_div_spec := pal_div;
     ts_norm := pal_nf;
     ts_norm_spec := pal_nf_spec;
     ts_hash := pal_size |}.

Lemma ρ_incl_of_Γ_incl (S S' : subset_of A) :
  ⌈ Γᴘᴀʟ ⌉ S ⊆ ⌈ Γᴘᴀʟ ⌉ S' → ⌈ ρ[𝔸ᴘᴀʟ] ⌉ S ⊆ ⌈ ρ[𝔸ᴘᴀʟ] ⌉ S'.
Proof.
  intros h x (μ & hμ & ->).
  destruct (h (Γᴘᴀʟ μ)) as (μ' & hμ' & e); [by exists μ |].
  exists μ'. split; [exact hμ' |]. by apply ρᴘᴀʟ_eq.
Qed.

Definition pal_verdict (m k n : nat) (p q : proc) : result := verdict m k n p q.

Theorem pal_verdict_holds (m k n : nat) (p q : proc) : pal_verdict m k n p q = R_holds → p ᴘᴀʟ⊑ₘᵤₛₜᵢ q.
Proof.
  intros h. pose proof (verdict_holds m k n p q h) as hc.
  apply PAL_Alt_equivalence. split.
  - intros s hp. exact (proj1 (hc s) hp).
  - intros s q' hp w st. destruct (proj2 (hc s) q' hp w st) as (p' & w' & st' & sub).
    exists p'. split_and!; [exact w' | exact st' | exact (ρ_incl_of_Γ_incl _ _ sub)].
Qed.

Theorem pal_verdict_refutes (m k n : nat) (p q : proc) s t : pal_verdict m k n p q = R_fails s t → ¬ p ᴘᴀʟ⊑ₘᵤₛₜᵢ q.
Proof.
  intros h. destruct (verdict_fails m k n p q s t h) as [h1 h2].
  exact (distinguishing_test_refutes p q t h1 h2).
Qed.

End PAL_Trace_Search.
(* end hide *)
