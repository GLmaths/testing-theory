(* begin hide *)
From Stdlib Require Import Lia.
From stdpp Require Import sets gmap gmultiset countable numbers list sorting.
From TestingTheory Require Import VCCS.Testing.ta_tc_gen DefinitionAS Equivalence Must
  ParallelLTSConstruction InteractionBetweenLts Bisimulation
  ActTau InputOutputActions Convergence Termination InListPropHelper
  gLts Lts_OBA FiniteImageLTS Testing_Predicate Completeness Lts_FW Lts_OBA_FB MultisetLTSConstruction
  SetLTSConstruction ForwarderConstruction.
From TestingTheory Require Import coFiniteImage coConvergence coWeakTransition DefinitionASrel
  CompletenessASco EquivalenceASco TestSpecBridge SyncActions
  VCCS.Language.LTS VCCS.Language.gLts_Instance VCCS.Language.Label_Abstraction
  Label_Abstraction.LabelAbstraction Label_Abstraction.Decidable_dichotomic Subset_Act
  Decision.Tools_in_construction.Inductive.Generic.Helpers Decision.Tools_in_construction.Inductive.Generic.Acceptance_Tests_Gamma
  Decision.Tools_in_construction.Inductive.VCCS.Tests VCCS.Helper.Value_Swap VCCS.Characterisations.Must_Characterisation
  Decision.Tools_in_construction.Inductive.Generic.Bisim Decision.Tools_in_construction.Inductive.Generic.Interface Decision.Tools_in_construction.Inductive.Generic.Sets Decision.Tools_in_construction.Inductive.Generic.Graph Decision.Tools_in_construction.Inductive.Generic.Swaps Decision.Tools_in_construction.Inductive.Generic.Adequacy Decision.Tools_in_construction.Inductive.Generic.Verdict.
Import ListNotations.

Section VCCS_Trace_Search.

Context `{VP : VCCS_Parameters}.

#[local] Instance SyncAction_VCCS : SyncAction (ExtAct TypeOfActions) (ExtAct TypeOfActions) :=
  SyncAction_of_dual.

Notation A := (ExtAct TypeOfActions).

Notation Γᴠᴄᴄꜱ := (λ μ : A, αᴘᴠᴄᴄꜱ (αᴛᴠᴄᴄꜱ μ)).

Definition VarC_sub1 (c : ChannelData) : option ChannelData :=
  match c with
  | cst c => Some (cst c)
  | bvar 0 => None
  | bvar (S i) => Some (bvar i)
  end.

Fixpoint input_channels_of_g (gp : gproc) : list ChannelData :=
  match gp with
  | c ? • _ => [c]
  | g1 + g2 => input_channels_of_g g1 ++ input_channels_of_g g2
  | _ => []
  end.

Fixpoint input_channels_of (p : proc) : list ChannelData :=
  match p with
  | p1 ‖ p2 => input_channels_of p1 ++ input_channels_of p2
  | If C Then P1 Else P2 => match (Eval_Eq 0 C) with
                            | Some true => input_channels_of P1
                            | Some false => input_channels_of P2
                            | None => []
                            end
  | ν p => omap VarC_sub1 (input_channels_of p)
  | g gp => input_channels_of_g gp
  | _ => []
  end.

Lemma input_channels_of_spec p c v q : lts p (ActExt (ActIn (c, v))) q → c ∈ input_channels_of p.
Proof.
  intro l. remember (ActExt (ActIn (c, v))) as α eqn:hα. revert c v hα.
  induction l; intros c' v' hα; try discriminate; simpl.
  - injection hα as -> ->. apply list_elem_of_singleton. reflexivity.
  - rewrite H. eauto.
  - rewrite H. eauto.
  - injection hα as ->. apply list_elem_of_omap. exists (VarC_add 1 c'). split.
    + apply (IHl (VarC_add 1 c') v'). reflexivity.
    + destruct c'; reflexivity.
  - apply elem_of_app. left. eauto.
  - apply elem_of_app. right. eauto.
  - apply elem_of_app. left. eauto.
  - apply elem_of_app. right. eauto.
Qed.

Definition co_actions_of (vals : list ValueData) (p : proc) : list A :=
  map ActIn (elements (outputs_of p)) ++
  flat_map (λ c, map (λ v, ActOut (c, v)) vals) (input_channels_of p).

Lemma co_actions_of_spec vals p μ μ' q :
  dual μ' μ → p ⟶[μ'] q → (∀ a, a ∈ (match μ with ActIn _ => [] | ActOut (_, v) => [v] end) → a ∈ vals) →
  μ ∈ co_actions_of vals p.
Proof.
  intros duo l hv. destruct μ as [a | [c v]].
  - apply elem_of_app. left. apply elem_of_map_list. exists a. split; [reflexivity |].
    apply elem_of_elements. eapply outputs_of_spec1.
    exact (proj1 (vccs_dual_image_in_iff p a q) (ex_intro _ μ' (conj duo l))).
  - pose proof (proj1 (vccs_dual_image_out_iff p (c, v) q) (ex_intro _ μ' (conj duo l))) as l'.
    apply elem_of_app. right. apply elem_of_flat_map_list. exists c. split.
    + exact (input_channels_of_spec p c v q l').
    + apply elem_of_map_list. exists v. split; [reflexivity | apply hv; left].
Qed.


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
  | pr_var _ => false
  | rec y • p' => act_var y p' || act_div p'
  | If C Then P1 Else P2 => match (Eval_Eq 0 C) with
                            | Some true => act_div P1
                            | Some false => act_div P2
                            | None => false
                            end
  | ν p' => act_div p'
  | g gp => act_div_g gp
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
  apply proc_ind'; simpl; intros.
  - destruct (H k) as [h1 h2], (H0 k) as [h3 h4]. split; [intros x; by rewrite h1, h3 | by rewrite h2, h4].
  - split; reflexivity.
  - destruct (H k) as [h1 h2]. split; [intros x; by rewrite h1 | by rewrite h1, h2].
  - destruct (H k) as [h1 h2], (H0 k) as [h3 h4].
    split; [intros x; by rewrite h1, h3 | by rewrite h2, h4].
  - exact (H (S k)).
  - exact (H k).
  - split; reflexivity.
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
  apply proc_ind'; simpl; intros.
  - apply orb_true_iff in H1 as [h | h]; apply orb_true_iff; [left | right]; eauto.
  - apply bool_decide_eq_true in H as ->. rewrite decide_False by congruence. simpl.
    by apply bool_decide_eq_true.
  - destruct (decide (x = n)); [discriminate |].
    destruct (decide (y = n)); simpl; rewrite decide_False by congruence; eauto.
  - destruct (Eval_Eq 0 e) as [[] |]; eauto.
  - eauto.
  - eauto.
  - discriminate.
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
  apply proc_ind'; simpl; intros.
  - apply orb_true_iff in H1 as [h | h]; apply orb_true_iff; [left | right]; eauto.
  - discriminate.
  - destruct (decide (y = n)); simpl; [exact H0 |].
    apply orb_true_iff in H0 as [h | h]; apply orb_true_iff; [left | right].
    + apply (proj1 (act_var_subst n y (not_eq_sym n0))). exact h.
    + eauto.
  - destruct (Eval_Eq 0 e) as [[] |]; eauto.
  - eauto.
  - eauto.
  - discriminate.
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
  apply proc_ind'; simpl; intros.
  - apply orb_true_iff in H1 as [h | h]; apply orb_true_iff; [left | right]; eauto.
  - apply bool_decide_eq_true in H as ->. rewrite decide_True by reflexivity. exact H0.
  - destruct (decide (x = n)); [discriminate |]. simpl.
    apply orb_true_iff. right. eauto.
  - destruct (Eval_Eq 0 e) as [[] |]; eauto.
  - apply H; [exact H0 |]. rewrite (proj2 ((proj1 act_NewVarC) R 0)). exact H1.
  - eauto.
  - discriminate.
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
  apply proc_ind'; simpl; intros.
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
  - destruct (H H0) as (p' & l & h'). exists (ν p'). split; [apply lts_res_tau, l | exact h'].
  - exact (H H0).
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - exists p. split; [apply lts_tau | exact H0].
  - apply orb_true_iff in H1 as [h | h].
    + destruct (H h) as (p' & l & h'). exists p'. split; [apply lts_choiceL, l | exact h'].
    + destruct (H0 h) as (p' & l & h'). exists p'. split; [apply lts_choiceR, l | exact h'].
Qed.

Lemma act_div_diverges (p : proc) : act_div p = true → ¬ p ⤓.
Proof.
  intros h t. revert h. induction t as [p _ IH]. intros h.
  destruct ((proj1 act_div_step) p h) as (p' & l & h'). exact (IH p' l h').
Qed.


Fixpoint max_bvar (ds : list ValueData) : nat :=
  match ds with
  | [] => 0
  | cst _ :: ds => max_bvar ds
  | bvar j :: ds => j `max` max_bvar ds
  end.

Lemma max_bvar_spec (ds : list ValueData) j : bvar j ∈ ds → j ≤ max_bvar ds.
Proof.
  induction ds as [| [v | i] ds IH]; simpl; intros m.
  - inversion m.
  - apply elem_of_cons in m as [m | m]; [discriminate | exact (IH m)].
  - apply elem_of_cons in m as [m | m]; [injection m as ->; lia | specialize (IH m); lia].
Qed.

Lemma dual_swap a b μ' μ : dual μ' μ → dual (swap_ext a b μ') (swap_ext a b μ).
Proof.
  destruct μ' as [[c v] | [c v]], μ as [[c' v'] | [c' v']]; simpl; intros h; try contradiction;
    inversion h; subst; reflexivity.
Qed.


Definition atoms_act (μ : A) : list ValueData :=
  match μ with
  | ActIn (_, v) => [v]
  | ActOut (_, v) => [v]
  end.

Definition next_of (vals : list ValueData) (p : proc) : list A := co_actions_of vals p.

Lemma next_of_spec vals p μ μ' q :
  dual μ' μ → p ⟶[μ'] q → (∀ a, a ∈ atoms_act μ → a ∈ vals) → μ ∈ next_of vals p.
Proof.
  intros duo l hv. apply (co_actions_of_spec vals p μ μ' q duo l).
  destruct μ as [[c v] | [c v]]; simpl; [intros a m; inversion m | exact hv].
Qed.

Definition pool (avoid : list ValueData) (N : nat) : list ValueData :=
  (λ i, bvar (S (max_bvar avoid) + i)) <$> seq 0 N.

Lemma pool_avoid avoid N f : f ∈ pool avoid N → f ∉ avoid.
Proof.
  intros (i & -> & _)%list_elem_of_fmap m. apply max_bvar_spec in m. lia.
Qed.

Lemma pool_NoDup avoid N : NoDup (pool avoid N).
Proof. apply NoDup_fmap_2; [intros i j h; injection h; lia | apply NoDup_seq]. Qed.

Lemma swap_data_self a b : swap_data 0 a b a = b.
Proof. unfold swap_data. rewrite decide_True; [destruct b; reflexivity | destruct a; reflexivity]. Qed.

Lemma pool_spec avoid N a M :
  length M ≤ N → a ∈ M → a ∉ pool avoid N → ∃ f, f ∈ pool avoid N ∧ f ∉ M ∧ swap_data 0 a f a = f.
Proof.
  intros hM ha hap. destruct (decide (Forall (λ f, f ∈ M) (pool avoid N))) as [h | h].
  - exfalso. assert (a :: pool avoid N ⊆+ M) as sub.
    { apply NoDup_submseteq; [constructor; [exact hap | apply pool_NoDup] |].
      intros x [-> | m]%elem_of_cons; [exact ha | rewrite Forall_forall in h; exact (h x m)]. }
    apply submseteq_length in sub. simpl in sub. unfold pool in sub.
    rewrite length_fmap, length_seq in sub. lia.
  - apply not_Forall_Exists, Exists_exists in h as (f & m & hf); [| intros x; apply _].
    exists f. split_and!; [exact m | exact hf | apply swap_data_self].
Qed.

Lemma swap_atom_other a b c : c ≠ a → c ≠ b → swap_data 0 a b c = c.
Proof.
  intros ha hb. unfold swap_data. destruct a as [va | ja], b as [vb | jb]; simpl;
    rewrite !decide_False by assumption; reflexivity.
Qed.

Lemma vccs_tc_spec (p : proc) (s : trace A) : p must_pass gen_conv s ↔ p ⇓ᶜᵒ s.
Proof. apply must_iff_cocnv. Qed.

Lemma vccs_step_swap a b (p : proc) μ q : p ⟶[μ] q → swap_proc a b p ⟶[swap_ext a b μ] swap_proc a b q.
Proof. exact (lts_swap a b p (ActExt μ) q). Qed.

Lemma vccs_tau_swap a b (p q : proc) : p ⟶ q → swap_proc a b p ⟶ swap_proc a b q.
Proof. exact (lts_swap a b p τ q). Qed.

Lemma vccs_Γ_swap a b μ : Γᴠᴄᴄꜱ (swap_ext a b μ) = Γᴠᴄᴄꜱ μ.
Proof. destruct μ as [[c v] | [c v]]; reflexivity. Qed.

Lemma vccs_atoms_act_swap a b μ : atoms_act (swap_ext a b μ) = map (swap_data 0 a b) (atoms_act μ).
Proof. destruct μ as [[c v] | [c v]]; reflexivity. Qed.

Lemma vccs_arity_spec (p : proc) (μ μ' : A) q : dual μ' μ → p ⟶[μ'] q → length (atoms_act μ) ≤ 1.
Proof. intros _ _. destruct μ as [[c v] | [c v]]; simpl; lia. Qed.

Definition is_nil (P : proc) : bool :=
  match P with
  | g 𝟘 => true
  | _ => false
  end.

Lemma is_nil_spec P : is_nil P = true → P = g 𝟘.
Proof. destruct P as [| | | | | G]; try discriminate. destruct G; try discriminate. reflexivity. Qed.

Definition leaf (p : proc) : list proc := if is_nil p then [] else [p].

Fixpoint par_comps (p : proc) : list proc :=
  match p with
  | P ‖ Q => par_comps P ++ par_comps Q
  | _ => leaf p
  end.

Fixpoint par_build (l : list proc) : proc :=
  match l with
  | [] => g 𝟘
  | [a] => a
  | a :: l => a ‖ par_build l
  end.

Definition proc_le (a b : proc) : Prop := Pos.leb (encode a) (encode b) = true.

#[local] Instance proc_le_dec : RelDecision proc_le :=
  λ a b, decide (Pos.leb (encode a) (encode b) = true).

Definition sort_procs (l : list proc) : list proc := merge_sort proc_le l.

Lemma leaf_cgr p : par_build (leaf p) ≡* p.
Proof. unfold leaf. destruct (is_nil p) eqn:e; [apply is_nil_spec in e as ->; reflexivity | reflexivity]. Qed.

Lemma par_build_cons a l : par_build (a :: l) ≡* a ‖ par_build l.
Proof. destruct l; [apply cgr_par_nil_rev | reflexivity]. Qed.

Lemma par_build_app l1 l2 : par_build (l1 ++ l2) ≡* par_build l1 ‖ par_build l2.
Proof.
  induction l1 as [| a l1 IH].
  - transitivity (par_build l2 ‖ g 𝟘); [apply cgr_par_nil_rev | apply cgr_par_com].
  - etransitivity; [apply par_build_cons |].
    etransitivity; [apply cgr_fullpar; [reflexivity | exact IH] |].
    etransitivity; [apply cgr_par_assoc_rev |]. apply cgr_par. symmetry. apply par_build_cons.
Qed.

Lemma par_build_perm l1 l2 : l1 ≡ₚ l2 → par_build l1 ≡* par_build l2.
Proof.
  induction 1 as [| x l l' _ IH | x y l | l l' l'' _ IH1 _ IH2].
  - reflexivity.
  - etransitivity; [apply par_build_cons |].
    etransitivity; [apply cgr_fullpar; [reflexivity | exact IH] |]. symmetry. apply par_build_cons.
  - etransitivity; [apply par_build_cons |].
    etransitivity; [apply cgr_fullpar; [reflexivity | apply par_build_cons] |].
    etransitivity; [apply cgr_par_assoc_rev |].
    etransitivity; [apply cgr_par, cgr_par_com |].
    etransitivity; [apply cgr_par_assoc |]. symmetry.
    etransitivity; [apply par_build_cons |]. apply cgr_fullpar; [reflexivity | apply par_build_cons].
  - etransitivity; [exact IH1 | exact IH2].
Qed.

Lemma par_comps_cgr p : par_build (par_comps p) ≡* p.
Proof.
  induction p; cbn [par_comps]; try apply leaf_cgr.
  etransitivity; [apply par_build_app | apply cgr_fullpar; assumption].
Qed.

Definition mk_res (P : proc) : proc := if is_nil P then g 𝟘 else ν P.

Fixpoint vccs_nf (p : proc) : proc :=
  match p with
  | P ‖ Q => par_build (sort_procs (par_comps (vccs_nf P) ++ par_comps (vccs_nf Q)))
  | ν P => mk_res (vccs_nf P)
  | _ => p
  end.

Lemma mk_res_cgr P : mk_res P ≡* ν P.
Proof.
  unfold mk_res. destruct (is_nil P) eqn:e; [apply is_nil_spec in e as ->; apply cgr_res_nil_rev | reflexivity].
Qed.

Lemma vccs_nf_cgr p : vccs_nf p ≡* p.
Proof.
  induction p; simpl; try reflexivity.
  - etransitivity; [apply par_build_perm, merge_sort_Permutation |].
    etransitivity; [apply par_build_app |].
    etransitivity; [apply cgr_fullpar; apply par_comps_cgr |]. apply cgr_fullpar; assumption.
  - etransitivity; [apply mk_res_cgr | apply cgr_res; assumption].
Qed.


Lemma vccs_nf_spec p : sbisim (vccs_nf p) p.
Proof. exact (eq_sbisim (gLtsEqP := VCCS_gLtsEq) _ _ (vccs_nf_cgr p)). Qed.

Definition vccs_co_next (p : proc) (μ : A) : list proc :=
  match vccs_co μ with
  | ActIn a => lts_list_input p a
  | ActOut a => lts_list_output p a
  end.

Lemma vccs_tau_next_spec (p q : proc) : q ∈ lts_list_tau p ↔ lts p τ q.
Proof. etransitivity; [| exact (lts_set_spec p τ q)]. unfold lts_set. rewrite elem_of_list_to_set. reflexivity. Qed.

Lemma vccs_co_next_spec (p : proc) (μ : A) (q : proc) : q ∈ vccs_co_next p μ ↔ ∃ μ', dual μ' μ ∧ lts p (ActExt μ') q.
Proof.
  etransitivity; [| exact (vccs_co_image_spec p μ q)].
  unfold lts_set, vccs_co_next. destruct μ; simpl; rewrite elem_of_list_to_set; reflexivity.
Qed.

#[global] Instance VCCS_TraceSearch : TraceSearchLang proc A ValueData PreAct proc :=
  {| ts_Γ := Γᴠᴄᴄꜱ;
     ts_dichotomy := dichotomy_of_finite Γᴠᴄᴄꜱ PreCoAct_of PreCoAct_of_spec;
     ts_must p t := p must_pass t;
     ts_tc := gen_conv;
     ts_ta X s := gen_acc X s;
     ts_tc_spec := vccs_tc_spec;
     ts_ta_spec p q q' s X hp w st hXC hXS := gen_acc_distinguishes p q q' s hp X w st hXC hXS;
     ts_swap := swap_proc;
     ts_swap_act := swap_ext;
     ts_swap_atom a b := swap_data 0 a b;
     ts_swap_pre _ _ x := x;
     ts_swap_invol := swap_proc_invol;
     ts_swap_act_invol := swap_ext_invol;
     ts_swap_pre_invol _ _ _ := eq_refl;
     ts_swap_atom_other := swap_atom_other;
     ts_step_swap := vccs_step_swap;
     ts_tau_swap := vccs_tau_swap;
     ts_sync_swap := dual_swap;
     ts_nb_swap _ _ _ h := h;
     ts_Γ_swap := vccs_Γ_swap;
     ts_atoms := atoms_of;
     ts_atoms_act := atoms_act;
     ts_atoms_act_swap := vccs_atoms_act_swap;
     ts_swap_fix := swap_proc_fix;
     ts_next := next_of;
     ts_next_spec := next_of_spec;
     ts_arity _ := 1;
     ts_arity_spec := vccs_arity_spec;
     ts_pool := pool;
     ts_pool_avoid := pool_avoid;
     ts_pool_spec := pool_spec;
     ts_tau_next := lts_list_tau;
     ts_tau_next_spec := vccs_tau_next_spec;
     ts_co_next := vccs_co_next;
     ts_co_next_spec := vccs_co_next_spec;
     ts_div := act_div;
     ts_div_spec := act_div_diverges;
     ts_norm := vccs_nf;
     ts_norm_spec := vccs_nf_spec;
     ts_hash := size |}.

#[local] Existing Instance LA_class_proj.

Lemma ρ_incl_of_Γ_incl (S S' : subset_of A) :
  ⌈ Γᴠᴄᴄꜱ ⌉ S ⊆ ⌈ Γᴠᴄᴄꜱ ⌉ S' → ⌈ ρ[𝔸ᴠᴄᴄꜱ] ⌉ S ⊆ ⌈ ρ[𝔸ᴠᴄᴄꜱ] ⌉ S'.
Proof.
  intros h x (μ & hμ & ->).
  destruct (h (Γᴠᴄᴄꜱ μ)) as (μ' & hμ' & e); [by exists μ |].
  exists μ'. split; [exact hμ' |].
  apply (LA_proj_spec (R := label_ker 𝔸ᴠᴄᴄꜱ) (f := ρ[𝔸ᴠᴄᴄꜱ])).
  apply (LA_proj_spec (R := label_ker 𝔸ᴠᴄᴄꜱ) (f := Γᴠᴄᴄꜱ)). exact e.
Qed.

Definition vccs_verdict (m k n : nat) (p q : proc) : result := verdict m k n p q.

Theorem vccs_verdict_holds (m k n : nat) (p q : proc) : vccs_verdict m k n p q = R_holds → p ⊑ₘᵤₛₜᵢ q.
Proof.
  intros h. pose proof (verdict_holds m k n p q h) as hc.
  apply must_iff_co_acceptance_set_VCCS_without_toFW. split.
  - intros s hp. exact (proj1 (hc s) hp).
  - intros s q' hp w st. destruct (proj2 (hc s) q' hp w st) as (p' & w' & st' & sub).
    exists p'. split_and!; [exact w' | exact st' | exact (ρ_incl_of_Γ_incl _ _ sub)].
Qed.

Theorem vccs_verdict_refutes (m k n : nat) (p q : proc) s t : vccs_verdict m k n p q = R_fails s t → p ⋢ₘᵤₛₜᵢ q.
Proof.
  intros h. destruct (verdict_fails m k n p q s t h) as [h1 h2].
  exact (distinguishing_test_refutes p q t h1 h2).
Qed.

End VCCS_Trace_Search.
(* end hide *)
