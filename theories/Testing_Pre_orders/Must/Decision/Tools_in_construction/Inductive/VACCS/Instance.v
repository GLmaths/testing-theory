(* begin hide *)
From Stdlib Require Import Lia.
From stdpp Require Import sets gmap gmultiset countable numbers list sorting finite.
From TestingTheory Require Import Termination VACCS.Testing.ta_tc_gen DefinitionAS Equivalence Must Lift
  ParallelLTSConstruction InteractionBetweenLts Bisimulation
  ActTau InputOutputActions Convergence InListPropHelper
  gLts Lts_OBA FiniteImageLTS Testing_Predicate Completeness Lts_FW Lts_OBA_FB MultisetLTSConstruction
  SetLTSConstruction ForwarderConstruction.
From TestingTheory Require Import coFiniteImage coConvergence coWeakTransition DefinitionASrel
  CompletenessASco EquivalenceASco TestSpecBridge SyncActions
  VACCS.Language.LTS VACCS.Language.gLts_Instance VACCS.Language.Label_Abstraction
  VACCS.Characterisations.Must_Characterisation VACCS.Helper.Atom_Swap VACCS.Helper.Divergence
  Label_Abstraction.LabelAbstraction Label_Abstraction.Decidable_dichotomic Subset_Act
  Decision.Tools_in_construction.Inductive.Generic.Helpers Decision.Tools_in_construction.Inductive.Generic.Acceptance_Tests_Gamma
  Decision.Tools_in_construction.Inductive.VACCS.Tests Decision.Tools_in_construction.Inductive.Generic.Bisim Decision.Tools_in_construction.Inductive.Generic.Interface Decision.Tools_in_construction.Inductive.Generic.Sets Decision.Tools_in_construction.Inductive.Generic.Graph Decision.Tools_in_construction.Inductive.Generic.Swaps Decision.Tools_in_construction.Inductive.Generic.Adequacy Decision.Tools_in_construction.Inductive.Generic.Verdict Decision.Tools_in_construction.Inductive.Generic.Forwarders.
Import ListNotations.

Section VACCS_Trace_Search.

Context `{VP : VACCS_Parameters}.

#[local] Instance SyncAction_VACCS : SyncAction (ExtAct TypeOfActions) (ExtAct TypeOfActions) :=
  SyncAction_of_dual.

Notation A := (ExtAct TypeOfActions).
Notation FW := (proc * MO A)%type.

Lemma dual_swap a b μ' μ : dual μ' μ → dual (swap_ext a b μ') (swap_ext a b μ).
Proof.
  destruct μ' as [[c v] | [c v]], μ as [[c' v'] | [c' v']]; simpl; intros h; try contradiction;
    inversion h; subst; reflexivity.
Qed.

Lemma nb_swap a b μ : non_blocking μ → non_blocking (swap_ext a b μ).
Proof. intros (x & ->). destruct x as [c v]. eexists. reflexivity. Qed.

Lemma nb_swap_back a b μ : non_blocking (swap_ext a b μ) → non_blocking μ.
Proof. destruct μ as [[c v] | [c v]]; simpl; intros (x & e); [discriminate | eexists; reflexivity]. Qed.

Lemma proc_step_swap a b (p : proc) α q :
  p ⟶{α} q → swap_proc a b p ⟶{map_label (swap_ext a b) α} swap_proc a b q.
Proof. intros l. pose proof (lts_swap_at a b p α q l 0) as l'. destruct α; exact l'. Qed.

Definition swap_fw (a b : Atom) (pm : FW) : FW := fw_map (swap_ext a b) (swap_proc a b) pm.

Lemma swap_fw_invol a b pm : swap_fw a b (swap_fw a b pm) = pm.
Proof. exact (fw_map_invol (swap_ext a b) (swap_proc a b) (swap_ext_invol a b) (swap_proc_invol a b) pm). Qed.

Lemma swap_fw_step a b (pm : FW) α qm : pm ⟶{α} qm → swap_fw a b pm ⟶{map_label (swap_ext a b) α} swap_fw a b qm.
Proof. exact (fw_step_map (swap_ext a b) (swap_proc a b) (dual_swap a b) (nb_swap a b) (proc_step_swap a b) pm α qm). Qed.

Lemma swap_fw_ext a b (pm : FW) μ qm : pm ⟶[μ] qm → swap_fw a b pm ⟶[swap_ext a b μ] swap_fw a b qm.
Proof. exact (swap_fw_step a b pm (ActExt μ) qm). Qed.

Lemma swap_fw_tau a b (pm qm : FW) : pm ⟶ qm → swap_fw a b pm ⟶ swap_fw a b qm.
Proof. exact (swap_fw_step a b pm τ qm). Qed.

Definition swap_atom (a b x : Atom) : Atom :=
  match x with
  | inl c => inl (swap_cd 0 a b c)
  | inr v => inr (swap_vd 0 a b v)
  end.

Lemma swap_atom_other a b x : x ≠ a → x ≠ b → swap_atom a b x = x.
Proof.
  intros ha hb. destruct x as [c | v]; simpl; f_equal.
  - destruct a as [a | a], b as [b | b]; simpl; try reflexivity. unfold swap_D.
    destruct a, b; simpl; rewrite !decide_False by congruence; reflexivity.
  - destruct a as [a | a], b as [b | b]; simpl; try reflexivity. unfold swap_D.
    destruct a, b; simpl; rewrite !decide_False by congruence; reflexivity.
Qed.

Definition swap_pre (a b : Atom) (x : ChannelData + ChannelData) : ChannelData + ChannelData :=
  match x with
  | inl c => inl (swap_cd 0 a b c)
  | inr c => inr (swap_cd 0 a b c)
  end.

Lemma swap_pre_invol a b x : swap_pre a b (swap_pre a b x) = x.
Proof. destruct x; simpl; by rewrite swap_cd_invol. Qed.

Lemma Γ_swap a b μ : Γᴠᴀᴄᴄꜱ (swap_ext a b μ) = swap_pre a b (Γᴠᴀᴄᴄꜱ μ).
Proof. destruct μ as [[c v] | [c v]]; reflexivity. Qed.

Definition atoms_act (μ : A) : list Atom :=
  match μ with
  | ActIn (c, v) => [inl c; inr v]
  | ActOut (c, v) => [inl c; inr v]
  end.

Lemma atoms_act_swap a b μ : atoms_act (swap_ext a b μ) = map (swap_atom a b) (atoms_act μ).
Proof. destruct μ as [[c v] | [c v]]; reflexivity. Qed.

Definition atoms_fw (pm : FW) : list Atom := atoms_of pm.1 ++ flat_map atoms_act (elements pm.2).

Lemma atoms_of_D_zero {T} `{Countable T} (inj : Data T → Atom) D : atoms_of_D inj 0 D = [inj D].
Proof. unfold atoms_of_D. destruct D; [reflexivity | rewrite decide_True by lia; by rewrite Nat.sub_0_r]. Qed.

Lemma swap_ext_fix a b μ : a ∉ atoms_act μ → b ∉ atoms_act μ → swap_ext a b μ = μ.
Proof.
  destruct μ as [[c v] | [c v]]; simpl; intros ha hb; unfold swap_ext; simpl;
    (rewrite swap_cd_fix, swap_vd_fix; [reflexivity | ..]); rewrite atoms_of_D_zero; set_solver.
Qed.

Lemma swap_fw_fix a b pm : a ∉ atoms_fw pm → b ∉ atoms_fw pm → swap_fw a b pm = pm.
Proof.
  destruct pm as [p m]. unfold atoms_fw, swap_fw, fw_map. simpl. intros ha hb.
  rewrite swap_proc_fix by set_solver. f_equal.
  assert (hm : ∀ μ, μ ∈ m → swap_ext a b μ = μ).
  { intros μ hμ. apply swap_ext_fix; intros h; [apply ha | apply hb]; apply elem_of_app; right;
      apply elem_of_flat_map_list; exists μ; (split; [| exact h]); by apply gmultiset_elem_of_elements. }
  exact (gmultiset_map_fix (swap_ext a b) (swap_ext_invol a b) m hm).
Qed.

Definition chan_atoms (vals : list Atom) : list ChannelData :=
  omap (λ x, match x with inl c => Some c | inr _ => None end) vals.

Definition val_atoms (vals : list Atom) : list ValueData :=
  omap (λ x, match x with inr v => Some v | inl _ => None end) vals.

Definition next_fw (vals : list Atom) (pm : FW) : list A :=
  map ActIn (elements (outputs_of pm.1)) ++ map vaccs_co (elements pm.2) ++
  flat_map (λ c, map (λ v, ActOut (c, v)) (val_atoms vals)) (chan_atoms vals).

Lemma next_fw_spec vals (pm : FW) μ μ' qm :
  sync μ' μ → pm ⟶[μ'] qm → (∀ a, a ∈ atoms_act μ → a ∈ vals) → μ ∈ next_fw vals pm.
Proof.
  intros duo l hv. unfold next_fw. rewrite !elem_of_app.
  assert (hall : ∀ c v, μ = ActOut (c, v) → μ ∈ flat_map (λ c, map (λ v, ActOut (c, v)) (val_atoms vals)) (chan_atoms vals)).
  { intros c v ->. apply elem_of_flat_map_list. exists c. split.
    - apply list_elem_of_omap. exists (inl c). split; [apply hv; left | reflexivity].
    - apply elem_of_map_list. exists v. split; [reflexivity |].
      apply list_elem_of_omap. exists (inr v). split; [apply hv; right; left | reflexivity]. }
  destruct pm as [p m].
  inversion l as [α' a1 a2 b l1 | α' a b1 b2 l1 | μ1 μ2 a1 a2 b1 b2 eq l1 l2]; subst.
  - destruct μ' as [a' | a'], μ as [x | [c v]]; simpl in duo; try contradiction.
    + right; right. by apply (hall c v).
    + subst. left. apply elem_of_map_list. exists x. split; [reflexivity |].
      apply elem_of_elements. exact (outputs_of_spec1 p x a2 l1).
  - inversion l1 as [m0 η μ0 duo' nb | m0 η nb]; subst.
    + destruct nb as ([c v] & ->). destruct μ' as [x | x]; simpl in duo'; [| contradiction].
      destruct μ as [y | y]; simpl in duo; [contradiction |]. subst. right; right. apply (hall c v). reflexivity.
    + right; left. apply elem_of_map_list. exists μ'.
      split; [destruct μ' as [x | x], μ as [y | y]; simpl in duo; try contradiction; by subst |].
      apply gmultiset_elem_of_elements. simpl. multiset_solver.
Qed.

Definition chan_idx (x : Atom) : option nat := match x with inl (bvar j) => Some j | _ => None end.
Definition val_idx (x : Atom) : option nat := match x with inr (bvar j) => Some j | _ => None end.

Definition base_chan (avoid : list Atom) : nat := S (foldr max 0 (omap chan_idx avoid)).
Definition base_val (avoid : list Atom) : nat := S (foldr max 0 (omap val_idx avoid)).

Definition pool_chan (avoid : list Atom) (N : nat) : list Atom :=
  (λ i, inl (bvar (Nat.add (base_chan avoid) i))) <$> seq 0 N.

Definition pool_val (avoid : list Atom) (N : nat) : list Atom :=
  (λ i, inr (bvar (Nat.add (base_val avoid) i))) <$> seq 0 N.

Definition pool (avoid : list Atom) (N : nat) : list Atom := pool_chan avoid N ++ pool_val avoid N.

Lemma foldr_max_spec (l : list nat) j : j ∈ l → j ≤ foldr max 0 l.
Proof. induction l as [| x l IH]; simpl; intros m; [inversion m |]. apply elem_of_cons in m as [-> | m]; [lia | specialize (IH m); lia]. Qed.

Lemma pool_avoid avoid N f : f ∈ pool avoid N → f ∉ avoid.
Proof.
  intros m hm. apply elem_of_app in m as [m | m]; apply list_elem_of_fmap in m as (i & -> & _).
  - assert (h : Nat.add (base_chan avoid) i ∈ omap chan_idx avoid)
      by (apply list_elem_of_omap; exists (inl (bvar (Nat.add (base_chan avoid) i))); split; [exact hm | reflexivity]).
    apply foldr_max_spec in h. unfold base_chan in h. lia.
  - assert (h : Nat.add (base_val avoid) i ∈ omap val_idx avoid)
      by (apply list_elem_of_omap; exists (inr (bvar (Nat.add (base_val avoid) i))); split; [exact hm | reflexivity]).
    apply foldr_max_spec in h. unfold base_val in h. lia.
Qed.

Lemma pigeon (P0 : list Atom) N a M :
  NoDup P0 → length P0 = N → length M ≤ N → a ∈ M → a ∉ P0 → ∃ f, f ∈ P0 ∧ f ∉ M.
Proof.
  intros hnd hl hM ha hap. destruct (decide (Forall (λ f, f ∈ M) P0)) as [h | h].
  - exfalso. assert (a :: P0 ⊆+ M) as sub.
    { apply NoDup_submseteq; [constructor; [exact hap | exact hnd] |].
      intros x [-> | m]%elem_of_cons; [exact ha | rewrite Forall_forall in h; exact (h x m)]. }
    apply submseteq_length in sub. simpl in sub. lia.
  - apply not_Forall_Exists, Exists_exists in h as (f & m & hf); [| intros x; apply _].
    exists f. split; assumption.
Qed.

Lemma swap_D_self {T} `{Countable T} (a b : Data T) : swap_D 0 a b a = b.
Proof. unfold swap_D. rewrite decide_True; [destruct b; reflexivity | destruct a; reflexivity]. Qed.

Lemma pool_spec avoid N a M :
  length M ≤ N → a ∈ M → a ∉ pool avoid N → ∃ f, f ∈ pool avoid N ∧ f ∉ M ∧ swap_atom a f a = f.
Proof.
  intros hM ha hap. destruct a as [c | v].
  - destruct (pigeon (pool_chan avoid N) N (inl c) M) as (f & hf & hfM).
    + apply NoDup_fmap_2; [intros i j h; injection h; lia | apply NoDup_seq].
    + unfold pool_chan. by rewrite length_fmap, length_seq.
    + exact hM.
    + exact ha.
    + intros m. apply hap, elem_of_app. left. exact m.
    + exists f. split_and!; [apply elem_of_app; left; exact hf | exact hfM |].
      apply list_elem_of_fmap in hf as (i & -> & _). simpl. by rewrite swap_D_self.
  - destruct (pigeon (pool_val avoid N) N (inr v) M) as (f & hf & hfM).
    + apply NoDup_fmap_2; [intros i j h; injection h; lia | apply NoDup_seq].
    + unfold pool_val. by rewrite length_fmap, length_seq.
    + exact hM.
    + exact ha.
    + intros m. apply hap, elem_of_app. right. exact m.
    + exists f. split_and!; [apply elem_of_app; right; exact hf | exact hfM |].
      apply list_elem_of_fmap in hf as (i & -> & _). simpl. by rewrite swap_D_self.
Qed.

Lemma vaccs_tc_spec (pm : FW) (s : trace A) : pm must_pass gen_conv s ↔ pm ⇓ᶜᵒ s.
Proof. apply must_iff_cocnv. Qed.

Lemma vaccs_arity_spec (pm : FW) (μ μ' : A) qm : dual μ' μ → pm ⟶[μ'] qm → length (atoms_act μ) ≤ 2.
Proof. intros _ _. destruct μ as [[c v] | [c v]]; simpl; lia. Qed.

Definition is_nil (P : proc) : bool :=
  match P with
  | g 𝟘 => true
  | _ => false
  end.

Lemma is_nil_spec P : is_nil P = true → P = g 𝟘.
Proof. destruct P as [| | | | | | G]; try discriminate. destruct G; try discriminate. reflexivity. Qed.

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

Fixpoint vaccs_nf (p : proc) : proc :=
  match p with
  | P ‖ Q => par_build (sort_procs (par_comps (vaccs_nf P) ++ par_comps (vaccs_nf Q)))
  | ν P => mk_res (vaccs_nf P)
  | _ => p
  end.

Lemma mk_res_cgr P : mk_res P ≡* ν P.
Proof.
  unfold mk_res. destruct (is_nil P) eqn:e; [apply is_nil_spec in e as ->; apply cgr_res_nil_rev | reflexivity].
Qed.

Lemma vaccs_nf_cgr p : vaccs_nf p ≡* p.
Proof.
  induction p; simpl; try reflexivity.
  - etransitivity; [apply par_build_perm, merge_sort_Permutation |].
    etransitivity; [apply par_build_app |].
    etransitivity; [apply cgr_fullpar; apply par_comps_cgr |]. apply cgr_fullpar; assumption.
  - etransitivity; [apply mk_res_cgr | apply cgr_res; assumption].
Qed.


Lemma vaccs_nf_spec (pm : FW) : sbisim (vaccs_nf pm.1, pm.2) pm.
Proof.
  destruct pm as [p m]. apply fw_sbisim.
  exact (eq_sbisim (gLtsEqP := VACCS_gLtsEq) _ _ (vaccs_nf_cgr p)).
Qed.

Lemma fw_div (pm : FW) : act_div pm.1 = true → ¬ pm ⤓.
Proof.
  intros h t. revert h. induction t as [[p m] _ IH]. simpl. intros h.
  destruct ((proj1 act_div_step) p h) as (p' & l & h').
  exact (IH (p', m) (ParLeft τ p p' m l) h').
Qed.

Definition proc_co (p : proc) (μ : A) : list proc :=
  match co μ with
  | ActIn a => lts_list_input p a
  | ActOut a => lts_list_output p a
  end.

Lemma proc_co_spec (p : proc) (μ : A) (q : proc) : q ∈ proc_co p μ ↔ lts p (ActExt (co μ)) q.
Proof. rewrite <- lts_set_spec. unfold lts_set, proc_co. destruct (co μ) as [a | a]; rewrite elem_of_list_to_set; reflexivity. Qed.

Lemma proc_tau_spec (p q : proc) : q ∈ lts_list_tau p ↔ lts p τ q.
Proof. rewrite <- lts_set_spec. unfold lts_set. rewrite elem_of_list_to_set. reflexivity. Qed.

Definition fw_co_next (pm : FW) (μ : A) : list FW :=
  ((λ q, (q, pm.2)) <$> proc_co pm.1 μ) ++ ((λ m', (pm.1, proj1_sig m')) <$> @enum _ _ (fw_ms_dual_image_finite pm.2 μ)).

Lemma fw_co_next_spec (pm : FW) (μ : A) (qm : FW) : qm ∈ fw_co_next pm μ ↔ ∃ μ', dual μ' μ ∧ pm ⟶[μ'] qm.
Proof.
  destruct pm as [p m], qm as [q m']. etransitivity; [| symmetry; exact (fw_dual_image_ext_iff p q m m' μ)].
  unfold fw_co_next. simpl. rewrite elem_of_app, !list_elem_of_fmap. split.
  - intros [(q0 & e & h) | (d & e & _)].
    + injection e as -> ->. left. split; [reflexivity | apply proc_co_spec, h].
    + injection e as -> ->. right. split; [reflexivity | exact (bool_decide_unpack _ (proj2_sig d))].
  - intros [[-> h] | [-> h]].
    + left. exists q. split; [reflexivity | apply proc_co_spec, h].
    + right. exists (dexist m' h). split; [reflexivity | apply elem_of_enum].
Qed.

Definition fw_tau_next (pm : FW) : list FW :=
  ((λ q, (q, pm.2)) <$> lts_list_tau pm.1) ++
  flat_map (λ μ, (λ q, (q, pm.2 ∖ {[+ μ +]})) <$> proc_co pm.1 μ) (filter (λ μ, non_blocking μ) (elements pm.2)).

Lemma fw_tau_next_spec (pm qm : FW) : qm ∈ fw_tau_next pm ↔ pm ⟶ qm.
Proof.
  destruct pm as [p m], qm as [q m']. etransitivity; [| symmetry; exact (fw_tau_image_iff p q m m')].
  unfold fw_tau_next. simpl. rewrite elem_of_app, list_elem_of_fmap, elem_of_flat_map_list. split.
  - intros [(q0 & e & h) | (μ & mμ & h)].
    + injection e as -> ->. left. split; [reflexivity | apply proc_tau_spec, h].
    + apply list_elem_of_filter in mμ as [nb mμ]. apply list_elem_of_fmap in h as (q0 & e & h).
      injection e as -> ->. right. exists μ. split_and!; [exact nb | | apply proc_co_spec, h].
      apply gmultiset_elem_of_elements in mμ. multiset_solver.
  - intros [[-> h] | (η & nb & -> & h)].
    + left. exists q. split; [reflexivity | apply proc_tau_spec, h].
    + right. exists η. split.
      * apply list_elem_of_filter. split; [exact nb | apply gmultiset_elem_of_elements; multiset_solver].
      * apply list_elem_of_fmap. exists q. split; [| apply proc_co_spec, h]. f_equal. multiset_solver.
Qed.

#[global] Instance VACCS_TraceSearch : TraceSearchLang FW A Atom (ChannelData + ChannelData) proc :=
  {| ts_Γ := Γᴠᴀᴄᴄꜱ;
     ts_dichotomy := dichotomy_of_finite Γᴠᴀᴄᴄꜱ coR_Γ coR_Γ_spec;
     ts_must pm t := pm must_pass t;
     ts_tc := gen_conv;
     ts_ta := ta_Γ;
     ts_tc_spec := vaccs_tc_spec;
     ts_ta_spec p q q' s X hp w st hXC hXS := ta_distinguishes p q q' s hp X w st hXC hXS;
     ts_swap := swap_fw;
     ts_swap_act := swap_ext;
     ts_swap_atom := swap_atom;
     ts_swap_pre := swap_pre;
     ts_swap_invol := swap_fw_invol;
     ts_swap_act_invol := swap_ext_invol;
     ts_swap_pre_invol := swap_pre_invol;
     ts_swap_atom_other := swap_atom_other;
     ts_step_swap := swap_fw_ext;
     ts_tau_swap := swap_fw_tau;
     ts_sync_swap := dual_swap;
     ts_nb_swap := nb_swap_back;
     ts_Γ_swap := Γ_swap;
     ts_atoms := atoms_fw;
     ts_atoms_act := atoms_act;
     ts_atoms_act_swap := atoms_act_swap;
     ts_swap_fix := swap_fw_fix;
     ts_next := next_fw;
     ts_next_spec := next_fw_spec;
     ts_arity _ := 2;
     ts_arity_spec := vaccs_arity_spec;
     ts_pool := pool;
     ts_pool_avoid := pool_avoid;
     ts_pool_spec := pool_spec;
     ts_tau_next := fw_tau_next;
     ts_tau_next_spec pm qm := fw_tau_next_spec pm qm;
     ts_co_next := fw_co_next;
     ts_co_next_spec := fw_co_next_spec;
     ts_div pm := act_div pm.1;
     ts_div_spec := fw_div;
     ts_norm pm := (vaccs_nf pm.1, pm.2);
     ts_norm_spec := vaccs_nf_spec;
     ts_hash pm := Nat.add (size pm.1) (length (elements pm.2)) |}.

#[local] Existing Instance LA_class_proj.

#[local] Instance LA_proj_VACCS' : LA_proj (label_ker 𝔸ᴠᴀᴄᴄꜱ) Γᴠᴀᴄᴄꜱ.
Proof.
  intros μ μ'. transitivity (ρ[𝔸ᴠᴀᴄᴄꜱ] μ = ρ[𝔸ᴠᴀᴄᴄꜱ] μ');
    [| apply (LA_proj_spec (R := label_ker 𝔸ᴠᴀᴄᴄꜱ) (f := ρ[𝔸ᴠᴀᴄᴄꜱ]))].
  split.
  - intros h. apply class_eq_vaccs.
    destruct μ as [[c v]|[c v]], μ' as [[c' v']|[c' v']]; simpl in *; congruence.
  - intros h%class_eq_vaccs_inv.
    destruct μ as [[c v]|[c v]], μ' as [[c' v']|[c' v']]; simpl in *;
      first [contradiction | by subst].
Qed.

Lemma ρ_incl_of_Γ_incl (S S' : subset_of A) :
  ⌈ Γᴠᴀᴄᴄꜱ ⌉ S ⊆ ⌈ Γᴠᴀᴄᴄꜱ ⌉ S' → ⌈ ρ[𝔸ᴠᴀᴄᴄꜱ] ⌉ S ⊆ ⌈ ρ[𝔸ᴠᴀᴄᴄꜱ] ⌉ S'.
Proof.
  intros h x (μ & hμ & ->).
  destruct (h (Γᴠᴀᴄᴄꜱ μ)) as (μ' & hμ' & e); [by exists μ |].
  exists μ'. split; [exact hμ' |].
  apply (LA_proj_spec (R := label_ker 𝔸ᴠᴀᴄᴄꜱ) (f := ρ[𝔸ᴠᴀᴄᴄꜱ])).
  apply (LA_proj_spec (R := label_ker 𝔸ᴠᴀᴄᴄꜱ) (f := Γᴠᴀᴄᴄꜱ)). exact e.
Qed.

Definition vaccs_verdict (m k n : nat) (p q : proc) : result := verdict m k n (p ▷ ∅) (q ▷ ∅).

Theorem vaccs_verdict_holds (m k n : nat) (p q : proc) : vaccs_verdict m k n p q = R_holds → p ⊑ₘᵤₛₜᵢ q.
Proof.
  intros h. pose proof (verdict_holds m k n _ _ h) as hc.
  apply must_iff_co_acceptance_set_VACCS. split.
  - intros s hp. exact (proj1 (hc s) hp).
  - intros s q' hp w st. destruct (proj2 (hc s) q' hp w st) as (p' & w' & st' & sub).
    exists p'. split_and!; [exact w' | exact st' | exact (ρ_incl_of_Γ_incl _ _ sub)].
Qed.

Theorem vaccs_verdict_refutes (m k n : nat) (p q : proc) s t : vaccs_verdict m k n p q = R_fails s t → p ⋢ₘᵤₛₜᵢ q.
Proof.
  intros h. destruct (verdict_fails m k n _ _ s t h) as [h1 h2].
  exact (distinguishing_test_refutes p q t h1 h2).
Qed.

End VACCS_Trace_Search.
(* end hide *)
