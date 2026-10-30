(* begin hide *)
From Stdlib Require Import Lia.
From stdpp Require Import base countable gmap list sets.
From TestingTheory Require Import ActTau gLts SyncActions Termination Subset_Act InListPropHelper
  coWeakTransition coConvergence coFiniteImage
  Decision.Tools_in_construction.Inductive.Generic.Helpers Decision.Tools_in_construction.Inductive.Generic.Bisim
  Decision.Tools_in_construction.Inductive.Generic.Interface Decision.Tools_in_construction.Inductive.Generic.Sets Decision.Tools_in_construction.Inductive.Generic.Transport Decision.Tools_in_construction.Inductive.Generic.Graph.
Import ListNotations.

Section Swaps.

Context `{TS : TraceSearchLang P A Atom PreAct T}.

Lemma approx_swap_fix (a : Atom) (b : Atom) (x : P) (s : trace A) (X : list P) :
  approx_after x s X → (∀ r, r ∈ X → ts_swap a b r = r) → approx_after (ts_swap a b x) (swap_trace a b s) X.
Proof.
  intros [h1 h2] hf. split.
  - intros r w. apply cowt_swap_inv in w. rewrite swap_trace_invol in w.
    destruct (h1 _ w) as (r' & m & hb). exists r'. split; [exact m |].
    pose proof (sbisim_swap a b _ _ hb) as hb'. rewrite ts_swap_invol, (hf r' m) in hb'. exact hb'.
  - intros r' m. destruct (h2 r' m) as (r & w & hb). exists (ts_swap a b r). split.
    + exact (cowt_swap a b x s r w).
    + pose proof (sbisim_swap a b _ _ hb) as hb'. rewrite (hf r' m) in hb'. exact hb'.
Qed.

Definition fixes (π : list (Atom * Atom)) (D : list Atom) : Prop := ∀ a b, (a, b) ∈ π → a ∉ D ∧ b ∉ D.

Lemma node_atoms_fix (x : pair_states) (a : Atom) (b : Atom) r :
  a ∉ node_atoms x → b ∉ node_atoms x → r ∈ x.1 ∨ r ∈ x.2 → ts_swap a b r = r.
Proof.
  intros ha hb hr.
  assert (hr' : r ∈ x.1 ++ x.2) by (apply elem_of_app; exact hr).
  apply ts_swap_fix; intros m.
  - apply ha, elem_of_flat_map_list. exists r. split; [exact hr' | exact m].
  - apply hb, elem_of_flat_map_list. exists r. split; [exact hr' | exact m].
Qed.

Lemma approx_sws_fix (π : list (Atom * Atom)) (x : P) (s : trace A) (X : list P) (D : list Atom) :
  (∀ a b r, a ∉ D → b ∉ D → r ∈ X → ts_swap a b r = r) → fixes π D →
  approx_after x s X → approx_after (sws π x) (sws_trace π s) X.
Proof.
  intros hf. induction π as [| [a b] π IH]; simpl; intros hπ hX; [exact hX |].
  destruct (hπ a b (list_elem_of_here _ _)) as [ha hb].
  apply approx_swap_fix; [| intros r m; exact (hf a b r ha hb m)].
  apply IH; [| exact hX]. intros a' b' m. apply hπ. by apply list_elem_of_further.
Qed.

Definition foreign (E : list Atom) (l : list Atom) : nat := length (filter (λ c, c ∉ E) l).

Lemma foreign_swap (E : list Atom) (a f : Atom) (l : list Atom) :
  a ∉ E → f ∈ E → f ∉ l → ts_swap_atom a f a = f →
  foreign E (map (ts_swap_atom a f) l) ≤ foreign E l ∧
  (a ∈ l → foreign E (map (ts_swap_atom a f) l) < foreign E l).
Proof.
  intros haE hf hfl hs. induction l as [| c l IH].
  - split; [done | intros m; inversion m].
  - assert (hfl' : f ∉ l) by (intros m; apply hfl; right; exact m).
    destruct (IH hfl') as [IH1 IH2]. unfold foreign in *. simpl. rewrite !filter_cons.
    destruct (decide (c = a)) as [-> | hca].
    + rewrite hs. rewrite decide_False by (intros h; exact (h hf)). rewrite decide_True by exact haE.
      simpl. split; lia.
    + assert (hcf : c ≠ f) by (intros ->; apply hfl; left).
      rewrite (ts_swap_atom_other a f c hca hcf).
      destruct (decide (c ∉ E)); simpl; (split; [lia |]); intros m;
        apply elem_of_cons in m as [m | m]; try (subst; contradiction); specialize (IH2 m); lia.
Qed.

Lemma normalise (x : pair_states) : ∀ (n : nat) (μ : A),
  foreign (explored x) (ts_atoms_act μ) ≤ n → length (ts_atoms_act μ) ≤ node_arity x →
  ∃ σ, fixes σ (node_atoms x) ∧ in_atoms (explored x) (sws_act σ μ).
Proof.
  induction n as [| n IH]; intros μ hn hl.
  - exists []. split; [intros a b m; inversion m |]. simpl. intros a m.
    destruct (decide (a ∈ explored x)) as [h | h]; [exact h |]. exfalso.
    assert (0 < foreign (explored x) (ts_atoms_act μ)); [| lia].
    unfold foreign. apply list_elem_of_split in m as (l1 & l2 & ->).
    rewrite filter_app, filter_cons_True by exact h. rewrite length_app. simpl. lia.
  - destruct (decide (in_atoms (explored x) μ)) as [h | h].
    { exists []. split; [intros a b m; inversion m | exact h]. }
    assert (∃ a, a ∈ ts_atoms_act μ ∧ a ∉ explored x) as (a & ha & haE).
    { unfold in_atoms in h. destruct (decide (Exists (λ a, a ∉ explored x) (ts_atoms_act μ))) as [e | e].
      - apply Exists_exists in e as (a & m & na). exists a. split; assumption.
      - exfalso. apply h. intros a m. destruct (decide (a ∈ explored x)) as [h' | h']; [exact h' |].
        exfalso. apply e, Exists_exists. exists a. split; assumption. }
    assert (hap : a ∉ ts_pool (node_atoms x) (node_arity x)) by (intros m; apply haE, elem_of_app; right; exact m).
    destruct (ts_pool_spec (node_atoms x) (node_arity x) a (ts_atoms_act μ) hl ha hap) as (f & hf & hfμ & hs).
    assert (haD : a ∉ node_atoms x) by (intros m; apply haE, elem_of_app; left; exact m).
    assert (hfD : f ∉ node_atoms x) by exact (ts_pool_avoid _ _ f hf).
    assert (hfE : f ∈ explored x) by (apply elem_of_app; right; exact hf).
    destruct (IH (ts_swap_act a f μ)) as (σ & hσ & hin).
    + rewrite ts_atoms_act_swap. pose proof (proj2 (foreign_swap (explored x) a f _ haE hfE hfμ hs) ha). lia.
    + by rewrite ts_atoms_act_swap, length_map.
    + exists (σ ++ [(a, f)]). split.
      * intros a' b' m. apply elem_of_app in m as [m | m]; [exact (hσ a' b' m) |].
        apply list_elem_of_singleton in m. injection m as -> ->. split; assumption.
      * rewrite sws_act_app. exact hin.
Qed.

(** The invariant up to swaps. *)

Lemma node_arity_spec (x : pair_states) r : r ∈ x.2 → ts_arity r ≤ node_arity x.
Proof.
  intros m. unfold node_arity. revert m.
  generalize x.2. intros l m. induction l as [| y l IH]; [inversion m |].
  simpl. apply elem_of_cons in m as [-> | m]; [lia | specialize (IH m); lia].
Qed.

Lemma trace_inv_sw_step (k : nat) (p q : P) (R : list pair_states) (s : trace A) (μ : A) :
  certified k p q R = true → graph_closed R → trace_inv_sw p q R s → trace_inv_sw p q R (s ++ [μ]).
Proof.
  intros hc hgc [hn | [[hq hd] | (π & [hn | [[hq hd] | (x & mx & hX & hY & hp & hq)]])]].
  - left. intros h. exact (hn (cocnv_app_l p s [μ] h)).
  - right; left. apply trace_inv_dead; [exact hq |].
    intros q' w. apply cowt_split in w as (r & w & _). exact (hd r w).
  - left. intros h. apply hn. apply (cocnv_app_l _ _ [sws_act π μ]).
    rewrite <- sws_trace_snoc. apply cocnv_sws, h.
  - right; left. apply trace_inv_dead; [exact (cocnv_sws_back π q s hq) |].
    intros q' w. apply cowt_split in w as (r & w & _). exact (hd (sws π r) (cowt_sws π q s r w)).
  - set (μ1 := sws_act π μ).
    destruct (ext x.2 μ1) as [| r2 l2] eqn:he.
    + right; left. apply trace_inv_dead; [exact (cocnv_sws_back π q s hq) |].
      intros q' w. destruct (hgc x mx) as [_ cl2]. apply (approx_dead _ _ x.2 μ1 hY cl2 he (sws π q')).
      pose proof (cowt_sws π q _ q' w) as w'. rewrite sws_trace_snoc in w'. exact w'.
    + right; right.
      assert (m2 : r2 ∈ ext x.2 μ1) by (rewrite he; apply list_elem_of_here).
      apply ext_spec in m2 as (r1 & m1 & μ' & duo & l).
      pose proof (node_arity_spec x r1 m1) as har.
      pose proof (ts_arity_spec r1 μ1 μ' r2 duo l) as har'.
      destruct (normalise x _ μ1 (le_n _) ltac:(lia)) as (σ & hσ & hin).
      assert (hfx : ∀ a b r, a ∉ node_atoms x → b ∉ node_atoms x → r ∈ x.1 → ts_swap a b r = r)
        by (intros a b r ha hb m; exact (node_atoms_fix x a b r ha hb (or_introl m))).
      assert (hfy : ∀ a b r, a ∉ node_atoms x → b ∉ node_atoms x → r ∈ x.2 → ts_swap a b r = r)
        by (intros a b r ha hb m; exact (node_atoms_fix x a b r ha hb (or_intror m))).
      destruct (inv_step_node k p q R x (sws (σ ++ π) p) (sws (σ ++ π) q) (sws_trace (σ ++ π) s) (sws_act (σ ++ π) μ)
                  hc hgc mx) as (π' & hi).
      * rewrite sws_act_app. exact hin.
      * rewrite sws_app, sws_trace_app. exact (approx_sws_fix σ _ _ _ _ hfx hσ hX).
      * rewrite sws_app, sws_trace_app. exact (approx_sws_fix σ _ _ _ _ hfy hσ hY).
      * rewrite sws_app, sws_trace_app. exact (cocnv_sws σ _ _ hp).
      * rewrite sws_app, sws_trace_app. exact (cocnv_sws σ _ _ hq).
      * exists (π' ++ σ ++ π).
        rewrite (sws_app π' (σ ++ π) p), (sws_app π' (σ ++ π) q), (sws_trace_app π' (σ ++ π)), sws_trace_snoc.
        exact hi.
Qed.

Lemma trace_inv_sw_all (k : nat) (p q : P) (R : list pair_states) :
  certified k p q R = true → graph_closed R → ∀ s, trace_inv_sw p q R s.
Proof.
  intros hc hgc s. induction s as [| μ s IH] using rev_ind.
  - exact (trace_inv_root k p q R hc).
  - exact (trace_inv_sw_step k p q R s μ hc hgc IH).
Qed.

Theorem certify_spec (m k : nat) (p q : P) : certify m k p q = true → ∀ s, co_conditions p q s.
Proof.
  intros hc s. destruct (trace_inv_sw_all k p q _ hc (pair_graph_closed m k p q) s) as [hn | [[hq hd] | (π & hi)]].
  - rewrite <- (app_nil_r s). exact (co_conditions_pdiv p q s [] hn).
  - split; [intros _; exact hq |]. intros q' _ w. exfalso. exact (hd q' w).
  - apply (co_conditions_sws_back π). exact (co_conditions_of_inv k p q _ _ _ _ hc hi).
Qed.

End Swaps.
(* end hide *)
