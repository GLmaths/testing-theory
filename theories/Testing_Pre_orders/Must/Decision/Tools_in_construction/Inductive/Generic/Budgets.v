(* begin hide *)
From Stdlib Require Import Lia.
From stdpp Require Import base countable gmap list sets numbers.
From TestingTheory Require Import ActTau gLts SyncActions Termination Subset_Act InListPropHelper
  coWeakTransition coConvergence coFiniteImage
  Decision.Tools_in_construction.Inductive.Generic.Helpers Decision.Tools_in_construction.Inductive.Generic.Bisim
  Decision.Tools_in_construction.Inductive.Generic.Interface Decision.Tools_in_construction.Inductive.Generic.Sets Decision.Tools_in_construction.Inductive.Generic.Transport Decision.Tools_in_construction.Inductive.Generic.Graph
  Decision.Tools_in_construction.Inductive.Generic.Swaps Decision.Tools_in_construction.Inductive.Generic.Adequacy Decision.Tools_in_construction.Inductive.Generic.Verdict.
Import ListNotations.

Section Budgets.

Context `{TS : TraceSearchLang P A Atom PreAct T}.

(** Existence of adequate budgets. *)

Definition bfs_closed (k : nat) (V : list (pair_states * list A)) : Prop :=
  ∀ e c, e ∈ V → c ∈ children_tr k e → in_graph c.1 (map fst V) = true.

Lemma bfs_tr_closes (k : nat) (F : list pair_states) (G : pair_states → Prop)
  (hG : ∀ x c, G x → c ∈ children k x → G c) (hF : ∀ x, G x → canon x ∈ F) :
  ∀ n visited work, length F - length visited = n →
  NoDup (map (λ e, canon e.1) visited) → (∀ e, e ∈ visited → G e.1) → (∀ e, e ∈ work → G e.1) →
  (∀ e c, e ∈ visited → c ∈ children_tr k e → in_graph c.1 (map fst visited) = true ∨ c ∈ work) →
  ∃ m, bfs_closed k (bfs_tr k m (canon_index (map fst visited)) visited work) ∧
    ∀ e, e ∈ work → in_graph e.1 (map fst (bfs_tr k m (canon_index (map fst visited)) visited work)) = true.
Proof.
  intros n. induction n as [n IHn] using lt_wf_ind. intros v w hn hnd hv hw hinv.
  revert hw hinv. induction w as [| e w IHw]; intros hw hinv.
  - exists 0. simpl. split.
    + intros e c me mc. destruct (hinv e c me mc) as [h | h]; [exact h | inversion h].
    + intros e me. inversion me.
  - destruct (in_graph e.1 (map fst v)) eqn:ge.
    + destruct IHw as (m & hcl & hall).
      * intros e' m'. apply hw. by apply list_elem_of_further.
      * intros e0 c me0 mc. destruct (hinv e0 c me0 mc) as [h | h]; [by left |].
        apply elem_of_cons in h as [-> | h]; [left; exact ge | by right].
      * exists (S m). cbn [bfs_tr]. rewrite in_graph_set, ge. split; [exact hcl |].
        intros e0 [-> | me0]%elem_of_cons; [| exact (hall e0 me0)].
        exact (in_graph_mono _ _ _ (map_fst_mono k m _ v w) ge).
    + assert (hev : canon e.1 ∉ map (λ e, canon e.1) v).
      { intros mc. apply list_elem_of_fmap in mc as (z & ez & mz).
        assert (in_graph e.1 (map fst v) = true) as h; [| congruence].
        apply existsb_exists. exists (canon z.1).
        split; [apply list_elem_of_In, list_elem_of_fmap_2, list_elem_of_fmap_2, mz | rewrite ez; apply same_pair_refl]. }
      assert (hnd' : NoDup (map (λ e, canon e.1) (e :: v))) by (simpl; constructor; assumption).
      assert (hlen : length (e :: v) ≤ length F).
      { rewrite <- (length_map (λ e, canon e.1) (e :: v)). apply submseteq_length, NoDup_submseteq; [exact hnd' |].
        intros c mc. apply list_elem_of_fmap in mc as (z & -> & mz). apply hF.
        apply elem_of_cons in mz as [-> | mz]; [apply hw, list_elem_of_here | apply hv, mz]. }
      destruct (IHn (length F - length (e :: v)) ltac:(simpl in *; lia) (e :: v) (w ++ children_tr k e) eq_refl hnd')
        as (m & hcl & hall).
      * intros z [-> | mz]%elem_of_cons; [apply hw, list_elem_of_here | apply hv, mz].
      * intros z [mz | mz]%elem_of_app; [apply hw, list_elem_of_further, mz |].
        apply (hG e.1); [apply hw, list_elem_of_here | exact (children_tr_fst k e z mz)].
      * intros e0 c me0 mc. apply elem_of_cons in me0 as [-> | me0]; [right; apply elem_of_app; right; exact mc |].
        destruct (hinv e0 c me0 mc) as [h | h].
        -- left. apply (in_graph_mono _ (map fst v)); [| exact h]. intros y my. simpl. by apply list_elem_of_further.
        -- apply elem_of_cons in h as [-> | h].
           ++ left. apply in_graph_refl. simpl. apply list_elem_of_here.
           ++ right. apply elem_of_app. left. exact h.
      * exists (S m). cbn [bfs_tr]. rewrite in_graph_set, ge. split; [exact hcl |].
        intros e0 [-> | me0]%elem_of_cons.
        -- apply (in_graph_mono _ _ _ (map_fst_mono k m _ (e :: v) _)). apply in_graph_refl. simpl. apply list_elem_of_here.
        -- apply hall. apply elem_of_app. left. exact me0.
Qed.

Lemma root_nodup (k : nat) (p q : P) c : root_pair k p q = Some c → NoDup c.1 ∧ NoDup c.2.
Proof.
  intros h. rewrite root_pair_unfold in h.
  destruct (τbounded k [p] && τbounded k [q]); [| discriminate]. injection h as <-.
  split; apply τclose_nodup, NoDup_singleton.
Qed.

Lemma children_nodup (k : nat) (x c : pair_states) : c ∈ children k x → NoDup c.1 ∧ NoDup c.2.
Proof.
  intros m. unfold children in m. apply list_elem_of_omap in m as (μ & _ & h). rewrite child_pair_unfold in h.
  destruct (τbounded k (ext x.1 μ) && τbounded k (ext x.2 μ)); [| discriminate]. injection h as <-.
  split; apply τclose_nodup, ext_nodup.
Qed.

Theorem adequate_exists (k : nat) (F : list pair_states) (p q : P) :
  adeq k [p] = true → adeq k [q] = true →
  (∀ x μ, node_exact p q x → adeq k (ext x.1 μ) = true ∧ adeq k (ext x.2 μ) = true) →
  (∀ x, node_exact p q x → NoDup x.1 → NoDup x.2 → canon x ∈ F) →
  ∃ m, adequate m k p q = true.
Proof.
  intros hp hq hch hF. destruct (root_pair k p q) as [c |] eqn:er.
  - destruct (bfs_tr_closes k F (λ x, node_exact p q x ∧ NoDup x.1 ∧ NoDup x.2)
                (λ x c hx mc, conj (children_exact k p q x c (proj1 hx) mc) (children_nodup k x c mc))
                (λ x hx, hF x (proj1 hx) (proj1 (proj2 hx)) (proj2 (proj2 hx))) _ [] [(c, [])] eq_refl)
      as (m & hcl & hroot).
    + constructor.
    + intros e me. inversion me.
    + intros e me. apply list_elem_of_singleton in me as ->. exact (conj (root_exact k p q c er) (root_nodup k p q c er)).
    + intros e c' me. inversion me.
    + exists m.
      assert (eR : pair_graph m k p q = map fst (bfs_tr k m (canon_index (map fst ([] : list (pair_states * list A)))) [] [(c, [])]))
        by (unfold pair_graph, graph_entries; rewrite er; reflexivity).
      pose proof (hroot (c, []) (list_elem_of_here _ _)) as hr. cbn [fst] in hr.
      unfold adequate. cbv zeta. rewrite er, eR, hp, hq, hr. cbn [andb].
      apply forallb_forall. intros x mx'. pose proof (proj2 (list_elem_of_In _ _) mx') as mx.
      apply forallb_forall. intros μ mμ.
      assert (hx : node_exact p q x) by (apply (pair_graph_exact m k p q); rewrite eR; exact mx).
      destruct (hch x μ hx) as [h1 h2]. rewrite h1, h2. cbn [andb].
      destruct (child_pair k x μ) as [c' |] eqn:ec; [| reflexivity].
      apply list_elem_of_fmap in mx as (e & -> & me).
      apply (hcl e (c', μ :: e.2) me). unfold children_tr. apply list_elem_of_omap.
      exists μ. split; [apply list_elem_of_In; exact mμ |]. rewrite ec. reflexivity.
  - exists 0.
    assert (eR : pair_graph 0 k p q = []) by (unfold pair_graph, graph_entries; rewrite er; reflexivity).
    unfold adequate. cbv zeta. rewrite er, eR, hp, hq. reflexivity.
Qed.

Corollary verdict_exists (k : nat) (F : list pair_states) (p q : P) :
  adeq k [p] = true → adeq k [q] = true →
  (∀ x μ, node_exact p q x → adeq k (ext x.1 μ) = true ∧ adeq k (ext x.2 μ) = true) →
  (∀ x, node_exact p q x → NoDup x.1 → NoDup x.2 → canon x ∈ F) →
  ∃ m, ∀ n, verdict m k n p q = R_holds ∨ ∃ s t, verdict m k n p q = R_fails s t.
Proof.
  intros hp hq hch hF. destruct (adequate_exists k F p q hp hq hch hF) as (m & ha).
  exists m. intros n. exact (verdict_complete m k n p q ha).
Qed.

(** Finite state spaces. *)

Fixpoint tpath (l : list P) : Prop :=
  match l with
  | x :: ((y :: _) as l') => x ⟶ y ∧ tpath l'
  | _ => True
  end.

Lemma tpath_app_r (l1 l2 : list P) : tpath (l1 ++ l2) → tpath l2.
Proof.
  induction l1 as [| a l1 IH]; intros h; [exact h |]. apply IH. simpl in h.
  destruct (l1 ++ l2) as [| b l]; [exact I | exact (proj2 h)].
Qed.

Lemma tpath_app_l (l1 l2 : list P) : tpath (l1 ++ l2) → tpath l1.
Proof.
  induction l1 as [| a l1 IH]; intros h; [exact I |].
  destruct l1 as [| b l1]; [exact I |]. simpl in h |- *. split; [exact (proj1 h) | apply IH, (proj2 h)].
Qed.

Lemma tpath_cowt (l : list P) : ∀ x, tpath (x :: l) → ∀ t, t ∈ x :: l → x ⟹ᶜᵒ t.
Proof.
  induction l as [| y l IH]; intros x hp t mt.
  - apply list_elem_of_singleton in mt as ->. apply cowt_nil.
  - destruct hp as [lx hp]. apply elem_of_cons in mt as [-> | mt]; [apply cowt_nil |].
    exact (cowt_tau [] x y t lx (IH y hp t mt)).
Qed.

Lemma tpath_reach (l1 : list P) : ∀ k (Y : list P) y l r l2,
  y ∈ Y → tpath (y :: l) → y :: l = l1 ++ r :: l2 → length l1 ≤ k → r ∈ τclose k Y.
Proof.
  induction l1 as [| a l1 IH]; intros k Y y l r l2 hy hp e hl.
  - injection e as -> _. apply τclose_incl, hy.
  - injection e as ea e. subst a.
    destruct l as [| z l']; [destruct l1; discriminate |].
    destruct hp as [hz hp]. destruct k as [| k]; [simpl in hl; lia |].
    simpl. apply elem_of_remove_dups, elem_of_app. right.
    apply (IH k _ z l' r l2); [exact (tau_succ_mem Y y z hy hz) | exact hp | exact e | simpl in hl; lia].
Qed.

Lemma tau_bounded_path (k : nat) : ∀ X, τbounded k X = false → ∃ x l, x ∈ X ∧ tpath (x :: l) ∧ length l = S k.
Proof.
  induction k as [| k IH]; intros X h; simpl in h.
  - apply bool_decide_eq_false in h. destruct (τsucc X) as [| y l0] eqn:es; [contradiction |].
    assert (my : y ∈ τsucc X) by (rewrite es; apply list_elem_of_here).
    destruct (τsucc_spec X y my) as (x & mx & lx).
    exists x, [y]. split_and!; [exact mx | split; [exact lx | exact I] | reflexivity].
  - destruct (IH _ h) as (y & l & my & hp & hl). destruct (τsucc_spec X y my) as (x & mx & lx).
    exists x, (y :: l). split_and!; [exact mx | split; [exact lx | exact hp] | simpl; lia].
Qed.

Lemma not_NoDup_split (l : list P) : ¬ NoDup l → ∃ l1 r l2 l3, l = l1 ++ r :: l2 ++ r :: l3.
Proof.
  induction l as [| a l IH]; intros h; [exfalso; apply h; constructor |].
  destruct (decide (a ∈ l)) as [m | m].
  - apply list_elem_of_split in m as (l2 & l3 & ->). exists [], a, l2, l3. reflexivity.
  - destruct IH as (l1 & r & l2 & l3 & ->); [intros hn; apply h; constructor; assumption |].
    exists (a :: l1), r, l2, l3. reflexivity.
Qed.

Lemma adeq_finite (Fp : list P) (Y : list P) : (∀ y t, y ∈ Y → y ⟹ᶜᵒ t → t ∈ Fp) → adeq (length Fp) Y = true.
Proof.
  intros hF. unfold adeq. destruct (τbounded (length Fp) Y) eqn:b; [reflexivity |]. cbn [orb].
  destruct (tau_bounded_path _ Y b) as (x & l & mx & hp & hl).
  assert (hnd : ¬ NoDup (x :: l)).
  { intros hnd. assert (length (x :: l) ≤ length Fp); [| simpl in *; lia].
    apply submseteq_length, NoDup_submseteq; [exact hnd |].
    intros t mt. exact (hF x t mx (tpath_cowt l x hp t mt)). }
  destruct (not_NoDup_split _ hnd) as (l1 & r & l2 & l3 & e).
  assert (hlen : length (x :: l) = length l1 + S (length l2 + S (length l3))).
  { rewrite e, length_app. simpl. rewrite length_app. simpl. lia. }
  simpl in hlen. unfold div_set. apply existsb_exists. exists r. split.
  - apply list_elem_of_In.
    apply (tpath_reach l1 _ Y x l r (l2 ++ r :: l3)); [exact mx | exact hp | exact e | lia].
  - apply orb_true_iff. right. apply bool_decide_eq_true.
    assert (hp2 : tpath (r :: l2 ++ [r])).
    { rewrite e in hp. pose proof (tpath_app_r l1 _ hp) as h2.
      replace (r :: l2 ++ r :: l3) with ((r :: l2 ++ [r]) ++ l3) in h2 by (simpl; rewrite <- app_assoc; reflexivity).
      exact (tpath_app_l _ _ h2). }
    destruct (l2 ++ [r]) as [| r1 l'] eqn:e2; [destruct l2; discriminate |].
    destruct hp2 as [l0 hp2].
    apply (tpath_reach l2 _ _ r1 l' r []);
      [exact (tau_succ_mem _ r r1 (list_elem_of_here _ _) l0) | exact hp2 | exact (eq_sym e2) | lia].
Qed.

Fixpoint lists_upto (l : list P) (n : nat) : list (list P) :=
  match n with
  | 0 => [[]]
  | S n => [] :: flat_map (λ a, (a ::.) <$> lists_upto l n) l
  end.

Lemma lists_upto_spec (l : list P) (n : nat) : ∀ (X : list P), (∀ r, r ∈ X → r ∈ l) → length X ≤ n → X ∈ lists_upto l n.
Proof.
  induction n as [| n IH]; intros X h hl; simpl.
  - destruct X; [apply list_elem_of_here | simpl in hl; lia].
  - destruct X as [| a X]; [apply list_elem_of_here |]. apply list_elem_of_further, elem_of_flat_map_list.
    exists a. split; [apply h, list_elem_of_here |]. apply list_elem_of_fmap_2, IH; [| simpl in hl; lia].
    intros r m. apply h, list_elem_of_further, m.
Qed.

Lemma nodup_length (Fp X : list P) : NoDup X → (∀ r, r ∈ X → r ∈ Fp) → length X ≤ length Fp.
Proof. intros hn h. apply submseteq_length, NoDup_submseteq; assumption. Qed.

Theorem adequate_of_finite_state (Fp : list P) (p q : P) :
  (∀ s r, p ⟹ᶜᵒ[s] r → r ∈ Fp) → (∀ s r, q ⟹ᶜᵒ[s] r → r ∈ Fp) → ∃ m, adequate m (length Fp) p q = true.
Proof.
  intros hp hq. apply (adequate_exists _ (canon <$> List.list_prod (lists_upto Fp (length Fp)) (lists_upto Fp (length Fp)))).
  - apply adeq_finite. intros y t my w. apply list_elem_of_singleton in my as ->. exact (hp [] t w).
  - apply adeq_finite. intros y t my w. apply list_elem_of_singleton in my as ->. exact (hq [] t w).
  - intros x μ (s & hX & hY & _ & _). split; apply adeq_finite; intros y t my w.
    + apply (hp (s ++ [μ])). apply (proj2 (child_gen p s x.1 hX μ t)). exists y. split; assumption.
    + apply (hq (s ++ [μ])). apply (proj2 (child_gen q s x.2 hY μ t)). exists y. split; assumption.
  - intros [X Y] (s & hX & hY & _ & _) nX nY. apply list_elem_of_fmap. exists (X, Y). split; [reflexivity |].
    assert (hX' : ∀ r, r ∈ X → r ∈ Fp) by (intros r m; exact (hp s r (proj1 (hX r) m))).
    assert (hY' : ∀ r, r ∈ Y → r ∈ Fp) by (intros r m; exact (hq s r (proj1 (hY r) m))).
    apply list_elem_of_In, in_prod; apply list_elem_of_In, lists_upto_spec.
    + exact hX'.
    + exact (nodup_length Fp X nX hX').
    + exact hY'.
    + exact (nodup_length Fp Y nY hY').
Qed.

Corollary verdict_of_finite_state (Fp : list P) (p q : P) :
  (∀ s r, p ⟹ᶜᵒ[s] r → r ∈ Fp) → (∀ s r, q ⟹ᶜᵒ[s] r → r ∈ Fp) →
  ∃ m, ∀ n, verdict m (length Fp) n p q = R_holds ∨ ∃ s t, verdict m (length Fp) n p q = R_fails s t.
Proof.
  intros hp hq. destruct (adequate_of_finite_state Fp p q hp hq) as (m & ha).
  exists m. intros n. exact (verdict_complete m (length Fp) n p q ha).
Qed.

End Budgets.
(* end hide *)
