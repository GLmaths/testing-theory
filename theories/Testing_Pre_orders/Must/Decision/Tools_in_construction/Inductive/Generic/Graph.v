(* begin hide *)
From Stdlib Require Import Lia.
From stdpp Require Import base countable gmap list sets numbers.
From TestingTheory Require Import ActTau gLts SyncActions Termination Subset_Act InListPropHelper
  coWeakTransition coConvergence coFiniteImage
  Decision.Tools_in_construction.Inductive.Generic.Helpers Decision.Tools_in_construction.Inductive.Generic.Bisim
  Decision.Tools_in_construction.Inductive.Generic.Interface Decision.Tools_in_construction.Inductive.Generic.Sets Decision.Tools_in_construction.Inductive.Generic.Transport.
Import ListNotations.

Section Graph.

Context `{TS : TraceSearchLang P A Atom PreAct T}.

(** The pair graph and its certificate. *)

Definition pair_states : Type := list P * list P.

Definition norm_pair (x : pair_states) : pair_states := (ts_norm <$> x.1, ts_norm <$> x.2).

Definition node_atoms (x : pair_states) : list Atom := flat_map ts_atoms (x.1 ++ x.2).

Fixpoint canon_go (C used : list Atom) (σ : list (Atom * Atom)) (l : list Atom) : list (Atom * Atom) :=
  match l with
  | [] => σ
  | a :: l =>
      let a' := sws_atom σ a in
      if bool_decide (a' ∈ C ∧ a' ∉ used) then canon_go C (a' :: used) σ l
      else match find (λ f, bool_decide (f ∉ used ∧ ts_swap_atom a' f a' = f)) C with
           | Some f => canon_go C (f :: used) ((a', f) :: σ) l
           | None => canon_go C used σ l
           end
  end.

Definition canon_sw (x : pair_states) : list (Atom * Atom) :=
  let l := remove_dups (node_atoms x) in canon_go (ts_pool [] (length l)) [] [] l.

Definition sw_pair (π : list (Atom * Atom)) (x : pair_states) : pair_states :=
  (sws π <$> x.1, sws π <$> x.2).

Definition canon (x : pair_states) : pair_states := norm_pair (sw_pair (canon_sw x) x).

Definition same_set (X Y : list P) : bool :=
  forallb (λ a, bool_decide (a ∈ Y)) X && forallb (λ a, bool_decide (a ∈ X)) Y.

Lemma same_set_spec (X Y : list P) : same_set X Y = true ↔ ∀ z, z ∈ X ↔ z ∈ Y.
Proof.
  unfold same_set. rewrite andb_true_iff, !forallb_forall. split.
  - intros [h1 h2] z. split; intros m.
    + apply (bool_decide_eq_true_1 _ (h1 z (proj1 (list_elem_of_In _ _) m))).
    + apply (bool_decide_eq_true_1 _ (h2 z (proj1 (list_elem_of_In _ _) m))).
  - intros h. split; intros z m; apply bool_decide_eq_true_2, h, list_elem_of_In, m.
Qed.

Definition same_pair (x y : pair_states) : bool := same_set x.1 y.1 && same_set x.2 y.2.

Lemma same_pair_refl (x : pair_states) : same_pair x x = true.
Proof. unfold same_pair. rewrite !(proj2 (same_set_spec _ _)); done. Qed.

Definition canon_set (R : list pair_states) : list pair_states := canon <$> R.

Definition in_graph (c : pair_states) (R : list pair_states) : bool := existsb (same_pair (canon c)) (canon_set R).


Lemma in_graph_spec (c : pair_states) (R : list pair_states) :
  in_graph c R = true → ∃ y, y ∈ R ∧ (∀ z, z ∈ (canon c).1 ↔ z ∈ (canon y).1) ∧ (∀ z, z ∈ (canon c).2 ↔ z ∈ (canon y).2).
Proof.
  intros h. apply existsb_exists in h as (cy & m & h). apply list_elem_of_In, list_elem_of_fmap in m as (y & -> & m).
  unfold same_pair in h. apply andb_true_iff in h as [h1 h2].
  exists y. split_and!; [exact m | apply same_set_spec, h1 | apply same_set_spec, h2].
Qed.

Lemma in_graph_refl (c : pair_states) (R : list pair_states) : c ∈ R → in_graph c R = true.
Proof.
  intros m. apply existsb_exists. exists (canon c).
  split; [apply list_elem_of_In, list_elem_of_fmap_2, m | apply same_pair_refl].
Qed.

Definition sum_key (l : list P) : N := foldr (λ x acc, (N.succ (N.of_nat (ts_hash x)) + acc)%N) 0%N l.

Lemma sum_perm (l l' : list P) : l ≡ₚ l' → sum_key l = sum_key l'.
Proof. induction 1; simpl; lia. Qed.

Definition set_key (X : list P) : N := sum_key (remove_dups X).

Lemma set_key_same (X Y : list P) : same_set X Y = true → set_key X = set_key Y.
Proof.
  intros h. pose proof (proj1 (same_set_spec X Y) h) as h'. clear h. unfold set_key. apply sum_perm, NoDup_Permutation; [apply NoDup_remove_dups | apply NoDup_remove_dups |].
  intros z. rewrite !elem_of_remove_dups. apply h'.
Qed.

Definition node_key (x : pair_states) : N * N := (set_key x.1, set_key x.2).

Lemma node_key_same (x y : pair_states) : same_pair x y = true → node_key x = node_key y.
Proof. unfold same_pair. intros [h1 h2]%andb_true_iff. unfold node_key. by rewrite (set_key_same _ _ h1), (set_key_same _ _ h2). Qed.

Definition idx_mem (c : pair_states) (I : gmap (N * N) (list pair_states)) : bool :=
  match I !! node_key c with
  | Some l => existsb (same_pair c) l
  | None => false
  end.

Definition idx_add (c : pair_states) (I : gmap (N * N) (list pair_states)) : gmap (N * N) (list pair_states) := <[node_key c := c :: default [] (I !! node_key c)]> I.

Definition canon_index (R : list pair_states) : gmap (N * N) (list pair_states) := foldr (λ y I, idx_add (canon y) I) ∅ R.

Lemma idx_mem_add (c y : pair_states) (I : gmap (N * N) (list pair_states)) : idx_mem c (idx_add y I) = same_pair c y || idx_mem c I.
Proof.
  unfold idx_mem, idx_add. destruct (decide (node_key y = node_key c)) as [e | ne].
  - rewrite e, lookup_insert_eq. simpl. destruct (I !! node_key c); reflexivity.
  - rewrite lookup_insert_ne by exact ne. destruct (same_pair c y) eqn:hs; [| reflexivity].
    exfalso. apply ne. symmetry. exact (node_key_same _ _ hs).
Qed.

Lemma in_graph_set (c : pair_states) (R : list pair_states) : idx_mem (canon c) (canon_index R) = in_graph c R.
Proof.
  unfold in_graph, canon_set. induction R as [| y R IH]; [reflexivity |].
  change (canon_index (y :: R)) with (idx_add (canon y) (canon_index R)). rewrite idx_mem_add, IH. reflexivity.
Qed.

Definition approx_after (x : P) (s : trace A) (X : list P) : Prop :=
  (∀ r, x ⟹ᶜᵒ[s] r → ∃ r', r' ∈ X ∧ sbisim r r') ∧ (∀ r', r' ∈ X → ∃ r, x ⟹ᶜᵒ[s] r ∧ sbisim r r').

Lemma approx_of_exact (x : P) (s : trace A) (X : list P) : exact_after x s X → approx_after x s X.
Proof.
  intros hX. split.
  - intros r w. exists r. split; [apply hX, w | apply sbisim_refl].
  - intros r' m. exists r'. split; [apply hX, m | apply sbisim_refl].
Qed.

Lemma norm_bisim (r r' : P) : ts_norm r = ts_norm r' → sbisim r r'.
Proof.
  intros e. apply (sbisim_trans _ (ts_norm r)); [apply sbisim_sym, ts_norm_spec |]. rewrite e. apply ts_norm_spec.
Qed.

Lemma approx_norm (x : P) (s : trace A) (X Y : list P) :
  approx_after x s X → (∀ z, z ∈ ts_norm <$> X ↔ z ∈ ts_norm <$> Y) → approx_after x s Y.
Proof.
  intros [h1 h2] e. split.
  - intros r w. destruct (h1 r w) as (r' & m & hb).
    assert (hn : ts_norm r' ∈ ts_norm <$> Y) by (apply e, list_elem_of_fmap_2, m).
    apply list_elem_of_fmap in hn as (r'' & er & m''). exists r''. split; [exact m'' |].
    exact (sbisim_trans _ _ _ hb (norm_bisim _ _ er)).
  - intros r'' m''.
    assert (hn : ts_norm r'' ∈ ts_norm <$> X) by (apply e, list_elem_of_fmap_2, m'').
    apply list_elem_of_fmap in hn as (r' & er & m'). destruct (h2 r' m') as (r & w & hb).
    exists r. split; [exact w |]. exact (sbisim_trans _ _ _ hb (norm_bisim _ _ (eq_sym er))).
Qed.

Lemma approx_sws (π : list (Atom * Atom)) (x : P) (s : trace A) (X : list P) :
  approx_after x s X → approx_after (sws π x) (sws_trace π s) (sws π <$> X).
Proof.
  intros [h1 h2]. split.
  - intros r w. pose proof (cowt_sws (rev π) _ _ _ w) as w'.
    rewrite sws_rev_invol, sws_trace_rev_invol in w'.
    destruct (h1 _ w') as (r' & m & hb). exists (sws π r'). split; [by apply list_elem_of_fmap_2 |].
    pose proof (sbisim_sws π _ _ hb) as hb'.
    rewrite <- (rev_involutive π) in hb' at 1. rewrite sws_rev_invol in hb'. exact hb'.
  - intros r'' m. apply list_elem_of_fmap in m as (r' & -> & m). destruct (h2 r' m) as (r & w & hb).
    exists (sws π r). split; [exact (cowt_sws π x s r w) | exact (sbisim_sws π _ _ hb)].
Qed.

Lemma map_sws_rev (π : list (Atom * Atom)) (Y : list P) : sws (rev π) <$> (sws π <$> Y) = Y.
Proof.
  rewrite <- list_fmap_compose. rewrite <- (list_fmap_id Y) at 2.
  apply list_fmap_ext. intros i y _. apply sws_rev_invol.
Qed.

Lemma approx_canon (π1 π2 : list (Atom * Atom)) (x : P) (s : trace A) (X Y : list P) :
  approx_after x s X → (∀ z, z ∈ ts_norm <$> (sws π1 <$> X) ↔ z ∈ ts_norm <$> (sws π2 <$> Y)) →
  approx_after (sws (rev π2 ++ π1) x) (sws_trace (rev π2 ++ π1) s) Y.
Proof.
  intros hX e. rewrite sws_app, sws_trace_app, <- (map_sws_rev π2 Y).
  apply approx_sws. exact (approx_norm _ _ _ _ (approx_sws π1 x s X hX) e).
Qed.

Definition tau_closed (X : list P) : Prop := ∀ y y', y ∈ X → y ⟶ y' → y' ∈ X.

Lemma closed_nil (X : list P) p q : tau_closed X → p ∈ X → p ⟹ᶜᵒ q → q ∈ X.
Proof.
  intros hX hp w. remember ([] : trace A) as s0 eqn:hs0 in w. revert hs0 hp.
  induction w as [p | s0 p p' q l w IH | ]; intros hs0 hp; [done | | discriminate].
  eapply IH; [exact hs0 | eapply hX; eauto].
Qed.

Lemma τclose_closed (k : nat) (Y : list P) : τbounded k Y = true → tau_closed (τclose k Y).
Proof.
  intros hb y y' m l. destruct (τclose_sound k Y y m) as (x & mx & w).
  exact (τclose_complete k Y hb x y' mx (cowt_push_nil_right x y y' [] w (lts_to_cowt_tau l))).
Qed.

Lemma τclose_terminate (k : nat) (Y : list P) : τbounded k Y = true → ∀ r, r ∈ τclose k Y → r ⤓.
Proof.
  intros hb r m. destruct (τclose_sound k Y r m) as (y & my & w).
  exact (cocnv_terminate r [] (cocnv_preserved_by_cowt_nil [] y (cocnv_nil y (τbounded_terminate k Y hb y my)) r w)).
Qed.

Lemma approx_child (k : nat) (x : P) (s : trace A) (X : list P) (μ : A) :
  approx_after x s X → tau_closed X → τbounded k (ext X μ) = true → x ⇓ᶜᵒ s →
  approx_after x (s ++ [μ]) (τclose k (ext X μ)) ∧ x ⇓ᶜᵒ s ++ [μ].
Proof.
  intros [h1 h2] hcl hb hx.
  assert (fwd : ∀ r, x ⟹ᶜᵒ[s ++ [μ]] r → ∃ r', r' ∈ τclose k (ext X μ) ∧ sbisim r r').
  { intros r w. apply cowt_split in w as (r0 & w0 & w1).
    destruct (h1 r0 w0) as (y & my & hb0).
    destruct (sbisim_cowt r0 y [μ] r hb0 w1) as (r' & wy & hr).
    destruct (cowt_decomp_one wy) as (y1 & y2 & μ' & w2 & duo & l & w3).
    exists r'. split; [| exact hr].
    apply (τclose_complete k _ hb y2 r'); [| exact w3].
    apply ext_spec. exists y1. split; [exact (closed_nil X y y1 hcl my w2) |].
    exists μ'. split; [exact duo | exact l]. }
  split; [split |].
  - exact fwd.
  - intros r' m. destruct (τclose_sound k _ r' m) as (y2 & m2 & w).
    apply ext_spec in m2 as (y1 & m1 & μ' & duo & l).
    destruct (h2 y1 m1) as (p0 & w0 & hb0).
    destruct (sbisim_step y1 p0 (ActExt μ') y2 (sbisim_sym _ _ hb0) l) as (p2 & l2 & hb2).
    destruct (sbisim_cowt y2 p2 [] r' hb2 w) as (r & w2 & hb3).
    exists r. split; [| exact (sbisim_sym _ _ hb3)].
    apply (cowt_concat x p0 r s [μ]); [exact w0 |].
    exact (cowt_push_nil_right p0 p2 r [μ] (lts_to_cowt duo l2) w2).
  - apply (cocnv_snoc x s μ hx). intros r w. destruct (fwd r w) as (r' & m & hr).
    exact (sbisim_terminate r' r (sbisim_sym _ _ hr) (τclose_terminate k _ hb r' m)).
Qed.

Lemma approx_dead (q : P) (s : trace A) (Y : list P) (μ : A) :
  approx_after q s Y → tau_closed Y → ext Y μ = [] → ∀ q', ¬ q ⟹ᶜᵒ[s ++ [μ]] q'.
Proof.
  intros [h1 _] hcl he q' w. apply cowt_split in w as (r0 & w0 & w1).
  destruct (h1 r0 w0) as (y & my & hb0).
  destruct (sbisim_cowt r0 y [μ] q' hb0 w1) as (r' & wy & _).
  destruct (cowt_decomp_one wy) as (y1 & y2 & μ' & w2 & duo & l & _).
  assert (y2 ∈ ext Y μ) as m.
  { apply ext_spec. exists y1. split; [exact (closed_nil Y y y1 hcl my w2) |].
    exists μ'. split; [exact duo | exact l]. }
  rewrite he in m. inversion m.
Qed.

Lemma approx_no_cotrace (vals : list Atom) (q : P) (s : trace A) (Y : list P) (μ : A) :
  approx_after q s Y → tau_closed Y → in_atoms vals μ → μ ∉ next_list vals Y →
  ∀ q', ¬ q ⟹ᶜᵒ[s ++ [μ]] q'.
Proof.
  intros [h1 _] hcl hv hn q' w. apply cowt_split in w as (r0 & w0 & w1).
  destruct (h1 r0 w0) as (y & my & hb0).
  destruct (sbisim_cowt r0 y [μ] q' hb0 w1) as (r' & wy & _).
  destruct (cowt_decomp_one wy) as (y1 & y2 & μ' & w2 & duo & l & _).
  apply hn. eapply (next_list_spec vals _ y1 μ μ' y2); [| exact duo | exact l | exact hv].
  exact (closed_nil Y y y1 hcl my w2).
Qed.


Definition root_pair (k : nat) (p q : P) : option pair_states :=
  match τclose_b k [p], τclose_b k [q] with
  | Some X, Some Y => Some (X, Y)
  | _, _ => None
  end.

Lemma root_pair_unfold (k : nat) (p q : P) :
  root_pair k p q = if τbounded k [p] && τbounded k [q] then Some (τclose k [p], τclose k [q]) else None.
Proof. unfold root_pair. rewrite !τclose_b_eq. destruct (τbounded k [p]), (τbounded k [q]); reflexivity. Qed.

Definition child_pair (k : nat) (x : pair_states) (μ : A) : option pair_states :=
  match τclose_b k (ext x.1 μ), τclose_b k (ext x.2 μ) with
  | Some X, Some Y => Some (X, Y)
  | _, _ => None
  end.

Lemma child_pair_unfold (k : nat) (x : pair_states) (μ : A) :
  child_pair k x μ = if τbounded k (ext x.1 μ) && τbounded k (ext x.2 μ)
                     then Some (τclose k (ext x.1 μ), τclose k (ext x.2 μ)) else None.
Proof. unfold child_pair. rewrite !τclose_b_eq. destruct (τbounded k (ext x.1 μ)), (τbounded k (ext x.2 μ)); reflexivity. Qed.

Definition local_ok (x : pair_states) : bool :=
  forallb (λ y, existsb (λ x', if coR_dichotomy x' y then true else false) (stable_list x.1)) (stable_list x.2).

Definition node_arity (x : pair_states) : nat := foldr max 0 (map ts_arity x.2).

Definition explored (x : pair_states) : list Atom :=
  node_atoms x ++ ts_pool (node_atoms x) (node_arity x).

Definition child_ok (k : nat) (S : gmap (N * N) (list pair_states)) (x : pair_states) (μ : A) : bool :=
  match child_pair k x μ with
  | Some c => idx_mem (canon c) S
  | None => false
  end || div_set k (ext x.1 μ).

Definition root_ok (k : nat) (p q : P) (S : gmap (N * N) (list pair_states)) : bool :=
  div_set k [p] ||
  match root_pair k p q with
  | Some c => idx_mem (canon c) S
  | None => false
  end.

Definition certified_in (k : nat) (p q : P) (R : list pair_states) (S : gmap (N * N) (list pair_states)) : bool :=
  root_ok k p q S &&
  forallb (λ x, local_ok x && forallb (child_ok k S x) (next_list (explored x) x.2)) R.

Definition certified (k : nat) (p q : P) (R : list pair_states) : bool := certified_in k p q R (canon_index R).

Definition children (k : nat) (x : pair_states) : list pair_states :=
  omap (child_pair k x) (next_list (explored x) x.2).

Definition children_tr (k : nat) (e : pair_states * list A) : list (pair_states * list A) :=
  omap (λ μ, (λ c, (c, μ :: e.2)) <$> child_pair k e.1 μ) (next_list (explored e.1) e.1.2).

Fixpoint bfs_tr (k m : nat) (seen : gmap (N * N) (list pair_states)) (visited work : list (pair_states * list A)) :
  list (pair_states * list A) :=
  match m with
  | 0 => visited
  | S m =>
      match work with
      | [] => visited
      | e :: work' =>
          let c := canon e.1 in
          if idx_mem c seen then bfs_tr k m seen visited work'
          else bfs_tr k m (idx_add c seen) (e :: visited) (work' ++ children_tr k e)
      end
  end.

Definition graph_entries (m k : nat) (p q : P) : list (pair_states * list A) :=
  match root_pair k p q with
  | Some c => bfs_tr k m ∅ [] [(c, [])]
  | None => []
  end.

Definition pair_graph (m k : nat) (p q : P) : list pair_states := map fst (graph_entries m k p q).

Definition graph_traces (m k : nat) (p q : P) : list (list A) := map snd (graph_entries m k p q).

Definition certify (m k : nat) (p q : P) : bool := certified k p q (pair_graph m k p q).

Definition graph_closed (R : list pair_states) : Prop := ∀ x, x ∈ R → tau_closed x.1 ∧ tau_closed x.2.

Lemma children_tr_fst (k : nat) (e c : pair_states * list A) : c ∈ children_tr k e → c.1 ∈ children k e.1.
Proof.
  unfold children_tr, children. intros m. apply list_elem_of_omap in m as (μ & mμ & h).
  apply list_elem_of_omap. exists μ. split; [exact mμ |].
  destruct (child_pair k e.1 μ) as [c' |]; [| discriminate]. injection h as <-. reflexivity.
Qed.

Lemma bfs_tr_inv (k : nat) (Q : pair_states → Prop) (hQ : ∀ x c, Q x → c ∈ children k x → Q c) :
  ∀ m seen visited work, (∀ e, e ∈ visited → Q e.1) → (∀ e, e ∈ work → Q e.1) →
  ∀ e, e ∈ bfs_tr k m seen visited work → Q e.1.
Proof.
  induction m as [| m IH]; intros seen visited work hv hw x hx; simpl in hx; [exact (hv x hx) |].
  destruct work as [| y work']; [exact (hv x hx) |].
  destruct (idx_mem (canon y.1) seen).
  - apply (IH seen visited work' hv); [intros z hz; apply hw, list_elem_of_further, hz | exact hx].
  - apply (IH (idx_add (canon y.1) seen) (y :: visited) (work' ++ children_tr k y)); [| | exact hx].
    + intros z [-> | hz]%elem_of_cons; [apply hw, list_elem_of_here | exact (hv z hz)].
    + intros z [hz | hz]%elem_of_app; [apply hw, list_elem_of_further, hz |].
      apply (hQ y.1 z.1); [apply hw, list_elem_of_here | exact (children_tr_fst k y z hz)].
Qed.

Lemma pair_graph_inv (m k : nat) (p q : P) (Q : pair_states → Prop) :
  (∀ x c, Q x → c ∈ children k x → Q c) → (∀ c, root_pair k p q = Some c → Q c) →
  ∀ x, x ∈ pair_graph m k p q → Q x.
Proof.
  intros hQ hr x hx. unfold pair_graph, graph_entries in hx.
  destruct (root_pair k p q) as [c |] eqn:e; [| inversion hx].
  apply list_elem_of_fmap in hx as (e' & -> & he).
  apply (bfs_tr_inv k Q hQ m ∅ [] [(c, [])]); [intros z hz; inversion hz | | exact he].
  intros z hz. apply list_elem_of_singleton in hz as ->. exact (hr c eq_refl).
Qed.

Lemma pair_graph_closed (m k : nat) (p q : P) : graph_closed (pair_graph m k p q).
Proof.
  intros x. apply (pair_graph_inv m k p q (λ x, tau_closed x.1 ∧ tau_closed x.2)).
  - intros y c _ mc. unfold children in mc. apply list_elem_of_omap in mc as (μ & _ & h).
    rewrite child_pair_unfold in h. destruct (τbounded k (ext y.1 μ)) eqn:b1, (τbounded k (ext y.2 μ)) eqn:b2;
      simpl in h; try discriminate. injection h as <-. split; apply τclose_closed; assumption.
  - intros c h. rewrite root_pair_unfold in h. destruct (τbounded k [p]) eqn:b1, (τbounded k [q]) eqn:b2;
      simpl in h; try discriminate. injection h as <-. split; apply τclose_closed; assumption.
Qed.

Definition trace_inv (p q : P) (R : list pair_states) (s : trace A) : Prop :=
  ¬ p ⇓ᶜᵒ s ∨ (q ⇓ᶜᵒ s ∧ ∀ q', ¬ q ⟹ᶜᵒ[s] q') ∨
  ∃ x, x ∈ R ∧ approx_after p s x.1 ∧ approx_after q s x.2 ∧ p ⇓ᶜᵒ s ∧ q ⇓ᶜᵒ s.

Definition trace_inv_sw (p q : P) (R : list pair_states) (s : trace A) : Prop :=
  ¬ p ⇓ᶜᵒ s ∨ (q ⇓ᶜᵒ s ∧ ∀ q', ¬ q ⟹ᶜᵒ[s] q') ∨
  ∃ π, trace_inv (sws π p) (sws π q) R (sws_trace π s).

Lemma in_graph_inv (c : pair_states) (R : list pair_states) (p q : P) (s : trace A) :
  in_graph c R = true → approx_after p s c.1 → approx_after q s c.2 → p ⇓ᶜᵒ s → q ⇓ᶜᵒ s →
  ∃ π, trace_inv (sws π p) (sws π q) R (sws_trace π s).
Proof.
  intros h hX hY hp hq. destruct (in_graph_spec _ _ h) as (y & my & e).
  destruct e as [e1 e2]. unfold canon, norm_pair, sw_pair in e1, e2. simpl in e1, e2.
  exists (rev (canon_sw y) ++ canon_sw c). right; right. exists y. split_and!; [exact my | | | |].
  - exact (approx_canon _ _ p s _ _ hX e1).
  - exact (approx_canon _ _ q s _ _ hY e2).
  - exact (cocnv_sws _ p s hp).
  - exact (cocnv_sws _ q s hq).
Qed.

Lemma local_ok_spec (p q : P) (s : trace A) (x : pair_states) :
  local_ok x = true → approx_after p s x.1 → approx_after q s x.2 →
  ∀ q', q ⟹ᶜᵒ[s] q' → q' ↛ → ∃ p', p ⟹ᶜᵒ[s] p' ∧ p' ↛ ∧ ⌈ ts_Γ ⌉ (coR p') ⊆ ⌈ ts_Γ ⌉ (coR q').
Proof.
  intros h [hX1 hX2] [hY1 hY2] q' w st. destruct (hY1 q' w) as (y & my & hqy).
  assert (sty : y ↛) by exact (sbisim_stable q' y hqy st).
  unfold local_ok in h. rewrite forallb_forall in h.
  assert (y ∈ stable_list x.2) as m by (unfold stable_list; apply list_elem_of_filter; split; [apply stable_b_spec |]; assumption).
  specialize (h y (proj1 (list_elem_of_In _ _) m)).
  apply existsb_exists in h as (x' & mx' & h).
  destruct (coR_dichotomy x' y) as [sub |]; [| discriminate].
  apply list_elem_of_In in mx'. unfold stable_list in mx'. apply list_elem_of_filter in mx' as [stx%stable_b_spec mx].
  destruct (hX2 x' mx) as (p' & wp & hpx).
  exists p'. split_and!; [exact wp | exact (sbisim_stable x' p' (sbisim_sym _ _ hpx) stx) |].
  intros z hz. apply (sbisim_coR ts_Γ y q' z (sbisim_sym _ _ hqy)). apply sub.
  exact (sbisim_coR ts_Γ p' x' z hpx hz).
Qed.

Lemma certified_local (k : nat) (p q : P) (R : list pair_states) (x : pair_states) :
  certified k p q R = true → x ∈ R →
  local_ok x = true ∧ ∀ μ, μ ∈ next_list (explored x) x.2 → child_ok k (canon_index R) x μ = true.
Proof.
  intros h m. apply andb_true_iff in h as [_ h]. rewrite forallb_forall in h.
  specialize (h x (proj1 (list_elem_of_In _ _) m)). apply andb_true_iff in h as [h1 h2].
  split; [exact h1 |]. intros μ mμ. rewrite forallb_forall in h2. exact (h2 μ (proj1 (list_elem_of_In _ _) mμ)).
Qed.

Lemma trace_inv_root (k : nat) (p q : P) (R : list pair_states) : certified k p q R = true → trace_inv_sw p q R [].
Proof.
  intros h. apply andb_true_iff in h as [h _]. apply orb_true_iff in h as [h | h].
  - left. destruct (div_set_spec k _ h) as (r & hr%list_elem_of_singleton & hn).
    intros hc. apply hn. rewrite hr. exact (cocnv_terminate p [] hc).
  - right; right. rewrite root_pair_unfold in h.
    destruct (τbounded k [p]) eqn:bp, (τbounded k [q]) eqn:bq; simpl in h; try discriminate.
    rewrite in_graph_set in h. apply (in_graph_inv _ R p q [] h).
    + exact (approx_of_exact _ _ _ (τclose_exact p [] _ k (root_gen p) bp)).
    + exact (approx_of_exact _ _ _ (τclose_exact q [] _ k (root_gen q) bq)).
    + exact (root_cv p (τbounded_terminate k _ bp)).
    + exact (root_cv q (τbounded_terminate k _ bq)).
Qed.

Lemma trace_inv_dead (q : P) (s : trace A) (μ : A) :
  q ⇓ᶜᵒ s → (∀ q', ¬ q ⟹ᶜᵒ[s ++ [μ]] q') → q ⇓ᶜᵒ s ++ [μ] ∧ ∀ q', ¬ q ⟹ᶜᵒ[s ++ [μ]] q'.
Proof.
  intros hq hn. split; [| exact hn].
  apply (cocnv_snoc q s μ hq). intros r w. exfalso. exact (hn r w).
Qed.

Lemma inv_step_node (k : nat) (p0 q0 : P) (R : list pair_states) (x : pair_states) (p q : P) (s : trace A) (μ : A) :
  certified k p0 q0 R = true → graph_closed R → x ∈ R → in_atoms (explored x) μ →
  approx_after p s x.1 → approx_after q s x.2 → p ⇓ᶜᵒ s → q ⇓ᶜᵒ s →
  ∃ π, trace_inv (sws π p) (sws π q) R (sws_trace π (s ++ [μ])).
Proof.
  intros hc hgc mx hv hX hY hp hq. destruct (hgc x mx) as [cl1 cl2].
  destruct (decide (μ ∈ next_list (explored x) x.2)) as [m | m].
  2: { exists []. cbn [sws sws_trace]. right; left. apply trace_inv_dead; [exact hq |].
       exact (approx_no_cotrace (explored x) q s x.2 μ hY cl2 hv m). }
  destruct (certified_local k p0 q0 R x hc mx) as [_ hch].
  specialize (hch μ m). unfold child_ok in hch. rewrite orb_comm in hch. apply orb_true_iff in hch as [h | h].
  - exists []. cbn [sws sws_trace]. left. destruct (div_set_spec k _ h) as (r & mr & hn). intros hc'.
    apply ext_spec in mr as (y1 & m1 & μ' & duo & l).
    destruct (proj2 hX y1 m1) as (p1 & w1 & hb1).
    destruct (sbisim_step y1 p1 (ActExt μ') r (sbisim_sym _ _ hb1) l) as (r0 & l0 & hr).
    apply hn. apply (sbisim_terminate r0 r (sbisim_sym _ _ hr)).
    apply (cocnv_cowt_s_terminate p r0 (s ++ [μ]) hc').
    exact (cowt_push_right p p1 r0 μ s w1 (lts_to_cowt duo l0)).
  - rewrite child_pair_unfold in h.
    destruct (τbounded k (ext x.1 μ)) eqn:bp, (τbounded k (ext x.2 μ)) eqn:bq; simpl in h; try discriminate.
    destruct (approx_child k p s x.1 μ hX cl1 bp hp) as [hX' hp'].
    destruct (approx_child k q s x.2 μ hY cl2 bq hq) as [hY' hq'].
    rewrite in_graph_set in h. exact (in_graph_inv _ R p q _ h hX' hY' hp' hq').
Qed.

Lemma co_conditions_of_inv (k : nat) (p0 q0 : P) (R : list pair_states) (p q : P) (s : trace A) :
  certified k p0 q0 R = true → trace_inv p q R s → co_conditions p q s.
Proof.
  intros hc [hn | [[hq hd] | (x & mx & hX & hY & hp & hq)]].
  - rewrite <- (app_nil_r s). exact (co_conditions_pdiv p q s [] hn).
  - split; [intros _; exact hq |]. intros q' _ w. exfalso. exact (hd q' w).
  - split; [intros _; exact hq |]. intros q' _ w st.
    destruct (certified_local k p0 q0 R x hc mx) as [hl _].
    exact (local_ok_spec p q s x hl hX hY q' w st).
Qed.

Lemma in_graph_mono (c : pair_states) (R R' : list pair_states) :
  (∀ y, y ∈ R → y ∈ R') → in_graph c R = true → in_graph c R' = true.
Proof.
  intros hR h. destruct (in_graph_spec c R h) as (y & my & e1 & e2).
  apply existsb_exists. exists (canon y). split; [apply list_elem_of_In, list_elem_of_fmap_2, hR, my |].
  unfold same_pair. apply andb_true_iff. split; apply same_set_spec; assumption.
Qed.

Lemma bfs_tr_mono (k : nat) : ∀ m seen visited work e, e ∈ visited → e ∈ bfs_tr k m seen visited work.
Proof.
  induction m as [| m IH]; intros seen visited work e me; simpl; [exact me |].
  destruct work as [| y work']; [exact me |].
  destruct (idx_mem (canon y.1) seen); apply IH; [exact me | by apply list_elem_of_further].
Qed.

Lemma map_fst_mono (k m : nat) (seen : gmap (N * N) (list pair_states)) (visited work : list (pair_states * list A)) :
  ∀ y, y ∈ map fst visited → y ∈ map fst (bfs_tr k m seen visited work).
Proof.
  intros y my. apply list_elem_of_fmap in my as (z & -> & mz).
  apply list_elem_of_fmap. exists z. split; [reflexivity | apply bfs_tr_mono, mz].
Qed.

End Graph.
(* end hide *)
