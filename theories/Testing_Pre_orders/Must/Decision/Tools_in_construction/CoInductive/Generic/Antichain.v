(* begin hide *)
From Stdlib Require Import Lia.
From stdpp Require Import base countable gmap list sets numbers.
From Coinduction Require Import all.
From TestingTheory Require Import ActTau gLts SyncActions Termination Subset_Act InListPropHelper
  coWeakTransition coConvergence coFiniteImage DefinitionASrel Coin_tower_co
  Decision.Tools_in_construction.Inductive.Generic.Helpers Decision.Tools_in_construction.Inductive.Generic.Bisim
  Decision.Tools_in_construction.Inductive.Generic.Interface Decision.Tools_in_construction.Inductive.Generic.Sets Decision.Tools_in_construction.Inductive.Generic.Transport
  Decision.Tools_in_construction.Inductive.Generic.Graph Decision.Tools_in_construction.Inductive.Generic.Swaps Decision.Tools_in_construction.Inductive.Generic.Adequacy
  Decision.Tools_in_construction.Inductive.Generic.Verdict Decision.Tools_in_construction.CoInductive.Generic.Certificate.
Import ListNotations.

Section Antichain.

Context `{TS : TraceSearchLang P A Atom PreAct T}.

(** Subsumption of nodes: a node with fewer states of [p] and more states of [q] is harder. *)

Definition incl_b (X Y : list P) : bool := forallb (λ a, bool_decide (a ∈ Y)) X.

Lemma incl_b_spec (X Y : list P) : incl_b X Y = true → ∀ z, z ∈ X → z ∈ Y.
Proof.
  unfold incl_b. rewrite forallb_forall. intros h z m.
  exact (bool_decide_eq_true_1 _ (h z (proj1 (list_elem_of_In _ _) m))).
Qed.

Definition subsumes (cy cc : pair_states) : bool := if incl_b cy.1 cc.1 then incl_b cc.2 cy.2 else false.

Fixpoint lexistsb {X : Type} (f : X → bool) (l : list X) : bool :=
  match l with
  | [] => false
  | x :: l => if f x then true else lexistsb f l
  end.

Lemma lexistsb_eq {X : Type} (f : X → bool) (l : list X) : lexistsb f l = existsb f l.
Proof. induction l as [| x l IH]; simpl; [reflexivity |]. destruct (f x); [reflexivity | exact IH]. Qed.

Definition key_le (ky kc : N * N) : bool := if N.leb ky.1 kc.1 then N.leb kc.2 ky.2 else false.

Definition covered (cc : pair_states) (I : gmap (N * N) (list pair_states)) (L : list ((N * N) * pair_states)) : bool :=
  if idx_mem cc I then true else let kc := node_key cc in lexistsb (λ ky, if key_le ky.1 kc then subsumes ky.2 cc else false) L.

Definition L_ok (R : list pair_states) (L : list ((N * N) * pair_states)) : Prop :=
  ∀ ky, ky ∈ L → ∃ y, y ∈ R ∧ ky.2 = canon y.

Lemma covered_spec (c : pair_states) (R : list pair_states) (L : list ((N * N) * pair_states)) :
  L_ok R L → covered (canon c) (canon_index R) L = true →
  ∃ y, y ∈ R ∧ (∀ z, z ∈ (canon y).1 → z ∈ (canon c).1) ∧ (∀ z, z ∈ (canon c).2 → z ∈ (canon y).2).
Proof.
  intros hL. unfold covered. intros [h | h]%orb_true_iff.
  - rewrite in_graph_set in h. destruct (in_graph_spec _ _ h) as (y & my & e1 & e2).
    exists y. split_and!; [exact my | intros z m; apply e1, m | intros z m; apply e2, m].
  - cbv zeta in h. rewrite lexistsb_eq in h. apply existsb_exists in h as (ky & mky & h). apply andb_true_iff in h as [_ h].
    destruct (hL ky (proj2 (list_elem_of_In _ _) mky)) as (y & my & ey). rewrite ey in h.
    unfold subsumes in h. apply andb_true_iff in h as [h1 h2].
    exists y. split_and!; [exact my | exact (incl_b_spec _ _ h1) | exact (incl_b_spec _ _ h2)].
Qed.

(** Exploration up to subsumption. *)

Fixpoint bfs_ac (k m : nat) (I : gmap (N * N) (list pair_states)) (L : list ((N * N) * pair_states))
  (visited work : list (pair_states * list A)) : list (pair_states * list A) * list ((N * N) * pair_states) :=
  match m with
  | 0 => (visited, L)
  | S m =>
      match work with
      | [] => (visited, L)
      | e :: work' =>
          let c := canon e.1 in
          if covered c I L then bfs_ac k m I L visited work'
          else let kc := node_key c in
               bfs_ac k m (idx_add c I) ((kc, c) :: filter (λ ky, negb (if key_le kc ky.1 then subsumes c ky.2 else false)) L)
                 (e :: visited) (work' ++ children_tr k e)
      end
  end.

Definition ac_run (m k : nat) (p q : P) : list (pair_states * list A) * list ((N * N) * pair_states) :=
  match root_pair k p q with
  | Some c => bfs_ac k m ∅ [] [] [(c, [])]
  | None => ([], [])
  end.

Definition graph_ac (m k : nat) (p q : P) : list pair_states := map fst (ac_run m k p q).1.

Lemma bfs_ac_inv (k : nat) (Q : pair_states → Prop) (hQ : ∀ x c, Q x → c ∈ children k x → Q c) :
  ∀ m I L visited work, (∀ e, e ∈ visited → Q e.1) → (∀ e, e ∈ work → Q e.1) →
  ∀ e, e ∈ (bfs_ac k m I L visited work).1 → Q e.1.
Proof.
  induction m as [| m IH]; intros I L visited work hv hw x hx; simpl in hx; [exact (hv x hx) |].
  destruct work as [| y work']; [exact (hv x hx) |].
  destruct (covered (canon y.1) I L).
  - apply (IH I L visited work' hv); [intros z hz; apply hw, list_elem_of_further, hz | exact hx].
  - refine (IH _ _ (y :: visited) (work' ++ children_tr k y) _ _ x hx).
    + intros z [-> | hz]%elem_of_cons; [apply hw, list_elem_of_here | exact (hv z hz)].
    + intros z [hz | hz]%elem_of_app; [apply hw, list_elem_of_further, hz |].
      apply (hQ y.1 z.1); [apply hw, list_elem_of_here | exact (children_tr_fst k y z hz)].
Qed.

Lemma bfs_ac_L (k : nat) : ∀ m I L visited work, (∀ ky, ky ∈ L → ∃ e, e ∈ visited ∧ ky.2 = canon e.1) →
  ∀ ky, ky ∈ (bfs_ac k m I L visited work).2 → ∃ e, e ∈ (bfs_ac k m I L visited work).1 ∧ ky.2 = canon e.1.
Proof.
  induction m as [| m IH]; intros I L visited work hL ky mky; simpl in mky |- *; [exact (hL ky mky) |].
  revert mky. destruct work as [| y work']; [intros mky; exact (hL ky mky) |].
  destruct (covered (canon y.1) I L); intros mky; [exact (IH _ _ _ _ hL ky mky) |].
  apply (IH _ _ _ _); [| exact mky]. intros ky' [-> | m']%elem_of_cons.
  - exists y. split; [apply list_elem_of_here | reflexivity].
  - apply list_elem_of_filter in m' as [_ m']. destruct (hL ky' m') as (e & me & ee).
    exists e. split; [by apply list_elem_of_further | exact ee].
Qed.

Lemma ac_L_ok (m k : nat) (p q : P) : L_ok (graph_ac m k p q) (ac_run m k p q).2.
Proof.
  unfold graph_ac, ac_run. destruct (root_pair k p q) as [c |]; [| intros ky mky; inversion mky].
  intros ky mky. destruct (bfs_ac_L k m ∅ [] [] [(c, [])] ltac:(intros ky' m'; inversion m') ky mky) as (e & me & ee).
  exists e.1. split; [apply list_elem_of_fmap_2, me | exact ee].
Qed.

Lemma graph_ac_inv (m k : nat) (p q : P) (Q : pair_states → Prop) :
  (∀ x c, Q x → c ∈ children k x → Q c) → (∀ c, root_pair k p q = Some c → Q c) →
  ∀ x, x ∈ graph_ac m k p q → Q x.
Proof.
  intros hQ hr x hx. unfold graph_ac, ac_run in hx.
  destruct (root_pair k p q) as [c |] eqn:e; [| inversion hx].
  apply list_elem_of_fmap in hx as (e' & -> & he).
  apply (bfs_ac_inv k Q hQ m ∅ [] [] [(c, [])]); [intros z hz; inversion hz | | exact he].
  intros z hz. apply list_elem_of_singleton in hz as ->. exact (hr c eq_refl).
Qed.

Lemma graph_ac_props (m k : nat) (p q : P) :
  ∀ x, x ∈ graph_ac m k p q → (tau_closed x.1 ∧ tau_closed x.2) ∧ (∀ r, r ∈ x.1 → r ⤓) ∧ (∀ r, r ∈ x.2 → r ⤓).
Proof.
  apply graph_ac_inv.
  - intros y c _ mc. unfold children in mc. apply list_elem_of_omap in mc as (μ & _ & h). rewrite child_pair_unfold in h.
    destruct (τbounded k (ext y.1 μ)) eqn:b1, (τbounded k (ext y.2 μ)) eqn:b2; simpl in h; try discriminate.
    injection h as <-. simpl. split_and!; first [apply τclose_closed | apply τclose_terminate]; assumption.
  - intros c h. rewrite root_pair_unfold in h.
    destruct (τbounded k [p]) eqn:b1, (τbounded k [q]) eqn:b2; simpl in h; try discriminate.
    injection h as <-. simpl. split_and!; first [apply τclose_closed | apply τclose_terminate]; assumption.
Qed.

(** The certificate up to subsumption. *)

Definition child_ok_ac (k : nat) (I : gmap (N * N) (list pair_states)) (L : list ((N * N) * pair_states)) (x : pair_states) (μ : A) : bool :=
  if match child_pair k x μ with
     | Some c => covered (canon c) I L
     | None => false
     end then true else div_set k (ext x.1 μ).

Definition root_ok_ac (k : nat) (p q : P) (I : gmap (N * N) (list pair_states)) (L : list ((N * N) * pair_states)) : bool :=
  if div_set k [p] then true else
  match root_pair k p q with
  | Some c => covered (canon c) I L
  | None => false
  end.

Definition certified_ac_in (k : nat) (p q : P) (R : list pair_states) (I : gmap (N * N) (list pair_states))
  (L : list ((N * N) * pair_states)) : bool :=
  if root_ok_ac k p q I L then forallb (λ x, if local_ok x then forallb (child_ok_ac k I L x) (next_list (explored x) x.2) else false) R else false.

Definition certify_ac (m k : nat) (p q : P) : bool :=
  let r := ac_run m k p q in
  let R := map fst r.1 in certified_ac_in k p q R (canon_index R) r.2.

Lemma certified_ac_local (k : nat) (p q : P) (R : list pair_states) I L (x : pair_states) :
  certified_ac_in k p q R I L = true → x ∈ R →
  local_ok x = true ∧ ∀ μ, μ ∈ next_list (explored x) x.2 → child_ok_ac k I L x μ = true.
Proof.
  intros h m. unfold certified_ac_in in h. apply andb_true_iff in h as [_ h]. rewrite forallb_forall in h.
  specialize (h x (proj1 (list_elem_of_In _ _) m)). apply andb_true_iff in h as [h1 h2].
  split; [exact h1 |]. intros μ mμ. rewrite forallb_forall in h2. exact (h2 μ (proj1 (list_elem_of_In _ _) mμ)).
Qed.

Definition cover_set (π : list (Atom * Atom)) (X : gset P) (N : list P) : Prop :=
  ∀ r', r' ∈ N → ∃ r t, r ∈ X ∧ r ⟹ᶜᵒ t ∧ sbisim (sws π t) r'.

Definition cert_rel_ac (R : list pair_states) (X Y : gset P) : Prop :=
  (∃ r, r ∈ X ∧ ¬ r ⤓) ∨ (∀ q, q ∈ Y → False) ∨
  ∃ x π, x ∈ R ∧ cover_set π X x.1 ∧ sub_set π Y x.2.

Lemma cover_set_fix (x : pair_states) (σ π : list (Atom * Atom)) (X : gset P) :
  fixes σ (node_atoms x) → cover_set π X x.1 → cover_set (σ ++ π) X x.1.
Proof.
  intros hσ h r' m'. destruct (h r' m') as (r & t & m & w & hb). exists r, t. split_and!; [exact m | exact w |].
  rewrite sws_app, <- (sws_fix x σ r' hσ (or_introl m')). apply sbisim_sws, hb.
Qed.

Lemma cover_set_child (k : nat) (π : list (Atom * Atom)) (X X' : gset P) (N : list P) (μ : A) :
  cover_set π X N → (∀ p', p' ∈ X' ↔ ∃ p, p ∈ X ∧ p ⟹ᶜᵒ{μ} p') → cover_set π X' (τclose k (ext N (sws_act π μ))).
Proof.
  intros h2 hX' t mt. destruct (τclose_sound k _ t mt) as (n2 & mn2 & w2). apply ext_spec in mn2 as (n1 & mn1 & μ' & duo & l).
  destruct (h2 n1 mn1) as (p & t0 & mp & w0 & hb0).
  destruct (sbisim_step _ _ (ActExt μ') n2 (sbisim_sym _ _ hb0) l) as (u & lu & hu).
  destruct (sbisim_cowt _ _ [] t hu w2) as (v & wv & hv).
  assert (w : sws π p ⟹ᶜᵒ{sws_act π μ} v).
  { apply (cowt_push_nil_left (cowt_sws_nil π p t0 w0)). exact (cowt_push_nil_right _ _ _ _ (lts_to_cowt duo lu) wv). }
  exists (sws (rev π) v), (sws (rev π) v). split_and!.
  - apply hX'. exists p. split; [exact mp | exact (cowt_sws_one_back π p v μ w)].
  - apply cowt_nil.
  - rewrite <- (rev_involutive π) at 1. rewrite sws_rev_invol. exact (sbisim_sym _ _ hv).
Qed.

Lemma cover_set_incl (π π1 π2 : list (Atom * Atom)) (X : gset P) (N M : list P) :
  cover_set π X N → (∀ z, z ∈ ts_norm <$> (sws π2 <$> M) → z ∈ ts_norm <$> (sws π1 <$> N)) →
  cover_set (rev π2 ++ π1 ++ π) X M.
Proof.
  intros h2 e n' mn'.
  assert (hz : ts_norm (sws π2 n') ∈ ts_norm <$> (sws π1 <$> N)) by (apply e, list_elem_of_fmap_2, list_elem_of_fmap_2, mn').
  apply list_elem_of_fmap in hz as (z & ez & mz). apply list_elem_of_fmap in mz as (n & -> & mn).
  destruct (h2 n mn) as (r & t & m & w & hb). exists r, t. split_and!; [exact m | exact w |].
  rewrite !sws_app. rewrite <- (sws_rev_invol π2 n').
  apply sbisim_sws. exact (sbisim_trans _ _ _ (sbisim_sws π1 _ _ hb) (norm_bisim _ _ (eq_sym ez))).
Qed.

Lemma sub_set_incl (π π1 π2 : list (Atom * Atom)) (Y : gset P) (N M : list P) :
  sub_set π Y N → (∀ z, z ∈ ts_norm <$> (sws π1 <$> N) → z ∈ ts_norm <$> (sws π2 <$> M)) →
  sub_set (rev π2 ++ π1 ++ π) Y M.
Proof.
  intros h e r m. destruct (h r m) as (n & mn & hb).
  assert (hz : ts_norm (sws π1 n) ∈ ts_norm <$> (sws π2 <$> M)) by (apply e, list_elem_of_fmap_2, list_elem_of_fmap_2, mn).
  apply list_elem_of_fmap in hz as (z & ez & mz). apply list_elem_of_fmap in mz as (n' & -> & mn').
  exists n'. split; [exact mn' |]. rewrite !sws_app. rewrite <- (sws_rev_invol π2 n').
  apply sbisim_sws. exact (sbisim_trans _ _ _ (sbisim_sws π1 _ _ hb) (norm_bisim _ _ ez)).
Qed.

Lemma cert_postfix_ac (k : nat) (p0 q0 : P) (R : list pair_states) (L : list ((N * N) * pair_states)) :
  certified_ac_in k p0 q0 R (canon_index R) L = true → L_ok R L → graph_closed R → graph_term R →
  ∀ X Y, cert_rel_ac R X Y → copre_co_ ts_Γ (cert_rel_ac R) X Y.
Proof.
  intros hc hL hgc hgt X Y [(r & mr & hr) | [hY | (x & π & mx & hX & hY)]].
  - constructor.
    + intros Y' _. left. exists r. split; assumption.
    + intros hX. exfalso. exact (hr (hX r mr)).
    + intros μ X' Y' hX. exfalso. exact (hr (cocnv_terminate r _ (hX r mr))).
    + intros hX. exfalso. exact (hr (hX r mr)).
  - constructor.
    + intros Y' hY'. right; left. intros q' mq'. destruct (hY' q' mq') as (q & mq & _). exact (hY q mq).
    + intros _ q mq. exfalso. exact (hY q mq).
    + intros μ X' Y' _ hY' _. right; left. intros q' mq'. destruct (hY' q' mq') as (q & mq & _). exact (hY q mq).
    + intros _ q mq. exfalso. exact (hY q mq).
  - destruct (hgc x mx) as [cl1 cl2]. destruct (hgt x mx) as [t1 t2].
    destruct (certified_ac_local k p0 q0 R _ _ x hc mx) as [hloc hch].
    constructor.
    + intros Y' hY'. right; right. exists x, π. split_and!; [exact mx | exact hX |].
      intros r' mr'. destruct (hY' r' mr') as (q & mq & w). destruct (hY q mq) as (n & mn & hb).
      destruct (sbisim_cowt _ _ _ _ hb (cowt_sws_nil π q r' w)) as (n' & wn & hb').
      exists n'. split; [exact (closed_nil _ n n' cl2 mn wn) | exact hb'].
    + intros hXt q mq st. destruct (hY q mq) as (n & mn & hb).
      assert (stn : n ↛) by exact (sbisim_stable _ _ hb (refuses_sws π q st)).
      unfold local_ok in hloc. rewrite forallb_forall in hloc.
      assert (mns : n ∈ stable_list x.2) by (unfold stable_list; apply list_elem_of_filter; split; [apply stable_b_spec, stn | exact mn]).
      specialize (hloc n (proj1 (list_elem_of_In _ _) mns)). apply existsb_exists in hloc as (x' & mx' & hd).
      destruct (coR_dichotomy x' n) as [sub |]; [| discriminate].
      apply list_elem_of_In in mx'. unfold stable_list in mx'. apply list_elem_of_filter in mx' as [stx%stable_b_spec mx1].
      destruct (hX x' mx1) as (r & t & mr & w & hbt).
      exists r. split; [exact mr |]. exists t. split_and!; [exact w | |].
      * apply (refuses_sws_back π). exact (sbisim_stable _ _ (sbisim_sym _ _ hbt) stx).
      * intros z hz. apply (coR_sws_back π). apply (sbisim_coR ts_Γ n (sws π q) _ (sbisim_sym _ _ hb)). apply sub.
        apply (sbisim_coR ts_Γ (sws π t) x' _ hbt). apply coR_sws, hz.
    + intros μ X' Y' hXμ hY' hX'.
      destruct (ext x.2 (sws_act π μ)) as [| e2 l2] eqn:he.
      * right; left. intros q' mq'. destruct (hY' q' mq') as (q & mq & w). destruct (hY q mq) as (n & mn & hb).
        destruct (sbisim_cowt _ _ _ _ hb (cowt_sws_one π q q' μ w)) as (n' & wn & _).
        destruct (cowt_decomp_one wn) as (n1 & n2 & μ' & w1 & duo & l & _).
        assert (m2 : n2 ∈ ext x.2 (sws_act π μ))
          by (apply ext_spec; exists n1; split; [exact (closed_nil _ n n1 cl2 mn w1) |]; exists μ'; split; assumption).
        rewrite he in m2. inversion m2.
      * assert (m2 : e2 ∈ ext x.2 (sws_act π μ)) by (rewrite he; apply list_elem_of_here).
        apply ext_spec in m2 as (r1 & m1 & μ' & duo & l).
        pose proof (node_arity_spec x r1 m1) as har. pose proof (ts_arity_spec r1 (sws_act π μ) μ' e2 duo l) as har'.
        destruct (normalise x _ (sws_act π μ) (le_n _) ltac:(lia)) as (σ & hσ & hin).
        rewrite <- sws_act_app in hin.
        pose proof (cover_set_fix x σ π X hσ hX) as hX2. pose proof (sub_set_fix x σ π Y hσ hY) as hY2.
        destruct (decide (sws_act (σ ++ π) μ ∈ next_list (explored x) x.2)) as [mμ | nμ].
        2: { right; left. intros q' mq'. destruct (hY' q' mq') as (q & mq & w). destruct (hY2 q mq) as (n & mn & hb).
             destruct (sbisim_cowt _ _ _ _ hb (cowt_sws_one (σ ++ π) q q' μ w)) as (n' & wn & _).
             destruct (cowt_decomp_one wn) as (n1 & n2 & μ'' & w1 & duo' & l' & _).
             apply nμ. exact (next_list_spec (explored x) x.2 n1 _ μ'' n2 (closed_nil _ n n1 cl2 mn w1) duo' l' hin). }
        specialize (hch _ mμ). unfold child_ok_ac in hch. apply orb_true_iff in hch as [hc2 | hdiv].
        -- destruct (child_pair k x (sws_act (σ ++ π) μ)) as [c |] eqn:ec; [| discriminate].
           rewrite child_pair_unfold in ec.
           destruct (τbounded k (ext x.1 (sws_act (σ ++ π) μ))) eqn:b1, (τbounded k (ext x.2 (sws_act (σ ++ π) μ))) eqn:b2;
             simpl in ec; try discriminate.
           injection ec as <-.
           destruct (covered_spec _ _ _ hL hc2) as (y & my & e1 & e2').
           unfold canon, norm_pair, sw_pair in e1, e2'. simpl in e1, e2'.
           right; right.
           exists y, (rev (canon_sw y) ++ canon_sw (τclose k (ext x.1 (sws_act (σ ++ π) μ)), τclose k (ext x.2 (sws_act (σ ++ π) μ))) ++ σ ++ π).
           split_and!; [exact my | |].
           ++ apply (cover_set_incl (σ ++ π) _ _ X' (τclose k (ext x.1 (sws_act (σ ++ π) μ)))); [| exact e1].
              exact (cover_set_child k (σ ++ π) X X' x.1 μ hX2 hX').
           ++ apply (sub_set_incl (σ ++ π) _ _ Y' (τclose k (ext x.2 (sws_act (σ ++ π) μ)))); [| exact e2'].
              exact (sub_set_child k (σ ++ π) Y Y' x.2 μ hY2 cl2 b2 hY').
        -- left. destruct (div_set_spec k _ hdiv) as (r2 & mr2 & hr2). apply ext_spec in mr2 as (n1 & mn1 & μ'' & duo' & l').
           destruct (hX2 n1 mn1) as (r & t & mr & w & hbt).
           destruct (sbisim_step _ _ (ActExt μ'') r2 (sbisim_sym _ _ hbt) l') as (u & lu & hu).
           assert (wu : sws (σ ++ π) r ⟹ᶜᵒ{sws_act (σ ++ π) μ} u)
             by exact (cowt_push_nil_left (cowt_sws_nil (σ ++ π) r t w) (lts_to_cowt duo' lu)).
           exists (sws (rev (σ ++ π)) u). split.
           ++ apply hX'. exists r. split; [exact mr | exact (cowt_sws_one_back (σ ++ π) r u μ wu)].
           ++ intros ht. apply hr2. apply (sbisim_terminate u r2 (sbisim_sym _ _ hu)).
              rewrite <- (sws_rev_invol (rev (σ ++ π)) u), rev_involutive. apply terminate_sws, ht.
    + intros _ q mq. destruct (hY q mq) as (n & mn & hb). apply (terminate_sws_back π).
      exact (sbisim_terminate _ _ (sbisim_sym _ _ hb) (t2 n mn)).
Qed.

Lemma cert_root_ac (m k : nat) (p q : P) : certify_ac m k p q = true → cert_rel_ac (graph_ac m k p q) {[ p ]} {[ q ]}.
Proof.
  intros hc. pose proof (ac_L_ok m k p q) as hL. unfold certify_ac, certified_ac_in in hc. cbv zeta in hc.
  fold (graph_ac m k p q) in hc. apply andb_true_iff in hc as [hr _].
  unfold root_ok_ac in hr. apply orb_true_iff in hr as [hd | hin].
  - left. destruct (div_set_spec k _ hd) as (r & ->%list_elem_of_singleton & hn). exists p. split; [set_solver | exact hn].
  - right; right. destruct (root_pair k p q) as [c |] eqn:er; [| discriminate].
    rewrite root_pair_unfold in er. destruct (τbounded k [p]) eqn:bp, (τbounded k [q]) eqn:bq; simpl in er; try discriminate.
    injection er as <-.
    destruct (covered_spec _ _ _ hL hin) as (y & my & e1 & e2). unfold canon, norm_pair, sw_pair in e1, e2. simpl in e1, e2.
    exists y, (rev (canon_sw y) ++ canon_sw (τclose k [p], τclose k [q]) ++ []). split_and!; [exact my | |].
    + apply (cover_set_incl [] _ _ {[ p ]} (τclose k [p])); [| exact e1].
      intros r' m'. destruct (τclose_sound k [p] r' m') as (x0 & ->%list_elem_of_singleton & w).
      exists p, r'. split_and!; [set_solver | exact w | apply sbisim_refl].
    + apply (sub_set_incl [] _ _ {[ q ]} (τclose k [q])); [| exact e2].
      intros r ->%elem_of_singleton. exists q. split; [apply τclose_incl, list_elem_of_here | apply sbisim_refl].
Qed.

Theorem certify_ac_spec (m k : nat) (p q : P) : certify_ac m k p q = true → p ≼꜀ₒ₋ₐₛ[ ts_Γ ] q.
Proof.
  intros hc. apply (proj1 (copre_co_singleton ts_Γ p q)).
  pose proof (cert_root_ac m k p q hc) as hroot. revert hroot.
  generalize ({[ p ]} : gset P) ({[ q ]} : gset P). unfold copre_co. coinduction RR CIH. intros X Y h.
  assert (hgc : graph_closed (graph_ac m k p q)) by (intros x mx; exact (proj1 (graph_ac_props m k p q x mx))).
  assert (hgt : graph_term (graph_ac m k p q)) by (intros x mx; exact (proj2 (graph_ac_props m k p q x mx))).
  assert (hc' : certified_ac_in k p q (graph_ac m k p q) (canon_index (graph_ac m k p q)) (ac_run m k p q).2 = true) by exact hc.
  destruct (cert_postfix_ac k p q _ _ hc' (ac_L_ok m k p q) hgc hgt X Y h) as [f1 f2 f3 f4].
  constructor.
  - intros Y' hY'. apply CIH, (f1 Y' hY').
  - exact f2.
  - intros μ X' Y' a b c. apply CIH, (f3 μ X' Y' a b c).
  - exact f4.
Qed.

(** The verdict: the certificate up to subsumption first, the exact procedure otherwise. *)

Definition verdict_ac (m k n : nat) (p q : P) : result :=
  if certify_ac m k p q then R_holds else verdict m k n p q.

Theorem verdict_ac_holds (m k n : nat) (p q : P) : verdict_ac m k n p q = R_holds → p ≼꜀ₒ₋ₐₛ[ ts_Γ ] q.
Proof.
  unfold verdict_ac. destruct (certify_ac m k p q) eqn:hc; [intros _; exact (certify_ac_spec m k p q hc) |].
  intros h. exact (verdict_holds_co m k n p q h).
Qed.

Theorem verdict_ac_fails (m k n : nat) (p q : P) (s : trace A) (t : T) :
  verdict_ac m k n p q = R_fails s t → ts_must p t ∧ ¬ ts_must q t.
Proof.
  unfold verdict_ac. destruct (certify_ac m k p q); [discriminate |]. apply verdict_fails.
Qed.

Theorem verdict_ac_complete (m k n : nat) (p q : P) :
  adequate m k p q = true → verdict_ac m k n p q = R_holds ∨ ∃ s t, verdict_ac m k n p q = R_fails s t.
Proof.
  intros ha. unfold verdict_ac. destruct (certify_ac m k p q); [left; reflexivity |]. exact (verdict_complete m k n p q ha).
Qed.

(** The exact procedure first, the certificate up to subsumption when it does not answer. *)

Definition verdict_xa (m k n : nat) (p q : P) : result :=
  match verdict m k n p q with
  | R_unknown => if certify_ac m k p q then R_holds else R_unknown
  | r => r
  end.

Theorem verdict_xa_holds (m k n : nat) (p q : P) : verdict_xa m k n p q = R_holds → p ≼꜀ₒ₋ₐₛ[ ts_Γ ] q.
Proof.
  unfold verdict_xa. destruct (verdict m k n p q) eqn:hv; intros h.
  - exact (verdict_holds_co m k n p q hv).
  - discriminate.
  - destruct (certify_ac m k p q) eqn:hc; [exact (certify_ac_spec m k p q hc) | discriminate].
Qed.

Theorem verdict_xa_fails (m k n : nat) (p q : P) (s : trace A) (t : T) :
  verdict_xa m k n p q = R_fails s t → ts_must p t ∧ ¬ ts_must q t.
Proof.
  unfold verdict_xa. destruct (verdict m k n p q) eqn:hv; intros h; try discriminate.
  - injection h as -> ->. exact (verdict_fails m k n p q s t hv).
  - destruct (certify_ac m k p q); discriminate.
Qed.

Theorem verdict_xa_complete (m k n : nat) (p q : P) :
  adequate m k p q = true → verdict_xa m k n p q = R_holds ∨ ∃ s t, verdict_xa m k n p q = R_fails s t.
Proof.
  intros ha. unfold verdict_xa. destruct (verdict_complete m k n p q ha) as [-> | (s & t & ->)]; [left | right; eauto]; reflexivity.
Qed.

End Antichain.
(* end hide *)
