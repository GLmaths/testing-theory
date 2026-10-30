(* begin hide *)
From Stdlib Require Import Lia.
From stdpp Require Import base countable gmap list sets numbers.
From Coinduction Require Import all.
From TestingTheory Require Import ActTau gLts SyncActions Termination Subset_Act InListPropHelper
  coWeakTransition coConvergence coFiniteImage DefinitionASrel Coin_tower_co
  Decision.Tools_in_construction.Inductive.Generic.Helpers Decision.Tools_in_construction.Inductive.Generic.Bisim
  Decision.Tools_in_construction.Inductive.Generic.Interface Decision.Tools_in_construction.Inductive.Generic.Sets Decision.Tools_in_construction.Inductive.Generic.Transport
  Decision.Tools_in_construction.Inductive.Generic.Graph Decision.Tools_in_construction.Inductive.Generic.Swaps Decision.Tools_in_construction.Inductive.Generic.Adequacy
  Decision.Tools_in_construction.Inductive.Generic.Verdict.
Import ListNotations.

Section Certificate.

Context `{TS : TraceSearchLang P A Atom PreAct T}.

(** The certificate as a post-fixpoint of the co-inductive preorder. *)

Definition match_set (π : list (Atom * Atom)) (X : gset P) (N : list P) : Prop :=
  (∀ r, r ∈ X → ∃ r', r' ∈ N ∧ sbisim (sws π r) r') ∧
  (∀ r', r' ∈ N → ∃ r t, r ∈ X ∧ r ⟹ᶜᵒ t ∧ sbisim (sws π t) r').

Definition sub_set (π : list (Atom * Atom)) (Y : gset P) (N : list P) : Prop :=
  ∀ r, r ∈ Y → ∃ r', r' ∈ N ∧ sbisim (sws π r) r'.

Definition graph_term (R : list pair_states) : Prop := ∀ x, x ∈ R → (∀ r, r ∈ x.1 → r ⤓) ∧ (∀ r, r ∈ x.2 → r ⤓).

Definition cert_rel (R : list pair_states) (X Y : gset P) : Prop :=
  (∃ r, r ∈ X ∧ ¬ r ⤓) ∨ (∀ q, q ∈ Y → False) ∨
  ∃ x π, x ∈ R ∧ match_set π X x.1 ∧ sub_set π Y x.2.

Fixpoint sws_pre (π : list (Atom * Atom)) (x : PreAct) : PreAct :=
  match π with
  | [] => x
  | (a, b) :: π => ts_swap_pre a b (sws_pre π x)
  end.

Lemma coR_sws (π : list (Atom * Atom)) (p : P) (x : PreAct) :
  x ∈ ⌈ ts_Γ ⌉ (coR p) → sws_pre π x ∈ ⌈ ts_Γ ⌉ (coR (sws π p)).
Proof.
  induction π as [| [a b] π IH]; simpl; intros h; [exact h |]. apply coR_swap_inv. rewrite ts_swap_pre_invol. exact (IH h).
Qed.

Lemma coR_sws_back (π : list (Atom * Atom)) (p : P) (x : PreAct) :
  sws_pre π x ∈ ⌈ ts_Γ ⌉ (coR (sws π p)) → x ∈ ⌈ ts_Γ ⌉ (coR p).
Proof.
  induction π as [| [a b] π IH]; simpl; intros h; [exact h |]. apply IH.
  pose proof (coR_swap a b _ _ h) as h'. rewrite ts_swap_pre_invol in h'. exact h'.
Qed.

Lemma refuses_sws (π : list (Atom * Atom)) (p : P) : p ↛ → sws π p ↛.
Proof. induction π as [| [a b] π IH]; simpl; intros h; [exact h | apply refuses_swap, IH, h]. Qed.

Lemma terminate_sws (π : list (Atom * Atom)) (p : P) : p ⤓ → (sws π p) ⤓.
Proof. induction π as [| [a b] π IH]; simpl; intros h; [exact h | apply terminate_swap, IH, h]. Qed.

Lemma refuses_sws_back (π : list (Atom * Atom)) (p : P) : sws π p ↛ → p ↛.
Proof. intros h. rewrite <- (sws_rev_invol π p). apply refuses_sws, h. Qed.

Lemma terminate_sws_back (π : list (Atom * Atom)) (p : P) : (sws π p) ⤓ → p ⤓.
Proof. intros h. rewrite <- (sws_rev_invol π p). apply terminate_sws, h. Qed.

Lemma sws_trace_single (π : list (Atom * Atom)) (μ : A) : sws_trace π [μ] = [sws_act π μ].
Proof. induction π as [| [a b] π IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma sws_trace_nil (π : list (Atom * Atom)) : sws_trace π [] = [].
Proof. induction π as [| [a b] π IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma cowt_sws_one (π : list (Atom * Atom)) (p q : P) (μ : A) : p ⟹ᶜᵒ{μ} q → sws π p ⟹ᶜᵒ{sws_act π μ} sws π q.
Proof. intros w. pose proof (cowt_sws π p [μ] q w) as w'. rewrite sws_trace_single in w'. exact w'. Qed.

Lemma cowt_sws_nil (π : list (Atom * Atom)) (p q : P) : p ⟹ᶜᵒ q → sws π p ⟹ᶜᵒ sws π q.
Proof. intros w. pose proof (cowt_sws π p [] q w) as w'. rewrite sws_trace_nil in w'. exact w'. Qed.

Lemma sws_act_rev_invol (π : list (Atom * Atom)) (μ : A) : sws_act (rev π) (sws_act π μ) = μ.
Proof.
  induction π as [| [a b] π IH]; simpl; [reflexivity |].
  by rewrite sws_act_app; simpl; rewrite ts_swap_act_invol, IH.
Qed.

Lemma cowt_sws_one_back (π : list (Atom * Atom)) (p q : P) (μ : A) : sws π p ⟹ᶜᵒ{sws_act π μ} q → p ⟹ᶜᵒ{μ} sws (rev π) q.
Proof.
  intros w. pose proof (cowt_sws_one (rev π) _ _ _ w) as w'. rewrite sws_rev_invol, sws_act_rev_invol in w'. exact w'.
Qed.

Lemma sws_fix (x : pair_states) (σ : list (Atom * Atom)) r : fixes σ (node_atoms x) → r ∈ x.1 ∨ r ∈ x.2 → sws σ r = r.
Proof.
  intros hσ hr. induction σ as [| [a b] σ IH]; simpl; [reflexivity |].
  destruct (hσ a b (list_elem_of_here _ _)) as [ha hb].
  rewrite IH; [exact (node_atoms_fix x a b r ha hb hr) |]. intros a' b' m. apply hσ. by apply list_elem_of_further.
Qed.

Lemma match_set_fix (x : pair_states) (σ π : list (Atom * Atom)) (X : gset P) :
  fixes σ (node_atoms x) → match_set π X x.1 → match_set (σ ++ π) X x.1.
Proof.
  intros hσ [h1 h2]. split.
  - intros r m. destruct (h1 r m) as (r' & m' & hb). exists r'. split; [exact m' |].
    rewrite sws_app, <- (sws_fix x σ r' hσ (or_introl m')). apply sbisim_sws, hb.
  - intros r' m'. destruct (h2 r' m') as (r & t & m & w & hb). exists r, t. split_and!; [exact m | exact w |].
    rewrite sws_app, <- (sws_fix x σ r' hσ (or_introl m')). apply sbisim_sws, hb.
Qed.

Lemma sub_set_fix (x : pair_states) (σ π : list (Atom * Atom)) (Y : gset P) :
  fixes σ (node_atoms x) → sub_set π Y x.2 → sub_set (σ ++ π) Y x.2.
Proof.
  intros hσ h r m. destruct (h r m) as (r' & m' & hb). exists r'. split; [exact m' |].
  rewrite sws_app, <- (sws_fix x σ r' hσ (or_intror m')). apply sbisim_sws, hb.
Qed.

Lemma match_set_child (k : nat) (π : list (Atom * Atom)) (X X' : gset P) (N : list P) (μ : A) :
  match_set π X N → tau_closed N → τbounded k (ext N (sws_act π μ)) = true →
  (∀ p', p' ∈ X' ↔ ∃ p, p ∈ X ∧ p ⟹ᶜᵒ{μ} p') → match_set π X' (τclose k (ext N (sws_act π μ))).
Proof.
  intros [h1 h2] hcl hb hX'. split.
  - intros r' m'. apply hX' in m' as (p & mp & w). destruct (h1 p mp) as (n & mn & hpn).
    destruct (sbisim_cowt _ _ _ _ hpn (cowt_sws_one π p r' μ w)) as (t & wt & ht).
    destruct (cowt_decomp_one wt) as (n1 & n2 & μ' & w1 & duo & l & w2).
    exists t. split; [| exact ht]. apply (τclose_complete k _ hb n2 t); [| exact w2].
    apply ext_spec. exists n1. split; [exact (closed_nil N n n1 hcl mn w1) |]. exists μ'. split; assumption.
  - intros t mt. destruct (τclose_sound k _ t mt) as (n2 & mn2 & w2). apply ext_spec in mn2 as (n1 & mn1 & μ' & duo & l).
    destruct (h2 n1 mn1) as (p & t0 & mp & w0 & hb0).
    destruct (sbisim_step _ _ (ActExt μ') n2 (sbisim_sym _ _ hb0) l) as (u & lu & hu).
    destruct (sbisim_cowt _ _ [] t hu w2) as (v & wv & hv).
    assert (w : sws π p ⟹ᶜᵒ{sws_act π μ} v).
    { apply (cowt_push_nil_left (cowt_sws_nil π p t0 w0)). exact (cowt_push_nil_right _ _ _ _ (lts_to_cowt duo lu) wv). }
    exists (sws (rev π) v), (sws (rev π) v). split_and!.
    + apply hX'. exists p. split; [exact mp | exact (cowt_sws_one_back π p v μ w)].
    + apply cowt_nil.
    + rewrite <- (rev_involutive π) at 1. rewrite sws_rev_invol. exact (sbisim_sym _ _ hv).
Qed.

Lemma sub_set_child (k : nat) (π : list (Atom * Atom)) (Y Y' : gset P) (N : list P) (μ : A) :
  sub_set π Y N → tau_closed N → τbounded k (ext N (sws_act π μ)) = true →
  (∀ q', q' ∈ Y' → ∃ q, q ∈ Y ∧ q ⟹ᶜᵒ{μ} q') → sub_set π Y' (τclose k (ext N (sws_act π μ))).
Proof.
  intros h hcl hb hY' r' m'. destruct (hY' r' m') as (q & mq & w). destruct (h q mq) as (n & mn & hqn).
  destruct (sbisim_cowt _ _ _ _ hqn (cowt_sws_one π q r' μ w)) as (t & wt & ht).
  destruct (cowt_decomp_one wt) as (n1 & n2 & μ' & w1 & duo & l & w2).
  exists t. split; [| exact ht]. apply (τclose_complete k _ hb n2 t); [| exact w2].
  apply ext_spec. exists n1. split; [exact (closed_nil N n n1 hcl mn w1) |]. exists μ'. split; assumption.
Qed.

Lemma match_set_canon (π π1 π2 : list (Atom * Atom)) (X : gset P) (N M : list P) :
  match_set π X N → (∀ z, z ∈ ts_norm <$> (sws π1 <$> N) ↔ z ∈ ts_norm <$> (sws π2 <$> M)) →
  match_set (rev π2 ++ π1 ++ π) X M.
Proof.
  intros [h1 h2] e. split.
  - intros r m. destruct (h1 r m) as (n & mn & hb).
    assert (hz : ts_norm (sws π1 n) ∈ ts_norm <$> (sws π2 <$> M)) by (apply e, list_elem_of_fmap_2, list_elem_of_fmap_2, mn).
    apply list_elem_of_fmap in hz as (z & ez & mz). apply list_elem_of_fmap in mz as (n' & -> & mn').
    exists n'. split; [exact mn' |]. rewrite !sws_app. rewrite <- (sws_rev_invol π2 n').
    apply sbisim_sws. exact (sbisim_trans _ _ _ (sbisim_sws π1 _ _ hb) (norm_bisim _ _ ez)).
  - intros n' mn'.
    assert (hz : ts_norm (sws π2 n') ∈ ts_norm <$> (sws π1 <$> N)) by (apply e, list_elem_of_fmap_2, list_elem_of_fmap_2, mn').
    apply list_elem_of_fmap in hz as (z & ez & mz). apply list_elem_of_fmap in mz as (n & -> & mn).
    destruct (h2 n mn) as (r & t & m & w & hb). exists r, t. split_and!; [exact m | exact w |].
    rewrite !sws_app. rewrite <- (sws_rev_invol π2 n').
    apply sbisim_sws. exact (sbisim_trans _ _ _ (sbisim_sws π1 _ _ hb) (norm_bisim _ _ (eq_sym ez))).
Qed.

Lemma sub_set_canon (π π1 π2 : list (Atom * Atom)) (Y : gset P) (N M : list P) :
  sub_set π Y N → (∀ z, z ∈ ts_norm <$> (sws π1 <$> N) ↔ z ∈ ts_norm <$> (sws π2 <$> M)) →
  sub_set (rev π2 ++ π1 ++ π) Y M.
Proof.
  intros h e r m. destruct (h r m) as (n & mn & hb).
  assert (hz : ts_norm (sws π1 n) ∈ ts_norm <$> (sws π2 <$> M)) by (apply e, list_elem_of_fmap_2, list_elem_of_fmap_2, mn).
  apply list_elem_of_fmap in hz as (z & ez & mz). apply list_elem_of_fmap in mz as (n' & -> & mn').
  exists n'. split; [exact mn' |]. rewrite !sws_app. rewrite <- (sws_rev_invol π2 n').
  apply sbisim_sws. exact (sbisim_trans _ _ _ (sbisim_sws π1 _ _ hb) (norm_bisim _ _ ez)).
Qed.

Lemma graph_term_pair (m k : nat) (p q : P) : graph_term (pair_graph m k p q).
Proof.
  intros x. apply (pair_graph_inv m k p q (λ x, (∀ r, r ∈ x.1 → r ⤓) ∧ (∀ r, r ∈ x.2 → r ⤓))).
  - intros y c _ mc. unfold children in mc. apply list_elem_of_omap in mc as (μ & _ & h). rewrite child_pair_unfold in h.
    destruct (τbounded k (ext y.1 μ)) eqn:b1, (τbounded k (ext y.2 μ)) eqn:b2; simpl in h; try discriminate.
    injection h as <-. split; apply τclose_terminate; assumption.
  - intros c h. rewrite root_pair_unfold in h.
    destruct (τbounded k [p]) eqn:b1, (τbounded k [q]) eqn:b2; simpl in h; try discriminate.
    injection h as <-. split; apply τclose_terminate; assumption.
Qed.

Lemma cert_postfix (k : nat) (p0 q0 : P) (R : list pair_states) :
  certified k p0 q0 R = true → graph_closed R → graph_term R →
  ∀ X Y, cert_rel R X Y → copre_co_ ts_Γ (cert_rel R) X Y.
Proof.
  intros hc hgc hgt X Y [(r & mr & hr) | [hY | (x & π & mx & hX & hY)]].
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
    destruct (certified_local k p0 q0 R x hc mx) as [hloc hch].
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
      destruct (proj2 hX x' mx1) as (r & t & mr & w & hbt).
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
        pose proof (match_set_fix x σ π X hσ hX) as hX2. pose proof (sub_set_fix x σ π Y hσ hY) as hY2.
        destruct (decide (sws_act (σ ++ π) μ ∈ next_list (explored x) x.2)) as [mμ | nμ].
        2: { right; left. intros q' mq'. destruct (hY' q' mq') as (q & mq & w). destruct (hY2 q mq) as (n & mn & hb).
             destruct (sbisim_cowt _ _ _ _ hb (cowt_sws_one (σ ++ π) q q' μ w)) as (n' & wn & _).
             destruct (cowt_decomp_one wn) as (n1 & n2 & μ'' & w1 & duo' & l' & _).
             apply nμ. exact (next_list_spec (explored x) x.2 n1 _ μ'' n2 (closed_nil _ n n1 cl2 mn w1) duo' l' hin). }
        specialize (hch _ mμ). unfold child_ok in hch. apply orb_true_iff in hch as [hc2 | hdiv].
        -- destruct (child_pair k x (sws_act (σ ++ π) μ)) as [c |] eqn:ec; [| discriminate]. rewrite in_graph_set in hc2.
           rewrite child_pair_unfold in ec.
           destruct (τbounded k (ext x.1 (sws_act (σ ++ π) μ))) eqn:b1, (τbounded k (ext x.2 (sws_act (σ ++ π) μ))) eqn:b2;
             simpl in ec; try discriminate.
           injection ec as <-.
           destruct (in_graph_spec _ _ hc2) as (y & my & e1 & e2').
           unfold canon, norm_pair, sw_pair in e1, e2'. simpl in e1, e2'.
           right; right.
           exists y, (rev (canon_sw y) ++ canon_sw (τclose k (ext x.1 (sws_act (σ ++ π) μ)), τclose k (ext x.2 (sws_act (σ ++ π) μ))) ++ σ ++ π).
           split_and!; [exact my | |].
           ++ apply (match_set_canon (σ ++ π) _ _ X' (τclose k (ext x.1 (sws_act (σ ++ π) μ)))); [| exact e1].
              exact (match_set_child k (σ ++ π) X X' x.1 μ hX2 cl1 b1 hX').
           ++ apply (sub_set_canon (σ ++ π) _ _ Y' (τclose k (ext x.2 (sws_act (σ ++ π) μ)))); [| exact e2'].
              exact (sub_set_child k (σ ++ π) Y Y' x.2 μ hY2 cl2 b2 hY').
        -- left. destruct (div_set_spec k _ hdiv) as (r2 & mr2 & hr2). apply ext_spec in mr2 as (n1 & mn1 & μ'' & duo' & l').
           destruct (proj2 hX2 n1 mn1) as (r & t & mr & w & hbt).
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

Lemma cert_root (m k : nat) (p q : P) : certify m k p q = true → cert_rel (pair_graph m k p q) {[ p ]} {[ q ]}.
Proof.
  intros hc. unfold certify in hc. unfold certified, certified_in in hc. apply andb_true_iff in hc as [hr _].
  unfold root_ok in hr. apply orb_true_iff in hr as [hd | hin].
  - left. destruct (div_set_spec k _ hd) as (r & ->%list_elem_of_singleton & hn). exists p. split; [set_solver | exact hn].
  - right; right. destruct (root_pair k p q) as [c |] eqn:er; [| discriminate]. rewrite in_graph_set in hin.
    rewrite root_pair_unfold in er. destruct (τbounded k [p]) eqn:bp, (τbounded k [q]) eqn:bq; simpl in er; try discriminate.
    injection er as <-.
    destruct (in_graph_spec _ _ hin) as (y & my & e1 & e2). unfold canon, norm_pair, sw_pair in e1, e2. simpl in e1, e2.
    exists y, (rev (canon_sw y) ++ canon_sw (τclose k [p], τclose k [q]) ++ []). split_and!; [exact my | |].
    + apply (match_set_canon [] _ _ {[ p ]} (τclose k [p])); [| exact e1]. split.
      * intros r ->%elem_of_singleton. exists p. split; [apply τclose_incl, list_elem_of_here | apply sbisim_refl].
      * intros r' m'. destruct (τclose_sound k [p] r' m') as (x0 & ->%list_elem_of_singleton & w).
        exists p, r'. split_and!; [set_solver | exact w | apply sbisim_refl].
    + apply (sub_set_canon [] _ _ {[ q ]} (τclose k [q])); [| exact e2].
      intros r ->%elem_of_singleton. exists q. split; [apply τclose_incl, list_elem_of_here | apply sbisim_refl].
Qed.

Theorem certify_spec_co (m k : nat) (p q : P) : certify m k p q = true → p ≼꜀ₒ₋ₐₛ[ ts_Γ ] q.
Proof.
  intros hc. apply (proj1 (copre_co_singleton ts_Γ p q)).
  pose proof (cert_root m k p q hc) as hroot. revert hroot.
  generalize ({[ p ]} : gset P) ({[ q ]} : gset P). unfold copre_co. coinduction RR CIH. intros X Y h.
  destruct (cert_postfix k p q _ hc (pair_graph_closed m k p q) (graph_term_pair m k p q) X Y h) as [f1 f2 f3 f4].
  constructor.
  - intros Y' hY'. apply CIH, (f1 Y' hY').
  - exact f2.
  - intros μ X' Y' a b c. apply CIH, (f3 μ X' Y' a b c).
  - exact f4.
Qed.

Corollary certify_co_conditions (m k : nat) (p q : P) : certify m k p q = true → ∀ s, co_conditions p q s.
Proof.
  intros hc s. destruct (certify_spec_co m k p q hc) as [h1 h2].
  split; [exact (h1 s) | intros q' hp w st; exact (h2 s q' hp w st)].
Qed.

Lemma decide_false_not_holds (m k n : nat) (p q : P) E hE :
  match decide_false m k n p q E hE with Holds _ _ _ => False | _ => True end.
Proof.
  unfold decide_false, fallback.
  destruct (open_root k p) as [Xp hXp hp | |].
  - destruct (open_root k q) as [Xq hXq hq | hn |].
    + destruct (refute k p q n [] Xp Xq hXp hXq hp hq) as [[[s t] h'] |]; [exact I |].
      destruct (test_entries k p q E hE) as [[[s t] h'] |]; exact I.
    + exact I.
    + destruct (test_entries k p q E hE) as [[[s t] h'] |]; exact I.
  - destruct (test_entries k p q E hE) as [[[s t] h'] |]; exact I.
  - destruct (test_entries k p q E hE) as [[[s t] h'] |]; exact I.
Qed.

Theorem verdict_holds_co (m k n : nat) (p q : P) : verdict m k n p q = R_holds → p ≼꜀ₒ₋ₐₛ[ ts_Γ ] q.
Proof.
  intros hv. destruct (fast_certify m k p q) eqn:hf.
  - exact (certify_spec_co m k p q (fast_sound m k p q hf)).
  - exfalso. unfold verdict in hv. rewrite (decide_preorder_false m k n p q hf) in hv.
    pose proof (decide_false_not_holds m k n p q _ (fast_facts m k p q)) as hn.
    destruct (decide_false m k n p q _ (fast_facts m k p q)); [exact hn | discriminate | discriminate].
Qed.

End Certificate.
(* end hide *)
