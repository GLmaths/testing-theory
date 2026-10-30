(* begin hide *)
From Stdlib Require Import Lia.
From stdpp Require Import base countable gmap list sets numbers.
From Coinduction Require Import all.
From TestingTheory Require Import ActTau gLts SyncActions Termination Subset_Act InListPropHelper
  coWeakTransition coConvergence coFiniteImage DefinitionASrel Coin_tower_co
  Decision.Tools_in_construction.Inductive.Generic.Helpers Decision.Tools_in_construction.Inductive.Generic.Bisim
  Decision.Tools_in_construction.Inductive.Generic.Interface Decision.Tools_in_construction.Inductive.Generic.Sets Decision.Tools_in_construction.Inductive.Generic.Transport
  Decision.Tools_in_construction.Inductive.Generic.Graph Decision.Tools_in_construction.Inductive.Generic.Swaps Decision.Tools_in_construction.Inductive.Generic.Adequacy
  Decision.Tools_in_construction.Inductive.Generic.Verdict Decision.Tools_in_construction.CoInductive.Generic.Certificate Decision.Tools_in_construction.CoInductive.Generic.Antichain.
Import ListNotations.

Section Normalised.

Context `{TS : TraceSearchLang P A Atom PreAct T}.

(** Sets of states up to strong bisimilarity: every produced state is normalised. *)

Definition nτsucc (X : list P) : list P := remove_dups (ts_norm <$> τsucc X).

Fixpoint nτb (k : nat) (X : list P) : option (list P) :=
  match k with
  | 0 => if bool_decide (τsucc X = []) then Some X else None
  | S k => (λ Z, remove_dups (X ++ Z)) <$> nτb k (nτsucc X)
  end.

Definition next_n (X : list P) (μ : A) : list P := remove_dups (ts_norm <$> ext X μ).

Lemma norm_sb (r : P) : sbisim r (ts_norm r).
Proof. apply sbisim_sym, ts_norm_spec. Qed.

Lemma nτsucc_sound (X : list P) y : y ∈ nτsucc X → ∃ x y0, x ∈ X ∧ x ⟶ y0 ∧ sbisim y0 y.
Proof.
  intros m. apply elem_of_remove_dups, list_elem_of_fmap in m as (y0 & -> & m).
  destruct (τsucc_spec X y0 m) as (x & mx & l). exists x, y0. split_and!; [exact mx | exact l | apply norm_sb].
Qed.

Lemma nτsucc_complete (X : list P) x y0 : x ∈ X → x ⟶ y0 → ∃ y, y ∈ nτsucc X ∧ sbisim y0 y.
Proof.
  intros mx l. exists (ts_norm y0). split; [| apply norm_sb].
  apply elem_of_remove_dups, list_elem_of_fmap_2, (tau_succ_mem X x y0 mx l).
Qed.

Lemma next_n_sound (X : list P) (μ : A) y : y ∈ next_n X μ → ∃ x μ' y0, x ∈ X ∧ sync μ' μ ∧ x ⟶[μ'] y0 ∧ sbisim y0 y.
Proof.
  intros m. apply elem_of_remove_dups, list_elem_of_fmap in m as (y0 & -> & m).
  apply ext_spec in m as (x & mx & μ' & duo & l). exists x, μ', y0. split_and!; [exact mx | exact duo | exact l | apply norm_sb].
Qed.

Lemma next_n_complete (X : list P) (μ μ' : A) x y0 : x ∈ X → sync μ' μ → x ⟶[μ'] y0 → ∃ y, y ∈ next_n X μ ∧ sbisim y0 y.
Proof.
  intros mx duo l. exists (ts_norm y0). split; [| apply norm_sb].
  apply elem_of_remove_dups, list_elem_of_fmap_2, ext_spec. exists x. split; [exact mx |]. exists μ'. split; assumption.
Qed.

Lemma no_tau_cowt (X : list P) x t : τsucc X = [] → x ∈ X → x ⟹ᶜᵒ t → t = x.
Proof.
  intros h mx w. remember ([] : trace A) as s0 eqn:hs0 in w. revert hs0 mx.
  induction w as [x | s0 x x1 t l w IHw | ]; intros hs0 mx; [reflexivity | | discriminate].
  exfalso. pose proof (tau_succ_mem X x x1 mx l) as m. rewrite h in m. inversion m.
Qed.

Lemma nτb_terminate (k : nat) : ∀ X Z, nτb k X = Some Z → ∀ x, x ∈ X → x ⤓.
Proof.
  induction k as [| k IH]; intros X Z h x mx; simpl in h.
  - case_bool_decide as e; [| discriminate]. constructor. intros y l. exfalso.
    pose proof (tau_succ_mem X x y mx l) as m. rewrite e in m. inversion m.
  - destruct (nτb k (nτsucc X)) as [Z' |] eqn:e; [| discriminate]. constructor. intros y l.
    destruct (nτsucc_complete X x y mx l) as (y' & my' & hb).
    exact (sbisim_terminate _ _ (sbisim_sym _ _ hb) (IH _ _ e y' my')).
Qed.

Lemma nτb_sound (k : nat) : ∀ X Z, nτb k X = Some Z → ∀ t, t ∈ Z → ∃ x t0, x ∈ X ∧ x ⟹ᶜᵒ t0 ∧ sbisim t0 t.
Proof.
  induction k as [| k IH]; intros X Z h t mt; simpl in h.
  - case_bool_decide; [| discriminate]. injection h as <-. exists t, t. split_and!; [exact mt | apply cowt_nil | apply sbisim_refl].
  - destruct (nτb k (nτsucc X)) as [Z' |] eqn:e; [| discriminate]. injection h as <-.
    apply elem_of_remove_dups, elem_of_app in mt as [mt | mt].
    + exists t, t. split_and!; [exact mt | apply cowt_nil | apply sbisim_refl].
    + destruct (IH _ _ e t mt) as (y & t1 & my & w & hb).
      destruct (nτsucc_sound X y my) as (x & y0 & mx & l & hb0).
      destruct (sbisim_cowt _ _ _ _ (sbisim_sym _ _ hb0) w) as (t2 & w2 & hb2).
      exists x, t2. split_and!; [exact mx | exact (cowt_tau [] x y0 t2 l w2) |].
      exact (sbisim_trans _ _ _ (sbisim_sym _ _ hb2) hb).
Qed.

Lemma nτb_complete (k : nat) : ∀ X Z, nτb k X = Some Z → ∀ x t, x ∈ X → x ⟹ᶜᵒ t → ∃ t', t' ∈ Z ∧ sbisim t t'.
Proof.
  induction k as [| k IH]; intros X Z h x t mx w; simpl in h.
  - case_bool_decide as e; [| discriminate]. injection h as <-.
    rewrite (no_tau_cowt X x t e mx w). exists x. split; [exact mx | apply sbisim_refl].
  - destruct (nτb k (nτsucc X)) as [Z' |] eqn:e; [| discriminate]. injection h as <-.
    remember ([] : trace A) as s0 eqn:hs0 in w. revert hs0 mx.
    induction w as [x | s0 x x1 t l w IHw | ]; intros hs0 mx; [| | discriminate].
    + exists x. split; [apply elem_of_remove_dups, elem_of_app; left; exact mx | apply sbisim_refl].
    + subst. destruct (nτsucc_complete X x x1 mx l) as (y & my & hb).
      destruct (sbisim_cowt _ _ _ _ hb w) as (t' & w' & hb').
      destruct (IH _ _ e y t' my w') as (t'' & mt'' & hb'').
      exists t''. split; [apply elem_of_remove_dups, elem_of_app; right; exact mt'' | exact (sbisim_trans _ _ _ hb' hb'')].
Qed.

Definition closed_sb (N : list P) : Prop := ∀ y y', y ∈ N → y ⟶ y' → ∃ y'', y'' ∈ N ∧ sbisim y' y''.

Definition term_set (N : list P) : Prop := ∀ r, r ∈ N → r ⤓.

Lemma nτb_closed (k : nat) (X Z : list P) : nτb k X = Some Z → closed_sb Z.
Proof.
  intros h y y' my l. destruct (nτb_sound k X Z h y my) as (x & t0 & mx & w & hb).
  destruct (sbisim_step _ _ τ y' (sbisim_sym _ _ hb) l) as (t1 & l1 & hb1).
  destruct (nτb_complete k X Z h x t1 mx (cowt_push_nil_right _ _ _ _ w (lts_to_cowt_tau l1))) as (y'' & my'' & hb2).
  exists y''. split; [exact my'' | exact (sbisim_trans _ _ _ hb1 hb2)].
Qed.

Lemma nτb_term (k : nat) (X Z : list P) : nτb k X = Some Z → term_set Z.
Proof.
  intros h t mt. destruct (nτb_sound k X Z h t mt) as (x & t0 & mx & w & hb).
  apply (sbisim_terminate t0 t hb).
  exact (cocnv_terminate t0 [] (cocnv_preserved_by_cowt_nil [] x (cocnv_nil x (nτb_terminate k X Z h x mx)) t0 w)).
Qed.

Lemma closed_sb_cowt (N : list P) : closed_sb N → ∀ a b, a ⟹ᶜᵒ b → ∀ u, u ∈ N → sbisim a u → ∃ v, v ∈ N ∧ sbisim b v.
Proof.
  intros hN a b w. remember ([] : trace A) as s0 eqn:hs0 in w. revert hs0.
  induction w as [a | s0 a a1 b l w IHw | ]; intros hs0 u mu hb; [exists u; split; assumption | | discriminate].
  subst. destruct (sbisim_step _ _ τ a1 hb l) as (u1 & lu & hb1).
  destruct (hN u u1 mu lu) as (u2 & mu2 & hb2). exact (IHw eq_refl u2 mu2 (sbisim_trans _ _ _ hb1 hb2)).
Qed.

(** The normalised pair graph. *)

Definition nchild (k : nat) (x : pair_states) (μ : A) : option pair_states :=
  match nτb k (next_n x.1 μ), nτb k (next_n x.2 μ) with
  | Some X, Some Y => Some (X, Y)
  | _, _ => None
  end.

Definition nroot (k : nat) (p q : P) : option pair_states :=
  match nτb k [ts_norm p], nτb k [ts_norm q] with
  | Some X, Some Y => Some (X, Y)
  | _, _ => None
  end.

Definition nchildren_tr (k : nat) (e : pair_states * list A) : list (pair_states * list A) :=
  omap (λ μ, (λ c, (c, μ :: e.2)) <$> nchild k e.1 μ) (next_list (explored e.1) e.1.2).

Fixpoint nbfs (k m : nat) (I : gmap (N * N) (list pair_states)) (L : list ((N * N) * pair_states))
  (visited work : list (pair_states * list A)) : list (pair_states * list A) * list ((N * N) * pair_states) :=
  match m with
  | 0 => (visited, L)
  | S m =>
      match work with
      | [] => (visited, L)
      | e :: work' =>
          let c := canon e.1 in
          if covered c I L then nbfs k m I L visited work'
          else let kc := node_key c in
               nbfs k m (idx_add c I) ((kc, c) :: filter (λ ky, negb (if key_le kc ky.1 then subsumes c ky.2 else false)) L)
                 (e :: visited) (work' ++ nchildren_tr k e)
      end
  end.

Definition nrun (m k : nat) (p q : P) : list (pair_states * list A) * list ((N * N) * pair_states) :=
  match nroot k p q with
  | Some c => nbfs k m ∅ [] [] [(c, [])]
  | None => ([], [])
  end.

Definition ngraph (m k : nat) (p q : P) : list pair_states := map fst (nrun m k p q).1.

Lemma nbfs_inv (k : nat) (Q : pair_states → Prop)
  (hQ : ∀ e c, Q e.1 → c ∈ nchildren_tr k e → Q c.1) :
  ∀ m I L visited work, (∀ e, e ∈ visited → Q e.1) → (∀ e, e ∈ work → Q e.1) →
  ∀ e, e ∈ (nbfs k m I L visited work).1 → Q e.1.
Proof.
  induction m as [| m IH]; intros I L visited work hv hw x hx; simpl in hx; [exact (hv x hx) |].
  destruct work as [| y work']; [exact (hv x hx) |].
  destruct (covered (canon y.1) I L).
  - apply (IH I L visited work' hv); [intros z hz; apply hw, list_elem_of_further, hz | exact hx].
  - refine (IH _ _ (y :: visited) (work' ++ nchildren_tr k y) _ _ x hx).
    + intros z [-> | hz]%elem_of_cons; [apply hw, list_elem_of_here | exact (hv z hz)].
    + intros z [hz | hz]%elem_of_app; [apply hw, list_elem_of_further, hz |].
      apply (hQ y z); [apply hw, list_elem_of_here | exact hz].
Qed.

Lemma nbfs_L (k : nat) : ∀ m I L visited work, (∀ ky, ky ∈ L → ∃ e, e ∈ visited ∧ ky.2 = canon e.1) →
  ∀ ky, ky ∈ (nbfs k m I L visited work).2 → ∃ e, e ∈ (nbfs k m I L visited work).1 ∧ ky.2 = canon e.1.
Proof.
  induction m as [| m IH]; intros I L visited work hL ky mky; simpl in mky |- *; [exact (hL ky mky) |].
  revert mky. destruct work as [| y work']; [intros mky; exact (hL ky mky) |].
  destruct (covered (canon y.1) I L); intros mky; [exact (IH _ _ _ _ hL ky mky) |].
  apply (IH _ _ _ _); [| exact mky]. intros ky' [-> | m']%elem_of_cons.
  - exists y. split; [apply list_elem_of_here | reflexivity].
  - apply list_elem_of_filter in m' as [_ m']. destruct (hL ky' m') as (e & me & ee).
    exists e. split; [by apply list_elem_of_further | exact ee].
Qed.

Lemma nrun_L_ok (m k : nat) (p q : P) : L_ok (ngraph m k p q) (nrun m k p q).2.
Proof.
  unfold ngraph, nrun. destruct (nroot k p q) as [c |]; [| intros ky mky; inversion mky].
  intros ky mky. destruct (nbfs_L k m ∅ [] [] [(c, [])] ltac:(intros ky' m'; inversion m') ky mky) as (e & me & ee).
  exists e.1. split; [apply list_elem_of_fmap_2, me | exact ee].
Qed.

Definition node_ok (x : pair_states) : Prop := closed_sb x.1 ∧ closed_sb x.2 ∧ term_set x.1 ∧ term_set x.2.

Lemma nchild_ok_node (k : nat) (x c : pair_states) (μ : A) : nchild k x μ = Some c → node_ok c.
Proof.
  unfold nchild. destruct (nτb k (next_n x.1 μ)) as [X |] eqn:e1, (nτb k (next_n x.2 μ)) as [Y |] eqn:e2; try discriminate.
  intros h. injection h as <-. split_and!; simpl.
  - exact (nτb_closed k _ _ e1).
  - exact (nτb_closed k _ _ e2).
  - exact (nτb_term k _ _ e1).
  - exact (nτb_term k _ _ e2).
Qed.

Lemma ngraph_nodes (m k : nat) (p q : P) : ∀ x, x ∈ ngraph m k p q → node_ok x.
Proof.
  intros x hx. unfold ngraph, nrun in hx. destruct (nroot k p q) as [c |] eqn:er; [| inversion hx].
  apply list_elem_of_fmap in hx as (e' & -> & he).
  apply (nbfs_inv k (λ x, node_ok x)) with (m := m) (I := ∅) (L := []) (visited := []) (work := [(c, [])]); [| intros z hz; inversion hz | | exact he].
  - intros e c' _ mc. unfold nchildren_tr in mc. apply list_elem_of_omap in mc as (μ & _ & h).
    destruct (nchild k e.1 μ) as [c1 |] eqn:ec; [| discriminate]. injection h as <-. exact (nchild_ok_node k e.1 c1 μ ec).
  - intros z hz. apply list_elem_of_singleton in hz as ->. unfold nroot in er.
    destruct (nτb k [ts_norm p]) as [X |] eqn:e1, (nτb k [ts_norm q]) as [Y |] eqn:e2; try discriminate.
    injection er as <-. split_and!; simpl; [exact (nτb_closed k _ _ e1) | exact (nτb_closed k _ _ e2) | exact (nτb_term k _ _ e1) | exact (nτb_term k _ _ e2)].
Qed.

(** The certificate on the normalised graph. *)

Definition nchild_ok (k : nat) (I : gmap (N * N) (list pair_states)) (L : list ((N * N) * pair_states)) (x : pair_states) (μ : A) : bool :=
  if match nchild k x μ with
     | Some c => covered (canon c) I L
     | None => false
     end then true else div_set k (ext x.1 μ).

Definition nroot_ok (k : nat) (p q : P) (I : gmap (N * N) (list pair_states)) (L : list ((N * N) * pair_states)) : bool :=
  if div_set k [p] then true else
  match nroot k p q with
  | Some c => covered (canon c) I L
  | None => false
  end.

Definition ncertified_in (k : nat) (p q : P) (R : list pair_states) (I : gmap (N * N) (list pair_states))
  (L : list ((N * N) * pair_states)) : bool :=
  if nroot_ok k p q I L then forallb (λ x, if local_ok x then forallb (nchild_ok k I L x) (next_list (explored x) x.2) else false) R else false.

Definition ncertify (m k : nat) (p q : P) : bool :=
  let r := nrun m k p q in
  let R := map fst r.1 in ncertified_in k p q R (canon_index R) r.2.

Lemma ncertified_local (k : nat) (p q : P) (R : list pair_states) I L (x : pair_states) :
  ncertified_in k p q R I L = true → x ∈ R →
  local_ok x = true ∧ ∀ μ, μ ∈ next_list (explored x) x.2 → nchild_ok k I L x μ = true.
Proof.
  intros h m. unfold ncertified_in in h. apply andb_true_iff in h as [_ h]. rewrite forallb_forall in h.
  specialize (h x (proj1 (list_elem_of_In _ _) m)). apply andb_true_iff in h as [h1 h2].
  split; [exact h1 |]. intros μ mμ. rewrite forallb_forall in h2. exact (h2 μ (proj1 (list_elem_of_In _ _) mμ)).
Qed.

Lemma cover_set_nchild (k : nat) (π : list (Atom * Atom)) (X X' : gset P) (N Z : list P) (μ : A) :
  cover_set π X N → nτb k (next_n N (sws_act π μ)) = Some Z →
  (∀ p', p' ∈ X' ↔ ∃ p, p ∈ X ∧ p ⟹ᶜᵒ{μ} p') → cover_set π X' Z.
Proof.
  intros hc hz hX' t mt. destruct (nτb_sound k _ Z hz t mt) as (y & t0 & my & w & hb).
  destruct (next_n_sound N _ y my) as (n1 & μ' & y0 & mn1 & duo & l & hby).
  destruct (hc n1 mn1) as (p & t1 & mp & w1 & hb1).
  destruct (sbisim_step _ _ (ActExt μ') y0 (sbisim_sym _ _ hb1) l) as (u & lu & hu).
  destruct (sbisim_cowt _ _ _ _ (sbisim_sym _ _ (sbisim_trans _ _ _ (sbisim_sym _ _ hu) hby)) w) as (v & wv & hv).
  assert (wpv : sws π p ⟹ᶜᵒ{sws_act π μ} v).
  { apply (cowt_push_nil_left (cowt_sws_nil π p t1 w1)). exact (cowt_push_nil_right _ _ _ _ (lts_to_cowt duo lu) wv). }
  exists (sws (rev π) v), (sws (rev π) v). split_and!.
  - apply hX'. exists p. split; [exact mp | exact (cowt_sws_one_back π p v μ wpv)].
  - apply cowt_nil.
  - rewrite <- (rev_involutive π) at 1. rewrite sws_rev_invol. exact (sbisim_trans _ _ _ (sbisim_sym _ _ hv) hb).
Qed.

Lemma sub_set_nchild (k : nat) (π : list (Atom * Atom)) (Y Y' : gset P) (N Z : list P) (μ : A) :
  sub_set π Y N → closed_sb N → nτb k (next_n N (sws_act π μ)) = Some Z →
  (∀ q', q' ∈ Y' → ∃ q, q ∈ Y ∧ q ⟹ᶜᵒ{μ} q') → sub_set π Y' Z.
Proof.
  intros hs hcl hz hY' r mr. destruct (hY' r mr) as (q & mq & w). destruct (hs q mq) as (n & mn & hqn).
  destruct (sbisim_cowt _ _ _ _ hqn (cowt_sws_one π q r μ w)) as (w' & ww & hw).
  destruct (cowt_decomp_one ww) as (n1 & n2 & μ' & w1 & duo & l & w2).
  destruct (closed_sb_cowt N hcl n n1 w1 n mn (sbisim_refl n)) as (n1' & mn1' & hb1).
  destruct (sbisim_step _ _ (ActExt μ') n2 hb1 l) as (n2' & l2 & hb2).
  destruct (next_n_complete N _ μ' n1' n2' mn1' duo l2) as (y & my & hby).
  destruct (sbisim_cowt _ _ _ _ (sbisim_trans _ _ _ hb2 hby) w2) as (t & wt & ht).
  destruct (nτb_complete k _ Z hz y t my wt) as (t' & mt' & ht').
  exists t'. split; [exact mt' |]. exact (sbisim_trans _ _ _ hw (sbisim_trans _ _ _ ht ht')).
Qed.

Lemma ncert_postfix (k : nat) (p0 q0 : P) (R : list pair_states) (L : list ((N * N) * pair_states)) :
  ncertified_in k p0 q0 R (canon_index R) L = true → L_ok R L → (∀ x, x ∈ R → node_ok x) →
  ∀ X Y, cert_rel_ac R X Y → copre_co_ ts_Γ (cert_rel_ac R) X Y.
Proof.
  intros hc hL hR X Y [(r & mr & hr) | [hY | (x & π & mx & hX & hY)]].
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
  - destruct (hR x mx) as (cl1 & cl2 & t1 & t2).
    destruct (ncertified_local k p0 q0 R _ _ x hc mx) as [hloc hch].
    constructor.
    + intros Y' hY'. right; right. exists x, π. split_and!; [exact mx | exact hX |].
      intros r' mr'. destruct (hY' r' mr') as (q & mq & w). destruct (hY q mq) as (n & mn & hb).
      destruct (sbisim_cowt _ _ _ _ hb (cowt_sws_nil π q r' w)) as (n' & wn & hb').
      destruct (closed_sb_cowt _ cl2 n n' wn n mn (sbisim_refl n)) as (n'' & mn'' & hb'').
      exists n''. split; [exact mn'' | exact (sbisim_trans _ _ _ hb' hb'')].
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
        destruct (closed_sb_cowt _ cl2 n n1 w1 n mn (sbisim_refl n)) as (n1' & mn1' & hb1).
        destruct (sbisim_step _ _ (ActExt μ') n2 hb1 l) as (n2' & l2 & _).
        assert (m2 : n2' ∈ ext x.2 (sws_act π μ))
          by (apply ext_spec; exists n1'; split; [exact mn1' |]; exists μ'; split; assumption).
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
             destruct (closed_sb_cowt _ cl2 n n1 w1 n mn (sbisim_refl n)) as (n1' & mn1' & hb1).
             destruct (sbisim_step _ _ (ActExt μ'') n2 hb1 l') as (n2' & ln2 & _).
             apply nμ. exact (next_list_spec (explored x) x.2 n1' _ μ'' n2' mn1' duo' ln2 hin). }
        specialize (hch _ mμ). unfold nchild_ok in hch. apply orb_true_iff in hch as [hc2 | hdiv].
        -- destruct (nchild k x (sws_act (σ ++ π) μ)) as [c |] eqn:ec; [| discriminate].
           unfold nchild in ec.
           destruct (nτb k (next_n x.1 (sws_act (σ ++ π) μ))) as [Z1 |] eqn:ez1,
             (nτb k (next_n x.2 (sws_act (σ ++ π) μ))) as [Z2 |] eqn:ez2; try discriminate.
           injection ec as <-.
           destruct (covered_spec _ _ _ hL hc2) as (y & my & f1 & f2).
           unfold canon, norm_pair, sw_pair in f1, f2. simpl in f1, f2.
           right; right.
           exists y, (rev (canon_sw y) ++ canon_sw (Z1, Z2) ++ σ ++ π).
           split_and!; [exact my | |].
           ++ apply (cover_set_incl (σ ++ π) _ _ X' Z1); [| exact f1].
              exact (cover_set_nchild k (σ ++ π) X X' x.1 Z1 μ hX2 ez1 hX').
           ++ apply (sub_set_incl (σ ++ π) _ _ Y' Z2); [| exact f2].
              exact (sub_set_nchild k (σ ++ π) Y Y' x.2 Z2 μ hY2 cl2 ez2 hY').
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

Lemma ncert_root (m k : nat) (p q : P) : ncertify m k p q = true → cert_rel_ac (ngraph m k p q) {[ p ]} {[ q ]}.
Proof.
  intros hc. pose proof (nrun_L_ok m k p q) as hL. unfold ncertify, ncertified_in in hc. cbv zeta in hc.
  fold (ngraph m k p q) in hc. apply andb_true_iff in hc as [hr _].
  unfold nroot_ok in hr. apply orb_true_iff in hr as [hd | hin].
  - left. destruct (div_set_spec k _ hd) as (r & ->%list_elem_of_singleton & hn). exists p. split; [set_solver | exact hn].
  - right; right. destruct (nroot k p q) as [c |] eqn:er; [| discriminate].
    unfold nroot in er. destruct (nτb k [ts_norm p]) as [Z1 |] eqn:e1, (nτb k [ts_norm q]) as [Z2 |] eqn:e2; try discriminate.
    injection er as <-.
    destruct (covered_spec _ _ _ hL hin) as (y & my & f1 & f2). unfold canon, norm_pair, sw_pair in f1, f2. simpl in f1, f2.
    exists y, (rev (canon_sw y) ++ canon_sw (Z1, Z2) ++ []). split_and!; [exact my | |].
    + apply (cover_set_incl [] _ _ {[ p ]} Z1); [| exact f1].
      intros t mt. destruct (nτb_sound k _ Z1 e1 t mt) as (y0 & t0 & ->%list_elem_of_singleton & w & hb).
      destruct (sbisim_cowt _ _ _ _ (ts_norm_spec p) w) as (t1 & w1 & hb1).
      exists p, t1. split_and!; [set_solver | exact w1 | exact (sbisim_trans _ _ _ (sbisim_sym _ _ hb1) hb)].
    + apply (sub_set_incl [] _ _ {[ q ]} Z2); [| exact f2].
      intros r ->%elem_of_singleton.
      destruct (nτb_complete k _ Z2 e2 (ts_norm q) (ts_norm q) (list_elem_of_here _ _) (cowt_nil _)) as (t & mt & ht).
      exists t. split; [exact mt | exact (sbisim_trans _ _ _ (norm_sb q) ht)].
Qed.

Theorem ncertify_spec (m k : nat) (p q : P) : ncertify m k p q = true → p ≼꜀ₒ₋ₐₛ[ ts_Γ ] q.
Proof.
  intros hc. apply (proj1 (copre_co_singleton ts_Γ p q)).
  pose proof (ncert_root m k p q hc) as hroot. revert hroot.
  generalize ({[ p ]} : gset P) ({[ q ]} : gset P). unfold copre_co. coinduction RR CIH. intros X Y h.
  assert (hc' : ncertified_in k p q (ngraph m k p q) (canon_index (ngraph m k p q)) (nrun m k p q).2 = true) by exact hc.
  destruct (ncert_postfix k p q _ _ hc' (nrun_L_ok m k p q) (ngraph_nodes m k p q) X Y h) as [f1 f2 f3 f4].
  constructor.
  - intros Y' hY'. apply CIH, (f1 Y' hY').
  - exact f2.
  - intros μ X' Y' a b c. apply CIH, (f3 μ X' Y' a b c).
  - exact f4.
Qed.

(** The verdict: the normalised certificate first, the exact procedure otherwise. *)

Definition verdict_n (m k n : nat) (p q : P) : result :=
  if ncertify m k p q then R_holds else verdict m k n p q.

Theorem verdict_n_holds (m k n : nat) (p q : P) : verdict_n m k n p q = R_holds → p ≼꜀ₒ₋ₐₛ[ ts_Γ ] q.
Proof.
  unfold verdict_n. destruct (ncertify m k p q) eqn:hc; [intros _; exact (ncertify_spec m k p q hc) |].
  intros h. exact (verdict_holds_co m k n p q h).
Qed.

Theorem verdict_n_fails (m k n : nat) (p q : P) (s : trace A) (t : T) :
  verdict_n m k n p q = R_fails s t → ts_must p t ∧ ¬ ts_must q t.
Proof. unfold verdict_n. destruct (ncertify m k p q); [discriminate |]. apply verdict_fails. Qed.

Theorem verdict_n_complete (m k n : nat) (p q : P) :
  adequate m k p q = true → verdict_n m k n p q = R_holds ∨ ∃ s t, verdict_n m k n p q = R_fails s t.
Proof.
  intros ha. unfold verdict_n. destruct (ncertify m k p q); [left; reflexivity |]. exact (verdict_complete m k n p q ha).
Qed.

End Normalised.
(* end hide *)
