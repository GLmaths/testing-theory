(* begin hide *)
From Stdlib Require Import Lia.
From stdpp Require Import base countable gmap list sets numbers.
From TestingTheory Require Import ActTau gLts SyncActions Termination Subset_Act InListPropHelper
  coWeakTransition coConvergence coFiniteImage
  Decision.Tools_in_construction.Inductive.Generic.Helpers Decision.Tools_in_construction.Inductive.Generic.Bisim
  Decision.Tools_in_construction.Inductive.Generic.Interface Decision.Tools_in_construction.Inductive.Generic.Sets Decision.Tools_in_construction.Inductive.Generic.Transport Decision.Tools_in_construction.Inductive.Generic.Graph Decision.Tools_in_construction.Inductive.Generic.Swaps Decision.Tools_in_construction.Inductive.Generic.Adequacy.
Import ListNotations.

Section Verdict.

Context `{TS : TraceSearchLang P A Atom PreAct T}.

(** Refutation and decision. *)

Fixpoint first_some {X Y : Type} (f : X → option Y) (l : list X) : option Y :=
  match l with
  | [] => None
  | x :: l => match f x with
              | Some y => Some y
              | None => first_some f l
              end
  end.

Lemma first_some_some {X Y : Type} (f : X → option Y) (l : list X) (x : X) :
  x ∈ l → f x ≠ None → first_some f l ≠ None.
Proof.
  induction l as [| y l IH]; simpl; intros m h; [inversion m |].
  destruct (f y) eqn:e; [discriminate |]. apply elem_of_cons in m as [-> | m]; [contradiction | exact (IH m h)].
Qed.

Lemma conv_test_spec (p q : P) (s : trace A) : p ⇓ᶜᵒ s → ¬ q ⇓ᶜᵒ s → ts_must p (ts_tc s) ∧ ¬ ts_must q (ts_tc s).
Proof. intros hp hn. rewrite !ts_tc_spec. split; [exact hp | exact hn]. Qed.

Definition conv_test (p q : P) (s : trace A) (hp : p ⇓ᶜᵒ s) (hn : ¬ q ⇓ᶜᵒ s) : distinguishing_test_of p q :=
  exist _ (s, ts_tc s) (conv_test_spec p q s hp hn).

Definition rec_type (p q : P) : Type :=
  ∀ (s : trace A) (Xp Xq : list P), exact_after p s Xp → exact_after q s Xq →
    p ⇓ᶜᵒ s → q ⇓ᶜᵒ s → option (distinguishing_test_of p q).

Definition child_test (k : nat) (p q : P) (rec : rec_type p q) (s : trace A) (Xp Xq : list P)
  (hXp : exact_after p s Xp) (hXq : exact_after q s Xq) (hp : p ⇓ᶜᵒ s) (hq : q ⇓ᶜᵒ s) (μ : A) :
  option (distinguishing_test_of p q) :=
  match open_child k p s Xp hXp hp μ with
  | Opened Xp' hXp' hp' =>
      match open_child k q s Xq hXq hq μ with
      | Opened Xq' hXq' hq' => rec (s ++ [μ]) Xp' Xq' hXp' hXq' hp' hq'
      | Diverged hn => Some (conv_test p q (s ++ [μ]) hp' hn)
      | Unknown => None
      end
  | _ => None
  end.

Fixpoint refute (k : nat) (p q : P) (n : nat) : rec_type p q :=
  λ s Xp Xq hXp hXq hp hq,
  match distinguish_sets p q s hp Xp Xq hXp hXq with
  | Some d => Some d
  | None =>
      match n with
      | 0 => None
      | S n => first_some (child_test k p q (refute k p q n) s Xp Xq hXp hXq hp hq)
                 (next_list (explored (Xp, Xq)) Xq)
      end
  end.

Inductive answer (p q : P) : Type :=
| Holds : (∀ s, co_conditions p q s) → answer p q
| Fails (s : trace A) (t : T) : ts_must p t ∧ ¬ ts_must q t → answer p q
| Unknown_answer : answer p q.

Arguments Holds {p q}.
Arguments Fails {p q}.
Arguments Unknown_answer {p q}.

Inductive node_at (p q : P) (s : trace A) : Type :=
| NodeAt (Xp Xq : list P) : exact_after p s Xp → exact_after q s Xq → p ⇓ᶜᵒ s → q ⇓ᶜᵒ s → node_at p q s.

Arguments NodeAt {p q s}.

Fixpoint follow_rev (k : nat) (p q : P) (r : list A) : option (node_at p q (rev r)) :=
  match r with
  | [] =>
      match open_root k p, open_root k q with
      | Opened Xp hXp hp, Opened Xq hXq hq => Some (NodeAt Xp Xq hXp hXq hp hq)
      | _, _ => None
      end
  | μ :: r' =>
      match follow_rev k p q r' with
      | Some (NodeAt Xp Xq hXp hXq hp hq) =>
          match open_child k p (rev r') Xp hXp hp μ, open_child k q (rev r') Xq hXq hq μ with
          | Opened Xp' hXp' hp', Opened Xq' hXq' hq' => Some (NodeAt Xp' Xq' hXp' hXq' hp' hq')
          | _, _ => None
          end
      | None => None
      end
  end.

Definition entry_facts (p q : P) (e : pair_states * list A) : Prop :=
  exact_after p (rev e.2) e.1.1 ∧ exact_after q (rev e.2) e.1.2 ∧ p ⇓ᶜᵒ rev e.2 ∧ q ⇓ᶜᵒ rev e.2.

Lemma reverse_eq_rev {X : Type} (l : list X) : reverse l = rev l.
Proof. unfold reverse. rewrite rev_append_rev, app_nil_r. reflexivity. Qed.

Lemma entry_f1 {p q : P} {l : list (pair_states * list A)} (hl : ∀ e, e ∈ l → entry_facts p q e) e (m : e ∈ l) :
  exact_after p (reverse e.2) e.1.1.
Proof. rewrite reverse_eq_rev. exact (proj1 (hl e m)). Qed.

Lemma entry_f2 {p q : P} {l : list (pair_states * list A)} (hl : ∀ e, e ∈ l → entry_facts p q e) e (m : e ∈ l) :
  exact_after q (reverse e.2) e.1.2.
Proof. rewrite reverse_eq_rev. exact (proj1 (proj2 (hl e m))). Qed.

Lemma entry_f3 {p q : P} {l : list (pair_states * list A)} (hl : ∀ e, e ∈ l → entry_facts p q e) e (m : e ∈ l) :
  p ⇓ᶜᵒ reverse e.2.
Proof. rewrite reverse_eq_rev. exact (proj1 (proj2 (proj2 (hl e m)))). Qed.

Lemma entry_f4 {p q : P} {l : list (pair_states * list A)} (hl : ∀ e, e ∈ l → entry_facts p q e) e (m : e ∈ l) :
  q ⇓ᶜᵒ reverse e.2.
Proof. rewrite reverse_eq_rev. exact (proj2 (proj2 (proj2 (hl e m)))). Qed.

Fixpoint test_entries (k : nat) (p q : P) (l : list (pair_states * list A)) :
  (∀ e, e ∈ l → entry_facts p q e) → option (distinguishing_test_of p q) :=
  match l with
  | [] => λ _, None
  | e :: l' => λ hl,
      let m := list_elem_of_here e l' in
      match refute k p q 1 (reverse e.2) e.1.1 e.1.2 (entry_f1 hl e m) (entry_f2 hl e m) (entry_f3 hl e m) (entry_f4 hl e m) with
      | Some d => Some d
      | None => test_entries k p q l' (λ e' m, hl e' (list_elem_of_further e' e l' m))
      end
  end.

Lemma test_entries_some (k : nat) (p q : P) (l : list (pair_states * list A)) hl e :
  e ∈ l → (∀ hX hY hp hq, refute k p q 1 (reverse e.2) e.1.1 e.1.2 hX hY hp hq ≠ None) → test_entries k p q l hl ≠ None.
Proof.
  revert hl. induction l as [| e0 l IH]; intros hl m hr; [inversion m |]. cbn [test_entries].
  match goal with |- context [refute k p q 1 (reverse e0.2) e0.1.1 e0.1.2 ?a ?b ?c ?d] => destruct (refute k p q 1 (reverse e0.2) e0.1.1 e0.1.2 a b c d) eqn:E end;
    [congruence |].
  apply elem_of_cons in m as [-> | m]; [exfalso; exact (hr _ _ _ _ E) | exact (IH _ m hr)].
Qed.

Definition fallback (k : nat) (p q : P) (E : list (pair_states * list A)) (hE : ∀ e, e ∈ E → entry_facts p q e) : answer p q :=
  match test_entries k p q E hE with
  | Some (exist _ (s, t) h') => Fails s t h'
  | None => Unknown_answer
  end.

Definition decide_false (m k n : nat) (p q : P) (E : list (pair_states * list A)) (hE : ∀ e, e ∈ E → entry_facts p q e) : answer p q :=
  match open_root k p with
  | Opened Xp hXp hp =>
      match open_root k q with
      | Opened Xq hXq hq =>
          match refute k p q n [] Xp Xq hXp hXq hp hq with
          | Some (exist _ (s, t) h') => Fails s t h'
          | None => fallback k p q E hE
          end
      | Diverged hn => Fails [] (ts_tc []) (conv_test_spec p q [] hp hn)
      | Unknown => fallback k p q E hE
      end
  | _ => fallback k p q E hE
  end.

(** With adequate budgets, the verdict is never unknown. *)

Lemma open_side_unknown' (k : nat) (x : P) (s : trace A) (Y : list P) hgen hcv :
  open_side k x s Y hgen hcv = Unknown → τbounded k Y = false ∧ div_set k Y = false.
Proof.
  unfold open_side. generalize (eq_refl (τbounded k Y)). generalize (τbounded k Y) at 2 3.
  intros b e. destruct b; [discriminate |].
  generalize (eq_refl (div_set k Y)). generalize (div_set k Y) at 2 3.
  intros d e'. destruct d; [discriminate | intros _; split; assumption].
Qed.

Lemma open_side_bounded (k : nat) (x : P) (s : trace A) (Y : list P) hgen hcv :
  τbounded k Y = true → ∃ X hX hx, open_side k x s Y hgen hcv = Opened X hX hx.
Proof.
  intros hb. destruct (open_side k x s Y hgen hcv) as [X hX hx | hn |] eqn:E.
  - eauto.
  - exfalso. exact (hn (hcv (τbounded_terminate k Y hb))).
  - apply open_side_unknown' in E as [e _]. congruence.
Qed.

Lemma open_side_div (k : nat) (x : P) (s : trace A) (Y : list P) hgen hcv :
  τbounded k Y = false → div_set k Y = true → ∃ hn, open_side k x s Y hgen hcv = Diverged hn.
Proof.
  intros hb hd. destruct (open_side k x s Y hgen hcv) as [X hX hx | hn |] eqn:E.
  - exfalso. destruct (div_set_spec k Y hd) as (y & my & hy). apply hy.
    apply (cocnv_cowt_s_terminate x y s hx), hgen. exists y. split; [exact my | apply cowt_nil].
  - eauto.
  - apply open_side_unknown' in E as [_ e]. congruence.
Qed.

Lemma open_side_bounded_eq (k : nat) (x : P) (s : trace A) (Y : list P) hgen hcv :
  τbounded k Y = true → ∃ hX hx, open_side k x s Y hgen hcv = Opened (τclose k Y) hX hx.
Proof.
  intros hb. unfold open_side. generalize (eq_refl (τbounded k Y)). generalize (τbounded k Y) at 2 3.
  intros b e. destruct b; [eexists _, _; reflexivity | congruence].
Qed.

Definition entry_ok (k : nat) (p q : P) (e : pair_states * list A) : Prop :=
  ∃ hX hY hp hq, follow_rev k p q e.2 = Some (NodeAt e.1.1 e.1.2 hX hY hp hq).

Lemma entry_ok_child (k : nat) (p q : P) (e c : pair_states * list A) :
  entry_ok k p q e → c ∈ children_tr k e → entry_ok k p q c.
Proof.
  intros (hX & hY & hp & hq & E) m. unfold children_tr in m. apply list_elem_of_omap in m as (μ & _ & h).
  destruct (child_pair k e.1 μ) as [cp |] eqn:ec; [| discriminate]. injection h as <-. simpl.
  rewrite child_pair_unfold in ec.
  destruct (τbounded k (ext e.1.1 μ)) eqn:b1, (τbounded k (ext e.1.2 μ)) eqn:b2; simpl in ec; try discriminate.
  injection ec as <-. unfold entry_ok. cbn [fst snd follow_rev]. rewrite E. unfold open_child.
  destruct (open_side_bounded_eq k p (rev e.2 ++ [μ]) (ext e.1.1 μ) (child_gen p (rev e.2) e.1.1 hX μ)
              (child_cv p (rev e.2) μ _ hp (child_gen p (rev e.2) e.1.1 hX μ)) b1) as (hXp & hp' & E1).
  destruct (open_side_bounded_eq k q (rev e.2 ++ [μ]) (ext e.1.2 μ) (child_gen q (rev e.2) e.1.2 hY μ)
              (child_cv q (rev e.2) μ _ hq (child_gen q (rev e.2) e.1.2 hY μ)) b2) as (hXq & hq' & E2).
  rewrite E1, E2. eexists _, _, _, _. reflexivity.
Qed.

Lemma entry_ok_root (k : nat) (p q : P) c : root_pair k p q = Some c → entry_ok k p q (c, []).
Proof.
  intros h. rewrite root_pair_unfold in h.
  destruct (τbounded k [p]) eqn:b1, (τbounded k [q]) eqn:b2; simpl in h; try discriminate.
  injection h as <-. unfold entry_ok. cbn [fst snd follow_rev]. unfold open_root.
  destruct (open_side_bounded_eq k p [] [p] (root_gen p) (root_cv p) b1) as (hXp & hp & E1).
  destruct (open_side_bounded_eq k q [] [q] (root_gen q) (root_cv q) b2) as (hXq & hq & E2).
  rewrite E1, E2. eexists _, _, _, _. reflexivity.
Qed.

Lemma bfs_tr_entries (k : nat) (Q : pair_states * list A → Prop) (hQ : ∀ e c, Q e → c ∈ children_tr k e → Q c) :
  ∀ m seen visited work, (∀ e, e ∈ visited → Q e) → (∀ e, e ∈ work → Q e) → ∀ e, e ∈ bfs_tr k m seen visited work → Q e.
Proof.
  induction m as [| m IH]; intros seen visited work hv hw x hx; simpl in hx; [exact (hv x hx) |].
  destruct work as [| y work']; [exact (hv x hx) |].
  destruct (idx_mem (canon y.1) seen).
  - apply (IH seen visited work' hv); [intros z hz; apply hw, list_elem_of_further, hz | exact hx].
  - apply (IH (idx_add (canon y.1) seen) (y :: visited) (work' ++ children_tr k y)); [| | exact hx].
    + intros z [-> | hz]%elem_of_cons; [apply hw, list_elem_of_here | exact (hv z hz)].
    + intros z [hz | hz]%elem_of_app; [apply hw, list_elem_of_further, hz |].
      apply (hQ y z); [apply hw, list_elem_of_here | exact hz].
Qed.

Lemma graph_entries_ok (m k : nat) (p q : P) : ∀ e, e ∈ graph_entries m k p q → entry_ok k p q e.
Proof.
  unfold graph_entries. destruct (root_pair k p q) as [c |] eqn:ec; [| intros e h; inversion h].
  apply bfs_tr_entries; [apply entry_ok_child | intros e h; inversion h |].
  intros e h. apply list_elem_of_singleton in h as ->. exact (entry_ok_root k p q c ec).
Qed.

Lemma graph_entries_facts (m k : nat) (p q : P) : ∀ e, e ∈ graph_entries m k p q → entry_facts p q e.
Proof. intros e me. destruct (graph_entries_ok m k p q e me) as (hX & hY & hp & hq & _). split_and!; assumption. Qed.

Definition expand (k : nat) (e : pair_states * list A) : list (pair_states * list A) * bool :=
  let cs := (λ μ, (μ, child_pair k e.1 μ)) <$> next_list (explored e.1) e.1.2 in
  (omap (λ μc, (λ c, (c, μc.1 :: e.2)) <$> μc.2) cs,
   local_ok e.1 && forallb (λ μc, match μc.2 with Some _ => true | None => div_set k (ext e.1.1 μc.1) end) cs).

Lemma expand_fst (k : nat) (e : pair_states * list A) : (expand k e).1 = children_tr k e.
Proof.
  unfold expand, children_tr. simpl. generalize (next_list (explored e.1) e.1.2). intros l.
  induction l as [| μ l IH]; simpl; [reflexivity |]. destruct (child_pair k e.1 μ); simpl; [f_equal |]; exact IH.
Qed.

Lemma expand_snd (k : nat) (e : pair_states * list A) :
  (expand k e).2 = true ↔ local_ok e.1 = true ∧
    ∀ μ, μ ∈ next_list (explored e.1) e.1.2 → child_pair k e.1 μ = None → div_set k (ext e.1.1 μ) = true.
Proof.
  unfold expand. simpl. rewrite andb_true_iff, forallb_forall. split.
  - intros [h1 h2]. split; [exact h1 |]. intros μ m hn.
    specialize (h2 (μ, child_pair k e.1 μ) (proj1 (list_elem_of_In _ _) (list_elem_of_fmap_2 (λ μ, (μ, child_pair k e.1 μ)) _ _ m))).
    simpl in h2. rewrite hn in h2. exact h2.
  - intros [h1 h2]. split; [exact h1 |]. intros μc mc. apply list_elem_of_In, list_elem_of_fmap in mc as (μ & -> & m). simpl.
    destruct (child_pair k e.1 μ) eqn:ec; [reflexivity | exact (h2 μ m ec)].
Qed.

Fixpoint bfs_full (k m : nat) (seen : gmap (N * N) (list pair_states)) (visited work : list (pair_states * list A)) (ok : bool) :
  list (pair_states * list A) * gmap (N * N) (list pair_states) * list (pair_states * list A) * bool :=
  match m with
  | 0 => (visited, seen, work, ok)
  | S m =>
      match work with
      | [] => (visited, seen, [], ok)
      | e :: work' =>
          let c := canon e.1 in
          if idx_mem c seen then bfs_full k m seen visited work' ok
          else let x := expand k e in bfs_full k m (idx_add c seen) (e :: visited) (work' ++ x.1) (ok && x.2)
      end
  end.

Lemma bfs_full_visited (k : nat) : ∀ m seen visited work ok, (bfs_full k m seen visited work ok).1.1.1 = bfs_tr k m seen visited work.
Proof.
  induction m as [| m IH]; intros seen visited work ok; [reflexivity |]. cbn [bfs_full bfs_tr].
  destruct work as [| e work']; [reflexivity |]. destruct (idx_mem (canon e.1) seen); [apply IH |].
  rewrite IH, expand_fst. reflexivity.
Qed.

Lemma bfs_full_seen (k : nat) : ∀ m seen visited work ok, seen = canon_index (map fst visited) →
  (bfs_full k m seen visited work ok).1.1.2 = canon_index (map fst (bfs_full k m seen visited work ok).1.1.1).
Proof.
  induction m as [| m IH]; intros seen visited work ok hs; [exact hs |]. cbn [bfs_full].
  destruct work as [| e work']; [exact hs |]. destruct (idx_mem (canon e.1) seen); [apply IH, hs |].
  apply IH. rewrite hs. reflexivity.
Qed.

Lemma bfs_full_mem (k m : nat) seen (visited work : list (pair_states * list A)) ok e :
  e ∈ visited → e ∈ (bfs_full k m seen visited work ok).1.1.1.
Proof. intros me. rewrite bfs_full_visited. apply bfs_tr_mono, me. Qed.

Lemma bfs_full_ok_sound (k : nat) : ∀ m seen visited work ok,
  (bfs_full k m seen visited work ok).2 = true →
  ok = true ∧ ∀ e, e ∈ (bfs_full k m seen visited work ok).1.1.1 → e ∈ visited ∨ (expand k e).2 = true.
Proof.
  induction m as [| m IH]; intros seen visited work ok.
  - simpl. intros h. split; [exact h | intros e me; left; exact me].
  - cbn [bfs_full]. destruct work as [| e work'].
    + simpl. intros h. split; [exact h | intros e me; left; exact me].
    + destruct (idx_mem (canon e.1) seen); [apply IH |]. intros h. destruct (IH _ _ _ _ h) as [h1 h3].
      apply andb_true_iff in h1 as [h1 h2]. split; [exact h1 |]. intros e' me'.
      destruct (h3 e' me') as [m' | m']; [| right; exact m'].
      apply elem_of_cons in m' as [-> | m']; [right; exact h2 | left; exact m'].
Qed.

Lemma bfs_full_ok_complete (k : nat) : ∀ m seen visited work ok, ok = true →
  (∀ e, e ∈ (bfs_full k m seen visited work ok).1.1.1 → (expand k e).2 = true) →
  (bfs_full k m seen visited work ok).2 = true.
Proof.
  induction m as [| m IH]; intros seen visited work ok hok h; [exact hok |]. revert h. cbn [bfs_full].
  destruct work as [| e work']; [intros _; exact hok |].
  destruct (idx_mem (canon e.1) seen); [apply IH, hok |]. intros h. apply IH; [| exact h].
  apply andb_true_iff. split; [exact hok |]. exact (h e (bfs_full_mem k m _ (e :: visited) _ _ e (list_elem_of_here _ _))).
Qed.

Lemma bfs_full_closed (k : nat) : ∀ m seen visited work ok, seen = canon_index (map fst visited) →
  (∀ e c, e ∈ visited → c ∈ children_tr k e → in_graph c.1 (map fst visited) = true ∨ c ∈ work) →
  (∀ e c, e ∈ (bfs_full k m seen visited work ok).1.1.1 → c ∈ children_tr k e →
     in_graph c.1 (map fst (bfs_full k m seen visited work ok).1.1.1) = true ∨ c ∈ (bfs_full k m seen visited work ok).1.2) ∧
  (∀ c, c ∈ work → in_graph c.1 (map fst (bfs_full k m seen visited work ok).1.1.1) = true ∨ c ∈ (bfs_full k m seen visited work ok).1.2).
Proof.
  induction m as [| m IH]; intros seen v w ok hs hinv.
  - split; [exact hinv | intros c mc; right; exact mc].
  - cbn [bfs_full]. destruct w as [| e w'].
    + split; [| intros c mc; inversion mc].
      intros e c me mc. destruct (hinv e c me mc) as [h | h]; [left; exact h | inversion h].
    + destruct (idx_mem (canon e.1) seen) eqn:ge; rewrite hs, in_graph_set in ge.
      * destruct (IH seen v w' ok hs) as [h1 h2].
        { intros e0 c me0 mc. destruct (hinv e0 c me0 mc) as [h | h]; [left; exact h |].
          apply elem_of_cons in h as [-> | h]; [left; exact ge | right; exact h]. }
        split; [exact h1 |]. intros c mc. apply elem_of_cons in mc as [-> | mc]; [| exact (h2 c mc)].
        left. refine (in_graph_mono _ _ _ _ ge). intros y my. rewrite bfs_full_visited. exact (map_fst_mono k m _ v w' y my).
      * destruct (IH (idx_add (canon e.1) seen) (e :: v) (w' ++ (expand k e).1) (ok && (expand k e).2)) as [h1 h2].
        { rewrite hs. reflexivity. }
        { rewrite expand_fst. intros e0 c me0 mc. apply elem_of_cons in me0 as [-> | me0].
          - right. apply elem_of_app. right. exact mc.
          - destruct (hinv e0 c me0 mc) as [h | h].
            + left. apply (in_graph_mono _ (map fst v)); [| exact h]. intros y my. simpl. by apply list_elem_of_further.
            + apply elem_of_cons in h as [-> | h].
              * left. apply in_graph_refl. simpl. apply list_elem_of_here.
              * right. apply elem_of_app. left. exact h. }
        split; [exact h1 |]. intros c mc. apply elem_of_cons in mc as [-> | mc].
        -- left. refine (in_graph_mono _ (map fst (e :: v)) _ _ (in_graph_refl _ _ (list_elem_of_here _ _))).
           intros y my. rewrite bfs_full_visited. exact (map_fst_mono k m _ (e :: v) _ y my).
        -- apply h2. apply elem_of_app. left. exact mc.
Qed.

Lemma bfs_full_work (k : nat) (Q : pair_states * list A → Prop) : ∀ m seen visited work ok,
  (∀ c, c ∈ work → Q c ∨ ∃ e, e ∈ visited ∧ c ∈ children_tr k e) →
  ∀ c, c ∈ (bfs_full k m seen visited work ok).1.2 →
    Q c ∨ ∃ e, e ∈ (bfs_full k m seen visited work ok).1.1.1 ∧ c ∈ children_tr k e.
Proof.
  induction m as [| m IH]; intros seen v w ok hw c mc; [exact (hw c mc) |]. revert mc. cbn [bfs_full].
  destruct w as [| e w']; [intros mc; inversion mc |].
  destruct (idx_mem (canon e.1) seen); apply IH.
  - intros c' mc'. apply hw. by apply list_elem_of_further.
  - rewrite expand_fst. intros c' mc'. apply elem_of_app in mc' as [mc' | mc'].
    + destruct (hw c' (list_elem_of_further _ _ _ mc')) as [h | (e0 & me0 & h)]; [left; exact h |].
      right. exists e0. split; [by apply list_elem_of_further | exact h].
    + right. exists e. split; [apply list_elem_of_here | exact mc'].
Qed.

Definition fast_run (m k : nat) (p q : P) :
  list (pair_states * list A) * gmap (N * N) (list pair_states) * list (pair_states * list A) * bool :=
  match root_pair k p q with
  | Some c => bfs_full k m ∅ [] [(c, [])] true
  | None => ([], ∅, [], true)
  end.

Definition fast_check (k : nat) (p q : P) (seen : gmap (N * N) (list pair_states)) (work : list (pair_states * list A))
  (ok : bool) : bool :=
  match root_pair k p q with
  | Some _ => ok && forallb (λ c, idx_mem (canon c.1) seen) work
  | None => div_set k [p]
  end.

Definition fast_certify (m k : nat) (p q : P) : bool :=
  let r := fast_run m k p q in fast_check k p q r.1.1.2 r.1.2 r.2.

Lemma fast_run_visited (m k : nat) (p q : P) : (fast_run m k p q).1.1.1 = graph_entries m k p q.
Proof. unfold fast_run, graph_entries. destruct (root_pair k p q); [apply bfs_full_visited | reflexivity]. Qed.

Lemma fast_facts (m k : nat) (p q : P) : ∀ e, e ∈ (fast_run m k p q).1.1.1 → entry_facts p q e.
Proof. rewrite fast_run_visited. exact (graph_entries_facts m k p q). Qed.

Lemma fast_sound (m k : nat) (p q : P) : fast_certify m k p q = true → certify m k p q = true.
Proof.
  unfold fast_certify, fast_check, certify, pair_graph. cbv zeta. rewrite <- fast_run_visited. unfold fast_run.
  destruct (root_pair k p q) as [c |] eqn:er.
  2: { intros h. unfold certified, certified_in, root_ok. rewrite er, h. reflexivity. }
  pose proof (bfs_full_seen k m ∅ [] [(c, [])] true eq_refl) as hs.
  destruct (bfs_full_closed k m ∅ [] [(c, [])] true eq_refl) as [hcl hw]; [intros e c' me; inversion me |].
  remember (bfs_full k m ∅ [] [(c, [])] true) as r eqn:Er.
  intros h. apply andb_true_iff in h as [hok hfin].
  assert (hin : ∀ c', c' ∈ r.1.2 → in_graph c'.1 (map fst r.1.1.1) = true).
  { intros c' mc. rewrite forallb_forall in hfin. specialize (hfin c' (proj1 (list_elem_of_In _ _) mc)).
    rewrite hs, in_graph_set in hfin. exact hfin. }
  assert (hflags : ∀ e, e ∈ r.1.1.1 → (expand k e).2 = true).
  { intros e me. subst r. destruct (bfs_full_ok_sound k m ∅ [] [(c, [])] true hok) as [_ hf].
    destruct (hf e me) as [m0 | h']; [inversion m0 | exact h']. }
  unfold certified, certified_in. apply andb_true_iff. split.
  - unfold root_ok. rewrite er. apply orb_true_iff. right. rewrite in_graph_set.
    destruct (hw (c, []) (list_elem_of_here _ _)) as [h' | h']; [exact h' | exact (hin _ h')].
  - apply forallb_forall. intros x mx'. pose proof (proj2 (list_elem_of_In _ _) mx') as mx.
    apply list_elem_of_fmap in mx as (e & -> & me). destruct (proj1 (expand_snd k e) (hflags e me)) as [hl hdiv].
    apply andb_true_iff. split; [exact hl |]. apply forallb_forall. intros μ mμ'. pose proof (proj2 (list_elem_of_In _ _) mμ') as mμ.
    unfold child_ok. destruct (child_pair k e.1 μ) as [c' |] eqn:ec.
    + apply orb_true_iff. left. rewrite in_graph_set.
      assert (mc : (c', μ :: e.2) ∈ children_tr k e).
      { unfold children_tr. apply list_elem_of_omap. exists μ. split; [exact mμ | rewrite ec; reflexivity]. }
      destruct (hcl e _ me mc) as [h' | h']; [exact h' | exact (hin _ h')].
    + apply orb_true_iff. right. exact (hdiv μ mμ ec).
Qed.

Lemma fast_complete (m k : nat) (p q : P) :
  adequate m k p q = true → certify m k p q = true → fast_certify m k p q = true.
Proof.
  intros ha hc. unfold adequate in ha. cbv zeta in ha.
  apply andb_true_iff in ha as [ha hall]. apply andb_true_iff in ha as [_ hroot].
  unfold certify in hc. unfold fast_certify, fast_check, fast_run in *. cbv zeta. unfold pair_graph, graph_entries in *.
  destruct (root_pair k p q) as [c |] eqn:er.
  2: { unfold certified, certified_in, root_ok in hc. rewrite er in hc. simpl in hc.
       apply andb_true_iff in hc as [hc _]. rewrite orb_false_r in hc. exact hc. }
  rewrite <- (bfs_full_visited k m ∅ [] [(c, [])] true) in hall, hroot, hc.
  pose proof (bfs_full_seen k m ∅ [] [(c, [])] true eq_refl) as hs.
  remember (bfs_full k m ∅ [] [(c, [])] true) as r eqn:Er.
  set (R := map fst r.1.1.1) in *.
  apply andb_true_iff. split.
  - subst r. apply bfs_full_ok_complete; [reflexivity |]. intros e me. apply expand_snd.
    unfold certified, certified_in in hc. apply andb_true_iff in hc as [_ hc]. rewrite forallb_forall in hc.
    specialize (hc e.1 (proj1 (list_elem_of_In _ _) (list_elem_of_fmap_2 fst _ e me))). apply andb_true_iff in hc as [hl hc].
    split; [exact hl |]. intros μ mμ hn. rewrite forallb_forall in hc. specialize (hc μ (proj1 (list_elem_of_In _ _) mμ)).
    unfold child_ok in hc. rewrite hn in hc. exact hc.
  - apply forallb_forall. intros c' mc'. pose proof (proj2 (list_elem_of_In _ _) mc') as mc. rewrite hs, in_graph_set. fold R.
    assert (hwk := bfs_full_work k (λ c0, c0 = (c, [])) m ∅ [] [(c, [])] true).
    rewrite <- Er in hwk. destruct (hwk ltac:(intros c0 m0; left; apply list_elem_of_singleton in m0; exact m0) c' mc) as [-> | (e & me & hce)].
    + exact hroot.
    + rewrite forallb_forall in hall. specialize (hall e.1 (proj1 (list_elem_of_In _ _) (list_elem_of_fmap_2 fst _ e me))).
      unfold children_tr in hce. apply list_elem_of_omap in hce as (μ & mμ & h').
      destruct (child_pair k e.1 μ) as [c1 |] eqn:ec; [| discriminate]. injection h' as <-.
      rewrite forallb_forall in hall. specialize (hall μ (proj1 (list_elem_of_In _ _) mμ)).
      rewrite ec in hall. apply andb_true_iff in hall as [_ hall]. exact hall.
Qed.

Definition decide_preorder (m k n : nat) (p q : P) : answer p q :=
  let r := fast_run m k p q in
  match fast_check k p q r.1.1.2 r.1.2 r.2 as b return fast_check k p q r.1.1.2 r.1.2 r.2 = b → answer p q with
  | true => λ h, Holds (certify_spec m k p q (fast_sound m k p q h))
  | false => λ _, decide_false m k n p q r.1.1.1 (fast_facts m k p q)
  end eq_refl.

Inductive result : Type :=
| R_holds
| R_fails (s : trace A) (t : T)
| R_unknown.

Definition verdict (m k n : nat) (p q : P) : result :=
  match decide_preorder m k n p q with
  | Holds _ => R_holds
  | Fails s t _ => R_fails s t
  | Unknown_answer => R_unknown
  end.

Lemma verdict_holds (m k n : nat) (p q : P) : verdict m k n p q = R_holds → ∀ s, co_conditions p q s.
Proof. unfold verdict. destruct (decide_preorder m k n p q); [done | discriminate | discriminate]. Qed.

Lemma verdict_fails (m k n : nat) (p q : P) (s : trace A) (t : T) : verdict m k n p q = R_fails s t → ts_must p t ∧ ¬ ts_must q t.
Proof.
  unfold verdict. destruct (decide_preorder m k n p q) as [| s' t' h |]; [discriminate | | discriminate].
  intros e. injection e as -> ->. exact h.
Qed.

Lemma distinguish_sets_none (p q : P) (s : trace A) (hp : p ⇓ᶜᵒ s) (Xp Xq : list P) hXp hXq :
  distinguish_sets p q s hp Xp Xq hXp hXq = None → local_ok (Xp, Xq) = true.
Proof.
  intros hn. pose proof (distinguish_list_none p q s hp _ _ (stable_list Xq) _ hn) as h.
  unfold local_ok. apply forallb_forall. intros y my'. pose proof (proj2 (list_elem_of_In _ _) my') as my.
  destruct (h y my) as (p' & wp & stp & sub).
  apply existsb_exists. exists p'. split.
  - apply list_elem_of_In, (stable_list_spec p s Xp hXp). split; assumption.
  - apply dichotomy_inl, sub.
Qed.

Lemma child_test_div (k : nat) (p q : P) (rec : rec_type p q) (s : trace A) (Xp Xq : list P)
  hXp hXq hp hq (μ : A) :
  τbounded k (ext Xp μ) = true → τbounded k (ext Xq μ) = false → div_set k (ext Xq μ) = true →
  child_test k p q rec s Xp Xq hXp hXq hp hq μ ≠ None.
Proof.
  intros b1 b2 d2. unfold child_test, open_child.
  destruct (open_side_bounded k p (s ++ [μ]) (ext Xp μ) (child_gen p s Xp hXp μ)
              (child_cv p s μ _ hp (child_gen p s Xp hXp μ)) b1) as (Xp' & hXp' & hp' & E1).
  rewrite E1.
  destruct (open_side_div k q (s ++ [μ]) (ext Xq μ) (child_gen q s Xq hXq μ)
              (child_cv q s μ _ hq (child_gen q s Xq hXq μ)) b2 d2) as (hn & E2).
  rewrite E2. congruence.
Qed.

Lemma forallb_false {X : Type} (f : X → bool) (l : list X) : forallb f l = false → ∃ x, In x l ∧ f x = false.
Proof.
  induction l as [| x l IH]; simpl; [discriminate |]. intros h. apply andb_false_iff in h as [h | h].
  - exists x. split; [left; reflexivity | exact h].
  - destruct (IH h) as (y & m & hy). exists y. split; [right; exact m | exact hy].
Qed.

Lemma decide_preorder_true (m k n : nat) (p q : P) :
  fast_certify m k p q = true → ∃ h, decide_preorder m k n p q = Holds h.
Proof.
  intros h. unfold fast_certify in h. cbv zeta in h. unfold decide_preorder. cbv zeta. generalize (eq_refl (fast_check k p q (fast_run m k p q).1.1.2 (fast_run m k p q).1.2 (fast_run m k p q).2)).
  generalize (fast_check k p q (fast_run m k p q).1.1.2 (fast_run m k p q).1.2 (fast_run m k p q).2) at 2 3. intros b e. destruct b; [eexists; reflexivity | congruence].
Qed.

Lemma decide_preorder_false (m k n : nat) (p q : P) :
  fast_certify m k p q = false → decide_preorder m k n p q = decide_false m k n p q (fast_run m k p q).1.1.1 (fast_facts m k p q).
Proof.
  intros h. unfold fast_certify in h. cbv zeta in h. unfold decide_preorder. cbv zeta. generalize (eq_refl (fast_check k p q (fast_run m k p q).1.1.2 (fast_run m k p q).1.2 (fast_run m k p q).2)).
  generalize (fast_check k p q (fast_run m k p q).1.1.2 (fast_run m k p q).1.2 (fast_run m k p q).2) at 2 3. intros b e. destruct b; [congruence | reflexivity].
Qed.

Theorem verdict_complete (m k n : nat) (p q : P) :
  adequate m k p q = true → verdict m k n p q = R_holds ∨ ∃ s t, verdict m k n p q = R_fails s t.
Proof.
  intros ha. destruct (fast_certify m k p q) eqn:hf.
  { left. unfold verdict. destruct (decide_preorder_true m k n p q hf) as (h & ->). reflexivity. }
  right. unfold verdict. rewrite (decide_preorder_false m k n p q hf).
  generalize (fast_facts m k p q). rewrite fast_run_visited. intros hE.
  destruct (certify m k p q) eqn:hc.
  { exfalso. rewrite (fast_complete m k p q ha hc) in hf. discriminate. }
  assert (ha' := ha). unfold adequate in ha'. set (R := pair_graph m k p q) in *.
  apply andb_true_iff in ha' as [ha' hall]. apply andb_true_iff in ha' as [ha' hroot].
  apply andb_true_iff in ha' as [hap haq]. unfold adeq in hap, haq.
  assert (bp : τbounded k [p] = true).
  { apply orb_true_iff in hap as [bp | dp]; [exact bp |]. exfalso.
    assert (τbounded k [p] = false) as nb.
    { destruct (τbounded k [p]) eqn:e; [| reflexivity]. exfalso.
      destruct (div_set_spec k _ dp) as (r & hr%list_elem_of_singleton & hn). subst r.
      exact (hn (τbounded_terminate k _ e p (list_elem_of_here _ _))). }
    assert (R = []) as eR by (subst R; unfold pair_graph, graph_entries; rewrite root_pair_unfold, nb; reflexivity).
    unfold certify in hc. fold R in hc. rewrite eR in hc. unfold certified, certified_in, root_ok in hc.
    rewrite dp in hc. discriminate. }
  unfold decide_false.
  destruct (open_side_bounded k p [] [p] (root_gen p) (root_cv p) bp) as (Xp & hXp & hp & Ep).
  unfold open_root at 1. rewrite Ep.
  apply orb_true_iff in haq as [bq | dq].
  2: { destruct (τbounded k [q]) eqn:bq.
       - exfalso. destruct (div_set_spec k _ dq) as (r & hr%list_elem_of_singleton & hn). subst r.
         exact (hn (τbounded_terminate k _ bq q (list_elem_of_here _ _))).
       - destruct (open_side_div k q [] [q] (root_gen q) (root_cv q) bq dq) as (hn & Eq).
         unfold open_root. rewrite Eq. eauto. }
  destruct (open_side_bounded k q [] [q] (root_gen q) (root_cv q) bq) as (Xq & hXq & hq & Eq).
  unfold open_root. rewrite Eq.
  destruct (refute k p q n [] Xp Xq hXp hXq hp hq) as [[[s t] h'] |]; [eauto |].
  unfold fallback. destruct (test_entries k p q (graph_entries m k p q) hE) as [[[s t] h'] |] eqn:et;
    [eauto | exfalso].
  assert (hrp : root_pair k p q = Some (τclose k [p], τclose k [q])) by (rewrite root_pair_unfold, bp, bq; reflexivity).
  unfold certify in hc. fold R in hc. unfold certified, certified_in in hc. apply andb_false_iff in hc as [hc | hc].
  { unfold root_ok in hc. rewrite hrp in hroot, hc. apply orb_false_iff in hc as [_ hc]. rewrite in_graph_set in hc. congruence. }
  apply forallb_false in hc as (x & mx' & hx). pose proof (proj2 (list_elem_of_In _ _) mx') as mx.
  subst R. unfold pair_graph in mx. apply list_elem_of_fmap in mx as (e & -> & me).
  assert (htest : ∀ hX hY hpe hqe, refute k p q 1 (reverse e.2) e.1.1 e.1.2 hX hY hpe hqe ≠ None).
  { intros hX hY hpe hqe. simpl.
    destruct (distinguish_sets _ _ _ _ _ _ _ _) as [d |] eqn:ed; [congruence |].
    apply andb_false_iff in hx as [hx | hx].
    - exfalso. pose proof (distinguish_sets_none p q _ hpe e.1.1 e.1.2 hX hY ed) as hl.
      rewrite <- surjective_pairing in hl. congruence.
    - apply forallb_false in hx as (μ & mμ' & hμ). pose proof (proj2 (list_elem_of_In _ _) mμ') as mμ.
      rewrite forallb_forall in hall. specialize (hall e.1 (proj1 (list_elem_of_In _ _) (list_elem_of_fmap_2 fst _ e me))).
      rewrite forallb_forall in hall. specialize (hall μ mμ').
      apply andb_true_iff in hall as [hall hc2]. apply andb_true_iff in hall as [a1 a2]. unfold adeq in a1, a2.
      unfold child_ok in hμ. rewrite orb_comm in hμ. apply orb_false_iff in hμ as [hd1 hcp].
      rewrite hd1, orb_false_r in a1.
      apply (first_some_some _ _ μ); [destruct e.1; exact mμ |].
      destruct (τbounded k (ext e.1.2 μ)) eqn:b2.
      + exfalso. rewrite child_pair_unfold in hcp, hc2. rewrite a1, b2 in hcp, hc2. cbn [andb] in hcp, hc2. rewrite in_graph_set in hcp. congruence.
      + rewrite orb_false_l in a2. exact (child_test_div k p q _ _ _ _ hX hY hpe hqe μ a1 b2 a2). }
  exact (test_entries_some k p q _ _ e me htest et).
Qed.

End Verdict.
(* end hide *)
