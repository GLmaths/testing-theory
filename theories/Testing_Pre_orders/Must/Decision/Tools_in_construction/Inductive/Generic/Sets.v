(* begin hide *)
From Stdlib Require Import Lia.
From stdpp Require Import base countable gmap list sets.
From TestingTheory Require Import ActTau gLts SyncActions Termination Subset_Act InListPropHelper
  coWeakTransition coConvergence coFiniteImage
  Decision.Tools_in_construction.Inductive.Generic.Helpers Decision.Tools_in_construction.Inductive.Generic.Bisim
  Decision.Tools_in_construction.Inductive.Generic.Interface.
Import ListNotations.

Section Sets.

Context `{TS : TraceSearchLang P A Atom PreAct T}.

Definition co_conditions (p q : P) (s : trace A) : Prop :=
  (p ⇓ᶜᵒ s → q ⇓ᶜᵒ s) ∧
  (∀ q', p ⇓ᶜᵒ s → q ⟹ᶜᵒ[s] q' → q' ↛ →
     ∃ p', p ⟹ᶜᵒ[s] p' ∧ p' ↛ ∧ ⌈ ts_Γ ⌉ (coR p') ⊆ ⌈ ts_Γ ⌉ (coR q')).

Definition in_atoms (vals : list Atom) (μ : A) : Prop := ∀ a, a ∈ ts_atoms_act μ → a ∈ vals.

#[global] Instance in_atoms_dec vals μ : Decision (in_atoms vals μ).
Proof.
  unfold in_atoms. destruct (decide (Forall (λ a, a ∈ vals) (ts_atoms_act μ))) as [h | h].
  - left. intros a m. rewrite Forall_forall in h. exact (h a m).
  - right. intros h'. apply h. rewrite Forall_forall. exact h'.
Defined.

Definition next_list (vals : list Atom) (X : list P) : list A :=
  remove_dups (flat_map (ts_next vals) X).

Lemma next_list_spec (vals : list Atom) (X : list P) p (μ : A) (μ' : A) q :
  p ∈ X → sync μ' μ → p ⟶[μ'] q → in_atoms vals μ → μ ∈ next_list vals X.
Proof.
  intros hp duo l hv. apply elem_of_remove_dups, elem_of_flat_map_list. exists p.
  split; [exact hp | exact (ts_next_spec vals p μ μ' q duo l hv)].
Qed.

(** States and transitions on sets. *)

Definition τsucc (X : list P) : list P := remove_dups (flat_map ts_tau_next X).

Definition ext (X : list P) (μ : A) : list P := remove_dups (flat_map (λ x, ts_co_next x μ) X).

Fixpoint τbounded (k : nat) (X : list P) : bool :=
  match k with
  | 0 => bool_decide (τsucc X = [])
  | S k => τbounded k (τsucc X)
  end.

Fixpoint τclose (k : nat) (X : list P) : list P :=
  match k with
  | 0 => X
  | S k => remove_dups (X ++ τclose k (τsucc X))
  end.

Fixpoint τclose_b (k : nat) (X : list P) : option (list P) :=
  match k with
  | 0 => if bool_decide (τsucc X = []) then Some X else None
  | S k => (λ Z, remove_dups (X ++ Z)) <$> τclose_b k (τsucc X)
  end.

Lemma τclose_b_eq (k : nat) : ∀ (X : list P), τclose_b k X = if τbounded k X then Some (τclose k X) else None.
Proof.
  induction k as [| k IH]; intros X; simpl; [destruct (bool_decide _); reflexivity |].
  rewrite IH. destruct (τbounded k (τsucc X)); reflexivity.
Qed.

Lemma τsucc_spec (X : list P) y : y ∈ τsucc X → ∃ x, x ∈ X ∧ x ⟶ y.
Proof.
  intros m. apply elem_of_remove_dups, elem_of_flat_map_list in m as (x & mx & m).
  exists x. split; [exact mx | apply ts_tau_next_spec, m].
Qed.

Lemma tau_succ_mem (X : list P) p q : p ∈ X → p ⟶ q → q ∈ τsucc X.
Proof.
  intros hp l. apply elem_of_remove_dups, elem_of_flat_map_list. exists p.
  split; [exact hp | apply ts_tau_next_spec, l].
Qed.

Lemma τbounded_terminate (k : nat) : ∀ (X : list P), τbounded k X = true → ∀ y, y ∈ X → y ⤓.
Proof.
  induction k as [| k IH]; intros X h p hp; simpl in h.
  - apply bool_decide_eq_true in h. constructor. intros q l.
    exfalso. pose proof (tau_succ_mem X p q hp l) as m. rewrite h in m. inversion m.
  - constructor. intros q l. exact (IH _ h q (tau_succ_mem X p q hp l)).
Qed.

Lemma τclose_incl (k : nat) (X : list P) y : y ∈ X → y ∈ τclose k X.
Proof. intros m. destruct k; simpl; [exact m |]. apply elem_of_remove_dups, elem_of_app. left. exact m. Qed.

Lemma τclose_complete (k : nat) : ∀ (X : list P), τbounded k X = true → ∀ x t, x ∈ X → x ⟹ᶜᵒ t → t ∈ τclose k X.
Proof.
  induction k as [| k IH]; intros X h p t hp w; simpl in h.
  - apply bool_decide_eq_true in h.
    remember ([] : trace A) as s0 eqn:hs0 in w. revert hs0 hp.
    induction w as [p | s0 p p' t l w IHw | ]; intros hs0 hp; [exact hp | | discriminate].
    exfalso. pose proof (tau_succ_mem X p p' hp l) as m. rewrite h in m. inversion m.
  - remember ([] : trace A) as s0 eqn:hs0 in w. revert hs0 hp.
    induction w as [p | s0 p p' t l w IHw | ]; intros hs0 hp; [apply τclose_incl, hp | | discriminate].
    simpl. apply elem_of_remove_dups, elem_of_app. right. subst.
    exact (IH _ h p' t (tau_succ_mem X p p' hp l) w).
Qed.

Lemma τclose_nodup (k : nat) (X : list P) : NoDup X → NoDup (τclose k X).
Proof. intros h. destruct k; simpl; [exact h | apply NoDup_remove_dups]. Qed.

Lemma ext_nodup (X : list P) (μ : A) : NoDup (ext X μ).
Proof. apply NoDup_remove_dups. Qed.

Lemma τclose_sound (k : nat) : ∀ (X : list P) t, t ∈ τclose k X → ∃ x, x ∈ X ∧ x ⟹ᶜᵒ t.
Proof.
  induction k as [| k IH]; intros X t m.
  - exists t. split; [exact m | apply cowt_nil].
  - cbn [τclose] in m. apply elem_of_remove_dups, elem_of_app in m as [m | m].
    + exists t. split; [exact m | apply cowt_nil].
    + destruct (IH (τsucc X) t m) as (x1 & m1 & w).
      destruct (τsucc_spec X x1 m1) as (x & mx & l).
      exists x. split; [exact mx | exact (cowt_tau [] x x1 t l w)].
Qed.

Lemma ext_spec (X : list P) (μ : A) y : y ∈ ext X μ ↔ ∃ x, x ∈ X ∧ ∃ μ', sync μ' μ ∧ x ⟶[μ'] y.
Proof.
  unfold ext. rewrite elem_of_remove_dups, elem_of_flat_map_list. split.
  - intros (x & mx & m). exists x. split; [exact mx | apply ts_co_next_spec, m].
  - intros (x & mx & h). exists x. split; [exact mx | apply ts_co_next_spec, h].
Qed.

Definition exact_after (x : P) (s : trace A) (X : list P) : Prop := ∀ r, r ∈ X ↔ x ⟹ᶜᵒ[s] r.

Lemma τclose_exact (x : P) (s : trace A) (Y : list P) (k : nat) :
  (∀ r, x ⟹ᶜᵒ[s] r ↔ ∃ y, y ∈ Y ∧ y ⟹ᶜᵒ r) → τbounded k Y = true → exact_after x s (τclose k Y).
Proof.
  intros hgen hb r. split.
  - intros m. apply hgen. exact (τclose_sound k Y r m).
  - intros w. apply hgen in w as (y & hy & w). exact (τclose_complete k Y hb y r hy w).
Qed.

Lemma root_gen (x : P) : ∀ r, x ⟹ᶜᵒ[[]] r ↔ ∃ y, y ∈ ([x] : list P) ∧ y ⟹ᶜᵒ r.
Proof.
  intros r. split.
  - intros w. exists x. split; [apply list_elem_of_singleton; reflexivity | exact w].
  - intros (y & ->%list_elem_of_singleton & w). exact w.
Qed.

Lemma root_cv (x : P) : (∀ y, y ∈ ([x] : list P) → y ⤓) → x ⇓ᶜᵒ [].
Proof. intros h. apply cocnv_nil, h. apply list_elem_of_singleton. reflexivity. Qed.

Lemma child_gen (x : P) (s : trace A) (X : list P) (hX : exact_after x s X) (μ : A) :
  ∀ r, x ⟹ᶜᵒ[s ++ [μ]] r ↔ ∃ y, y ∈ ext X μ ∧ y ⟹ᶜᵒ r.
Proof.
  intros r. split.
  - intros w. apply cowt_split in w as (r0 & w1 & w2).
    apply cowt_decomp_one in w2 as (r1 & r2 & μ' & w3 & duo & l & w4).
    exists r2. split; [| exact w4].
    apply ext_spec. exists r1. split.
    + apply hX. exact (cowt_push_nil_right x r0 r1 s w1 w3).
    + exists μ'. split; [exact duo | exact l].
  - intros (y & hy & w). apply ext_spec in hy as (t & ht & μ' & duo & l).
    apply (cowt_concat x t r s [μ]); [apply hX, ht |].
    exact (cowt_push_nil_right t y r [μ] (lts_to_cowt duo l) w).
Qed.

Lemma cocnv_snoc (x : P) (s : trace A) (μ : A) :
  x ⇓ᶜᵒ s → (∀ r, x ⟹ᶜᵒ[s ++ [μ]] r → r ⤓) → x ⇓ᶜᵒ s ++ [μ].
Proof.
  revert x. induction s as [| a s IH]; intros x hx h; simpl.
  - apply cocnv_act; [exact (cocnv_terminate x [] hx) |].
    intros r w. apply cocnv_nil. exact (h r w).
  - apply cocnv_act; [exact (cocnv_terminate x (a :: s) hx) |].
    intros r w. apply IH.
    + eapply cocnv_preserved_by_cowt_act; eassumption.
    + intros r' w'. exact (h r' (cowt_push_left w w')).
Qed.

Lemma child_cv (x : P) (s : trace A) (μ : A) (Y : list P) (hx : x ⇓ᶜᵒ s)
  (hgen : ∀ r, x ⟹ᶜᵒ[s ++ [μ]] r ↔ ∃ y, y ∈ Y ∧ y ⟹ᶜᵒ r) :
  (∀ y, y ∈ Y → y ⤓) → x ⇓ᶜᵒ s ++ [μ].
Proof.
  intros ht. apply (cocnv_snoc x s μ hx). intros r w.
  apply hgen in w as (y & hy & w).
  exact (cocnv_terminate r [] (cocnv_preserved_by_cowt_nil [] y (cocnv_nil y (ht y hy)) r w)).
Qed.

Lemma cocnv_app_l (p : P) (s : trace A) s' : p ⇓ᶜᵒ s ++ s' → p ⇓ᶜᵒ s.
Proof.
  intros h. apply cocnv_iff_prefix_terminate_r. intros t r hpre w.
  apply (cocnv_iff_prefix_terminate_l p (s ++ s') h t r); [apply prefix_app_r, hpre | exact w].
Qed.

Lemma co_conditions_pdiv (p q : P) (s : trace A) s' : ¬ p ⇓ᶜᵒ s → co_conditions p q (s ++ s').
Proof.
  intros hn. split.
  - intros h. exfalso. exact (hn (cocnv_app_l p s s' h)).
  - intros q' h. exfalso. exact (hn (cocnv_app_l p s s' h)).
Qed.

(** Divergence. *)

Lemma tau_cycle_diverges (x : P) : x ⤓ → ∀ x1, x ⟶ x1 → x1 ⟹ᶜᵒ x → False.
Proof.
  induction 1 as [x _ IH]. intros x1 l w.
  inversion w as [y | s0 y y2 z l2 w2 | ]; subst.
  - exact (IH x l x l (cowt_nil x)).
  - exact (IH x1 l y2 l2 (cowt_push_nil_right y2 x x1 [] w2 (lts_to_cowt_tau l))).
Qed.

Definition div_set (k : nat) (X : list P) : bool :=
  existsb (λ r, ts_div r || bool_decide (r ∈ τclose k (τsucc [r]))) (τclose k X).

Lemma div_set_spec (k : nat) (X : list P) : div_set k X = true → ∃ r, r ∈ X ∧ ¬ r ⤓.
Proof.
  intros h. apply existsb_exists in h as (r & m & h).
  apply list_elem_of_In in m. destruct (τclose_sound k X r m) as (x & mx & w).
  exists x. split; [exact mx |]. intros tx.
  assert (tr : r ⤓) by exact (cocnv_terminate r [] (cocnv_preserved_by_cowt_nil [] x (cocnv_nil x tx) r w)).
  apply orb_true_iff in h as [h | h]; [exact (ts_div_spec r h tr) |].
  apply bool_decide_eq_true in h.
  destruct (τclose_sound k _ r h) as (r1 & m1 & w1).
  destruct (τsucc_spec _ r1 m1) as (r0 & ->%list_elem_of_singleton & l).
  exact (tau_cycle_diverges r tr r1 l w1).
Qed.

(** Opening the states after one more action. *)

Inductive side (x : P) (s : trace A) : Type :=
| Opened (X : list P) : exact_after x s X → x ⇓ᶜᵒ s → side x s
| Diverged : ¬ x ⇓ᶜᵒ s → side x s
| Unknown : side x s.

#[global] Arguments Opened {x s}.
#[global] Arguments Diverged {x s}.
#[global] Arguments Unknown {x s}.

Definition open_side (k : nat) (x : P) (s : trace A) (Y : list P)
  (hgen : ∀ r, x ⟹ᶜᵒ[s] r ↔ ∃ y, y ∈ Y ∧ y ⟹ᶜᵒ r)
  (hcv : (∀ y, y ∈ Y → y ⤓) → x ⇓ᶜᵒ s) : side x s.
Proof.
  destruct (τbounded k Y) eqn:hb.
  - exact (Opened (τclose k Y) (τclose_exact x s Y k hgen hb) (hcv (τbounded_terminate k Y hb))).
  - destruct (div_set k Y) eqn:hd; [| exact Unknown].
    apply Diverged. intros hc. destruct (div_set_spec k Y hd) as (y & m & hy).
    apply hy, (cocnv_cowt_s_terminate x y s hc), hgen.
    exists y. split; [exact m | apply cowt_nil].
Defined.

Lemma open_side_unknown (k : nat) (x : P) (s : trace A) (Y : list P) hgen hcv :
  open_side k x s Y hgen hcv = Unknown → τbounded k Y = false.
Proof. unfold open_side. generalize (eq_refl (τbounded k Y)). generalize (τbounded k Y) at 2 3. intros b e. destruct b; [discriminate | intros _; exact e]. Qed.

Definition open_root (k : nat) (x : P) : side x [] :=
  open_side k x [] [x] (root_gen x) (root_cv x).

Definition open_child (k : nat) (x : P) (s : trace A) (X : list P)
  (hX : exact_after x s X) (hx : x ⇓ᶜᵒ s) μ : side x (s ++ [μ]) :=
  open_side k x (s ++ [μ]) (ext X μ) (child_gen x s X hX μ) (child_cv x s μ _ hx (child_gen x s X hX μ)).

(** Acceptance sets. *)

Definition coR_dichotomy (p' q' : P) :
  (⌈ ts_Γ ⌉ (coR p') ⊆ ⌈ ts_Γ ⌉ (coR q')) + { x | x ∈ ⌈ ts_Γ ⌉ (coR p') ∧ x ∉ ⌈ ts_Γ ⌉ (coR q') } :=
  ts_dichotomy p' q'.

Definition stable_b (r : P) : bool := bool_decide (ts_tau_next r = []).

Lemma stable_b_spec (r : P) : stable_b r = true ↔ r ↛.
Proof.
  unfold stable_b. rewrite bool_decide_eq_true. split.
  - intros e hm. destruct (lts_may_perform_spec1 _ _ hm) as [q l].
    pose proof (proj2 (ts_tau_next_spec r q) l) as m. rewrite e in m. inversion m.
  - intros st. destruct (ts_tau_next r) as [| q l] eqn:e; [reflexivity | exfalso].
    apply st, lts_may_perform_spec2. exists q. apply ts_tau_next_spec. rewrite e. apply list_elem_of_here.
Qed.

Definition stable_list (X : list P) : list P := filter (λ r, stable_b r = true) X.

Lemma stable_list_spec (x : P) (s : trace A) (X : list P) :
  exact_after x s X → ∀ r, r ∈ stable_list X ↔ x ⟹ᶜᵒ[s] r ∧ r ↛.
Proof. intros hX r. unfold stable_list, exact_after in *. rewrite list_elem_of_filter, stable_b_spec, hX. tauto. Qed.

Lemma iff_mem_w {x : P} {s : trace A} {Lp : list P} (hLp : ∀ r, r ∈ Lp ↔ x ⟹ᶜᵒ[s] r ∧ r ↛) r : r ∈ Lp → x ⟹ᶜᵒ[s] r.
Proof. intros m. exact (proj1 (proj1 (hLp r) m)). Qed.

Lemma iff_mem_st {x : P} {s : trace A} {Lp : list P} (hLp : ∀ r, r ∈ Lp ↔ x ⟹ᶜᵒ[s] r ∧ r ↛) r : r ∈ Lp → r ↛.
Proof. intros m. exact (proj2 (proj1 (hLp r) m)). Qed.

Definition acc_witness (p : P) (s : trace A) (Lp : list P)
  (hLp : ∀ r, r ∈ Lp ↔ p ⟹ᶜᵒ[s] r ∧ r ↛) (q' : P) :
  { p' | p ⟹ᶜᵒ[s] p' ∧ p' ↛ ∧ ⌈ ts_Γ ⌉ (coR p') ⊆ ⌈ ts_Γ ⌉ (coR q') }
  + { X : gset PreAct | (∀ x, x ∈ X → x ∉ ⌈ ts_Γ ⌉ (coR q'))
        ∧ (∀ p', p ⟹ᶜᵒ[s] p' → p' ↛ → ∃ x, x ∈ X ∧ x ∈ ⌈ ts_Γ ⌉ (coR p')) }.
Proof.
  destruct (included_or_witnesses Lp (λ p', ⌈ ts_Γ ⌉ (coR p')) (⌈ ts_Γ ⌉ (coR q')))
    as [(p' & mem & sub) | (X & hXC & hXS)].
  - intros p' _. exact (coR_dichotomy p' q').
  - left. exists p'. split_and!; [exact (iff_mem_w hLp p' mem) | exact (iff_mem_st hLp p' mem) | exact sub].
  - right. exists X. split; [exact hXC |]. intros p' w' st'. apply hXS, hLp. split; assumption.
Defined.

Definition distinguishing_test_of (p q : P) : Type :=
  { st : trace A * T | ts_must p st.2 ∧ ¬ ts_must q st.2 }.

Fixpoint distinguish_list (p q : P) (s : trace A) (hp : p ⇓ᶜᵒ s) (Lp : list P)
  (hLp : ∀ r, r ∈ Lp ↔ p ⟹ᶜᵒ[s] r ∧ r ↛) (Lq : list P) :
  (∀ q', q' ∈ Lq → q ⟹ᶜᵒ[s] q' ∧ q' ↛) → option (distinguishing_test_of p q) :=
  match Lq with
  | [] => λ _, None
  | q' :: Lq' => λ hl,
      match acc_witness p s Lp hLp q' with
      | inl _ => distinguish_list p q s hp Lp hLp Lq' (λ x m, hl x (list_elem_of_further x q' Lq' m))
      | inr (exist _ X hX) =>
          Some (exist _ (s, ts_ta X s) (ts_ta_spec p q q' s X hp
                  (proj1 (hl q' (list_elem_of_here q' Lq'))) (proj2 (hl q' (list_elem_of_here q' Lq')))
                  (proj1 hX) (proj2 hX)))
      end
  end.

Lemma distinguish_list_none (p q : P) (s : trace A) (hp : p ⇓ᶜᵒ s) Lp hLp (Lq : list P) hl :
  distinguish_list p q s hp Lp hLp Lq hl = None →
  ∀ q', q' ∈ Lq → ∃ p', p ⟹ᶜᵒ[s] p' ∧ p' ↛ ∧ ⌈ ts_Γ ⌉ (coR p') ⊆ ⌈ ts_Γ ⌉ (coR q').
Proof.
  induction Lq as [| q0 Lq IH]; simpl.
  - intros _ q' m. inversion m.
  - destruct (acc_witness p s Lp hLp q0) as [(p' & hp') | (X & hX)]; [| discriminate].
    intros hnone q' [-> | m]%elem_of_cons.
    + exists p'. exact hp'.
    + exact (IH _ hnone q' m).
Qed.

Definition distinguish_sets (p q : P) (s : trace A) (hp : p ⇓ᶜᵒ s) (Xp Xq : list P)
  (hXp : exact_after p s Xp) (hXq : exact_after q s Xq) : option (distinguishing_test_of p q) :=
  distinguish_list p q s hp (stable_list Xp) (stable_list_spec p s Xp hXp) (stable_list Xq)
    (λ q' m, proj1 (stable_list_spec q s Xq hXq q') m).

End Sets.
(* end hide *)
