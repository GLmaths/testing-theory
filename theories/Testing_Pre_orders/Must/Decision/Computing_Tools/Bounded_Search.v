(* begin hide *)
From Stdlib.Unicode Require Import Utf8.
From Stdlib Require Import Lia.
From stdpp Require Import base decidable countable gmap finite list sets.
From TestingTheory Require Import ActTau gLts Bisimulation Lts_OBA Lts_FW Lts_OBA_FB Termination
    Must Subset_Act FiniteImageLTS Convergence InteractionBetweenLts ParallelLTSConstruction
    Testing_Predicate SyncActions.
From TestingTheory Require Import coFiniteImage coWeakTransition coConvergence DefinitionASrel LtsFW
    CompletenessASco EquivalenceASco Label_Abstraction.LabelAbstraction Label_Abstraction.Decidable_dichotomic
    Decision.Computing_Tools.Search_Helpers Decision.Computing_Tools.Bounded_Convergence
    Decision.Computing_Tools.Acceptance_Tests_Gamma.
Import ListNotations.

#[local] Hint Mode ExtAction ! : typeclass_instances.

Inductive bounded_result {A E : Type} : Type :=
| B_holds
| B_distinguished (s : trace A) (X : E)
| B_timeout (s : trace A) (on_p : bool).
Arguments bounded_result : clear implicits.

Fixpoint first_fail {B A E : Type} (f : B → bounded_result A E) (l : list B) : bounded_result A E :=
  match l with
  | [] => B_holds
  | b :: l' => match f b with B_holds => first_fail f l' | r => r end
  end.

Lemma first_fail_holds {B A E : Type} (f : B → bounded_result A E) l :
  first_fail f l = B_holds → ∀ b, b ∈ l → f b = B_holds.
Proof.
  induction l as [| b0 l IH]; simpl; intros h b hb; [inversion hb |].
  destruct (f b0) eqn:e; try discriminate.
  apply elem_of_cons in hb as [-> | hb]; [exact e | exact (IH h b hb)].
Qed.

Lemma first_fail_other {B A E : Type} (f : B → bounded_result A E) l r :
  first_fail f l = r → r ≠ B_holds → ∃ b, b ∈ l ∧ f b = r.
Proof.
  induction l as [| b0 l IH]; simpl; intros h hr; [by subst |].
  destruct (f b0) eqn:e.
  - destruct (IH h hr) as (b & hb & hf). exists b. split; [by apply elem_of_cons; right | exact hf].
  - exists b0. split; [apply elem_of_cons; by left | by rewrite e].
  - exists b0. split; [apply elem_of_cons; by left | by rewrite e].
Qed.

Section Bounded_Search.

Context `{H : !ExtAction A} `{gLtsP : !gLts P H} `{!coFiniteImagegLts P A}.
Context {PreAct : Type} `{CC : Countable PreAct} (Γ : A → PreAct) `{DΓ : !Dichotomic P Γ}.

Definition bounded_co_preorder (alphabet : list A) (n : nat) (p q : P) : Prop :=
  ∀ s, length s ≤ n → (∀ μ, μ ∈ s → μ ∈ alphabet) →
    (p ⇓ᶜᵒ s → q ⇓ᶜᵒ s) ∧
    (∀ q', p ⇓ᶜᵒ s → q ⟹ᶜᵒ[s] q' → q' ↛ →
       ∃ p', p ⟹ᶜᵒ[s] p' ∧ p' ↛ ∧ ⌈ Γ ⌉ (coR p') ⊆ ⌈ Γ ⌉ (coR q')).

Definition stable_list (X : gset P) : list P := filter (λ r, r ↛) (elements X).

Lemma stable_list_spec X r : r ∈ stable_list X ↔ r ∈ X ∧ r ↛.
Proof. unfold stable_list. rewrite list_elem_of_filter, elem_of_elements. tauto. Qed.

Lemma stable_of_mem X r : r ∈ stable_list X → r ↛.
Proof. intros h. by apply stable_list_spec in h as [_ h]. Qed.

Definition acc_check (X : gset P) (q' : P) (st : q' ↛) : option (gset PreAct) :=
  match included_or_witnesses (stable_list X) (λ p', ⌈ Γ ⌉ (coR p')) (⌈ Γ ⌉ (coR q'))
          (λ p' m, coR_dichotomy (Γ := Γ) p' q' (stable_of_mem X p' m) st) with
  | inl _ => None
  | inr (exist _ E _) => Some E
  end.

Lemma acc_check_none X q' st :
  acc_check X q' st = None → ∃ p', p' ∈ X ∧ p' ↛ ∧ ⌈ Γ ⌉ (coR p') ⊆ ⌈ Γ ⌉ (coR q').
Proof.
  unfold acc_check.
  destruct (included_or_witnesses _ _ _ _) as [(p' & m & sub) | (E & _)]; [| discriminate].
  intros _. apply stable_list_spec in m as [m st']. by exists p'.
Qed.

Lemma acc_check_some X q' st E :
  acc_check X q' st = Some E →
  (∀ x, x ∈ E → x ∉ ⌈ Γ ⌉ (coR q')) ∧
  (∀ p', p' ∈ X → p' ↛ → ∃ x, x ∈ E ∧ x ∈ ⌈ Γ ⌉ (coR p')).
Proof.
  unfold acc_check.
  destruct (included_or_witnesses _ _ _ _) as [_ | (E' & hC & hS)]; [discriminate |].
  intros [= <-]. split; [exact hC |].
  intros p' m st'. apply hS, stable_list_spec. by split.
Qed.

Fixpoint node_check (X : gset P) (l : list P) : option (gset PreAct) :=
  match l with
  | [] => None
  | q' :: l' =>
      match decide (q' ↛) with
      | left st => match acc_check X q' st with Some E => Some E | None => node_check X l' end
      | right _ => node_check X l'
      end
  end.

Lemma node_check_none X l :
  node_check X l = None →
  ∀ q', q' ∈ l → q' ↛ → ∃ p', p' ∈ X ∧ p' ↛ ∧ ⌈ Γ ⌉ (coR p') ⊆ ⌈ Γ ⌉ (coR q').
Proof.
  induction l as [| q0 l IH]; simpl; intros h q' hq' st; [inversion hq' |].
  apply elem_of_cons in hq' as [<- | hq'].
  - destruct (decide (q' ↛)) as [st0 | n]; [| contradiction].
    destruct (acc_check X q' st0) eqn:e; [discriminate |]. exact (acc_check_none X q' st0 e).
  - destruct (decide (q0 ↛)) as [st0 |]; [destruct (acc_check X q0 st0); [discriminate |] |];
      exact (IH h q' hq' st).
Qed.

Lemma node_check_some X l E :
  node_check X l = Some E →
  ∃ q', q' ∈ l ∧ q' ↛ ∧ (∀ x, x ∈ E → x ∉ ⌈ Γ ⌉ (coR q')) ∧
    (∀ p', p' ∈ X → p' ↛ → ∃ x, x ∈ E ∧ x ∈ ⌈ Γ ⌉ (coR p')).
Proof.
  induction l as [| q0 l IH]; simpl; intros h; [discriminate |].
  destruct (decide (q0 ↛)) as [st0 |].
  - destruct (acc_check X q0 st0) eqn:e.
    + injection h as ->. exists q0. split; [apply elem_of_cons; by left |].
      split; [exact st0 | exact (acc_check_some X q0 st0 E e)].
    + destruct (IH h) as (q' & hq' & r). exists q'. split; [apply elem_of_cons; by right | exact r].
  - destruct (IH h) as (q' & hq' & r). exists q'. split; [apply elem_of_cons; by right | exact r].
Qed.

Definition dead (Y : gset P) : bool := match elements Y with [] => true | _ :: _ => false end.

Lemma dead_spec Y : dead Y = true → ∀ r, r ∉ Y.
Proof.
  unfold dead. destruct (elements Y) as [| y ys] eqn:e; [| discriminate].
  intros _ r hr. apply elem_of_elements in hr. rewrite e in hr. inversion hr.
Qed.

Fixpoint explore (alphabet : list A) (k n : nat) (s : trace A) (X0 Y0 : gset P) {struct n}
  : bounded_result A (gset PreAct) :=
  if tau_bounded_set k X0 then
    if tau_bounded_set k Y0 then
      let X := tau_reach_set k X0 in
      let Y := tau_reach_set k Y0 in
      match node_check X (elements Y) with
      | Some E => B_distinguished s E
      | None =>
          match n with
          | 0 => B_holds
          | S n' =>
              if dead Y then B_holds
              else first_fail (λ μ, explore alphabet k n' (s ++ [μ])
                     (colts_extaction_set_from_pset X μ) (colts_extaction_set_from_pset Y μ)) alphabet
          end
      end
    else B_timeout s false
  else B_timeout s true.

Definition bounded_verdict (alphabet : list A) (n k : nat) (p q : P) : bounded_result A (gset PreAct) :=
  explore alphabet k n [] {[ p ]} {[ q ]}.

Definition base_inv (p : P) (s : trace A) (X0 : gset P) : Prop :=
  ∀ r, (∃ x, x ∈ X0 ∧ x ⟹ᶜᵒ[ ([] : trace A) ] r) ↔ p ⟹ᶜᵒ[s] r.

Definition term_pre (p : P) (s : trace A) : Prop :=
  ∀ s0 r, s0 `prefix_of` s → length s0 < length s → p ⟹ᶜᵒ[s0] r → r ⤓.

Lemma tau_reach_set_sound k : ∀ X t, t ∈ tau_reach_set (A := A) k X → ∃ x, x ∈ X ∧ x ⟹ᶜᵒ[ ([] : trace A) ] t.
Proof.
  induction k as [| k IH]; simpl; intros X t ht.
  - exists t. split; [exact ht | constructor].
  - apply elem_of_union in ht as [ht | ht].
    + exists t. split; [exact ht | constructor].
    + destruct (IH _ t ht) as (y & hy & w).
      destruct (proj1 (colts_tau_set_from_pset_ispec X) y hy) as (x & hx & l).
      exists x. split; [exact hx | exact (cowt_tau [] x y t l w)].
Qed.

Lemma closure_spec k (p : P) s X0 :
  tau_bounded_set k X0 = true → base_inv p s X0 → ∀ r, r ∈ tau_reach_set k X0 ↔ p ⟹ᶜᵒ[s] r.
Proof.
  intros hb hinv r. split.
  - intros hr. apply hinv. exact (tau_reach_set_sound k X0 r hr).
  - intros w. apply hinv in w as (x & hx & w). exact (tau_reach_set_complete k X0 hb x r hx w).
Qed.

Lemma closure_term k (p : P) s X0 :
  tau_bounded_set k X0 = true → base_inv p s X0 → ∀ r, p ⟹ᶜᵒ[s] r → r ⤓.
Proof.
  intros hb hinv r w. apply hinv in w as (x & hx & w).
  apply (cocnv_terminate r ([] : trace A)).
  apply (cocnv_preserved_by_cowt_nil ([] : trace A) x); [| exact w].
  apply cocnv_nil. exact (tau_bounded_set_terminate k X0 hb x hx).
Qed.

Lemma child_base (p : P) s X μ :
  (∀ r, r ∈ X ↔ p ⟹ᶜᵒ[s] r) → base_inv p (s ++ [μ]) (colts_extaction_set_from_pset X μ).
Proof.
  intros hX r. split.
  - intros (x & hx & w). apply elem_of_colts_extaction_set_from_pset in hx as (t & ht & μ' & duo & l).
    apply cowt_concat with t; [by apply hX |].
    exact (cowt_push_nil_right t x r [μ] (lts_to_cowt duo l) w).
  - intros w. apply cowt_split in w as (t & w1 & w2).
    apply cowt_decomp_one in w2 as (r1 & r2 & μ' & w3 & duo & l & w4).
    exists r2. split; [| exact w4].
    apply elem_of_colts_extaction_set_from_pset. exists r1. split; [| by exists μ'].
    apply hX. exact (cowt_push_nil_right p t r1 s w1 w3).
Qed.

Lemma term_full (p : P) s :
  term_pre p s → (∀ r, p ⟹ᶜᵒ[s] r → r ⤓) → ∀ s0 r, s0 `prefix_of` s → p ⟹ᶜᵒ[s0] r → r ⤓.
Proof.
  intros hpre hs s0 r hp w.
  destruct (decide (length s0 < length s)) as [hl | hl]; [exact (hpre s0 r hp hl w) |].
  rewrite (prefix_length_eq s0 s hp) in w; [exact (hs r w) | lia].
Qed.

Lemma term_child (p : P) s μ :
  (∀ s0 r, s0 `prefix_of` s → p ⟹ᶜᵒ[s0] r → r ⤓) → term_pre p (s ++ [μ]).
Proof.
  intros h s0 r hp hl w. apply (h s0 r); [| exact w].
  destruct hp as (l & e). destruct l as [| x l] using rev_ind.
  - rewrite app_nil_r in e. subst. lia.
  - rewrite app_assoc in e. apply app_inj_tail in e as [e _]. by exists l.
Qed.

Lemma root_base (p : P) : base_inv p [] {[ p ]}.
Proof.
  intros r. split.
  - by intros (x & ->%elem_of_singleton & w).
  - intros w. exists p. split; [set_solver | exact w].
Qed.

Lemma root_term (p : P) : term_pre p [].
Proof. intros s0 r _ hl. simpl in hl. lia. Qed.

Definition node_ok (p q : P) (s : trace A) : Prop :=
  (p ⇓ᶜᵒ s → q ⇓ᶜᵒ s) ∧
  (∀ q', p ⇓ᶜᵒ s → q ⟹ᶜᵒ[s] q' → q' ↛ →
     ∃ p', p ⟹ᶜᵒ[s] p' ∧ p' ↛ ∧ ⌈ Γ ⌉ (coR p') ⊆ ⌈ Γ ⌉ (coR q')).

Lemma node_ok_of_check k (p q : P) s X0 Y0 :
  base_inv p s X0 → base_inv q s Y0 → term_pre q s →
  tau_bounded_set k X0 = true → tau_bounded_set k Y0 = true →
  node_check (tau_reach_set k X0) (elements (tau_reach_set k Y0)) = None → node_ok p q s.
Proof.
  intros hX hY tq bX bY enc. split.
  - intros _. apply cocnv_iff_prefix_terminate_r.
    exact (term_full q s tq (closure_term k q s Y0 bY hY)).
  - intros q' _ w st.
    destruct (node_check_none _ _ enc q') as (p' & hp' & st' & sub).
    + apply elem_of_elements, (closure_spec k q s Y0 bY hY), w.
    + exact st.
    + exists p'. split; [apply (closure_spec k p s X0 bX hX), hp' | by split].
Qed.

Lemma node_ok_dead (p q : P) s s1 :
  (∀ r, ¬ q ⟹ᶜᵒ[s] r) → (∀ s0 r, s0 `prefix_of` s → q ⟹ᶜᵒ[s0] r → r ⤓) → node_ok p q (s ++ s1).
Proof.
  intros hd ht. split.
  - intros _. apply cocnv_iff_prefix_terminate_r. intros t r (u & e) w.
    apply app_eq_app in e as (v & [[e1 _] | [e1 _]]); subst;
      first [ apply cowt_split in w as (r' & w' & _); exact (False_rect _ (hd r' w'))
            | apply (ht t r); [by exists v | exact w] ].
  - intros q' _ w _. apply cowt_split in w as (r & w & _). exact (False_rect _ (hd r w)).
Qed.

Lemma explore_holds alphabet k (p q : P) n :
  ∀ s X0 Y0, base_inv p s X0 → base_inv q s Y0 → term_pre q s →
    explore alphabet k n s X0 Y0 = B_holds →
    ∀ s1, length s1 ≤ n → (∀ μ, μ ∈ s1 → μ ∈ alphabet) → node_ok p q (s ++ s1).
Proof.
  induction n as [| n IH]; intros s X0 Y0 hX hY tq e s1 hl ha; simpl in e;
    destruct (tau_bounded_set k X0) eqn:bX; try discriminate;
    destruct (tau_bounded_set k Y0) eqn:bY; try discriminate;
    revert e; destruct (node_check _ _) as [E0 |] eqn:enc; intros e; try discriminate.
  all: pose proof (node_ok_of_check k p q s X0 Y0 hX hY tq bX bY enc) as hnode.
  - destruct s1; [| simpl in hl; lia]. by rewrite app_nil_r.
  - destruct s1 as [| μ s1]; [by rewrite app_nil_r |].
    revert e; destruct (dead _) eqn:eY; intros e.
    { apply (node_ok_dead p q s (μ :: s1)).
      - intros r w. exact (dead_spec _ eY r (proj2 (closure_spec k q s Y0 bY hY r) w)).
      - exact (term_full q s tq (closure_term k q s Y0 bY hY)). }
    assert (μ ∈ alphabet) as hμ by (apply ha; apply elem_of_cons; by left).
    pose proof (first_fail_holds _ _ e μ hμ) as eμ.
    replace (s ++ μ :: s1) with ((s ++ [μ]) ++ s1) by (by rewrite <- app_assoc).
    apply (IH _ _ _ (child_base p s _ μ (closure_spec k p s X0 bX hX))
              (child_base q s _ μ (closure_spec k q s Y0 bY hY))
              (term_child q s μ (term_full q s tq (closure_term k q s Y0 bY hY))) eμ).
    + simpl in hl. lia.
    + intros μ' h'. apply ha. apply elem_of_cons. by right.
Qed.

Lemma explore_distinguished alphabet k (p q : P) n :
  ∀ s X0 Y0, base_inv p s X0 → base_inv q s Y0 → term_pre p s →
    ∀ s' E, explore alphabet k n s X0 Y0 = B_distinguished s' E →
    p ⇓ᶜᵒ s' ∧
    (∃ q', q ⟹ᶜᵒ[s'] q' ∧ q' ↛ ∧ ∀ x, x ∈ E → x ∉ ⌈ Γ ⌉ (coR q')) ∧
    (∀ p', p ⟹ᶜᵒ[s'] p' → p' ↛ → ∃ x, x ∈ E ∧ x ∈ ⌈ Γ ⌉ (coR p')).
Proof.
  induction n as [| n IH]; intros s X0 Y0 hX hY tp s' E e; simpl in e;
    destruct (tau_bounded_set k X0) eqn:bX; try discriminate;
    destruct (tau_bounded_set k Y0) eqn:bY; try discriminate;
    revert e; destruct (node_check _ _) as [E0 |] eqn:enc; intros e.
  1,3: injection e as <- <-;
    destruct (node_check_some _ _ _ enc) as (q' & hq' & st & hC & hS);
    split; [apply cocnv_iff_prefix_terminate_r; exact (term_full p s tp (closure_term k p s X0 bX hX)) |];
    split; [exists q'; split; [apply (closure_spec k q s Y0 bY hY), elem_of_elements, hq' | by split] |];
    intros p' w st'; apply hS; [apply (closure_spec k p s X0 bX hX), w | exact st'].
  - discriminate.
  - revert e; destruct (dead _) eqn:eY; intros e; [discriminate |].
    destruct (first_fail_other _ _ _ e) as (μ & hμ & eμ); [discriminate |].
    exact (IH _ _ _ (child_base p s _ μ (closure_spec k p s X0 bX hX))
              (child_base q s _ μ (closure_spec k q s Y0 bY hY))
              (term_child p s μ (term_full p s tp (closure_term k p s X0 bX hX))) s' E eμ).
Qed.

Theorem bounded_verdict_holds alphabet n k (p q : P) :
  bounded_verdict alphabet n k p q = B_holds → bounded_co_preorder alphabet n p q.
Proof.
  intros e s hl ha.
  exact (explore_holds alphabet k p q n [] _ _ (root_base p) (root_base q) (root_term q) e s hl ha).
Qed.

Definition bounded_holds_b (alphabet : list A) (n k : nat) (p q : P) : bool :=
  match bounded_verdict alphabet n k p q with B_holds => true | _ => false end.

Theorem bounded_holds_b_spec alphabet n k (p q : P) :
  bounded_holds_b alphabet n k p q = true → bounded_co_preorder alphabet n p q.
Proof.
  unfold bounded_holds_b. destruct (bounded_verdict alphabet n k p q) eqn:e; try discriminate.
  intros _. exact (bounded_verdict_holds alphabet n k p q e).
Qed.

Definition bounded_refuted_b (alphabet : list A) (n k : nat) (p q : P) : bool :=
  match bounded_verdict alphabet n k p q with B_distinguished _ _ => true | _ => false end.

End Bounded_Search.

Section Bounded_Search_Tests.

Context `{outcome : T -> Prop} `{outcome_dec : forall t, Decision (outcome t)} `{P : Type}
        `{H : !ExtAction A}.
Context `{gLtsEqP : !gLtsEq P H, !coFiniteImagegLts P A}
        `{!gLtsOba T gLtsEqT, !Testing_Predicate outcome _} `{!CountablegLts T A}.
Context `{!Prop_of_Inter P T A A dual}.
Context `{tc_spec : !test_convergence_spec (t_conv : trace A → T)}.
Context `{!LtsFW P A}.
Context (𝔸 : Label_abstraction P T) `{!Dichotomic P ρ[𝔸] }.
Context {PreAct : Type} `{CC : Countable PreAct} (Γ : A → PreAct).
Context `{!LA_proj (label_ker 𝔸) Γ} `{!LA_surj Γ} `{DΓ : !Dichotomic P Γ}.
Context `{ta_spec : !test_co_acceptance_set_spec (ta : gset PreAct → trace A → T) Γ}.

Theorem bounded_verdict_distinguishes alphabet n k (p q : P) s E :
  bounded_verdict Γ alphabet n k p q = B_distinguished s E →
  p must_pass (ta E s) ∧ ¬ q must_pass (ta E s).
Proof.
  intros e.
  destruct (explore_distinguished Γ alphabet k p q n [] _ _ (root_base p) (root_base q) (root_term p) s E e)
    as (hp & (q' & w & st & hC) & hS).
  split.
  - exact (must_ta_for_all_trace_co_Γ 𝔸 Γ (ta := ta) s p hp E hS).
  - exact (not_must_ta_without_required_acc_set q q' s E w st hC).
Qed.

Corollary bounded_verdict_refutes alphabet n k (p q : P) s E :
  bounded_verdict Γ alphabet n k p q = B_distinguished s E → p ⋢ₘᵤₛₜᵢ q.
Proof.
  intros e hpre. destruct (bounded_verdict_distinguishes alphabet n k p q s E e) as [hp hq].
  exact (hq (hpre _ hp)).
Qed.

Corollary bounded_verdict_refutes_co alphabet n k (p q : P) s E :
  bounded_verdict Γ alphabet n k p q = B_distinguished s E → ¬ p ≼꜀ₒ₋ₐₛ[ ρ[𝔸] ] q.
Proof.
  intros e h%(equivalence_fw_acc_set_and_must_i_co_trace 𝔸 (ta := ta_ρ 𝔸 Γ (ta := ta)) (ta_spec := ta_ρ_spec 𝔸 Γ)).
  exact (bounded_verdict_refutes alphabet n k p q s E e h).
Qed.

Definition bounded_test_of_not (alphabet : list A) (n k : nat) (p q : P) (hn : ¬ bounded_co_preorder Γ alphabet n p q) :
  { sE : trace A * gset PreAct | p must_pass (ta sE.2 sE.1) ∧ ¬ q must_pass (ta sE.2 sE.1) }
  + (trace A * bool).
Proof.
  destruct (bounded_verdict Γ alphabet n k p q) as [| s E | s b] eqn:e.
  - exfalso. exact (hn (bounded_verdict_holds Γ alphabet n k p q e)).
  - left. exists (s, E). exact (bounded_verdict_distinguishes alphabet n k p q s E e).
  - right. exact (s, b).
Defined.

#[local] Existing Instance LA_class_proj.

Lemma Γ_incl_of_ρ_incl (S S' : subset_of A) :
  ⌈ ρ[𝔸] ⌉ S ⊆ ⌈ ρ[𝔸] ⌉ S' → ⌈ Γ ⌉ S ⊆ ⌈ Γ ⌉ S'.
Proof.
  intros h x (μ & hμ & ->).
  destruct (h (ρ[𝔸] μ)) as (μ' & hμ' & e); [by exists μ |].
  exists μ'. split; [exact hμ' |].
  apply (LA_proj_spec (R := label_ker 𝔸) (f := Γ)).
  apply (LA_proj_spec (R := label_ker 𝔸) (f := ρ[𝔸])). exact e.
Qed.

Lemma bounded_of_co_preorder alphabet n (p q : P) :
  p ≼꜀ₒ₋ₐₛ[ ρ[𝔸] ] q → bounded_co_preorder Γ alphabet n p q.
Proof.
  intros [hc ha] s _ _. split; [exact (hc s) |].
  intros q' hps w st. destruct (ha s q' hps w st) as (p' & w' & st' & sub).
  exists p'. split_and!; [exact w' | exact st' | by apply Γ_incl_of_ρ_incl].
Qed.

Corollary bounded_of_must alphabet n (p q : P) :
  p ⊑ₘᵤₛₜᵢ q → bounded_co_preorder Γ alphabet n p q.
Proof.
  intros h%(equivalence_fw_acc_set_and_must_i_co_trace 𝔸 (ta := ta_ρ 𝔸 Γ (ta := ta)) (ta_spec := ta_ρ_spec 𝔸 Γ)).
  exact (bounded_of_co_preorder alphabet n p q h).
Qed.

Corollary bounded_refuted_b_spec alphabet n k (p q : P) :
  bounded_refuted_b Γ alphabet n k p q = true → p ⋢ₘᵤₛₜᵢ q.
Proof.
  unfold bounded_refuted_b. destruct (bounded_verdict Γ alphabet n k p q) as [| s E |] eqn:e; try discriminate.
  intros _. exact (bounded_verdict_refutes alphabet n k p q s E e).
Qed.

End Bounded_Search_Tests.
(* end hide *)
