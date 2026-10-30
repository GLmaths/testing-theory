(* begin hide *)
From Stdlib Require Import Lia.
From stdpp Require Import base countable gmap list sets.
From TestingTheory Require Import ActTau gLts SyncActions Termination Subset_Act InListPropHelper
  coWeakTransition coConvergence coFiniteImage
  Decision.Tools_in_construction.Inductive.Generic.Helpers Decision.Tools_in_construction.Inductive.Generic.Bisim
  Decision.Tools_in_construction.Inductive.Generic.Interface Decision.Tools_in_construction.Inductive.Generic.Sets Decision.Tools_in_construction.Inductive.Generic.Transport Decision.Tools_in_construction.Inductive.Generic.Graph Decision.Tools_in_construction.Inductive.Generic.Swaps.
Import ListNotations.

Section Adequacy.

Context `{TS : TraceSearchLang P A Atom PreAct T}.

(** Completeness of the certificate when the budgets are adequate. *)

Definition adeq (k : nat) (Y : list P) : bool := τbounded k Y || div_set k Y.

Definition adequate (m k : nat) (p q : P) : bool :=
  let R := pair_graph m k p q in
  adeq k [p] && adeq k [q] &&
  match root_pair k p q with Some c => in_graph c R | None => true end &&
  forallb (λ x, forallb (λ μ, adeq k (ext x.1 μ) && adeq k (ext x.2 μ) &&
              match child_pair k x μ with Some c => in_graph c R | None => true end)
            (next_list (explored x) x.2)) R.

Definition node_exact (p q : P) (x : pair_states) : Prop :=
  ∃ s, exact_after p s x.1 ∧ exact_after q s x.2 ∧ p ⇓ᶜᵒ s ∧ q ⇓ᶜᵒ s.

Lemma root_exact (k : nat) (p q : P) c : root_pair k p q = Some c → node_exact p q c.
Proof.
  intros h. rewrite root_pair_unfold in h.
  destruct (τbounded k [p]) eqn:bp, (τbounded k [q]) eqn:bq; simpl in h; try discriminate.
  injection h as <-. exists []. simpl. split_and!.
  - exact (τclose_exact p [] _ k (root_gen p) bp).
  - exact (τclose_exact q [] _ k (root_gen q) bq).
  - exact (root_cv p (τbounded_terminate k _ bp)).
  - exact (root_cv q (τbounded_terminate k _ bq)).
Qed.

Lemma child_pair_exact (k : nat) (p q : P) (x : pair_states) (μ : A) c :
  node_exact p q x → child_pair k x μ = Some c → node_exact p q c.
Proof.
  intros (s & hX & hY & hp & hq) h. rewrite child_pair_unfold in h.
  destruct (τbounded k (ext x.1 μ)) eqn:bp, (τbounded k (ext x.2 μ)) eqn:bq; simpl in h; try discriminate.
  injection h as <-. exists (s ++ [μ]). simpl. split_and!.
  - exact (τclose_exact p (s ++ [μ]) _ k (child_gen p s x.1 hX μ) bp).
  - exact (τclose_exact q (s ++ [μ]) _ k (child_gen q s x.2 hY μ) bq).
  - exact (child_cv p s μ _ hp (child_gen p s x.1 hX μ) (τbounded_terminate k _ bp)).
  - exact (child_cv q s μ _ hq (child_gen q s x.2 hY μ) (τbounded_terminate k _ bq)).
Qed.

Lemma children_exact (k : nat) (p q : P) (x c : pair_states) :
  node_exact p q x → c ∈ children k x → node_exact p q c.
Proof.
  intros hx m. unfold children in m. apply list_elem_of_omap in m as (μ & _ & h).
  exact (child_pair_exact k p q x μ c hx h).
Qed.

Lemma pair_graph_exact (m k : nat) (p q : P) x : x ∈ pair_graph m k p q → node_exact p q x.
Proof. apply pair_graph_inv; [intros y c hy hc; exact (children_exact k p q y c hy hc) | apply root_exact]. Qed.

Lemma dichotomy_inl (p' y : P) :
  ⌈ ts_Γ ⌉ (coR p') ⊆ ⌈ ts_Γ ⌉ (coR y) → (if coR_dichotomy p' y then true else false) = true.
Proof. intros sub. destruct (coR_dichotomy p' y) as [| (z & h1 & h2)]; [reflexivity | exfalso; exact (h2 (sub z h1))]. Qed.

Theorem certify_complete (m k : nat) (p q : P) :
  adequate m k p q = true → (∀ s, co_conditions p q s) → certify m k p q = true.
Proof.
  intros ha hco. unfold adequate in ha. set (R := pair_graph m k p q) in *.
  apply andb_true_iff in ha as [ha hall]. apply andb_true_iff in ha as [ha hroot].
  apply andb_true_iff in ha as [hap haq].
  unfold certify. fold R. unfold certified, certified_in. apply andb_true_iff. split.
  - unfold root_ok. apply orb_true_iff. unfold adeq in hap, haq.
    apply orb_true_iff in hap as [bp | dp]; [| left; exact dp]. right.
    apply orb_true_iff in haq as [bq | dq].
    + rewrite root_pair_unfold in *. rewrite bp, bq in *. cbn [andb] in *. rewrite in_graph_set. exact hroot.
    + exfalso. destruct (div_set_spec k _ dq) as (r & hr%list_elem_of_singleton & hn). subst r.
      apply hn. apply (cocnv_terminate q []). apply (proj1 (hco [])).
      exact (root_cv p (τbounded_terminate k _ bp)).
  - apply forallb_forall. intros x mx'. pose proof (proj2 (list_elem_of_In _ _) mx') as mx.
    destruct (pair_graph_exact m k p q x mx) as (s & hX & hY & hp & hq).
    rewrite forallb_forall in hall. specialize (hall x mx').
    apply andb_true_iff. split.
    + unfold local_ok. apply forallb_forall. intros y my'.
      pose proof (proj2 (list_elem_of_In _ _) my') as my.
      destruct (proj1 (stable_list_spec q s x.2 hY y) my) as [wy sty].
      destruct (proj2 (hco s) y hp wy sty) as (p' & wp & stp & sub).
      apply existsb_exists. exists p'. split.
      * apply list_elem_of_In, (stable_list_spec p s x.1 hX). split; assumption.
      * apply dichotomy_inl, sub.
    + apply forallb_forall. intros μ mμ. rewrite forallb_forall in hall. specialize (hall μ mμ).
      apply andb_true_iff in hall as [hall hc]. apply andb_true_iff in hall as [a1 a2].
      unfold child_ok. rewrite orb_comm. apply orb_true_iff. unfold adeq in a1, a2.
      apply orb_true_iff in a1 as [b1 | d1]; [| left; exact d1]. right.
      apply orb_true_iff in a2 as [b2 | d2].
      * rewrite !child_pair_unfold in *. rewrite b1, b2 in *. cbn [andb] in *. rewrite in_graph_set. exact hc.
      * exfalso. destruct (div_set_spec k _ d2) as (r & mr & hn). apply hn.
        apply (cocnv_cowt_s_terminate q r (s ++ [μ])).
        -- apply (proj1 (hco (s ++ [μ]))).
           exact (child_cv p s μ _ hp (child_gen p s x.1 hX μ) (τbounded_terminate k _ b1)).
        -- apply (child_gen q s x.2 hY μ). exists r. split; [exact mr | apply cowt_nil].
Qed.

Lemma certify_refutes (m k : nat) (p q : P) :
  adequate m k p q = true → certify m k p q = false → ¬ ∀ s, co_conditions p q s.
Proof. intros ha hc h. rewrite (certify_complete m k p q ha h) in hc. discriminate. Qed.

End Adequacy.
(* end hide *)
