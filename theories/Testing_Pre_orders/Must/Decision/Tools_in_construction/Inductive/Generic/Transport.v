(* begin hide *)
From Stdlib Require Import Lia.
From stdpp Require Import base countable gmap list sets.
From TestingTheory Require Import ActTau gLts SyncActions Termination Subset_Act InListPropHelper
  coWeakTransition coConvergence coFiniteImage
  Decision.Tools_in_construction.Inductive.Generic.Helpers Decision.Tools_in_construction.Inductive.Generic.Bisim
  Decision.Tools_in_construction.Inductive.Generic.Interface Decision.Tools_in_construction.Inductive.Generic.Sets.
Import ListNotations.

Section Transport.

Context `{TS : TraceSearchLang P A Atom PreAct T}.

(** Transport along atom swaps. *)

Definition swap_trace (a : Atom) (b : Atom) (s : trace A) : trace A := map (ts_swap_act a b) s.

Lemma swap_trace_invol (a : Atom) (b : Atom) (s : trace A) : swap_trace a b (swap_trace a b s) = s.
Proof. induction s as [| μ s IH]; simpl; [reflexivity | by rewrite ts_swap_act_invol, IH]. Qed.

Lemma tau_swap_inv (a : Atom) (b : Atom) (p q : P) : ts_swap a b p ⟶ q → p ⟶ ts_swap a b q.
Proof. intros l. pose proof (ts_tau_swap a b _ _ l) as l'. by rewrite ts_swap_invol in l'. Qed.

Lemma step_swap_inv (a : Atom) (b : Atom) (p q : P) (μ : A) : ts_swap a b p ⟶[μ] q → p ⟶[ts_swap_act a b μ] ts_swap a b q.
Proof. intros l. pose proof (ts_step_swap a b _ _ _ l) as l'. by rewrite ts_swap_invol in l'. Qed.

Lemma cowt_swap (a : Atom) (b : Atom) (p : P) (s : trace A) q : p ⟹ᶜᵒ[s] q → ts_swap a b p ⟹ᶜᵒ[swap_trace a b s] ts_swap a b q.
Proof.
  induction 1 as [p | s p p' q l w IH | μ μ' s p p' q duo l w IH]; simpl.
  - apply cowt_nil.
  - eapply cowt_tau; [exact (ts_tau_swap a b p p' l) | exact IH].
  - eapply cowt_act; [exact (ts_sync_swap a b μ' μ duo) | exact (ts_step_swap a b p μ' p' l) | exact IH].
Qed.

Lemma cowt_swap_inv (a : Atom) (b : Atom) (p : P) (s : trace A) q : ts_swap a b p ⟹ᶜᵒ[s] q → p ⟹ᶜᵒ[swap_trace a b s] ts_swap a b q.
Proof. intros w. pose proof (cowt_swap a b _ _ _ w) as w'. by rewrite ts_swap_invol in w'. Qed.

Lemma terminate_swap (a : Atom) (b : Atom) (p : P) : p ⤓ → (ts_swap a b p) ⤓.
Proof.
  induction 1 as [p _ IH]. constructor. intros q l.
  rewrite <- (ts_swap_invol a b q). apply IH. exact (tau_swap_inv a b p q l).
Qed.

Lemma cocnv_swap (a : Atom) (b : Atom) (p : P) (s : trace A) : p ⇓ᶜᵒ s → ts_swap a b p ⇓ᶜᵒ swap_trace a b s.
Proof.
  induction 1 as [p ht | p μ s ht _ IH]; simpl.
  - apply cocnv_nil, terminate_swap, ht.
  - apply cocnv_act; [exact (terminate_swap a b p ht) |]. intros q w.
    rewrite <- (ts_swap_invol a b q). apply IH.
    pose proof (cowt_swap_inv a b p [ts_swap_act a b μ] q w) as w'. simpl in w'.
    rewrite ts_swap_act_invol in w'. exact w'.
Qed.

Lemma cocnv_swap_back (a : Atom) (b : Atom) (p : P) (s : trace A) : ts_swap a b p ⇓ᶜᵒ swap_trace a b s → p ⇓ᶜᵒ s.
Proof.
  intros h. pose proof (cocnv_swap a b _ _ h) as h'.
  by rewrite ts_swap_invol, swap_trace_invol in h'.
Qed.

Lemma refuses_swap (a : Atom) (b : Atom) (p : P) : p ↛ → (ts_swap a b p) ↛.
Proof.
  intros h hm. apply h. apply lts_may_perform_spec2.
  destruct (lts_may_perform_spec1 _ _ hm) as [q l].
  exists (ts_swap a b q). exact (tau_swap_inv a b p q l).
Qed.

Lemma coR_swap (a : Atom) (b : Atom) (p : P) (x : PreAct) : x ∈ ⌈ ts_Γ ⌉ (coR (ts_swap a b p)) → ts_swap_pre a b x ∈ ⌈ ts_Γ ⌉ (coR p).
Proof.
  intros (μ1 & (μ2 & hm & duo & hb) & ->). exists (ts_swap_act a b μ1). split.
  - exists (ts_swap_act a b μ2). split_and!.
    + apply lts_may_perform_spec2. destruct (lts_may_perform_spec1 _ _ hm) as [q l].
      exists (ts_swap a b q). exact (step_swap_inv a b p q μ2 l).
    + exact (ts_sync_swap a b μ2 μ1 duo).
    + intros h. apply hb. exact (ts_nb_swap a b μ1 h).
  - by rewrite ts_Γ_swap.
Qed.

Lemma coR_swap_inv (a : Atom) (b : Atom) (p : P) (x : PreAct) : ts_swap_pre a b x ∈ ⌈ ts_Γ ⌉ (coR p) → x ∈ ⌈ ts_Γ ⌉ (coR (ts_swap a b p)).
Proof.
  intros h. rewrite <- (ts_swap_invol a b p) in h. apply coR_swap in h.
  by rewrite ts_swap_pre_invol in h.
Qed.

Lemma co_conditions_swap (a : Atom) (b : Atom) (p q : P) (s : trace A) :
  co_conditions p q s → co_conditions (ts_swap a b p) (ts_swap a b q) (swap_trace a b s).
Proof.
  intros [h1 h2]. split.
  - intros hp. apply cocnv_swap, h1, (cocnv_swap_back a b), hp.
  - intros q' hp w st.
    pose proof (cowt_swap_inv a b q _ q' w) as w'. rewrite swap_trace_invol in w'.
    destruct (h2 (ts_swap a b q') (cocnv_swap_back a b p s hp) w' (refuses_swap a b q' st))
      as (p' & wp & stp & sub).
    exists (ts_swap a b p'). split_and!.
    + exact (cowt_swap a b p s p' wp).
    + exact (refuses_swap a b p' stp).
    + intros x hx. pose proof (coR_swap a b q' _ (sub _ (coR_swap a b p' x hx))) as h.
      rewrite ts_swap_pre_invol in h. exact h.
Qed.

Fixpoint sws (π : list (Atom * Atom)) (p : P) : P :=
  match π with
  | [] => p
  | (a, b) :: π => ts_swap a b (sws π p)
  end.

Fixpoint sws_act (π : list (Atom * Atom)) (μ : A) : A :=
  match π with
  | [] => μ
  | (a, b) :: π => ts_swap_act a b (sws_act π μ)
  end.

Fixpoint sws_trace (π : list (Atom * Atom)) (s : trace A) : trace A :=
  match π with
  | [] => s
  | (a, b) :: π => swap_trace a b (sws_trace π s)
  end.

Lemma sws_app (π1 : list (Atom * Atom)) (π2 : list (Atom * Atom)) p : sws (π1 ++ π2) p = sws π1 (sws π2 p).
Proof. induction π1 as [| [a b] π1 IH]; simpl; [reflexivity | by rewrite IH]. Qed.

Lemma sws_act_app (π1 : list (Atom * Atom)) (π2 : list (Atom * Atom)) (μ : A) : sws_act (π1 ++ π2) μ = sws_act π1 (sws_act π2 μ).
Proof. induction π1 as [| [a b] π1 IH]; simpl; [reflexivity | by rewrite IH]. Qed.

Lemma sws_trace_app (π1 : list (Atom * Atom)) (π2 : list (Atom * Atom)) (s : trace A) : sws_trace (π1 ++ π2) s = sws_trace π1 (sws_trace π2 s).
Proof. induction π1 as [| [a b] π1 IH]; simpl; [reflexivity | by rewrite IH]. Qed.

Lemma sws_trace_snoc (π : list (Atom * Atom)) (s : trace A) (μ : A) : sws_trace π (s ++ [μ]) = sws_trace π s ++ [sws_act π μ].
Proof. induction π as [| [a b] π IH]; simpl; [reflexivity |]. rewrite IH. unfold swap_trace. by rewrite map_app. Qed.

Lemma cowt_sws (π : list (Atom * Atom)) (p : P) (s : trace A) q : p ⟹ᶜᵒ[s] q → sws π p ⟹ᶜᵒ[sws_trace π s] sws π q.
Proof. induction π as [| [a b] π IH]; simpl; [done |]. intros w. apply cowt_swap, IH, w. Qed.

Lemma cocnv_sws (π : list (Atom * Atom)) (p : P) (s : trace A) : p ⇓ᶜᵒ s → sws π p ⇓ᶜᵒ sws_trace π s.
Proof. induction π as [| [a b] π IH]; simpl; [done |]. intros h. apply cocnv_swap, IH, h. Qed.

Lemma cocnv_sws_back (π : list (Atom * Atom)) (p : P) (s : trace A) : sws π p ⇓ᶜᵒ sws_trace π s → p ⇓ᶜᵒ s.
Proof. induction π as [| [a b] π IH]; simpl; [done |]. intros h. apply IH, (cocnv_swap_back a b), h. Qed.

Lemma co_conditions_sws_back (π : list (Atom * Atom)) (p q : P) (s : trace A) :
  co_conditions (sws π p) (sws π q) (sws_trace π s) → co_conditions p q s.
Proof.
  induction π as [| [a b] π IH]; simpl; [done |]. intros h. apply IH.
  pose proof (co_conditions_swap a b _ _ _ h) as h'.
  by rewrite !ts_swap_invol, swap_trace_invol in h'.
Qed.

Lemma sbisim_swap (a b : Atom) (r r' : P) : sbisim r r' → sbisim (ts_swap a b r) (ts_swap a b r').
Proof.
  intros (R & hR & h). exists (λ u v, R (ts_swap a b u) (ts_swap a b v)).
  split; [| by rewrite !ts_swap_invol].
  intros u v huv. destruct (hR _ _ huv) as [f g]. split.
  - intros α u' l. destruct α as [μ |].
    + destruct (f _ _ (ts_step_swap a b u μ u' l)) as (v0 & lv & hv).
      exists (ts_swap a b v0). split; [| by rewrite ts_swap_invol].
      pose proof (ts_step_swap a b _ _ _ lv) as l'. by rewrite ts_swap_invol, ts_swap_act_invol in l'.
    + destruct (f _ _ (ts_tau_swap a b u u' l)) as (v0 & lv & hv).
      exists (ts_swap a b v0). split; [| by rewrite ts_swap_invol].
      pose proof (ts_tau_swap a b _ _ lv) as l'. by rewrite ts_swap_invol in l'.
  - intros α v' l. destruct α as [μ |].
    + destruct (g _ _ (ts_step_swap a b v μ v' l)) as (u0 & lu & hu).
      exists (ts_swap a b u0). split; [| by rewrite ts_swap_invol].
      pose proof (ts_step_swap a b _ _ _ lu) as l'. by rewrite ts_swap_invol, ts_swap_act_invol in l'.
    + destruct (g _ _ (ts_tau_swap a b v v' l)) as (u0 & lu & hu).
      exists (ts_swap a b u0). split; [| by rewrite ts_swap_invol].
      pose proof (ts_tau_swap a b _ _ lu) as l'. by rewrite ts_swap_invol in l'.
Qed.
Fixpoint sws_atom (π : list (Atom * Atom)) (c : Atom) : Atom :=
  match π with
  | [] => c
  | (a, b) :: π => ts_swap_atom a b (sws_atom π c)
  end.

Lemma sws_rev_invol (π : list (Atom * Atom)) (p : P) : sws (rev π) (sws π p) = p.
Proof.
  induction π as [| [a b] π IH]; simpl; [reflexivity |].
  by rewrite sws_app; simpl; rewrite ts_swap_invol, IH.
Qed.

Lemma sws_trace_rev_invol (π : list (Atom * Atom)) (s : trace A) : sws_trace (rev π) (sws_trace π s) = s.
Proof.
  induction π as [| [a b] π IH]; simpl; [reflexivity |].
  by rewrite sws_trace_app; simpl; rewrite swap_trace_invol, IH.
Qed.

Lemma sbisim_sws (π : list (Atom * Atom)) (r r' : P) : sbisim r r' → sbisim (sws π r) (sws π r').
Proof. induction π as [| [a b] π IH]; simpl; [done |]. intros h. apply sbisim_swap, IH, h. Qed.

End Transport.
(* end hide *)
