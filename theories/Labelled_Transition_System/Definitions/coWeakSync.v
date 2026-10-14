(* begin hide *)
(*
   Copyright (c) 2026 Gaëtan Lopez <glopez@irif.fr>

   Permission is hereby granted, free of charge, to any person obtaining a copy
   of this software and associated documentation files (the "Software"), to deal
   in the Software without restriction, including without limitation the rights
   to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
   copies of the Software, and to permit persons to whom the Software is
   furnished to do so, subject to the following conditions:

   The above copyright notice and this permission notice shall be included in all
   copies or substantial portions of the Software.

   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
   OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
   SOFTWARE.
*)
(* end hide *)
(* begin hide *)
(* * Co-traces over the alphabet of the tests

    [coWeakTransition.v] reads a trace [s] as what an observer performs and
    lets the process answer with a /dual/ action.  When the observer speaks
    another language, the trace lives over [Atest] and the answer is any [μ]
    with [sync μ η]: this is [cowt] below.  With [Aproc = Atest] and
    [sync = dual] it is [cowt] ([cowts_iff_cowt]).

    Everything is phrased so that a co-trace fact can be read back as a plain
    weak transition against /some/ trace of the process pointwise related to
    [s] ([cowt_to_wt], [wt_to_cowt]): the process-side machinery of
    [WeakTransitions.v] then applies unchanged.

    The subsets [R t] and [coR p] of [Subset_Act.v] both become subsets of
    [Atest] — which is what makes the abstraction [Φ] live on one alphabet
    only. *)
(* end hide *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From Stdlib.Program Require Import Equality.
From stdpp Require Import base countable list decidable finite gmap gmultiset.
From TestingTheory Require Import ActTau ForAllHelper gLts SyncActions MemAction InteractionUnion MemForwarder Bisimulation Lts_OBA Lts_FW
  Subset_Act WeakTransitions Termination coWeakTransition coConvergence.
(* begin hide *)
Section coWeakSync.

Context {P Aproc Atest : Type}.
Context `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest}.
Context `{gLtsP : !gLts P Hp}.
Context `{SA : !SyncAction Aproc Atest}.

(* The co-weak transitions [p ⟹ᶜᵒ[s] q] and the co-convergence [p ⇓ᶜᵒ s]
    are the ones of [coWeakTransition.v] and [coConvergence.v], which take two
    alphabets.  What follows is only what the one-alphabet development states
    with [dual] in place of [sync]. *)

(* ** Every state reached along a converging co-trace terminates *)

Lemma cocnv_cowt_terminate p q s : p ⇓ᶜᵒ s → p ⟹ᶜᵒ[s] q → q ⤓.
Proof.
  revert p q. induction s as [| η s' IH]; intros p q hc w.
  - eapply cocnv_terminate, cocnv_preserved_by_cowt_nil; [exact hc | exact w].
  - apply cowt_pop in w as (t & w1 & w2).
    eapply IH; [| exact w2].
    eapply cocnv_preserved_by_cowt_act; [exact hc | exact w1].
Qed.

(* ** The blocking co-actions of a process, as test actions

    [coR p] ([Subset_Act.v]) is what an observer must be able to do to
    interact with [p]. *)


End coWeakSync.

(* ** Co-traces against a forwarder

    The lemmas that cancel actions of the trace against one another.  They are
    where [msg_spec] and the forwarder axioms [gLtsFWMem] are needed; each use is
    flagged in the proof. *)

Section coWeakSync_forwarder.

#[local] Hint Mode ExtAction ! : typeclass_instances.

Context {P Aproc Atest : Type}.
Context `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest} `{SA : !SyncAction Aproc Atest}.
Context `{gLtsEqP : !gLtsEq P (@ExtAction_sum Aproc (MemAct Atest) Hp (@ExtAction_mem Atest Ht))}.
Context `{!gLtsFWMem P Aproc Atest}.

(* *** Transport along the bisimulation *)

Lemma cocnv_eq_preserved (p q : P) (s : trace Atest) : p ⋍ q → p ⇓ᶜᵒ s → q ⇓ᶜᵒ s.
Proof. intros heq hc. by eapply cocnv_preserved_by_eq; [exact heq | reflexivity | exact hc]. Qed.

(* *** Giving back what has just been emitted *)

Lemma cocnv_retract_fw (p q : P) (η : Atest) (s : trace Atest) :
  non_blocking η → p ⇓ᶜᵒ s → p ⟶[inr (msg η)] q → q ⇓ᶜᵒ (η :: s).
Proof.
  intros nbη hc l.
  destruct (msg_spec (Aproc := Aproc) η nbη) as (nb & _).
  apply cocnv_act.
  - eapply (fw_terminate_preserved η); [exact nbη | exact l | by eapply cocnv_terminate].
  - intros q0 w.
    apply cowt_decomp_one in w as (r1 & r2 & μ' & w1 & hsy' & l' & w2).
    (* the action realising the co-step is *some* action synchronising with
       [η]; [sync_fwd_feedback] takes any of them *)
    assert (w1' : q ⟹ r1) by exact (proj1 (cowt_iff_wt_nil _ _) w1).
    destruct (fw_delay_wt_nil η nbη (mk_lts_eq l) w1') as (t & w0 & l1).
    destruct l1 as (r' & l1 & heq).
    edestruct (eq_spec r' r2 (ActExt μ')) as (r'' & hlr'' & heqr'').
    { exists r1. split; [exact heq | exact l']. }
    assert (wpt : p ⟹ᶜᵒ[@nil Atest] t) by exact (proj2 (cowt_iff_wt_nil _ _) w0).
    assert (ht : t ⇓ᶜᵒ s) by (eapply cocnv_preserved_by_cowt_nil; eauto).
    destruct (sync_fwd_feedback η μ' nbη hsy' l1 hlr'') as [(m & hlm & heqm) | heqr].
    + assert (hm : m ⇓ᶜᵒ s) by (eapply cocnv_preserved_by_lts_tau; eauto).
      assert (hr'' : r'' ⇓ᶜᵒ s) by (eapply cocnv_eq_preserved; [exact heqm | exact hm]).
      assert (hr2 : r2 ⇓ᶜᵒ s) by (eapply cocnv_eq_preserved; [exact heqr'' | exact hr'']).
      eapply cocnv_preserved_by_cowt_nil; eauto.
    + assert (hr'' : r'' ⇓ᶜᵒ s) by (eapply cocnv_eq_preserved; [exact heqr | exact ht]).
      assert (hr2 : r2 ⇓ᶜᵒ s) by (eapply cocnv_eq_preserved; [exact heqr'' | exact hr'']).
      eapply cocnv_preserved_by_cowt_nil; eauto.
Qed.

(* *** Dropping an action of the trace that the process answers *)

Lemma cocnv_drop_action_in_the_middle_fw (p : P) (s1 s2 : trace Atest) (η : Atest) :
  Forall non_blocking s1 → p ⇓ᶜᵒ (s1 ++ [η] ++ s2) →
  ∀ r (μ : Aproc + MemAct Atest), sync μ η → p ⟶[μ] r → r ⇓ᶜᵒ (s1 ++ s2).
Proof.
  intros his hc. revert p s2 hc.
  induction s1 as [| a s1' IH]; intros p s2 hc r μ hsy l; simpl in *.
  - eapply cocnv_preserved_by_cowt_act; [exact hc |].
    eapply lts_to_cowt; [exact hsy | exact l].
  - inversion his as [| a0 l0 nba his']; subst.
    (* [fwm_boomerang]: the forwarder receives [a] as [inr (cobar a)] and
       gives it back as [inr (msg a)] *)
    destruct (fw_boomerang_total p a nba) as (μ0 & p2 & hsyco & tr_b & tr_nb).
    destruct (fw_delay a nba tr_nb l) as (t & w0 & (r' & lar & heqr)).
    assert (pcowt : p ⟹ᶜᵒ[[a]] p2)
      by (eapply lts_to_cowt; [exact hsyco | exact tr_b]).
    inversion hc as [| p' a'' rest hp hclause]; subst.
    assert (hp2 : p2 ⇓ᶜᵒ (s1' ++ η :: s2)) by (by eapply hclause).
    assert (ht : t ⇓ᶜᵒ (s1' ++ s2)) by (by eapply (IH his' p2 s2 hp2 t μ)).
    assert (hr' : r' ⇓ᶜᵒ (a :: (s1' ++ s2))).
    { eapply cocnv_retract_fw; [exact nba | exact ht | exact lar]. }
    eapply cocnv_eq_preserved; [exact heqr | exact hr'].
Qed.

(* *** Cancelling an action of the trace against its dual *)

Lemma cocnv_annhil_base_fw (p : P) (η μ1 : Atest) (s2 s3 : trace Atest) :
  Forall non_blocking s2 → non_blocking η → dual μ1 η →
  p ⇓ᶜᵒ ([η] ++ s2 ++ [μ1] ++ s3) → p ⇓ᶜᵒ (s2 ++ s3).
Proof.
  intros his2 nbη duo hc.
  (* [η] names the non-blocking action [γ := inr (msg η)] of the process;
     [fwm_boomerang] receives [η] and gives it back as [γ] *)
  destruct (msg_spec (Aproc := Aproc) η nbη) as (nbγ & hdν).
  destruct (fw_boomerang_total p η nbη) as (μ0 & t & hsyco & l1 & l2).
  set (γ := inr (msg η) : Aproc + MemAct Atest) in *.
  assert (pcowt : p ⟹ᶜᵒ[[η]] t) by (eapply lts_to_cowt; [exact hsyco | exact l1]).
  assert (w2 : t ⟹⋍[[γ]] p).
  { exists p. split; [| reflexivity]. eapply wt_act; [exact l2 | apply wt_nil]. }
  simpl in hc.
  inversion hc as [| p' η' rest hp hclause]; subst.
  assert (ht : t ⇓ᶜᵒ (s2 ++ [μ1] ++ s3)) by (by eapply hclause).
  destruct w2 as (p' & w2 & heqp').
  apply wt_decomp_one in w2 as (r1 & r2 & wr1 & lη & wr2).
  assert (r1cowt : t ⟹ᶜᵒ[@nil Atest] r1) by exact (proj2 (cowt_iff_wt_nil _ _) wr1).
  assert (hr1 : r1 ⇓ᶜᵒ (s2 ++ μ1 :: s3))
    by (eapply cocnv_preserved_by_cowt_nil; eauto).
  (* [msg_spec]'s second clause: dualising [η] on the observer side is
     answered by [γ] itself on the process side *)
  assert (hsyγν : sync γ μ1) by (by apply hdν).
  assert (hr2 : r2 ⇓ᶜᵒ (s2 ++ s3))
    by (eapply (cocnv_drop_action_in_the_middle_fw r1 s2 s3 μ1 his2 hr1 r2 γ);
        [exact hsyγν | exact lη]).
  assert (r2cowt : r2 ⟹ᶜᵒ[@nil Atest] p') by exact (proj2 (cowt_iff_wt_nil _ _) wr2).
  assert (hp' : p' ⇓ᶜᵒ (s2 ++ s3))
    by (eapply cocnv_preserved_by_cowt_nil; eauto).
  eapply cocnv_eq_preserved; [exact heqp' | exact hp'].
Qed.

Lemma cocnv_annhil_fw (p : P) (η μ : Atest) (s1 s2 s3 : trace Atest) :
  Forall non_blocking s1 → Forall non_blocking s2 → non_blocking η → dual μ η →
  p ⇓ᶜᵒ (s1 ++ [η] ++ s2 ++ [μ] ++ s3) → p ⇓ᶜᵒ (s1 ++ s2 ++ s3).
Proof.
  intros his1 his2 nbη duo. revert p.
  induction s1 as [| a s1' IH]; intros p hc; simpl in *.
  - by eapply cocnv_annhil_base_fw.
  - inversion his1 as [| a0 l0 nba his1']; subst.
    inversion hc as [| p' a'' rest hp hclause]; subst.
    apply cocnv_act; [exact hp |].
    intros q w. by apply IH, hclause.
Qed.

End coWeakSync_forwarder.
(* end hide *)
