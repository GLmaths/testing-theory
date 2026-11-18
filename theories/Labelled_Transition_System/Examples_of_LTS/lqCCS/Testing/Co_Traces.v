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
From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base gmultiset countable decidable list.
From TestingTheory Require Import ActTau pMust_scheduled pMust_almost_sure pMust_smyth pMust_transfer pMust_canonical pMust_cotrace.
From TestingTheory Require Import lqCCS.quantum_mem.Algebra lqCCS.quantum_mem.Syntax lqCCS.quantum_mem.Quantum_Weights.
From TestingTheory Require Import lqCCS.lqCCS_prog.Syntax lqCCS.Helper_substitution.De_Brujin_lemmas lqCCS.General_definition.Parallel_choice_LTS lqCCS.quantum_mem.LTS lqCCS.lqCCS_prog.LTS lqCCS.lqCCS_par_Qmem.LTS lqCCS.lqCCS_process.LTS.LTS lqCCS.Helper_substitution.Label_lemmas lqCCS.Testing.Scheduled lqCCS.Testing.Observer_predicates lqCCS.Helper_substitution.Tag_lemmas lqCCS.Testing.DistLTS lqCCS.Testing.Programs lqCCS.Testing.Observers lqCCS.Testing.Smyth_Soundness lqCCS.Testing.Canonical lqCCS.Testing.Final lqCCS.Testing.Trace lqCCS.Testing.Trace_Finitary.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

Section LqP.
  Context `{LP : lqCCS_Parameters}.

Section CoTraces.
  Context `{QM : QuantumModel} (p q : proc * St).

  Definition co_visited (π : nat → dist node) (n : node) : Prop := ∃ i ρ, (n, ρ) ∈ π i.

  Definition co_coherent (O : node → list msg) (S : node → bool) (Ch : channel → Prop) (K : tag → okind)
      (π : nat → dist node) (U : node → offer → Prop) : Prop :=
    ext_closed S ∧ (∀ n, ¬ co_visited π n → S n = true ∧ O n = []) ∧ (∀ n o, U n o → real_off p q Ch K o)
    ∧ outputs_sync p q O S Ch K ∧ one_output_per_tag O S ∧ outputs_persist O S.

  Definition alt_cotrace : Prop :=
    ∀ O S Ch K π U R, (∀ k, K k ≠ KRec) → co_trace (M := lq_menu O) S (dinit q) π U R → co_coherent O S Ch K π U →
      fin (co_visited π) →
      ∃ I π' R', co_run (M := lq_menu O) I (co_success (M := lq_menu O) S (co_menu (real_off p q Ch K) U R) U) (dinit p) π' R'
        ∧ co_below (M := lq_menu O) (real_off p q Ch K) S U R π I π' R'.

  Definition alt_cotrace_inf : Prop :=
    ∀ O S Ch K π U R, co_trace (M := lq_menu O) S (dinit q) π U R → co_coherent O S Ch K π U →
      ∃ I π' R', co_run (M := lq_menu O) I (co_success (M := lq_menu O) S (co_menu (real_off p q Ch K) U R) U) (dinit p) π' R'
        ∧ co_below (M := lq_menu O) (real_off p q Ch K) S U R π I π' R'.

  Lemma alt_cotrace_inf_fin : alt_cotrace_inf → alt_cotrace.
  Proof. intros Hi O S Ch K π U R _ Ht Hc _. exact (Hi O S Ch K π U R Ht Hc). Qed.

  Lemma visited_co O (r : nat → dist comp) n :
    visited r n ↔ co_visited (λ i, co_dist (M := lq_menu O) (r i)) n.
  Proof.
    split.
    - intros (i & c & ρ & Hin & <-). exists i, ρ. apply list_elem_of_fmap. by exists (c, ρ).
    - intros (i & ρ & Hin). apply list_elem_of_fmap in Hin as ([c ρ'] & Ex & Hin).
      injection Ex as En _. exists i, c, ρ'. split; [exact Hin|]. symmetry. exact En.
  Qed.

  Lemma fin_iff {B} (P Q : B → Prop) : (∀ x, P x ↔ Q x) → fin P → fin Q.
  Proof. intros HPQ (l & Hl). exists l. intros x Hx. by apply Hl, HPQ. Qed.

  Lemma dinit_root (r : nat → dist comp) : r 0 = dinit q → ∀ x, x ∈ r 0 → x.1.1 = [].
  Proof. intros -> x Hx. apply list_elem_of_singleton in Hx. by subst x. Qed.

  Theorem alt_cotrace_iff (DC : dep_choice) : alt_trace p q ↔ alt_cotrace.
  Proof.
    split.
    - intros Ht O S Ch K π U R HKr (r & w & Hw & -> & -> & ->) (HS & Hq & Hc & Ho1 & Ho2 & Ho3) Hfin.
      assert (Hr : run_word (M := lq_menu O) (cells (M := lq_menu O) S r w) S (r 0) r w) by (split; [done|apply Hw]).
      refine (co_fwd (M := lq_menu O) (real_off p q Ch K) (dinit p) S r w Hr (dinit_root r (proj1 Hw)) DC _).
      apply (Ht O S Ch K r w HKr).
      + split; [done|]. split; [|done]. intros n Hn. apply Hq. by rewrite <- (visited_co O).
      + split; [exact Hw|]. refine (fin_iff _ _ _ Hfin). intros n. symmetry. apply (visited_co O).
    - intros Hc O S Ch K r w HKr (HS & Hq & Hcs & Ho1 & Ho2 & Ho3) [Hw Hfin].
      assert (Hr : run_word (M := lq_menu O) (cells (M := lq_menu O) S r w) S (r 0) r w) by (split; [done|apply Hw]).
      refine (co_bwd (M := lq_menu O) (real_off p q Ch K) (dinit p) S r w Hr (dinit_root r (proj1 Hw)) Hcs _).
      apply (Hc O S Ch K); [exact HKr| | |].
      + by exists r, w.
      + split; [done|]. split; [|done]. intros n Hn. apply Hq. by rewrite (visited_co O).
      + refine (fin_iff _ _ _ Hfin). intros n. apply (visited_co O).
  Qed.
End CoTraces.

Theorem cotrace_characterisation `{QM : QuantumModel} (DC : dep_choice) (p q : proc * St) :
  q.2 ≠ szero →
  (ctx_pre_sm_on Stay (obs_for p q) p q ↔ alt_cotrace p q).
Proof.
  intros Hz. rewrite (trace_characterisation_all DC p q Hz). exact (alt_cotrace_iff p q DC).
Qed.

End LqP.

(* end hide *)
