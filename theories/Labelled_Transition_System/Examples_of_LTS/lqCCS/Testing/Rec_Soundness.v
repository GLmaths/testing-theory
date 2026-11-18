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
From stdpp Require Import base gmultiset countable decidable list propset.
From TestingTheory Require Import ActTau pMust_scheduled pMust_almost_sure pMust_smyth pMust_transfer pMust_canonical pMust_cotrace.
From TestingTheory Require Import lqCCS.General_definition.Algebra lqCCS.quantum_mem.Syntax lqCCS.quantum_mem.Quantum_Weights.
From TestingTheory Require Import lqCCS.lqCCS_prog.Syntax lqCCS.Helper.De_Brujin_lemmas lqCCS.General_definition.Parallel_choice_LTS lqCCS.quantum_mem.LTS lqCCS.lqCCS_prog.LTS lqCCS.lqCCS_par_Qmem.LTS lqCCS.lqCCS_process.LTS.LTS lqCCS.Helper.Conf_labels lqCCS.Helper.Label_lemmas lqCCS.Testing.Scheduled lqCCS.Testing.Observer_predicates lqCCS.Helper.Tag_lemmas lqCCS.Testing.DistLTS lqCCS.Testing.Programs lqCCS.Testing.Observers lqCCS.Testing.Rec_Observers lqCCS.Testing.Smyth_Soundness lqCCS.Testing.Canonical lqCCS.Testing.Final lqCCS.Testing.Trace lqCCS.Testing.Trace_Sound lqCCS.Testing.Co_Traces.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

Section Rec_Soundness.
  Context `{lqP : lqCCS_Parameters}.

Lemma tnodes_chans_r T : obsr T → ∀ z X, X ∈ tnodes T z →
  (∀ c, c ∈ out_chans X → c ∈ out_chans T) ∧ (∀ c, c ∈ in_chans X → c ∈ in_chans T).
Proof.
  intros HT z. induction z as [|a z IH] using rev_ind; intros X Hin.
  - rewrite tnodes_nil in Hin. apply list_elem_of_singleton in Hin. subst. split; intros c Hc; exact Hc.
  - apply tnodes_app_elem in Hin as (X0 & HX0 & Hin). destruct (IH X0 HX0) as [Ho Hi].
    assert (Hst : ∃ k 𝜆, X0 ⟶ₚ{𝜆}[k] X) by (pose proof (co_succ_step _ _ _ Hin); eauto).
    destruct Hst as (k & 𝜆 & Hp).
    destruct (prog_step_chans_sub_r X0 k 𝜆 X (proj1 (tnodes_obsr T HT z X0 HX0)) Hp) as [Ho0 Hi0].
    split; intros c Hc; [exact (Ho c (Ho0 c Hc))|exact (Hi c (Hi0 c Hc))].
Qed.

Definition obs_for_r `{QM : QuantumModel} (p q : prog * St) (T : prog) : Prop :=
  observer_r T ∧ ∀ t, t ∈ tags T → t ∉ otags p.1 ∧ t ∉ otags q.1.

Lemma otags_base P t t' : tag_base t = tag_base t' → t ∈ otags P → t' ∈ otags P.
Proof. unfold otags. rewrite !elem_of_PropSet. intros E. by rewrite E. Qed.

Lemma rtagged_tags T t x : rtagged T t x → ∃ t', t' ∈ tags T ∧ tag_base t' = tag_base t.
Proof.
  unfold rtagged. rewrite tagged_tren. intros ([t' x'] & E & Hin)%list_elem_of_fmap. simpl in E.
  injection E as E _. exists t'. split; [unfold tags; apply list_elem_of_fmap; by exists (t', x')|by symmetry].
Qed.

Lemma rtagged_otags `{QM : QuantumModel} p q T t x :
  obs_for_r p q T → rtagged T t x → t ∉ otags p.1 ∧ t ∉ otags q.1.
Proof.
  intros [_ Hpq] Hk. destruct (rtagged_tags T t x Hk) as (t' & Ht & E).
  destruct (Hpq t' Ht) as [Hp Hq]. split; intros Hk'; [apply Hp|apply Hq]; exact (otags_base _ t t' (eq_sym E) Hk').
Qed.

Lemma rec_pre_sound_obs `{QM : QuantumModel} (DC : dep_choice)
    (p q : prog * St) T :
  obs_for_r p q T → smyth_le (SchedSts0 := dlts (menu T) (O_T T) (S_T T)) Stay (dinit p) (dinit q) →
  smyth_le (SchedSts0 := lq_SchedSts) Stay (compose p T) (compose q T).
Proof.
  intros HT Hsm.
  apply (alt_pre_sound_obs T (rtagged T) (observer_r_w T (proj1 HT)) (tnodes_rtagged T)
           (λ t x y, proj1 (proj2 (proj1 HT)) (tag_base t) x y) Stay DC p q); [| |exact Hsm].
  - intros t' Ht Hin. apply elem_of_PropSet in Hin as (x & Hx). exact (proj1 (rtagged_otags p q T t' x HT Hx) Ht).
  - intros t' Ht Hin. apply elem_of_PropSet in Hin as (x & Hx). exact (proj2 (rtagged_otags p q T t' x HT Hx) Ht).
Qed.

Definition kinds_r (T : prog) (t : tag) : okind := kinds_of (tren tag_base T) (tag_base t).

Lemma kinds_r_tagged T t x : observer_r T → rtagged T t x → kinds_r T t = x.
Proof.
  intros HT Hin. unfold kinds_r, kinds_of. unfold rtagged in Hin.
  destruct (find (λ y, bool_decide (y.1 = tag_base t)) (tagged (tren tag_base T))) as [y|] eqn:E.
  - apply find_some in E as [Hy Hk]. apply bool_decide_eq_true in Hk. destruct y as [t' x']. simpl in *. subst t'.
    apply (proj1 (proj2 HT) (tag_base t)); [by apply list_elem_of_In|exact Hin].
  - exfalso. pose proof (find_none _ _ E (tag_base t, x) (proj1 (list_elem_of_In _ _) Hin)) as Hf.
    simpl in Hf. by rewrite bool_decide_eq_false in Hf.
Qed.

Lemma menu_rtagged T z o : menu T z o → rtagged T (off_tag o) (off_kind o).
Proof.
  intros (X & a & HX & <- & Hne). destruct (co_succ X a) as [|X' l] eqn:E; [done|].
  assert (Hin : (co_tag a, kind_of a) ∈ tagged X) by (apply (co_succ_tagged X a X'); rewrite E; by left).
  pose proof (tnodes_rtagged T z X _ _ HX Hin) as H. by destruct a.
Qed.

Lemma menu_real_r `{QM : QuantumModel} (p q : prog * St) T z o :
  obs_for_r p q T → menu T z o → real_off p q (λ c, c ∈ out_chans T) (kinds_r T) o.
Proof.
  intros HT Hm. pose proof (menu_rtagged T z o Hm) as Hk.
  split; [unfold typed; symmetry; exact (kinds_r_tagged T _ _ (proj1 HT) Hk)|].
  destruct (rtagged_otags p q T _ _ HT Hk) as [Htp Htq]. split; [exact Htp|]. split; [exact Htq|].
  intros t c -> Hc1.
  destruct Hm as (X & a & HX & Ha & Hne). destruct a as [|t' c' v| | | |]; try discriminate Ha.
  simpl in Ha. injection Ha as -> ->.
  destruct (co_succ X (CoIn t c v)) as [|X' l] eqn:E; [done|].
  assert (HX' : X' ∈ co_succ X (CoIn t c v)) by (rewrite E; by left).
  pose proof (co_succ_step _ _ _ HX') as Hs.
  pose proof (prog_step_in_chan_r X t c v X' (proj1 (tnodes_obsr T (proj1 (proj1 HT)) z X HX)) Hs) as Hc.
  exact (proj2 (proj1 (proj1 HT)) c Hc1 (proj2 (tnodes_chans_r T (proj1 (proj1 HT)) z X HX) c Hc)).
Qed.

Definition RealT_r `{QM : QuantumModel} (p q : prog * St) (O : node → list msg) (Ch : channel → Prop)
    (K : tag → okind) (I : node → offer → Prop) (S : node → bool) : Prop :=
  (∃ T, obs_for_r p q T ∧ (∀ z m, plain z → S z = false → (m ∈ O z ↔ m ∈ O_T T z)) ∧ I = menu T ∧ S = S_T T
        ∧ (∀ c, c ∈ out_chans T → Ch c) ∧ ∀ t x, rtagged T t x → K t = x)
  ∧ ∀ z o, I z o → real_off p q Ch K o.

Definition alt_free_obs_r `{QM : QuantumModel} (p q : prog * St) : Prop :=
  ∀ O Ch K, malt_free_on (M := lq_menu O) (real_off p q Ch K) (RealT_r p q O Ch K) (dinit p) (dinit q).

Theorem rec_free_sound `{QM : QuantumModel} (DC : dep_choice)
    (p q : prog * St) :
  q.2 ≠ szero → alt_free_obs_r p q → ctx_pre_sm_on Stay (obs_for_r p q) p q.
Proof.
  intros Hz Hf T HT. apply (rec_pre_sound_obs DC p q T HT).
  assert (Hpre : malt_pre_on (M := lq_menu (O_T T)) (RealT_r p q (O_T T) (λ c, c ∈ out_chans T) (kinds_r T))
                   (dinit p) (dinit q)).
  { apply (malt_free_on_sound (M := lq_menu (O_T T)) (real_off p q (λ c, c ∈ out_chans T) (kinds_r T)) _
             (λ I S HR, proj2 HR) DC); [| |apply Hf].
    - intros x ->%list_elem_of_singleton. done.
    - intros x ->%list_elem_of_singleton. exact Hz. }
  apply (Hpre (menu T) (S_T T)). split; [|intros z o Hm; exact (menu_real_r p q T z o HT Hm)].
  exists T. split; [done|]. split; [done|]. split; [done|]. split; [done|]. split; [done|].
  intros t x Hin. exact (kinds_r_tagged T t x (proj1 HT) Hin).
Qed.

Definition alt_trace_inf `{QM : QuantumModel} (p q : prog * St) : Prop :=
  ∀ O S Ch K r w, coherent p q O S Ch K r w → run_word (M := lq_menu O) (used_by O S r w) S (dinit q) r w →
    ∃ r', is_run (SchedSts0 := trace_sts p q O S Ch K r w) Stay (dinit p) r'
        ∧ run_le (SchedSts0 := trace_sts p q O S Ch K r w) r' r.

Theorem trace_sound_r `{QM : QuantumModel} (DC : dep_choice) (p q : prog * St) :
  q.2 ≠ szero → alt_trace_inf p q → alt_free_obs_r p q.
Proof.
  intros Hz Halt O Ch K I S HR r w Hw.
  destruct HR as ((T & HT & HO & -> & -> & HCh & HK) & HokI).
  refine (snd_main p q O Ch K T r w (observer_r_w T (proj1 HT)) _ HO HCh HokI Hw Hz DC
            (λ Hc Hw', Halt _ _ Ch K r w Hc Hw')).
  intros z X c HX Hc. exact (proj1 (tnodes_chans_r T (proj1 (proj1 HT)) z X HX) c Hc).
Qed.

Lemma cotrace_trace_inf `{QM : QuantumModel} (p q : prog * St) : alt_cotrace_inf p q → alt_trace_inf p q.
Proof.
  intros Hc O S Ch K r w (HS & Hq & Hcs & Ho1 & Ho2 & Ho3) Hw.
  assert (Hr : run_word (M := lq_menu O) (cells (M := lq_menu O) S r w) S (r 0) r w) by (split; [done|apply Hw]).
  refine (co_bwd (M := lq_menu O) (real_off p q Ch K) (dinit p) S r w Hr (dinit_root q r (proj1 Hw)) Hcs _).
  apply (Hc O S Ch K).
  - by exists r, w.
  - split; [done|]. split; [|done]. intros z Hn. apply Hq. by rewrite (visited_co O).
Qed.

Theorem cotrace_sound_rec `{QM : QuantumModel} (DC : dep_choice)
    (p q : prog * St) :
  q.2 ≠ szero → alt_cotrace_inf p q → ctx_pre_sm_on Stay (obs_for_r p q) p q.
Proof.
  intros Hz Hc. apply (rec_free_sound DC p q Hz), (trace_sound_r DC p q Hz), cotrace_trace_inf, Hc.
Qed.

End Rec_Soundness.

(* end hide *)
