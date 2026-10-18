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

From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base countable decidable gmap.
From TestingTheory Require Import ActTau gLts SyncActions MemAction InteractionUnion MemForwarder Bisimulation Lts_OBA
  Subset_Act coFiniteImage Testing_Predicate InteractionBetweenLts
  Must DefinitionASrel CompletenessASsync SoundnessASsync
  Label_Abstraction.LabelAbstraction Label_Abstraction.Decidable_dichotomic Sum_LTS.

#[local] Hint Mode ExtAction ! : typeclass_instances.

Section Equivalence_label_abstraction.

Context {P T Ap At : Type}.
Context `{Hp : ExtAction Ap} `{Ht : ExtAction At} `{SA : !SyncAction Ap At}.
Context (outcome : T → Prop).

Context `{gLtsEqT : !gLtsEq T Ht} `{gLtsObaT : !gLtsOba T _}.
Context `{TP : !Testing_Predicate outcome gLtsEqT}.

Context `{gLtsEqP : !gLtsEq P (@ExtAction_sum Ap (MemAct At) Hp (@ExtAction_mem At Ht))} `{FWP : !gLtsFWMem P Ap At}.
Context `{SYP : !Prop_of_Inter P T (Ap + MemAct At) At sync} `{CFIP : !coFiniteImagegLts P At}.

Context (𝔸 : Label_abstraction (Hp := ExtAction_sum) (SA := SyncAction_mem) P T).
Context `{DichP : !Dichotomic (Hp := ExtAction_sum) (SA := SyncAction_mem) P ρ[𝔸] }.

Context (tconv : trace At → T) `{!test_convergence_spec tconv}.
Context (ta : gset (At / 𝔸) → trace At → T)
        `{!test_co_acceptance_set_spec ta ρ[𝔸] }.

Theorem equivalence_fw_label_abstraction (p q : P) :
  p ⊆ₘᵤₛₜᵢ q ↔ p ≼꜀ₒ₋ₐₛ[ ρ[𝔸] ] q.
Proof.
  split.
  - intros hpre.
    by eapply (completeness_fw_co_sync_dich 𝔸 (tconv := tconv) (ta := ta)).
  - intros hpre.
    by eapply (soundness_fw_co_sync outcome 𝔸).
Qed.

End Equivalence_label_abstraction.

Section Must_sum.
  Context {P Q T A1 A2 At : Type} `{H1 : ExtAction A1} `{H2 : ExtAction A2} `{Ht : ExtAction At}.
  Context `{SA1 : !SyncAction A1 At} `{SA2 : !SyncAction A2 At}.
  Context {gLtsP : gLts P H1} {gLtsQ : gLts Q H2} {gLtsT : gLtsEq T Ht}.
  Context {outcome : T → Prop} `{TP : !Testing_Predicate outcome gLtsT}.

  Notation gLP := (@lift_left_lts A1 A2 H1 H2 P gLtsP).
  Notation gLQ := (@lift_right_lts A1 A2 H1 H2 Q gLtsQ).
  Notation SAS := (@SyncAction_sum A1 A2 H1 H2 At Ht SA1 SA2).

  #[local] Hint Extern 0 (ExtAction (A1 + A2)) => exact (@ExtAction_sum A1 A2 H1 H2) : typeclass_instances.
  #[local] Instance SASi : SyncAction (A1 + A2) At := SAS.

  Notation gT := (@gLtsEq_gLts T At Ht gLtsT).

  Context (PIP : @Prop_of_Inter P T A1 At (@sync _ _ _ _ SA1) H1 gLtsP Ht gT).
  Context (PIQ : @Prop_of_Inter Q T A2 At (@sync _ _ _ _ SA2) H2 gLtsQ Ht gT).

  Notation STSP := (ParSts_of_union gLP gLtsT (SY := lift_left_inter PIP)).
  Notation STSQ := (ParSts_of_union gLQ gLtsT (SY := lift_right_inter PIQ)).
  Notation STSS := (ParSts_of_union gLts_sum gLtsT (SY := Prop_of_Inter_sum PIP PIQ)).

  Lemma must_inl_to (p : P) (t : T) :
    must (SA := SAS) (STS := STSP) p t → must (SA := SAS) (STS := STSS) (inl p) t.
  Proof.
    induction 1 as [p t ho | p t nh ex pt IHpt et IHet com IHcom].
    - by apply m_now.
    - apply m_step; [exact nh | | | exact IHet |].
      + destruct ex as (y & hy).
        apply par_step_inv in hy
          as [(p' & -> & l) | [(t' & -> & l) | (p' & t' & μ1 & μ2 & -> & hs & l1 & l2)]].
        * exists (inl p', t). by apply par_step_left.
        * exists (inl p, t'). by apply par_step_right.
        * exists (inl p', t').
          by eapply par_step_sync.
      + intros [p' | q'] l; [exact (IHpt p' l) | done].
      + intros [p' | q'] t' μ1 μ2 hs l1 l2; [exact (IHcom p' t' μ1 μ2 hs l1 l2) | done].
  Qed.

  Lemma must_inr_to (q : Q) (t : T) :
    must (SA := SAS) (STS := STSQ) q t → must (SA := SAS) (STS := STSS) (inr q) t.
  Proof.
    induction 1 as [q t ho | q t nh ex pt IHpt et IHet com IHcom].
    - by apply m_now.
    - apply m_step; [exact nh | | | exact IHet |].
      + destruct ex as (y & hy).
        apply par_step_inv in hy
          as [(q' & -> & l) | [(t' & -> & l) | (q' & t' & μ1 & μ2 & -> & hs & l1 & l2)]].
        * exists (inr q', t). by apply par_step_left.
        * exists (inr q, t'). by apply par_step_right.
        * exists (inr q', t').
          by eapply par_step_sync.
      + intros [p' | q'] l; [done | exact (IHpt q' l)].
      + intros [p' | q'] t' μ1 μ2 hs l1 l2; [done | exact (IHcom q' t' μ1 μ2 hs l1 l2)].
  Qed.

  Lemma must_inl_from (s : P + Q) (t : T) :
    must (SA := SAS) (STS := STSS) s t → ∀ p, s = inl p → must (SA := SAS) (STS := STSP) p t.
  Proof.
    induction 1 as [s t ho | s t nh ex pt IHpt et IHet com IHcom]; intros p ->.
    - by apply m_now.
    - apply m_step; [exact nh | | | |].
      + destruct ex as (y & hy).
        apply par_step_inv in hy
          as [(s' & -> & l) | [(t' & -> & l) | (s' & t' & μ1 & μ2 & -> & hs & l1 & l2)]].
        * destruct s' as [p' | q']; [| done].
          exists (p', t). by apply par_step_left.
        * exists (p, t'). by apply par_step_right.
        * destruct s' as [p' | q']; [| done].
          exists (p', t').
          by eapply par_step_sync.
      + intros p' l. exact (IHpt (inl p') l p' eq_refl).
      + intros t' l. exact (IHet t' l p eq_refl).
      + intros p' t' μ1 μ2 hs l1 l2. exact (IHcom (inl p') t' μ1 μ2 hs l1 l2 p' eq_refl).
  Qed.

  Lemma must_inr_from (s : P + Q) (t : T) :
    must (SA := SAS) (STS := STSS) s t → ∀ q, s = inr q → must (SA := SAS) (STS := STSQ) q t.
  Proof.
    induction 1 as [s t ho | s t nh ex pt IHpt et IHet com IHcom]; intros q ->.
    - by apply m_now.
    - apply m_step; [exact nh | | | |].
      + destruct ex as (y & hy).
        apply par_step_inv in hy
          as [(s' & -> & l) | [(t' & -> & l) | (s' & t' & μ1 & μ2 & -> & hs & l1 & l2)]].
        * destruct s' as [p' | q']; [done |].
          exists (q', t). by apply par_step_left.
        * exists (q, t'). by apply par_step_right.
        * destruct s' as [p' | q']; [done |].
          exists (q', t').
          by eapply par_step_sync.
      + intros q' l. exact (IHpt (inr q') l q' eq_refl).
      + intros t' l. exact (IHet t' l q eq_refl).
      + intros q' t' μ1 μ2 hs l1 l2. exact (IHcom (inr q') t' μ1 μ2 hs l1 l2 q' eq_refl).
  Qed.
End Must_sum.