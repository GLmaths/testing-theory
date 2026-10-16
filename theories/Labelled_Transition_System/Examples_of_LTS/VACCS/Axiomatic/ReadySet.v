(* begin hide *)
(*
   Copyright (c) 2026 Gaëtan Lopez <gaetanlopez.maths@gmail.com>

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
(* * Ready sets in VACCS: a process's ready set is the set of channels it
      has a pending message on

    [coR p := λ μ₁. ∃ μ₂, p performs [μ₂] ∧ dual μ₂ μ₁ ∧ blocking μ₁]
    ([Subset_Act.v]).  In VCCS [blocking] is unconditionally true, so
    [coR p] is "the co-actions of everything [p] can do".  In VACCS
    [non_blocking] is [is_output], so [blocking μ₁] says μ₁ is an **input**
    — and [dual] then forces the witness μ₂ to be the matching **output**.
    Hence

        coR p  =  { ActIn a | p can emit a }

    and, since VACCS's abstraction has the single constructor [Inputs c]
    (it erases the value *and* the polarity),

        ⌈𝝳∘Φ⌉(coR p)  =  { Inputs c | p has a pending message on c }.

    Two consequences worth stating plainly, both proved below:

    - **A guarded sum has an empty ready set** ([gproc_coR_empty]): it can
      never emit.  So at the bare-process level the acceptance-set preorder
      sees *nothing at all* of a process's input offers.
    - **A normal form's ready set is exactly its message bag's channels**
      ([msgs_coR_abs]).

    That is precisely why VACCS's must-preorder needs the **forwarder**:
    the bare-process acceptance sets carry only the outgoing messages, and
    it is the buffer — which absorbs any input at any time — that supplies
    the incoming half.  [Characterisations/Must_Characterisation.v] has no
    [_without_toFW] variant for exactly this reason, and here it is,
    visible at the level of [coR]. *)

From Stdlib Require Import List PeanoNat Lia.
From stdpp Require Import decidable base sets gmap.
From TestingTheory Require Import VACCS.Language.LTS VACCS.Language.gLts_Instance Must ActTau InputOutputActions
  gLts Bisimulation InteractionBetweenLts Testing_Predicate VACCS_Good WeakTransitions
  Subset_Act DefinitionAS Convergence VACCS.Axiomatic.Static VACCS.Characterisations.Must_Characterisation
  VACCS.Axiomatic.Erasure VACCS.Axiomatic.Shift VACCS.Axiomatic.Precongruence VACCS.Axiomatic.Expansion VACCS.Axiomatic.ResNormalize
  VACCS.Axiomatic.Copycat VACCS.Axiomatic.DefinitionAxiomatic VACCS.Axiomatic.SoundnessAx VACCS.Axiomatic.Forwarder
  VACCS.Axiomatic.NormalForm.
Section VACCS_ReadySet.

Context `{VP : VACCS_Parameters}.

(* ** [coR] holds inputs only, and records what the process can emit *)

Lemma coR_only_inputs : forall (p : proc) (μ : ExtAct TypeOfActions),
  μ ∈ coR p -> exists x, μ = ActIn x /\ p ⟶[ActOut x].
Proof.
  intros p μ (μ2 & Hnr & Hd & Hb).
  destruct μ as [x|x].
  - destruct μ2 as [y|y]; simpl in Hd; try (exact (match Hd with end)).
    subst. exists x. split; [ reflexivity | exact Hnr ].
  - exfalso. apply Hb. unfold non_blocking_output, is_output. eexists; reflexivity.
Qed.

Lemma coR_input_iff : forall (p : proc) (x : TypeOfActions),
  (ActIn x) ∈ coR p <-> p ⟶[ActOut x].
Proof.
  intros p x. split.
  - intro H. destruct (coR_only_inputs _ _ H) as (y & Hy & Hn). inversion Hy; subst. exact Hn.
  - intro H. exists (ActOut x). repeat split.
    + exact H.
    + unfold non_blocking_output, is_output. intros (b & Hb). discriminate Hb.
Qed.

(* The abstracted form: [Φ] keeps the channel only. *)

Lemma coR_abs_iff : forall (p : proc) (c : ChannelData),
  (Inputs c) ∈ ⌈ 𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ ⌉ (coR p) <-> exists v, p ⟶[ActOut (c,v)].
Proof.
  intros p c. unfold elem_of, subset_of, map_set. simpl. split.
  - intros (μ & Hmu & Heq).
    destruct (coR_only_inputs _ _ Hmu) as ((c0,v0) & Hshape & Hn). subst.
    simpl in Heq. inversion Heq; subst. exists v0. exact Hn.
  - intros (v & Hn). exists (ActIn (c,v)). split; [ | reflexivity ].
    apply coR_input_iff. exact Hn.
Qed.

Lemma coR_abs_shape : forall (p : proc) (x : PreAct),
  x ∈ ⌈ 𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ ⌉ (coR p) -> exists c, x = Inputs c.
Proof. intros p [c] _. exists c. reflexivity. Qed.

(* ** Refusal, spelled out

    The generic [lts_performs_spec1]/[_spec2] frequently fail to apply
    against this concrete [gLts] instance (an elaboration mismatch, not a
    type error), so everything here goes through [lts_set_spec0]/[_spec1]
    directly — the workaround already recorded for VCCS. *)

Lemma no_lts_stable : forall (p : proc), (forall q, ~ lts p τ q) -> p ↛.
Proof.
  intros p H Hp. apply lts_performs_spec1 in Hp as (q & Hq). eapply H. exact Hq.
Qed.

Lemma stable_no_lts : forall (p : proc), p ↛ -> forall q, ~ lts p τ q.
Proof.
  intros p H q Hq. apply H, lts_performs_spec2. exists q. exact Hq.
Qed.

Lemma no_lts_ext_stable : forall (p : proc) (μ : ExtAct TypeOfActions),
  (forall q, ~ lts p (ActExt μ) q) -> p ↛[μ].
Proof.
  intros p μ H Hp. apply lts_performs_spec1 in Hp as (q & Hq). eapply H. exact Hq.
Qed.

Lemma ext_stable_no_lts : forall (p : proc) (μ : ExtAct TypeOfActions),
  p ↛[μ] -> forall q, ~ lts p (ActExt μ) q.
Proof.
  intros p μ H q Hq. apply H, lts_performs_spec2. exists q. exact Hq.
Qed.

(* ** A guarded sum has an empty ready set *)

Lemma gproc_coR_empty : forall (M : gproc) (μ : ExtAct TypeOfActions), ~ (μ ∈ coR (g M)).
Proof.
  intros M μ H. destruct (coR_only_inputs _ _ H) as (x & _ & Hn).
  apply Hn. simpl. apply set_eq. intro q. split.
  - intro Hq. exfalso. eapply gproc_no_output. eapply lts_set_spec0. exact Hq.
  - intro Hq. set_solver.
Qed.

(* ** Stability of a guarded sum, computed structurally *)

Fixpoint gStable (M : gproc) : Prop :=
match M with
| ① => True
| 𝟘 => True
| c ? • p => True
| 𝛕 • p => False
| M1 + M2 => gStable M1 /\ gStable M2
end.

Lemma gStable_iff : forall M, (g M) ↛ <-> gStable M.
Proof.
  induction M; simpl.
  - split; [ intro; exact I | intro; apply no_lts_stable; intros q Hq; inversion Hq ].
  - split; [ intro; exact I | intro; apply no_lts_stable; intros q Hq; inversion Hq ].
  - split; [ intro; exact I | intro; apply no_lts_stable; intros q Hq; inversion Hq ].
  - split; [ | intro H; exact (match H with end) ].
    intro H. exfalso. eapply stable_no_lts; [ exact H | apply lts_tau ].
  - split.
    + intro H. apply choice_stable_iff in H as (H1 & H2).
      split; [ apply IHM1; exact H1 | apply IHM2; exact H2 ].
    + intros (H1 & H2). apply choice_stable_iff.
      split; [ apply IHM1; exact H1 | apply IHM2; exact H2 ].
Qed.

(* ** The ready set of a message bag *)

Lemma msg_emits_iff : forall c' v' c v,
  (c' ! v' • 𝟘) ⟶[ActOut (c,v)] <-> (c' = c /\ v' = v).
Proof.
  intros c' v' c v. split.
  - intro H. destruct (decide (c' = c /\ v' = v)) as [Hyes|Hno]; [ exact Hyes | ].
    exfalso. revert H. apply no_lts_ext_stable. intros q Hq.
    inversion Hq; subst. apply Hno. split; reflexivity.
  - intros (H1 & H2); subst. apply lts_performs_spec2. eexists. apply lts_output.
Qed.

Lemma nil_ext_stable : forall (μ : ExtAct TypeOfActions), (g 𝟘) ↛[μ].
Proof. intro μ. apply no_lts_ext_stable. intros q Hq. inversion Hq. Qed.

Lemma msgs_emits_iff : forall l c v, (msgs l) ⟶[ActOut (c,v)] <-> In (c,v) l.
Proof.
  induction l as [|cv l IH]; intros c v; simpl.
  - split; [ intro H; exfalso; revert H; apply nil_ext_stable | intro H; exact (match H with end) ].
  - destruct cv as (c',v'). simpl. split.
    + intro H. destruct (decide ((c',v') = (c,v))) as [Heq|Hne]; [ left; exact Heq | right ].
      apply IH. apply (dec_stable (H := not_dec (proc_stable_dec _ _))). intro Hst. revert H. apply par_ext_stable_iff. split; [ | exact Hst ].
      apply no_lts_ext_stable. intros q Hq. inversion Hq; subst. apply Hne. reflexivity.
    + intros [Heq|Hin]; apply (dec_stable (H := not_dec (proc_stable_dec _ _))); intros Hst; apply par_ext_stable_iff in Hst as (H1 & H2).
      * inversion Heq; subst. eapply ext_stable_no_lts; [ exact H1 | apply lts_output ].
      * exact (H2 (proj2 (IH c v) Hin)).
Qed.

(* The payoff: a message bag's abstracted ready set is exactly the set of
    channels it carries a message on. *)
Corollary msgs_coR_abs : forall l c,
  (Inputs c) ∈ ⌈ 𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ ⌉ (coR (msgs l)) <-> exists v, In (c,v) l.
Proof.
  intros l c. rewrite coR_abs_iff. split.
  - intros (v & H). exists v. apply msgs_emits_iff. exact H.
  - intros (v & H). exists v. apply msgs_emits_iff. exact H.
Qed.

End VACCS_ReadySet.
(* end hide *)
