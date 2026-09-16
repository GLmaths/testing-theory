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

(** * Core Erlang: the axioms of the framework

    The system LTS of [Erlang_LTS] is shown to be an LTS with non-blocking
    actions ([gLts]), whose bisimulation is /equality/ ([gLtsEq]), satisfying
    the Selinger axioms ([gLtsOba]), FEEDBACK ([gLtsObaFB]) and the finiteness
    conditions.  The boomerang axiom does /not/ hold — a process cannot emit a
    message it has not received — which is exactly why the forwarder
    construction [toFW] is needed. *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list numbers finite sets gmap gmultiset.
From TestingTheory Require Import InListPropHelper ActTau InputOutputActions gLts Bisimulation
  Lts_OBA Lts_OBA_FB Lts_FW Lts_Finite_Output_Chain FiniteImageLTS
  InteractionBetweenLts MultisetLTSConstruction ForwarderConstruction
  VACCS VACCS_Instance Erlang_Syntax Erlang_LTS.

(** ** Actions

    Those of VACCS instantiated by [Erlang_VACCS_Parameters]: [VACCS_ExtAction]
    and [VACCS_UniqueDual] are reused as they stand, so that Erlang systems and
    VACCS observers speak of the same actions. *)

Section Erlang_Instance.

Context `{EP : Erlang_Program}.

(** ** Multiset helpers *)

Lemma sys_split (c d : comp) (A B : sys) :
  c ≠ d → {[+ c +]} ⊎ A = {[+ d +]} ⊎ B →
  ∃ C, A = {[+ d +]} ⊎ C ∧ B = {[+ c +]} ⊎ C.
Proof.
  intros hne heq. exists (A ∖ {[+ d +]}). split; multiset_solver.
Qed.

Lemma sys_cancel (c : comp) (A B : sys) : {[+ c +]} ⊎ A = {[+ c +]} ⊎ B → A = B.
Proof. multiset_solver. Qed.

(** ** Shape of the external transitions *)

Lemma erl_out_inv S p v T :
  S ⟶ₑ[out_act p v] T ↔ S = ⟪p, v⟫ ⊎ T.
Proof.
  split.
  - intros hl. inversion hl; subst. by simplify_eq.
  - intros ->. apply ErlOut.
Qed.

(** Inputs block, outputs do not. *)
Lemma in_act_blocking p v : blocking (in_act p v : erl_act).
Proof.
  intros hnb. simpl in hnb. unfold non_blocking_output, is_output in hnb.
  destruct hnb as (a & heq). discriminate heq.
Qed.

Lemma out_act_non_blocking p v : non_blocking (out_act p v : erl_act).
Proof. by exists (cst p, cst v). Qed.

(** An Erlang system only performs actions over closed data. *)
Lemma erl_out_shape S a T :
  S ⟶ₑ[ActOut a] T → ∃ p v, a = (cst p, cst v) ∧ S = ⟪p, v⟫ ⊎ T.
Proof.
  intros hl. inversion hl; subst. simplify_eq. by exists p, v.
Qed.

Lemma erl_in_shape S a T : S ⟶ₑ[ActIn a] T → ∃ p v, a = (cst p, cst v).
Proof.
  intros hl. inversion hl; subst. simplify_eq. by exists p, v.
Qed.

Lemma erl_in_inv S p v T :
  S ⟶ₑ[in_act p v] T →
  ∃ n e cls ao e' body S0,
    estep e = Some (LRec cls ao, e') ∧ match_cls cls v = Some body ∧
    S = ⟨p, n, e⟩ ⊎ S0 ∧ T = ⟨p, n, hfill e' body⟩ ⊎ S0.
Proof.
  intros hl. inversion hl; subst. simplify_eq.
  by exists n, e, cls, ao, e', body, S0.
Qed.

(** ** The key lemma: a message in transit is only used by a communication

    A transition of [⟪p,v⟫ ⊎ S] either does not use the message at all, or is
    the output of that very message, or is the internal communication that the
    environment could have performed as the input [ActIn (p,v)].  This is the
    combinatorial content of all the Selinger axioms. *)

Lemma erl_drop_msg S p v α T :
  (⟪p, v⟫ ⊎ S) ⟶ₑ{α} T →
    (∃ R, S ⟶ₑ{α} R ∧ T = ⟪p, v⟫ ⊎ R)
  ∨ (α = ActExt (out_act p v) ∧ T = S)
  ∨ (α = τ ∧ S ⟶ₑ[in_act p v] T).
Proof.
  intros hl. inversion hl; subst.
  all: try (assert (CMsg p v ≠ CProc p0 n e) as hne by (by intros ?)).
  (* ErlComm: either the message consumed is the one we singled out, in which
     case the environment could have provided it, or it is another one. *)
  6:{ destruct (decide (CMsg p0 v0 = CMsg p v)) as [heqm | hnem].
      - simplify_eq.
        assert (S = ⟨p, n, e⟩ ⊎ S0) as -> by multiset_solver.
        right; right. split; [done |]. eapply ErlIn; eassumption.
      - assert (∃ D, S = ⟨p0, n, e⟩ ⊎ ⟪p0, v0⟫ ⊎ D ∧ S0 = ⟪p, v⟫ ⊎ D) as (D & -> & ->).
        { exists (S0 ∖ ⟪p, v⟫). split; multiset_solver. }
        left. exists (⟨p0, n, hfill e' body⟩ ⊎ D).
        split; [eapply ErlComm; eassumption | multiset_solver]. }
  (* All the rules driven by a process: the message is untouched. *)
  1-6: assert (∃ C, S = ⟨p0, n, e⟩ ⊎ C ∧ S0 = ⟪p, v⟫ ⊎ C) as (C & -> & ->)
         by (exists (S ∖ ⟨p0, n, e⟩); split; multiset_solver).
  1:{ left. eexists. split; [eapply ErlTau; eassumption | multiset_solver]. }
  1:{ left. eexists. split; [eapply ErlSend; eassumption | multiset_solver]. }
  1:{ left. eexists. split; [eapply ErlSelf; eassumption | multiset_solver]. }
  1:{ left. eexists. split; [eapply ErlSpawn; eassumption | multiset_solver]. }
  1:{ left. eexists. split; [eapply ErlTimeout; eassumption | multiset_solver]. }
  1:{ left. eexists. split; [eapply ErlIn; eassumption | multiset_solver]. }
  (* ErlOut: either it is the message we singled out, or another one. *)
  1:{ destruct (decide (CMsg p0 v0 = CMsg p v)) as [heqm | hnem].
      - simplify_eq. right; left. split; [done | multiset_solver].
      - assert (∃ C, S = ⟪p0, v0⟫ ⊎ C ∧ T = ⟪p, v⟫ ⊎ C) as (C & -> & ->)
          by (exists (T ∖ ⟪p, v⟫); split; multiset_solver).
        left. eexists. split; [apply ErlOut | done]. }
Qed.

(** ** Computing the successors

    The expression semantics is a function and a system is a finite multiset,
    so the set of successors of a system is computable.  Everything decidable
    that the framework requires follows. *)

Definition tau_succ (S : sys) (c : comp) : list sys :=
  match c with
  | CMsg _ _ => []
  | CProc p n e =>
      match estep e with
      | None => []
      | Some (LTau, e') => [⟨p, n, e'⟩ ⊎ (S ∖ ⟨p, n, e⟩)]
      | Some (LSend q w, e') => [⟨p, n, e'⟩ ⊎ ⟪q, w⟫ ⊎ (S ∖ ⟨p, n, e⟩)]
      | Some (LSelf, e') => [⟨p, n, hfill e' (EVal (VPid p))⟩ ⊎ (S ∖ ⟨p, n, e⟩)]
      | Some (LSpawn f vs, e') =>
          match fun_def f with
          | None => []
          | Some (xs, body) =>
              if decide (length xs = length vs)
              then [⟨p, n + 1, hfill e' (EVal (VPid (n :: p)))⟩
                    ⊎ ⟨n :: p, 0, subst (zip xs vs) body⟩ ⊎ (S ∖ ⟨p, n, e⟩)]
              else []
          end
      | Some (LRec cls ao, e') =>
          (match ao with
           | Some a => [⟨p, n, hfill e' a⟩ ⊎ (S ∖ ⟨p, n, e⟩)]
           | None => []
           end)
          ++ omap (λ d, match d with
                        | CProc _ _ _ => None
                        | CMsg p' w =>
                            if decide (p' = p)
                            then match match_cls cls w with
                                 | Some body =>
                                     Some (⟨p, n, hfill e' body⟩
                                           ⊎ ((S ∖ ⟨p, n, e⟩) ∖ ⟪p', w⟫))
                                 | None => None
                                 end
                            else None
                        end) (elements (S ∖ ⟨p, n, e⟩))
      end
  end.

Definition in_succ (p : pid) (v : val) (S : sys) (c : comp) : list sys :=
  match c with
  | CMsg _ _ => []
  | CProc p' n e =>
      if decide (p' = p)
      then match estep e with
           | Some (LRec cls ao, e') =>
               match match_cls cls v with
               | Some body => [⟨p', n, hfill e' body⟩ ⊎ (S ∖ ⟨p', n, e⟩)]
               | None => []
               end
           | _ => []
           end
      else []
  end.

Definition erl_succ (S : sys) (α : Act erl_act) : list sys :=
  match α with
  | τ => elements S ≫= tau_succ S
  | ActExt (ActIn (cst p, cst v)) => elements S ≫= in_succ p v S
  | ActExt (ActOut (cst p, cst v)) => if decide (CMsg p v ∈ S) then [S ∖ ⟪p, v⟫] else []
  | ActExt _ => []
  end.

(** *** [erl_succ] enumerates exactly the successors *)

Lemma erl_succ_sound S α T : T ∈ erl_succ S α → S ⟶ₑ{α} T.
Proof.
  (* the actions over open data have no successor *)
  destruct α as [[[[p | k] [v | k']] | [[p | k] [v | k']]] |]; simpl;
    try (by inversion 1).
  3:{ intros (c & hT & hc)%list_elem_of_bind.
      assert (c ∈ S) as hcS by (by apply gmultiset_elem_of_elements).
      destruct c as [p n e | p v]; [| by inversion hT].
      remember (S ∖ ⟨p, n, e⟩) as R eqn:hR.
      assert (S = ⟨p, n, e⟩ ⊎ R) as heq2 by (subst R; multiset_solver).
      clear hR hc hcS. subst S. unfold tau_succ in hT.
      destruct (estep e) as [[l e'] |] eqn:hst; [| by inversion hT].
      destruct l as [| q w | cls ao | f vs |].
      all: assert (({[+ CProc p n e +]} ⊎ R) ∖ {[+ CProc p n e +]} = R) as hd
             by multiset_solver.
      all: rewrite hd in hT; clear hd.
      1:{ apply list_elem_of_singleton in hT as ->. by apply ErlTau. }
      1:{ apply list_elem_of_singleton in hT as ->. by apply ErlSend. }
      3:{ apply list_elem_of_singleton in hT as ->. by apply ErlSelf. }
      2:{ destruct (fun_def f) as [[xs body] |] eqn:hfd; [| by inversion hT].
          destruct (decide (length xs = length vs)) as [hlen |]; [| by inversion hT].
          apply list_elem_of_singleton in hT as ->. eapply ErlSpawn; eassumption. }
      apply elem_of_app in hT as [h1 | h2].
      - destruct ao as [a |]; [| by inversion h1].
        apply list_elem_of_singleton in h1 as ->. eapply ErlTimeout; eassumption.
      - apply list_elem_of_omap in h2 as (d & hd & hsome).
        destruct d as [p2 n2 e2 | p2 w]; [by inversion hsome |].
        destruct (decide (p2 = p)) as [-> |]; [| by inversion hsome].
        destruct (match_cls cls w) as [body |] eqn:hm; [| by inversion hsome].
        injection hsome as <-.
        assert (CMsg p w ∈ R) as hin by (by apply gmultiset_elem_of_elements).
        assert ({[+ CProc p n e +]} ⊎ R = ⟨p, n, e⟩ ⊎ ⟪p, w⟫ ⊎ (R ∖ ⟪p, w⟫)) as ->
          by multiset_solver.
        eapply ErlComm; eassumption. }
  1:{ intros (c & hT & hc)%list_elem_of_bind.
      assert (c ∈ S) as hcS by (by apply gmultiset_elem_of_elements).
      destruct c as [p' n e | p' w]; [| by inversion hT].
      remember (S ∖ ⟨p', n, e⟩) as R eqn:hR.
      assert (S = ⟨p', n, e⟩ ⊎ R) as heq2 by (subst R; multiset_solver).
      clear hR hc hcS. subst S. unfold in_succ in hT.
      assert (({[+ CProc p' n e +]} ⊎ R) ∖ {[+ CProc p' n e +]} = R) as hd
        by multiset_solver.
      rewrite hd in hT. clear hd.
      destruct (decide (p' = p)) as [-> |]; [| by inversion hT].
      destruct (estep e) as [[l e'] |] eqn:hst; [| by inversion hT].
      destruct l as [| q w | cls ao | f vs |]; try (by inversion hT).
      destruct (match_cls cls v) as [body |] eqn:hm; [| by inversion hT].
      apply list_elem_of_singleton in hT as ->. eapply ErlIn; eassumption. }
  1:{ destruct (decide (CMsg p v ∈ S)) as [hin | hnin]; [| by inversion 1].
      intros ->%list_elem_of_singleton.
      assert (S = ⟪p, v⟫ ⊎ (S ∖ ⟪p, v⟫)) as heq by multiset_solver.
      rewrite heq at 1. apply ErlOut. }
Qed.

Lemma erl_succ_complete S α T : S ⟶ₑ{α} T → T ∈ erl_succ S α.
Proof.
  intros hl. inversion hl; subst; simpl.
  all: try (assert (∀ (X : sys), (⟨p, n, e⟩ ⊎ X) ∖ ⟨p, n, e⟩ = X) as hd
              by (intros; multiset_solver)).
  all: try (apply list_elem_of_bind; exists (CProc p n e); split;
            [ unfold tau_succ, in_succ
            | apply gmultiset_elem_of_elements; multiset_solver ]).
  1:{ rewrite H. simpl. rewrite (hd S0). by apply list_elem_of_singleton. }
  1:{ rewrite H. simpl. rewrite (hd S0). by apply list_elem_of_singleton. }
  1:{ rewrite H. simpl. rewrite (hd S0). by apply list_elem_of_singleton. }
  1:{ rewrite H. simpl. rewrite H0. simpl.
      destruct (decide (length xs = length vs)) as [? | ?]; [| done].
      rewrite (hd S0). by apply list_elem_of_singleton. }
  1:{ rewrite H. simpl. rewrite (hd S0). apply elem_of_cons. by left. }
  2:{ rewrite decide_True; [| done]. rewrite H. simpl. rewrite H0. rewrite (hd S0).
      by apply list_elem_of_singleton. }
  2:{ rewrite decide_True; [| multiset_solver].
      apply list_elem_of_singleton. multiset_solver. }
  1:{ assert ((⟨p, n, e⟩ ⊎ ⟪p, v⟫ ⊎ S0) ∖ ⟨p, n, e⟩ = ⟪p, v⟫ ⊎ S0) as hd2
        by multiset_solver.
      rewrite H. simpl. rewrite hd2.
      apply elem_of_app. right. apply list_elem_of_omap. exists (CMsg p v). split.
      - apply gmultiset_elem_of_elements. multiset_solver.
      - rewrite decide_True; [| done]. rewrite H0. f_equal. multiset_solver. }
Qed.

(** ** The LTS *)

Definition erl_refuses (S : sys) (α : Act erl_act) : Prop := erl_succ S α = [].

#[global] Instance erl_refuses_dec S α : Decision (erl_refuses S α).
Proof. unfold erl_refuses. apply _. Defined.

Definition erl_step_dec S α T : Decision (S ⟶ₑ{α} T).
Proof.
  destruct (decide (T ∈ erl_succ S α)) as [h | h].
  - left. by apply erl_succ_sound.
  - right. intros hl. apply h. by apply erl_succ_complete.
Defined.

Definition erl_refuses_spec1 S α : ¬ erl_refuses S α → { T | S ⟶ₑ{α} T }.
Proof.
  intros h. unfold erl_refuses in h.
  destruct (erl_succ S α) as [| T l] eqn:heq; [done |].
  exists T. apply erl_succ_sound. rewrite heq. apply elem_of_cons. by left.
Defined.

Definition erl_refuses_spec2 S α : { T | S ⟶ₑ{α} T } → ¬ erl_refuses S α.
Proof.
  intros (T & hl) heq. unfold erl_refuses in heq.
  apply erl_succ_complete in hl. rewrite heq in hl. by inversion hl.
Defined.

#[global] Program Instance Erl_gLts : gLts sys VACCS_ExtAction :=
  {| lts_step S α T := S ⟶ₑ{α} T ;
     lts_state_eqdec := _ ;
     lts_step_decidable S α T := erl_step_dec S α T ;
     lts_refuses := erl_refuses ;
     lts_refuses_decidable S α := erl_refuses_dec S α |}.
Next Obligation. intros. by apply erl_refuses_spec1. Defined.
Next Obligation. intros. by apply erl_refuses_spec2. Defined.

(** The structural congruence is equality: parallel composition is multiset
    union, which is associative, commutative and has [∅] as a unit. *)
#[global] Program Instance Erl_gLtsEq : gLtsEq sys VACCS_ExtAction :=
  {| gLtsEq_gLts := Erl_gLts ;
     eq_rel S T := S = T |}.
Next Obligation.
  intros p q α (R & <- & hl). exists q. split; [exact hl | reflexivity].
Defined.

(** ** The multiset of messages in transit

    It plays the role of the multiset of pending outputs of an output-buffered
    agent. *)

Definition comp_out (c : comp) : option erl_act :=
  match c with CMsg p v => Some (out_act p v) | CProc _ _ _ => None end.

Definition erl_mo (S : sys) : gmultiset erl_act :=
  list_to_set_disj (omap comp_out (elements S)).

Lemma erl_mo_union X Y : erl_mo (X ⊎ Y) = erl_mo X ⊎ erl_mo Y.
Proof.
  unfold erl_mo.
  rewrite (list_to_set_disj_perm _ _
             (omap_Permutation comp_out _ _ (gmultiset_elements_disj_union X Y))).
  by rewrite omap_app, list_to_set_disj_app.
Qed.

Lemma erl_mo_msg p v : erl_mo ⟪p, v⟫ = {[+ out_act p v +]}.
Proof.
  unfold erl_mo. rewrite gmultiset_elements_singleton. simpl. multiset_solver.
Qed.

Lemma erl_mo_elem_of S η : η ∈ erl_mo S → ∃ p v, η = out_act p v ∧ CMsg p v ∈ S.
Proof.
  unfold erl_mo. intros (c & hc & hout)%elem_of_list_to_set_disj%list_elem_of_omap.
  destruct c as [p n e | p v]; [by inversion hout |].
  injection hout as <-. exists p, v. split; [done | by apply gmultiset_elem_of_elements].
Qed.

(** ** The Selinger axioms

    Every one of them follows from [erl_drop_msg]: an output is the release of a
    message in transit, and a message in transit interferes with nothing but the
    communication that consumes it. *)

#[global] Program Instance Erl_gLtsOba : gLtsOba sys.
Next Obligation. (* NB-DELAY *)
  intros p q r η α nb hl1 hl2.
  destruct nb as (a & ->). apply erl_out_shape in hl1 as (p0 & v & -> & ->).
  exists (⟪p0, v⟫ ⊎ r). split; [by apply erl_lts_par_l |].
  exists r. split; [apply ErlOut | reflexivity].
Qed.
Next Obligation. (* NB-CONFLUENCE *)
  intros p q1 q2 η μ nb hne hl1 hl2.
  destruct nb as (a & ->). apply erl_out_shape in hl1 as (p0 & v & -> & ->).
  apply erl_drop_msg in hl2 as [(R & hR & ->) | [(heq & _) | (heq & _)]].
  - exists R. split; [exact hR |]. exists R. split; [apply ErlOut | reflexivity].
  - injection heq as ->. done.
  - discriminate heq.
Qed.
Next Obligation. (* NB-TAU *)
  intros p q1 q2 η nb hl1 hl2.
  destruct nb as (a & ->). apply erl_out_shape in hl1 as (p0 & v & -> & ->).
  apply erl_drop_msg in hl2 as [(R & hR & ->) | [(heq & _) | (_ & hin)]].
  - left. exists R. split; [exact hR |]. exists R. split; [apply ErlOut | reflexivity].
  - discriminate heq.
  - right. exists (in_act p0 v). split; [done |].
    exists q2. split; [exact hin | reflexivity].
Qed.
Next Obligation. (* NB-DETERMINACY *)
  intros p1 p2 p3 η nb hl1 hl2.
  destruct nb as (a & ->).
  apply erl_out_shape in hl1 as (p0 & v & -> & ->). apply erl_out_inv in hl2.
  change (p2 = p3). multiset_solver.
Qed.
Next Obligation. (* BACKWARDS-NB-DETERMINACY *)
  intros p1 p2 q1 q2 η nb hl1 hl2 heq.
  destruct nb as (a & ->).
  apply erl_out_shape in hl1 as (p0 & v & -> & ->).
  apply erl_out_inv in hl2.
  change (q1 = q2) in heq. change (⟪p0, v⟫ ⊎ q1 = p2). multiset_solver.
Qed.

(** ** FEEDBACK

    Releasing a message and receiving it back is the internal communication. *)

#[global] Program Instance Erl_gLtsObaFB : gLtsObaFB sys erl_act.
Next Obligation.
  intros p1 p2 p3 η β nb duo hl1 hl2.
  destruct nb as (a & ->).
  symmetry in duo. apply simplify_match_output in duo as ->.
  apply erl_out_shape in hl1 as (p0 & v & heqa & ->). simplify_eq.
  apply erl_in_inv in hl2 as (n & e & cls & ao & e' & body & S0 & hst & hm & -> & ->).
  exists (⟨p0, n, hfill e' body⟩ ⊎ S0). split; [| reflexivity].
  assert (⟪p0, v⟫ ⊎ (⟨p0, n, e⟩ ⊎ S0) = ⟨p0, n, e⟩ ⊎ ⟪p0, v⟫ ⊎ S0) as ->
    by multiset_solver.
  eapply ErlComm; eassumption.
Qed.

(** ** The messages in transit form the output multiset *)

#[global] Program Instance Erl_FiniteOutputChain : FiniteOutputChain_LtsOba sys :=
  {| lts_oba_mo := erl_mo |}.
Next Obligation.
  intros S η T nb hl. destruct nb as (a & ->).
  apply erl_out_shape in hl as (p0 & v & -> & ->).
  rewrite erl_mo_union, erl_mo_msg. multiset_solver.
Defined.
Next Obligation.
  intros S η hin. destruct η as [[[p | k] [v | k']] | [[p | k] [v | k']]];
    try (by exfalso; apply erl_mo_elem_of in hin as (p' & v' & heq & _); discriminate heq).
  (* only [ActOut (cst p, cst v)] is left *)
  exists (S ∖ ⟪p, v⟫).
  apply erl_mo_elem_of in hin as (p' & v' & heq & hmem). injection heq as -> ->.
  split; [by exists (cst p', cst v') |].
  assert (S = ⟪p', v'⟫ ⊎ (S ∖ ⟪p', v'⟫)) as heq2 by multiset_solver.
  rewrite heq2 at 1. apply ErlOut.
Defined.
Next Obligation.
  intros S η T nb hl. destruct nb as (a & ->).
  apply erl_out_shape in hl as (p0 & v & -> & ->).
  by rewrite erl_mo_union, erl_mo_msg.
Defined.

(** ** Finite image *)

#[global] Program Instance Erl_FiniteImage : FiniteImagegLts sys erl_act.
Next Obligation.
  intros S α. eapply (in_list_finite (erl_succ S α)).
  intros T htr%bool_decide_unpack. by apply erl_succ_complete.
Defined.

(** ** Available outputs *)

Lemma erl_out_dom S p v : CMsg p v ∈ S → out_act p v ∈ dom (erl_mo S).
Proof.
  intros hmem. apply gmultiset_elem_of_dom.
  assert (S = ⟪p, v⟫ ⊎ (S ∖ ⟪p, v⟫)) as -> by multiset_solver.
  rewrite erl_mo_union, erl_mo_msg. multiset_solver.
Qed.

Lemma erl_dom_out S ξ : ξ ∈ dom (erl_mo S) → ∃ p v, ξ = out_act p v ∧ CMsg p v ∈ S.
Proof. intros hin%gmultiset_elem_of_dom. by apply erl_mo_elem_of. Qed.

Lemma erl_out_of_dom S ξ : ξ ∈ dom (erl_mo S) → { T | S ⟶ₑ[ξ] T }.
Proof.
  intros hin.
  destruct ξ as [[[p | k] [v | k']] | [[p | k] [v | k']]];
    try (by exfalso; apply erl_dom_out in hin as (p' & v' & heq & _); discriminate heq).
  exists (S ∖ ⟪p, v⟫).
  apply erl_dom_out in hin as (p' & v' & heq & hmem). injection heq as -> ->.
  assert (S = ⟪p', v'⟫ ⊎ (S ∖ ⟪p', v'⟫)) as heq2 by multiset_solver.
  rewrite heq2 at 1. apply ErlOut.
Defined.

(** ** Interaction with the forwarder multiset: the axioms required by [toFW] *)

#[global] Program Instance Erl_Inter_MO :
  Prop_of_Inter sys (MO erl_act) erl_act fw_inter :=
  {| lts_essential_actions_left S := empty ;
     lts_essential_actions_right m := dom (MO_without_not_nb m) ;
     lts_co_inter_action_right m := fun x => empty |}.
Next Obligation.
  intros ? ? hin; simpl in *. inversion hin.
Qed.
Next Obligation.
  intros m ξ hin; simpl in *.
  apply gmultiset_elem_of_dom in hin.
  assert (ξ ∈ MO_without_not_nb m) as hmem by eauto.
  apply lts_MO_nb_with_nb_spec1 in hmem as (nb & heq).
  apply gmultiset_disj_union_difference' in heq.
  exists (m ∖ {[+ ξ +]}). rewrite heq at 1.
  by apply lts_multiset_minus.
Defined.
Next Obligation.
  intros ? ? ? m ? m' ? ? hinter; simpl in *.
  right. destruct hinter as (duo & nb).
  eapply non_blocking_action_in_ms in nb as heq2; eauto.
  rewrite <- heq2.
  assert (MO_without_not_nb ({[+ μ2 +]} ⊎ m') = {[+ μ2 +]} ⊎ MO_without_not_nb m') as ->
    by (by apply lts_MO_nb_spec1).
  apply gmultiset_elem_of_dom. multiset_solver.
Defined.
Next Obligation.
  intros ξ S; simpl in *.
  destruct (decide (non_blocking ξ)) as [nb | not_nb].
  - exact {[ co ξ ]}.
  - exact empty.
Defined.
Next Obligation.
  intros S S' ξ μ m hmem hl hinter; simpl in *.
  unfold Erl_Inter_MO_obligation_4.
  destruct hinter as (duo & nb). rewrite decide_True; [| eauto].
  assert (μ = co ξ) as -> by (apply VACCS_UniqueDual; by symmetry). set_solver.
Defined.
Next Obligation.
  intros ? ? ? ? m hmem hl hinter; simpl in *. inversion hmem.
Qed.

(** ** Interaction of two systems: parallel composition *)

#[global] Program Instance Erl_Inter_par : Prop_of_Inter sys sys erl_act dual :=
  {| lts_essential_actions_left S := dom (erl_mo S) ;
     lts_essential_actions_right S := dom (erl_mo S) |}.
Next Obligation. intros S ξ hin. by apply erl_out_of_dom. Defined.
Next Obligation. intros S ξ hin. by apply erl_out_of_dom. Defined.
Next Obligation.
  intros S1 μ1 S1' S2 μ2 S2' hl1 hl2 hinter.
  destruct μ1 as [a | a].
  - right. apply simplify_match_input in hinter as ->.
    apply erl_out_shape in hl2 as (p & v & -> & ->).
    apply erl_out_dom. multiset_solver.
  - left. apply erl_out_shape in hl1 as (p & v & -> & ->).
    apply erl_out_dom. multiset_solver.
Defined.
Next Obligation.
  intros ξ S. destruct ξ as [a | a]; [exact empty | exact {[ ActIn a ]}].
Defined.
Next Obligation.
  intros S1 S1' ξ μ S2 hmem hl hinter; simpl in *.
  unfold Erl_Inter_par_obligation_4.
  destruct ξ as [a | a].
  - exfalso. apply erl_dom_out in hmem as (p' & v' & heq & _). discriminate heq.
  - symmetry in hinter. apply simplify_match_output in hinter as ->. set_solver.
Defined.
Next Obligation.
  intros ξ S. destruct ξ as [a | a]; [exact empty | exact {[ ActIn a ]}].
Defined.
Next Obligation.
  intros S2 S2' ξ μ S1 hmem hl hinter; simpl in *.
  unfold Erl_Inter_par_obligation_6.
  destruct ξ as [a | a].
  - exfalso. apply erl_dom_out in hmem as (p' & v' & heq & _). discriminate heq.
  - apply simplify_match_output in hinter as ->. set_solver.
Defined.

End Erlang_Instance.
