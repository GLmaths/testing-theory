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
(* * lqCCS: the programming language alone

    The LTS of lqCCS processes *without* the quantum memory.  As the program
    side of the Harmony lemma ([Harmony_lemma/Harmony.v], [pstep]), quantum
    operations are actions addressed to the memory:

    - [AOp E q̃]: request the superoperator [E] on [q̃];
    - [AMeas M q̃ x]: measure [q̃] with [M] and store the outcome in [x]; the
      continuation is left open in [x], and the composition with the memory
      substitutes each outcome [k] with its probability (as [Br m xs] in
      [Harmony.v]).  One step of the program is then one measurement step of
      lqCCS, whatever the outcome.

    The rules follow Figure 4 of Ceragioli, Gadducci, Lomurno, Tedeschi
    (arXiv:2604.23756), with no quantum state.  Each step carries the
    scheduler that selects it: a tag [t], or a pair [(t, t')] for an internal
    synchronisation.  Outputs are asynchronous ([PSend] has no continuation).

    That a received qubit exists in the memory is checked by the
    composition, which knows the memory.

    Deliberate difference with the paper: no rule checks that a received
    qubit is not already owned, neither by the receiver (Recv) nor by a
    parallel component (ParL/ParR).  The qubit sent is owned by its sender,
    so on well-typed terms (disjoint [Σ] in parallel) these checks never
    fire.  Dropping them makes the semantics independent of the qubits
    owned ([qnames]): the structural congruence ([lqCCS_Congruence.v]),
    associativity included, is then a bisimulation on all terms, and the
    output-buffered axioms hold.  Typing can be added later as a
    hypothesis. *)
(* end hide *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list sets.
From TestingTheory Require Import lqCCS_Syntax.
(* begin hide *)
(* ** Schedulers and labels *)

Inductive Sched : Type :=
| STag (t : tag)
| SPair (t t' : tag).

#[global] Instance Sched_eq_dec : EqDecision Sched.
Proof. solve_decision. Defined.

(* Visible actions of a program. *)
Inductive pact : Type :=
| AOut (c : chan) (v : val)
| AIn (c : chan) (v : val)
| AOp (E : sop) (qs : list qubit)
| AMeas (M : meas) (qs : list qubit) (x : var).

#[global] Instance pact_eq_dec : EqDecision pact.
Proof. solve_decision. Defined.

Inductive plbl : Type :=
| LTau (s : Sched)
| LAct (t : tag) (a : pact).

#[global] Instance plbl_eq_dec : EqDecision plbl.
Proof. solve_decision. Defined.

(* ** Auxiliary definitions *)

Definition eval_qubit (e : exp) : option qubit :=
  match eval e with Some (VQubit q) => Some q | _ => None end.

Definition eval_qubits (es : list exp) : option (list qubit) :=
  mapM eval_qubit es.

Definition val_qubits (v : val) : list qubit :=
  match v with VQubit q => [q] | _ => [] end.

Fixpoint exp_qubits (e : exp) : list qubit :=
  match e with
  | EVar _ => []
  | EVal v => val_qubits v
  | ENot e => exp_qubits e
  | EOr e1 e2 | ELe e1 e2 | EEq e1 e2 => exp_qubits e1 ++ exp_qubits e2
  end.

Definition prefix_qubits (α : prefix) : list qubit :=
  match α with
  | PTau _ | PTauPair _ _ | PRecv _ _ _ => []
  | POp _ _ es | PMeas _ _ es _ => concat (map exp_qubits es)
  end.

(* [qnames P]: the qubits owned by [P]. *)
Fixpoint qnames (P : proc) : list qubit :=
  match P with
  | PSend _ _ e => exp_qubits e
  | PIte e P Q => exp_qubits e ++ qnames P ++ qnames Q
  | PPar P Q => qnames P ++ qnames Q
  | PRes P _ => qnames P
  | PG g => gqnames g
  end
with gqnames (g : guard) : list qubit :=
  match g with
  | GNil es => concat (map exp_qubits es)
  | GSucc => []
  | GPre α P => prefix_qubits α ++ qnames P
  | GSum g1 g2 => gqnames g1 ++ gqnames g2
  end.

(* [l] is a communication on [c]. *)
Definition on_chan (c : chan) (l : plbl) : Prop :=
  ∃ t v, l = LAct t (AOut c v) ∨ l = LAct t (AIn c v).

(* ** Transitions *)

(* Steps of a guard: a prefix, or one side of a sum. *)
Inductive gstep : guard → plbl → proc → Prop :=
| gs_tau t P :
    gstep (GPre (PTau t) P) (LTau (STag t)) P
| gs_taupair t t' P :
    gstep (GPre (PTauPair t t') P) (LTau (SPair t t')) P
| gs_recv t c x v P :
    gstep (GPre (PRecv t c x) P) (LAct t (AIn c v)) (subst P x v)
| gs_op t E es qs P :
    eval_qubits es = Some qs →
    gstep (GPre (POp t E es) P) (LAct t (AOp E qs)) P
| gs_meas t M es x qs P :
    eval_qubits es = Some qs →
    gstep (GPre (PMeas t M es x) P) (LAct t (AMeas M qs x)) P
| gs_sumL g1 g2 l P' :
    gstep g1 l P' → gstep (GSum g1 g2) l P'
| gs_sumR g1 g2 l P' :
    gstep g2 l P' → gstep (GSum g1 g2) l P'.

Inductive pstep : proc → plbl → proc → Prop :=
| ps_guard g l P' :
    gstep g l P' → pstep (PG g) l P'
| ps_send t c e v :
    eval e = Some v →
    pstep (PSend t c e) (LAct t (AOut c v)) (PG (GNil []))
| ps_iteT e P Q l P' :
    eval e = Some (VBool true) → pstep P l P' → pstep (PIte e P Q) l P'
| ps_iteF e P Q l Q' :
    eval e = Some (VBool false) → pstep Q l Q' → pstep (PIte e P Q) l Q'
| ps_parL P Q l P' :
    pstep P l P' → pstep (PPar P Q) l (PPar P' Q)
| ps_parR P Q l Q' :
    pstep Q l Q' → pstep (PPar P Q) l (PPar P Q')
| ps_syncL P Q t t' c v P' Q' :
    pstep P (LAct t (AOut c v)) P' → pstep Q (LAct t' (AIn c v)) Q' →
    pstep (PPar P Q) (LTau (SPair t t')) (PPar P' Q')
| ps_syncR P Q t t' c v P' Q' :
    pstep P (LAct t (AIn c v)) P' → pstep Q (LAct t' (AOut c v)) Q' →
    pstep (PPar P Q) (LTau (SPair t t')) (PPar P' Q')
| ps_res P c l P' :
    ¬ on_chan c l → pstep P l P' → pstep (PRes P c) l (PRes P' c).

(* A guard never outputs. *)
Lemma gstep_not_out g t c v P' : ¬ gstep g (LAct t (AOut c v)) P'.
Proof. intros Hs. remember (LAct t (AOut c v)) as l. induction Hs; simplify_eq; auto. Qed.

(* ** Success of an observer: [①] at top level

    [①] in parallel, under a restriction, in a sum, or in the branch of a
    conditional that is taken. *)

Fixpoint ggoodb (g : guard) : bool :=
  match g with
  | GSucc => true
  | GSum g1 g2 => ggoodb g1 || ggoodb g2
  | _ => false
  end.

Fixpoint goodb (P : proc) : bool :=
  match P with
  | PSend _ _ _ => false
  | PIte e P Q =>
      match eval e with
      | Some (VBool true) => goodb P
      | Some (VBool false) => goodb Q
      | _ => false
      end
  | PPar P Q => goodb P || goodb Q
  | PRes P _ => goodb P
  | PG g => ggoodb g
  end.

Definition good (P : proc) : Prop := goodb P = true.

#[global] Instance good_dec P : Decision (good P).
Proof. unfold good. apply _. Defined.

(* ** Free variables *)

Fixpoint exp_fv (e : exp) : list var :=
  match e with
  | EVar x => [x]
  | EVal _ => []
  | ENot e => exp_fv e
  | EOr e1 e2 | ELe e1 e2 | EEq e1 e2 => exp_fv e1 ++ exp_fv e2
  end.

Definition prefix_fv (α : prefix) : list var :=
  match α with
  | PTau _ | PTauPair _ _ | PRecv _ _ _ => []
  | POp _ _ es | PMeas _ _ es _ => concat (map exp_fv es)
  end.

Fixpoint fv (P : proc) : list var :=
  match P with
  | PSend _ _ e => exp_fv e
  | PIte e P Q => exp_fv e ++ fv P ++ fv Q
  | PPar P Q => fv P ++ fv Q
  | PRes P _ => fv P
  | PG g => gfv g
  end
with gfv (g : guard) : list var :=
  match g with
  | GNil es => concat (map exp_fv es)
  | GSucc => []
  | GPre α P =>
      prefix_fv α ++
        (match prefix_binder α with
         | Some x => filter (λ y, y ≠ x) (fv P)
         | None => fv P
         end)
  | GSum g1 g2 => gfv g1 ++ gfv g2
  end.

Lemma exp_subst_fresh e x v : x ∉ exp_fv e → exp_subst e x v = e.
Proof.
  induction e; simpl; intros Hx; rewrite ?elem_of_app in Hx;
    try (f_equal; naive_solver).
  case_decide; [set_solver | done].
Qed.

Lemma exps_subst_fresh es x v :
  x ∉ concat (map exp_fv es) → exps_subst es x v = es.
Proof.
  induction es as [|e es IH]; simpl; [done|]. rewrite elem_of_app.
  intros Hx. unfold exps_subst in *. simpl. f_equal; [apply exp_subst_fresh|apply IH]; tauto.
Qed.

Lemma prefix_subst_fresh α x v : x ∉ prefix_fv α → prefix_subst α x v = α.
Proof. destruct α; simpl; intros Hx; try done; by rewrite exps_subst_fresh. Qed.

Lemma subst_gsubst_fresh x v :
  (∀ P, x ∉ fv P → subst P x v = P) ∧ (∀ g, x ∉ gfv g → gsubst g x v = g).
Proof.
  apply proc_guard_ind; simpl; intros; rewrite ?elem_of_app in *.
  - by rewrite exp_subst_fresh.
  - rewrite exp_subst_fresh, H, H0; tauto.
  - rewrite H, H0; tauto.
  - by rewrite H.
  - by rewrite H.
  - by rewrite exps_subst_fresh.
  - done.
  - rewrite prefix_subst_fresh by tauto. f_equal. case_decide; [done|].
    apply H. destruct (prefix_binder α) eqn:Hb.
    + intros Hin. apply H0. right. apply list_elem_of_filter. split; [|done].
      intros ->. done.
    + tauto.
  - rewrite H, H0; tauto.
Qed.

Lemma subst_fresh P x v : x ∉ fv P → subst P x v = P.
Proof. apply subst_gsubst_fresh. Qed.

(* ** A sent qubit is owned by the sender *)

Lemma eval_qubit_in e q : eval e = Some (VQubit q) → q ∈ exp_qubits e.
Proof.
  destruct e; simpl; try discriminate.
  - intros [= ->]. simpl. set_solver.
  - by destruct (eval e) as [[]|].
  - by destruct (eval e1) as [[]|], (eval e2) as [[]|].
  - destruct (eval e1), (eval e2); try discriminate.
    by destruct (val_le _ _).
  - by destruct (eval e1), (eval e2).
Qed.

Lemma send_qubit_owned P t c q P' :
  pstep P (LAct t (AOut c (VQubit q))) P' → q ∈ qnames P.
Proof.
  intros Hs. remember (LAct t (AOut c (VQubit q))) as l eqn:El.
  induction Hs; simplify_eq; simpl; rewrite ?elem_of_app; try tauto.
  - by edestruct gstep_not_out.
  - by apply eval_qubit_in.
Qed.
(* end hide *)
