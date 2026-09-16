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

(** * Core Erlang: no trace-following observer exists

    The characterisations of the must preorder need a family of observers
    [gen : trace → T] following a trace, axiomatised by [test_spec]
    ([Completeness.v], [CompletenessASco.v]).  Three of its axioms suffice to
    make it unsatisfiable for Core Erlang:

    - (1) [gen s] never reports success;
    - (2) [gen (μ :: s) ⟶[μ] gen s];
    - (6) any action of [gen (β :: s)] other than the blocking [β] leads to
      success.

    Take the trace [ActIn (p,v) :: ActOut (q,w) :: ε].  By (2) the observer
    [gen (ActOut (q,w) :: ε)] performs the output [(q,w)!], so — the only rule
    producing an output being [ErlOut] — it /holds the message in transit/.  By
    (2) again, [gen (ActIn (p,v) :: ActOut (q,w) :: ε)] reaches it by a single
    input, and an input changes one process and no message: the message is
    /already/ in transit before the input.  So the observer can release it, by
    (6) the result reports success, and success is not destroyed by removing a
    message: the observer reported success before the input, against (1).

    In CCS-like calculi this is where the prefix does its work: in
    [c?(x).(a!v ∥ P)] the pending output [a!v] is inert until the input fires,
    and appears in the /same/ step.  Core Erlang has no output term: the only
    way to make a message available is [ESend], which is a τ, so a pending
    output is available either one step too early (as a message in transit) or
    one step too late (after the τ).  It cannot be guarded by an input.

    Two ways out, both changing something:

    - give the system semantics an /eager send/: a step performs the local
      reduction and immediately flushes every enabled [ESend] (sends are
      deterministic and always enabled, so this loses no behaviour).  The
      reception then produces the messages in transit atomically, and the
      observer above exists.  This is the semantics the characterisation needs.
    - or weaken [test_spec] so that the observer may follow the trace up to
      administrative τ steps, which means giving up the /strong/ bisimulation
      [⋍] of [gLtsEq].

    The statement below is the obstruction, not a claim about Erlang: it says
    that /this/ LTS has no trace-following observer. *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list numbers finite sets gmap gmultiset.
From TestingTheory Require Import ActTau InputOutputActions gLts Bisimulation
  Lts_OBA Testing_Predicate Erlang_Syntax Erlang_LTS Erlang_Instance Erlang_Good.

Section Erlang_Test_Dilemma.

Context `{EP : Erlang_Program}.

(** Releasing a message in transit does not create success: this is the
    converse half of [Testing_Predicate] for [good_Erl].  (For an /input/ it is
    false, and rightly so: that is how an observer reports success.) *)
Lemma good_Erl_of_out S T p v : S ⟶ₑ[out_act p v] T → good_Erl T → good_Erl S.
Proof.
  intros hl hg.
  apply erl_out_inv in hl as ->.
  apply good_Erl_spec in hg as (c & hin & ht). apply good_Erl_spec.
  exists c. split; [multiset_solver | done].
Qed.

(** ** The three axioms of [test_spec] that clash *)

Theorem no_trace_following_observer (gen : list erl_act → sys) :
  (* (1) *) (∀ s, ¬ good_Erl (gen s)) →
  (* (2) *) (∀ μ s, gen (μ :: s) ⟶ₑ[μ] gen s) →
  (* (6) *) (∀ β μ s t, blocking β → gen (β :: s) ⟶ₑ[μ] t → μ ≠ β → good_Erl t) →
  False.
Proof.
  intros h1 h2 h6.
  (* one input and one output, both arbitrary *)
  pose (p := @nil nat). pose (v := VNil). pose (q := @nil nat). pose (w := VNil).
  set (β := in_act p v). set (s := [out_act q w]).
  assert (blocking β) as hb by (subst β; apply in_act_blocking).
  (* the observer of [s] holds the message in transit *)
  assert (gen s = ⟪q, w⟫ ⊎ gen []) as hs by (apply erl_out_inv, (h2 (out_act q w) [])).
  (* one input leads from [gen (β :: s)] to [gen s] *)
  assert (gen (β :: s) ⟶ₑ[β] gen s) as hin by apply h2.
  apply erl_in_inv in hin as (n & e & cls & ao & e' & body & S0 & _ & _ & heq1 & heq2).
  (* so the message is in transit before the input *)
  assert (CMsg q w ∈ S0) as hmem.
  { rewrite hs in heq2.
    assert (CMsg q w ≠ CProc p n (hfill e' body)) as hne by (by intros ?).
    multiset_solver. }
  assert (CMsg q w ∈ gen (β :: s)) as hmem'.
  { rewrite heq1. multiset_solver. }
  (* the observer can release it *)
  assert (gen (β :: s) ⟶ₑ[out_act q w] (gen (β :: s) ∖ ⟪q, w⟫)) as hout.
  { assert (gen (β :: s) = ⟪q, w⟫ ⊎ (gen (β :: s) ∖ ⟪q, w⟫)) as heq3 by multiset_solver.
    rewrite heq3 at 1. apply ErlOut. }
  (* by (6) the result is good, hence so was the observer, against (1) *)
  assert (good_Erl (gen (β :: s) ∖ ⟪q, w⟫)) as hg.
  { eapply (h6 β (out_act q w) s); [exact hb | exact hout | by intros ?]. }
  eapply (h1 (β :: s)). eapply good_Erl_of_out; [exact hout | exact hg].
Qed.

(** ** A sharper obstruction: a trace over two pids

    The first argument can be blamed on [ESend] being a τ.  This one cannot: it
    uses two inputs at two /different/ pids and only the fact that a transition
    of the system rewrites one process.

    In CCS the observer of a trace is one sequential term, [c₁?(x).c₂?(y).…]:
    inputs on different channels are prefixes of the same process.  In Erlang
    the capability to receive is attached to a process /identity/: receiving at
    [p₁] then at [p₂] needs two processes, both present from the start.  The
    second one can therefore receive too early; by axiom (6) that must report
    success, and the very same reception is the one axiom (2) requires later,
    which then reports success too — against axiom (1). *)

Theorem no_trace_following_observer_two_pids (gen : list erl_act → sys)
  (p1 p2 : pid) (v1 v2 : val) :
  p1 ≠ p2 →
  (* (1) *) (∀ s, ¬ good_Erl (gen s)) →
  (* (2) *) (∀ μ s, gen (μ :: s) ⟶ₑ[μ] gen s) →
  (* (6) *) (∀ β μ s t, blocking β → gen (β :: s) ⟶ₑ[μ] t → μ ≠ β → good_Erl t) →
  False.
Proof.
  intros hp h1 h2 h6.
  assert (blocking (in_act p1 v1 : erl_act)) as hb by apply in_act_blocking.
  (* the observer of [[ActIn (p2,v2)]] receives [v1] at [p1] and becomes the
     observer of [[ActIn (p2,v2)]] *)
  destruct (erl_in_inv _ _ _ _ (h2 (in_act p1 v1 : erl_act) [in_act p2 v2]))
    as (n & e & cls & ao & e' & body & S0 & hst & hm & heq1 & heq2).
  (* the observer of [[ActIn (p2,v2)]] receives [v2] at [p2] *)
  destruct (erl_in_inv _ _ _ _ (h2 (in_act p2 v2 : erl_act) []))
    as (m & f & cls2 & ao2 & f' & body2 & S1 & hst2 & hm2 & heq3 & heq4).
  (* the process of [p2] is already there before the first input *)
  assert (CProc p2 m f ≠ CProc p1 n (hfill e' body)) as hne by congruence.
  assert (⟨p2, m, f⟩ ⊎ S1 = ⟨p1, n, hfill e' body⟩ ⊎ S0) as heq6
    by (etransitivity; [symmetry; exact heq3 | exact heq2]).
  assert (CProc p2 m f ∈ S0) as hmem by multiset_solver.
  assert (gen ((in_act p1 v1 : erl_act) :: [in_act p2 v2])
          = ⟨p2, m, f⟩ ⊎ (gen ((in_act p1 v1 : erl_act) :: [in_act p2 v2]) ∖ ⟨p2, m, f⟩)) as heq5
    by (rewrite heq1; multiset_solver).
  (* so it can receive [v2] too early *)
  assert (gen ((in_act p1 v1 : erl_act) :: [in_act p2 v2]) ⟶ₑ[(in_act p2 v2 : erl_act)]
            (⟨p2, m, hfill f' body2⟩
             ⊎ (gen ((in_act p1 v1 : erl_act) :: [in_act p2 v2]) ∖ ⟨p2, m, f⟩))) as hearly.
  { rewrite heq5 at 1. eapply ErlIn; eassumption. }
  (* by (6) that state reports success *)
  assert (good_Erl (⟨p2, m, hfill f' body2⟩
                    ⊎ (gen ((in_act p1 v1 : erl_act) :: [in_act p2 v2]) ∖ ⟨p2, m, f⟩))) as hg.
  { eapply (h6 (in_act p1 v1 : erl_act) (in_act p2 v2) [in_act p2 v2]);
      [exact hb | exact hearly | congruence]. }
  apply good_Erl_spec in hg as (c & hin & ht).
  (* either the success is the new [p2] process — and then the observer of [ε]
     reports success — or it was already there before the input *)
  apply gmultiset_elem_of_disj_union in hin as [hin | hin].
  - apply gmultiset_elem_of_singleton in hin as ->.
    eapply (h1 []). apply good_Erl_spec.
    exists (CProc p2 m (hfill f' body2)). split; [rewrite heq4; multiset_solver | done].
  - eapply (h1 ((in_act p1 v1 : erl_act) :: [in_act p2 v2])). apply good_Erl_spec.
    exists c. split; [| done]. rewrite heq5. multiset_solver.
Qed.

End Erlang_Test_Dilemma.
