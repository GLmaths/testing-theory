# Theories directory

This folder hosts the Coq developments for the must-testing project, including ACCS-style systems and the pi-calculus formalisation.

## Pi calculus (overview)
See [pi/README.md](pi/README.md) for the module structure.
- Renamings and notations: [pi/Renamings.v](pi/Renamings.v).
- Structural congruence rules: [pi/Congruence.v](pi/Congruence.v).
- Labelled transitions and renaming lemmas: [pi/LTS.v](pi/LTS.v) and [pi/LTS_Renamings.v](pi/LTS_Renamings.v).
- Reduction semantics, shape lemmas, and Harmony Lemma proof: [pi/Pi_Instance.v](pi/Pi_Instance.v#L1).

## ACCS+SEQ legacy notes

ACCS + SEQ is an Asynchronous Communicating System with Sequentiation made by Gaëtan Lopez, Hugo Feree and Giovanni Bernardi.

The COQ file is made by Gaëtan Lopez, supervised by Hugo Feree.

It respects the Harmony Lemma, (The π-calculus, A Theory of Mobile Processes, Davide Sangiorgi & David Walker, 2001, page 51)

By Asynchronous, it means : "Respects all of the 5 Asynchronous OutBuffered Agents Axioms from Peter Selinger" (First-Order Axioms for Asynchrony, Peter Selinger, 1997)

Finally, it fits to all LTS (Labelled Transition System) classes from the Characterization of Paul Laforgue, Léo Stefanesco and Giovanni Bernardi for the MUST-Preorder.


## Appendix



- line 85 to 134 : definition of Process (+ notations)
- line 772 to 773 : definition of States (:= a MailBox + a Process)
- line 458 to 537 : definition of the Congruence of Process (mainly, you have to add the transitivity , added on line : 557)
- line 1179  to 1182 : definition of the Congruence of States (induced by the one on Process)
- line 787 to 826 : Transition System of the Process
- line 828 to 847 : Transition System of the States (induced mainly from the one on Process)
- line 1189 to 1227 : Reduction System of the State
- line 2119 to 2149 : Closed Terms reduces to Closed Terms
- line 2186 to 2214 : Closed Termns transits to Closed Terms
- line 1510 to 1533 : One side of the Harmony Lemma
- line 1574 to 1667 : The other side of the Harmony Lemma
- line 2249 to 2335 : All Proof of Selingers axioms
- line 2337 to 2342 : Proof of the Lemma 3.4. from (First-Order Axioms for Asynchrony, Peter Selinger, 1997)
- line 3134 to 3178 : Instance of all the Classes, you need for the characterization
## Processes and States

```javascript
Inductive proc : Type :=
(* To parallele two processes*)
| pr_par : proc -> proc -> proc
(* Variable in a process, for recursion and substitution*)
| pr_var : nat -> proc
(* recursion for process*)
| pr_rec : nat -> proc -> proc
(* If test *NEW term in comparison of CCS* *)
| pr_if_then_else : Equation Data -> proc -> proc -> proc
(* The Process that does nothing without blocking state*)
| pr_nil : proc
(*The Guards*)
| g : gproc -> proc

with gproc : Type :=
(* Deadlock, no more computation *)
| gpr_deadlock : gproc
(* The Success operation*)
| gpr_success : gproc
(*An input is a name of a channel, an input variable, followed by a process*)
| gpr_input : Channel ->  proc -> gproc
(*An output is a name of a channel, an ouput value, followed by a process*)
| gpr_output : Channel -> Data -> proc -> gproc
(*A tau action : does nothing *)
| gpr_tau : proc -> gproc
(* To choose between two processes*)
| gpr_choice : gproc -> gproc -> gproc
(*Sequentiality for process*)
| gpr_seq : proc -> proc -> gproc
.

Definition States := gmultiset TypeOfActions * proc
```

