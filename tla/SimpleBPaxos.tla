------------------------------ MODULE SimpleBPaxos -----------------------------
(******************************************************************************)
(* This is a specification for Simple BPaxos. We make a couple of             *)
(* simplifcations to keep the model simple:                                   *)
(*                                                                            *)
(*   - In practice, Simple BPaxos nodes would gossip committed commands to    *)
(*     one another. In the specification, they do not.                        *)
(*   - In practice, if a Simple BPaxos node is recovering an instance I, it   *)
(*     would first contact the dependency service to see if any dependency    *)
(*     service node knows the command that was proposedCommands in instance I. Then,  *)
(*     it would propose the command to the dependency service. In this        *)
(*     specification, BPaxos nodes simply propose noops. TODO(mwhittaker):    *)
(*     Remove this simplification and specify the full recovery behavior.     *)
(******************************************************************************)

EXTENDS Dict, Integers, FiniteSets

(******************************************************************************)
(* Constants                                                                  *)
(******************************************************************************)

\* The set of dependency service replicas.
CONSTANT DepServiceReplica

\* The set of dependency service quorums. Every two quorums must interesct.
\* Typically, we deploy 2f + 1 dependency service replicas and let quorums be
\* sets of replicas of size f + 1.
CONSTANT DepServiceQuorum
ASSUME
    /\ \A Q \in DepServiceQuorum : Q \subseteq DepServiceReplica
    /\ \A Q1, Q2 \in DepServiceQuorum : Q1 \intersect Q2 /= {}

\* The set of commands that can be proposedCommands to BPaxos.
CONSTANT Command
ASSUME IsFiniteSet(Command)

CONSTANT noop
ASSUME noop \notin Command

\* The command conflict relation. Conflict is a symmetric relation over Command
\* such that two commands a and b conflict if (a, b) is in Conflict.
CONSTANT Conflict
ASSUME
    /\ Conflict \subseteq Command \X Command
    /\ \A ab \in Conflict : <<ab[2], ab[1]>> \in Conflict

--------------------------------------------------------------------------------

(******************************************************************************)
(* Variables and definitions.                                                 *)
(******************************************************************************)
\* As with EPaxos, an instance is a pair of a BPaxos replica's address and a
\* monotonically increasing id (e.g., R.1, Q.2).
\*
\* TODO(mwhittaker): Explain why we have 1..Cardinality(Command) and not Nat.
Instance == 0..Cardinality(Command)

\* TODO(mwhittaker): Document.
Gadget == [cmd: Command \union {noop}, deps: SUBSET Instance]
noopGadget == [cmd |-> noop, deps |-> {}]


\* A dependency graph is a directed graph where each vertex is labelled with an
\* instance and contains a command. We model the graph as a dictionary mapping
\* an instance to its command and dependencies.
DependencyGraph == [Instance -> Gadget \cup {NULL}]

\* dependencyGraphs[d] is the dependency graph maintained on dependency
\* service node d.
VARIABLE dependencyGraphs

\* TODO(mwhittaker): Document.
VARIABLE nextInstance

\* TODO(mwhittaker): Document.
VARIABLE proposedCommands

\* TODO(mwhittaker): Document.
VARIABLE proposedGadgets

\* TODO(mwhittaker): Document.
VARIABLE chosenGadgets

vars == <<
  dependencyGraphs,
  nextInstance,
  proposedCommands,
  proposedGadgets,
  chosenGadgets
>>

TypeOk ==
  /\ dependencyGraphs \in Dict(DepServiceReplica, DependencyGraph)
  /\ nextInstance \in Instance
  /\ proposedCommands \in Dict(Instance, Command)
  /\ proposedGadgets \in Dict(Instance, SUBSET Gadget)
  /\ chosenGadgets \in Dict(Instance, Gadget)

--------------------------------------------------------------------------------

(******************************************************************************)
(* Actions.                                                                   *)
(******************************************************************************)

\* TODO(mwhittaker): Document.
ProposeCommand(cmd) ==
  /\ cmd \notin Values(proposedCommands)
  /\ proposedCommands' = [proposedCommands EXCEPT ![nextInstance] = cmd]
  /\ nextInstance' = nextInstance + 1
  /\ UNCHANGED <<dependencyGraphs, proposedGadgets, chosenGadgets>>

\* Given a dependency graph G and command cmd, return the set of instances in G
\* that contain commands that conflict with cmd. For example, consider the
\* following dependency graph with commands b, c, and d in instances I_b, I_c,
\* and I_d. If command a conflicts with c and d, then the dependencies of a are
\* I_c and I_d.
\*
\*                                 I_b     I_c
\*                                +---+   +---+
\*                                | b +---> c |
\*                                +-+-+   +---+
\*                                  |
\*                                +-v-+
\*                                | d |
\*                                +---+
\*                                 I_c
Dependencies(G, cmd) ==
  {I \in Instance : G[I] /= NULL /\ <<cmd, G[I].cmd>> \in Conflict}

\* TODO(mwhittaker): Document.
DepServiceProcess(d, I) ==
  LET G == dependencyGraphs[d] IN
  /\ proposedCommands[I] /= NULL
  /\ G[I] = NULL
  /\ LET cmd == proposedCommands[I] IN
    /\ dependencyGraphs' = [dependencyGraphs EXCEPT ![d][I] =
                              [cmd |-> cmd, deps |-> Dependencies(G, cmd)]]
    /\ UNCHANGED <<nextInstance, proposedCommands, proposedGadgets,
                   chosenGadgets>>

ExistsQuorumReply(Q, I) ==
  \A d \in Q : dependencyGraphs[d][I] /= NULL

QuorumReply(Q, I) ==
  LET gadgets == {dependencyGraphs[d][I] : d \in Q} IN
  [cmd |-> (CHOOSE gadget \in gadgets : TRUE).cmd,
   deps |-> UNION {gadget.deps : gadget \in gadgets}]

ConsensusProposeNoop(I) ==
  /\ proposedGadgets' = [proposedGadgets EXCEPT ![I] = @ \union {noopGadget}]
  /\ UNCHANGED <<dependencyGraphs, nextInstance, proposedCommands,
                 chosenGadgets>>

ConsensusPropose(I) ==
  \E Q \in DepServiceQuorum :
    /\ ExistsQuorumReply(Q, I)
    /\ proposedGadgets' = [proposedGadgets EXCEPT ![I] =
                             @ \union {QuorumReply(Q, I)}]
    /\ UNCHANGED <<dependencyGraphs, nextInstance, proposedCommands,
                   chosenGadgets>>

ConsensusChoose(I) ==
  /\ proposedGadgets[I] /= {}
  /\ chosenGadgets[I] = NULL
  /\ chosenGadgets' = [chosenGadgets EXCEPT ![I] =
                         CHOOSE g \in proposedGadgets[I] : TRUE]
  /\ UNCHANGED <<dependencyGraphs, nextInstance, proposedCommands,
                 proposedGadgets>>

--------------------------------------------------------------------------------

(******************************************************************************)
(* Specification.                                                             *)
(******************************************************************************)
Init ==
    /\ dependencyGraphs =
        [d \in DepServiceReplica |-> [I \in Instance |-> NULL]]
    /\ nextInstance = 0
    /\ proposedCommands = [I \in Instance |-> NULL]
    /\ proposedGadgets = [I \in Instance |-> {}]
    /\ chosenGadgets = [I \in Instance |-> NULL]

Next ==
  \/ \E cmd \in Command : ProposeCommand(cmd)
  \/ \E d \in DepServiceReplica : \E I \in Instance : DepServiceProcess(d, I)
  \/ \E I \in Instance : ConsensusProposeNoop(I)
  \/ \E I \in Instance : ConsensusPropose(I)
  \/ \E I \in Instance : ConsensusChoose(I)

Spec == Init /\ [][Next]_vars

--------------------------------------------------------------------------------

(******************************************************************************)
(* Invariants.                                                                *)
(******************************************************************************)
\* The consensus service can choose at most command in any given instance.
ConsensusConsistency ==
  \A I \in Instance :
    chosenGadgets[I] /= NULL => chosenGadgets'[I] = chosenGadgets[I]

AlwaysConsensusConsistency ==
  [][ConsensusConsistency]_vars

\* If two conflicting commands a and b yield dependencies deps(a) and deps(b)
\* from the dependency service, then a is in deps(b), or b is in deps(a), or
\* both.
DepServiceConflicts ==
  \A I1, I2 \in Instance :
  \A Q1, Q2 \in DepServiceQuorum :
  IF I1 /= I2 /\ ExistsQuorumReply(Q1, I1) /\ ExistsQuorumReply(Q2, I2) THEN
     LET gadget1 == QuorumReply(Q1, I1)
         gadget2 == QuorumReply(Q2, I2) IN
     <<gadget1.cmd, gadget2.cmd>> \in Conflict =>
       I1 \in gadget2.deps \/ I2 \in gadget1.deps
  ELSE
    TRUE

\* Simple BPaxos should only choose proposed commands. This is inspired by [1].
\*
\* [1]: github.com/efficient/epaxos/blob/master/tla+/EgalitarianPaxos.tla
Nontriviality ==
  \A I \in Instance :
    chosenGadgets[I] /= NULL =>
      \/ chosenGadgets[I].cmd \in Values(proposedCommands)
      \/ chosenGadgets[I].cmd = noop

\* If two conflicting commands a and b are chosen, then a is in deps(b), or b
\* is in deps(a), or both.
ChosenConflicts ==
  \A I1, I2 \in Instance :
  IF I1 /= I2 /\ chosenGadgets[I1] /= NULL /\ chosenGadgets[I2] /= NULL THEN
    LET gadget1 == chosenGadgets[I1]
        gadget2 == chosenGadgets[I2] IN
     <<gadget1.cmd, gadget2.cmd>> \in Conflict =>
       I1 \in gadget2.deps \/ I2 \in gadget1.deps
  ELSE
    TRUE

================================================================================
