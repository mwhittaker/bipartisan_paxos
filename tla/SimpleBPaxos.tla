------------------------------ MODULE SimpleBPaxos -----------------------------
(******************************************************************************)
(* This is a specification of Simple BPaxos. To keep things simple and to     *)
(* make models more easily checkable, we abstract a way a lot of the          *)
(* unimportant details of Simple BPaxos. In particular, the specification     *)
(* does not model messages being sent between components and does include     *)
(* Simple BPaxos nodes at all. The consensus service is also left abstract.   *)
(* The core of Simple BPaxos is that dependency service responses (noops) are *)
(* proposed to a consensus service. This core of the algorithm is what is     *)
(* modelled.                                                                  *)
(******************************************************************************)

EXTENDS Dict, Integers, FiniteSets

(******************************************************************************)
(* Constants                                                                  *)
(******************************************************************************)

\* The set of commands that can be proposed to BPaxos. In this specification,
\* every command can be proposed at most once. This is mostly to keep behaviors
\* finite. In a real execution of Simple BPaxos, a command can be proposed an
\* infinite number of times.
CONSTANT Command
ASSUME IsFiniteSet(Command)

\* The command conflict relation. Conflict is a symmetric relation over Command
\* such that two commands a and b conflict if (a, b) is in Conflict.
CONSTANT Conflict
ASSUME
    /\ Conflict \subseteq Command \X Command
    /\ \A ab \in Conflict : <<ab[2], ab[1]>> \in Conflict

\* We assume the existence of a special noop command that does not conflict
\* with any other command. Because noop is not in Command, it does not appear
\* in Conflict.
CONSTANT noop
ASSUME noop \notin Command

\* The set of dependency service replicas.
CONSTANT DepServiceReplica
ASSUME IsFiniteSet(DepServiceReplica)

\* The set of dependency service quorums. Every two quorums must interesct.
\* Typically, we deploy 2f + 1 dependency service replicas and let quorums be
\* sets of replicas of size f + 1.
CONSTANT DepServiceQuorum
ASSUME
    /\ \A Q \in DepServiceQuorum : Q \subseteq DepServiceReplica
    /\ \A Q1, Q2 \in DepServiceQuorum : Q1 \intersect Q2 /= {}

--------------------------------------------------------------------------------

(******************************************************************************)
(* Variables and definitions.                                                 *)
(******************************************************************************)
\* In Simple BPaxos, instances are of the form Q.i where Q is a Simple BPaxos
\* replica and i is a monotonically increasing id. In this specification, we
\* don't even model Simple BPaxos replicas. So, we let instances be simple
\* integers. You might imagine we would say `Instance == Nat`, but keeping
\* things finite helps TLC. Every command can be proposed at most once, so
\* allowing instances to range between 0 and |Command| works great.
Instance == 0..Cardinality(Command)

\* In our paper, we describe a gadget as an instance, a command, and a set of
\* dependencies. Here, we drop the instance, but it's not a fundamental change.
Gadget == [cmd: Command \union {noop}, deps: SUBSET Instance]

\* The gadget associated with noop. Noop doesn't conflict with any other
\* command, so its dependencies are always empty.
noopGadget == [cmd |-> noop, deps |-> {}]

\* A dependency graph is a directed graph where each vertex is labelled with an
\* instance and contains a command. We model the graph as a dictionary mapping
\* an instance to its command and dependencies.
DependencyGraph == Dict(Instance, Gadget)

\* dependencyGraphs[d] is the dependency graph maintained on dependency
\* service node d.
VARIABLE dependencyGraphs

\* The next instance to assign a proposed command. It is initially 0 and
\* incremented after every proposed command.
VARIABLE nextInstance

\* A dictionary mapping instance to the command proposed in that instance.
VARIABLE proposedCommands

\* A dictionary mapping instance to the set of gadgets proposed to the
\* consensus service in that instance.
VARIABLE proposedGadgets

\* A dictionary mapping instance to the chosen gadget that was chosen by the
\* consensus service in that instance.
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

\* Propose a command `cmd` to Simple BPaxos. In a real implementation of Simple
\* BPaxos, a client would send the command to a Simple BPaxos node, and the
\* Simple BPaxos node would forward the command to the set of dependency
\* service nodes. Here, we bypass all that. The only thing to do here is to
\* assign the command an instance and make sure it hasn't already been proposed.
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

\* Here, dependency service node d processes a request in instance I. Namely,
\* it adds I to its dependency graph. Dependency service nodes also do not
\* process a command more than once. In a real Simple BPaxos implementation,
\* the dependency service node would send the resulting gadget back to a Simple
\* BPaxos node and could process a command more than once.
DepServiceProcess(d, I) ==
  LET G == dependencyGraphs[d] IN
  /\ proposedCommands[I] /= NULL
  /\ G[I] = NULL
  /\ LET cmd == proposedCommands[I] IN
    /\ dependencyGraphs' = [dependencyGraphs EXCEPT ![d][I] =
                              [cmd |-> cmd, deps |-> Dependencies(G, cmd)]]
    /\ UNCHANGED <<nextInstance, proposedCommands, proposedGadgets,
                   chosenGadgets>>

\* Evalutes to whether a quorum of dependency service nodes have processed the
\* command in instance I.
ExistsQuorumReply(Q, I) ==
  \A d \in Q : dependencyGraphs[d][I] /= NULL

\* Evaluates to the dependency service reply for instance I from quorum Q of
\* dependency service nodes.
QuorumReply(Q, I) ==
  LET gadgets == {dependencyGraphs[d][I] : d \in Q} IN
  [cmd |-> (CHOOSE gadget \in gadgets : TRUE).cmd,
   deps |-> UNION {gadget.deps : gadget \in gadgets}]

\* Propose a noop gadget in instance I to the consensus service. In a real
\* Simple BPaxos implementation, a Simple BPaxos node would propose a noop only
\* in some circumstances. In this model, we allow noops to be proposed at any
\* time.
ConsensusProposeNoop(I) ==
  /\ proposedGadgets' = [proposedGadgets EXCEPT ![I] = @ \union {noopGadget}]
  /\ UNCHANGED <<dependencyGraphs, nextInstance, proposedCommands,
                 chosenGadgets>>

\* Propose a dependency service reply in instance I to the consensus service.
ConsensusPropose(I) ==
  \E Q \in DepServiceQuorum :
    /\ ExistsQuorumReply(Q, I)
    /\ proposedGadgets' = [proposedGadgets EXCEPT ![I] =
                             @ \union {QuorumReply(Q, I)}]
    /\ UNCHANGED <<dependencyGraphs, nextInstance, proposedCommands,
                   chosenGadgets>>

\* Choose a value for instance I.
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
  /\ dependencyGraphs = [d \in DepServiceReplica |-> [I \in Instance |-> NULL]]
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

FairSpec == Spec /\ WF_vars(Next)

--------------------------------------------------------------------------------

(******************************************************************************)
(* Properties and Invariants.                                                 *)
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

\* True if every command is chosen.
EverythingChosen ==
  \A cmd \in Command :
    \E I \in Instance :
      /\ chosenGadgets[I] /= NULL
      /\ chosenGadgets[I] = cmd

\* Fairness free theorem.
THEOREM
  Spec => /\ AlwaysConsensusConsistency
          /\ []DepServiceConflicts
          /\ []Nontriviality
          /\ []ChosenConflicts

\* True if no noops are chosen.
NoNoop ==
  ~ \E I \in Instance :
    /\ chosenGadgets[I] /= NULL
    /\ chosenGadgets[I].cmd = noop

\* If no noops are chosen, then every command is chosen. This property is only
\* true for FairSpec.
NoNoopEverythingChosen ==
  []NoNoop => <>EverythingChosen

\* Fairness theorem.
THEOREM
  FairSpec => /\ AlwaysConsensusConsistency
              /\ []DepServiceConflicts
              /\ []Nontriviality
              /\ []ChosenConflicts
              /\ NoNoopEverythingChosen

================================================================================
