------------------------------ MODULE SimpleBPaxos -----------------------------
(******************************************************************************)
(* This is a specification of Simple BPaxos. To keep things simple and to     *)
(* make models more easily checkable, we abstract a way a lot of the          *)
(* unimportant details of Simple BPaxos. In particular, the specification     *)
(* does not model messages being sent between components and does not         *)
(* include leaders, proposers, or replicas. The consensus service is also     *)
(* left abstract. The core of Simple BPaxos is that dependency service        *)
(* responses (noops) are proposed to a consensus service. This core of the    *)
(* algorithm is what is modelled.                                             *)
(*                                                                            *)
(* Run `tlc SimpleBPaxosModel` to check the model.                            *)
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

\* The set of dependency service nodes.
CONSTANT DepServiceNode
ASSUME IsFiniteSet(DepServiceNode)

\* The set of dependency service quorums. Every two quorums must interesct.
\* Typically, we deploy 2f + 1 dependency service replicas and let quorums be
\* sets of replicas of size f + 1.
CONSTANT DepServiceQuorum
ASSUME
    /\ \A Q \in DepServiceQuorum : Q \subseteq DepServiceNode
    /\ \A Q1, Q2 \in DepServiceQuorum : Q1 \intersect Q2 /= {}

--------------------------------------------------------------------------------

(******************************************************************************)
(* Variables and definitions.                                                 *)
(******************************************************************************)
\* In Simple BPaxos, vertex ids are of the form Q.i where Q is a leader and i is
\* a monotonically increasing id (intially zero). In this specification, we
\* don't even model Simple BPaxos nodes. So, we let instances be simple
\* integers. You might imagine we would say `VertexId == Nat`, but keeping
\* things finite helps TLC. Every command can be proposed at most once, so
\* allowing instances to range between 0 and |Command| works great.
VertexId == 0..Cardinality(Command)

\* A proposal is a command (or noop) and its dependencies.
Proposal == [cmd: Command \union {noop}, deps: SUBSET VertexId]

\* The proposal associated with noop. Noop doesn't conflict with any other
\* command, so its dependencies are always empty.
noopProposal == [cmd |-> noop, deps |-> {}]

\* A dependency graph is a directed graph where each vertex is labelled with an
\* vertex id and contains a command. We model the graph as a dictionary mapping
\* a vertex id to its command and dependencies.
DependencyGraph == Dict(VertexId, Proposal)

\* dependencyGraphs[d] is the dependency graph maintained on dependency
\* service node d.
VARIABLE dependencyGraphs

\* The next vertex id to assign to a proposed command. It is initially 0 and
\* incremented after every proposed command.
VARIABLE nextVertexId

\* A dictionary mapping vertex id to the command proposed with that vertex id.
VARIABLE proposedCommands

\* A dictionary mapping vertex id to the set of proposals proposed to the
\* consensus service in that instance.
VARIABLE proposals

\* A dictionary mapping vertex id to the proposal that was chosen by the
\* consensus service for that vertex id.
VARIABLE chosen

vars == <<
  dependencyGraphs,
  nextVertexId,
  proposedCommands,
  proposals,
  chosen
>>

TypeOk ==
  /\ dependencyGraphs \in Dict(DepServiceNode, DependencyGraph)
  /\ nextVertexId \in VertexId
  /\ proposedCommands \in Dict(VertexId, Command)
  /\ proposals \in Dict(VertexId, SUBSET Proposal)
  /\ chosen \in Dict(VertexId, Proposal)

--------------------------------------------------------------------------------

(******************************************************************************)
(* Actions.                                                                   *)
(******************************************************************************)

\* Propose a command `cmd` to Simple BPaxos. In a real implementation of Simple
\* BPaxos, a client would send the command to a leader, and the leader would
\* forward the command to the set of dependency service nodes. Here, we bypass
\* all that. The only thing to do here is to assign the command an instance and
\* make sure it hasn't already been proposed.
ProposeCommand(cmd) ==
  /\ cmd \notin Values(proposedCommands)
  /\ proposedCommands' = [proposedCommands EXCEPT ![nextVertexId] = cmd]
  /\ nextVertexId' = nextVertexId + 1
  /\ UNCHANGED <<dependencyGraphs, proposals, chosen>>

\* Given a dependency graph G and command cmd, return the set of vertices in G
\* that contain commands that conflict with cmd. For example, consider the
\* following dependency graph with commands b, c, and d in vertices v_b, v_c,
\* and v_d. If command a conflicts with c and d, then the dependencies of a are
\* v_c and v_d.
\*
\*                                 v_b     v_c
\*                                +---+   +---+
\*                                | b +---> c |
\*                                +-+-+   +---+
\*                                  |
\*                                +-v-+
\*                                | d |
\*                                +---+
\*                                 v_d
Dependencies(G, cmd) ==
  {v \in VertexId : G[v] /= NULL /\ <<cmd, G[v].cmd>> \in Conflict}

\* Here, dependency service node d processes a request in vertex v. Namely,
\* it adds v to its dependency graph (along with the command in
\* proposedCommands). Dependency service nodes also do not process a command
\* more than once. In a real Simple BPaxos implementation, the dependency
\* service node would receive a message from a leader and send dependencies
\* back to the leader. Also, a dependency service node could receive a request
\* from the leader more than once. We abstract all of this away.
DepServiceProcess(d, v) ==
  LET G == dependencyGraphs[d] IN
  /\ proposedCommands[v] /= NULL
  /\ G[v] = NULL
  /\ LET cmd == proposedCommands[v] IN
    /\ dependencyGraphs' = [dependencyGraphs EXCEPT ![d][v] =
                              [cmd |-> cmd, deps |-> Dependencies(G, cmd)]]
    /\ UNCHANGED <<nextVertexId, proposedCommands, proposals, chosen>>

\* Evalutes to whether a quorum of dependency service nodes have processed the
\* command in vertex v.
ExistsQuorumReply(Q, v) ==
  \A d \in Q : dependencyGraphs[d][v] /= NULL

\* Evaluates to the dependency service reply for vertex v from quorum Q of
\* dependency service nodes.
QuorumReply(Q, v) ==
  LET responses == {dependencyGraphs[d][v] : d \in Q} IN
  [cmd |-> (CHOOSE response \in responses : TRUE).cmd,
   deps |-> UNION {response.deps : response \in responses}]

\* Propose a noop gadget in vertex v to the consensus service. In a real
\* Simple BPaxos implementation, a proposer would propose a noop only
\* in some circumstances. In this model, we allow noops to be proposed at any
\* time.
ConsensusProposeNoop(v) ==
  /\ proposals' = [proposals EXCEPT ![v] = @ \union {noopProposal}]
  /\ UNCHANGED <<dependencyGraphs, nextVertexId, proposedCommands, chosen>>

\* Propose a dependency service reply in vertex v to the consensus service.
ConsensusPropose(v) ==
  \E Q \in DepServiceQuorum :
    /\ ExistsQuorumReply(Q, v)
    /\ proposals' = [proposals EXCEPT ![v] = @ \union {QuorumReply(Q, v)}]
    /\ UNCHANGED <<dependencyGraphs, nextVertexId, proposedCommands, chosen>>

\* Choose a value for vertex v.
ConsensusChoose(v) ==
  /\ proposals[v] /= {}
  /\ chosen[v] = NULL
  /\ chosen' = [chosen EXCEPT ![v] = CHOOSE g \in proposals[v] : TRUE]
  /\ UNCHANGED <<dependencyGraphs, nextVertexId, proposedCommands, proposals>>

--------------------------------------------------------------------------------

(******************************************************************************)
(* Specification.                                                             *)
(******************************************************************************)
Init ==
  /\ dependencyGraphs = [d \in DepServiceNode |-> [v \in VertexId |-> NULL]]
  /\ nextVertexId = 0
  /\ proposedCommands = [v \in VertexId |-> NULL]
  /\ proposals = [v \in VertexId |-> {}]
  /\ chosen = [v \in VertexId |-> NULL]

Next ==
  \/ \E cmd \in Command : ProposeCommand(cmd)
  \/ \E d \in DepServiceNode : \E v \in VertexId : DepServiceProcess(d, v)
  \/ \E v \in VertexId : ConsensusProposeNoop(v)
  \/ \E v \in VertexId : ConsensusPropose(v)
  \/ \E v \in VertexId : ConsensusChoose(v)

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

--------------------------------------------------------------------------------

(******************************************************************************)
(* Properties and Invariants.                                                 *)
(******************************************************************************)
\* The consensus service can choose at most command in any given instance.
ConsensusConsistency ==
  \A v \in VertexId :
    chosen[v] /= NULL => chosen'[v] = chosen[v]

AlwaysConsensusConsistency ==
  [][ConsensusConsistency]_vars

\* If two conflicting commands a and b yield dependencies deps(a) and deps(b)
\* from the dependency service, then a is in deps(b), or b is in deps(a), or
\* both.
DepServiceConflicts ==
  \A v1, v2 \in VertexId :
  \A Q1, Q2 \in DepServiceQuorum :
  IF v1 /= v2 /\ ExistsQuorumReply(Q1, v1) /\ ExistsQuorumReply(Q2, v2) THEN
     LET proposal1 == QuorumReply(Q1, v1)
         proposal2 == QuorumReply(Q2, v2) IN
     <<proposal1.cmd, proposal2.cmd>> \in Conflict =>
       v1 \in proposal2.deps \/ v2 \in proposal1.deps
  ELSE
    TRUE

\* Simple BPaxos should only choose proposed commands. This is inspired by [1].
\*
\* [1]: github.com/efficient/epaxos/blob/master/tla+/EgalitarianPaxos.tla
Nontriviality ==
  \A v \in VertexId :
    chosen[v] /= NULL =>
      \/ chosen[v].cmd \in Values(proposedCommands)
      \/ chosen[v].cmd = noop

\* If two conflicting commands a and b are chosen, then a is in deps(b), or b
\* is in deps(a), or both.
ChosenConflicts ==
  \A v1, v2 \in VertexId :
  IF v1 /= v2 /\ chosen[v1] /= NULL /\ chosen[v2] /= NULL THEN
    LET proposal1 == chosen[v1]
        proposal2 == chosen[v2] IN
     <<proposal1.cmd, proposal2.cmd>> \in Conflict =>
       v1 \in proposal2.deps \/ v2 \in proposal1.deps
  ELSE
    TRUE

\* True if every command is chosen.
EverythingChosen ==
  \A cmd \in Command :
    \E v \in VertexId :
      /\ chosen[v] /= NULL
      /\ chosen[v] = cmd

\* Fairness free theorem.
THEOREM
  Spec => /\ AlwaysConsensusConsistency
          /\ []DepServiceConflicts
          /\ []Nontriviality
          /\ []ChosenConflicts

\* True if no noops are chosen.
NoNoop ==
  ~ \E v \in VertexId :
    /\ chosen[v] /= NULL
    /\ chosen[v].cmd = noop

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
