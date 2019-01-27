------------------------------ MODULE SimpleBPaxos -----------------------------
(******************************************************************************)
(* This is a specification for Simple BPaxos. We make a couple of             *)
(* simplifcations to keep the model simple:                                   *)
(*                                                                            *)
(*   - In practice, Simple BPaxos nodes would gossip committed commands to    *)
(*     one another. In the specification, they do not.                        *)
(*   - In practice, if a Simple BPaxos node is recovering an instance I, it   *)
(*     would first contact the dependency service to see if any dependency    *)
(*     service node knows the command that was proposed in instance I. Then,  *)
(*     it would propose the command to the dependency service. In this        *)
(*     specification, BPaxos nodes simply propose noops. TODO(mwhittaker):    *)
(*     Remove this simplification and specify the full recovery behavior.     *)
(******************************************************************************)

EXTENDS Integers, FiniteSets

(******************************************************************************)
(* Constants                                                                  *)
(******************************************************************************)

\* The set of dependency service replicas.
CONSTANT DependencyServiceReplica

\* The set of dependency service quorums. Every two quorums must interesct.
\* Typically, we deploy 2f + 1 dependency service replicas and let quorums be
\* sets of replicas of size f + 1.
CONSTANT DependencyServiceQuorum
ASSUME
    /\ \A Q \in DependencyServiceQuorum : Q \subseteq DependencyServiceReplica
    /\ \A Q1, Q2 \in DependencyServiceQuorum : Q1 \intersect Q2 /= {}

\* The set of Simple BPaxos replicas.
CONSTANT BPaxosReplica

\* The set of commands that can be proposed to BPaxos.
CONSTANT Command
ASSUME IsFiniteSet(Command)

\* The command conflict relation. Conflict is a symmetric relation over Command
\* such that two commands a and b conflict if (a, b) is in Conflict.
CONSTANT Conflict
ASSUME
    /\ Conflict \subseteq Command \X Command
    /\ \A ab \in Conflict : <<ab[2], ab[1]>> \in Conflict

\* Dependency service nodes and BPaxos nodes both maintain dependency graphs.
\* We model these dependency graphs as dicts from an instance (e.g., Q.1) to
\* the instance's command (e.g., a) and its dependencies (e.g, {R.1, S.2}). As
\* described in [1], we model a dict from domain K to range V as a function
\* from K to V \cup {NULL}. This is that NULL value.
\*
\* [1]: https://stackoverflow.com/a/47118549/3187068
CONSTANT NULL

--------------------------------------------------------------------------------

(******************************************************************************)
(* Variables and definitions.                                                 *)
(******************************************************************************)
noop == CHOOSE c : c \notin Command

\* As with EPaxos, an instance is a pair of a BPaxos replica's address and a
\* monotonically increasing id (e.g., R.1, Q.2).
\*
\* TODO(mwhittaker): Explain why we have 1..Cardinality(Command) and not Nat.
Instance == BPaxosReplica \X (0..Cardinality(Command))

\* TODO(mwhittaker): Document.
Gadget == [cmd: Command, deps: SUBSET Instance]

\* A dependency graph is a directed graph where each vertex is labelled with an
\* instance and contains a command. We model the graph as a dictionary mapping
\* an instance to its command and dependencies.
DependencyGraph == [Instance -> Gadget \cup {NULL}]

\* dependencyServiceGraphs[d] is the dependency graph maintained on dependency
\* service node d.
VARIABLE dependencyServiceGraphs

\* TODO(mwhittaker): Document.
VARIABLE bpaxosInstance

\* TODO(mwhittaker): Document.
VARIABLE proposed

\* TODO(mwhittaker): Document.
Message ==
  [
    type: {"dependency_service_propose"},
    leader: BPaxosReplica,
    instance: Instance,
    cmd: Command
  ]
  \cup
  [
    type: {"dependency_service_reply"},
    leader: BPaxosReplica,
    replica: DependencyServiceReplica,
    instance: Instance,
    cmd: Command,
    deps: SUBSET Instance
  ]
  \cup
  [
    type: {"consensus_propose"},
    instance: Instance,
    cmd: Command,
    deps: SUBSET Instance
  ]
  \cup
  [
    type: {"consensus_chosen"},
    instance: Instance,
    cmd: Command,
    deps: SUBSET Instance
  ]

\* TODO(mwhittaker): Document.
VARIABLE msgs

vars == <<dependencyServiceGraphs, bpaxosInstance, proposed, msgs>>

TypeOk ==
  /\ dependencyServiceGraphs \in [DependencyServiceReplica -> DependencyGraph]
  /\ bpaxosInstance \in [BPaxosReplica -> 0..Cardinality(Command)]
  /\ proposed \subseteq Command
  /\ msgs \subseteq Message

--------------------------------------------------------------------------------

(******************************************************************************)
(* Actions.                                                                   *)
(******************************************************************************)

\* TODO(mwhittaker): Document.
Propose(n, cmd) ==
  /\ ~ (cmd \in proposed)
  /\ LET I == <<n, bpaxosInstance[n]>>
         msg == [type |-> "dependency_service_propose",
                 leader |-> n,
                 instance |-> I,
                 cmd |-> cmd] IN
     /\ bpaxosInstance' = [bpaxosInstance EXCEPT ![n] = @ + 1]
     /\ proposed' = proposed \union {cmd}
     /\ msgs' = msgs \union {msg}
     /\ UNCHANGED <<dependencyServiceGraphs>>

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
DependencyServiceReply(d, I) ==
  \E msg \in msgs :
    /\ msg.type = "dependency_service_propose"
    /\ msg.instance = I
    /\ IF dependencyServiceGraphs[d][I] /= NULL THEN
         \* If we've already received a command in this instance, then we
         \* simply re-send the dependencies that we've already computed.
         /\ msgs' = msgs \cup {[
              type |-> "dependency_service_reply",
              leader |-> msg.leader,
              replica |-> d,
              instance |-> I,
              cmd |-> dependencyServiceGraphs[d][I].cmd,
              deps |-> dependencyServiceGraphs[d][I].deps
            ]}
         /\ UNCHANGED <<dependencyServiceGraphs, bpaxosInstance, proposed>>
       ELSE
         \* Otherwise, we have to compute the dependencies and then send them.
         LET G == dependencyServiceGraphs[d]
             deps == Dependencies(G, msg.cmd) IN
         /\ dependencyServiceGraphs' = [dependencyServiceGraphs
               EXCEPT ![d][I] = [cmd |-> msg.cmd, deps |-> deps]]
         /\ msgs' = msgs \cup {[
              type |-> "dependency_service_reply",
              leader |-> msg.leader,
              replica |-> d,
              instance |-> I,
              cmd |-> msg.cmd,
              deps |-> {}
            ]}
         /\ UNCHANGED <<bpaxosInstance, proposed>>

ConsensusPropose(n, I) ==
  LET replies == {msg \in msgs : /\ msg.type = "dependency_service_reply"
                                /\ msg.leader = n
                                /\ msg.instance = I} IN
  /\ \E Q \in DependencyServiceQuorum :
     \A d \in Q :
     \E msg \in replies : msg.replica = d
  /\ LET cmd == (CHOOSE msg \in replies : TRUE).cmd
         deps == UNION {msg.deps : msg \in replies} IN
     /\ msgs' = msgs \union {[type |-> "consensus_propose",
                              instance |-> I,
                              cmd |-> cmd,
                              deps |-> deps]}
     /\ UNCHANGED <<dependencyServiceGraphs, bpaxosInstance, proposed>>

ConsensusChoose(I) ==
  LET inI == {msg \in msgs : msg.instance = I}
      proposals == {msg \in inI : msg.type = "consensus_propose"}
      chosens == {msg \in inI : msg.type = "consensus_chosen"} IN
  /\ \E proposal \in proposals : TRUE
  /\ ~ \E chosen \in chosens : TRUE
  /\ LET chosen == CHOOSE msg \in proposals : TRUE IN
    /\ msgs' = msgs \cup {[type |-> "consensus_chosen",
                           instance |-> I,
                           cmd |-> chosen.cmd,
                           deps |-> chosen.deps]}
    /\ UNCHANGED <<dependencyServiceGraphs, bpaxosInstance, proposed>>

--------------------------------------------------------------------------------

(******************************************************************************)
(* Specification.                                                             *)
(******************************************************************************)
Init ==
    /\ dependencyServiceGraphs =
        [d \in DependencyServiceReplica |-> [I \in Instance |-> NULL]]
    /\ bpaxosInstance = [n \in BPaxosReplica |-> 0]
    /\ proposed = {}
    /\ msgs = {}

Next ==
  \/ \E n \in BPaxosReplica :
     \E cmd \in Command :
     Propose(n, cmd)
  \/ \E d \in DependencyServiceReplica :
     \E I \in Instance :
     DependencyServiceReply(d, I)
  \/ \E n \in DependencyServiceReplica :
     \E I \in Instance :
     ConsensusPropose(n, I)
  \/ \E I \in Instance :
     ConsensusChoose(I)

\* set of ordering service nodes
\* definition of consensus
\* definition of bpaxos nodes
\* definition of instances
\* definition commands
\* definition conflict
\* definition gadget
\* noop

\* Actions
\* propose to bpaxos and send to ordering service
\* receive response from ordernig service; propose to consensus
\* propose to consensus and commit gadget

\* Invariants
\* single command per instance
\* dependency service for conlicts
\* only propose noop or response from ordering service (trivial)
\* chosen conflicting commands depend

================================================================================
