---------------------------- MODULE IncorrectBPaxos ----------------------------

(******************************************************************************)
(* This is a specification of an incorrect BPaxos variant that naively        *)
(* marries the dependency service with Fast Paxos. To find an history that    *)
(* witness the variant's incorrectness, run the following command:            *)
(*                                                                            *)
(*   tlc -simulate -difftrace IncorrectBPaxosModule.tla                       *)
(*                                                                            *)
(* This command randomly simulates the specification until an error is found. *)
(* It may take a while to finish, but it will eventually.                     *)
(******************************************************************************)

EXTENDS Dict, Integers, FiniteSets

(******************************************************************************)
(* Constants                                                                  *)
(******************************************************************************)

\* The set of commands that can be proposed to BPaxos. In this specification,
\* every command can be proposed at most once. This is mostly to keep behaviors
\* finite. In a real execution of BPaxos, a command can be proposed an infinite
\* number of times.
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

\* The set of Fast Paxos acceptors. We colocate dependency service replicas and
\* acceptors, so we assume the two sets are actually identical.
CONSTANT Acceptor
ASSUME DepServiceReplica = Acceptor

\* The set of fast and classic quorums. Every two quorums (fast or classic)
\* must intersect. Moreover any quorum (fast or classic) and any two fast
\* quorums must intersect. In practice, we deploy 2f + 1 acceptors, let classic
\* quorums be of size f + 1, and let fast quorums be of size f + floor(f+1/2) +
\* 1.
CONSTANT AcceptorFastQuorum, AcceptorClassicQuorum
AcceptorQuorum == AcceptorFastQuorum \union AcceptorClassicQuorum
ASSUME
  /\ \A Q \in AcceptorQuorum : Q \subseteq Acceptor
  /\ \A Q1, Q2 \in AcceptorQuorum : Q1 \intersect Q2 /= {}
  /\ \A Q \in AcceptorClassicQuorum, FQ1, FQ2 \in AcceptorFastQuorum:
       Q \intersect FQ1 \intersect FQ2 /= {}

\* The set of BPaxos replicas.
CONSTANT BPaxosReplica
ASSUME IsFiniteSet(BPaxosReplica)

\* The set of instances. Really, Instance should be BPaxosReplica \X Nat, but
\* because commands can only proposed once, we can keep things finite.
Instance == BPaxosReplica \X (0..Cardinality(Command))

\* Every Fast Paxos instance is associated with a set of rounds (aka ballots).
\* In theory, there could be infinitely many rounds. The FLP impossibility
\* result tells us that we cannot bound the number of rounds we need to
\* terminate. In this specification, however, we constrain the number of
\* rounds to less than or equal to MaxRound. 0 is a fast round. All other
\* rounds are classic rounds.
CONSTANT MaxRound
ASSUME MaxRound \in Nat
Round == 0..MaxRound
VoteRound == -1..MaxRound

\* CoordinatorOf(I, i) is the unique coordinator of Fast Paxos round i in
\* instance I.
CONSTANT CoordinatorOf(_, _)
ASSUME
  \A I \in Instance :
    /\ CoordinatorOf(I, 0) = I[1]
    /\ \A i \in Round : CoordinatorOf(I, i) \in BPaxosReplica

--------------------------------------------------------------------------------

(******************************************************************************)
(* Variables and definitions.                                                 *)
(******************************************************************************)

Max(S) == CHOOSE i \in S : \A j \in S : j \leq i

Gadget == [cmd: Command \union {noop}, deps: SUBSET Instance]

noopGadget == [cmd |-> noop, deps |-> {}]

DependencyGraph == Dict(Instance, Gadget)

\* Dependency service.
VARIABLE dependencyGraphs

\* Acceptors.
VARIABLE round
VARIABLE voteRound
VARIABLE voteValue

\* Bpaxos nodes.
VARIABLE nextInstance
VARIABLE coordinatorRound
VARIABLE coordinatorValue

\* Meta.
VARIABLE proposed
VARIABLE chosen
VARIABLE msgs

Message ==
  [
    type: {"phase1a"},
    instance: Instance,
    round: Round
  ]
  \union
  [
    type: {"phase1b"},
    instance: Instance,
    round: Round,
    voteRound: VoteRound,
    voteValue: Gadget \cup {NULL},
    acceptor: Acceptor
  ]
  \union
  [
    type: {"phase2a"},
    instance: Instance,
    round: Round,
    value: Gadget
  ]
  \union
  [
    type: {"phase2b"},
    instance: Instance,
    round: Round,
    value: Gadget,
    acceptor: Acceptor
  ]

TypeOk ==
  /\ dependencyGraphs \in Dict(DepServiceReplica, DependencyGraph)
  /\ round \in Dict(Acceptor, Dict(Instance, Round))
  /\ voteRound \in Dict(Acceptor, Dict(Instance, VoteRound))
  /\ voteValue \in Dict(Acceptor, Dict(Instance, Gadget \union {NULL}))
  /\ nextInstance \in Dict(BPaxosReplica, 0..Cardinality(Command))
  /\ coordinatorRound \in Dict(BPaxosReplica, Dict(Instance, {-1} \cup Round))
  /\ coordinatorValue \in Dict(BPaxosReplica,
                               Dict(Instance, Gadget \union {NULL}))
  /\ proposed \in Dict(Instance, Command)
  /\ chosen \in Dict(Instance, SUBSET Gadget)
  /\ msgs \in SUBSET Message

depServiceVars == <<dependencyGraphs>>
acceptorVars == <<round, voteRound, voteValue>>
bpaxosVars == <<nextInstance, coordinatorRound, coordinatorValue>>
vars == <<depServiceVars, acceptorVars, bpaxosVars, proposed, chosen, msgs>>

--------------------------------------------------------------------------------

(******************************************************************************)
(* Actions.                                                                   *)
(******************************************************************************)
Send(msg) ==
  msgs' = msgs \cup {msg}

(******************************************************************************)
(* Dependency service actions.                                                *)
(******************************************************************************)
\* Given a dependency graph G and command cmd, return the set of instances in G
\* that contain commands that conflict with cmd.
Dependencies(G, cmd) ==
  {I \in Instance : G[I] /= NULL /\ <<cmd, G[I].cmd>> \in Conflict}

\* Dependency service node d processes the command proposed in instance I. d
\* adds I to its dependency graphs and draws outbound edges to conflicting
\* instances.
DepServiceProcess(d, I) ==
  LET G == dependencyGraphs[d] IN
  /\ proposed[I] /= NULL
  /\ G[I] = NULL
  /\ LET cmd == proposed[I] IN
    /\ dependencyGraphs' = [dependencyGraphs EXCEPT ![d][I] =
                              [cmd |-> cmd, deps |-> Dependencies(G, cmd)]]
    /\ UNCHANGED <<acceptorVars, bpaxosVars, proposed, chosen, msgs>>

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

(******************************************************************************)
(* BPaxos actions.                                                            *)
(******************************************************************************)
\* Propose a command to BPaxos node n.
ProposeCommand(n, cmd) ==
  /\ cmd \notin Values(proposed)
  /\ proposed' = [proposed EXCEPT ![<<n, nextInstance[n]>>] = cmd]
  /\ nextInstance' = [nextInstance EXCEPT ![n] = @ + 1]
  /\ UNCHANGED <<depServiceVars, acceptorVars, coordinatorRound,
                 coordinatorValue, chosen, msgs>>

\* Fast Paxos phase 1a at node n, instance I, round i.
Phase1a(n, I, i) ==
  /\ i > coordinatorRound[n][I]
  /\ n = CoordinatorOf(I, i)
  /\ coordinatorRound' = [coordinatorRound EXCEPT ![n][I] = i]
  /\ coordinatorValue' = [coordinatorValue EXCEPT ![n][I] = NULL]
  /\ Send([
       type |-> "phase1a",
       instance |-> I,
       round |-> i
     ])
  /\ UNCHANGED <<depServiceVars, acceptorVars, nextInstance, proposed, chosen>>

Phase1bsFrom(Q, I, i) ==
  {msg \in msgs : /\ msg.type = "phase1b"
                  /\ msg.instance = I
                  /\ msg.round = i
                  /\ msg.acceptor \in Q}

IsProposable(Q, I, i, M, v) ==
  LET voteRoundFor(p) == (CHOOSE msg \in M : msg.acceptor = p).voteRound
      voteValueFor(p) == (CHOOSE msg \in M : msg.acceptor = p).voteValue
      k == Max({voteRoundFor(p) : p \in Q})
      V == {voteValueFor(p) : p \in {q \in Q : voteRoundFor(q) = k}}
      O4(w) == \E R \in AcceptorFastQuorum :
                 \A p \in Q \intersect R :
                    voteRoundFor(p) = k /\ voteValueFor(p) = w  IN
  \* If k = -1, then no acceptor in Q has voted at all. In this case, we
  \* propose noop.
  IF k = -1 THEN
    \/ \E R \in DepServiceQuorum :
         /\ ExistsQuorumReply(R, I)
         /\ v = QuorumReply(R, I)
    \/ v = noopGadget
  \* If k is greater than 0, then k is a classic round, so V is a singleton
  \* set {v}. We can only propose this v.
  ELSE IF k > 0 THEN
    v \in V
  \* Otherwise, k = 0 is a fast round. If it's possible that v was chosen
  \* (i.e., O4(v)), then we propose v. Otherwise, we propose noop.
  ELSE IF \E w \in V : O4(w) THEN
    v = CHOOSE w \in V : O4(w)
  ELSE
    \/ \E R \in DepServiceQuorum :
         /\ ExistsQuorumReply(R, I)
         /\ v = QuorumReply(R, I)
    \/  v = noopGadget

\* Fast Paxos phase 2a at node n, instance I, for value v.
Phase2a(n, I, v) ==
  LET i == coordinatorRound[n][I] IN
  \* Since we shortcut fast round 0, a BPaxos node will never send a phase2a
  \* message in round 0.
  /\ i /= 0
  \* Only start phase2a if we haven't already.
  /\ coordinatorValue[n][I] = NULL
  /\ \E Q \in AcceptorClassicQuorum :
    /\ \A p \in Q : \E msg \in Phase1bsFrom(Q, I, i) : msg.acceptor = p
    /\ IsProposable(Q, I, i, Phase1bsFrom(Q, I, i), v)
  /\ coordinatorValue' = [coordinatorValue EXCEPT ![n][I] = v]
  /\ Send([
       type |-> "phase2a",
       instance |-> I,
       round |-> i,
       value |-> v
     ])
  /\ UNCHANGED <<depServiceVars, acceptorVars, nextInstance, coordinatorRound,
                 proposed, chosen>>

(******************************************************************************)
(* Acceptor actions.                                                          *)
(******************************************************************************)
\* Fast Paxos phase 1b at acceptor p, instance I, round i.
Phase1b(p, I, i) ==
  /\ i > round[p][I]
  /\ [type |-> "phase1a", instance |-> I, round |-> i] \in msgs
  /\ round' = [round EXCEPT ![p][I] = i]
  /\ Send([
       type |-> "phase1b",
       instance |-> I,
       round |-> i,
       voteRound |-> voteRound[p][I],
       voteValue |-> voteValue[p][I],
       acceptor |-> p
     ])
  /\ UNCHANGED <<depServiceVars, voteRound, voteValue, bpaxosVars, proposed,
                 chosen>>

\* Fast Paxos phase 2b at acceptor p, instance I, round 0.
FastPhase2b(p, I) ==
  LET v == dependencyGraphs[p][I] IN
  /\ round[p][I] = 0
  /\ voteRound[p][I] = -1
  /\ v /= NULL
  /\ voteRound' = [voteRound EXCEPT ![p][I] = 0]
  /\ voteValue' = [voteValue EXCEPT ![p][I] = v]
  /\ Send([
       type |-> "phase2b",
       instance |-> I,
       round |-> 0,
       value |-> v,
       acceptor |-> p
     ])
  /\ UNCHANGED <<depServiceVars, round, bpaxosVars, proposed, chosen>>

\* Fast Paxos phase 2b at acceptor p, instance I, round i > 0, value v.
ClassicPhase2b(p, I, i, v) ==
  /\ round[p][I] =< i
  /\ voteRound[p][I] < i
  /\ [type |-> "phase2a", instance |-> I, round |-> i, value |-> v] \in msgs
  /\ round' = [round EXCEPT ![p][I] = i]
  /\ voteRound' = [voteRound EXCEPT ![p][I] = i]
  /\ voteValue' = [voteValue EXCEPT ![p][I] = v]
  /\ Send([
       type |-> "phase2b",
       instance |-> I,
       round |-> i,
       value |-> v,
       acceptor |-> p
     ])
  /\ UNCHANGED <<depServiceVars, bpaxosVars, proposed, chosen>>

(******************************************************************************)
(* Meta actions.                                                              *)
(******************************************************************************)
Phase2bsFrom(Q, I, i) ==
  {msg \in msgs : /\ msg.type = "phase2b"
                  /\ msg.instance = I
                  /\ msg.round = i
                  /\ msg.acceptor \in Q}

\* Choose a gadget v in instance I in round 0.
ChooseFast(I, v) ==
  /\ \E Q \in AcceptorFastQuorum :
       \A p \in Q :
         \E msg \in Phase2bsFrom(Q, I, 0) : msg.acceptor = p /\ msg.value = v
  /\ chosen' = [chosen EXCEPT ![I] = @ \cup {v}]
  /\ UNCHANGED <<depServiceVars, acceptorVars, bpaxosVars, proposed, msgs>>

\* Choose a gadget v in instance I in round > 0.
ChooseSlow(I, v) ==
  /\ \E i \in Round, Q \in AcceptorClassicQuorum :
       /\ i > 0
       /\ \A p \in Q :
            \E msg \in Phase2bsFrom(Q, I, i) : msg.acceptor = p /\ msg.value = v
  /\ chosen' = [chosen EXCEPT ![I] = @ \cup {v}]
  /\ UNCHANGED <<depServiceVars, acceptorVars, bpaxosVars, proposed, msgs>>

Choose(I, v) ==
  \/ ChooseFast(I, v)
  \/ ChooseSlow(I, v)

--------------------------------------------------------------------------------

(******************************************************************************)
(* Specification.                                                             *)
(******************************************************************************)

Init ==
  /\ dependencyGraphs = [d \in DepServiceReplica |-> [I \in Instance |-> NULL]]
  /\ round = [p \in Acceptor |-> [I \in Instance |-> 0]]
  /\ voteRound = [p \in Acceptor |-> [I \in Instance |-> -1]]
  /\ voteValue = [p \in Acceptor |-> [I \in Instance |-> NULL]]
  /\ nextInstance = [n \in BPaxosReplica |-> 0]
  /\ coordinatorRound = [n \in BPaxosReplica |->
                        [I \in Instance |-> IF I[1] = n THEN 0 ELSE -1]]
  /\ coordinatorValue = [n \in BPaxosReplica |-> [I \in Instance |-> NULL]]
  /\ proposed = [I \in Instance |-> NULL]
  /\ chosen = [I \in Instance |-> {}]
  /\ msgs = {}

Next ==
  \/ \E n \in BPaxosReplica, cmd \in Command : ProposeCommand(n, cmd)
  \/ \E n \in BPaxosReplica, I \in Instance, i \in Round : Phase1a(n, I, i)
  \/ \E n \in BPaxosReplica, I \in Instance, v \in Gadget : Phase2a(n, I, v)
  \/ \E d \in DepServiceReplica, I \in Instance : DepServiceProcess(d, I)
  \/ \E p \in Acceptor, I \in Instance, i \in Round : Phase1b(p, I, i)
  \/ \E p \in Acceptor, I \in Instance : FastPhase2b(p, I)
  \/ \E p \in Acceptor, I \in Instance, i \in Round, v \in Gadget :
       ClassicPhase2b(p, I, i, v)
  \/ \E I \in Instance, v \in Gadget : Choose(I, v)

Spec == Init /\ [][Next]_vars

--------------------------------------------------------------------------------

(******************************************************************************)
(* Properties and Invariants.                                                 *)
(******************************************************************************)
\* Fast Paxos should only choose at most value per instance.
ConsensusConsistency ==
  \A I \in Instance : Cardinality(chosen[I]) =< 1

\* Only proposed commands (or noop) should be chosen.
Nontriviality ==
  \A I \in Instance :
    \A gadget \in chosen[I] :
      \/ gadget.cmd \in Values(proposed)
      \/ gadget.cmd = noop

\* If two conflicting commands a and b are chosen, then a is in deps(b), or b
\* is in deps(a), or both.
ChosenConflicts ==
  \A I1, I2 \in Instance :
    \A gadget1 \in chosen[I1], gadget2 \in chosen[I2] :
      \/ I1 = I2
      \/ <<gadget1.cmd, gadget2.cmd>> \notin Conflict
      \/ I1 \in gadget2.deps
      \/ I2 \in gadget1.deps

THEOREM Spec => /\ ConsensusConsistency
                /\ Nontriviality
                /\ ChosenConflicts

=============================================================================
