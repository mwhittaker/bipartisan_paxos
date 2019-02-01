-------------------------- MODULE DeadlockBPaxosModel --------------------------

EXTENDS FiniteSets, DeadlockBPaxos, TLC

\* Dependency service replicas.
CONSTANT d1, d2, d3, d4, d5
DepServiceReplicas == {d1, d2, d3, d4, d5}
DepServiceReplicasSymmetry == Permutations(DepServiceReplicas)
DepServiceQuorums == {Q \in SUBSET DepServiceReplicas : Cardinality(Q) >= 3}

\* Acceptors.
CONSTANT p1, p2, p3, p4, p5
Acceptors == {p1, p2, p3, p4, p5}
AcceptorsSymmetry == Permutations(Acceptors)
AcceptorFastQuorums == {Q \in SUBSET Acceptors : Cardinality(Q) >= 4}
AcceptorClassicQuorums == {Q \in SUBSET Acceptors : Cardinality(Q) >= 3}

\* BPaxos replicas.
CONSTANT n1
BPaxosReplicas == {n1}
BPaxosReplicasSymmetry == Permutations(BPaxosReplicas)
MaxRoundValue == 1
CoordinatorOfValue(I, i) == n1

\* Commands.
CONSTANT a, b
Commands == {a, b}
CommandsSymmetry == Permutations(Commands)
Conflicts == {<<a, b>>, <<b, a>>}

Symmetry ==
  DepServiceReplicasSymmetry \union
  AcceptorsSymmetry \union
  BPaxosReplicasSymmetry \union
  CommandsSymmetry

================================================================================
