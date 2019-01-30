------------------------- MODULE IncorrectBPaxosModel --------------------------

EXTENDS FiniteSets, IncorrectBPaxos, TLC

\* Dependency service replicas.
CONSTANT d1, d2, d3
DepServiceReplicas == {d1, d2, d3}
DepServiceReplicasSymmetry == Permutations(DepServiceReplicas)
DepServiceQuorums == {Q \in SUBSET DepServiceReplicas : Cardinality(Q) >= 2}

\* Acceptors.
CONSTANT p1, p2, p3
Acceptors == {p1, p2, p3}
AcceptorsSymmetry == Permutations(Acceptors)
AcceptorFastQuorums == {Q \in SUBSET Acceptors : Cardinality(Q) >= 3}
AcceptorClassicQuorums == {Q \in SUBSET Acceptors : Cardinality(Q) >= 2}

\* BPaxos replicas.
CONSTANT n1, n2
BPaxosReplicas == {n1, n2}
BPaxosReplicasSymmetry == Permutations(Acceptors)
MaxRoundValue == 3
CoordinatorOfValue(i) == IF i % 2 = 0 THEN n1 ELSE n2

\* Commands.
CONSTANT a, b, c
Commands == {a, b, c}
CommandsSymmetry == Permutations(Commands)
Conflicts == {
  <<a, b>>, <<b, a>>,
  <<a, c>>, <<c, a>>,
  <<b, c>>, <<c, b>>
}

Symmetry ==
  DepServiceReplicasSymmetry \union
  AcceptorsSymmetry \union
  BPaxosReplicasSymmetry \union
  CommandsSymmetry

================================================================================
