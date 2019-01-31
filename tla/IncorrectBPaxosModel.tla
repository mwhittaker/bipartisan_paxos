------------------------- MODULE IncorrectBPaxosModel --------------------------

EXTENDS FiniteSets, IncorrectBPaxos, TLC

\* Dependency service replicas.
CONSTANT d1, d2, d3, d4
DepServiceReplicas == {d1, d2, d3, d4}
DepServiceReplicasSymmetry == Permutations(DepServiceReplicas)
DepServiceQuorums == {Q \in SUBSET DepServiceReplicas : Cardinality(Q) >= 3}

\* Acceptors.
CONSTANT p1, p2, p3, p4
Acceptors == {p1, p2, p3, p4}
AcceptorsSymmetry == Permutations(Acceptors)
AcceptorFastQuorums == {Q \in SUBSET Acceptors : Cardinality(Q) >= 3}
AcceptorClassicQuorums == {Q \in SUBSET Acceptors : Cardinality(Q) >= 3}

\* BPaxos replicas.
CONSTANT n1, n2
BPaxosReplicas == {n1, n2}
BPaxosReplicasSymmetry == Permutations(Acceptors)
MaxRoundValue == 1
CoordinatorOfValue(I, i) ==
  \* For instance n.i, BPaxos node n must be the coordinator of fast round 0.
  IF I[1] = n1 THEN
    IF i % 2 = 0 THEN n1 ELSE n2
  ELSE
    IF i % 2 = 0 THEN n2 ELSE n1

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