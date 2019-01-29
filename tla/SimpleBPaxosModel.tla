--------------------------- MODULE SimpleBPaxosModel ---------------------------

EXTENDS FiniteSets, SimpleBPaxos, TLC

\* Dependency service replicas.
CONSTANT d1, d2, d3
DepServiceReplicas == {d1, d2, d3}
DepServiceReplicasSymmetry == Permutations(DepServiceReplicas)
DepServiceQuorums == {Q \in SUBSET DepServiceReplicas : Cardinality(Q) >= 2}

\* Commands.
CONSTANT a, b, c
Commands == {a, b, c}
CommandsSymmetry == Permutations(Commands)
Conflicts == {
  <<a, b>>, <<b, a>>,
  <<a, c>>, <<c, a>>,
  <<b, c>>, <<c, b>>
}

Symmetry == DepServiceReplicasSymmetry \union CommandsSymmetry

================================================================================
