--------------------------- MODULE SimpleBPaxosModel ---------------------------

EXTENDS FiniteSets, SimpleBPaxos, TLC

\* Commands.
CONSTANT a, b, c
Commands == {a, b, c}
CommandsSymmetry == Permutations(Commands)
Conflicts == {
  <<a, b>>, <<b, a>>,
  <<a, c>>, <<c, a>>,
  <<b, c>>, <<c, b>>
}

\* Dependency service nodes.
CONSTANT d1, d2, d3
DepServiceNodes == {d1, d2, d3}
DepServiceNodesSymmetry == Permutations(DepServiceNodes)
DepServiceQuorums == {Q \in SUBSET DepServiceNodes : Cardinality(Q) >= 2}

Symmetry == CommandsSymmetry \union DepServiceNodesSymmetry

================================================================================
