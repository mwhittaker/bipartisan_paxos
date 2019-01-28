--------------------------- MODULE SimpleBPaxosModel ---------------------------

EXTENDS FiniteSets, SimpleBPaxos, TLC

\* Constants.
CONSTANT d1, d2, d3
DependencyServiceReplicas == {d1, d2, d3}
DependencyServiceReplicasSymmetry == Permutations(DependencyServiceReplicas)
DependencyServiceQuorums ==
    {Q \in SUBSET DependencyServiceReplicas : Cardinality(Q) >= 2}

CONSTANT n1, n2, n3
BPaxosReplicas == {n1, n2, n3}
BPaxosReplicasSymmetry == Permutations(BPaxosReplicas)

Commands == {"a", "b", "c", "d"}
Conflicts == {
    <<"a", "b">>, <<"b", "a">>,
    <<"b", "c">>, <<"c", "b">>,
    <<"c", "d">>, <<"d", "c">>,
    <<"d", "a">>, <<"a", "d">>
}

Symmetry == DependencyServiceReplicasSymmetry \union BPaxosReplicasSymmetry

================================================================================
