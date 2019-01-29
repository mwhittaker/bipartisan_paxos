--------------------------------- MODULE Dict ----------------------------------

\* Dependency service nodes and BPaxos nodes both maintain dependency graphs.
\* We model these dependency graphs as dicts from an instance (e.g., Q.1) to
\* the instance's command (e.g., a) and its dependencies (e.g, {R.1, S.2}). As
\* described in [1], we model a dict from domain K to range V as a function
\* from K to V \cup {NULL}. This is that NULL value.
\*
\* [1]: https://stackoverflow.com/a/47118549/3187068
CONSTANT NULL

Dict(K, V) == [K -> V \cup {NULL}]

Keys(dict) == {k \in DOMAIN dict : dict[k] /= NULL}

Values(dict) == {dict[k] : k \in Keys(dict)}

Items(dict) == {<<k, dict[k]>> : k \in Keys(dict)}

================================================================================
