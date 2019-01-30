--------------------------------- MODULE Dict ----------------------------------

(******************************************************************************)
(* TLA+ has the notion of functions. For example [A -> B] is the set of all   *)
(* functions from the set A to the set B. Functions are a lot like the        *)
(* dictionaries you find in a language like Python, except for one notable    *)
(* distinction. A function f \in [A \to B] is total, so every value a \in A   *)
(* must map to some value b \in B by way of f. Dictionaries from A to B, on   *)
(* the other hand, do not have to map every a \in A to some corresponding b   *)
(* \in B. This module builds up dictionaries out of functions. Doing so is    *)
(* relatively straightforward. We introduce a NULL value and model a          *)
(* Dictionary as a function [A \to B \cup {NULL}].                            *)
(******************************************************************************)

CONSTANT NULL

Dict(K, V) == [K -> V \cup {NULL}]

Keys(dict) == {k \in DOMAIN dict : dict[k] /= NULL}

Values(dict) == {dict[k] : k \in Keys(dict)}

Items(dict) == {<<k, dict[k]>> : k \in Keys(dict)}

================================================================================
