---------------------------- MODULE UnanimousBPaxos ----------------------------

(******************************************************************************)
(* This is a specification of an Unanimous BPaxos. Unanimous BPaxos is the    *)
(* same as the incorrect variant of BPaxos, except that superquorums now      *)
(* include every acceptor.                                                    *)
(******************************************************************************)

EXTENDS IncorrectBPaxos
ASSUME AcceptorFastQuorum = {Acceptor}

=============================================================================
