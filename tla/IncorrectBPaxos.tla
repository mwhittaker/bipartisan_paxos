---------------------------- MODULE IncorrectBPaxos ----------------------------

\* TODO(mwhittaker): Document.

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
    voteValue: Command \cup {noop, NULL},
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
  /\ voteValue \in Dict(Acceptor, Dict(Instance, Command \union {noop, NULL}))
  /\ nextInstance \in Dict(BPaxosReplica, Instance)
  /\ coordinatorRound \in Dict(BPaxosReplica, Dict(Instance, Round))
  /\ coordinatorValue \in Dict(BPaxosReplica, Dict(Instance, Command \union {noop, NULL}))
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
(* BPaxos actions.                                                            *)
(******************************************************************************)
ProposeCommand(n, cmd) ==
  /\ cmd \notin Values(proposed)
  /\ proposed' = [proposed EXCEPT ![<<n, nextInstance[n]>>] = cmd]
  /\ nextInstance' = [nextInstance EXCEPT ![n] = @ + 1]
  /\ UNCHANGED <<depServiceVars, acceptorVars, coordinatorRound,
                 coordinatorValue, chosen, msgs>>

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
  LET voteRoundFor(p) == (CHOOSE msg \in M : msg.acceptor = p).voteRoundFor
      voteValueFor(p) == (CHOOSE msg \in M : msg.acceptor = p).voteValueFor
      k == Max({voteRoundFor(p) : p \in Q})
      V == {voteValueFor(p) : p \in {q \in Q : voteRoundFor(q) = k}}
      O4(w) == \E R \in AcceptorFastQuorum :
                 \A p \in Q \intersect R :
                    voteRoundFor(p) = k /\ voteValueFor(p) = w  IN
  \* If k is not equal to 0, then k is a classic round, so V is a singleton
  \* set. We can only propose this v.
  IF k /= 0 THEN
    v \in V
  \* If k = -1, then no acceptor in Q has voted at all. In this case, we
  \* propose noop.
  ELSE IF k = -1 THEN
    v = noopGadget
  \* Otherwise, if it's possible that v was chosen (i.e., O4(v)), then we
  \* propose v. Otherwise, we propose noop.
  ELSE
    O4(v) \/ v = noopGadget

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
(* Dependency service actions.                                                *)
(******************************************************************************)
\* Given a dependency graph G and command cmd, return the set of instances in G
\* that contain commands that conflict with cmd.
Dependencies(G, cmd) ==
  {I \in Instance : G[I] /= NULL /\ <<cmd, G[I].cmd>> \in Conflict}

DepServiceProcess(d, I) ==
  LET G == dependencyGraphs[d] IN
  /\ proposed[I] /= NULL
  /\ G[I] = NULL
  /\ LET cmd == proposed[I] IN
    /\ dependencyGraphs' = [dependencyGraphs EXCEPT ![d][I] =
                              [cmd |-> cmd, deps |-> Dependencies(G, cmd)]]
    /\ UNCHANGED <<acceptorVars, bpaxosVars, proposed, chosen, msgs>>

(******************************************************************************)
(* Acceptor actions.                                                          *)
(******************************************************************************)
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
\* TODO(mwhittaker): Choose.

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
  /\ coordinatorRound = [n \in BPaxosReplica |-> [I \in Instance |-> 0]]
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

Spec == Init /\ [][Next]_vars

--------------------------------------------------------------------------------

(******************************************************************************)
(* Properties and Invariants.                                                 *)
(******************************************************************************)













(* dependency service nodes *)
(*   - dependency graphs *)
(*  *)
(* fast paxos acceptors *)
(*   - for every instance: *)
(*     - round *)
(*     - voteRound *)
(*     - voteValue *)
(*  *)
(* ACTIONS *)
(*  *)
(* dependency service nodes *)
(*   - process command and send to fast paxos acceptors *)
(*   - process command and return response directly *)
(*  *)
(*  *)
(* fast paxos acceptors *)
(*   - for every instance: *)
(*     - handle phase 1a *)
(*     - handle phase 2a *)
(*  *)
(* BPaxos nodes *)
(*   - choose an instance for a new command *)
(*   - send the command out to the fast dep service nodes *)
(*  *)
(*   - collect fast paxos acceptor responses, and choose *)
(*  *)
(*   - initiate a new ballot for instance and run paxos for it *)


\*   (***************************************************************************)
\*   (* The module imports two standard modules.  Module $Naturals$ defines the *)
\*   (* set $Nat$ of naturals and the ordinary arithmetic operators; module     *)
\*   (* $FiniteSets$ defines $IsFiniteSet(S)$ to be true iff $S$ is a finite    *)
\*   (* set and defines $Cardinality(S)$ to be the number of elements in $S$,   *)
\*   (* if $S$ is finite.                                                       *)
\*   (***************************************************************************)
\*   EXTENDS Naturals, FiniteSets
\*   -----------------------------------------------------------------------------
\*   (***************************************************************************)
\*   (* \centering \large\bf Constants                                          *)
\*   (***************************************************************************)
\*
\*   (***************************************************************************)
\*   (* $Max(S)$ is defined to be the maximum of a nonempty finite set $S$ of   *)
\*   (* numbers.                                                                *)
\*   (***************************************************************************)
\*
\*   (***************************************************************************)
\*   (* The next statement declares the specification's constant parameters,    *)
\*   (* which have the following meanings:\\ \s{1}%                             *)
\*   (* \begin{tabular}{l@{ }l}                                                 *)
\*   (* $Val$ &    the set of values that may be proposed.\\                    *)
\*   (* $Acceptor$ &    the set of acceptors.\\                                 *)
\*   (* $FastNum$ &    the set of fast round numbers.\\                         *)
\*   (* $Quorum(i)$ &    the set of $i$-quorums.\\                              *)
\*   (* $Coord$ &    the set of coordinators.\\                                 *)
\*   (* $Coord(i)$ &    the coordinator of round $i$.                           *)
\*   (* \end{tabular}                                                           *)
\*   (***************************************************************************)
\*   CONSTANTS Val, Acceptor, FastNum, Quorum(_), Coord, CoordOf(_)
\*
\*   (***************************************************************************)
\*   (* $RNum$ is defined to be the set of positive integers, which is the set  *)
\*   (* of round numbers.                                                       *)
\*   (***************************************************************************)
\*   RNum == Nat \ {0}
\*
\*   (***************************************************************************)
\*   (* The following statement asserts the assumption that $FastNum$ is a set  *)
\*   (* of round numbers.                                                       *)
\*   (***************************************************************************)
\*   ASSUME FastNum \subseteq RNum
\*
\*   (***************************************************************************)
\*   (* $ClassicNum$ is defined to be the set of classic round numbers.         *)
\*   (***************************************************************************)
\*   ClassicNum == RNum \ FastNum
\*
\*   (***************************************************************************)
\*   (* The following assumption asserts that the set of acceptors is finite.   *)
\*   (* It is needed to ensure progress.                                        *)
\*   (***************************************************************************)
\*   ASSUME IsFiniteSet(Acceptor)
\*
\*   (***************************************************************************)
\*   (* The following asserts the assumptions that $Quorum(i)$ is a set of sets *)
\*   (* of acceptors, for every round number $i$, and that the Quorum           *)
\*   (* Requirement (Section~\ref{pg:quorum-requirement},                       *)
\*   (* page~\pageref{pg:quorum-requirement}) holds.                            *)
\*   (***************************************************************************)
\*   ASSUME \A i \in RNum :
\*            /\ Quorum(i) \subseteq SUBSET Acceptor
\*            /\ \A j \in RNum :
\*                 /\ \A Q \in Quorum(i), R \in Quorum(j) : Q \cap R # {}
\*                 /\ (j \in FastNum) =>
\*                      \A Q \in Quorum(i) : \A R1, R2 \in Quorum(j) :
\*                        Q \cap R1 \cap R2 # {}
\*
\*   (***************************************************************************)
\*   (* The following asserts the assumptions that $CoordOf(i)$ is a            *)
\*   (* coordinator, for every round number $i$, and that every coordinator is  *)
\*   (* the coordinator of infinitely many classic rounds.                      *)
\*   (***************************************************************************)
\*   ASSUME /\ \A i \in RNum : CoordOf(i) \in Coord
\*   \*       /\ \A c \in Coord, i \in Nat :
\*   \*            \E j \in ClassicNum : (j > i) /\ (c = CoordOf(j))
\*
\*   (***************************************************************************)
\*   (* $any$ and $none$ are defined to be arbitrary, distinct values that are  *)
\*   (* not elements of $Val$.                                                  *)
\*   (***************************************************************************)
\*   any  == CHOOSE v : v \notin Val
\*   none == CHOOSE n : n \notin Val \cup {any}
\*
\*   (***************************************************************************)
\*   (* $Message$ is defined to be the set of all possible messages.  A message *)
\*   (* is a record having a $type$ field indicating what phase message it is,  *)
\*   (* a $rnd$ field indicating the round number.  What other fields, if any,  *)
\*   (* a message has depends on its type.                                      *)
\*   (***************************************************************************)
\*   Message ==
\*          [type : {"phase1a"}, rnd : RNum]
\*     \cup [type : {"phase1b"}, rnd : RNum, vrnd : RNum \cup {0},
\*            vval : Val \cup {any}, acc : Acceptor]
\*     \cup [type : {"phase2a"}, rnd : RNum, val : Val \cup {any}]
\*     \cup [type : {"phase2b"}, rnd : RNum, val : Val, acc : Acceptor]
\*   -----------------------------------------------------------------------------
\*   (***************************************************************************)
\*   (* \centering\large\bf Variables and State Predicates                      *)
\*   (***************************************************************************)
\*
\*   (***************************************************************************)
\*   (* The following statement declares the specification's variables, which   *)
\*   (* have all been described above---either in Section~\ref{sec:basic-alg}   *)
\*   (* on page~\pageref{pg:variables} or in this appendix.                     *)
\*   (***************************************************************************)
\*   VARIABLES rnd, vrnd, vval, crnd, cval, amLeader, sentMsg, proposed,
\*             learned, goodSet
\*
\*   (***************************************************************************)
\*   (* Defining the following tuples of variables makes it more convenient to  *)
\*   (* state which variables are left unchanged by the actions.                *)
\*   (***************************************************************************)
\*   aVars == <<rnd, vrnd, vval>>                       \* Acceptor variables.
\*   cVars == <<crnd, cval>>                            \* Coordinator variables.
\*   oVars == <<amLeader, proposed, learned, goodSet>>  \* Most other variables.
\*   vars  == <<aVars, cVars, oVars, sentMsg>>          \* All variables.
\*
\*   (***************************************************************************)
\*   (* $TypeOK$ is the type-correctness invariant, asserting that the value of *)
\*   (* each variable is an element of the proper set (its ``type'').  Type     *)
\*   (* correctness of the specification means that $TypeOK$ is an              *)
\*   (* invariant---that is, it is true in every state of every behavior        *)
\*   (* allowed by the specification.                                           *)
\*   (***************************************************************************)
\*   TypeOK ==
\*     /\ rnd  \in [Acceptor -> Nat]
\*     /\ vrnd \in [Acceptor -> Nat]
\*     /\ vval \in [Acceptor -> Val \cup {any}]
\*     /\ crnd \in [Coord -> Nat]
\*     /\ cval \in [Coord -> Val \cup {any, none}]
\*     /\ amLeader \in [Coord -> BOOLEAN]
\*     /\ sentMsg  \in SUBSET Message
\*     /\ proposed \in SUBSET Val
\*     /\ learned  \in SUBSET Val
\*     /\ goodSet \subseteq Acceptor \cup Coord
\*
\*   (***************************************************************************)
\*   (* $Init$ is the initial predicate that describes the initial values of    *)
\*   (* all the variables.                                                      *)
\*   (***************************************************************************)
\*   Init ==
\*     /\ rnd  = [a \in Acceptor |-> 0]
\*     /\ vrnd = [a \in Acceptor |-> 0]
\*     /\ vval = [a \in Acceptor |-> any]
\*     /\ crnd = [c \in Coord |-> 0]
\*     /\ cval = [c \in Coord |-> none]
\*     /\ amLeader \in [Coord -> BOOLEAN]
\*     /\ sentMsg  = {}
\*     /\ proposed = {}
\*     /\ learned  = {}
\*     /\ goodSet \in SUBSET (Acceptor \cup Coord)
\*   -----------------------------------------------------------------------------
\*   (***************************************************************************)
\*   (* \centering\large\bf Action Definitions                                  *)
\*   (***************************************************************************)
\*
\*   (***************************************************************************)
\*   (* $Send(m)$ describes the state change that represents the sending of     *)
\*   (* message $m$.  It is used as a conjunct in defining the algorithm        *)
\*   (* actions.                                                                *)
\*   (***************************************************************************)
\*   Send(m)  ==  sentMsg' = sentMsg \cup {m}
\*
\*   (***************************************************************************)
\*   (* \centering \large\bf Coordinator Actions                                *)
\*   (***************************************************************************)
\*
\*   (***************************************************************************)
\*   (* Action $Phase1a(c,i)$ specifies the execution of phase 1a of round $i$  *)
\*   (* by coordinator $c$, described in Section~\ref{sec:basic-alg} (on        *)
\*   (* page~\pageref{pg:1a}) and refined by CA2$'$ (Section~\ref{sec:CA2'},    *)
\*   (* page~\pageref{sec:CA2'}).                                               *)
\*   (***************************************************************************)
\*   Phase1a(c, i) ==
\*     /\ amLeader[c]
\*     /\ c = CoordOf(i)
\*     /\ crnd[c] < i
\*     /\ \/ crnd[c] = 0
\*        \/ \E m \in sentMsg : /\ crnd[c] < m.rnd
\*                              /\ m.rnd < i
\*        \/ /\ crnd[c] \in FastNum
\*           /\ i \in ClassicNum
\*     /\ crnd' = [crnd EXCEPT ![c] = i]
\*     /\ cval' = [cval EXCEPT ![c] = none]
\*     /\ Send([type |-> "phase1a", rnd |-> i])
\*     /\ UNCHANGED <<aVars, oVars>>
\*
\*   (***************************************************************************)
\*   (* $MsgsFrom(Q, i, phase)$ is defined to be the set of messages in         *)
\*   (* $sentMsg$ of type $phase$ (which may equal $"phase1b"$ or $"phase2b"$)  *)
\*   (* sent in round $i$ by the acceptors in the set $Q$.                      *)
\*   (***************************************************************************)
\*   MsgsFrom(Q, i, phase) ==
\*      {m \in sentMsg : (m.type = phase) /\ (m.acc \in Q) /\ (m.rnd = i)}
\*
\*   (***************************************************************************)
\*   (* If $M$ is the set of round $i$ phase 1b messages sent by the acceptors  *)
\*   (* in a quorum $Q$, then $IsPickableVal(Q, i, M, v)$ is true iff the rule  *)
\*   (* of Figure~\ref{fig:fast-paxos-choice}                                   *)
\*   (* (page~\pageref{fig:fast-paxos-choice}) allows the coordinator to send   *)
\*   (* the value $v$ in a phase 2a message for round~$i$.                      *)
\*   (***************************************************************************)
\*   IsPickableVal(Q, i, M, v) ==
\*     LET vr(a) == (CHOOSE m \in M : m.acc = a).vrnd
\*         vv(a) == (CHOOSE m \in M : m.acc = a).vval
\*         k == Max({vr(a) : a \in Q})
\*         V == {vv(a) : a \in {b \in Q : vr(b) = k}}
\*         O4(w) == \E R \in Quorum(k) :
\*                    \A a \in R \cap Q : (vr(a) = k) /\ (vv(a) = w)
\*     IN  IF k = 0 THEN \/ v \in proposed
\*                       \/ /\ i \in FastNum
\*                          /\ v = any
\*                  ELSE IF Cardinality(V) = 1
\*                         THEN v \in V
\*                         ELSE IF \E w \in V : O4(w)
\*                                 THEN v = CHOOSE w \in V : O4(w)
\*                                 ELSE v \in proposed
\*
\*   (***************************************************************************)
\*   (* Action $Phase2a(c,v)$ specifies the execution of phase 2a by            *)
\*   (* coordinator $c$ with value $v$, as described in                         *)
\*   (* Section~\ref{sec:basic-alg} (on page~\pageref{pg:2a}) and               *)
\*   (* Section~\ref{sec:picking} (page~\pageref{sec:picking}), and refined by  *)
\*   (* CA2$'$ (Section~\ref{sec:CA2'}, page~\pageref{sec:CA2'}).               *)
\*   (***************************************************************************)
\*   Phase2a(c, v) ==
\*     LET i == crnd[c]
\*     IN  /\ i # 0
\*         /\ cval[c] = none
\*         /\ amLeader[c]
\*         /\ \E Q \in Quorum(i) :
\*              /\ \A a \in Q : \E m \in MsgsFrom(Q, i, "phase1b") : m.acc = a
\*              /\ IsPickableVal(Q, i, MsgsFrom(Q, i, "phase1b"), v)
\*         /\ cval' = [cval EXCEPT ![c] = v]
\*         /\ Send([type |-> "phase2a", rnd |-> i, val |-> v])
\*         /\ UNCHANGED <<crnd, aVars, oVars>>
\*
\*   (***************************************************************************)
\*   (* $P2bToP1b(Q, i)$ is defined to be the set of round $i+1$ phase~1b       *)
\*   (* messages implied by the round $i$ phase~2b messages sent by the         *)
\*   (* acceptors in the set $Q$, as explained in                               *)
\*   (* Section~\ref{sec:collision-recovery}.                                   *)
\*   (***************************************************************************)
\*   P2bToP1b(Q, i) ==
\*     {[type |-> "phase1b", rnd |-> i+1, vrnd |-> i,
\*         vval |-> m.val, acc |-> m.acc] : m \in MsgsFrom(Q, i, "phase2b")}
\*
\*   (***************************************************************************)
\*   (* Action $CoordinatedRecovery(c, v)$ specifies the coordinated recovery   *)
\*   (* described in Section~\ref{pg:coord-recovery},                           *)
\*   (* page~\pageref{pg:coord-recovery}.  With this action, coordinator $c$    *)
\*   (* attempts to recover from a collision in round $crnd[c]$ by sending      *)
\*   (* round $crnd[c]+1$ phase~2a messages for the value $v$.  Although CA2$'$ *)
\*   (* (Section~\ref{sec:CA2'}, page~\pageref{sec:CA2'}) implies that this     *)
\*   (* action should be performed only if $crnd[c]+1$ is a classic round, that *)
\*   (* restriction is not required for correctness and is omitted from the     *)
\*   (* specification.                                                          *)
\*   (***************************************************************************)
\*   CoordinatedRecovery(c, v) ==
\*     LET i == crnd[c]
\*     IN  /\ amLeader[c]
\*         /\ cval[c] = any
\*         /\ c = CoordOf(i+1)
\*         /\ \E Q \in Quorum(i+1) :
\*              /\ \A a \in Q : \E m \in P2bToP1b(Q, i) : m.acc  = a
\*              /\ IsPickableVal(Q, i+1, P2bToP1b(Q, i), v)
\*         /\ cval' = [cval EXCEPT ![c] = v]
\*         /\ crnd' = [crnd EXCEPT ![c] = i+1]
\*         /\ Send([type |-> "phase2a", rnd |-> i+1, val |-> v])
\*         /\ UNCHANGED <<aVars, oVars>>
\*
\*   (***************************************************************************)
\*   (* $coordLastMsg(c)$ is defined to be the last message that coordinator    *)
\*   (* $c$ sent, if $crnd[c]>0$.                                               *)
\*   (***************************************************************************)
\*   coordLastMsg(c) ==
\*      IF cval[c] = none
\*        THEN [type |-> "phase1a", rnd |-> crnd[c]]
\*        ELSE [type |-> "phase2a", rnd |-> crnd[c], val |-> cval[c]]
\*
\*
\*   (***************************************************************************)
\*   (* In action $CoordRetransmit(c)$, coordinator $c$ retransmits the last    *)
\*   (* message it sent.  This action is a stuttering action (meaning it does   *)
\*   (* not change the value of any variable, so it is a no-op) if that message *)
\*   (* is still in $sentMsg$.  However, this action is needed because $c$      *)
\*   (* might have failed after first sending the message and subsequently have *)
\*   (* been repaired after the message was removed from $sentMsg$.             *)
\*   (***************************************************************************)
\*   CoordRetransmit(c) ==
\*     /\ amLeader[c]
\*     /\ crnd[c] # 0
\*     /\ Send(coordLastMsg(c))
\*     /\ UNCHANGED <<aVars, cVars, oVars>> \* amLeader, proposed, learned, goodSet
\*
\*   (***************************************************************************)
\*   (* $CoordNext(c)$ is the next-state action of coordinator $c$---that is,   *)
\*   (* the disjunct of the algorithm's complete next-state action that         *)
\*   (* represents actions of that coordinator.                                 *)
\*   (***************************************************************************)
\*   CoordNext(c) ==
\*     \/ \E i \in RNum : Phase1a(c, i)
\*     \/ \E v \in Val \cup {any} : Phase2a(c, v)
\*     \/ \E v \in Val : CoordinatedRecovery(c, v)
\*     \/ CoordRetransmit(c)
\*   -----------------------------------------------------------------------------
\*   (***************************************************************************)
\*   (* \centering \large\bf Acceptor Actions                                   *)
\*   (***************************************************************************)
\*
\*   (***************************************************************************)
\*   (* Action $Phase1b(i, a)$ specifies the execution of phase 1b for round    *)
\*   (* $i$ by acceptor $a$, described in Section~\ref{sec:basic-alg} on        *)
\*   (* page~\pageref{pg:1a}.                                                   *)
\*   (***************************************************************************)
\*   Phase1b(i, a) ==
\*     /\ rnd[a] < i
\*     /\ [type |-> "phase1a", rnd |-> i] \in sentMsg
\*     /\ rnd' = [rnd EXCEPT ![a] = i]
\*     /\ Send([type |-> "phase1b", rnd |-> i, vrnd |-> vrnd[a], vval |-> vval[a],
\*              acc |-> a])
\*     /\ UNCHANGED <<cVars, oVars, vrnd, vval>>
\*
\*   (***************************************************************************)
\*   (* Action $Phase2b(i, a, v)$ specifies the execution of phase 2b for round *)
\*   (* $i$ by acceptor $a$, upon receipt of either a phase~2a message or a     *)
\*   (* proposal (for a fast round) with value $v$.  It is described in         *)
\*   (* Section~\ref{sec:basic-alg} on page~\pageref{pg:1a} and                 *)
\*   (* Section~\ref{sec:basic-fast} on page~\pageref{pg:fast-2b}.              *)
\*   (***************************************************************************)
\*   Phase2b(i, a, v) ==
\*     /\ rnd[a] \leq i
\*     /\ vrnd[a] < i
\*     /\ \E m \in sentMsg :
\*          /\ m.type = "phase2a"
\*          /\ m.rnd = i
\*          /\ \/ m.val = v
\*             \/ /\ m.val = any
\*                /\ v \in proposed
\*     /\ rnd'  = [rnd  EXCEPT ![a] = i]
\*     /\ vrnd' = [vrnd EXCEPT ![a] = i]
\*     /\ vval' = [vval EXCEPT ![a] = v]
\*     /\ Send([type |-> "phase2b", rnd |-> i, val |-> v, acc |-> a])
\*     /\ UNCHANGED <<cVars, oVars>>
\*
\*   (***************************************************************************)
\*   (* Action $UncoordinatedRecovery(i, a, v)$ specifies uncoordinated         *)
\*   (* recovery, described in Section~\ref{pg:uncoord-recovery} on             *)
\*   (* page~\pageref{pg:uncoord-recovery}.  With this action, acceptor $a$     *)
\*   (* attempts to recover from a collision in round $i$ by sending a round    *)
\*   (* $i+1$ phase~2b message with value $v$.                                  *)
\*   (***************************************************************************)
\*   UncoordinatedRecovery(i, a, v) ==
\*     /\ i+1 \in FastNum
\*     /\ rnd[a] \leq i
\*     /\ \E Q \in Quorum(i+1) :
\*           /\ \A b \in Q : \E m \in P2bToP1b(Q, i) : m.acc = b
\*           /\ IsPickableVal(Q, i+1, P2bToP1b(Q, i), v)
\*     /\ rnd'  = [rnd  EXCEPT ![a] = i+1]
\*     /\ vrnd' = [vrnd EXCEPT ![a] = i+1]
\*     /\ vval' = [vval EXCEPT ![a] = v]
\*     /\ Send([type |-> "phase2b", rnd |-> i+1, val |-> v, acc |-> a])
\*     /\ UNCHANGED <<cVars, oVars>>
\*
\*   (***************************************************************************)
\*   (* $accLastMsg(a)$ is defined to be the last message sent by acceptor $a$, *)
\*   (* if $rnd[a]>0$.                                                          *)
\*   (***************************************************************************)
\*   accLastMsg(a) ==
\*     IF vrnd[a] < rnd[a]
\*       THEN [type |-> "phase1b", rnd |-> rnd[a], vrnd |-> vrnd[a],
\*               vval |-> vval[a], acc |-> a]
\*       ELSE [type |-> "phase2b", rnd |-> rnd[a], val |-> vval[a],
\*               acc |-> a]
\*
\*   (***************************************************************************)
\*   (* In action $AcceptorRetransmit(a)$, acceptor $a$ retransmits the last    *)
\*   (* message it sent.                                                        *)
\*   (***************************************************************************)
\*   AcceptorRetransmit(a) ==
\*     /\ rnd[a] # 0
\*     /\ Send(accLastMsg(a))
\*     /\ UNCHANGED <<aVars, cVars, oVars>> \* amLeader, proposed, learned, goodSet
\*
\*   (***************************************************************************)
\*   (* $AcceptorNext(a)$ is the next-state action of acceptor $a$---that is,   *)
\*   (* the disjunct of the next-state action that represents actions of that   *)
\*   (* acceptor.                                                               *)
\*   (***************************************************************************)
\*   AcceptorNext(a) ==
\*     \/ \E i \in RNum : \/ Phase1b(i, a)
\*                        \/ \E v \in Val : Phase2b(i, a, v)
\*     \/ \E i \in FastNum, v \in Val : UncoordinatedRecovery(i, a, v)
\*     \/ AcceptorRetransmit(a)
\*   -----------------------------------------------------------------------------
\*   (***************************************************************************)
\*   (* \centering \large\bf Other Actions                                      *)
\*   (***************************************************************************)
\*
\*   (***************************************************************************)
\*   (* Action $Propose(v)$ represents the proposal of a value $v$ by some      *)
\*   (* proposer.                                                               *)
\*   (***************************************************************************)
\*   Propose(v) ==
\*     /\ proposed' = proposed \cup {v}
\*     /\ UNCHANGED <<aVars, cVars, amLeader, sentMsg, learned, goodSet>>
\*
\*   (***************************************************************************)
\*   (* Action $Learn(v)$ represents the learning of a value $v$ by some        *)
\*   (* learner.                                                                *)
\*   (***************************************************************************)
\*   Learn(v) ==
\*     /\ \E i \in RNum :
\*          \E Q \in Quorum(i) :
\*            \A a \in Q :
\*              \E m \in sentMsg : /\ m.type = "phase2b"
\*                                 /\ m.rnd  = i
\*                                 /\ m.val = v
\*                                 /\ m.acc  = a
\*     /\ learned' = learned \cup {v}
\*     /\ UNCHANGED
\*          <<aVars, cVars, amLeader, sentMsg, proposed, goodSet>>
\*
\*   (***************************************************************************)
\*   (* Action $LeaderSelection$ allows an arbitrary change to the values of     *)
\*   (* $amLeader[c]$, for all coordinators $c$.  Since this action may be      *)
\*   (* performed at any time, the specification makes no assumption about the  *)
\*   (* outcome of leader selection.  (However, progress is guaranteed only     *)
\*   (* under an assumption about the values of $amLeader[c]$.)                 *)
\*   (***************************************************************************)
\*   LeaderSelection ==
\*     /\ amLeader' \in [Coord -> BOOLEAN]
\*     /\ UNCHANGED <<aVars, cVars, sentMsg, proposed, learned, goodSet>>
\*
\*
\*   (***************************************************************************)
\*   (* Action $FailOrRepair$ allows an arbitrary change to the set $goodSet$. *)
\*   (* Since this action may be performed at any time, the specification makes *)
\*   (* no assumption about what agents are good.  (However, progress is        *)
\*   (* guaranteed only under an assumption about the value of $goodSet$.)     *)
\*   (***************************************************************************)
\*   FailOrRepair ==
\*     /\ goodSet' \in SUBSET (Coord \cup Acceptor)
\*     /\ UNCHANGED <<aVars, cVars, amLeader, sentMsg, proposed, learned>>
\*
\*   (***************************************************************************)
\*   (* Action $LoseMsg(m)$ removes message $m$ from $sentMsg$.  It is always   *)
\*   (* enabled unless $m$ is the last message sent by an acceptor or           *)
\*   (* coordinator in $goodSet$.  Hence, the only assumption the              *)
\*   (* specification makes about message loss is that the last message sent by *)
\*   (* an agent in $goodSet$ is not lost.  Because $sentMsg$ includes         *)
\*   (* messages in an agent's output buffer, this effectively means that a     *)
\*   (* non-failed process always has the last message it sent in its output    *)
\*   (* buffer, ready to be retransmitted.                                      *)
\*   (***************************************************************************)
\*   LoseMsg(m) ==
\*     /\ ~ \/ /\ m.type \in {"phase1a", "phase2a"}
\*             /\ m = coordLastMsg(CoordOf(m.rnd))
\*             /\ CoordOf(m.rnd) \in goodSet
\*             /\ amLeader[CoordOf(m.rnd)]
\*          \/ /\ m.type \in {"phase1b", "phase2b"}
\*             /\ m = accLastMsg(m.acc)
\*             /\ m.acc \in goodSet
\*     /\ sentMsg' = sentMsg \ {m}
\*     /\ UNCHANGED <<aVars, cVars, oVars>> \* amLeader, proposed, learned, goodSet
\*
\*   (***************************************************************************)
\*   (* Action $OtherAction$ is the disjunction of all actions other than ones  *)
\*   (* performed by acceptors or coordinators, plus the $LeaderSelection$      *)
\*   (* action (which represents leader-selection actions performed by the      *)
\*   (* coordinators).                                                          *)
\*   (***************************************************************************)
\*   OtherAction ==
\*     \/ \E v \in Val : Propose(v) \/ Learn(v)
\*     \/ LeaderSelection \/ FailOrRepair
\*     \/ \E m \in sentMsg : LoseMsg(m)
\*
\*
\*   (***************************************************************************)
\*   (* $Next$ is the algorithm's complete next-state action.                   *)
\*   (***************************************************************************)
\*   Next ==
\*     \/ \E c \in Coord : CoordNext(c)
\*     \/ \E a \in Acceptor : AcceptorNext(a)
\*     \/ OtherAction
\*   -----------------------------------------------------------------------------
\*   (***************************************************************************)
\*   (* \centering\large\bf Temporal Formulas                                   *)
\*   (***************************************************************************)
\*
\*   (***************************************************************************)
\*   (* Formula $Fairness$ specifies the fairness requirements as the           *)
\*   (* conjunction of weak fairnes formulas.  Intuitively, it states           *)
\*   (* approximately the following:                                            *)
\*   (* \begin{itemize}                                                         *)
\*   (* \item[] A coordinator $c$ in $goodSet$ must perform some action if it   *)
\*   (* can, and it must perform a $Phase1a(c,i)$ action for a classic round    *)
\*   (* $i$ if it can.                                                          *)
\*   (*                                                                         *)
\*   (* \item[] An acceptor in $goodSet$ must perform some action if it can.    *)
\*   (*                                                                         *)
\*   (* \item[] A value that can be learned must be learned.                    *)
\*   (* \end{itemize}                                                           *)
\*   (* It is not obvious that these fairness requirements suffice to imply the *)
\*   (* progress property, and that fairness of each individual acceptor and    *)
\*   (* coordinator action is not needed.  Part of the reason is that formula   *)
\*   (* $Fairness$ does not allow an agent in $goodSet$ to do nothing but       *)
\*   (* $Retransmit$ actions if another of its actions is enabled, since all    *)
\*   (* but the first retransmission would be a stuttering step, and weak       *)
\*   (* fairness of an action $A$ requires a non-stuttering $A$ step to occur   *)
\*   (* if it is enabled.                                                       *)
\*   (***************************************************************************)
\*   Fairness ==
\*     /\ \A c \in Coord :
\*          /\ WF_vars((c \in goodSet) /\ CoordNext(c))
\*          /\ WF_vars((c \in goodSet) /\ (\E i \in ClassicNum : Phase1a(c, i)))
\*     /\ \A a \in Acceptor : WF_vars((a \in goodSet) /\ AcceptorNext(a))
\*     /\ \A v \in Val : WF_vars(Learn(v))
\*
\*   (***************************************************************************)
\*   (* Formula $Spec$ is the complete specification of the Fast Paxos          *)
\*   (* algorithm.                                                              *)
\*   (***************************************************************************)
\*   Spec == Init /\ [][Next]_vars /\ Fairness
\*
\*   (***************************************************************************)
\*   (* $Nontriviality$ asserts that every learned value has been proposed, and *)
\*   (* $Consistency$ asserts that at most one value has been learned.  The     *)
\*   (* Nontriviality and Consistency conditions for consensus                  *)
\*   (* (Section~\ref{sec:problem}) are equivalent to the invariance of these   *)
\*   (* state predicates.                                                       *)
\*   (***************************************************************************)
\*   Nontriviality == learned \subseteq proposed
\*   Consistency   == Cardinality(learned) \leq 1
\*
\*   (***************************************************************************)
\*   (* The following theorem asserts that the state predicates $TypeOK$,       *)
\*   (* $Nontriviality$, and $Consistency$ are invariants of specification      *)
\*   (* $Spec$, which implies that $Spec$ satisfies the safety properties of a  *)
\*   (* consensus algorithm.  It was checked by the TLC model checker on models *)
\*   (* that were too small to find a real bug in the algorithm but would have  *)
\*   (* detected most simple errors in the specification.                       *)
\*   (***************************************************************************)
\*   THEOREM Spec => [](TypeOK /\ Nontriviality /\ Consistency)
\*
\*   (***************************************************************************)
\*   (* Because the specification does not explicitly mention proposers and     *)
\*   (* learners, condition $LA(p,l,c,Q)$ described on                          *)
\*   (* page~\pageref{pg:condition-LA} of Section~\ref{pg:condition-LA} is      *)
\*   (* replaced by $LA(c,Q)$, which depends only on $c$ and $Q$.  Instead of   *)
\*   (* asserting that some particular proposer $p$ has proposed a value, it    *)
\*   (* asserts that some value has been proposed.                              *)
\*   (***************************************************************************)
\*   LA(c, Q) ==
\*     /\ {c} \cup Q \subseteq goodSet
\*     /\ proposed # {}
\*     /\ \A ll \in Coord : amLeader[ll] \equiv (c = ll)
\*
\*   (***************************************************************************)
\*   (* The following theorem asserts that $Spec$ satisfies the progress        *)
\*   (* property of Fast Paxos, described in Sections \ref{sec:progress}        *)
\*   (* and~\ref{sec:fast-progress}.  The temporal formula $<>[]LA(c,Q)$        *)
\*   (* asserts that $LA(c,Q)$ holds from some time on, and $<>(learned # \{\})$*)
\*   (* asserts that some value is eventually learned.                          *)
\*   (***************************************************************************)
\*   THEOREM /\ Spec
\*           /\ \E Q \in SUBSET Acceptor :
\*                  /\ \A i \in ClassicNum : Q \in Quorum(i)
\*                  /\ \E c \in Coord : <>[]LA(c, Q)
\*           => <>(learned # {})

=============================================================================
