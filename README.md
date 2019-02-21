# Bipartisan Paxos

Consensus and state machine replication are fundamental problems in distributed
systems that are both well-studied in academia and widely implemented in
industry. Paxos, one of the earliest asynchronous consensus protocols, was
developed roughly 30 years ago and has since become the de-facto standard in
industry. Since that time, Paxos and Multi-Paxos (the state machine replication
protocol built on Paxos) have been improved along three core dimensions:
latency, throughput, and simplicity.

- First, the latency of Paxos---i.e. the minimum number of message delays
  between when a value is proposed by a client and when it is chosen by the
  protocol---is higher than necessary. Fast Paxos improves Paxos' latency to
  its theoretical minimum by allowing clients to propose commands directly to
  acceptors.
- Second, the throughput of Multi-Paxos is bottlenecked by the throughput of a
  single leader. Fast Paxos partially resolves this problem by allowing clients
  to bypass the leader, but this leads to high conflict rates, lowering the
  throughput of the protocol. Generalized Paxos and GPaxos reduce the number of
  conflicts by taking advantage of the commutativity of state machine commands,
  but still rely on a single arbiter to resolve conflicts when they arise.
  EPaxos and Caesar are both fully leaderless and improve on Generalized Paxos
  by not relying on a single process either during normal processing or
  conflict resolution.
- Third, Paxos and Multi-Paxos have developed a reputation for being overly
  complicated, leading to a number of publications attempting to clarify the
  protocols and a number of protocols touted as simpler alternatives.

Despite the large body of work, no state machine replication protocol has
claimed the trifecta of low latency, high throughput, and simplicity. Existing
protocols typically sacrifice one of these features for the other two. In this
paper, we present Bipartisan Paxos (or BPaxos, for short): a family of
asynchronous state machine replication protocols that accomplish all three. The
BPaxos protocols can commit a command in two message delays (the theoretical
minimum). They are also fully leaderless and do not depend on a distinguished
leader for normal processing or conflict resolution. Furthermore, we employ
three techniques to make the BPaxos protocols as simple as possible.

- First, the protocols are modular. Every protocol is composed of small
  subcomponents, each of which can be understood individually.
- Second, we re-use existing algorithms to implement these subcomponents
  whenever possible, reducing the cognitive burden of understanding a new
  protocol that is written entirely from scratch.
- Third, the three BPaxos protocols---Simple BPaxos, Unanimous BPaxos, and
  Majority Commit BPaxos---are all incremental refinements of one another. We
  begin with a very simple protocol, Simple BPaxos, and then slowly increase
  the complexity. This allows us to decouple the nuances of the protocols,
  understanding each in isolation.
