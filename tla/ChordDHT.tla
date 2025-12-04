------------------------------- MODULE ChordDHT --------------------------------

EXTENDS Integers, FiniteSets

CONSTANTS
    Nodes,
    M, \* ring size = 2^M
    Keys

ASSUME
  /\ Nodes \subseteq 0..(2^M - 1)
  /\ Keys \subseteq 0..(2^M - 1)
  /\ Cardinality(Nodes) > 0

VARIABLES
    succ,     \* succ[n] = successor of node n
    pred,     \* pred[n] = predecessor of node n
    finger,   \* finger[n][i] = i-th finger table entry of n
    lookupRes \* lookupRes[k] = result of lookup for key k

vars == << succ, pred, finger, lookupRes >>

RingAdd(n, k) == (n + k) % (2 ^ M)

\* Check if k is in interval (n, s]
Between(k, n, s) ==
    IF n < s
    THEN n < k /\ k <= s
    ELSE n < k \/ k <= s

\* Check if k is in interval [n, s)
BetweenInclusive(k, n, s) ==
    IF n < s
    THEN n <= k /\ k < s
    ELSE n <= k \/ k < s

\* Find the node responsible for key k (first node >= k)
Responsible(k) ==
    LET candidates == {n \in Nodes: n >= k}
    IN IF candidates /= {}
        THEN CHOOSE n \in candidates: \A m \in candidates: n <= m
        ELSE CHOOSE n \in Nodes: \A m \in Nodes: n <= m

Init ==
    /\ succ = [n \in Nodes |-> Responsible(RingAdd(n, 1))]
    /\ pred = [n \in Nodes |->
        LET candidates == {m \in Nodes: Responsible(RingAdd(m, 1)) = n}
        IN IF candidates /= {}
            THEN CHOOSE m \in candidates: \A m2 \in candidates: m >= m2
            ELSE n]
    /\ finger = [n \in Nodes |-> [i \in 1..M |-> Responsible(RingAdd(n, 2 ^ (i - 1)))]]
    /\ lookupRes = [k \in Keys |-> Responsible(k)]

\* Node n stabilizes: checks if its successor's predecessor should be its new successor
Stabilize(n) ==
    /\ succ[n] \in Nodes
    /\ pred[succ[n]] \in Nodes
    /\ LET x == pred[succ[n]]
        IN IF x /= n /\ Between(x, n, succ[n])
            THEN succ' = [succ EXCEPT ![n] = x]
            ELSE UNCHANGED succ
    /\ UNCHANGED << pred, finger, lookupRes >>

\* Node n notifies its successor that n might be its predecessor
Notify(n) ==
    /\ succ[n] \in Nodes
    /\ LET s == succ[n]
        IN IF pred[s] = s \/ Between(n, pred[s], s)
            THEN pred' = [pred EXCEPT ![s] = n]
            ELSE UNCHANGED pred
    /\ UNCHANGED << succ, finger, lookupRes >>

\* Node n fixes i-th finger table entry
FixFinger(n, i) ==
    /\ i \in 1..M
    /\ LET target == RingAdd(n, 2 ^ (i - 1))
            closest == CHOOSE m \in Nodes:
                /\ BetweenInclusive(m, target, RingAdd(target, 2 ^ M - 1))
                /\ \A m2 \in Nodes:
                    BetweenInclusive(m2, target, RingAdd(target, 2 ^ M - 1)) => m <= m2
        IN finger' = [finger EXCEPT ![n][i] = closest]
    /\ UNCHANGED << succ, pred, lookupRes >>

\* Perform a lookup for key k starting from node n
Lookup(n, k) ==
    /\ k \in Keys
    /\ LET result == Responsible(k)
        IN lookupRes' = [lookupRes EXCEPT ![k] = result]
    /\ UNCHANGED << succ, pred, finger >>

Next ==
    \/ \E n \in Nodes: Stabilize(n)
    \/ \E n \in Nodes: Notify(n)
    \/ \E n \in Nodes, i \in 1..M: FixFinger(n, i)
    \/ \E n \in Nodes, k \in Keys: Lookup(n, k)

Spec == Init /\ [][Next]_vars

\* properties

SuccInNodes == \A n \in Nodes: succ[n] \in Nodes
PredInNodes == \A n \in Nodes: pred[n] \in Nodes

\* Finger table entries are valid nodes
FingerValid == \A n \in Nodes, i \in 1..M: finger[n][i] \in Nodes

\* Lookups return the correct responsible node
LookupCorrectness ==
    \A k \in Keys: lookupRes[k] = Responsible(k)

TypeOK ==
    /\ succ \in [Nodes -> Nodes]
    /\ pred \in [Nodes -> Nodes]
    /\ finger \in [Nodes -> [1..M -> Nodes]]
    /\ lookupRes \in [Keys -> Nodes]

\* Visualization helpers
RingView == [n \in Nodes |-> << n, succ[n] >>]
LookupView == [k \in Keys |-> << k, lookupRes[k], Responsible(k) >>]

================================================================================