------------------------------ MODULE VectorClock ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS
    \* @type: Set(Str);
    Procs

VARIABLES
    \* @type: Str -> (Str -> Int);
    vclock,
    \* @type: Set({from: Str, to: Str, vc: Str -> Int});
    msgs

vars == << vclock, msgs >>

TypeOK ==
    /\ vclock \in [Procs -> [Procs -> Nat]]
    /\ msgs \subseteq [from: Procs, to: Procs, vc: [Procs -> Nat]]

Init ==
    /\ vclock = [p \in Procs |-> [q \in Procs |-> 0]]
    /\ msgs = {}

Send(sender, receiver) ==
    /\ vclock' = [vclock EXCEPT ![sender][sender] = @ + 1]
    /\ msgs' = msgs \union {[from |-> sender, to |-> receiver,
        vc |-> vclock' [sender]]}

Receive(receiver) ==
    /\ \E m \in msgs:
        /\ m.to = receiver
        /\ vclock' = [vclock EXCEPT ![receiver] =
            [q \in Procs |->
                IF q = receiver
                THEN vclock[receiver][q] + 1
                ELSE (IF vclock[receiver][q] > m.vc[q]
                    THEN vclock[receiver][q]
                    ELSE m.vc[q])]]
        /\ msgs' = msgs \ {m}

Internal(p) ==
    /\ vclock' = [vclock EXCEPT ![p][p] = @ + 1]
    /\ UNCHANGED msgs

Next ==
    \/ \E s, r \in Procs: s /= r /\ Send(s, r)
    \/ \E r \in Procs: Receive(r)
    \/ \E p \in Procs: Internal(p)

Spec == Init /\ [][Next]_vars

\* properties
VectorClocksMonotonic ==
    \A p, q \in Procs: vclock[p][q] >= 0

SelfClockConsistency ==
    \A p \in Procs: vclock[p][p] >= 0

\* Vector clock causality property
CausalityProperty ==
    \A m \in msgs: \A q \in Procs: vclock[m.from][q] >= m.vc[q]

\* bound state space
StateConstraint ==
    /\ \A p, q \in Procs: vclock[p][q] < 6
    /\ Cardinality(msgs) < 4

================================================================================