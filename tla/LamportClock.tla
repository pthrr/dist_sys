----------------------------- MODULE LamportClock ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS
    \* @type: Set(Str);
    Procs

VARIABLES
    \* @type: Str -> Int;
    clock,
    \* @type: Set({from: Str, to: Str, ts: Int});
    msgs

vars == << clock, msgs >>

TypeOK ==
    /\ clock \in [Procs -> Nat]
    /\ msgs \subseteq [from: Procs, to: Procs, ts: Nat]

Init ==
    /\ clock = [p \in Procs |-> 0]
    /\ msgs = {}

Send(sender, receiver) ==
    /\ clock' = [clock EXCEPT ![sender] = @ + 1]
    /\ msgs' = msgs \union {[from |-> sender, to |-> receiver,
        ts |-> clock' [sender]]}

Receive(receiver) ==
    /\ \E m \in msgs:
        /\ m.to = receiver
        /\ clock' = [clock EXCEPT ![receiver] =
            1 + (IF clock[receiver] > m.ts
                THEN clock[receiver]
                ELSE m.ts)]
        /\ msgs' = msgs \ {m}

Internal(p) ==
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ UNCHANGED msgs

Next ==
    \/ \E s, r \in Procs: s /= r /\ Send(s, r)
    \/ \E r \in Procs: Receive(r)
    \/ \E p \in Procs: Internal(p)

Spec == Init /\ [][Next]_vars

\* properties
ClocksMonotonic == \A p \in Procs: clock[p] >= 0

MessageTimestampsValid == \A m \in msgs: m.ts > 0

\* bound state space
StateConstraint ==
    /\ \A p \in Procs: clock[p] < 6
    /\ Cardinality(msgs) < 3

================================================================================