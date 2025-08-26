--------------------------------- MODULE spec ----------------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Accounts, Transfers, Readers, NULL

Readers_ == Permutations(Readers)

ReduceSet( op(_, _) , set, acc) ==
    LET f[s \in SUBSET set] == \* here's where the magic is
        IF s = {} THEN acc
        ELSE LET x == CHOOSE x \in s: TRUE
            IN op(x, f[s \ {x}])
    IN f[set]
ReduceSeq( op(_, _) , seq, acc) ==
    ReduceSet( LAMBDA i, a: op(seq[i], a) , DOMAIN seq, acc)
SumSnapshotItem(s) == s.state + ReduceSeq( LAMBDA m, acc: m.amount + acc , s.messages, 0)
SumSnapshot(snapshot) ==
    ReduceSet( LAMBDA n, acc: SumSnapshotItem(snapshot[n]) + acc , Accounts, 0)

(*--algorithm spec
variables
    network   = [n \in Accounts |-> <<>>],
    in_peers  = [n \in Accounts |-> Accounts \ {n}], \* TODO - Define alternate peer topologies
    out_peers = [n \in Accounts |-> Accounts \ {n}], \* TODO - Define alternate peer topologies
    snapshot  = [n \in Accounts |-> NULL];

define
    SnapshotFinished == \A s \in DOMAIN snapshot: snapshot[s] /= NULL /\ snapshot[s].waiting = {}
    SnapshotCorrect == (~SnapshotFinished) \/ (SumSnapshot(snapshot) = Cardinality(Accounts) * 100)
end define;

macro broadcast(dst, msg) begin
    network := [n \in DOMAIN network |-> IF n \in dst THEN Append(network[n], msg) ELSE network[n]];
end macro;

fair process node \in Accounts
variables
    state = 100,
    msg = NULL;
begin
    NodeWait:
        await network[self] /= <<>>;
        msg := Head(network[self]);
        network[self] := Tail(network[self]);
        if msg.type = "Transfer" then
            Transfer:
                if msg.src = self then
                    state := state - msg.amount;
                    network[msg.dst] := Append(@, msg);
                else
                    if snapshot[self] /= NULL /\ msg.src \in snapshot[self].waiting then
                        snapshot[self].messages := Append(@, msg);
                    end if;
                    state := state + msg.amount;
                end if;
                goto NodeWait;
        elsif msg.type = "Snapshot" then
            Snapshot:
                if snapshot[self] = NULL then
                    snapshot[self] := [
                        waiting  |-> in_peers[self] \ {msg.src},
                        messages |-> <<>>,
                        state    |-> state
                    ];
                    msg.src := self;
                    broadcast(out_peers[self], msg);
                else
                    snapshot[self].waiting := snapshot[self].waiting \ {msg.src};
                end if;
                goto NodeWait;
        end if;
end process;

fair process transfer \in Transfers
variables
    src = NULL,
    dst = NULL
begin
    Transfer:
        src := src \in Accounts;
        dst := dst \in Accounts \ {src};
        network[src] := Append(@, [type |-> "Transfer", amount |-> 10, src |-> src, dst |-> dst]);
end process;

fair process reader \in SUBSET Readers
begin
    Snapshot:
        with n \in Accounts do
            network[n] := Append(@, [type |-> "Snapshot",src  |-> NULL]);
        end with;
end process;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "6df3191c" /\ chksum(tla) = "aa7d8c10")
\* Label Transfer of process node at line 48 col 17 changed to Transfer_
\* Label Snapshot of process node at line 60 col 17 changed to Snapshot_
VARIABLES network, in_peers, out_peers, snapshot, pc

(* define statement *)
SnapshotFinished == \A s \in DOMAIN snapshot: snapshot[s] /= NULL /\ snapshot[s].waiting = {}
SnapshotCorrect == (~SnapshotFinished) \/ (SumSnapshot(snapshot) = Cardinality(Accounts) * 100)

VARIABLES state, msg, src, dst

vars == << network, in_peers, out_peers, snapshot, pc, state, msg, src, dst
>>

ProcSet == (Accounts) \union (Transfers) \union (SUBSET Readers)

Init == (* Global variables *)
    /\ network = [n \in Accounts |-> <<>>]
    /\ in_peers = [n \in Accounts |-> Accounts \ {n}]
    /\ out_peers = [n \in Accounts |-> Accounts \ {n}]
    /\ snapshot = [n \in Accounts |-> NULL]
    (* Process node *)
    /\ state = [self \in Accounts |-> 100]
    /\ msg = [self \in Accounts |-> NULL]
    (* Process transfer *)
    /\ src = [self \in Transfers |-> NULL]
    /\ dst = [self \in Transfers |-> NULL]
    /\ pc = [self \in ProcSet |-> CASE self \in Accounts -> "NodeWait"
        [] self \in Transfers -> "Transfer"
        [] self \in SUBSET Readers -> "Snapshot"]

NodeWait(self) ==
    /\ pc[self] = "NodeWait"
    /\ network[self] /= <<>>
    /\ msg' = [msg EXCEPT ![self] = Head(network[self])]
    /\ network' = [network EXCEPT ![self] = Tail(network[self])]
    /\ IF msg' [self].type = "Transfer"
        THEN
            /\ pc' = [pc EXCEPT ![self] = "Transfer_"]
        ELSE
            /\ IF msg' [self].type = "Snapshot"
                THEN
                    /\ pc' = [pc EXCEPT ![self] = "Snapshot_"]
                ELSE
                    /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED << in_peers, out_peers, snapshot, state, src,
            dst >>

Transfer_(self) ==
    /\ pc[self] = "Transfer_"
    /\ IF msg[self].src = self
        THEN
            /\ state' = [state EXCEPT ![self] = state[self] - msg[self].amount]
            /\ network' = [network EXCEPT ![msg[self].dst] = Append(@, msg[self])]
            /\ UNCHANGED snapshot
        ELSE
            /\ IF snapshot[self] /= NULL /\ msg[self].src \in snapshot[self].waiting
                THEN
                    /\ snapshot' = [snapshot EXCEPT ![self].messages = Append(@, msg[self])]
                ELSE
                    /\ TRUE
                    /\ UNCHANGED snapshot
            /\ state' = [state EXCEPT ![self] = state[self] + msg[self].amount]
            /\ UNCHANGED network
    /\ pc' = [pc EXCEPT ![self] = "NodeWait"]
    /\ UNCHANGED << in_peers, out_peers, msg, src, dst >>

Snapshot_(self) ==
    /\ pc[self] = "Snapshot_"
    /\ IF snapshot[self] = NULL
        THEN
            /\ snapshot' = [snapshot EXCEPT ![self] = [
                    waiting |-> in_peers[self] \ {msg[self].src},
                    messages |-> <<>>,
                    state |-> state[self]
                ]]
            /\ msg' = [msg EXCEPT ![self].src = self]
            /\ network' = [n \in DOMAIN network |-> IF n \in (out_peers[self]) THEN Append(network[n], msg' [self]) ELSE network[n]]
        ELSE
            /\ snapshot' = [snapshot EXCEPT ![self].waiting = snapshot[self].waiting \ {msg[self].src}]
            /\ UNCHANGED << network, msg >>
    /\ pc' = [pc EXCEPT ![self] = "NodeWait"]
    /\ UNCHANGED << in_peers, out_peers, state, src, dst >>

node(self) == NodeWait(self) \/ Transfer_(self) \/ Snapshot_(self)

Transfer(self) ==
    /\ pc[self] = "Transfer"
    /\ src' = [src EXCEPT ![self] = src[self] \in Accounts]
    /\ dst' = [dst EXCEPT ![self] = dst[self] \in Accounts \ {src' [self]}]
    /\ network' = [network EXCEPT ![src' [self]] = Append(@, [type |-> "Transfer", amount |-> 10, src |-> src' [self], dst |-> dst' [self]])]
    /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED << in_peers, out_peers, snapshot, state, msg >>

transfer(self) == Transfer(self)

Snapshot(self) ==
    /\ pc[self] = "Snapshot"
    /\ \E n \in Accounts:
        network' = [network EXCEPT ![n] = Append(@, [type |-> "Snapshot", src |-> NULL])]
    /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED << in_peers, out_peers, snapshot, state, msg,
        src, dst >>

reader(self) == Snapshot(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating ==
    /\ \A self \in ProcSet: pc[self] = "Done"
    /\ UNCHANGED vars

Next == (\E self \in Accounts: node(self))
\/ (\E self \in Transfers: transfer(self))
\/ (\E self \in SUBSET Readers: reader(self))
\/ Terminating

Spec ==
    /\ Init /\ [][Next]_vars
    /\ \A self \in Accounts: WF_vars(node(self))
    /\ \A self \in Transfers: WF_vars(transfer(self))
    /\ \A self \in SUBSET Readers: WF_vars(reader(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

SnapshotTerminates == <>(SnapshotFinished)

================================================================================

Distributed Algorithms - 3.1 Chandy-Lamport

https://github.com/tlaplus/DrTLAPlus/tree/master/GSnapshot
https://www.youtube.com/watch?v=ao58xine3jM

https://lamport.azurewebsites.net/pubs/chandy.pdf
