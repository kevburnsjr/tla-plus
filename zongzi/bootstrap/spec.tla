--------------------------------- MODULE spec ----------------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS Accounts, Readers, Transfers, NULL

Symmetry == Permutations(Readers)
\union Permutations(Transfers)

(*--algorithm spec
variables
    network   = [n \in Accounts |-> <<>>],
    in_peers  = [n \in Accounts |-> Accounts \ {n}], \* TODO - Define alternate peer topologies
    out_peers = [n \in Accounts |-> Accounts \ {n}], \* TODO - Define alternate peer topologies
    snapshot  = [n \in Accounts |-> NULL];

define
    SnapshotFinished == \A s \in DOMAIN snapshot: snapshot[s] /= NULL /\ snapshot[s].waiting = {}
end define;

macro broadcast(dst, msg) begin
    network := [n \in DOMAIN network |-> IF n \in dst THEN Append(network[n], msg) ELSE network[n]];
end macro;

fair process account \in Accounts
variables
    balance = 100,
    msg = NULL;
begin
    Wait:
        await network[self] /= <<>>;
        msg := Head(network[self]);
        network[self] := Tail(network[self]);
        if msg.type = "Transfer" then
            Transfer:
                if msg.src = self then
                    balance := balance - msg.amount;
                    broadcast({msg.dst}, msg)
                else
                    balance := balance + msg.amount;
                    if snapshot[self] /= NULL /\ msg.src \in snapshot[self].waiting then
                        snapshot[self].messages := Append(@, msg);
                    end if;
                end if;
                goto Wait;
        elsif msg.type = "Snapshot" then
            Snapshot:
                if snapshot[self] = NULL then
                    snapshot[self] := [
                        waiting  |-> in_peers[self] \ {msg.src},
                        messages |-> <<>>,
                        balance  |-> balance
                    ];
                    msg.src := self;
                    broadcast(out_peers[self], msg);
                else
                    snapshot[self].waiting := snapshot[self].waiting \ {msg.src};
                end if;
                goto Wait;
        end if;
end process;

fair process transfer \in Transfers
variables
    src = NULL,
    dst = NULL
begin
    StartTransfer:
        src := src \in Accounts;
        dst := dst \in Accounts \ {src};
        network[src] := Append(@, [type |-> "Transfer", amount |-> 10, src |-> src, dst |-> dst]);
end process;

fair process reader \in SUBSET Readers
begin
    StartSnapshot:
        with n \in Accounts do
            network[n] := Append(@, [type |-> "Snapshot", src  |-> NULL]);
        end with;
end process;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "6ed0139" /\ chksum(tla) = "33e1e3c5")
VARIABLES network, in_peers, out_peers, snapshot, pc

(* define statement *)
SnapshotFinished == \A s \in DOMAIN snapshot: snapshot[s] /= NULL /\ snapshot[s].waiting = {}

VARIABLES balance, msg, src, dst

vars == << network, in_peers, out_peers, snapshot, pc, balance, msg, src, dst
>>

ProcSet == (Accounts) \union (Transfers) \union (SUBSET Readers)

Init == (* Global variables *)
    /\ network = [n \in Accounts |-> <<>>]
    /\ in_peers = [n \in Accounts |-> Accounts \ {n}]
    /\ out_peers = [n \in Accounts |-> Accounts \ {n}]
    /\ snapshot = [n \in Accounts |-> NULL]
    (* Process account *)
    /\ balance = [self \in Accounts |-> 100]
    /\ msg = [self \in Accounts |-> NULL]
    (* Process transfer *)
    /\ src = [self \in Transfers |-> NULL]
    /\ dst = [self \in Transfers |-> NULL]
    /\ pc = [self \in ProcSet |-> CASE self \in Accounts -> "Wait"
        [] self \in Transfers -> "StartTransfer"
        [] self \in SUBSET Readers -> "StartSnapshot"]

Wait(self) ==
    /\ pc[self] = "Wait"
    /\ network[self] /= <<>>
    /\ msg' = [msg EXCEPT ![self] = Head(network[self])]
    /\ network' = [network EXCEPT ![self] = Tail(network[self])]
    /\ IF msg' [self].type = "Transfer"
        THEN
            /\ pc' = [pc EXCEPT ![self] = "Transfer"]
        ELSE
            /\ IF msg' [self].type = "Snapshot"
                THEN
                    /\ pc' = [pc EXCEPT ![self] = "Snapshot"]
                ELSE
                    /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED << in_peers, out_peers, snapshot, balance, src, dst >>

Transfer(self) ==
    /\ pc[self] = "Transfer"
    /\ IF msg[self].src = self
        THEN
            /\ balance' = [balance EXCEPT ![self] = balance[self] - msg[self].amount]
            /\ network' = [n \in DOMAIN network |-> IF n \in ({msg[self].dst}) THEN Append(network[n], msg[self]) ELSE network[n]]
            /\ UNCHANGED snapshot
        ELSE
            /\ balance' = [balance EXCEPT ![self] = balance[self] + msg[self].amount]
            /\ IF snapshot[self] /= NULL /\ msg[self].src \in snapshot[self].waiting
                THEN
                    /\ snapshot' = [snapshot EXCEPT ![self].messages = Append(@, msg[self])]
                ELSE
                    /\ TRUE
                    /\ UNCHANGED snapshot
            /\ UNCHANGED network
    /\ pc' = [pc EXCEPT ![self] = "Wait"]
    /\ UNCHANGED << in_peers, out_peers, msg, src, dst >>

Snapshot(self) ==
    /\ pc[self] = "Snapshot"
    /\ IF snapshot[self] = NULL
        THEN
            /\ snapshot' = [snapshot EXCEPT ![self] = [
                    waiting |-> in_peers[self] \ {msg[self].src},
                    messages |-> <<>>,
                    balance |-> balance[self]
                ]]
            /\ msg' = [msg EXCEPT ![self].src = self]
            /\ network' = [n \in DOMAIN network |-> IF n \in (out_peers[self]) THEN Append(network[n], msg' [self]) ELSE network[n]]
        ELSE
            /\ snapshot' = [snapshot EXCEPT ![self].waiting = snapshot[self].waiting \ {msg[self].src}]
            /\ UNCHANGED << network, msg >>
    /\ pc' = [pc EXCEPT ![self] = "Wait"]
    /\ UNCHANGED << in_peers, out_peers, balance, src, dst >>

account(self) == Wait(self) \/ Transfer(self) \/ Snapshot(self)

StartTransfer(self) ==
    /\ pc[self] = "StartTransfer"
    /\ src' = [src EXCEPT ![self] = src[self] \in Accounts]
    /\ dst' = [dst EXCEPT ![self] = dst[self] \in Accounts \ {src' [self]}]
    /\ network' = [network EXCEPT ![src' [self]] = Append(@, [type |-> "Transfer", amount |-> 10, src |-> src' [self], dst |-> dst' [self]])]
    /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED << in_peers, out_peers, snapshot, balance,
        msg >>

transfer(self) == StartTransfer(self)

StartSnapshot(self) ==
    /\ pc[self] = "StartSnapshot"
    /\ \E n \in Accounts:
        network' = [network EXCEPT ![n] = Append(@, [type |-> "Snapshot", src |-> NULL])]
    /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED << in_peers, out_peers, snapshot, balance,
        msg, src, dst >>

reader(self) == StartSnapshot(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating ==
    /\ \A self \in ProcSet: pc[self] = "Done"
    /\ UNCHANGED vars

Next == (\E self \in Accounts: account(self))
\/ (\E self \in Transfers: transfer(self))
\/ (\E self \in SUBSET Readers: reader(self))
\/ Terminating

Spec ==
    /\ Init /\ [][Next]_vars
    /\ \A self \in Accounts: WF_vars(account(self))
    /\ \A self \in Transfers: WF_vars(transfer(self))
    /\ \A self \in SUBSET Readers: WF_vars(reader(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* util operations
ReduceSet( op(_, _) , set, acc) ==
    LET f[s \in SUBSET set] ==
        IF s = {} THEN acc
        ELSE LET x == CHOOSE x \in s: TRUE
            IN op(x, f[s \ {x}])
    IN f[set]
ReduceSeq( op(_, _) , seq, acc) ==
    ReduceSet( LAMBDA i, a: op(seq[i], a) , DOMAIN seq, acc)
SumSnapshotItem(si) == 
    si.balance + ReduceSeq( LAMBDA m, acc: m.amount + acc , si.messages, 0)
SumSnapshot(s) ==
    ReduceSet( LAMBDA acct, acc: SumSnapshotItem(s[acct]) + acc , Accounts, 0)

SnapshotCorrect == (~SnapshotFinished) \/ (SumSnapshot(snapshot) = Cardinality(Accounts) * 100)

SnapshotTerminates == <>(SnapshotFinished)

================================================================================

Distributed Algorithms - 3.1 Chandy-Lamport

https://github.com/tlaplus/DrTLAPlus/tree/master/GSnapshot
https://www.youtube.com/watch?v=ao58xine3jM

https://lamport.azurewebsites.net/pubs/chandy.pdf
