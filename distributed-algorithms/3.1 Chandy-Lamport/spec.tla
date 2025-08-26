--------------------------------- MODULE spec ----------------------------------

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Nodes, Writers, NULL

(*--algorithm spec
variables
    network   = [n \in Nodes |-> <<>>],
    in_peers  = [n \in Nodes |-> { Nodes \ {n} }], \* TODO - Define alternate peer topologies
    out_peers = [n \in Nodes |-> { Nodes \ {n} }], \* TODO - Define alternate peer topologies
    snapshot  = [n \in Nodes |-> NULL],           \* Map from node to record
    complete  = FALSE,
    transfers = <<>>;

macro send_all(dst, msg) begin
    network := [n \in Nodes |-> IF n \in dst THEN network[n] = Append(network[n], msg) ELSE network[n]];
end macro;

process node \in Nodes
variables
    state = 100,
    msg = NULL;
begin
    Node:
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
            goto Node;
        elsif msg.type = "Snapshot" then
            Snapshot:
                if snapshot[self] = NULL then
                    snapshot[self] := [
                        waiting  |-> in_peers[self] \ {msg.src},
                        messages |-> <<>>,
                        state    |-> state
                    ];
                    msg.src := self;
                    send_all(out_peers[self] \ {msg.src}, msg);
                else
                    snapshot[self].waiting := snapshot[self].waiting \ {msg.src};
                end if;
                goto Node;
        end if;
end process;

process writer \in Writers
variables
    src \in Nodes;
    dst \in Nodes \ {src};
    t = NULL
begin
    WInit:
        transfers := Append(transfers, [type |-> "Transfer", amount |-> 10, src |-> src, dst |-> dst]);
    Transfer:
        while transfers /= <<>> do
            Send:
                t := Head(transfers);
                transfers := Tail(transfers);
                network[t.src] := Append(network[t.src], t);
        end while;
end process;

process reader = "Reader"
begin
    Snapshot:
        with n \in Nodes do
            network[n] := Append(network[n], [
                type |-> "Snapshot",
                src  |-> NULL
            ]);
        end with;
        \* await \A s \in snapshot : s /= NULL /\ s.waiting = <<>>;
end process;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "61ec2acb" /\ chksum(tla) = "d9d4ebd4")
\* Label Transfer of process node at line 31 col 17 changed to Transfer_
\* Label Snapshot of process node at line 43 col 17 changed to Snapshot_
VARIABLES network, in_peers, out_peers, snapshot, complete, transfers, pc,
    state, msg, src, dst, t

vars == << network, in_peers, out_peers, snapshot, complete, transfers, pc,
    state, msg, src, dst, t >>

ProcSet == (Nodes) \union (Writers) \union {"Reader"}

Init == (* Global variables *)
    /\ network = [n \in Nodes |-> <<>>]
    /\ in_peers = [n \in Nodes |-> {Nodes \ {n}}]
    /\ out_peers = [n \in Nodes |-> {Nodes \ {n}}]
    /\ snapshot = [n \in Nodes |-> NULL]
    /\ complete = FALSE
    /\ transfers = <<>>
    (* Process node *)
    /\ state = [self \in Nodes |-> 100]
    /\ msg = [self \in Nodes |-> NULL]
    (* Process writer *)
    /\ src \in [Writers -> Nodes]
    /\ dst \in [Writers -> Nodes \ {src[CHOOSE self \in Writers: TRUE]}]
    /\ t = [self \in Writers |-> NULL]
    /\ pc = [self \in ProcSet |-> CASE self \in Nodes -> "Node"
        [] self \in Writers -> "WInit"
        [] self = "Reader" -> "Snapshot"]

Node(self) ==
    /\ pc[self] = "Node"
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
    /\ UNCHANGED << in_peers, out_peers, snapshot, complete,
            transfers, state, src, dst, t >>

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
    /\ pc' = [pc EXCEPT ![self] = "Node"]
    /\ UNCHANGED << in_peers, out_peers, complete, transfers,
        msg, src, dst, t >>

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
            /\ network' = [n \in Nodes |-> IF n \in (out_peers[self] \ {msg' [self].src}) THEN network[n] = Append(network[n], msg' [self]) ELSE network[n]]
        ELSE
            /\ snapshot' = [snapshot EXCEPT ![self].waiting = snapshot[self].waiting \ {msg[self].src}]
            /\ UNCHANGED << network, msg >>
    /\ pc' = [pc EXCEPT ![self] = "Node"]
    /\ UNCHANGED << in_peers, out_peers, complete, transfers,
        state, src, dst, t >>

node(self) == Node(self) \/ Transfer_(self) \/ Snapshot_(self)

WInit(self) ==
    /\ pc[self] = "WInit"
    /\ transfers' = Append(transfers, [type |-> "Transfer", amount |-> 10, src |-> src[self], dst |-> dst[self]])
    /\ pc' = [pc EXCEPT ![self] = "Transfer"]
    /\ UNCHANGED << network, in_peers, out_peers, snapshot,
        complete, state, msg, src, dst, t >>

Transfer(self) ==
    /\ pc[self] = "Transfer"
    /\ IF transfers /= <<>>
        THEN
            /\ pc' = [pc EXCEPT ![self] = "Send"]
        ELSE
            /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED << network, in_peers, out_peers, snapshot,
            complete, transfers, state, msg, src, dst, t >>

Send(self) ==
    /\ pc[self] = "Send"
    /\ t' = [t EXCEPT ![self] = Head(transfers)]
    /\ transfers' = Tail(transfers)
    /\ network' = [network EXCEPT ![t' [self].src] = Append(network[t' [self].src], t' [self])]
    /\ pc' = [pc EXCEPT ![self] = "Transfer"]
    /\ UNCHANGED << in_peers, out_peers, snapshot, complete, state,
        msg, src, dst >>

writer(self) == WInit(self) \/ Transfer(self) \/ Send(self)

Snapshot ==
    /\ pc["Reader"] = "Snapshot"
    /\ \E n \in Nodes:
        network' = [network EXCEPT ![n] = Append(network[n], [
                type |-> "Snapshot",
                src |-> NULL
            ])]
    /\ pc' = [pc EXCEPT !["Reader"] = "Done"]
    /\ UNCHANGED << in_peers, out_peers, snapshot, complete, transfers,
        state, msg, src, dst, t >>

reader == Snapshot

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating ==
    /\ \A self \in ProcSet: pc[self] = "Done"
    /\ UNCHANGED vars

Next == reader
\/ (\E self \in Nodes: node(self))
\/ (\E self \in Writers: writer(self))
\/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

================================================================================

Distributed Algorithms - 3.1 Chandy-Lamport

https://github.com/tlaplus/DrTLAPlus/tree/master/GSnapshot
https://www.youtube.com/watch?v=ao58xine3jM

https://lamport.azurewebsites.net/pubs/chandy.pdf
