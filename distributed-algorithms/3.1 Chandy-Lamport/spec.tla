----------------------------- MODULE spec -----------------------------

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Nodes, Writers, NULL

(*--algorithm spec
variables
    inputs = [n \in Nodes |-> <<>>],
    \* peers = [n \in Nodes -> { Nodes \ {n} }],    \* TODO - Define alternate peer topologies
    snapshot = [n \in Nodes |-> NULL], \* Should be a map from node to record
    complete = FALSE;

process node \in Nodes
variables
    state = 100,
    msg = NULL,
    n = 0;
begin
    Node:
        await inputs[self] /= <<>>
        msg := Head(inputs[self])
        inputs[self] := Tail(inputs[self])
        if msg.type = "Transfer" do
            \* If node is source
                \* Apply transfer
                \* Forward transfer to peer
            \* If node is target
                \* Apply transfer
        elsif msg.type = "Snapshot" do
            if snapshot[self] = NULL do
                snapshot[self] := [
                    waiting  |-> (Nodes \ {self}) \ {msg.src},
                    messages |-> <<>>,
                    state    |-> state,
                ];
                n := Cardinality(snapshot[self].waiting)
                Forward:
                    while n > 0 do
                        inputs[n
                    end while;
            else
                snapshot[self].waiting := snapshot[self].waiting \ {msg.src}
            end if;
            \* Create marker [id |-> 1]
            \* Begin recording incoming channels
            \* Send to peers
        elsif msg[type] = "Marker" do
            \* Stop recording on channel of origin
            \* Forward non-origin markers
            \* Accumulate origin markers
                \* Mark snapshot complete when origin marker is whole
        end if;
        goto Node;
end process;

process writer \in Writers
begin
    Transfer:
        while transfers /= <<>> do
            Send:
                t = Head(transfers)
                transfers := Tail(transfers)
                inputs[t.from] := Append(inputs[t[from]], t)
        end while;
end process;

process reader = "Reader"
begin
    Snapshot:
        with n \in Nodes do
            inputs[n] := Append(inputs[n], [
                type -> "snapshot",
                src -> n,
            ])
        end with;
        await \A s \in snapshot : s /= <<>>;
        \* Await completion
end process;
end algorithm;*)


================================================================================

Distributed Algorithms - 3.1 Chandy-Lamport

https://github.com/tlaplus/DrTLAPlus/tree/master/GSnapshot
https://www.youtube.com/watch?v=ao58xine3jM

https://lamport.azurewebsites.net/pubs/chandy.pdf
