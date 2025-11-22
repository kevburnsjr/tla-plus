--------------------------------- MODULE spec ----------------------------------

EXTENDS Integers, TLC, Sequences, FiniteSets
CONSTANTS Leases, Clients, Keys, NULL, MaxRefresh

(*--algorithm spec
variables
    kvstore      = [k \in Keys |-> NULL],
    leaseKeys    = [l \in Leases |-> {}],
    leaseExp     = [l \in Leases |-> NULL],
    refreshes    = [l \in Leases |-> 0],
    leaseClients = [l \in Leases |-> NULL],
    clientLeases = [c \in Clients |-> {}],
    epoch        = 0;

define
    ActiveLeases    == {l \in Leases: leaseClients[l] # NULL}
    AvailableLeases == {l \in Leases: leaseExp[l] = NULL}
    AvailableKeys   == {k \in Keys: kvstore[k] = NULL}
    RefreshableLeases(c) == {l \in clientLeases[c]: refreshes[l] < MaxRefresh}
end define;

macro revoke(expired) begin
    kvstore := [l \in UNION {leaseKeys[l]: l \in expired} |-> NULL] @@ kvstore;
    clientLeases := [c \in Clients |-> clientLeases[c] \ {expired}] @@ clientLeases;
    leaseClients := [l \in expired |-> NULL] @@ leaseClients;
    leaseKeys := [l \in expired |-> {}] @@ leaseKeys;
    \* Note: resetting leaseExp to 0 rather than NULL prevents leases from being reacquired
    leaseExp := [l \in expired |-> 0] @@ leaseExp;
end macro;

fair process client \in Clients
variables
    wants \in SUBSET Keys;
begin
    Client:
        either
            \* Key claim
            with l \in clientLeases[self] do
                with k \in AvailableKeys \intersect wants do
                    kvstore[k] := l;
                    leaseKeys[l] := leaseKeys[l] \union {k};
                end with;
            end with;
        or
            \* Lease Acquire
            with l \in AvailableLeases do
                clientLeases[self] := clientLeases[self] \union {l};
                leaseClients[l] := self;
                leaseExp[l] := epoch + 10;
            end with;
        or
            \* Lease Refresh
            with l \in RefreshableLeases(self) do
                leaseExp[l] := epoch + 10;
                refreshes[l] := refreshes[l] + 1;
            end with;
        or
            \* Lease Revoke
            with l1 \in clientLeases[self] do
                revoke({l1});
            end with;
        end either;
        if clientLeases[self] # {} \/ wants # {} then
            goto Client;
        end if;
end process;

fair process tick = "tick"
variables
    expired = {};
begin
    Tick:
        epoch := epoch + 1;
        revoke({l \in Leases: leaseExp[l] = epoch});
        if AvailableLeases # {} /\ ActiveLeases # {} then
            goto Tick;
        end if;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "bf2156bb" /\ chksum(tla) = "8b7bbe4e")
VARIABLES kvstore, leaseKeys, leaseExp, refreshes, leaseClients, clientLeases,
    epoch, pc

(* define statement *)
ActiveLeases == {l \in Leases: leaseClients[l] /= NULL}
AvailableLeases == {l \in Leases: leaseExp[l] = NULL}
AvailableKeys == {k \in Keys: kvstore[k] = NULL}
RefreshableLeases(c) == {l \in clientLeases[c]: refreshes[l] < MaxRefresh}

VARIABLES wants, expired

vars == << kvstore, leaseKeys, leaseExp, refreshes, leaseClients,
    clientLeases, epoch, pc, wants, expired >>

ProcSet == (Clients) \union {"tick"}

Init == (* Global variables *)
    /\ kvstore = [k \in Keys |-> NULL]
    /\ leaseKeys = [l \in Leases |-> {}]
    /\ leaseExp = [l \in Leases |-> NULL]
    /\ refreshes = [l \in Leases |-> 0]
    /\ leaseClients = [l \in Leases |-> NULL]
    /\ clientLeases = [c \in Clients |-> {}]
    /\ epoch = 0
    (* Process client *)
    /\ wants \in [Clients -> SUBSET Keys]
    (* Process tick *)
    /\ expired = {}
    /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "Client"
        [] self = "tick" -> "Tick"]

Client(self) ==
    /\ pc[self] = "Client"
    /\
        \/
            /\ \E l \in clientLeases[self]:
                \E k \in AvailableKeys \intersect wants[self]:
                    /\ kvstore' = [kvstore EXCEPT ![k] = l]
                    /\ leaseKeys' = [leaseKeys EXCEPT ![l] = leaseKeys[l] \union {k}]
            /\ UNCHANGED << leaseExp, refreshes, leaseClients, clientLeases >>
        \/
                /\ \E l \in AvailableLeases:
                    /\ clientLeases' = [clientLeases EXCEPT ![self] = clientLeases[self] \union {l}]
                    /\ leaseClients' = [leaseClients EXCEPT ![l] = self]
                    /\ leaseExp' = [leaseExp EXCEPT ![l] = epoch + 10]
                /\ UNCHANGED << kvstore, leaseKeys, refreshes >>
        \/
                /\ \E l \in RefreshableLeases(self):
                    /\ leaseExp' = [leaseExp EXCEPT ![l] = epoch + 10]
                    /\ refreshes' = [refreshes EXCEPT ![l] = refreshes[l] + 1]
                /\ UNCHANGED << kvstore, leaseKeys, leaseClients, clientLeases >>
        \/
                /\ \E l1 \in clientLeases[self]:
                    /\ kvstore' = [l \in UNION {leaseKeys[l]: l \in ({l1})} |-> NULL] @@ kvstore
                    /\ clientLeases' = [c \in Clients |-> clientLeases[c] \ {({l1})}] @@ clientLeases
                    /\ leaseClients' = [l \in ({l1}) |-> NULL] @@ leaseClients
                    /\ leaseKeys' = [l \in ({l1}) |-> {}] @@ leaseKeys
                    /\ leaseExp' = [l \in ({l1}) |-> 0] @@ leaseExp
                /\ UNCHANGED refreshes
    /\ IF clientLeases' [self] /= {} \/ wants[self] /= {}
        THEN
            /\ pc' = [pc EXCEPT ![self] = "Client"]
        ELSE
            /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED << epoch, wants, expired >>

client(self) == Client(self)

Tick ==
    /\ pc["tick"] = "Tick"
    /\ epoch' = epoch + 1
    /\ kvstore' = [l \in UNION {leaseKeys[l]: l \in ({l \in Leases: leaseExp[l] = epoch'})} |-> NULL] @@ kvstore
    /\ clientLeases' = [c \in Clients |-> clientLeases[c] \ {({l \in Leases: leaseExp[l] = epoch'})}] @@ clientLeases
    /\ leaseClients' = [l \in ({l \in Leases: leaseExp[l] = epoch'}) |-> NULL] @@ leaseClients
    /\ leaseKeys' = [l \in ({l \in Leases: leaseExp[l] = epoch'}) |-> {}] @@ leaseKeys
    /\ leaseExp' = [l \in ({l \in Leases: leaseExp[l] = epoch'}) |-> 0] @@ leaseExp
    /\ IF AvailableLeases /= {} /\ ActiveLeases /= {}
        THEN
            /\ pc' = [pc EXCEPT !["tick"] = "Tick"]
        ELSE
            /\ pc' = [pc EXCEPT !["tick"] = "Done"]
    /\ UNCHANGED << refreshes, wants, expired >>

tick == Tick

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating ==
    /\ \A self \in ProcSet: pc[self] = "Done"
    /\ UNCHANGED vars

Next == tick
\/ (\E self \in Clients: client(self))
\/ Terminating

Spec ==
    /\ Init /\ [][Next]_vars
    /\ \A self \in Clients: WF_vars(client(self))
    /\ WF_vars(tick)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

================================================================================