--------------------------------- MODULE spec ----------------------------------

EXTENDS Integers, TLC, Sequences, FiniteSets
CONSTANTS Leases, Clients, Keys, NULL

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
    UnRevokedLeases == {l \in Leases: leaseExp[l] # 0}
    AvailableLeases == {l \in Leases: leaseExp[l] = NULL}
    AvailableKeys   == {k \in Keys: kvstore[k] = NULL}
end define;

macro revoke(l) begin
    kvstore := [b \in leaseKeys[l] |-> NULL] @@ kvstore;
    leaseKeys[l] := {};
    leaseExp[l] := NULL;
    leaseClients[l] := NULL;
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
            with l \in clientLeases[self] do
                if refreshes[l] > 5 then
                    clientLeases[self] := clientLeases[self] \ {l};
                    leaseClients[l] := NULL;
                else
                    leaseExp[l] := epoch + 10;
                    refreshes[l] := refreshes[l] + 1;
                end if;
            end with;
        or
            \* Lease Revoke
            with l \in clientLeases[self] do
                revoke(l);
                clientLeases[self] := clientLeases[self] \ {l};
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
        expired := {l \in Leases: leaseExp[l] = epoch};
        kvstore := [l \in UNION {leaseKeys[l]: l \in expired} |-> NULL] @@ kvstore;
        clientLeases := [c \in Clients |-> clientLeases[c] \ {expired}] @@ clientLeases;
        leaseClients := [l \in expired |-> NULL] @@ leaseClients;
        leaseKeys := [l \in expired |-> {}] @@ leaseKeys;
        leaseExp := [l \in expired |-> NULL] @@ leaseExp;
        goto Tick;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "186f05ae" /\ chksum(tla) = "c06acaed")
VARIABLES kvstore, leaseKeys, leaseExp, refreshes, leaseClients, clientLeases,
    epoch, pc

(* define statement *)
UnRevokedLeases == {l \in Leases: leaseExp[l] /= 0}
AvailableLeases == {l \in Leases: leaseExp[l] = NULL}
AvailableKeys == {k \in Keys: kvstore[k] = NULL}

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
                /\ \E l \in clientLeases[self]:
                    IF refreshes[l] > 5
                    THEN
                        /\ clientLeases' = [clientLeases EXCEPT ![self] = clientLeases[self] \ {l}]
                        /\ leaseClients' = [leaseClients EXCEPT ![l] = NULL]
                        /\ UNCHANGED << leaseExp, refreshes >>
                    ELSE
                        /\ leaseExp' = [leaseExp EXCEPT ![l] = epoch + 10]
                        /\ refreshes' = [refreshes EXCEPT ![l] = refreshes[l] + 1]
                        /\ UNCHANGED << leaseClients, clientLeases >>
                /\ UNCHANGED << kvstore, leaseKeys >>
        \/
                /\ \E l \in clientLeases[self]:
                    /\ kvstore' = [b \in leaseKeys[l] |-> NULL] @@ kvstore
                    /\ leaseKeys' = [leaseKeys EXCEPT ![l] = {}]
                    /\ leaseExp' = [leaseExp EXCEPT ![l] = NULL]
                    /\ leaseClients' = [leaseClients EXCEPT ![l] = NULL]
                    /\ clientLeases' = [clientLeases EXCEPT ![self] = clientLeases[self] \ {l}]
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
    /\ expired' = {l \in Leases: leaseExp[l] = epoch'}
    /\ kvstore' = [l \in UNION {leaseKeys[l]: l \in expired'} |-> NULL] @@ kvstore
    /\ clientLeases' = [c \in Clients |-> clientLeases[c] \ {expired'}] @@ clientLeases
    /\ leaseClients' = [l \in expired' |-> NULL] @@ leaseClients
    /\ leaseKeys' = [l \in expired' |-> {}] @@ leaseKeys
    /\ leaseExp' = [l \in expired' |-> NULL] @@ leaseExp
    /\ pc' = [pc EXCEPT !["tick"] = "Tick"]
    /\ UNCHANGED << refreshes, wants >>

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