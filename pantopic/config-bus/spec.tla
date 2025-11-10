--------------------------------- MODULE spec ----------------------------------

EXTENDS Integers, TLC, Sequences, FiniteSets
CONSTANTS Leases, Clients, Keys, NULL

(*--algorithm spec
variables
    kvstore   = [k \in Keys |-> NULL],
    leaseKeys = [b \in Leases |-> {}],
    leaseExp  = [b \in Leases |-> NULL],
    epoch     = 0;

define
    AvailableLeases == {l \in Leases: leaseExp[l] = NULL}
    AvailableKeys   == {k \in Keys: kvstore[k] = NULL}
end define;

macro revoke(l) begin
    kvstore := [b \in leaseKeys[l] |-> NULL] @@ kvstore;
    leaseKeys[l] := {};
    leaseExp[l] := 0;
end macro;

fair process client \in Clients
variables
    leases = {},
    wants \in SUBSET Keys;
begin
    Client:
        either
            \* Key claim
            with l \in leases do
                with k \in AvailableKeys \intersect wants do
                    kvstore[k] := l;
                    leaseKeys[l] := leaseKeys[l] \union {k};
                end with;
            end with;
        or
            \* Lease Acquire
            with l \in AvailableLeases do
                leases := leases \union {l};
                leaseExp[l] := epoch + 10;
            end with;
        or
            \* Lease Refresh
            with l \in leases do
                leaseExp[l] := epoch + 10;
            end with;
        or
            \* Lease Revoke
            with l \in leases do
                revoke(l);
            end with;
        or
            skip;
        end either;
        goto Client;
end process;

fair process tick = "tick"
variables
    expired = {};
begin
    Tick:
        epoch := epoch + 1;
        expired := {l \in Leases: leaseExp[l] = epoch};
        kvstore := [l \in UNION {leaseKeys[l]: l \in expired} |-> NULL] @@ kvstore;
        leaseKeys := [l \in expired |-> {}] @@ leaseKeys;
        leaseExp := [l \in expired |-> 0] @@ leaseExp;
        goto Tick;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "3e93225a" /\ chksum(tla) = "ad37305b")
VARIABLES kvstore, leaseKeys, leaseExp, epoch, pc

(* define statement *)
AvailableLeases == {l \in Leases: leaseExp[l] = NULL}
AvailableKeys == {k \in Keys: kvstore[k] = NULL}

VARIABLES leases, wants, expired

vars == << kvstore, leaseKeys, leaseExp, epoch, pc, leases, wants, expired >>

ProcSet == (Clients) \union {"tick"}

Init == (* Global variables *)
    /\ kvstore = [k \in Keys |-> NULL]
    /\ leaseKeys = [b \in Leases |-> {}]
    /\ leaseExp = [b \in Leases |-> NULL]
    /\ epoch = 0
    (* Process client *)
    /\ leases = [self \in Clients |-> {}]
    /\ wants \in [Clients -> SUBSET Keys]
    (* Process tick *)
    /\ expired = {}
    /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "Client"
        [] self = "tick" -> "Tick"]

Client(self) ==
    /\ pc[self] = "Client"
    /\
        \/
            /\ \E l \in leases[self]:
                \E k \in AvailableKeys \intersect wants[self]:
                    /\ kvstore' = [kvstore EXCEPT ![k] = l]
                    /\ leaseKeys' = [leaseKeys EXCEPT ![l] = leaseKeys[l] \union {k}]
            /\ UNCHANGED << leaseExp, leases >>
        \/
                /\ \E l \in AvailableLeases:
                    /\ leases' = [leases EXCEPT ![self] = leases[self] \union {l}]
                    /\ leaseExp' = [leaseExp EXCEPT ![l] = epoch + 10]
                /\ UNCHANGED << kvstore, leaseKeys >>
        \/
                /\ \E l \in leases[self]:
                    leaseExp' = [leaseExp EXCEPT ![l] = epoch + 10]
                /\ UNCHANGED << kvstore, leaseKeys, leases >>
        \/
                /\ \E l \in leases[self]:
                    /\ kvstore' = [b \in leaseKeys[l] |-> NULL] @@ kvstore
                    /\ leaseKeys' = [leaseKeys EXCEPT ![l] = {}]
                    /\ leaseExp' = [leaseExp EXCEPT ![l] = 0]
                /\ UNCHANGED leases
        \/
                /\ TRUE
                /\ UNCHANGED << kvstore, leaseKeys, leaseExp, leases >>
    /\ pc' = [pc EXCEPT ![self] = "Client"]
    /\ UNCHANGED << epoch, wants, expired >>

client(self) == Client(self)

Tick ==
    /\ pc["tick"] = "Tick"
    /\ epoch' = epoch + 1
    /\ expired' = {l \in Leases: leaseExp[l] = epoch'}
    /\ kvstore' = [l \in UNION {leaseKeys[l]: l \in expired'} |-> NULL] @@ kvstore
    /\ leaseKeys' = [l \in expired' |-> {}] @@ leaseKeys
    /\ leaseExp' = [l \in expired' |-> 0] @@ leaseExp
    /\ pc' = [pc EXCEPT !["tick"] = "Tick"]
    /\ UNCHANGED << leases, wants >>

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