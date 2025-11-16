-------------------------------- MODULE atomic ---------------------------------

EXTENDS Integers, TLC, Sequences, FiniteSets
CONSTANTS
    Clients,
    Keys,
    Leases,
    LimitAcquire,
    LimitRefresh,
    NULL,
    TTL

Symmetry == Permutations(Keys)
\union Permutations(Leases)
\union Permutations(Clients)

(*--algorithm atomic
variables
    epoch   = 0,
    key     = [k \in Keys |-> NULL],
    lease   = [l \in Leases |-> [
        acquire |-> 0,
        client  |-> NULL, 
        exp     |-> NULL, 
        keys    |-> {}, 
        locked  |-> FALSE,
        refresh |-> 0
    ]],
    change = FALSE,
    running = Clients;

define
    KeysAvailable     == {k \in Keys: key[k] = NULL}
    LeasesAcquirable  == {l \in Leases: lease[l].acquire < LimitAcquire}
    LeasesAvailable   == {l \in LeasesAcquirable: lease[l].exp = NULL}
    LeasesByClient(c) == {l \in Leases: lease[l].client = c}
    LeasesExpired     == {l \in Leases: lease[l].exp = epoch}
    LeasesRefreshable == {l \in Leases: lease[l].refresh < LimitRefresh}
end define;

fair process client \in Clients
variables
    wants \in SUBSET Keys;
begin
    Client:
        either \* Lease Acquire
            if wants # {} then
                with l \in LeasesAvailable do
                    lease[l] := [
                        acquire |-> @.acquire + 1,
                        client  |-> self,
                        exp     |-> epoch + TTL,
                        refresh |-> 0
                    ] @@ lease[l];
                end with;
            end if;
        or \* Key Acquire
            with k \in wants \intersect KeysAvailable do
                with l \in LeasesByClient(self) do
                    key[k] := l;
                    lease[l] := [
                        keys |-> @.keys \union {k}
                    ] @@ lease[l];
                    wants := wants \ {k};
                end with;
            end with;
        or \* Lease Refresh
            with l \in LeasesByClient(self) \intersect LeasesRefreshable do
                lease[l] := [
                    exp     |-> epoch + TTL,
                    refresh |-> @.refresh + 1
                ] @@ lease[l];
            end with;
        or \* Lease Revoke
            if wants = {} then
                with l \in LeasesByClient(self) do
                    key := [b \in lease[l].keys |-> NULL] @@ key;
                    lease[l] := [
                        client  |-> NULL,
                        exp     |-> NULL,
                        keys    |-> {}
                    ] @@ lease[l];
                end with;
            end if;
        end either;
        if (wants # {} /\ LeasesAcquirable # {}) \/ LeasesByClient(self) \intersect LeasesRefreshable # {} then
            goto Client;
        else
            running := running \ {self};
        end if;
end process;

fair process clock = "clock"
variable
    prev = NULL
begin
    Await:
        await lease # prev \/ running = {};
    Tick:
        epoch := epoch + 1;
        key := [k \in UNION {lease[l].keys: l \in LeasesExpired} |-> NULL] @@ key;
        lease := [l \in LeasesExpired |-> [
            client  |-> NULL,
            exp     |-> NULL,
            keys    |-> {}
        ] @@ lease[l]] @@ lease;
        prev := lease;
        if running # {} then
            goto Await;
        end if;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "1ff24a1c" /\ chksum(tla) = "e3db4d03")
VARIABLES epoch, key, lease, change, running, pc

(* define statement *)
KeysAvailable == {k \in Keys: key[k] = NULL}
LeasesAcquirable == {l \in Leases: lease[l].acquire < LimitAcquire}
LeasesAvailable == {l \in LeasesAcquirable: lease[l].exp = NULL}
LeasesByClient(c) == {l \in Leases: lease[l].client = c}
LeasesExpired == {l \in Leases: lease[l].exp = epoch}
LeasesRefreshable == {l \in Leases: lease[l].refresh < LimitRefresh}

VARIABLES wants, prev

vars == << epoch, key, lease, change, running, pc, wants, prev >>

ProcSet == (Clients) \union {"clock"}

Init == (* Global variables *)
    /\ epoch = 0
    /\ key = [k \in Keys |-> NULL]
    /\ lease = [l \in Leases |-> [
            acquire |-> 0,
            client |-> NULL,
            exp |-> NULL,
            keys |-> {},
            locked |-> FALSE,
            refresh |-> 0
        ]]
    /\ change = FALSE
    /\ running = Clients
    (* Process client *)
    /\ wants \in [Clients -> SUBSET Keys]
    (* Process clock *)
    /\ prev = NULL
    /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "Client"
        [] self = "clock" -> "Await"]

Client(self) ==
    /\ pc[self] = "Client"
    /\
        \/
            /\ IF wants[self] /= {}
                THEN
                    /\ \E l \in LeasesAvailable:
                        lease' = [lease EXCEPT ![l] = [
                                acquire |-> @.acquire + 1,
                                client |-> self,
                                exp |-> epoch + TTL,
                                refresh |-> 0
                            ] @@ lease[l]]
                ELSE
                    /\ TRUE
                    /\ lease' = lease
            /\ UNCHANGED << key, wants >>
        \/
                /\ \E k \in wants[self] \intersect KeysAvailable:
                    \E l \in LeasesByClient(self):
                        /\ key' = [key EXCEPT ![k] = l]
                        /\ lease' = [lease EXCEPT ![l] = [
                                keys |-> @.keys \union {k}
                            ] @@ lease[l]]
                        /\ wants' = [wants EXCEPT ![self] = wants[self] \ {k}]
        \/
                /\ \E l \in LeasesByClient(self) \intersect LeasesRefreshable:
                    lease' = [lease EXCEPT ![l] = [
                            exp |-> epoch + TTL,
                            refresh |-> @.refresh + 1
                        ] @@ lease[l]]
                /\ UNCHANGED << key, wants >>
        \/
                /\ IF wants[self] = {}
                    THEN
                        /\ \E l \in LeasesByClient(self):
                            /\ key' = [b \in lease[l].keys |-> NULL] @@ key
                            /\ lease' = [lease EXCEPT ![l] = [
                                    client |-> NULL,
                                    exp |-> NULL,
                                    keys |-> {}
                                ] @@ lease[l]]
                    ELSE
                        /\ TRUE
                        /\ UNCHANGED << key, lease >>
                /\ wants' = wants
    /\ IF (wants' [self] /= {} /\ LeasesAcquirable /= {}) \/ LeasesByClient(self) \intersect LeasesRefreshable /= {}
        THEN
            /\ pc' = [pc EXCEPT ![self] = "Client"]
            /\ UNCHANGED running
        ELSE
            /\ running' = running \ {self}
            /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED << epoch, change, prev >>

client(self) == Client(self)

Await ==
    /\ pc["clock"] = "Await"
    /\ lease /= prev \/ running = {}
    /\ pc' = [pc EXCEPT !["clock"] = "Tick"]
    /\ UNCHANGED << epoch, key, lease, change, running, wants, prev >>

Tick ==
    /\ pc["clock"] = "Tick"
    /\ epoch' = epoch + 1
    /\ key' = [k \in UNION {lease[l].keys: l \in LeasesExpired} |-> NULL] @@ key
    /\ lease' = [l \in LeasesExpired |-> [
            client |-> NULL,
            exp |-> NULL,
            keys |-> {}
        ] @@ lease[l]] @@ lease
    /\ prev' = lease'
    /\ IF running /= {}
        THEN
            /\ pc' = [pc EXCEPT !["clock"] = "Await"]
        ELSE
            /\ pc' = [pc EXCEPT !["clock"] = "Done"]
    /\ UNCHANGED << change, running, wants >>

clock == Await \/ Tick

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating ==
    /\ \A self \in ProcSet: pc[self] = "Done"
    /\ UNCHANGED vars

Next == clock
\/ (\E self \in Clients: client(self))
\/ Terminating

Spec ==
    /\ Init /\ [][Next]_vars
    /\ \A self \in Clients: WF_vars(client(self))
    /\ WF_vars(clock)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

================================================================================