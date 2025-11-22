-------------------------------- MODULE atomic ---------------------------------

EXTENDS Integers, TLC, Sequences, FiniteSets
CONSTANTS
    Clients,
    Keys,
    LimitAcquire,
    LimitRefresh,
    NULL,
    TTL

Symmetry == Permutations(Keys)
\union Permutations(Clients)

(*--algorithm atomic
variables
    network = [n \in {"service"} |-> <<>>],
    resp    = [c \in Clients \union {"controller"} |-> NULL],
    running = Clients,
    serviceRunning = TRUE;

macro request(p, msg) begin
    resp[p] := NULL;
    network["service"] := Append(network["service"], [src |-> p] @@ msg);
end macro;

macro respond(src, msg) begin
    resp[src] := msg
end macro;

fair process client \in Clients
variables
    acquisitions = 0,
    debounceReserve = NULL,
    debounceRefresh = 0,
    lease = 0,
    wants = Keys;
begin
    Setup:
        if acquisitions < LimitAcquire /\ wants # {} then
            request(self, [type |-> "Acquire", lease |-> lease]);
            AwaitAcquire:
                await resp[self] # NULL;
                assert resp[self].type = "Success";
                lease := resp[self].lease;
                acquisitions := acquisitions + 1;
                debounceRefresh := 0;
        else
            goto Finish;
        end if;
    Reserve:
        while wants # {} do
            either \* Key Reserve
                if debounceReserve # epoch then
                    with k \in wants do
                        request(self, [type |-> "Reserve", lease |-> lease, key |-> k]);
                    end with;
                    AwaitReserve:
                        await resp[self] # NULL;
                        if resp[self].type = "Success" then
                            wants := wants \ {resp[self].key};
                        elsif resp[self].type = "Expired" then
                            goto Setup;
                        else \* Block retry until next epoch
                            debounceReserve := epoch;
                        end if;
                end if;
            or \* Lease Refresh
                if debounceRefresh # NULL /\ debounceRefresh # epoch then
                    request(self, [type |-> "Refresh", lease |-> lease]);
                    AwaitRefresh:
                        await resp[self] # NULL;
                        if resp[self].type = "Success" then
                            debounceRefresh := epoch;
                        elsif resp[self].type = "Expired" then
                            goto Setup;
                        else \* Never retry failed refresh
                            debounceRefresh := NULL;
                        end if;
                end if;
            end either;
        end while;
    Finish:
        running := running \ {self};
        either \* Revoke
            request(self, [type |-> "Revoke", lease |-> lease]);
        or \* Expire
            skip;
        end either;
end process;

fair process service = "service"
variables
    epoch   = 0,
    expired = NULL,
    id      = 0,
    idauto  = 0,
    key     = [k \in Keys |-> NULL],
    leases  = <<>>,
    msg     = NULL;
begin
    Wait:
        await network["service"] # <<>>;
        msg := Head(network["service"]);
        network["service"] := Tail(network["service"]);
        if msg.type = "Acquire" then
            Acquire:
                if msg.lease > 0 then
                    id := msg.lease;
                else
                    idauto := idauto + 1;
                    id := idauto;
                end if;
                leases := Append(leases, [
                    client  |-> msg.src,
                    exp     |-> epoch + TTL,
                    keys    |-> {},
                    refresh |-> 0
                ]);
                respond(msg.src, [type |-> "Success", lease |-> id]);
        elsif msg.type = "Reserve" then
            Reserve:
                if leases[msg.lease].exp = NULL then
                    respond(msg.src, [type |-> "Expired"]);
                elsif key[msg.key] # NULL then
                    respond(msg.src, [type |-> "Conflict"]);
                else
                    key[msg.key] := msg.lease;
                    leases[msg.lease] := [
                        keys |-> @.keys \union {msg.key}
                    ] @@ leases[msg.lease];
                    respond(msg.src, [type |-> "Success", key |-> msg.key]);
                end if;
        elsif msg.type = "Refresh" then
            Refresh:
                if leases[msg.lease].exp = NULL then
                    respond(msg.src, [type |-> "Expired"]);
                elsif leases[msg.lease].refresh = LimitRefresh then
                    respond(msg.src, [type |-> "Conflict"]);
                else
                    leases[msg.lease] := [
                        exp     |-> epoch + TTL,
                        refresh |-> @.refresh + 1
                    ] @@ leases[msg.lease];
                    respond(msg.src, [type |-> "Success"]);
                end if;
        elsif msg.type = "Revoke" then
            Revoke:
                key := [b \in leases[msg.lease].keys |-> NULL] @@ key;
                leases[msg.lease] := [
                    client  |-> NULL,
                    exp     |-> NULL,
                    keys    |-> {}
                ] @@ leases[msg.lease];
                respond(msg.src, [type |-> "Success"]);
        elsif msg.type = "Tick" then
            Tick:
                epoch := epoch + 1;
                expired := {i \in DOMAIN leases: leases[i].exp = epoch};
                key := [k \in UNION {leases[i].keys: i \in expired} |-> NULL] @@ key;
                leases := [i \in expired |-> [
                    client  |-> NULL,
                    exp     |-> NULL,
                    keys    |-> {}
                ] @@ leases[i]] @@ leases;
                if running = {} /\ {i \in DOMAIN leases: leases[i].exp # NULL} = {} /\ network["service"] = <<>> then
                    serviceRunning := FALSE;
                end if;
                respond(msg.src, [type |-> "Success"]);
        else
            assert FALSE;
        end if;
    Again:
        if serviceRunning then
            goto Wait;
        end if;
end process;

fair process controller = "controller"
variable
begin
    Tick:
        request("controller", [type |-> "Tick"]);
        AwaitTick:
            await resp["controller"] # NULL;
            assert resp["controller"].type = "Success";
            if serviceRunning then
                goto Tick;
            end if;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "52c35096" /\ chksum(tla) = "65dbb861")
\* Label Reserve of process client at line 52 col 9 changed to Reserve_
\* Label Tick of process service at line 158 col 17 changed to Tick_
VARIABLES network, resp, running, serviceRunning, pc, acquisitions,
    debounceReserve, debounceRefresh, lease, wants, epoch, expired, id,
    idauto, key, leases, msg

vars == << network, resp, running, serviceRunning, pc, acquisitions,
    debounceReserve, debounceRefresh, lease, wants, epoch, expired, id,
    idauto, key, leases, msg >>

ProcSet == (Clients) \union {"service"} \union {"controller"}

Init == (* Global variables *)
    /\ network = [n \in {"service"} |-> <<>>]
    /\ resp = [c \in Clients \union {"controller"} |-> NULL]
    /\ running = Clients
    /\ serviceRunning = TRUE
    (* Process client *)
    /\ acquisitions = [self \in Clients |-> 0]
    /\ debounceReserve = [self \in Clients |-> NULL]
    /\ debounceRefresh = [self \in Clients |-> 0]
    /\ lease = [self \in Clients |-> 0]
    /\ wants = [self \in Clients |-> Keys]
    (* Process service *)
    /\ epoch = 0
    /\ expired = NULL
    /\ id = 0
    /\ idauto = 0
    /\ key = [k \in Keys |-> NULL]
    /\ leases = <<>>
    /\ msg = NULL
    /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "Setup"
        [] self = "service" -> "Wait"
        [] self = "controller" -> "Tick"]

Setup(self) ==
    /\ pc[self] = "Setup"
    /\ IF acquisitions[self] < LimitAcquire /\ wants[self] /= {}
        THEN
            /\ resp' = [resp EXCEPT ![self] = NULL]
            /\ network' = [network EXCEPT !["service"] = Append(network["service"], [src |-> self] @@ ([type |-> "Acquire", lease |-> lease[self]]))]
            /\ pc' = [pc EXCEPT ![self] = "AwaitAcquire"]
        ELSE
            /\ pc' = [pc EXCEPT ![self] = "Finish"]
            /\ UNCHANGED << network, resp >>
    /\ UNCHANGED << running, serviceRunning, acquisitions,
            debounceReserve, debounceRefresh, lease, wants,
            epoch, expired, id, idauto, key, leases, msg >>

AwaitAcquire(self) ==
    /\ pc[self] = "AwaitAcquire"
    /\ resp[self] /= NULL
    /\ Assert(resp[self].type = "Success",
        "Failure of assertion at line 44, column 17.")
    /\ lease' = [lease EXCEPT ![self] = resp[self].lease]
    /\ acquisitions' = [acquisitions EXCEPT ![self] = acquisitions[self] + 1]
    /\ debounceRefresh' = [debounceRefresh EXCEPT ![self] = 0]
    /\ pc' = [pc EXCEPT ![self] = "Reserve_"]
    /\ UNCHANGED << network, resp, running, serviceRunning,
        debounceReserve, wants, epoch, expired,
        id, idauto, key, leases, msg >>

Reserve_(self) ==
    /\ pc[self] = "Reserve_"
    /\ IF wants[self] /= {}
        THEN
            /\
                \/
                    /\ IF debounceReserve[self] /= epoch
                        THEN
                            /\ \E k \in wants[self]:
                                /\ resp' = [resp EXCEPT ![self] = NULL]
                                /\ network' = [network EXCEPT !["service"] = Append(network["service"], [src |-> self] @@ ([type |-> "Reserve", lease |-> lease[self], key |-> k]))]
                            /\ pc' = [pc EXCEPT ![self] = "AwaitReserve"]
                        ELSE
                            /\ pc' = [pc EXCEPT ![self] = "Reserve_"]
                            /\ UNCHANGED << network, resp >>
                \/
                        /\ IF debounceRefresh[self] /= NULL /\ debounceRefresh[self] /= epoch
                            THEN
                                /\ resp' = [resp EXCEPT ![self] = NULL]
                                /\ network' = [network EXCEPT !["service"] = Append(network["service"], [src |-> self] @@ ([type |-> "Refresh", lease |-> lease[self]]))]
                                /\ pc' = [pc EXCEPT ![self] = "AwaitRefresh"]
                            ELSE
                                /\ pc' = [pc EXCEPT ![self] = "Reserve_"]
                                /\ UNCHANGED << network, resp >>
        ELSE
            /\ pc' = [pc EXCEPT ![self] = "Finish"]
            /\ UNCHANGED << network, resp >>
    /\ UNCHANGED << running, serviceRunning, acquisitions,
            debounceReserve, debounceRefresh, lease,
            wants, epoch, expired, id, idauto, key,
            leases, msg >>

AwaitReserve(self) ==
    /\ pc[self] = "AwaitReserve"
    /\ resp[self] /= NULL
    /\ IF resp[self].type = "Success"
        THEN
            /\ wants' = [wants EXCEPT ![self] = wants[self] \ {resp[self].key}]
            /\ pc' = [pc EXCEPT ![self] = "Reserve_"]
            /\ UNCHANGED debounceReserve
        ELSE
            /\ IF resp[self].type = "Expired"
                THEN
                    /\ pc' = [pc EXCEPT ![self] = "Setup"]
                    /\ UNCHANGED debounceReserve
                ELSE
                    /\ debounceReserve' = [debounceReserve EXCEPT ![self] = epoch]
                    /\ pc' = [pc EXCEPT ![self] = "Reserve_"]
            /\ wants' = wants
    /\ UNCHANGED << network, resp, running, serviceRunning,
            acquisitions, debounceRefresh, lease,
            epoch, expired, id, idauto, key, leases,
            msg >>

AwaitRefresh(self) ==
    /\ pc[self] = "AwaitRefresh"
    /\ resp[self] /= NULL
    /\ IF resp[self].type = "Success"
        THEN
            /\ debounceRefresh' = [debounceRefresh EXCEPT ![self] = epoch]
            /\ pc' = [pc EXCEPT ![self] = "Reserve_"]
        ELSE
            /\ IF resp[self].type = "Expired"
                THEN
                    /\ pc' = [pc EXCEPT ![self] = "Setup"]
                    /\ UNCHANGED debounceRefresh
                ELSE
                    /\ debounceRefresh' = [debounceRefresh EXCEPT ![self] = NULL]
                    /\ pc' = [pc EXCEPT ![self] = "Reserve_"]
    /\ UNCHANGED << network, resp, running, serviceRunning,
            acquisitions, debounceReserve, lease,
            wants, epoch, expired, id, idauto, key,
            leases, msg >>

Finish(self) ==
    /\ pc[self] = "Finish"
    /\ running' = running \ {self}
    /\
        \/
            /\ resp' = [resp EXCEPT ![self] = NULL]
            /\ network' = [network EXCEPT !["service"] = Append(network["service"], [src |-> self] @@ ([type |-> "Revoke", lease |-> lease[self]]))]
        \/
            /\ TRUE
            /\ UNCHANGED << network, resp >>
    /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED << serviceRunning, acquisitions, debounceReserve,
        debounceRefresh, lease, wants, epoch, expired,
        id, idauto, key, leases, msg >>

client(self) == Setup(self) \/ AwaitAcquire(self) \/ Reserve_(self)
\/ AwaitReserve(self) \/ AwaitRefresh(self)
\/ Finish(self)

Wait ==
    /\ pc["service"] = "Wait"
    /\ network["service"] /= <<>>
    /\ msg' = Head(network["service"])
    /\ network' = [network EXCEPT !["service"] = Tail(network["service"])]
    /\ IF msg' .type = "Acquire"
        THEN
            /\ pc' = [pc EXCEPT !["service"] = "Acquire"]
        ELSE
            /\ IF msg' .type = "Reserve"
                THEN
                    /\ pc' = [pc EXCEPT !["service"] = "Reserve"]
                ELSE
                    /\ IF msg' .type = "Refresh"
                        THEN
                            /\ pc' = [pc EXCEPT !["service"] = "Refresh"]
                        ELSE
                            /\ IF msg' .type = "Revoke"
                                THEN
                                    /\ pc' = [pc EXCEPT !["service"] = "Revoke"]
                                ELSE
                                    /\ IF msg' .type = "Tick"
                                        THEN
                                            /\ pc' = [pc EXCEPT !["service"] = "Tick_"]
                                        ELSE
                                            /\ Assert(FALSE,
                                                "Failure of assertion at line 171, column 13.")
                                            /\ pc' = [pc EXCEPT !["service"] = "Again"]
    /\ UNCHANGED << resp, running, serviceRunning, acquisitions,
            debounceReserve, debounceRefresh, lease, wants, epoch,
            expired, id, idauto, key, leases >>

Acquire ==
    /\ pc["service"] = "Acquire"
    /\ IF msg.lease > 0
        THEN
            /\ id' = msg.lease
            /\ UNCHANGED idauto
        ELSE
            /\ idauto' = idauto + 1
            /\ id' = idauto'
    /\ leases' = Append(leases, [
                client |-> msg.src,
                exp |-> epoch + TTL,
                keys |-> {},
                refresh |-> 0
            ])
    /\ resp' = [resp EXCEPT ![(msg.src)] = [type |-> "Success", lease |-> id']]
    /\ pc' = [pc EXCEPT !["service"] = "Again"]
    /\ UNCHANGED << network, running, serviceRunning, acquisitions,
        debounceReserve, debounceRefresh, lease, wants,
        epoch, expired, key, msg >>

Reserve ==
    /\ pc["service"] = "Reserve"
    /\ IF leases[msg.lease].exp = NULL
        THEN
            /\ resp' = [resp EXCEPT ![(msg.src)] = [type |-> "Expired"]]
            /\ UNCHANGED << key, leases >>
        ELSE
            /\ IF key[msg.key] /= NULL
                THEN
                    /\ resp' = [resp EXCEPT ![(msg.src)] = [type |-> "Conflict"]]
                    /\ UNCHANGED << key, leases >>
                ELSE
                    /\ key' = [key EXCEPT ![msg.key] = msg.lease]
                    /\ leases' = [leases EXCEPT ![msg.lease] = [
                            keys |-> @.keys \union {msg.key}
                        ] @@ leases[msg.lease]]
                    /\ resp' = [resp EXCEPT ![(msg.src)] = [type |-> "Success", key |-> msg.key]]
    /\ pc' = [pc EXCEPT !["service"] = "Again"]
    /\ UNCHANGED << network, running, serviceRunning, acquisitions,
            debounceReserve, debounceRefresh, lease, wants,
            epoch, expired, id, idauto, msg >>

Refresh ==
    /\ pc["service"] = "Refresh"
    /\ IF leases[msg.lease].exp = NULL
        THEN
            /\ resp' = [resp EXCEPT ![(msg.src)] = [type |-> "Expired"]]
            /\ UNCHANGED leases
        ELSE
            /\ IF leases[msg.lease].refresh = LimitRefresh
                THEN
                    /\ resp' = [resp EXCEPT ![(msg.src)] = [type |-> "Conflict"]]
                    /\ UNCHANGED leases
                ELSE
                    /\ leases' = [leases EXCEPT ![msg.lease] = [
                            exp |-> epoch + TTL,
                            refresh |-> @.refresh + 1
                        ] @@ leases[msg.lease]]
                    /\ resp' = [resp EXCEPT ![(msg.src)] = [type |-> "Success"]]
    /\ pc' = [pc EXCEPT !["service"] = "Again"]
    /\ UNCHANGED << network, running, serviceRunning, acquisitions,
            debounceReserve, debounceRefresh, lease, wants,
            epoch, expired, id, idauto, key, msg >>

Revoke ==
    /\ pc["service"] = "Revoke"
    /\ key' = [b \in leases[msg.lease].keys |-> NULL] @@ key
    /\ leases' = [leases EXCEPT ![msg.lease] = [
            client |-> NULL,
            exp |-> NULL,
            keys |-> {}
        ] @@ leases[msg.lease]]
    /\ resp' = [resp EXCEPT ![(msg.src)] = [type |-> "Success"]]
    /\ pc' = [pc EXCEPT !["service"] = "Again"]
    /\ UNCHANGED << network, running, serviceRunning, acquisitions,
        debounceReserve, debounceRefresh, lease, wants,
        epoch, expired, id, idauto, msg >>

Tick_ ==
    /\ pc["service"] = "Tick_"
    /\ epoch' = epoch + 1
    /\ expired' = {i \in DOMAIN leases: leases[i].exp = epoch'}
    /\ key' = [k \in UNION {leases[i].keys: i \in expired'} |-> NULL] @@ key
    /\ leases' = [i \in expired' |-> [
            client |-> NULL,
            exp |-> NULL,
            keys |-> {}
        ] @@ leases[i]] @@ leases
    /\ IF running = {} /\ {i \in DOMAIN leases': leases' [i].exp /= NULL} = {} /\ network["service"] = <<>>
        THEN
            /\ serviceRunning' = FALSE
        ELSE
            /\ TRUE
            /\ UNCHANGED serviceRunning
    /\ resp' = [resp EXCEPT ![(msg.src)] = [type |-> "Success"]]
    /\ pc' = [pc EXCEPT !["service"] = "Again"]
    /\ UNCHANGED << network, running, acquisitions, debounceReserve,
        debounceRefresh, lease, wants, id, idauto, msg >>

Again ==
    /\ pc["service"] = "Again"
    /\ IF serviceRunning
        THEN
            /\ pc' = [pc EXCEPT !["service"] = "Wait"]
        ELSE
            /\ pc' = [pc EXCEPT !["service"] = "Done"]
    /\ UNCHANGED << network, resp, running, serviceRunning, acquisitions,
            debounceReserve, debounceRefresh, lease, wants, epoch,
            expired, id, idauto, key, leases, msg >>

service == Wait \/ Acquire \/ Reserve \/ Refresh \/ Revoke \/ Tick_
\/ Again

Tick ==
    /\ pc["controller"] = "Tick"
    /\ resp' = [resp EXCEPT !["controller"] = NULL]
    /\ network' = [network EXCEPT !["service"] = Append(network["service"], [src |-> "controller"] @@ ([type |-> "Tick"]))]
    /\ pc' = [pc EXCEPT !["controller"] = "AwaitTick"]
    /\ UNCHANGED << running, serviceRunning, acquisitions, debounceReserve,
        debounceRefresh, lease, wants, epoch, expired, id,
        idauto, key, leases, msg >>

AwaitTick ==
    /\ pc["controller"] = "AwaitTick"
    /\ resp["controller"] /= NULL
    /\ Assert(resp["controller"].type = "Success",
        "Failure of assertion at line 186, column 13.")
    /\ IF serviceRunning
        THEN
            /\ pc' = [pc EXCEPT !["controller"] = "Tick"]
        ELSE
            /\ pc' = [pc EXCEPT !["controller"] = "Done"]
    /\ UNCHANGED << network, resp, running, serviceRunning,
            acquisitions, debounceReserve, debounceRefresh,
            lease, wants, epoch, expired, id, idauto, key,
            leases, msg >>

controller == Tick \/ AwaitTick

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating ==
    /\ \A self \in ProcSet: pc[self] = "Done"
    /\ UNCHANGED vars

Next == service \/ controller
\/ (\E self \in Clients: client(self))
\/ Terminating

Spec ==
    /\ Init /\ [][Next]_vars
    /\ \A self \in Clients: WF_vars(client(self))
    /\ WF_vars(service)
    /\ WF_vars(controller)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

================================================================================