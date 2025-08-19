------------------------------ MODULE sm_database ------------------------------

EXTENDS Integers, Sequences, TLC
CONSTANTS Data, NULL, Clients

(*--algorithm sm_database
variables
    query = [c \in Clients |-> NULL],
    db_value \in Data;

define
    Exists(val) == val # NULL
    RequestingClients == {c \in Clients: Exists(query[c]) /\ query[c].type = "request"}
end define;

macro request(data) begin
    query[self] := [type |-> "request", data |-> data];
end macro;

macro wait_for_response() begin
    await query[self].type = "response";
end macro;

process database = "Database"
begin
    DB:
        with client \in RequestingClients, q = query[client] do
            db_value := q.data;
            query[client] := [type |-> "response"];
        end with;
    goto DB;
end process;

process clients \in Clients
variables result = NULL;
begin
    Request:
        while TRUE do
            either
                result := db_value;
                assert result = db_value;
            or
                with d \in Data do
                    request(d);
                end with;
                Wait:
                    wait_for_response();
            end either;
        end while
end process;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "1f539ef3" /\ chksum(tla) = "501e3fa1")
VARIABLES query, db_value, pc

(* define statement *)
Exists(val) == val /= NULL
RequestingClients == {c \in Clients: Exists(query[c]) /\ query[c].type = "request"}

VARIABLE result

vars == << query, db_value, pc, result >>

ProcSet == {"Database"} \union (Clients)

Init == (* Global variables *)
    /\ query = [c \in Clients |-> NULL]
    /\ db_value \in Data
    (* Process clients *)
    /\ result = [self \in Clients |-> NULL]
    /\ pc = [self \in ProcSet |-> CASE self = "Database" -> "DB"
        [] self \in Clients -> "Request"]

DB ==
    /\ pc["Database"] = "DB"
    /\ \E client \in RequestingClients:
        LET q == query[client] IN
            /\ db_value' = q.data
            /\ query' = [query EXCEPT ![client] = [type |-> "response"]]
    /\ pc' = [pc EXCEPT !["Database"] = "DB"]
    /\ UNCHANGED result

database == DB

Request(self) ==
    /\ pc[self] = "Request"
    /\
        \/
            /\ result' = [result EXCEPT ![self] = db_value]
            /\ Assert(result' [self] = db_value,
                "Failure of assertion at line 41, column 17.")
            /\ pc' = [pc EXCEPT ![self] = "Request"]
            /\ query' = query
        \/
            /\ \E d \in Data:
                query' = [query EXCEPT ![self] = [type |-> "request", data |-> d]]
            /\ pc' = [pc EXCEPT ![self] = "Wait"]
            /\ UNCHANGED result
    /\ UNCHANGED db_value

Wait(self) ==
    /\ pc[self] = "Wait"
    /\ query[self].type = "response"
    /\ pc' = [pc EXCEPT ![self] = "Request"]
    /\ UNCHANGED << query, db_value, result >>

clients(self) == Request(self) \/ Wait(self)

Next == database
\/ (\E self \in Clients: clients(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

================================================================================

Practical TLA+ - Chapter 9
