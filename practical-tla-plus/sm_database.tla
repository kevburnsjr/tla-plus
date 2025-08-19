------------------------------ MODULE sm_database ------------------------------

EXTENDS Integers, Sequences, TLC
CONSTANTS Data, NULL, Clients

(*--algorithm sm_database
variables
    db_value \in Data;

process clients \in Clients
variables result = NULL;
begin
    Client:
        either
            result := db_value;
            assert result = db_value;
        or
            with d \in Data do
                db_value := d;
            end with
        end either;
        goto Client;
end process;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "e2522473" /\ chksum(tla) = "98e3036d")
VARIABLES db_value, pc, result

vars == << db_value, pc, result >>

ProcSet == (Clients)

Init == (* Global variables *)
    /\ db_value \in Data
    (* Process clients *)
    /\ result = [self \in Clients |-> NULL]
    /\ pc = [self \in ProcSet |-> "Client"]

Client(self) ==
    /\ pc[self] = "Client"
    /\
        \/
            /\ result' = [result EXCEPT ![self] = db_value]
            /\ Assert(result' [self] = db_value,
                "Failure of assertion at line 16, column 13.")
            /\ UNCHANGED db_value
        \/
            /\ \E d \in Data:
                db_value' = d
            /\ UNCHANGED result
    /\ pc' = [pc EXCEPT ![self] = "Client"]

clients(self) == Client(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating ==
    /\ \A self \in ProcSet: pc[self] = "Done"
    /\ UNCHANGED vars

Next == (\E self \in Clients: clients(self))
\/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

================================================================================

Practical TLA+ - Chapter 9
