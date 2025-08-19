-------------------------------- MODULE sm_door --------------------------------

(*--algorithm sm_door

variables
    open = FALSE,
    locked = FALSE,
    key \in BOOLEAN;

begin
    Event:
        either
            await locked /\ (open \/ key);
            locked := FALSE;
        or
            await ~locked /\ (open \/ key);
            locked := TRUE;
        or
            await ~locked /\ ~open;
            open := TRUE;
        or
            await open /\ ~locked;
            open := FALSE;
        end either;
    goto Event;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "b132eb85" /\ chksum(tla) = "ddd12b84")
VARIABLES open, locked, key, pc

vars == << open, locked, key, pc >>

Init == (* Global variables *)
    /\ open = FALSE
    /\ locked = FALSE
    /\ key \in BOOLEAN
    /\ pc = "Event"

Event ==
    /\ pc = "Event"
    /\
        \/
            /\ locked /\ (open \/ key)
            /\ locked' = FALSE
            /\ open' = open
        \/
            /\ ~locked /\ (open \/ key)
            /\ locked' = TRUE
            /\ open' = open
        \/
            /\ ~locked /\ ~open
            /\ open' = TRUE
            /\ UNCHANGED locked
        \/
            /\ open /\ ~locked
            /\ open' = FALSE
            /\ UNCHANGED locked
    /\ pc' = "Event"
    /\ key' = key

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Event
\/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

================================================================================

Practical TLA+ - Chapter 4
