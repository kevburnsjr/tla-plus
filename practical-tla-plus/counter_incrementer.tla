-------------------------- MODULE counter_incrementer --------------------------

EXTENDS Integers, Sequences, TLC
\* CONSTANTS

(*--algorithm counter_incrementer
variables
    counter = 0,
    goal = 3;

define
    Success == <>[](counter = goal)
end define;

fair process incrementer \in 1..3
variable local = 0
begin
    Get:
        local := counter;
        counter := local + 1;
end process;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "82b7f231" /\ chksum(tla) = "bb8264af")
VARIABLES counter, goal, pc

(* define statement *)
Success == <>[](counter = goal)

VARIABLE local

vars == << counter, goal, pc, local >>

ProcSet == (1..3)

Init == (* Global variables *)
    /\ counter = 0
    /\ goal = 3
    (* Process incrementer *)
    /\ local = [self \in 1..3 |-> 0]
    /\ pc = [self \in ProcSet |-> "Get"]

Get(self) ==
    /\ pc[self] = "Get"
    /\ local' = [local EXCEPT ![self] = counter]
    /\ counter' = local' [self] + 1
    /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ goal' = goal

incrementer(self) == Get(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating ==
    /\ \A self \in ProcSet: pc[self] = "Done"
    /\ UNCHANGED vars

Next == (\E self \in 1..3: incrementer(self))
\/ Terminating

Spec ==
    /\ Init /\ [][Next]_vars
    /\ \A self \in 1..3: WF_vars(incrementer(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

================================================================================

Practical TLA+ - Chapter 7
