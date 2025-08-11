--------------------------------- MODULE cache ---------------------------------

EXTENDS Integers
CONSTANTS ResourceCap, MaxConsumerReq, Actors

ASSUME ResourceCap > 0
ASSUME MaxConsumerReq \in 1..ResourceCap
ASSUME Actors /= {}

(*--algorithm cache

variables
    resources_left = ResourceCap;
    ran = [a \in Actors |-> FALSE];

define
    ResourceInvariant == resources_left >= 0
end define;

process actor \in Actors
variables
    resources_needed \in 1..MaxConsumerReq
begin
    WaitForResources:
        while TRUE do
            await ~ran[self];
            UseResources:
                while resources_needed > 0 do
                    resources_left := resources_left - 1;
                    resources_needed := resources_needed - 1;
                end while;
                with x \in 1..MaxConsumerReq do
                    resources_needed := x;
                end with;
                ran[self] := TRUE;
        end while;
end process;

process time = "time"
begin
    Tick:
        resources_left := ResourceCap;
        ran := [a \in Actors |-> FALSE];
        goto Tick;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "5de6252" /\ chksum(tla) = "7f0900eb")
VARIABLES resources_left, ran, pc

(* define statement *)
ResourceInvariant == resources_left >= 0

VARIABLE resources_needed

vars == << resources_left, ran, pc, resources_needed >>

ProcSet == (Actors) \union {"time"}

Init == (* Global variables *)
    /\ resources_left = ResourceCap
    /\ ran = [a \in Actors |-> FALSE]
    (* Process actor *)
    /\ resources_needed \in [Actors -> 1..MaxConsumerReq]
    /\ pc = [self \in ProcSet |-> CASE self \in Actors -> "WaitForResources"
        [] self = "time" -> "Tick"]

WaitForResources(self) ==
    /\ pc[self] = "WaitForResources"
    /\ ~ran[self]
    /\ pc' = [pc EXCEPT ![self] = "UseResources"]
    /\ UNCHANGED << resources_left, ran,
        resources_needed >>

UseResources(self) ==
    /\ pc[self] = "UseResources"
    /\ IF resources_needed[self] > 0
        THEN
            /\ resources_left' = resources_left - 1
            /\ resources_needed' = [resources_needed EXCEPT ![self] = resources_needed[self] - 1]
            /\ pc' = [pc EXCEPT ![self] = "UseResources"]
            /\ ran' = ran
        ELSE
            /\ \E x \in 1..MaxConsumerReq:
                resources_needed' = [resources_needed EXCEPT ![self] = x]
            /\ ran' = [ran EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "WaitForResources"]
            /\ UNCHANGED resources_left

actor(self) == WaitForResources(self) \/ UseResources(self)

Tick ==
    /\ pc["time"] = "Tick"
    /\ resources_left' = ResourceCap
    /\ ran' = [a \in Actors |-> FALSE]
    /\ pc' = [pc EXCEPT !["time"] = "Tick"]
    /\ UNCHANGED resources_needed

time == Tick

Next == time
\/ (\E self \in Actors: actor(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

================================================================================

Practical TLA+ - Chapter 4
