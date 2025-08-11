--------------------------------- MODULE cache ---------------------------------

EXTENDS Integers
CONSTANTS ResourceCap, MaxConsumerReq, Actors

ASSUME ResourceCap > 0
ASSUME MaxConsumerReq \in 1..ResourceCap
ASSUME Actors /= {}

(*--algorithm cache

variables resources_left = ResourceCap;

define
    ResourceInvariant == resources_left >= 0
end define;

process actor \in Actors
variables
    resources_needed \in 1..MaxConsumerReq
begin
    UseResources:
        while TRUE do
            await resources_left >= resources_needed;
            resources_left := resources_left - resources_needed;
        end while;
end process;

process time = "time"
begin
    Tick:
        resources_left := ResourceCap;
        goto Tick;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "ed6aa90c" /\ chksum(tla) = "f1560614")
VARIABLES resources_left, pc

(* define statement *)
ResourceInvariant == resources_left >= 0

VARIABLE resources_needed

vars == << resources_left, pc, resources_needed >>

ProcSet == (Actors) \union {"time"}

Init == (* Global variables *)
    /\ resources_left = ResourceCap
    (* Process actor *)
    /\ resources_needed \in [Actors -> 1..MaxConsumerReq]
    /\ pc = [self \in ProcSet |-> CASE self \in Actors -> "UseResources"
        [] self = "time" -> "Tick"]

UseResources(self) ==
    /\ pc[self] = "UseResources"
    /\ resources_left >= resources_needed[self]
    /\ resources_left' = resources_left - resources_needed[self]
    /\ pc' = [pc EXCEPT ![self] = "UseResources"]
    /\ UNCHANGED resources_needed

actor(self) == UseResources(self)

Tick ==
    /\ pc["time"] = "Tick"
    /\ resources_left' = ResourceCap
    /\ pc' = [pc EXCEPT !["time"] = "Tick"]
    /\ UNCHANGED resources_needed

time == Tick

Next == time
\/ (\E self \in Actors: actor(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

================================================================================

Practical TLA+ - Chapter 4
