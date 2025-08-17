---------------------------------- MODULE add ----------------------------------

EXTENDS Integers, TLC

add(a, b) == a + b

(*--algorithm add

variables
    in_a \in -5..5,
    in_b \in -5..5,
    output;

begin
    output := in_a + in_b;
    assert output = add(in_a, in_b)
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "cedde9c9" /\ chksum(tla) = "fbe3029d")
CONSTANT defaultInitValue
VARIABLES in_a, in_b, output, pc

vars == << in_a, in_b, output, pc >>

Init == (* Global variables *)
    /\ in_a \in - 5..5
    /\ in_b \in - 5..5
    /\ output = defaultInitValue
    /\ pc = "Lbl_1"

Lbl_1 ==
    /\ pc = "Lbl_1"
    /\ output' = in_a + in_b
    /\ Assert(output' = add(in_a, in_b),
        "Failure of assertion at line 16, column 5.")
    /\ pc' = "Done"
    /\ UNCHANGED << in_a, in_b >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
\/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

================================================================================

Practical TLA+ - Chapter 7
