-------------------------------- MODULE leftpad --------------------------------

EXTENDS Integers, Sequences, TLC
CONSTANTS Characters

PT == INSTANCE PT

LeftPad(c, n, str) ==
    LET
        outlen == PT!Max(Len(str), n)
        padlen ==
            CHOOSE padlen \in 0..n:
                padlen + Len(str) = outlen
    IN
        [x \in 1..padlen |-> c] \o str

(*--algorithm leftpad
variables
    in_c \in Characters \union {" "},
    in_n \in 0..6,
    in_str \in PT!SeqOf(Characters, 6),
    output;
begin
    output := in_str;
    while Len(output) < in_n do
        output := <<in_c>> \o output;
    end while;
    assert output = LeftPad(in_c, in_n, in_str);
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "74309ae1" /\ chksum(tla) = "f84b8037")
CONSTANT defaultInitValue
VARIABLES in_c, in_n, in_str, output, pc

vars == << in_c, in_n, in_str, output, pc >>

Init == (* Global variables *)
    /\ in_c \in (Characters \union {" "})
    /\ in_n \in 0..6
    /\ in_str \in PT!SeqOf(Characters, 6)
    /\ output = defaultInitValue
    /\ pc = "Lbl_1"

Lbl_1 ==
    /\ pc = "Lbl_1"
    /\ output' = in_str
    /\ pc' = "Lbl_2"
    /\ UNCHANGED << in_c, in_n, in_str >>

Lbl_2 ==
    /\ pc = "Lbl_2"
    /\ IF Len(output) < in_n
        THEN
            /\ output' = << in_c >> \o output
            /\ pc' = "Lbl_2"
        ELSE
            /\ Assert(output = LeftPad(in_c, in_n, in_str),
                "Failure of assertion at line 28, column 5.")
            /\ pc' = "Done"
            /\ UNCHANGED output
    /\ UNCHANGED << in_c, in_n, in_str >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
\/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

================================================================================

Practical TLA+ - Chapter 7
