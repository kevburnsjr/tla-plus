----------------------------- MODULE binary_search -----------------------------

EXTENDS Integers, Sequences, TLC
CONSTANT MaxInt

PT == INSTANCE PT

OrderedSeqOf(set, n) ==
{seq \in PT!SeqOf(set, n) :
    \A x \in 2..Len(seq):
        seq[x] >= seq[x - 1]}

Range(f) == {f[x]: x \in DOMAIN f}

(*--algorithm binary_search
variables
    i = 1,
    seq \in OrderedSeqOf(1..MaxInt, MaxInt),
    target \in 1..MaxInt,
    found_index = 0;

begin
    Search:
        while i <= Len(seq) do
            if seq[i] = target then
                found_index := i;
                goto Result;
            else
                i := i + 1;
            end if;
        end while;
    Result:
        if target \in Range(seq) then
            assert seq[found_index] = target;
        else
            assert found_index = 0;
        end if;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "2ec6aa8" /\ chksum(tla) = "5d470adb")
VARIABLES i, seq, target, found_index, pc

vars == << i, seq, target, found_index, pc >>

Init == (* Global variables *)
    /\ i = 1
    /\ seq \in OrderedSeqOf(1..MaxInt, MaxInt)
    /\ target \in 1..MaxInt
    /\ found_index = 0
    /\ pc = "Search"

Search ==
    /\ pc = "Search"
    /\ IF i <= Len(seq)
        THEN
            /\ IF seq[i] = target
                THEN
                    /\ found_index' = i
                    /\ pc' = "Result"
                    /\ i' = i
                ELSE
                    /\ i' = i + 1
                    /\ pc' = "Search"
                    /\ UNCHANGED found_index
        ELSE
            /\ pc' = "Result"
            /\ UNCHANGED << i, found_index >>
    /\ UNCHANGED << seq, target >>

Result ==
    /\ pc = "Result"
    /\ IF target \in Range(seq)
        THEN
            /\ Assert(seq[found_index] = target,
                "Failure of assertion at line 34, column 13.")
        ELSE
            /\ Assert(found_index = 0,
                "Failure of assertion at line 36, column 13.")
    /\ pc' = "Done"
    /\ UNCHANGED << i, seq, target, found_index >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Search \/ Result
\/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

================================================================================

Practical TLA+ - Chapter 4
