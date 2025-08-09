--------------------------------- MODULE knapsack ---------------------------------

EXTENDS Sequences, Integers, TLC

PT == INSTANCE PT

Capacity == 4
Items == {"a", "b", "c"}
ItemParams == [size: 2..4, value: 0..5]
\* ItemSets == [a: ItemParams, b: ItemParams, c: ItemParams]
ItemSets == [Items -> ItemParams]

KnapsackSize(sack, itemset) ==
    LET size_for(item) == itemset[item].size * sack[item]
    IN PT!ReduceSet(LAMBDA item, acc: size_for(item) + acc, Items, 0)

ValidKnapsacks(itemset) ==
    {sack \in [Items -> 0..4]: KnapsackSize(sack, itemset) <= Capacity}

KnapsackValue(sack, itemset) ==
    LET value_for(item) == itemset[item].value * sack[item]
    IN PT!ReduceSet(LAMBDA item, acc: value_for(item) + acc, Items, 0)

BestKnapsack(itemset) ==
    LET all == ValidKnapsacks(itemset)
    IN CHOOSE best \in all:
        \A worse \in all \ {best}:
        KnapsackValue(best, itemset) > KnapsackValue(worse, itemset)

BestKnapsacks(itemset) ==
    LET
        value(sack) == KnapsackValue(sack, itemset)
        all == ValidKnapsacks(itemset)
        best == CHOOSE best \in all:
            \A worse \in all \ {best}:
                value(best) >= value(worse)
    IN
        {k \in all: value(best) = value(k)}

(*--algorithm knapsack
variables
    itemset \in ItemSets;
begin
    assert BestKnapsacks(itemset) \subseteq ValidKnapsacks(itemset);
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "6d2365f" /\ chksum(tla) = "576d8a6e")
VARIABLES itemset, pc

vars == << itemset, pc >>

Init == (* Global variables *)
        /\ itemset \in ItemSets
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(BestKnapsacks(itemset) \subseteq ValidKnapsacks(itemset),
                   "Failure of assertion at line 44, column 5.")
         /\ pc' = "Done"
         /\ UNCHANGED itemset

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

===============================================================================

Practical TLA+ - Chapter 3
