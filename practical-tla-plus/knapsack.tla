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

BestKnapsacksOne(itemset) == 
    LET all == ValidKnapsacks(itemset)
    IN CHOOSE all_the_best \in SUBSET all:
        \E good \in all_the_best:
            /\ \A other \in all_the_best:
                KnapsackValue(good, itemset) = KnapsackValue(other, itemset)
            /\ \A worse \in all \ all_the_best:
                KnapsackValue(good, itemset) > KnapsackValue(worse, itemset)

BestKnapsacksTwo(itemset) == 
    LET
        all == ValidKnapsacks(itemset)
        best == CHOOSE best \in all:
            \A worse \in all \ {best}:
                KnapsackValue(best, itemset) >= KnapsackValue(worse, itemset)
        value_of_best == KnapsackValue(best, itemset)
    IN
        {k \in all: value_of_best = KnapsackValue(k, itemset)}

(*--algorithm knapsack
variables
    itemset \in ItemSets;
begin
    \* assert BestKnapsack(itemset) \in ValidKnapsacks(itemset);
    assert \A is \in ItemSets: BestKnapsacksTwo(is) = BestKnapsacksOne(is)
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "b852ecd7" /\ chksum(tla) = "d6a45c12")
VARIABLES itemset, pc

vars == << itemset, pc >>

Init == (* Global variables *)
        /\ itemset \in ItemSets
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(\A is \in ItemSets: BestKnapsacksTwo(is) = BestKnapsacksOne(is), 
                   "Failure of assertion at line 54, column 5.")
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
