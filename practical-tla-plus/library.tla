-------------------------------- MODULE library --------------------------------

EXTENDS Integers, TLC, Sequences
CONSTANTS Books, People, NumCopiesMin, NumCopiesMax

NumCopies == NumCopiesMin..NumCopiesMax

ASSUME NumCopies \subseteq Nat
\* PT == INSTANCE PT

(*--algorithm library
variables
    library \in [Books -> NumCopies],
    reservations = [b \in Books |-> {}],
    order = [b \in Books |-> <<>>];

define
    AvailableBooks == {b \in Books: library[b] > 0}
    BorrowableBooks(p) == {b \in AvailableBooks: reservations[b] = {} \/ (p \in reservations[b] /\ p = Head(order[b])) }
end define;

fair process person \in People
variables
    books = {},
    wants \in SUBSET Books;
begin
    Person:
        either
            with b \in (BorrowableBooks(self) \intersect wants) \ books do
                if self \in reservations[b] then
                    order[b] := Tail(order[b]);
                    reservations[b] := reservations[b] \ {self}
                end if;
                library[b] := library[b] - 1;
                books := books \union {b};
                wants := wants \ {b};
            end with;
        or
            with b \in books do
                library[b] := library[b] + 1;
                books := books \ {b};
            end with;
        or
            with b \in {b \in wants: self \notin reservations[b]} do
                reservations[b] := reservations[b] \union {self};
                order[b] := Append(order[b], self);
            end with
        or
            await wants = {};
            with b \in SUBSET books do
                wants := b;
            end with;
        end either;
    goto Person;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "482dc1ec" /\ chksum(tla) = "db8cde1b")
VARIABLES library, reservations, order, pc

(* define statement *)
AvailableBooks == {b \in Books: library[b] > 0}
BorrowableBooks(p) == {b \in AvailableBooks: reservations[b] = {} \/ (p \in reservations[b] /\ p = Head(order[b]))}

VARIABLES books, wants

vars == << library, reservations, order, pc, books, wants >>

ProcSet == (People)

Init == (* Global variables *)
    /\ library \in [Books -> NumCopies]
    /\ reservations = [b \in Books |-> {}]
    /\ order = [b \in Books |-> <<>>]
    (* Process person *)
    /\ books = [self \in People |-> {}]
    /\ wants \in [People -> SUBSET Books]
    /\ pc = [self \in ProcSet |-> "Person"]

Person(self) ==
    /\ pc[self] = "Person"
    /\
        \/
            /\ \E b \in (BorrowableBooks(self) \intersect wants[self]) \ books[self]:
                /\ IF self \in reservations[b]
                    THEN
                        /\ order' = [order EXCEPT ![b] = Tail(order[b])]
                        /\ reservations' = [reservations EXCEPT ![b] = reservations[b] \ {self}]
                    ELSE
                        /\ TRUE
                        /\ UNCHANGED << reservations, order >>
                /\ library' = [library EXCEPT ![b] = library[b] - 1]
                /\ books' = [books EXCEPT ![self] = books[self] \union {b}]
                /\ wants' = [wants EXCEPT ![self] = wants[self] \ {b}]
        \/
                /\ \E b \in books[self]:
                    /\ library' = [library EXCEPT ![b] = library[b] + 1]
                    /\ books' = [books EXCEPT ![self] = books[self] \ {b}]
                /\ UNCHANGED << reservations, order, wants >>
        \/
                /\ \E b \in {b \in wants[self]: self \notin reservations[b]}:
                    /\ reservations' = [reservations EXCEPT ![b] = reservations[b] \union {self}]
                    /\ order' = [order EXCEPT ![b] = Append(order[b], self)]
                /\ UNCHANGED << library, books, wants >>
        \/
                /\ wants[self] = {}
                /\ \E b \in SUBSET books[self]:
                    wants' = [wants EXCEPT ![self] = b]
                /\ UNCHANGED << library, reservations, order, books >>
    /\ pc' = [pc EXCEPT ![self] = "Person"]

person(self) == Person(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating ==
    /\ \A self \in ProcSet: pc[self] = "Done"
    /\ UNCHANGED vars

Next == (\E self \in People: person(self))
\/ Terminating

Spec ==
    /\ Init /\ [][Next]_vars
    /\ \A self \in People: WF_vars(person(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

NoDuplicateReservations ==
    \A b \in Books:
        \A i, j \in 1..Len(order[b]):
            i /= j => order[b][i] /= order[b][j]

TypeInvariant ==
    /\ library \in [Books -> NumCopies \union {0}]
    /\ books \in [People -> SUBSET Books]
    /\ wants \in [People -> SUBSET Books]
    /\ order \in [Books -> Seq(People)]
    /\ NoDuplicateReservations

Liveness ==
    \A p \in People:
        \A b \in Books:
            b \in wants[p] ~> b \notin wants[p]

================================================================================

Practical TLA+ - Chapter 10
