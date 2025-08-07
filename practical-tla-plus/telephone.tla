------------------------------ MODULE telephone ----------------------------

EXTENDS Sequences, TLC

(*--algorithm recycler
variables
    to_send = <<1, 2, 3>>,
    received = <<>>,
    in_transit = {};

begin
    while Len(received) # 3 do
        if to_send # <<>> then
            in_transit := in_transit \cup {Head(to_send)};
            to_send := Tail(to_send);
        end if;
        either 
            with msg \in in_transit do
                received := Append(received, msg);
                in_transit := in_transit \cup {msg};
            end with;
        or
            skip;
        end either;
    end while;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "5c1ffa1d" /\ chksum(tla) = "2ddf5b03")
VARIABLES to_send, received, in_transit, pc

vars == << to_send, received, in_transit, pc >>

Init == (* Global variables *)
        /\ to_send = <<1, 2, 3>>
        /\ received = <<>>
        /\ in_transit = {}
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF Len(received) # 3
               THEN /\ IF to_send # <<>>
                          THEN /\ in_transit' = (in_transit \cup {Head(to_send)})
                               /\ to_send' = Tail(to_send)
                          ELSE /\ TRUE
                               /\ UNCHANGED << to_send, in_transit >>
                    /\ \/ /\ pc' = "Lbl_2"
                       \/ /\ TRUE
                          /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << to_send, in_transit >>
         /\ UNCHANGED received

Lbl_2 == /\ pc = "Lbl_2"
         /\ \E msg \in in_transit:
              /\ received' = Append(received, msg)
              /\ in_transit' = (in_transit \cup {msg})
         /\ pc' = "Lbl_1"
         /\ UNCHANGED to_send

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
===============================================================================

Practical TLA+ - Chapter 2
