----------------------------- MODULE message_queue -----------------------------

EXTENDS TLC, Integers, Sequences
CONSTANTS MaxQueueSize

(*--algorithm message_queue
variable queue = <<>>;

define
    BoundedQueue == Len(queue) <= MaxQueueSize
end define;

process writer = "writer"
begin Write:
    while TRUE do
        await Len(queue) < MaxQueueSize;
        queue := Append(queue, "msg");
    end while;
end process;

process reader = "readers"
variables current_message = "none";
begin Read:
    while TRUE do
        await Len(queue) > 0;
        current_message := Head(queue);
        queue := Tail(queue);
    end while;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "31e27fb6" /\ chksum(tla) = "8d3d0f6f")
VARIABLE queue

(* define statement *)
BoundedQueue == Len(queue) <= MaxQueueSize

VARIABLE current_message

vars == << queue, current_message >>

ProcSet == {"writer"} \union {"readers"}

Init == (* Global variables *)
    /\ queue = <<>>
    (* Process reader *)
    /\ current_message = "none"

writer ==
    /\ Len(queue) < MaxQueueSize
    /\ queue' = Append(queue, "msg")
    /\ UNCHANGED current_message

reader ==
    /\ Len(queue) > 0
    /\ current_message' = Head(queue)
    /\ queue' = Tail(queue)

Next == writer \/ reader

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

================================================================================

Practical TLA+ - Chapter 4
