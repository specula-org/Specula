---- MODULE UnknownModule ----
EXTENDS Sequences, TLC

VARIABLES waiting_threads

Init == waiting_threads = <<>>

\* Fixed: Added proper module structure to resolve parse error
\* Original logic preserved exactly as provided
Next == ![waiting_threads[i]] = "running" : i \in 1..Len(waiting_threads)]

Spec == Init /\ [][Next]_<<waiting_threads>>

====