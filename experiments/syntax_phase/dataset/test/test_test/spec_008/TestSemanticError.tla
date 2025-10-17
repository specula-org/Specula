---- MODULE TestSemanticError ----
EXTENDS Naturals

VARIABLES x, y

Init == x = 0 /\ y = 0

Next == x' = UndefinedSymbol + 1 /\ y' = y + 1

Spec == Init /\ [][Next]_<<x, y>>
====