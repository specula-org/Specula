
---- MODULE TestTypeError ----
EXTENDS Naturals

VARIABLES x, y

Init == x = 0 /\ y = 0

Next == x' = x + "string" /\ y' = y + 1  \\ Type error: can't add string to nat

Spec == Init /\ [][Next]_<<x, y>>
====
