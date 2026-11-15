---- MODULE Lasso ----
EXTENDS Naturals
VARIABLES x, done
vars == <<x, done>>
Init == x = 0 /\ done = FALSE
Step == x' = (x + 1) % 3 /\ UNCHANGED done
Spec == Init /\ [][Step]_vars /\ WF_vars(Step)
SpecNoFair == Init /\ [][Step]_vars
EventuallyDone == <>done
ZeroLeadsToOne == (x = 0) ~> (x = 1)
====
